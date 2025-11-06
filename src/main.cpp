#include <Arduino.h>
#include <BLEDevice.h>
#include <BLEServer.h>
#include <BLEUtils.h>
#include <BLE2902.h>
#include <esp_err.h>
#include <string.h>
#include <math.h>
#include "p300_waveform_data.h"
#include <algorithm>

// ========= ADS1299 実装と互換の設定 =========
#define DEVICE_NAME "ADS1299_EEG_NUS"
#define CH_MAX 8
#define SAMPLE_RATE_HZ 250
#define SAMPLES_PER_CHUNK 25 // 250SPS / 10Hz = 25

// ========= BLE (NUS-like) UUIDs (ADS1299 実装と同一) =========
#define SERVICE_UUID "6E400001-B5A3-F393-E0A9-E50E24DCCA9E"
#define CHARACTERISTIC_UUID_TX "6E400003-B5A3-F393-E0A9-E50E24DCCA9E" // Notify
#define CHARACTERISTIC_UUID_RX "6E400002-B5A3-F393-E0A9-E50E24DCCA9E" // Write

// ========= パケット種別 (ADS1299 実装と同一) =========
#define PKT_TYPE_DATA_CHUNK 0x66
#define PKT_TYPE_DEVICE_CFG 0xDD

// ========= 制御コマンド (ADS1299 実装と同一) =========
#define CMD_START_STREAMING 0xAA
#define CMD_STOP_STREAMING 0x5B
#define CMD_TRIGGER_PULSE 0xC1

// ========= データ構造 (ADS1299 実装と同一) =========
struct __attribute__((packed)) ElectrodeConfig
{
    char name[8];
    uint8_t type;
    uint8_t reserved;
};

// IMU なし、符号付き 16bit 信号に修正
struct __attribute__((packed)) SampleData
{
    int16_t signals[CH_MAX]; // 符号付き 16bit, little-endian
    uint8_t trigger_state;   // GPIO 下位 4bit を模倣 (0..15)
    uint8_t reserved[3];     // 予約領域
};

struct __attribute__((packed)) ChunkedSamplePacket
{
    uint8_t packet_type;  // 0x66
    uint16_t start_index; // LE
    uint8_t num_samples;  // 25
    SampleData samples[SAMPLES_PER_CHUNK];
};

struct __attribute__((packed)) DeviceConfigPacket
{
    uint8_t packet_type;  // 0xDD
    uint8_t num_channels; // 実使用 ch 数（今回は 8ch 固定のダミー）
    uint8_t reserved[6];
    ElectrodeConfig configs[CH_MAX];
};

static_assert(sizeof(SampleData) == 20, "SampleData must be 20 bytes");
static_assert(sizeof(ChunkedSamplePacket) <= 512, "Chunk packet exceeds BLE payload expectations");

constexpr size_t SAMPLE_DATA_BYTES = sizeof(SampleData);
constexpr size_t CHUNK_HEADER_BYTES = sizeof(uint8_t) + sizeof(uint16_t) + sizeof(uint8_t);
constexpr uint16_t DEFAULT_ATT_MTU = 23;
constexpr uint16_t REQUIRED_MTU_BYTES = static_cast<uint16_t>(sizeof(ChunkedSamplePacket) + 3);

// ========= グローバル変数 =========
BLEServer *pServer = nullptr;
BLECharacteristic *pTxCharacteristic = nullptr;
BLE2902 *pCccdDescriptor = nullptr;

bool deviceConnected = false;
volatile bool isStreaming = false; // volatile: 割り込みから変更されるため

volatile uint16_t negotiatedMtu = DEFAULT_ATT_MTU;
volatile bool mtuReady = false;
volatile bool streamStartRequested = false;

// 送信パケットをグローバルに確保 (スタックオーバーフロー防止)
ChunkedSamplePacket chunkPacket;
DeviceConfigPacket deviceConfigPacket;

// BLE コールバックからメインループへ処理を依頼するためのフラグ
volatile bool g_send_config_packet = false;

// サンプリング用タイマー
hw_timer_t *timer = nullptr;
portMUX_TYPE timerMux = portMUX_INITIALIZER_UNLOCKED;
volatile bool sampleReady = false;

// データバッファとカウンタ
SampleData sampleBuffer[SAMPLES_PER_CHUNK];
volatile int sampleBufferIndex = 0;
uint16_t sampleIndexCounter = 0;

// ========= P300 波形再生用の状態 =========
constexpr float MICROVOLT_PER_COUNT = 0.022f; // ADS1299 (Gain=24, Vref=4.5V) に近い LSB 換算値
constexpr float MICROVOLT_TO_COUNT = 1.0f / MICROVOLT_PER_COUNT;
constexpr size_t TRIGGER_PULSE_WIDTH_SAMPLES = 6; // ≒24ms
constexpr float BACKGROUND_NOISE_UV = 1.2f;
constexpr float TARGET_EVENT_SCALE = 1.0f;
constexpr float NONTARGET_EVENT_SCALE = 0.35f;
constexpr float DEFAULT_EVENT_SCALE = 0.25f;
constexpr float CHANNEL_GAIN[CH_MAX] = {1.0f, 0.65f, 0.55f, 0.5f, 0.45f, 0.4f, 0.35f, 0.3f};
constexpr float CHANNEL_PHASE[CH_MAX] = {0.0f, 0.7f, 1.4f, 2.1f, 0.5f, 1.2f, 1.9f, 2.6f};
constexpr float ALPHA_FREQ_HZ = 10.0f;
constexpr float BETA_FREQ_HZ = 20.0f;
constexpr float ALPHA_AMPLITUDE_UV = 8.0f;
constexpr float BETA_AMPLITUDE_UV = 3.0f;

portMUX_TYPE eventMux = portMUX_INITIALIZER_UNLOCKED;
bool p300Active = false;
size_t p300Cursor = 0;
uint8_t currentTriggerValue = 0;
size_t triggerSamplesRemaining = 0;

static void startStreamingNow();
static void handleStartStreamingRequest();
static void handleStopStreaming();

static float randomUniform()
{
    return static_cast<float>(rand()) / static_cast<float>(RAND_MAX);
}

static float sampleNoiseUv(float amplitudeUv)
{
    const float centered = randomUniform() * 2.0f - 1.0f;
    return centered * amplitudeUv;
}

static int16_t microvoltToCounts(float microvolt)
{
    const float raw = microvolt * MICROVOLT_TO_COUNT;
    const float clamped = std::max(-32768.0f, std::min(32767.0f, raw));
    return static_cast<int16_t>(clamped);
}

static float eventAmplitudeScale(uint8_t triggerValue)
{
    if (triggerValue == 1)
    {
        return TARGET_EVENT_SCALE;
    }
    if (triggerValue == 2)
    {
        return NONTARGET_EVENT_SCALE;
    }
    return DEFAULT_EVENT_SCALE;
}

static void resetStimulusPlayback()
{
    portENTER_CRITICAL(&eventMux);
    p300Active = false;
    p300Cursor = 0;
    currentTriggerValue = 0;
    triggerSamplesRemaining = 0;
    portEXIT_CRITICAL(&eventMux);
}

static void startStreamingNow()
{
    if (!deviceConnected)
    {
        return;
    }
    isStreaming = true;
    streamStartRequested = false;
    sampleIndexCounter = 0;
    sampleBufferIndex = 0;
    resetStimulusPlayback();
    g_send_config_packet = true;
    Serial.printf("[CMD] Streaming started (MTU=%u)\n", negotiatedMtu);
}

static void handleStartStreamingRequest()
{
    streamStartRequested = true;
    if (!mtuReady)
    {
        Serial.printf("[CMD] Start streaming requested, waiting for MTU >= %u (current=%u)\n", REQUIRED_MTU_BYTES, negotiatedMtu);
        return;
    }
    if (!isStreaming)
    {
        startStreamingNow();
    }
}

static void handleStopStreaming()
{
    isStreaming = false;
    streamStartRequested = false;
    sampleBufferIndex = 0;
    resetStimulusPlayback();
    Serial.println("[CMD] Stop streaming");
}

static void startStimulusEvent(uint8_t triggerValue)
{
    portENTER_CRITICAL(&eventMux);
    p300Active = true;
    p300Cursor = std::min<std::size_t>(P300_TRIGGER_OFFSET_SAMPLES, P300_CYCLE_SAMPLES - 1);
    currentTriggerValue = (triggerValue & 0x0F);
    triggerSamplesRemaining = TRIGGER_PULSE_WIDTH_SAMPLES;
    portEXIT_CRITICAL(&eventMux);
}

static bool notificationsEnabled()
{
    if (pCccdDescriptor == nullptr)
    {
        return false;
    }
    const uint8_t *value = pCccdDescriptor->getValue();
    if (value == nullptr)
    {
        return false;
    }
    const uint16_t flags = static_cast<uint8_t>(value[0]) | (static_cast<uint8_t>(value[1]) << 8);
    return (flags & 0x0001) != 0;
}

// ADS1299 互換の電極設定
const ElectrodeConfig defaultElectrodes[CH_MAX] = {
    {"CH1", 0, 0},
    {"CH2", 0, 0},
    {"CH3", 0, 0},
    {"CH4", 0, 0},
    {"CH5", 0, 0},
    {"CH6", 0, 0},
    {"CH7", 0, 0},
    {"CH8", 0, 0}};

// ========= BLE コールバック (ADS1299 実装と同一) =========
class ServerCallbacks : public BLEServerCallbacks
{
    void onConnect(BLEServer *s) override
    {
        deviceConnected = true;
        negotiatedMtu = DEFAULT_ATT_MTU;
        mtuReady = false;
        streamStartRequested = false;
        Serial.println(">>> [BLE] Client connected");
    }
    void onConnect(BLEServer *s, esp_ble_gatts_cb_param_t *param) override
    {
        onConnect(s);
        if (param != nullptr)
        {
            Serial.printf(">>> [BLE] Client connected (conn_id=%u)\n", param->connect.conn_id);
        }
    }
    void onDisconnect(BLEServer *s) override
    {
        deviceConnected = false;
        isStreaming = false;
        streamStartRequested = false;
        mtuReady = false;
        BLEDevice::startAdvertising();
        Serial.println(">>> [BLE] Client DISCONNECTED. Streaming stopped. Advertising restarted.");
    }
    void onDisconnect(BLEServer *s, esp_ble_gatts_cb_param_t *param) override
    {
        onDisconnect(s);
        if (param != nullptr)
        {
            Serial.printf(">>> [BLE] Disconnect reason=0x%02X\n", param->disconnect.reason);
        }
    }
    void onMtuChanged(BLEServer *s, esp_ble_gatts_cb_param_t *param) override
    {
        if (param == nullptr)
        {
            return;
        }
        negotiatedMtu = param->mtu.mtu;
        mtuReady = negotiatedMtu >= REQUIRED_MTU_BYTES;
        Serial.printf(">>> [BLE] MTU negotiated: %u bytes (required >= %u)\n", negotiatedMtu, REQUIRED_MTU_BYTES);
        if (!mtuReady)
        {
            Serial.println(">>> [BLE] Waiting for larger MTU before streaming.");
            return;
        }
        if (streamStartRequested && !isStreaming)
        {
            startStreamingNow();
        }
    }
};

class RxCallbacks : public BLECharacteristicCallbacks
{
    void onWrite(BLECharacteristic *ch) override
    {
        std::string v = ch->getValue();
        if (v.empty())
            return;
        uint8_t cmd = static_cast<uint8_t>(v[0]);

        if (cmd == CMD_START_STREAMING)
        {
            handleStartStreamingRequest();
        }
        else if (cmd == CMD_STOP_STREAMING)
        {
            handleStopStreaming();
        }
        else if (cmd == CMD_TRIGGER_PULSE)
        {
            if (v.size() >= 2)
            {
                const uint8_t triggerValue = static_cast<uint8_t>(v[1]);
                startStimulusEvent(triggerValue);
                Serial.printf("[CMD] Trigger pulse requested. value=%u\n", triggerValue);
            }
            else
            {
                startStimulusEvent(1);
                Serial.println("[CMD] Trigger pulse requested without value. Default=1");
            }
        }
    }
};

// ========= タイマー割り込み処理 =========
void IRAM_ATTR onTimer()
{
    portENTER_CRITICAL_ISR(&timerMux);
    sampleReady = true;
    portEXIT_CRITICAL_ISR(&timerMux);
}

// ========= ダミーデータ生成 (ADS1299 互換) =========
void generateDummyAds1299Sample(SampleData &outSample)
{
    bool localActive;
    size_t localCursor;
    uint8_t localTriggerValue;
    size_t localTriggerRemaining;

    portENTER_CRITICAL(&eventMux);
    localActive = p300Active;
    localCursor = p300Cursor;
    localTriggerValue = currentTriggerValue;
    localTriggerRemaining = triggerSamplesRemaining;
    portEXIT_CRITICAL(&eventMux);

    float p300Uv = 0.0f;
    bool playbackStillActive = localActive;
    size_t updatedCursor = localCursor;

    if (localActive && localCursor < P300_CYCLE_SAMPLES)
    {
        p300Uv = P300_WAVEFORM_MICROVOLT[localCursor];
        updatedCursor = localCursor + 1;
        if (updatedCursor >= P300_CYCLE_SAMPLES)
        {
            playbackStillActive = false;
            updatedCursor = 0;
        }
    }
    else
    {
        playbackStillActive = false;
        updatedCursor = 0;
    }

    const float timeSec = static_cast<float>(sampleIndexCounter) / static_cast<float>(SAMPLE_RATE_HZ);
    const float eventScale = localActive ? eventAmplitudeScale(localTriggerValue) : 0.0f;

    for (int ch = 0; ch < CH_MAX; ++ch)
    {
        const float gain = CHANNEL_GAIN[ch];
        const float phase = CHANNEL_PHASE[ch];

        const float alpha = ALPHA_AMPLITUDE_UV * sinf(2.0f * PI * ALPHA_FREQ_HZ * timeSec + phase);
        const float beta = BETA_AMPLITUDE_UV * sinf(2.0f * PI * BETA_FREQ_HZ * timeSec + phase * 0.7f);
        float channelUv = (alpha + beta) * gain;
        channelUv += sampleNoiseUv(BACKGROUND_NOISE_UV) * gain;
        if (eventScale > 0.0f)
        {
            channelUv += p300Uv * eventScale * gain;
        }
        outSample.signals[ch] = microvoltToCounts(channelUv);
    }

    uint8_t triggerState = 0;
    if (localTriggerRemaining > 0)
    {
        triggerState = static_cast<uint8_t>(localTriggerValue & 0x0F);
        localTriggerRemaining--;
    }
    outSample.trigger_state = triggerState;

    outSample.reserved[0] = triggerState;
    outSample.reserved[1] = triggerState ? 0xA5 : 0x00;
    outSample.reserved[2] = 0x00;

    portENTER_CRITICAL(&eventMux);
    p300Active = playbackStillActive;
    p300Cursor = updatedCursor;
    currentTriggerValue = playbackStillActive ? localTriggerValue : 0;
    triggerSamplesRemaining = localTriggerRemaining;
    portEXIT_CRITICAL(&eventMux);
}

// ========= Setup =========
void setup()
{
    Serial.begin(115200);
    delay(1000);
    Serial.println("\n--- ADS1299-Compatible Dummy Data Streamer ---");
    srand(1); // 再現性のあるノイズ生成

    // BLEデバイス初期化
    BLEDevice::init(DEVICE_NAME);
    esp_err_t mtuResult = BLEDevice::setMTU(517);
    if (mtuResult != ESP_OK)
    {
        Serial.printf("[BLE] Failed to request MTU 517 (err=0x%02X)\n", static_cast<uint32_t>(mtuResult));
    }
    pServer = BLEDevice::createServer();
    pServer->setCallbacks(new ServerCallbacks());
    BLEService *pService = pServer->createService(SERVICE_UUID);

    // TX Characteristic (Notify)
    pTxCharacteristic = pService->createCharacteristic(
        CHARACTERISTIC_UUID_TX, BLECharacteristic::PROPERTY_NOTIFY);
    pCccdDescriptor = new BLE2902();
    pTxCharacteristic->addDescriptor(pCccdDescriptor);

    // RX Characteristic (Write)
    BLECharacteristic *pRxCharacteristic = pService->createCharacteristic(
        CHARACTERISTIC_UUID_RX, BLECharacteristic::PROPERTY_WRITE);
    pRxCharacteristic->setCallbacks(new RxCallbacks());

    pService->start();
    BLEAdvertising *adv = BLEDevice::getAdvertising();
    adv->addServiceUUID(SERVICE_UUID);
    adv->setScanResponse(true);
    BLEDevice::startAdvertising();
    Serial.println("BLE advertising started (ADS1299-NUS compatible)");

    // サンプリング用タイマー設定
    const int timer_id = 0;
    const uint32_t prescaler = 80; // 80MHz / 80 = 1MHz
    const uint64_t alarm_value = 1000000 / SAMPLE_RATE_HZ;
    timer = timerBegin(timer_id, prescaler, true);
    timerAttachInterrupt(timer, &onTimer, true);
    timerAlarmWrite(timer, alarm_value, true);
    timerAlarmEnable(timer);
    Serial.printf("Sampling timer started for %d Hz\n", SAMPLE_RATE_HZ);
}

// ========= Loop =========
void loop()
{
    // --- [1] BLE コールバックからの設定情報送信要求を処理 ---
    if (g_send_config_packet && deviceConnected)
    {
        if (!mtuReady)
        {
            // MTU negotiation still in progress
        }
        else if (!notificationsEnabled())
        {
            // Wait until CCCD enables notifications
        }
        else
        {
            g_send_config_packet = false;
            deviceConfigPacket.packet_type = PKT_TYPE_DEVICE_CFG;
            deviceConfigPacket.num_channels = CH_MAX; // 8ch のダミーデバイスとして通知
            memset(deviceConfigPacket.reserved, 0, sizeof(deviceConfigPacket.reserved));
            memcpy(deviceConfigPacket.configs, defaultElectrodes, sizeof(defaultElectrodes));

            pTxCharacteristic->setValue((uint8_t *)&deviceConfigPacket, sizeof(deviceConfigPacket));
            pTxCharacteristic->notify();
            Serial.println("[CMD] Start streaming -> Sent DeviceConfigPacket");
            delay(10); // 送信処理のための短い待機
        }
    }

    // --- [2] ストリーミング中のデータ生成とバッファリング ---
    if (isStreaming && deviceConnected && mtuReady)
    {
        if (sampleReady)
        {
            portENTER_CRITICAL(&timerMux);
            sampleReady = false;
            portEXIT_CRITICAL(&timerMux);

            // ダミーデータを生成してバッファに格納
            generateDummyAds1299Sample(sampleBuffer[sampleBufferIndex]);
            sampleBufferIndex++;
            sampleIndexCounter++;
        }

        // --- [3] バッファが満たされたらBLEで送信 ---
        if (sampleBufferIndex >= SAMPLES_PER_CHUNK)
        {
            chunkPacket.packet_type = PKT_TYPE_DATA_CHUNK;
            chunkPacket.start_index = (uint16_t)(sampleIndexCounter - SAMPLES_PER_CHUNK);
            chunkPacket.num_samples = SAMPLES_PER_CHUNK;
            memcpy(chunkPacket.samples, sampleBuffer, sizeof(sampleBuffer));

            if (notificationsEnabled())
            {
                pTxCharacteristic->setValue((uint8_t *)&chunkPacket, sizeof(chunkPacket));
                pTxCharacteristic->notify();
                delay(2);
            }
            else
            {
                Serial.println("[BLE] Notifications disabled. Skipping notify.");
            }

            sampleBufferIndex = 0; // バッファインデックスをリセット
        }
    }
    else
    {
        // ストリーミング中でない場合はCPUを少し休ませる
        delay(10);
    }
}
