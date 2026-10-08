/* ============================================================================
   PULSELINK
   Smartphone Camera PPG → BPM → BLE → ESP32 → OLED

   Educational prototype only.
   ============================================================================ */

'use strict';

/* ============================================================================
   1. SETTINGS
   ============================================================================ */

// IMPORTANT: Must match ESP32 firmware
const BLE_DEVICE_NAME = 'PulseLink';

const BLE_SERVICE_UUID =
  '4fafc201-1fb5-459e-8fcc-c5c9c331914b';

const BLE_CHARACTERISTIC_UUID =
  'beb5483e-36e1-4688-b7f5-ea07361b26a8';

const BLE_RECONNECT_ATTEMPTS = 5;
const BLE_RECONNECT_DELAY_MS = 2000;


// Valid BPM range
const BPM_MIN_VALID = 40;
const BPM_MAX_VALID = 180;


// BLE sending
const SEND_INTERVAL_MS = 2000;
const SEND_MIN_GAP_MS = 1000;
const SEND_CHANGE_THRESHOLD = 3;


// Signal processing
const FS = 30;

const WINDOW_SEC = 10;

const MIN_ANALYSIS_SEC = 6;

const SETTLE_MS = 1500;

const ANALYSIS_INTERVAL_MS = 500;

const FINGER_LOST_MS = 600;

const NO_GOOD_RESET_MS = 5000;

const MIN_SIGNAL_STD = 0.02;

const BASELINE_SEC = 1.5;

const PERIODICITY_GOOD = 0.70;

const PERIODICITY_FAIR = 0.55;

const WAVE_SEC = 6;


// Camera
const ROI_FRACTION = 0.5;

const SAMPLE_SIZE = 48;

const FINGER_MIN_RED = 80;

const FINGER_RED_RATIO = 1.3;


/* ============================================================================
   2. PURE SIGNAL PROCESSING FUNCTIONS
   ============================================================================ */

function mean(arr) {

  if (!arr.length) return 0;

  let sum = 0;

  for (let i = 0; i < arr.length; i++) {
    sum += arr[i];
  }

  return sum / arr.length;
}


function stdDev(arr, m) {

  if (arr.length < 2) return 0;

  let sum = 0;

  for (let i = 0; i < arr.length; i++) {

    const d = arr[i] - m;

    sum += d * d;
  }

  return Math.sqrt(sum / arr.length);
}


function median(arr) {

  if (!arr.length) return 0;

  const sorted = Array.from(arr).sort(
    (a, b) => a - b
  );

  const mid = Math.floor(sorted.length / 2);

  if (sorted.length % 2) {
    return sorted[mid];
  }

  return (
    sorted[mid - 1] +
    sorted[mid]
  ) / 2;
}


/*
 * Moving average filter
 */
function movingAverage(x, win) {

  const n = x.length;

  const out = new Float32Array(n);

  const half = Math.floor(win / 2);

  const prefix = new Float64Array(n + 1);

  for (let i = 0; i < n; i++) {

    prefix[i + 1] =
      prefix[i] + x[i];

  }

  for (let i = 0; i < n; i++) {

    const a =
      Math.max(0, i - half);

    const b =
      Math.min(n - 1, i + half);

    out[i] =
      (prefix[b + 1] - prefix[a]) /
      (b - a + 1);
  }

  return out;
}


/*
 * Camera frames arrive at irregular times.
 * Convert them to a uniform 30 Hz signal.
 */
function resampleUniform(
  samples,
  startT,
  endT,
  fs
) {

  const n = Math.max(
    0,
    Math.floor(
      ((endT - startT) / 1000) * fs
    )
  );

  if (
    samples.length < 2 ||
    n <= 0
  ) {
    return new Float32Array(0);
  }

  const out =
    new Float32Array(n);

  let j = 0;

  for (let i = 0; i < n; i++) {

    const t =
      startT +
      (i * 1000) / fs;

    while (
      j < samples.length - 2 &&
      samples[j + 1].t < t
    ) {
      j++;
    }

    const a = samples[j];

    const b =
      samples[Math.min(
        j + 1,
        samples.length - 1
      )];

    const span =
      b.t - a.t;

    let f =
      span > 0
        ? (t - a.t) / span
        : 0;

    f = Math.max(
      0,
      Math.min(1, f)
    );

    out[i] =
      a.v +
      (b.v - a.v) * f;
  }

  return out;
}


/*
 * PPG filtering:
 *
 * raw red signal
 *      ↓
 * remove baseline
 *      ↓
 * invert
 *      ↓
 * smooth
 */
function filterPulse(x, fs) {

  if (!x.length) {
    return new Float32Array(0);
  }

  let baseWin =
    Math.round(
      fs * BASELINE_SEC
    );

  if (baseWin % 2 === 0) {
    baseWin++;
  }

  const baseline =
    movingAverage(
      x,
      baseWin
    );

  const highPass =
    new Float32Array(
      x.length
    );

  for (
    let i = 0;
    i < x.length;
    i++
  ) {

    highPass[i] =
      baseline[i] - x[i];
  }

  return movingAverage(
    highPass,
    5
  );
}


/*
 * Peak detection
 */
function findPeaks(
  x,
  fs,
  minDistSec,
  threshold
) {

  const minDist =
    Math.max(
      1,
      Math.round(
        minDistSec * fs
      )
    );

  const peaks = [];

  for (
    let i = 1;
    i < x.length - 1;
    i++
  ) {

    if (
      x[i] > threshold &&
      x[i] > x[i - 1] &&
      x[i] >= x[i + 1]
    ) {

      if (
        peaks.length &&
        i -
        peaks[peaks.length - 1] <
        minDist
      ) {

        const previous =
          peaks[peaks.length - 1];

        if (
          x[i] > x[previous]
        ) {

          peaks[
            peaks.length - 1
          ] = i;
        }

      } else {

        peaks.push(i);

      }
    }
  }

  return peaks;
}


/*
 * Autocorrelation
 */
function autocorrAt(
  x,
  lag
) {

  const n = x.length;

  if (
    lag <= 0 ||
    lag >= n - 2
  ) {
    return 0;
  }

  const m = mean(x);

  let numerator = 0;

  let denominator = 0;

  for (
    let i = 0;
    i < n;
    i++
  ) {

    const d =
      x[i] - m;

    denominator +=
      d * d;
  }

  for (
    let i = 0;
    i + lag < n;
    i++
  ) {

    numerator +=
      (x[i] - m) *
      (x[i + lag] - m);
  }

  if (
    denominator <= 0
  ) {
    return 0;
  }

  return (
    (numerator / (n - lag)) /
    (denominator / n)
  );
}


/*
 * Periodicity score
 */
function periodicityScore(
  x,
  periodSamples
) {

  const center =
    Math.round(
      periodSamples
    );

  let best = -1;

  for (
    let lag = center - 2;
    lag <= center + 2;
    lag++
  ) {

    if (lag > 0) {

      best =
        Math.max(
          best,
          autocorrAt(
            x,
            lag
          )
        );
    }
  }

  return best;
}


/*
 * Main BPM analysis
 */
function analyzePulse(
  filtered,
  fs
) {

  function poor(
    reason,
    extra = {}
  ) {

    return Object.assign(
      {
        bpm: null,
        quality: 'POOR',
        peaks: [],
        reason
      },
      extra
    );
  }


  const trim =
    Math.round(
      0.3 * fs
    );


  if (
    filtered.length <
    fs * 3 +
    2 * trim
  ) {

    return poor(
      'not enough data'
    );
  }


  const segment =
    filtered.subarray(
      trim,
      filtered.length - trim
    );


  const m =
    mean(segment);

  const sd =
    stdDev(
      segment,
      m
    );


  if (
    sd < MIN_SIGNAL_STD
  ) {

    return poor(
      'signal too weak'
    );
  }


  /*
   * Detect peaks
   */

  const minDistanceSec =
    60 / BPM_MAX_VALID;


  const rawPeaks =
    findPeaks(
      segment,
      fs,
      minDistanceSec,
      m + 0.2 * sd
    );


  const peaks =
    rawPeaks.map(
      i => i + trim
    );


  /*
   * Calculate beat intervals
   */

  const minInterval =
    60 / BPM_MAX_VALID;

  const maxInterval =
    60 / BPM_MIN_VALID;


  const intervals = [];


  for (
    let i = 1;
    i < rawPeaks.length;
    i++
  ) {

    const dt =
      (
        rawPeaks[i] -
        rawPeaks[i - 1]
      ) / fs;


    if (
      dt >= minInterval &&
      dt <= maxInterval
    ) {

      intervals.push(dt);

    }
  }


  if (
    intervals.length < 3
  ) {

    return poor(
      'too few pulses found',
      {
        peaks,
        std: sd
      }
    );
  }


  /*
   * Remove abnormal intervals
   */

  const med =
    median(intervals);


  const filteredIntervals =
    intervals.filter(
      value =>
        Math.abs(
          value - med
        ) <=
        0.20 * med
    );


  const consistency =
    filteredIntervals.length /
    intervals.length;


  if (
    filteredIntervals.length < 3
  ) {

    return poor(
      'pulse rhythm unstable',
      {
        peaks,
        std: sd
      }
    );
  }


  /*
   * Average heartbeat interval
   */

  const averageInterval =
    mean(
      filteredIntervals
    );


  const intervalStd =
    stdDev(
      filteredIntervals,
      averageInterval
    );


  const coefficientVariation =
    intervalStd /
    averageInterval;


  const bpm =
    60 /
    averageInterval;


  /*
   * Periodicity
   */

  const periodicity =
    periodicityScore(
      segment,
      averageInterval * fs
    );


  let quality = 'POOR';


  if (
    filteredIntervals.length >= 6 &&
    consistency >= 0.75 &&
    coefficientVariation <= 0.10 &&
    periodicity >= PERIODICITY_GOOD
  ) {

    quality = 'GOOD';

  } else if (
    filteredIntervals.length >= 4 &&
    consistency >= 0.60 &&
    coefficientVariation <= 0.18 &&
    periodicity >= PERIODICITY_FAIR
  ) {

    quality = 'FAIR';

  }


  if (
    bpm < BPM_MIN_VALID ||
    bpm > BPM_MAX_VALID
  ) {

    return poor(
      'BPM outside valid range',
      {
        peaks,
        std: sd
      }
    );
  }


  return {

    bpm,

    quality,

    peaks,

    reason: '',

    std: sd,

    cv: coefficientVariation,

    consistency,

    periodicity,

    pulses:
      filteredIntervals.length
  };
}


function isValidBpm(value) {

  return (
    Number.isInteger(value) &&
    value >= BPM_MIN_VALID &&
    value <= BPM_MAX_VALID
  );
}


/* ============================================================================
   3. DOM + APPLICATION STATE
   ============================================================================ */

const el = {};

const ELEMENT_IDS = [

  'banner',

  'bleDot',
  'bleStatus',

  'btnConnect',
  'btnDisconnect',
  'btnConnectAll',

  'btnStart',
  'btnStop',

  'bpmValue',
  'qualityChip',
  'measureStatus',
  'progress',

  'wave',
  'video',
  'sampleCanvas',

  'torchStatus',
  'redDebug',
  'logBox',
  'btnClearLog'
];


const state = {

  /* Camera */

  running: false,

  stream: null,

  track: null,

  wakeLock: null,

  canvasCtx: null,

  loopId: 0,

  analysisTimer: null,

  sendTimer: null,

  fingerActive: false,

  fingerSince: 0,

  lastFingerSeen: 0,

  lastSampleT: 0,

  samples: [],

  estimates: [],

  displayedBpm: null,

  quality: 'NONE',

  lastGoodAt: 0,

  lastRed: 0,


  /* BLE */

  device: null,

  characteristic: null,

  userDisconnected: false,

  reconnecting: false,

  writeChain: Promise.resolve(),

  lastSentAt: -Infinity,

  lastSentBpm: null
};


/* ============================================================================
   4. UI
   ============================================================================ */

function log(
  message,
  level
) {

  if (!el.logBox) return;

  const time =
    new Date().toLocaleTimeString();

  const prefix =
    level === 'error'
      ? '[ERROR] '
      : '';

  el.logBox.textContent +=
    `${time} ${prefix}${message}\n`;


  const lines =
    el.logBox.textContent
      .split('\n');


  if (
    lines.length > 120
  ) {

    el.logBox.textContent =
      lines
        .slice(
          lines.length - 100
        )
        .join('\n');
  }


  el.logBox.scrollTop =
    el.logBox.scrollHeight;


  if (
    level === 'error'
  ) {

    console.error(message);

  } else {

    console.log(message);

  }
}


function showBanner(
  message,
  type
) {

  if (!el.banner) return;

  el.banner.textContent =
    message;

  el.banner.className =
    'banner' +
    (
      type === 'info'
        ? ' info'
        : ''
    );
}


function hideBanner() {

  if (!el.banner) return;

  el.banner.className =
    'banner hidden';

  el.banner.textContent = '';
}


function setBleStatus(
  text,
  kind = ''
) {

  if (el.bleStatus) {

    el.bleStatus.textContent =
      text;
  }

  if (el.bleDot) {

    el.bleDot.className =
      'dot' +
      (
        kind
          ? ' ' + kind
          : ''
      );
  }
}


function setMeasureStatus(
  text
) {

  if (el.measureStatus) {

    el.measureStatus.textContent =
      text;
  }
}


function updateQualityChip() {

  if (!el.qualityChip) return;

  let quality =
    state.quality || 'NONE';


  el.qualityChip.textContent =
    quality;


  el.qualityChip.className =
    'chip';


  if (
    quality === 'GOOD'
  ) {

    el.qualityChip.classList.add(
      'good'
    );

  } else if (
    quality === 'FAIR'
  ) {

    el.qualityChip.classList.add(
      'fair'
    );

  } else if (
    quality === 'POOR'
  ) {

    el.qualityChip.classList.add(
      'poor'
    );
  }
}


function updateBpmDisplay() {

  if (!el.bpmValue) return;

  if (
    state.displayedBpm === null
  ) {

    el.bpmValue.textContent =
      '--';

    return;
  }


  el.bpmValue.textContent =
    Math.round(
      state.displayedBpm
    );
}


function updateBleButtons() {

  const connected =
    isBleConnected();


  if (el.btnConnect) {

    el.btnConnect.disabled =
      connected ||
      state.reconnecting;
  }


  if (el.btnConnectAll) {

    el.btnConnectAll.disabled =
      connected ||
      state.reconnecting;
  }


  if (el.btnDisconnect) {

    el.btnDisconnect.disabled =
      !connected &&
      !state.reconnecting;
  }
}


function updateMeasureButtons() {

  if (el.btnStart) {

    el.btnStart.disabled =
      state.running;
  }


  if (el.btnStop) {

    el.btnStop.disabled =
      !state.running;
  }
}


/* ============================================================================
   5. BLUETOOTH
   ============================================================================ */

function isBleConnected() {

  return !!(
    state.device &&
    state.device.gatt &&
    state.device.gatt.connected &&
    state.characteristic
  );
}


async function onConnectClick(showAll = false) {
  hideBanner();

  if (!navigator.bluetooth) {
    showBanner(
      'Web Bluetooth is not available. Use Chrome on Android.'
    );

    log(
      'Web Bluetooth is not supported.',
      'error'
    );

    return;
  }

  if (!window.isSecureContext) {
    showBanner(
      'HTTPS is required for Bluetooth and camera access.'
    );

    return;
  }

  state.userDisconnected = false;

  try {
    setBleStatus(
      'Searching for PulseLink...',
      'busy'
    );

    log(
      showAll
        ? 'Opening Bluetooth device picker (all devices)...'
        : `Opening Bluetooth device picker (filtering for ${BLE_DEVICE_NAME})...`
    );

    const options = showAll
      ? {
          acceptAllDevices: true,
          optionalServices: [
            BLE_SERVICE_UUID
          ]
        }
      : {
          filters: [
            { name: BLE_DEVICE_NAME }
          ],
          optionalServices: [
            BLE_SERVICE_UUID
          ]
        };

    const device =
      await navigator.bluetooth.requestDevice(options);

    if (!device) {
      throw new Error(
        'Bluetooth device selection returned no device.'
      );
    }

    state.device = device;

    log(
      `Selected device: ${device.name || '(unnamed)'}`
    );

    device.removeEventListener(
      'gattserverdisconnected',
      onGattDisconnected
    );

    device.addEventListener(
      'gattserverdisconnected',
      onGattDisconnected
    );

    setBleStatus(
      'Device selected - connecting...',
      'busy'
    );

    await connectGatt();

  } catch (error) {

    console.error(
      'BLE connection error:',
      error
    );

    handleBleError(error);
  }

  updateBleButtons();
}


async function connectGatt() {

  if (!state.device) {

    throw new Error(
      'No BLE device selected'
    );
  }

  if (!state.device.gatt) {

    throw new Error(
      'Selected Bluetooth device does not expose GATT'
    );
  }

  setBleStatus(
    'Connecting to ESP32...',
    'busy'
  );

  try {

    /*
     * ------------------------------------------
     * STEP 1: GATT connection
     * ------------------------------------------
     */

    log(
      'Connecting to GATT server...'
    );

    const server =
      await state.device.gatt.connect();

    log(
      'GATT server connected.'
    );


    /*
     * ------------------------------------------
     * STEP 2: Find service
     * ------------------------------------------
     */

    log(
      `Searching for service: ${BLE_SERVICE_UUID}`
    );

    let service;

    try {

      service =
        await server.getPrimaryService(
          BLE_SERVICE_UUID
        );

    } catch (error) {

      log(
        `SERVICE ERROR: ${error.name}: ${error.message}`,
        'error'
      );

      throw new Error(
        `PulseLink connected, but the BLE service was not found. ` +
        `Expected service UUID: ${BLE_SERVICE_UUID}`
      );
    }

    log(
      'BLE service found.'
    );


    /*
     * ------------------------------------------
     * STEP 3: Find characteristic
     * ------------------------------------------
     */

    log(
      `Searching for characteristic: ${BLE_CHARACTERISTIC_UUID}`
    );

    let characteristic;

    try {

      characteristic =
        await service.getCharacteristic(
          BLE_CHARACTERISTIC_UUID
        );

    } catch (error) {

      log(
        `CHARACTERISTIC ERROR: ${error.name}: ${error.message}`,
        'error'
      );

      throw new Error(
        `BLE service found, but the characteristic was not found. ` +
        `Expected characteristic UUID: ${BLE_CHARACTERISTIC_UUID}`
      );
    }

    log(
      'BLE characteristic found.'
    );


    /*
     * ------------------------------------------
     * STEP 4: Check write permission
     * ------------------------------------------
     */

    log(
      `Characteristic properties: ` +
      `${JSON.stringify(characteristic.properties)}`
    );

    if (
      !characteristic.properties.write &&
      !characteristic.properties.writeWithoutResponse
    ) {

      throw new Error(
        'BLE characteristic is not writable'
      );
    }


    /*
     * ------------------------------------------
     * STEP 5: Save characteristic
     * ------------------------------------------
     */

    state.characteristic =
      characteristic;

    state.lastSentAt =
      -Infinity;

    state.lastSentBpm =
      null;


    /*
     * ------------------------------------------
     * SUCCESS
     * ------------------------------------------
     */

    setBleStatus(
      'ESP32 Connected',
      'ok'
    );

    log(
      '================================'
    );

    log(
      'ESP32 connected successfully'
    );

    log(
      `Device: ${state.device.name || 'PulseLink'}`
    );

    log(
      'BLE communication ready.'
    );

    log(
      '================================'
    );

    updateBleButtons();

  } catch (error) {

    state.characteristic = null;

    log(
      `GATT connection failed: ${error.name || 'Error'}: ${error.message || error}`,
      'error'
    );

    try {

      if (
        state.device &&
        state.device.gatt &&
        state.device.gatt.connected
      ) {

        state.device.gatt.disconnect();
      }

    } catch (_) {}

    throw error;
  }
}


function handleBleError(error) {

  const name =
    error?.name || 'Error';

  const message =
    error?.message || String(error);

  console.error(
    'BLE error:',
    name,
    message,
    error
  );

  log(
    `BLE error: ${name}: ${message}`,
    'error'
  );

  state.characteristic = null;

  /*
   * User cancelled the Bluetooth picker.
   */
  if (name === 'NotFoundError') {

    /*
     * If a device is already selected and we got
     * this error during GATT/service discovery,
     * it is NOT a "no device selected" error.
     */
    if (state.device) {

      setBleStatus(
        'Device selected - GATT error',
        'error'
      );

      showBanner(
        `PulseLink was selected, but its BLE service could not be found. ` +
        `Check the Service UUID. Error: ${message}`
      );

      log(
        `GATT/service discovery failed: ${message}`,
        'error'
      );

    } else {

      setBleStatus(
        'Not connected',
        ''
      );

      showBanner(
        'No ESP32 selected. Select PulseLink from the Bluetooth list.'
      );
    }

  } else if (name === 'SecurityError') {

    setBleStatus(
      'Bluetooth blocked',
      'error'
    );

    showBanner(
      'Bluetooth permission was blocked. Allow Bluetooth/Nearby devices permission.'
    );

  } else if (name === 'NetworkError') {

    setBleStatus(
      'Connection failed',
      'error'
    );

    showBanner(
      'Could not connect to PulseLink. Restart the ESP32 and try again.'
    );

  } else if (name === 'InvalidStateError') {

    setBleStatus(
      'Bluetooth busy',
      'error'
    );

    showBanner(
      'Bluetooth is busy. Disconnect PulseLink and try again.'
    );

  } else {

    setBleStatus(
      'Connection error',
      'error'
    );

    showBanner(
      `Bluetooth error: ${message}`
    );
  }

  updateBleButtons();
}


async function onGattDisconnected() {

  log(
    'ESP32 disconnected',
    'error'
  );


  state.characteristic =
    null;


  updateBleButtons();


  if (
    state.userDisconnected
  ) {

    setBleStatus(
      'Not connected',
      ''
    );

    return;
  }


  setBleStatus(
    'Disconnected - reconnecting...',
    'busy'
  );


  autoReconnect();
}


async function autoReconnect() {

  if (
    state.reconnecting
  ) {

    return;
  }


  state.reconnecting =
    true;


  updateBleButtons();


  for (
    let attempt = 1;
    attempt <= BLE_RECONNECT_ATTEMPTS;
    attempt++
  ) {

    if (
      state.userDisconnected ||
      !state.device
    ) {

      break;
    }


    setBleStatus(
      `Reconnecting (${attempt}/${BLE_RECONNECT_ATTEMPTS})...`,
      'busy'
    );


    await sleep(
      BLE_RECONNECT_DELAY_MS
    );


    if (
      state.userDisconnected
    ) {

      break;
    }


    try {

      await connectGatt();


      state.reconnecting =
        false;


      log(
        'BLE reconnected'
      );


      updateBleButtons();

      return;


    } catch (error) {

      log(
        `Reconnect ${attempt} failed: ${
          error?.message || error
        }`,
        'error'
      );
    }
  }


  state.reconnecting =
    false;


  if (
    !state.userDisconnected
  ) {

    setBleStatus(
      'Disconnected',
      'error'
    );


    showBanner(
      'Automatic reconnect failed. Press Connect ESP32.'
    );
  }


  updateBleButtons();
}


function onDisconnectClick() {

  state.userDisconnected =
    true;


  state.reconnecting =
    false;


  try {

    if (
      state.device &&
      state.device.gatt &&
      state.device.gatt.connected
    ) {

      state.device.gatt.disconnect();
    }

  } catch (_) {}


  state.characteristic =
    null;


  setBleStatus(
    'Not connected',
    ''
  );


  log(
    'Disconnected by user'
  );


  updateBleButtons();
}


/*
 * Send a string to ESP32.
 */
async function writeCharacteristic(
  text
) {

  if (
    !state.characteristic
  ) {

    throw new Error(
      'BLE characteristic not available'
    );
  }


  const data =
    new TextEncoder().encode(
      text
    );


  const ch =
    state.characteristic;


  if (
    ch.properties.write &&
    typeof ch.writeValueWithResponse ===
      'function'
  ) {

    await ch.writeValueWithResponse(
      data
    );


  } else if (
    ch.properties.writeWithoutResponse &&
    typeof ch.writeValueWithoutResponse ===
      'function'
  ) {

    await ch.writeValueWithoutResponse(
      data
    );


  } else {

    await ch.writeValue(
      data
    );
  }
}


/*
 * Queue BLE writes.
 */
function sendToEsp(
  text
) {

  const job =
    state.writeChain.then(
      async () => {

        if (
          !isBleConnected()
        ) {

          return false;
        }


        try {

          await writeCharacteristic(
            text
          );


          log(
            `Sent → ${text}`
          );


          return true;


        } catch (error) {

          log(
            `BLE write failed: ${
              error?.message || error
            }`,
            'error'
          );


          return false;
        }
      }
    );


  state.writeChain =
    job.catch(
      () => {}
    );


  return job;
}


/* ============================================================================
   6. CAMERA
   ============================================================================ */

function describeCameraError(
  error
) {

  if (!error) {

    return 'Unknown camera error.';
  }


  if (
    error.name ===
    'NotAllowedError'
  ) {

    return (
      'Camera permission was denied. Allow camera access in Chrome.'
    );
  }


  if (
    error.name ===
    'NotFoundError'
  ) {

    return (
      'No camera was found.'
    );
  }


  if (
    error.name ===
    'NotReadableError'
  ) {

    return (
      'Camera is already being used by another application.'
    );
  }


  if (
    error.name ===
    'OverconstrainedError'
  ) {

    return (
      'The requested camera configuration is not available.'
    );
  }


  return (
    `Camera error: ${
      error.message || error.name
    }`
  );
}


async function getCameraStream() {

  if (
    !navigator.mediaDevices ||
    !navigator.mediaDevices.getUserMedia
  ) {

    throw new Error(
      'Camera API is not available in this browser.'
    );
  }


  /*
   * Rear camera is required.
   */
  const constraints = {

    audio: false,

    video: {

      facingMode: {
        ideal: 'environment'
      },

      width: {
        ideal: 640
      },

      height: {
        ideal: 480
      },

      frameRate: {
        ideal: 30,
        max: 30
      }
    }
  };


  return navigator.mediaDevices.getUserMedia(
    constraints
  );
}


async function enableTorch() {

  if (!state.track) {

    return false;
  }


  try {

    const capabilities =
      state.track.getCapabilities
        ? state.track.getCapabilities()
        : {};


    if (
      !capabilities.torch
    ) {

      log(
        'Camera torch control is not available'
      );

      if (el.torchStatus) {

        el.torchStatus.textContent =
          'Flash: unavailable';

      }

      return false;
    }


    await state.track.applyConstraints({

      advanced: [
        {
          torch: true
        }
      ]
    });


    if (el.torchStatus) {

      el.torchStatus.textContent =
        'Flash: ON';

    }


    log(
      'Camera flash enabled'
    );


    return true;


  } catch (error) {

    log(
      `Could not enable flash: ${
        error?.message || error
      }`,
      'error'
    );


    if (el.torchStatus) {

      el.torchStatus.textContent =
        'Flash: unavailable';

    }


    return false;
  }
}


async function requestWakeLock() {

  if (
    !('wakeLock' in navigator)
  ) {

    return;
  }


  try {

    state.wakeLock =
      await navigator.wakeLock.request(
        'screen'
      );


    log(
      'Screen wake lock enabled'
    );


  } catch (_) {}
}


/* ============================================================================
   7. MEASUREMENT
   ============================================================================ */

function resetEstimates() {

  state.samples = [];

  state.estimates = [];

  state.displayedBpm = null;

  state.lastGoodAt = 0;

  state.quality = 'WAIT';

  state.lastSentAt =
    -Infinity;

  state.lastSentBpm =
    null;


  updateBpmDisplay();

  updateQualityChip();

  clearWave();
}


function clearWave() {

  if (!el.wave) {

    return;
  }


  const canvas =
    el.wave;


  const ctx =
    canvas.getContext('2d');


  ctx.clearRect(
    0,
    0,
    canvas.width,
    canvas.height
  );
}


function drawWave(
  filtered,
  peaks
) {

  if (!el.wave) {

    return;
  }


  const canvas =
    el.wave;


  const ctx =
    canvas.getContext('2d');


  const width =
    canvas.width;


  const height =
    canvas.height;


  ctx.clearRect(
    0,
    0,
    width,
    height
  );


  if (
    !filtered ||
    filtered.length < 2
  ) {

    return;
  }


  /*
   * Show only recent WAVE_SEC seconds.
   */
  const start =
    Math.max(
      0,
      filtered.length -
      Math.round(
        WAVE_SEC * FS
      )
    );


  let min =
    Infinity;

  let max =
    -Infinity;


  for (
    let i = start;
    i < filtered.length;
    i++
  ) {

    min =
      Math.min(
        min,
        filtered[i]
      );

    max =
      Math.max(
        max,
        filtered[i]
      );
  }


  if (
    !Number.isFinite(min) ||
    !Number.isFinite(max)
  ) {

    return;
  }


  const range =
    Math.max(
      0.000001,
      max - min
    );


  /*
   * Waveform
   */

  ctx.beginPath();


  for (
    let i = start;
    i < filtered.length;
    i++
  ) {

    const x =
      (
        (i - start) /
        Math.max(
          1,
          filtered.length -
          start - 1
        )
      ) *
      width;


    const y =
      height -
      (
        (filtered[i] - min) /
        range
      ) *
      height;


    if (i === start) {

      ctx.moveTo(
        x,
        y
      );

    } else {

      ctx.lineTo(
        x,
        y
      );
    }
  }


  ctx.strokeStyle =
    '#00e676';

  ctx.lineWidth = 2;

  ctx.stroke();


  /*
   * Draw detected peaks.
   */

  if (
    Array.isArray(peaks)
  ) {

    ctx.fillStyle =
      '#ff5252';


    for (
      const peak of peaks
    ) {

      if (
        peak < start ||
        peak >= filtered.length
      ) {

        continue;
      }


      const x =
        (
          (peak - start) /
          Math.max(
            1,
            filtered.length -
            start - 1
          )
        ) *
        width;


      const y =
        height -
        (
          (filtered[peak] - min) /
          range
        ) *
        height;


      ctx.beginPath();

      ctx.arc(
        x,
        y,
        3,
        0,
        Math.PI * 2
      );

      ctx.fill();
    }
  }
}


function updateProgress(
  value
) {

  if (!el.progress) {

    return;
  }


  el.progress.value =
    Math.max(
      0,
      Math.min(
        100,
        value
      )
    );
}


/*
 * Start measurement.
 */
async function startMeasurement() {

  if (
    state.running
  ) {

    return;
  }


  hideBanner();


  if (
    !window.isSecureContext
  ) {

    showBanner(
      'HTTPS is required for camera and Bluetooth.'
    );

    return;
  }


  try {

    log(
      'Starting camera...'
    );


    state.stream =
      await getCameraStream();


    state.track =
      state.stream.getVideoTracks()[0];


    el.video.srcObject =
      state.stream;


    el.video.setAttribute(
      'playsinline',
      ''
    );


    await el.video.play();


    /*
     * Canvas used for reading camera pixels.
     */
    const canvas =
      el.sampleCanvas;


    canvas.width =
      SAMPLE_SIZE;

    canvas.height =
      SAMPLE_SIZE;


    state.canvasCtx =
      canvas.getContext(
        '2d',
        {
          willReadFrequently: true
        }
      );


    /*
     * Try flash.
     */
    await enableTorch();


    /*
     * Wake screen.
     */
    await requestWakeLock();


    /*
     * Reset measurement.
     */
    resetEstimates();


    state.running =
      true;


    state.fingerActive =
      false;


    state.lastFingerSeen =
      0;


    state.lastSampleT =
      0;


    state.lastRed =
      0;


    updateMeasureButtons();


    setMeasureStatus(
      'Camera started. Place your fingertip over the rear camera and flash.'
    );


    /*
     * Start camera frame loop.
     */
    startFrameLoop();


    /*
     * BPM analysis timer.
     */
    state.analysisTimer =
      setInterval(
        processTick,
        ANALYSIS_INTERVAL_MS
      );


    /*
     * BLE sending timer.
     */
    state.sendTimer =
      setInterval(
        sendTick,
        500
      );


    log(
      'Measurement started'
    );


  } catch (error) {

    log(
      `Measurement failed: ${
        error?.message || error
      }`,
      'error'
    );


    showBanner(
      describeCameraError(
        error
      )
    );


    await stopMeasurement(
      false
    );
  }


  updateMeasureButtons();
}


/*
 * Stop measurement.
 */
async function stopMeasurement(
  wasRunning = true
) {

  state.running =
    false;


  state.loopId++;


  if (
    state.analysisTimer
  ) {

    clearInterval(
      state.analysisTimer
    );

    state.analysisTimer =
      null;
  }


  if (
    state.sendTimer
  ) {

    clearInterval(
      state.sendTimer
    );

    state.sendTimer =
      null;
  }


  /*
   * Turn flash off.
   */

  try {

    if (state.track) {

      await state.track.applyConstraints({
        advanced: [
          {
            torch: false
          }
        ]
      });
    }

  } catch (_) {}


  /*
   * Stop camera.
   */

  if (state.stream) {

    state.stream
      .getTracks()
      .forEach(
        track =>
          track.stop()
      );
  }


  state.stream =
    null;


  state.track =
    null;


  if (el.video) {

    el.video.srcObject =
      null;
  }


  /*
   * Release wake lock.
   */

  try {

    if (state.wakeLock) {

      await state.wakeLock.release();
    }

  } catch (_) {}


  state.wakeLock =
    null;


  state.fingerActive =
    false;


  state.quality =
    'NONE';


  resetEstimates();


  updateBpmDisplay();

  updateQualityChip();

  updateMeasureButtons();


  if (el.torchStatus) {

    el.torchStatus.textContent =
      'Flash: off';
  }


  if (el.redDebug) {

    el.redDebug.textContent =
      'Red level: --';
  }


  updateProgress(0);


  setMeasureStatus(
    'Camera is off. Press Start Measurement.'
  );


  if (wasRunning) {

    log(
      'Measurement stopped'
    );
  }
}


/*
 * Camera frame loop.
 */
function startFrameLoop() {

  const currentLoopId =
    ++state.loopId;


  const video =
    el.video;


  const useRVFC =
    typeof video.requestVideoFrameCallback ===
    'function';


  function loop() {

    if (
      !state.running ||
      currentLoopId !==
        state.loopId
    ) {

      return;
    }


    try {

      sampleFrame(
        performance.now()
      );

    } catch (error) {

      log(
        `Frame error: ${
          error?.message || error
        }`,
        'error'
      );
    }


    if (
      useRVFC
    ) {

      video.requestVideoFrameCallback(
        loop
      );

    } else {

      requestAnimationFrame(
        loop
      );
    }
  }


  if (
    useRVFC
  ) {

    video.requestVideoFrameCallback(
      loop
    );

  } else {

    requestAnimationFrame(
      loop
    );
  }
}


/*
 * Read one camera frame.
 */
function sampleFrame(
  now
) {

  const video =
    el.video;


  if (
    video.readyState < 2 ||
    !video.videoWidth
  ) {

    return;
  }


  /*
   * Limit sampling to roughly 30 FPS.
   */
  if (
    now -
    state.lastSampleT <
    15
  ) {

    return;
  }


  state.lastSampleT =
    now;


  const videoWidth =
    video.videoWidth;

  const videoHeight =
    video.videoHeight;


  /*
   * Centre ROI.
   */
  const cropWidth =
    videoWidth *
    ROI_FRACTION;


  const cropHeight =
    videoHeight *
    ROI_FRACTION;


  const cropX =
    (videoWidth -
      cropWidth) / 2;


  const cropY =
    (videoHeight -
      cropHeight) / 2;


  const ctx =
    state.canvasCtx;


  ctx.drawImage(

    video,

    cropX,
    cropY,

    cropWidth,
    cropHeight,

    0,
    0,

    SAMPLE_SIZE,
    SAMPLE_SIZE
  );


  const data =
    ctx.getImageData(
      0,
      0,
      SAMPLE_SIZE,
      SAMPLE_SIZE
    ).data;


  let r = 0;

  let g = 0;

  let b = 0;


  const pixelCount =
    SAMPLE_SIZE *
    SAMPLE_SIZE;


  for (
    let i = 0;
    i < data.length;
    i += 4
  ) {

    r += data[i];

    g += data[i + 1];

    b += data[i + 2];
  }


  r /= pixelCount;

  g /= pixelCount;

  b /= pixelCount;


  state.lastRed =
    r;


  if (el.redDebug) {

    el.redDebug.textContent =
      `Red level: ${Math.round(r)}`;
  }


  /*
   * Detect fingertip.
   */
  const fingerDetected =
    r >= FINGER_MIN_RED &&
    r > g * FINGER_RED_RATIO &&
    r > b * FINGER_RED_RATIO;


  if (
    fingerDetected
  ) {

    state.lastFingerSeen =
      now;


    /*
     * Finger just appeared.
     */

    if (
      !state.fingerActive
    ) {

      state.fingerActive =
        true;


      state.fingerSince =
        now;


      resetEstimates();


      log(
        'Finger detected'
      );
    }


    /*
     * Wait for auto-exposure to settle.
     */

    if (
      now -
      state.fingerSince >=
      SETTLE_MS
    ) {

      state.samples.push({
        t: now,
        v: r
      });


      /*
       * Keep roughly 11 seconds.
       */

      const cutoff =
        now -
        (
          WINDOW_SEC *
          1000 +
          1000
        );


      while (
        state.samples.length &&
        state.samples[0].t <
          cutoff
      ) {

        state.samples.shift();
      }
    }


  } else if (
    state.fingerActive &&
    now -
      state.lastFingerSeen >
      FINGER_LOST_MS
  ) {

    state.fingerActive =
      false;


    resetEstimates();


    log(
      'Finger removed'
    );
  }
}


/* ============================================================================
   8. BPM PROCESSING
   ============================================================================ */

function processTick() {

  if (
    !state.running
  ) {

    return;
  }


  const now =
    performance.now();


  if (el.redDebug) {

    el.redDebug.textContent =
      `Red level: ${Math.round(
        state.lastRed || 0
      )}`;
  }


  /*
   * No finger
   */

  if (
    !state.fingerActive
  ) {

    state.quality =
      'NO FINGER';


    state.displayedBpm =
      null;


    updateBpmDisplay();

    updateQualityChip();

    updateProgress(0);


    setMeasureStatus(
      'No finger detected. Cover both the rear camera and flash.'
    );


    return;
  }


  const sampleCount =
    state.samples.length;


  if (
    sampleCount < 2
  ) {

    state.quality =
      'WAIT';


    updateQualityChip();


    setMeasureStatus(
      'Finger detected - keep still...'
    );


    return;
  }


  /*
   * Measurement duration.
   */

  const lastSample =
    state.samples[
      sampleCount - 1
    ].t;


  const windowStart =
    Math.max(
      state.samples[0].t,
      lastSample -
        WINDOW_SEC * 1000
    );


  const duration =
    (
      lastSample -
      windowStart
    ) / 1000;


  updateProgress(
    (
      duration /
      MIN_ANALYSIS_SEC
    ) * 100
  );


  if (
    duration <
    MIN_ANALYSIS_SEC
  ) {

    state.quality =
      'WAIT';


    updateQualityChip();


    setMeasureStatus(
      `Measuring... ${Math.round(
        (
          duration /
          MIN_ANALYSIS_SEC
        ) * 100
      )}% - keep your finger still`
    );


    return;
  }


  /*
   * Resample.
   */

  const uniform =
    resampleUniform(
      state.samples,
      windowStart,
      lastSample,
      FS
    );


  if (
    uniform.length < 30
  ) {

    return;
  }


  /*
   * Filter.
   */

  const filtered =
    filterPulse(
      uniform,
      FS
    );


  /*
   * Analyze.
   */

  const result =
    analyzePulse(
      filtered,
      FS
    );


  /*
   * Draw waveform.
   */

  drawWave(
    filtered,
    result.peaks
  );


  state.quality =
    result.quality;


  /*
   * Good or fair result.
   */

  if (
    result.quality !== 'POOR' &&
    result.bpm !== null
  ) {

    state.lastGoodAt =
      now;


    state.estimates.push(
      result.bpm
    );


    /*
     * Keep recent estimates.
     */

    if (
      state.estimates.length > 6
    ) {

      state.estimates.shift();
    }


    /*
     * Stabilize BPM.
     */

    if (
      state.estimates.length >= 3
    ) {

      const minimum =
        Math.min(
          ...state.estimates
        );


      const maximum =
        Math.max(
          ...state.estimates
        );


      /*
       * Reject large jumps.
       */

      if (
        maximum -
          minimum <=
        10
      ) {

        const med =
          median(
            state.estimates
          );


        if (
          state.displayedBpm === null
        ) {

          state.displayedBpm =
            med;

        } else {

          state.displayedBpm =
            state.displayedBpm +
            0.3 *
            (
              med -
              state.displayedBpm
            );
        }
      }
    }


    if (
      state.displayedBpm !== null
    ) {

      setMeasureStatus(
        'Measuring live - keep finger still'
      );

    } else {

      setMeasureStatus(
        'Measuring - stabilising BPM...'
      );
    }


  } else {

    setMeasureStatus(
      `Signal unreliable${
        result.reason
          ? ` (${result.reason})`
          : ''
      }. Keep still and press gently.`
    );


    /*
     * If signal remains bad,
     * clear old BPM.
     */

    if (
      now -
        state.lastGoodAt >
      NO_GOOD_RESET_MS
    ) {

      state.displayedBpm =
        null;


      state.estimates =
        [];
    }
  }


  updateBpmDisplay();

  updateQualityChip();
}


/* ============================================================================
   9. SEND BPM TO ESP32
   ============================================================================ */

function sendableBpm() {

  if (
    !state.running
  ) {

    return null;
  }


  if (
    !state.fingerActive
  ) {

    return null;
  }


  if (
    state.quality !== 'GOOD' &&
    state.quality !== 'FAIR'
  ) {

    return null;
  }


  if (
    state.displayedBpm === null
  ) {

    return null;
  }


  const bpm =
    Math.round(
      state.displayedBpm
    );


  if (
    !isValidBpm(bpm)
  ) {

    return null;
  }


  return bpm;
}


/*
 * IMPORTANT:
 *
 * ESP32 receives:
 *
 * HR:78
 *
 * Nothing else.
 */
function buildPayload(
  bpm
) {

  return `HR:${bpm}`;
}


/*
 * Send BPM periodically.
 */
function sendTick() {

  if (
    !isBleConnected()
  ) {

    return;
  }


  const bpm =
    sendableBpm();


  if (
    bpm === null
  ) {

    return;
  }


  const now =
    performance.now();


  const timeSinceLastSend =
    now -
    state.lastSentAt;


  const changed =
    state.lastSentBpm === null ||
    Math.abs(
      bpm -
      state.lastSentBpm
    ) >=
    SEND_CHANGE_THRESHOLD;


  /*
   * Send:
   *
   * every 2 seconds
   *
   * OR
   *
   * when BPM changes significantly
   */

  if (
    timeSinceLastSend >=
      SEND_INTERVAL_MS ||
    (
      changed &&
      timeSinceLastSend >=
        SEND_MIN_GAP_MS
    )
  ) {

    const payload =
      buildPayload(
        bpm
      );


    state.lastSentAt =
      now;


    state.lastSentBpm =
      bpm;


    sendToEsp(
      payload
    );
  }
}


/* ============================================================================
   10. UTILITY
   ============================================================================ */

function sleep(
  milliseconds
) {

  return new Promise(
    resolve =>
      setTimeout(
        resolve,
        milliseconds
      )
  );
}


/* ============================================================================
   11. INITIALIZATION
   ============================================================================ */

function init() {

  /*
   * Find all HTML elements.
   */

  ELEMENT_IDS.forEach(
    id => {

      el[id] =
        document.getElementById(
          id
        );
    }
  );


  /*
   * Buttons
   */

  if (el.btnConnect) {

    el.btnConnect.addEventListener(
      'click',
      () =>
        onConnectClick(false)
    );
  }


  if (el.btnConnectAll) {

    el.btnConnectAll.addEventListener(
      'click',
      () =>
        onConnectClick(true)
    );
  }


  if (el.btnDisconnect) {

    el.btnDisconnect.addEventListener(
      'click',
      onDisconnectClick
    );
  }


  if (el.btnStart) {

    el.btnStart.addEventListener(
      'click',
      startMeasurement
    );
  }


  if (el.btnStop) {

    el.btnStop.addEventListener(
      'click',
      () =>
        stopMeasurement(true)
    );
  }


  /*
   * Clear log.
   */

  if (el.btnClearLog) {

    el.btnClearLog.addEventListener(
      'click',
      () => {

        if (el.logBox) {

          el.logBox.textContent =
            '';
        }
      }
    );
  }


  /*
   * Stop measurement if page becomes hidden.
   */

  document.addEventListener(
    'visibilitychange',
    () => {

      if (
        document.hidden &&
        state.running
      ) {

        stopMeasurement(true);


        showBanner(
          'Measurement stopped because the page was hidden.'
        );
      }
    }
  );


  /*
   * Initial UI.
   */

  updateBleButtons();

  updateMeasureButtons();

  updateQualityChip();

  updateBpmDisplay();


  /*
   * Environment checks.
   */

  if (
    !window.isSecureContext
  ) {

    showBanner(
      'This page must be served over HTTPS for camera and Bluetooth.'
    );


  } else if (
    !navigator.bluetooth
  ) {

    showBanner(
      'Web Bluetooth is unavailable. Use Chrome on Android.'
    );
  }


  log(
    'PulseLink ready'
  );


  log(
    `BLE device: ${BLE_DEVICE_NAME}`
  );


  log(
    `Service UUID: ${BLE_SERVICE_UUID}`
  );


  log(
    'Waiting for ESP32 connection...'
  );
}


/*
 * Start application.
 */

if (
  typeof document !==
  'undefined'
) {

  if (
    document.readyState ===
    'loading'
  ) {

    document.addEventListener(
      'DOMContentLoaded',
      init
    );

  } else {

    init();
  }
}


/* ============================================================================
   12. NODE TEST EXPORTS
   ============================================================================ */

if (
  typeof module !== 'undefined' &&
  module.exports
) {

  module.exports = {

    mean,

    stdDev,

    median,

    movingAverage,

    resampleUniform,

    filterPulse,

    findPeaks,

    autocorrAt,

    periodicityScore,

    analyzePulse,

    isValidBpm,

    FS
  };
}