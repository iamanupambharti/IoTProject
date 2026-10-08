/* ============================================================================
   ESP32 HEALTH MONITOR - phone web app (plain JavaScript, no frameworks)
   ============================================================================
   Data flow:
     Finger -> phone camera + flash -> PPG signal -> filtering -> peak detection
     -> BPM -> Web Bluetooth (BLE) -> ESP32 -> OLED

   Sections:
     1. Settings (constants you can tweak)
     2. Pure signal-processing + BP helper functions (no DOM, unit-testable)
     3. App state + small UI helpers
     4. Bluetooth (connect, write, auto-reconnect)
     5. Camera + PPG measurement
     6. BP demonstration + sending data
     7. Initialisation

   IMPORTANT: educational prototype only. Camera BPM is an estimate and BP here
   is a demonstration status based on numbers typed in by the user.
   ============================================================================ */
'use strict';

/* ============================================================================
   1. SETTINGS
   ============================================================================ */

// ---- BLE (must match the ESP32 sketch) ----
const BLE_DEVICE_NAME = 'PulseLink';
const BLE_SERVICE_UUID          = '4fafc201-1fb5-459e-8fcc-c5c9c331914b';
const BLE_CHARACTERISTIC_UUID   = 'beb5483e-36e1-4688-b7f5-ea07361b26a8';
const BLE_RECONNECT_ATTEMPTS    = 5;
const BLE_RECONNECT_DELAY_MS    = 2000;

// ---- What BPM values are allowed to be displayed / sent ----
const BPM_MIN_VALID             = 40;
const BPM_MAX_VALID             = 180;

// ---- Sending to ESP32 ----
const SEND_INTERVAL_MS          = 2000;  // send at least this often while BPM is stable
const SEND_MIN_GAP_MS           = 1000;  // never send faster than this
const SEND_CHANGE_THRESHOLD     = 5;     // send early if BPM changed by >= this many BPM

// ---- Signal processing ----
const FS                        = 30;    // analysis sample rate (Hz) after resampling
const WINDOW_SEC                = 10;    // length of analysis window
const MIN_ANALYSIS_SEC          = 6;     // need this much data before first BPM
const SETTLE_MS                 = 1500;  // ignore first moments after finger appears (auto-exposure settling)
const ANALYSIS_INTERVAL_MS      = 500;   // how often BPM is recomputed
const FINGER_LOST_MS            = 600;   // finger considered removed after this long
const NO_GOOD_RESET_MS          = 5000;  // clear BPM if no good estimate for this long
const MIN_SIGNAL_STD            = 0.02;  // below this the signal is "flat" (no pulse)
const BASELINE_SEC              = 1.5;   // drift-removal window (must be longer than one heartbeat)
const PERIODICITY_GOOD          = 0.70;  // heartbeat repeat strength needed for GOOD (0..1)
const PERIODICITY_FAIR          = 0.55;  // ... and for FAIR (noise stays below ~0.45)
const WAVE_SEC                  = 6;     // seconds of waveform to draw

// ---- Fingertip region + detection ----
const ROI_FRACTION              = 0.5;   // centre 50% of the frame is analysed
const SAMPLE_SIZE               = 48;    // pixels (square) read from the video each frame
const FINGER_MIN_RED            = 80;    // minimum average red (0-255)
const FINGER_RED_RATIO          = 1.3;   // red must exceed green and blue by this factor

// ---- BP demonstration thresholds (simplified; NOT diagnostic) ----
const BP_LOW_SYS                = 90;    // sys <  90  or dia < 60  -> LOW
const BP_LOW_DIA                = 60;
const BP_HIGH_SYS               = 140;   // sys >= 140 or dia >= 90 -> HIGH
const BP_HIGH_DIA               = 90;
const BP_INPUT_SYS_MIN          = 60,  BP_INPUT_SYS_MAX = 250;
const BP_INPUT_DIA_MIN          = 30,  BP_INPUT_DIA_MAX = 150;

/* ============================================================================
   2. PURE HELPER FUNCTIONS (no DOM access)
   ============================================================================ */

function mean(arr) {
  if (!arr.length) return 0;
  let s = 0;
  for (let i = 0; i < arr.length; i++) s += arr[i];
  return s / arr.length;
}

function stdDev(arr, m) {
  if (arr.length < 2) return 0;
  let s = 0;
  for (let i = 0; i < arr.length; i++) {
    const d = arr[i] - m;
    s += d * d;
  }
  return Math.sqrt(s / arr.length);
}

function median(arr) {
  const s = Array.from(arr).sort((a, b) => a - b);
  const mid = Math.floor(s.length / 2);
  return s.length % 2 ? s[mid] : (s[mid - 1] + s[mid]) / 2;
}

/** Centred moving average; the window shrinks at the edges. */
function movingAverage(x, win) {
  const n = x.length;
  const out = new Float32Array(n);
  const half = Math.floor(win / 2);
  const prefix = new Float64Array(n + 1);
  for (let i = 0; i < n; i++) prefix[i + 1] = prefix[i] + x[i];
  for (let i = 0; i < n; i++) {
    const a = Math.max(0, i - half);
    const b = Math.min(n - 1, i + half);
    out[i] = (prefix[b + 1] - prefix[a]) / (b - a + 1);
  }
  return out;
}

/**
 * The camera delivers frames at irregular times. Linear interpolation turns the
 * list of {t, v} samples into an evenly spaced signal at `fs` Hz.
 * Requires samples.length >= 2.
 */
function resampleUniform(samples, startT, endT, fs) {
  const n = Math.max(0, Math.floor(((endT - startT) / 1000) * fs));
  const out = new Float32Array(n);
  let j = 0;
  for (let i = 0; i < n; i++) {
    const t = startT + (i * 1000) / fs;
    while (j < samples.length - 2 && samples[j + 1].t < t) j++;
    const a = samples[j];
    const b = samples[j + 1];
    const span = b.t - a.t;
    let f = span > 0 ? (t - a.t) / span : 0;
    f = f < 0 ? 0 : (f > 1 ? 1 : f);
    out[i] = a.v + (b.v - a.v) * f;
  }
  return out;
}

/**
 * Turn the raw red-channel signal into a clean pulse waveform:
 *   1. subtract a ~1.5 s moving average (removes slow drift / brightness changes)
 *   2. invert (blood absorbs red light, so red DROPS when the pulse arrives)
 *   3. smooth with a 5-sample moving average (removes high-frequency noise)
 */
function filterPulse(x, fs) {
  const baseWin = Math.round(fs * BASELINE_SEC) | 1;   // odd number of samples
  const baseline = movingAverage(x, baseWin);
  const hp = new Float32Array(x.length);
  for (let i = 0; i < x.length; i++) hp[i] = baseline[i] - x[i];
  return movingAverage(hp, 5);
}

/** Local maxima above `threshold`, at least `minDistSec` apart (keeps the taller one). */
function findPeaks(x, fs, minDistSec, threshold) {
  const minDist = Math.max(1, Math.round(minDistSec * fs));
  const peaks = [];
  for (let i = 1; i < x.length - 1; i++) {
    if (x[i] > threshold && x[i] > x[i - 1] && x[i] >= x[i + 1]) {
      if (peaks.length && i - peaks[peaks.length - 1] < minDist) {
        if (x[i] > x[peaks[peaks.length - 1]]) peaks[peaks.length - 1] = i;
      } else {
        peaks.push(i);
      }
    }
  }
  return peaks;
}

/**
 * Normalised autocorrelation of x (mean removed) at one lag. A real pulse repeats
 * itself every heartbeat, so the value is high (close to 1) at the heartbeat lag;
 * random noise gives a low value.
 */
function autocorrAt(x, lag) {
  const n = x.length;
  if (lag <= 0 || lag >= n - 2) return 0;
  const m = mean(x);
  let num = 0, den = 0;
  for (let i = 0; i < n; i++) { const d = x[i] - m; den += d * d; }
  for (let i = 0; i + lag < n; i++) num += (x[i] - m) * (x[i + lag] - m);
  if (den <= 0) return 0;
  return (num / (n - lag)) / (den / n);       // unbiased normalisation
}

/** Best autocorrelation within +-2 samples of the expected heartbeat period. */
function periodicityScore(x, periodSamples) {
  const c = Math.round(periodSamples);
  let best = -1;
  for (let l = c - 2; l <= c + 2; l++) best = Math.max(best, autocorrAt(x, l));
  return best;
}

/**
 * Estimate BPM from a filtered pulse waveform.
 * Returns { bpm, quality: 'GOOD'|'FAIR'|'POOR', peaks, reason }.
 * `peaks` are indices into `filtered` (for drawing).
 */
function analyzePulse(filtered, fs) {
  const poor = (reason, extra) => Object.assign({ bpm: null, quality: 'POOR', peaks: [], reason }, extra || {});

  const trim = Math.round(0.3 * fs);                 // drop filter edge effects
  if (filtered.length < fs * 3 + 2 * trim) return poor('not enough data');
  const seg = filtered.subarray(trim, filtered.length - trim);

  const m = mean(seg);
  const sd = stdDev(seg, m);
  if (sd < MIN_SIGNAL_STD) return poor('signal flat (press more gently / check flash)', { std: sd });

  const minDistSec = 60 / BPM_MAX_VALID;
  const rawPeaks = findPeaks(seg, fs, minDistSec, m + 0.2 * sd);
  const peaks = rawPeaks.map(i => i + trim);

  // Intervals between neighbouring peaks, in seconds
  const minInt = 60 / BPM_MAX_VALID;
  const maxInt = 60 / BPM_MIN_VALID;
  const intervals = [];
  for (let k = 1; k < rawPeaks.length; k++) {
    const dt = (rawPeaks[k] - rawPeaks[k - 1]) / fs;
    if (dt >= minInt && dt <= maxInt) intervals.push(dt);
  }
  if (intervals.length < 3) return poor('too few pulses found', { peaks, std: sd });

  // Keep only intervals close to the median (rejects missed / extra peaks)
  const med = median(intervals);
  const kept = intervals.filter(v => Math.abs(v - med) <= 0.2 * med);
  const consistency = kept.length / intervals.length;
  if (kept.length < 3) return poor('pulse rhythm not consistent', { peaks, std: sd });

  const keptMean = mean(kept);
  const cv = stdDev(kept, keptMean) / keptMean;
  const bpm = 60 / keptMean;
  const periodicity = periodicityScore(seg, keptMean * fs);

  let quality = 'POOR';
  if (kept.length >= 6 && consistency >= 0.75 && cv <= 0.10 && periodicity >= PERIODICITY_GOOD) quality = 'GOOD';
  else if (kept.length >= 4 && consistency >= 0.60 && cv <= 0.18 && periodicity >= PERIODICITY_FAIR) quality = 'FAIR';

  if (!(bpm >= BPM_MIN_VALID && bpm <= BPM_MAX_VALID)) {
    return poor('BPM out of range', { peaks, std: sd });
  }
  return { bpm, quality, peaks, reason: '', std: sd, cv, consistency, periodicity, pulses: kept.length };
}

/** Is this a BPM value we are willing to display / send? */
function isValidBpm(v) {
  return Number.isInteger(v) && v >= BPM_MIN_VALID && v <= BPM_MAX_VALID;
}

/** Validate typed BP numbers. Returns { ok, sys, dia, error }. */
function validateBpInputs(sysText, diaText) {
  const sys = parseInt(sysText, 10);
  const dia = parseInt(diaText, 10);
  if (!Number.isFinite(sys) || !Number.isFinite(dia)) {
    return { ok: false, error: 'Enter both Systolic and Diastolic values.' };
  }
  if (sys < BP_INPUT_SYS_MIN || sys > BP_INPUT_SYS_MAX) {
    return { ok: false, error: `Systolic must be between ${BP_INPUT_SYS_MIN} and ${BP_INPUT_SYS_MAX}.` };
  }
  if (dia < BP_INPUT_DIA_MIN || dia > BP_INPUT_DIA_MAX) {
    return { ok: false, error: `Diastolic must be between ${BP_INPUT_DIA_MIN} and ${BP_INPUT_DIA_MAX}.` };
  }
  if (sys <= dia) {
    return { ok: false, error: 'Systolic must be greater than Diastolic.' };
  }
  return { ok: true, sys, dia };
}

/** Demonstration classification only - NOT a diagnosis. */
function classifyBp(sys, dia) {
  if (sys < BP_LOW_SYS || dia < BP_LOW_DIA) return 'LOW';
  if (sys >= BP_HIGH_SYS || dia >= BP_HIGH_DIA) return 'HIGH';
  return 'NORMAL';
}

function sleep(ms) {
  return new Promise(resolve => setTimeout(resolve, ms));
}

/* ============================================================================
   3. APP STATE + UI HELPERS
   ============================================================================ */

const el = {};   // filled in init() with references to HTML elements
const ELEMENT_IDS = [
  'banner', 'bleDot', 'bleStatus', 'btnConnect', 'btnDisconnect', 'btnConnectAll',
  'btnStart', 'btnStop', 'bpmValue', 'qualityChip', 'measureStatus', 'progress',
  'wave', 'video', 'sampleCanvas', 'torchStatus', 'redDebug',
  'inpSys', 'inpDia', 'btnSendHealth', 'bpResult', 'bpMessage', 'logBox', 'btnClearLog'
];

const state = {
  // ---- camera / measurement ----
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
  samples: [],               // [{t: ms, v: red value}]
  estimates: [],             // recent raw BPM estimates
  displayedBpm: null,        // smoothed BPM shown to the user (float or null)
  quality: 'NONE',           // NONE | NO FINGER | WAIT | POOR | FAIR | GOOD
  lastGoodAt: 0,
  // ---- bluetooth ----
  device: null,
  characteristic: null,
  userDisconnected: false,
  reconnecting: false,
  writeChain: Promise.resolve(),
  lastSentAt: -Infinity,
  lastSentBpm: null,
  // ---- BP demo ----
  bpStatus: null             // 'LOW' | 'NORMAL' | 'HIGH' | null
};

function log(message, level) {
  const time = new Date().toLocaleTimeString();
  const prefix = level === 'error' ? '[ERROR] ' : '';
  el.logBox.textContent += `${time}  ${prefix}${message}\n`;
  // keep the log short
  const lines = el.logBox.textContent.split('\n');
  if (lines.length > 120) el.logBox.textContent = lines.slice(lines.length - 100).join('\n');
  el.logBox.scrollTop = el.logBox.scrollHeight;
  if (level === 'error') console.error(message); else console.log(message);
}

function showBanner(message, type) {
  el.banner.textContent = message;
  el.banner.className = 'banner' + (type === 'info' ? ' info' : '');
}

function hideBanner() {
  el.banner.className = 'banner hidden';
  el.banner.textContent = '';
}

function setBleStatus(text, kind) {
  el.bleStatus.textContent = text;
  el.bleDot.className = 'dot' + (kind ? ' ' + kind : '');
}

/* ============================================================================
   4. BLUETOOTH
   ============================================================================ */

function isBleConnected() {
  return !!(state.device && state.device.gatt && state.device.gatt.connected && state.characteristic);
}

function updateBleButtons() {
  const connected = isBleConnected();
  el.btnConnect.disabled = connected || state.reconnecting;
  el.btnConnectAll.disabled = connected || state.reconnecting;
  el.btnDisconnect.disabled = !connected && !state.reconnecting;
}

async function onConnectClick(showAll) {
  hideBanner();
  if (!navigator.bluetooth) {
    showBanner('Web Bluetooth is not available in this browser. Use Chrome (or Edge) on Android, opened over HTTPS.');
    log('Web Bluetooth not supported', 'error');
    return;
  }
  if (!window.isSecureContext) {
    showBanner('Web Bluetooth needs a secure page (HTTPS or localhost). See the README for how to host this page.');
    return;
  }

  state.userDisconnected = false;
  try {
    setBleStatus('Searching for ESP32...', 'busy');
    log(showAll ? 'Scanning for all BLE devices...' : `Scanning for "${BLE_DEVICE_NAME}"...`);

    const options = showAll
      ? { acceptAllDevices: true, optionalServices: [BLE_SERVICE_UUID] }
      : { filters: [{ name: BLE_DEVICE_NAME }, { services: [BLE_SERVICE_UUID] }],
          optionalServices: [BLE_SERVICE_UUID] };

    const device = await navigator.bluetooth.requestDevice(options);
    state.device = device;
    device.removeEventListener('gattserverdisconnected', onGattDisconnected);
    device.addEventListener('gattserverdisconnected', onGattDisconnected);
    log(`Selected device: ${device.name || '(unnamed)'}`);

    await connectGatt();
  } catch (err) {
    handleBleError(err);
  }
  updateBleButtons();
}

async function connectGatt() {
  setBleStatus('Connecting to ESP32...', 'busy');
  try {
    const server = await state.device.gatt.connect();
    const service = await server.getPrimaryService(BLE_SERVICE_UUID);
    const ch = await service.getCharacteristic(BLE_CHARACTERISTIC_UUID);
    if (!(ch.properties.write || ch.properties.writeWithoutResponse)) {
      throw new Error('The characteristic is not writable. Check the ESP32 sketch.');
    }
    state.characteristic = ch;
    state.lastSentAt = -Infinity;
    state.lastSentBpm = null;
    setBleStatus('ESP32 Connected', 'ok');
    log('ESP32 Connected (service + characteristic found)');
  } catch (err) {
    state.characteristic = null;
    try { if (state.device && state.device.gatt.connected) state.device.gatt.disconnect(); } catch (e) { /* ignore */ }
    throw err;
  }
  updateBleButtons();
}

function handleBleError(err) {
  const name = err && err.name ? err.name : 'Error';
  const msg = err && err.message ? err.message : String(err);
  log(`BLE error: ${name}: ${msg}`, 'error');
  state.characteristic = null;

  if (name === 'NotFoundError' && /cancel/i.test(msg)) {
    setBleStatus('Not connected', '');
    showBanner('No device was selected. Make sure the ESP32 is powered, then try again (or use "Show all BLE devices").', 'info');
  } else if (name === 'NotFoundError') {
    setBleStatus('ESP32 service not found', 'error');
    showBanner('Connected, but the health-monitor service was not found. Re-upload the ESP32 sketch and check the UUIDs.');
  } else if (name === 'SecurityError') {
    setBleStatus('Bluetooth blocked', 'error');
    showBanner('Bluetooth access was blocked. Use HTTPS, allow Bluetooth/Nearby devices permission, and turn Bluetooth ON.');
  } else if (name === 'NetworkError') {
    setBleStatus('Connection failed', 'error');
    showBanner('Could not connect. Move closer, make sure no other phone/app (e.g. nRF Connect) is connected to the ESP32, press the ESP32 EN button, and try again.');
  } else if (name === 'NotSupportedError') {
    setBleStatus('Not supported', 'error');
    showBanner('Bluetooth is not supported or is turned off on this phone.');
  } else {
    setBleStatus('Connection error', 'error');
    showBanner(`Bluetooth error: ${msg}`);
  }
}

async function onGattDisconnected() {
  log('ESP32 disconnected', 'error');
  state.characteristic = null;
  updateBleButtons();
  if (state.userDisconnected) {
    setBleStatus('Not connected', '');
    return;
  }
  setBleStatus('Disconnected - reconnecting...', 'busy');
  autoReconnect();
}

async function autoReconnect() {
  if (state.reconnecting) return;
  state.reconnecting = true;
  updateBleButtons();

  for (let attempt = 1; attempt <= BLE_RECONNECT_ATTEMPTS; attempt++) {
    if (state.userDisconnected || !state.device) break;
    setBleStatus(`Reconnecting (${attempt}/${BLE_RECONNECT_ATTEMPTS})...`, 'busy');
    await sleep(BLE_RECONNECT_DELAY_MS);          // give the ESP32 time to advertise again
    if (state.userDisconnected) break;
    try {
      await connectGatt();
      state.reconnecting = false;
      log('Reconnected automatically');
      updateBleButtons();
      return;
    } catch (err) {
      log(`Reconnect attempt ${attempt} failed: ${err && err.message ? err.message : err}`, 'error');
    }
  }

  state.reconnecting = false;
  if (!state.userDisconnected) {
    setBleStatus('Disconnected', 'error');
    showBanner('Automatic reconnect failed. Press "Connect ESP32" to connect again.');
  }
  updateBleButtons();
}

function onDisconnectClick() {
  state.userDisconnected = true;
  state.reconnecting = false;
  try {
    if (state.device && state.device.gatt.connected) state.device.gatt.disconnect();
  } catch (e) { /* ignore */ }
  state.characteristic = null;
  setBleStatus('Not connected', '');
  log('Disconnected by user');
  updateBleButtons();
}

/** Low-level write of a text message to the ESP32 characteristic. */
async function writeCharacteristic(text) {
  const data = new TextEncoder().encode(text);
  const ch = state.characteristic;
  if (ch.properties.write && typeof ch.writeValueWithResponse === 'function') {
    await ch.writeValueWithResponse(data);
  } else if (ch.properties.writeWithoutResponse && typeof ch.writeValueWithoutResponse === 'function') {
    await ch.writeValueWithoutResponse(data);
  } else {
    await ch.writeValue(data);
  }
}

/**
 * Queue a message to the ESP32. Writes are executed one after another because
 * Web Bluetooth only allows one GATT operation at a time.
 * Always resolves (true = sent, false = not sent).
 */
function sendToEsp(text) {
  const job = state.writeChain.then(async () => {
    if (!isBleConnected()) return false;
    try {
      await writeCharacteristic(text);
      log(`Sent -> ${text}`);
      return true;
    } catch (err) {
      log(`BLE write failed: ${err && err.message ? err.message : err}`, 'error');
      return false;
    }
  });
  state.writeChain = job;
  return job;
}

/* ============================================================================
   5. CAMERA + PPG MEASUREMENT
   ============================================================================ */

function setMeasureStatus(text) {
  el.measureStatus.textContent = text;
}

function updateQualityChip() {
  const q = state.quality;
  let cls = 'none';
  let text = '--';
  if (q === 'GOOD') { cls = 'good'; text = 'GOOD'; }
  else if (q === 'FAIR') { cls = 'fair'; text = 'FAIR'; }
  else if (q === 'POOR') { cls = 'poor'; text = 'POOR'; }
  else if (q === 'WAIT') { cls = 'none'; text = 'MEASURING...'; }
  else if (q === 'NO FINGER') { cls = 'none'; text = 'NO FINGER'; }
  el.qualityChip.className = 'chip ' + cls;
  el.qualityChip.textContent = 'Signal Quality: ' + text;
}

function updateBpmDisplay() {
  el.bpmValue.textContent = state.displayedBpm == null ? '--' : String(Math.round(state.displayedBpm));
}

function resetEstimates() {
  state.samples = [];
  state.estimates = [];
  state.displayedBpm = null;
  state.lastGoodAt = performance.now();
  el.progress.value = 0;
  clearWave();
}

function clearWave() {
  const c = el.wave;
  const ctx = c.getContext('2d');
  ctx.setTransform(1, 0, 0, 1, 0, 0);
  ctx.clearRect(0, 0, c.width, c.height);
}

function drawWave(filtered, peaks) {
  const c = el.wave;
  const dpr = window.devicePixelRatio || 1;
  const w = c.clientWidth;
  const h = c.clientHeight;
  if (c.width !== Math.round(w * dpr) || c.height !== Math.round(h * dpr)) {
    c.width = Math.round(w * dpr);
    c.height = Math.round(h * dpr);
  }
  const ctx = c.getContext('2d');
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.clearRect(0, 0, w, h);

  const N = Math.min(filtered.length, WAVE_SEC * FS);
  if (N < 2) return;
  const start = filtered.length - N;

  let maxAbs = 1e-6;
  for (let i = start; i < filtered.length; i++) maxAbs = Math.max(maxAbs, Math.abs(filtered[i]));

  const xAt = i => ((i - start) / (N - 1)) * (w - 8) + 4;
  const yAt = v => h / 2 - (v / maxAbs) * (h / 2 - 8);

  ctx.strokeStyle = '#38bdf8';
  ctx.lineWidth = 2;
  ctx.beginPath();
  for (let i = start; i < filtered.length; i++) {
    const x = xAt(i);
    const y = yAt(filtered[i]);
    if (i === start) ctx.moveTo(x, y); else ctx.lineTo(x, y);
  }
  ctx.stroke();

  ctx.fillStyle = '#ef4444';
  for (const p of peaks) {
    if (p < start) continue;
    ctx.beginPath();
    ctx.arc(xAt(p), yAt(filtered[p]), 3.5, 0, Math.PI * 2);
    ctx.fill();
  }
}

function updateMeasureButtons() {
  el.btnStart.disabled = state.running;
  el.btnStop.disabled = !state.running;
}

function describeCameraError(err) {
  const name = err && err.name ? err.name : 'Error';
  if (name === 'NotAllowedError' || name === 'PermissionDeniedError') {
    return 'Camera permission was denied. Allow camera access for this site in the browser settings, then try again.';
  }
  if (name === 'NotFoundError' || name === 'DevicesNotFoundError') {
    return 'No camera was found on this device.';
  }
  if (name === 'NotReadableError' || name === 'TrackStartError') {
    return 'The camera is in use by another app. Close other apps that use the camera and try again.';
  }
  if (name === 'SecurityError') {
    return 'The browser blocked camera access. Open this page over HTTPS.';
  }
  return `Camera error: ${name}${err && err.message ? ' - ' + err.message : ''}`;
}

async function getCameraStream() {
  const attempts = [
    { video: { facingMode: { ideal: 'environment' }, width: { ideal: 640 }, height: { ideal: 480 }, frameRate: { ideal: 30 } }, audio: false },
    { video: { facingMode: 'environment' }, audio: false },
    { video: true, audio: false }
  ];
  let lastErr = null;
  for (const constraints of attempts) {
    try {
      return await navigator.mediaDevices.getUserMedia(constraints);
    } catch (err) {
      lastErr = err;
      // Permission problems will not be fixed by simpler constraints
      if (err && (err.name === 'NotAllowedError' || err.name === 'SecurityError' || err.name === 'NotReadableError')) throw err;
    }
  }
  throw lastErr;
}

async function enableTorch() {
  const track = state.track;
  const readCaps = () => {
    try { return track.getCapabilities ? track.getCapabilities() : {}; } catch (e) { return {}; }
  };
  let caps = readCaps();
  if (!caps.torch) {            // capabilities can appear a moment late
    await sleep(500);
    caps = readCaps();
  }
  if (!caps.torch) {
    el.torchStatus.textContent = 'Flash: NOT available on this camera/browser';
    showBanner('The camera flash cannot be controlled by this browser. Measure in a bright place and cover the camera fully with your fingertip, or try another phone/browser.', 'info');
    log('Torch not supported', 'error');
    return false;
  }
  try {
    await track.applyConstraints({ advanced: [{ torch: true }] });
    el.torchStatus.textContent = 'Flash: ON';
    log('Flash (torch) ON');
    return true;
  } catch (err) {
    el.torchStatus.textContent = 'Flash: could not be turned on';
    log(`Torch error: ${err && err.message ? err.message : err}`, 'error');
    return false;
  }
}

async function requestWakeLock() {
  try {
    if ('wakeLock' in navigator) {
      state.wakeLock = await navigator.wakeLock.request('screen');
    }
  } catch (e) { /* not important */ }
}

async function startMeasurement() {
  if (state.running) return;
  hideBanner();

  if (!window.isSecureContext) {
    showBanner('The camera needs a secure page (HTTPS or localhost). See the README for how to host this page.');
    return;
  }
  if (!navigator.mediaDevices || !navigator.mediaDevices.getUserMedia) {
    showBanner('This browser does not support camera access (getUserMedia). Use Chrome on Android.');
    return;
  }

  setMeasureStatus('Requesting camera permission...');
  el.btnStart.disabled = true;

  try {
    state.stream = await getCameraStream();
  } catch (err) {
    const msg = describeCameraError(err);
    showBanner(msg);
    log(msg, 'error');
    setMeasureStatus('Camera is off. Press "Start Measurement".');
    updateMeasureButtons();
    return;
  }

  try {
    el.video.srcObject = state.stream;
    await el.video.play();
  } catch (err) {
    log(`Video play error: ${err && err.message ? err.message : err}`, 'error');
  }

  state.track = state.stream.getVideoTracks()[0];
  state.track.addEventListener('ended', () => {
    if (state.running) {
      showBanner('The camera stopped unexpectedly. Press "Start Measurement" to try again.');
      stopMeasurement();
    }
  });

  state.canvasCtx = el.sampleCanvas.getContext('2d', { willReadFrequently: true });
  el.sampleCanvas.width = SAMPLE_SIZE;
  el.sampleCanvas.height = SAMPLE_SIZE;

  await enableTorch();
  await requestWakeLock();

  state.running = true;
  state.fingerActive = false;
  state.lastSampleT = 0;
  state.quality = 'NO FINGER';
  resetEstimates();
  updateBpmDisplay();
  updateQualityChip();
  updateMeasureButtons();
  setMeasureStatus('Place your fingertip over the camera and flash.');
  log('Measurement started');

  startFrameLoop();
  state.analysisTimer = setInterval(processTick, ANALYSIS_INTERVAL_MS);
  state.sendTimer = setInterval(sendTick, 500);
}

async function stopMeasurement() {
  const wasRunning = state.running;
  state.running = false;
  state.loopId++;                                    // cancels the frame loop
  clearInterval(state.analysisTimer);
  clearInterval(state.sendTimer);
  state.analysisTimer = null;
  state.sendTimer = null;

  try {
    if (state.track) await state.track.applyConstraints({ advanced: [{ torch: false }] });
  } catch (e) { /* ignore */ }
  if (state.stream) state.stream.getTracks().forEach(t => t.stop());
  state.stream = null;
  state.track = null;
  el.video.srcObject = null;

  try { if (state.wakeLock) await state.wakeLock.release(); } catch (e) { /* ignore */ }
  state.wakeLock = null;

  state.fingerActive = false;
  state.quality = 'NONE';
  resetEstimates();
  updateBpmDisplay();
  updateQualityChip();
  updateMeasureButtons();
  el.torchStatus.textContent = 'Flash: off';
  el.redDebug.textContent = 'Red level: --';
  setMeasureStatus('Camera is off. Press "Start Measurement".');
  if (wasRunning) log('Measurement stopped');
}

/** Read frames as they arrive (requestVideoFrameCallback if available). */
function startFrameLoop() {
  const myId = ++state.loopId;
  const video = el.video;
  const useRvfc = typeof video.requestVideoFrameCallback === 'function';

  const loop = () => {
    if (!state.running || myId !== state.loopId) return;
    try {
      sampleFrame(performance.now());
    } catch (err) {
      log(`Frame error: ${err && err.message ? err.message : err}`, 'error');
    }
    if (useRvfc) video.requestVideoFrameCallback(loop);
    else requestAnimationFrame(loop);
  };

  if (useRvfc) video.requestVideoFrameCallback(loop);
  else requestAnimationFrame(loop);
}

/** Take one frame: average R, G, B over the centre of the image. */
function sampleFrame(now) {
  const v = el.video;
  if (v.readyState < 2 || !v.videoWidth) return;
  if (now - state.lastSampleT < 15) return;         // skip duplicate frames
  state.lastSampleT = now;

  const vw = v.videoWidth;
  const vh = v.videoHeight;
  const cw = vw * ROI_FRACTION;
  const ch = vh * ROI_FRACTION;
  const sx = (vw - cw) / 2;
  const sy = (vh - ch) / 2;

  const ctx = state.canvasCtx;
  ctx.drawImage(v, sx, sy, cw, ch, 0, 0, SAMPLE_SIZE, SAMPLE_SIZE);
  const data = ctx.getImageData(0, 0, SAMPLE_SIZE, SAMPLE_SIZE).data;

  let r = 0, g = 0, b = 0;
  const px = SAMPLE_SIZE * SAMPLE_SIZE;
  for (let i = 0; i < data.length; i += 4) {
    r += data[i];
    g += data[i + 1];
    b += data[i + 2];
  }
  r /= px; g /= px; b /= px;
  state.lastRed = r;

  const isFinger = r >= FINGER_MIN_RED && r > g * FINGER_RED_RATIO && r > b * FINGER_RED_RATIO;

  if (isFinger) {
    state.lastFingerSeen = now;
    if (!state.fingerActive) {                      // finger just appeared
      state.fingerActive = true;
      state.fingerSince = now;
      resetEstimates();
      log('Finger detected');
    }
    if (now - state.fingerSince >= SETTLE_MS) {
      state.samples.push({ t: now, v: r });
      const cutoff = now - (WINDOW_SEC * 1000 + 1000);
      while (state.samples.length && state.samples[0].t < cutoff) state.samples.shift();
    }
  } else if (state.fingerActive && now - state.lastFingerSeen > FINGER_LOST_MS) {
    state.fingerActive = false;                     // finger removed
    resetEstimates();
    log('Finger removed');
  }
}

/** Runs every 500 ms: filter, find pulses, estimate and smooth BPM. */
function processTick() {
  if (!state.running) return;
  const now = performance.now();
  el.redDebug.textContent = `Red level: ${Math.round(state.lastRed || 0)}`;

  if (!state.fingerActive) {
    state.quality = 'NO FINGER';
    state.displayedBpm = null;
    updateBpmDisplay();
    updateQualityChip();
    el.progress.value = 0;
    setMeasureStatus('No finger detected. Cover BOTH the rear camera and the flash with your fingertip.');
    return;
  }

  const n = state.samples.length;
  if (n < 2) {
    state.quality = 'WAIT';
    updateQualityChip();
    setMeasureStatus('Finger detected - keep still...');
    return;
  }

  const lastT = state.samples[n - 1].t;
  const winStart = Math.max(state.samples[0].t, lastT - WINDOW_SEC * 1000);
  const durSec = (lastT - winStart) / 1000;
  el.progress.value = Math.min(100, (durSec / MIN_ANALYSIS_SEC) * 100);

  if (durSec < MIN_ANALYSIS_SEC) {
    state.quality = 'WAIT';
    updateQualityChip();
    setMeasureStatus(`Measuring... ${Math.round(el.progress.value)}% - keep your finger still`);
    return;
  }

  // ----- signal processing -----
  const uniform = resampleUniform(state.samples, winStart, lastT, FS);
  const filtered = filterPulse(uniform, FS);
  const res = analyzePulse(filtered, FS);
  drawWave(filtered, res.peaks);

  state.quality = res.quality;

  if (res.quality !== 'POOR' && res.bpm !== null) {
    state.lastGoodAt = now;
    state.estimates.push(res.bpm);
    if (state.estimates.length > 6) state.estimates.shift();

    // Only accept a value when the recent estimates agree with each other
    if (state.estimates.length >= 3) {
      const mn = Math.min(...state.estimates);
      const mx = Math.max(...state.estimates);
      if (mx - mn <= 10) {
        const med = median(state.estimates);
        if (state.displayedBpm == null || Math.abs(med - state.displayedBpm) > 15) {
          state.displayedBpm = med;
        } else {
          state.displayedBpm = state.displayedBpm + 0.3 * (med - state.displayedBpm);   // gentle smoothing
        }
      }
    }
    setMeasureStatus(state.displayedBpm == null ? 'Measuring... stabilising' : 'Measuring (live) - keep still');
  } else {
    setMeasureStatus(`Signal unreliable${res.reason ? ' (' + res.reason + ')' : ''}. Keep still and press gently.`);
    if (now - state.lastGoodAt > NO_GOOD_RESET_MS) {
      state.displayedBpm = null;
      state.estimates = [];
    }
  }

  updateBpmDisplay();
  updateQualityChip();
}

/* ============================================================================
   6. SENDING DATA + BP DEMONSTRATION
   ============================================================================ */

/** The BPM we are allowed to send right now, or null. */
function sendableBpm() {
  if (!state.running || !state.fingerActive) return null;
  if (state.quality !== 'GOOD' && state.quality !== 'FAIR') return null;
  if (state.displayedBpm == null) return null;
  const bpm = Math.round(state.displayedBpm);
  return isValidBpm(bpm) ? bpm : null;
}

function buildPayload(bpm) {
const payload = `HR:${bpm}`;
  return payload;
}

/** Runs every 500 ms; decides whether it is time to send the BPM. */
function sendTick() {
  if (!isBleConnected()) return;
  const bpm = sendableBpm();
  if (bpm === null) return;

  const now = performance.now();
  const since = now - state.lastSentAt;
  const changed = state.lastSentBpm === null || Math.abs(bpm - state.lastSentBpm) >= SEND_CHANGE_THRESHOLD;

  if (since >= SEND_INTERVAL_MS || (changed && since >= SEND_MIN_GAP_MS)) {
    state.lastSentAt = now;
    state.lastSentBpm = bpm;
    sendToEsp(buildPayload(bpm));
  }
}

function setBpResult(status) {
  let cls = 'none';
  if (status === 'NORMAL') cls = 'good';
  else if (status === 'LOW') cls = 'fair';
  else if (status === 'HIGH') cls = 'poor';
  el.bpResult.className = 'chip ' + cls;
  el.bpResult.textContent = status || '--';
}

async function onSendHealthData() {
  el.bpMessage.textContent = '';
  const v = validateBpInputs(el.inpSys.value, el.inpDia.value);
  if (!v.ok) {
    el.bpMessage.textContent = v.error;
    return;
  }

  const status = classifyBp(v.sys, v.dia);
  state.bpStatus = status;
  setBpResult(status);
  log(`BP demo input ${v.sys}/${v.dia} -> ${status}`);

  if (!isBleConnected()) {
    el.bpMessage.textContent = 'Saved locally. Connect the ESP32 first so it can be sent.';
    return;
  }

  const bpm = sendableBpm();
  const payload = bpm !== null ? `HR:${bpm}` : null;
  if (!payload) return; 
  const ok = await sendToEsp(payload);
  el.bpMessage.textContent = ok
    ? `Sent "${payload}" to ESP32.` + (bpm === null ? ' (No stable heart rate yet, so only BP status was sent.)' : '')
    : 'Sending failed. Check the Bluetooth connection.';
}

/* ============================================================================
   7. INITIALISATION
   ============================================================================ */

function init() {
  ELEMENT_IDS.forEach(id => { el[id] = document.getElementById(id); });

  el.btnConnect.addEventListener('click', () => onConnectClick(false));
  el.btnConnectAll.addEventListener('click', () => onConnectClick(true));
  el.btnDisconnect.addEventListener('click', onDisconnectClick);
  el.btnStart.addEventListener('click', startMeasurement);
  el.btnStop.addEventListener('click', stopMeasurement);
  el.btnSendHealth.addEventListener('click', onSendHealthData);
  el.btnClearLog.addEventListener('click', () => { el.logBox.textContent = ''; });

  // The camera is paused by the browser when the page is hidden - stop cleanly.
  document.addEventListener('visibilitychange', () => {
    if (document.hidden && state.running) {
      stopMeasurement();
      showBanner('Measurement stopped because the page was hidden. Keep this page open while measuring.', 'info');
    }
  });

  updateBleButtons();
  updateMeasureButtons();
  updateQualityChip();
  updateBpmDisplay();
  setBpResult(null);

  // Early environment checks so the user sees problems immediately
  if (!window.isSecureContext) {
    showBanner('This page is not served over HTTPS, so camera and Bluetooth will NOT work. See the README for how to host it (GitHub Pages / Netlify / localhost).');
  } else if (!navigator.bluetooth) {
    showBanner('Web Bluetooth is not available in this browser. Use Chrome on Android. (iPhone/iOS browsers do not support Web Bluetooth.)');
  }

  log('App ready');
}

if (typeof document !== 'undefined') {
  document.addEventListener('DOMContentLoaded', init);
}

// Allows the pure functions to be unit-tested in Node (ignored in the browser).
if (typeof module !== 'undefined' && module.exports) {
  module.exports = {
    resampleUniform, filterPulse, analyzePulse, findPeaks, movingAverage, autocorrAt,
    classifyBp, validateBpInputs, isValidBpm, FS
  };
}
