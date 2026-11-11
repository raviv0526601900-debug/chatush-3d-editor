// סיור וירטואלי של STUDIO AI: הליכה במקלדת או במגע בתוך נכס שנבנה מסרטון רגיל.
// מועבר מ-videotour/tour/tour.js בלי לשנות את ההתנהגות. שלושה שינויים:
//   1. המסלול (רשימת החללים) נבנה משורות tour_places, או מ-tour_shared בקישור שיתוף, ולא מ-tour.json.
//   2. הקבצים (scene.ply ו-cameras.json של כל חלל) נטענים מהדלי tour-scenes כ-.ply ישיר.
//   3. טקסטים וצבעים של STUDIO AI, ו-Esc שולח chatush3d:close לאפליקציה שמסביב.
// כתובות:
//   view.html?embed=1&tour=<tour_id>   בתוך האפליקציה. ההתחברות מגיעה מהאפליקציה כטוקן גישה בלבד.
//   view.html?share=<share_token>      קישור שיתוף, בלי התחברות.
//   view.html?local=<dir>              בדיקה מקומית בלבד (localhost): ./data/<dir>/tour.json
// Each place is its own scene; moving on to the next one is a short fade.
import * as THREE from 'three';
import { SparkRenderer, SplatMesh } from '@sparkjsdev/spark';
import { SUPABASE_URL, SUPABASE_ANON } from '../js/config.js';

const V = (a) => new THREE.Vector3(a[0], a[1], a[2]);
const rad = THREE.MathUtils.degToRad;
const clamp = THREE.MathUtils.clamp;
const wrap = (a) => Math.atan2(Math.sin(a), Math.cos(a));
const q = new URLSearchParams(location.search);
const $ = (id) => document.getElementById(id);
const canvas = $('view');

// ---------- the app around the page ----------
const EMBED = q.get('embed') === '1' && window.parent !== window;
const APP_ORIGIN = /(^|\.)flutterflow\.app$|(^|\.)leaderbox\.online$|(^|\.)theouterspace\.online$|^localhost$|^127\.0\.0\.1$/;
const okOrigin = (o) => { try { return APP_ORIGIN.test(new URL(o).hostname); } catch (_) { return false; } };
function tellApp(msg) {
  try { (window.opener || (window.parent !== window ? window.parent : null))?.postMessage(msg, '*'); } catch (_) {}
}
const BUCKET = 'tour-scenes';
const LOCAL_HOST = /^(localhost|127\.0\.0\.1|\[::1\])$/.test(location.hostname);
const LOCAL = LOCAL_HOST && /^[\w-]+$/.test(q.get('local') || '') ? `./data/${q.get('local')}/` : null;

const loadingEl = $('loading'), loadingText = $('loadingText');
/** a message that stays on screen: the tour cannot be shown */
function fail(text) {
  loadingText.textContent = text;
  loadingEl.classList.add('error');
  loadingEl.classList.remove('done');
  throw new Error(text);
}
addEventListener('keydown', (e) => { if (e.key === 'Escape' && window.parent !== window) tellApp({ type: 'chatush3d:close' }); });

// The scene only exists where the camera looked. Unless ?free=1, the view may turn this far
// beyond the directions the camera faced around the current spot.
const FREE = q.has('free');
const PLAIN = q.has('plain');   // no backdrop and no edge reading (for measuring their cost)
const LOOK = rad(Number(q.get('look')) || 38);   // furthest turn past the headings the camera took
const TILT = rad(22);
const SLACK = rad(10);                           // spare width when fitting the view to what was filmed
const TURN = 1.3;   // rad / s

/** One place: the capture path of its scene and everything derived from it. */
class Place {
  /** skip: stretches of the clip (frame numbers [from, to]) left out of the walking path,
   *  for parts that did not rebuild well; the walk passes straight over them. */
  constructor(capture, skip = []) {
    const cams = capture.cams.filter((c) => !skip.some(([a, b]) => c.imgIdx >= a && c.imgIdx <= b))
      .sort((a, b) => a.imgIdx - b.imgIdx);
    const N = this.N = cams.length;
    this.P = cams.map((c) => V(c.pos));
    // camera axes in world space are the rows of R (world -> camera): right, down, forward
    // "Up": the average of the cameras' own up is biased whenever the camera tilts (a phone
    // panned around a room points slightly down, and the bias shows as a rolled horizon).
    // A level camera's right axis is horizontal whatever its tilt, so up is also the direction
    // the right axes avoid: up = (A + mu I)^-1 * meanUp, with A the spread of the right axes.
    const meanUp = cams.reduce((u, c) => u.sub(new THREE.Vector3(c.R[3], c.R[4], c.R[5])), new THREE.Vector3()).normalize();
    const A = [0.02, 0, 0, 0, 0.02, 0, 0, 0, 0.02];
    for (const c of cams) {
      for (let i = 0; i < 3; i++) for (let j = 0; j < 3; j++) A[i * 3 + j] += c.R[i] * c.R[j] / N;
    }
    this.up = meanUp.clone().applyMatrix3(new THREE.Matrix3().fromArray(A).invert()).normalize();
    const raw = cams.map((c) => new THREE.Vector3(c.R[6], c.R[7], c.R[8]));
    // forward directions smoothed over neighbours (an FPV drone twitches and banks)
    const w = Math.max(3, Math.round((capture.fps || 8) * 0.3));
    this.F = raw.map((_, i) => {
      const f = new THREE.Vector3();
      for (let k = Math.max(0, i - w); k <= Math.min(N - 1, i + w); k++) f.add(raw[k]);
      return f.normalize();
    });
    const diag = Math.max(new THREE.Box3().setFromPoints(this.P).getSize(new THREE.Vector3()).length(), 1e-6);
    const hops = this.P.slice(1).map((p, i) => p.distanceTo(this.P[i]));
    const step = hops.slice().sort((a, b) => a - b)[hops.length >> 1] || diag / 20;
    // cumulative distance along the path. A hop far longer than a normal step is where a
    // stretch was left out: it counts as three steps, so the walk glides across it quickly.
    this.D = [0];
    for (let i = 1; i < N; i++) this.D.push(this.D[i - 1] + (hops[i - 1] > step * 12 ? step * 3 : hops[i - 1]));
    this.pathLen = this.D[N - 1];
    this.diag = diag;
    this.step = step;
    const fps = capture.fps || 25 / 3;
    // scene units per second: a drone is fast, so walk at under half its speed
    this.walk = this.pathLen / (N / fps) * 0.45;
    this.leash = Math.max(diag * 0.12, step * 4);   // how far off the captured path one may wander
    const fy = cams[0].fy || cams[0].f;
    this.vfov = clamp(THREE.MathUtils.radToDeg(2 * Math.atan(capture.featH / 2 / fy)), 45, 65);
    // walking frame: e1 = first heading flattened, e2 = to its left
    this.e1 = this.F[0].clone().addScaledVector(this.up, -this.F[0].dot(this.up)).normalize();
    this.e2 = new THREE.Vector3().crossVectors(this.up, this.e1);
    this.camYaw = this.F.map((f) => Math.atan2(f.dot(this.e2), f.dot(this.e1)));
    this.camPitch = this.F.map((f) => Math.asin(clamp(f.dot(this.up), -1, 1)));
    // the lens: how wide and how tall one captured frame sees
    this.capH = 2 * Math.atan(capture.featW / 2 / cams[0].f);
    this.capV = 2 * Math.atan(capture.featH / 2 / fy);
    // how far the camera turned around a typical spot (a pan covers far more than one frame)
    const spans = this.P.map((p) => { const c = this.around(p); return c.hi - c.lo; }).sort((a, b) => a - b);
    this.span = spans[spans.length >> 1];
  }
  /** what the cameras near a point faced: the nearest camera, and the spread of headings
   *  (yaw relative to that camera, pitch absolute) among the cameras around it */
  around(p) {
    const i0 = this.nearest(p);
    let lo = 0, hi = 0, pLo = this.camPitch[i0], pHi = this.camPitch[i0];
    const r2 = (this.leash * 1.5) ** 2;
    for (let i = 0; i < this.N; i++) {
      if (this.P[i].distanceToSquared(p) > r2) continue;
      const d = wrap(this.camYaw[i] - this.camYaw[i0]);
      lo = Math.min(lo, d); hi = Math.max(hi, d);
      pLo = Math.min(pLo, this.camPitch[i]); pHi = Math.max(pHi, this.camPitch[i]);
    }
    return { i0, lo, hi, pLo, pHi };
  }
  /** pose on the path at distance d: position + smoothed forward */
  at(d) {
    const { P, F, D, N } = this;
    d = clamp(d, 0, this.pathLen);
    let i = 1;
    while (i < N - 1 && D[i] < d) i++;
    const t = (d - D[i - 1]) / (D[i] - D[i - 1] || 1);
    return { pos: P[i - 1].clone().lerp(P[i], t), fwd: F[i - 1].clone().lerp(F[i], t).normalize() };
  }
  /** index of the captured camera nearest to a point */
  nearest(p) {
    let best = 0, bd = Infinity;
    for (let i = 0; i < this.N; i++) { const d = this.P[i].distanceToSquared(p); if (d < bd) { bd = d; best = i; } }
    return best;
  }
}

// ---------- where the tour comes from ----------
/** The Supabase client for this visit: anonymous for a share link, the app's user inside the app. */
async function connect() {
  if (LOCAL) return null;
  if (!window.supabase) fail('טעינת הסיור נכשלה. נסו לרענן את הדף.');
  if (q.get('share')) {
    return window.supabase.createClient(SUPABASE_URL, SUPABASE_ANON, { auth: { persistSession: false, autoRefreshToken: false } });
  }
  if (!q.get('tour')) fail('הקישור לסיור לא שלם.');
  if (EMBED) {
    // the app hands over an access token only (never the refresh token) and renews it every few minutes
    let at = await new Promise((resolve) => {
      const on = (e) => {
        const d = e.data;
        if (!d || d.type !== 'chatush3d:token' || !d.access_token || !okOrigin(e.origin)) return;
        removeEventListener('message', on);
        resolve(d.access_token);
      };
      addEventListener('message', on);
      tellApp({ type: 'chatush3d:ready' });
      setTimeout(() => resolve(null), 8000);
    });
    if (!at) fail('לא התקבלה התחברות מהאפליקציה. סגרו את הסיור ופתחו אותו שוב.');
    addEventListener('message', (e) => {
      const d = e.data;
      if (d && d.type === 'chatush3d:token' && d.access_token && okOrigin(e.origin)) at = d.access_token;
    });
    return window.supabase.createClient(SUPABASE_URL, SUPABASE_ANON, { accessToken: async () => at });
  }
  // a separate window: the editor's saved sign-in on this site, if there is one
  const sb = window.supabase.createClient(SUPABASE_URL, SUPABASE_ANON, { auth: { persistSession: true, storageKey: 'chatush3d-auth' } });
  const { data } = await sb.auth.getSession();
  if (!data.session) fail('כדי לצפות בסיור מחוץ לאפליקציה צריך קישור שיתוף. יוצרים אותו בלשונית "סיור וירטואלי" בפרויקט.');
  return sb;
}

/** The route: { title, sub, scenes: [{ id, order, title, start, skip, bg, ply, cameras }] } */
async function loadManifest(sb) {
  if (LOCAL) {
    const t = await (await fetch(`${LOCAL}tour.json`)).json();
    return { title: t.title || '', sub: '', scenes: t.scenes };
  }
  if (q.get('share')) {
    const { data, error } = await sb.rpc('tour_shared', { p_token: q.get('share') });
    if (error) throw error;
    if (!data) fail('קישור השיתוף בוטל או שאינו תקין.');
    return { title: data.title, sub: data.studio_name || '', scenes: data.places || [] };
  }
  const id = q.get('tour');
  const { data: tour, error: e1 } = await sb.from('tours').select('id,title').eq('id', id).maybeSingle();
  if (e1) throw e1;
  if (!tour) fail('הסיור לא נמצא, או שאין לך הרשאה לצפות בו.');
  const { data: rows, error: e2 } = await sb.from('tour_places')
    .select('id,sort_order,title,status,start,skip,bg,profile,scene_path,cameras_path')
    .eq('tour_id', id).in('status', ['ready', 'partial']).not('scene_path', 'is', null)
    .order('sort_order').order('created_at');
  if (e2) throw e2;
  return {
    title: tour.title, sub: '',
    scenes: rows.map((r) => ({ id: r.id, order: r.sort_order, title: r.title, status: r.status, start: r.start,
      skip: r.skip, bg: r.bg, profile: r.profile, ply: r.scene_path, cameras: r.cameras_path })),
  };
}

let sb = null;
/** where one stored file can be fetched from */
async function fileUrl(path) {
  if (LOCAL) return `${LOCAL}${path}`;
  const { data, error } = await sb.storage.from(BUCKET).createSignedUrl(path, 3600);
  if (error) throw error;
  return data.signedUrl;
}
/** a file's bytes, reporting how much has arrived (0..1) */
async function fetchBytes(url, onProgress) {
  const r = await fetch(url);
  if (!r.ok) throw new Error(`HTTP ${r.status}`);
  const total = Number(r.headers.get('content-length')) || 0;
  if (!r.body || !total) return new Uint8Array(await r.arrayBuffer());
  const reader = r.body.getReader(), chunks = [];
  let got = 0;
  for (;;) {
    const { done, value } = await reader.read();
    if (done) break;
    chunks.push(value);
    got += value.length;
    onProgress(Math.min(1, got / total));
  }
  const out = new Uint8Array(got);
  let at = 0;
  for (const c of chunks) { out.set(c, at); at += c.length; }
  return out;
}
async function fetchJson(path) {
  const r = await fetch(await fileUrl(path));
  if (!r.ok) throw new Error(`HTTP ${r.status}`);
  return r.json();
}

// ---------- renderer ----------
// Where nothing was filmed the picture stays transparent, and a soft backdrop shows through:
// the scene's own colours, stretched and blurred, over the place's average colour. No black.
let renderer;
try {
  renderer = new THREE.WebGLRenderer({ canvas, antialias: false, alpha: true, powerPreference: 'high-performance' });
} catch (_) {
  fail('הדפדפן הזה לא מציג תלת-ממד. נסו ב-Chrome, Safari או Edge עדכניים.');
}
renderer.setClearColor(0x000000, 0);
const ambient = $('ambient'), actx = ambient ? ambient.getContext('2d') : null;
if (ambient) { ambient.width = 96; ambient.height = 54; }
const tone = [0.6, 0.58, 0.545];               // the colour behind everything: follows what is on screen
let ground = '#9a948b';
function setGround(rgb) {
  if (Array.isArray(rgb) && rgb.length >= 3) for (let k = 0; k < 3; k++) tone[k] = Number(rgb[k]) || 0;
  ground = `rgb(${tone.map((v) => Math.round(v * 255)).join(',')})`;
  document.documentElement.style.setProperty('--ground', ground);
}
function paintAmbient() {
  if (!actx) return;
  const w = ambient.width, h = ambient.height;
  actx.globalAlpha = 0.5;                      // eases from frame to frame instead of flickering
  actx.fillStyle = ground;
  actx.fillRect(0, 0, w, h);
  // the picture enlarged a little: what lies just inside an empty edge spreads over it
  actx.globalAlpha = 0.4;
  actx.drawImage(canvas, -w * 0.3, -h * 0.12, w * 1.6, h * 1.24);
  actx.globalAlpha = 0.6;
  actx.drawImage(canvas, -w * 0.12, -h * 0.05, w * 1.24, h * 1.1);
  actx.globalAlpha = 1;
  actx.drawImage(canvas, 0, 0, w, h);
}
// How empty each edge of the picture is right now (0 = filled, 1 = nothing filmed there),
// read from a thumbnail of the frame. The view drifts away from an empty edge.
const probe = document.createElement('canvas');
probe.width = 32; probe.height = 18;
const pctx = probe.getContext('2d', { willReadFrequently: true });
const edges = { left: 0, right: 0, above: 0, below: 0 };
function readEdges() {
  const w = probe.width, h = probe.height, bx = 6, by = 4;
  pctx.clearRect(0, 0, w, h);
  pctx.drawImage(canvas, 0, 0, w, h);
  const a = pctx.getImageData(0, 0, w, h).data;
  const hole = (x0, x1, y0, y1) => {
    let n = 0;
    for (let y = y0; y < y1; y++) for (let x = x0; x < x1; x++) if (a[(y * w + x) * 4 + 3] < 110) n++;
    return n / ((x1 - x0) * (y1 - y0));
  };
  edges.left = hole(0, bx, 0, h); edges.right = hole(w - bx, w, 0, h);
  edges.above = hole(0, w, 0, by); edges.below = hole(0, w, h - by, h);
  // The colour behind the picture follows the brighter half of what is on screen: in a room
  // the part nobody filmed is nearly always more wall or ceiling, not more shadow.
  let n = 0, light = 0;
  for (let i = 0; i < a.length; i += 4) { n += a[i + 3]; light += a[i + 3] * (a[i] + a[i + 1] + a[i + 2]); }
  if (n < 40 * 255) return;
  const mean = light / n;
  let m = 0;
  const sum = [0, 0, 0];
  for (let i = 0; i < a.length; i += 4) {
    if (a[i] + a[i + 1] + a[i + 2] < mean) continue;
    m += a[i + 3];
    for (let k = 0; k < 3; k++) sum[k] += a[i + 3] * a[i + k];
  }
  if (m) setGround(tone.map((v, k) => v + (sum[k] / m / 255 - v) * 0.06));
}
const scene = new THREE.Scene();
scene.add(new SparkRenderer({ renderer }));
const camera = new THREE.PerspectiveCamera(56, 1, 0.01, 1000);

/** The view is never wider than what was filmed around a typical spot (plus a little):
 *  a narrow clip on a wide screen zooms in a bit rather than showing empty sides. */
function fitView() {
  const pl = state && state.place;
  if (pl) {
    const tall = rad(pl.vfov);
    const wide = 2 * Math.atan(Math.tan(tall / 2) * camera.aspect);
    const want = Math.min(wide, pl.span + pl.capH + 2 * SLACK);
    const fit = 2 * Math.atan(Math.tan(want / 2) / camera.aspect);
    camera.fov = FREE ? pl.vfov : clamp(THREE.MathUtils.radToDeg(fit), 34, pl.vfov);
  }
  camera.updateProjectionMatrix();
}
function resize() {
  const w = canvas.clientWidth, h = canvas.clientHeight;
  renderer.setPixelRatio(Math.min(devicePixelRatio, 1.5));
  renderer.setSize(w, h, false);
  camera.aspect = w / h;
  fitView();
}
const state = { index: -1, place: null, mesh: null, busy: true, pos: new THREE.Vector3(), yaw: 0, pitch: 0, auto: false, autoD: 0,
  vel: new THREE.Vector3(), turn: 0 };
addEventListener('resize', resize);
resize();

// ---------- the route ----------
let tour;
try {
  sb = await connect();
  tour = await loadManifest(sb);
} catch (err) {
  if (!loadingEl.classList.contains('error')) fail('טעינת הסיור נכשלה: ' + ((err && err.message) || err));
  throw err;
}
const places = tour.scenes;
if (!places.length) fail('הסיור עוד לא מוכן לצפייה: אין בו חלל שנבנה עד הסוף.');
document.title = tour.title ? `${tour.title} · סיור וירטואלי` : 'סיור וירטואלי';
$('tourTitle').textContent = tour.title || 'סיור וירטואלי';
if (tour.sub) { $('tourSub').textContent = tour.sub; $('tourSub').hidden = false; }
$('placesPanel').hidden = false;
setGround(places[0] && places[0].bg);
// a tour may carry a colour grade for the whole picture (a CSS filter: brightness, contrast, saturation)
if (tour.grade) canvas.style.filter = tour.grade;

const listEl = $('places');
places.forEach((p, i) => {
  const b = document.createElement('button');
  b.type = 'button';
  b.textContent = p.title || `חלל ${i + 1}`;
  b.addEventListener('click', () => { go(i); canvas.focus(); });
  const li = document.createElement('li');
  li.append(b);
  listEl.append(li);
});
if (places.length < 2) listEl.hidden = true;

function headingFrom(fwd) {
  const pl = state.place;
  state.yaw = Math.atan2(fwd.dot(pl.e2), fwd.dot(pl.e1));
  state.pitch = Math.asin(clamp(fwd.dot(pl.up), -1, 1));
}
function forward(flat = false) {
  const pl = state.place;
  const cp = flat ? 1 : Math.cos(state.pitch);
  const f = pl.e1.clone().multiplyScalar(Math.cos(state.yaw) * cp).addScaledVector(pl.e2, Math.sin(state.yaw) * cp);
  if (!flat) f.addScaledVector(pl.up, Math.sin(state.pitch));
  return f;
}
/** Keep the view on what was filmed. Two things act together: the view may turn LOOK past the
 *  headings the cameras around this spot took, and it drifts away from whichever edge of the
 *  picture is empty. Both ease the view back rather than stopping it dead. */
function limitHeading(dt) {
  if (FREE) return;
  const pl = state.place;
  const c = pl.around(state.pos);
  const ease = Math.exp(-14 * dt);
  const pull = (v, a, b) => (v < a ? a + (v - a) * ease : v > b ? b + (v - b) * ease : v);
  // an empty edge on one side only: turn toward the other side, harder the emptier it is
  const drift = (near, far) => {
    const worst = Math.max(near, far);
    return (far - near) * clamp((worst - 0.3) / 0.3, 0, 1) * 5 * dt;
  };
  state.yaw += drift(edges.left, edges.right);       // left edge empty -> turn right (yaw falls)
  state.pitch += drift(edges.above, edges.below);    // top edge empty -> look down
  state.yaw = pl.camYaw[c.i0] + pull(wrap(state.yaw - pl.camYaw[c.i0]), c.lo - LOOK, c.hi + LOOK);
  state.pitch = pull(state.pitch, c.pLo - TILT, c.pHi + TILT);
}
function setAuto(on) {
  state.auto = on;
  $('auto').setAttribute('aria-pressed', String(on));
}
/** stand at the start (or the end) of the current place's path */
function stand(atEnd = false) {
  // a place may name where along its path the visit opens (`start`, 0..1):
  // the first frames of a clip are often a close-up of a wall
  const pl = state.place, d = pl.pathLen * (atEnd ? 1 : pl.start || 0), p = pl.at(d);
  state.pos.copy(p.pos);
  headingFrom(p.fwd);
  state.autoD = d;
  state.vel.set(0, 0, 0);
  state.turn = 0;
}

/** a place's scene: its .ply file, fetched whole, with the share that has arrived on the curtain */
async function sceneSource(p, label) {
  const bytes = await fetchBytes(await fileUrl(p.ply), (f) => { loadingText.textContent = `${label} ${Math.round(f * 100)}%`; });
  return { fileBytes: bytes, fileType: 'ply' };
}

const captures = new Map();
/** move to place i: fade out, swap the scene, fade in */
async function go(i, { keepAuto = false } = {}) {
  if (i < 0 || i >= places.length || (state.busy && state.index >= 0)) return;
  if (i === state.index) { stand(); setAuto(false); return; }
  state.busy = true;
  if (!keepAuto) setAuto(false);
  const p = places[i];
  const label = state.index < 0 ? 'טוען את הנכס…' : (p.title || `חלל ${i + 1}`);
  loadingText.textContent = label;
  loadingEl.classList.remove('done');
  await new Promise((r) => setTimeout(r, state.index < 0 ? 0 : 450));
  try {
    if (!captures.has(i)) captures.set(i, new Place(await fetchJson(p.cameras), p.skip || []));
    const mesh = new SplatMesh(await sceneSource(p, label));
    await mesh.initialized;
    if (state.mesh) { scene.remove(state.mesh); state.mesh.dispose(); }
    scene.add(mesh);
    state.mesh = mesh;
    state.place = captures.get(i);
    state.place.start = clamp(Number(p.start) || 0, 0, 1);
    state.index = i;
    camera.near = state.place.step * 0.15;
    camera.far = state.place.diag * 200;
    setGround(p.bg);
    fitView();
    stand();
    [...listEl.children].forEach((li, k) => li.firstChild.setAttribute('aria-current', String(k === i)));
    // one frame with the new scene before the curtain lifts
    await new Promise((r) => setTimeout(r, 250));
    loadingEl.classList.add('done');
  } catch (err) {
    loadingText.textContent = 'טעינת החלל נכשלה: ' + ((err && err.message) || err);
    setAuto(false);
  }
  state.busy = false;
}
const next = (opts) => go(state.index + 1, opts);
const prev = () => go(state.index - 1);

// ---------- input ----------
const keys = new Set();
const MOVE = new Set(['KeyW', 'KeyS', 'KeyA', 'KeyD', 'KeyQ', 'KeyE', 'ArrowUp', 'ArrowDown', 'ArrowLeft', 'ArrowRight']);
let fast = false;
addEventListener('keydown', (e) => {
  if (e.key === 'Shift') fast = true;
  if (e.metaKey || e.ctrlKey || e.altKey) return;
  if (e.code === 'Space') { e.preventDefault(); if (!e.repeat) setAuto(!state.auto); return; }
  if (e.code === 'KeyH') { if (!e.repeat) document.body.classList.toggle('clean'); return; }   // the house only, no on-screen controls
  if (e.code === 'KeyN' || e.code === 'Enter') { if (!e.repeat) next(); return; }
  if (e.code === 'KeyB') { if (!e.repeat) prev(); return; }
  if (/^Digit[1-9]$/.test(e.code)) { go(Number(e.code.slice(5)) - 1); return; }
  if (MOVE.has(e.code)) { e.preventDefault(); keys.add(e.code); setAuto(false); }
});
addEventListener('keyup', (e) => { if (e.key === 'Shift') fast = false; keys.delete(e.code); });
addEventListener('blur', () => { keys.clear(); fast = false; });

let drag = null;
canvas.addEventListener('pointerdown', (e) => {
  drag = { x: e.clientX, y: e.clientY };
  canvas.setPointerCapture(e.pointerId);
  canvas.classList.add('dragging');
  canvas.focus();
  setAuto(false);
});
canvas.addEventListener('pointermove', (e) => {
  if (!drag) return;
  const k = rad(camera.fov) / canvas.clientHeight;   // grab the view: 1 px = 1 px
  state.yaw += (e.clientX - drag.x) * k;
  state.pitch = clamp(state.pitch + (e.clientY - drag.y) * k, -1.2, 1.2);
  drag.x = e.clientX; drag.y = e.clientY;
});
const endDrag = () => { drag = null; canvas.classList.remove('dragging'); };
canvas.addEventListener('pointerup', endDrag);
canvas.addEventListener('pointercancel', endDrag);

$('auto').addEventListener('click', () => { setAuto(!state.auto); canvas.focus(); });
$('reset').addEventListener('click', () => { go(0).then(() => { if (state.index === 0) { stand(); setAuto(false); } }); canvas.focus(); });
const onward = $('onward');
onward.addEventListener('click', () => { next(); canvas.focus(); });
// on-screen walk buttons: hold to walk (a touch screen has no keyboard)
for (const [id, code] of [['fwd', 'KeyW'], ['back', 'KeyS']]) {
  const b = $(id);
  if (!b) continue;
  const stop = () => keys.delete(code);
  b.addEventListener('pointerdown', (e) => { e.preventDefault(); b.setPointerCapture(e.pointerId); keys.add(code); setAuto(false); });
  b.addEventListener('pointerup', stop);
  b.addEventListener('pointercancel', stop);
  b.addEventListener('lostpointercapture', stop);
  b.addEventListener('contextmenu', (e) => e.preventDefault());
}

// ---------- frame loop ----------
const held = (...codes) => codes.some((c) => keys.has(c));
let last = performance.now(), frames = 0;
renderer.setAnimationLoop((now) => {
  const dt = Math.min(0.1, (now - last) / 1000);
  last = now;
  const pl = state.place;
  if (!pl) return;

  if (!state.busy) {
    if (state.auto) {
      state.autoD += pl.walk * dt;
      const p = pl.at(state.autoD);
      state.pos.copy(p.pos);
      headingFrom(p.fwd);
      if (state.autoD >= pl.pathLen) {
        if (state.index < places.length - 1) next({ keepAuto: true });
        else setAuto(false);
      }
    } else {
      // walking and turning ease in and out rather than starting and stopping at once
      const turn = (held('ArrowLeft', 'KeyQ') ? 1 : 0) - (held('ArrowRight', 'KeyE') ? 1 : 0);
      state.turn += (turn * TURN - state.turn) * (1 - Math.exp(-9 * dt));
      state.yaw += state.turn * dt;
      const f = forward(true);
      const right = new THREE.Vector3().crossVectors(f, pl.up);
      const along = (held('KeyW', 'ArrowUp') ? 1 : 0) - (held('KeyS', 'ArrowDown') ? 1 : 0);
      const side = (held('KeyD') ? 1 : 0) - (held('KeyA') ? 1 : 0);
      const want = f.multiplyScalar(along).addScaledVector(right, side);
      if (along || side) want.normalize().multiplyScalar(pl.walk * (fast ? 2.2 : 1));
      state.vel.lerp(want, 1 - Math.exp(-6 * dt));
      if (state.vel.lengthSq() > (pl.walk * 0.01) ** 2) {
        state.pos.addScaledVector(state.vel, dt);
        // stay near what the camera actually saw, at the height it flew there
        const near = pl.P[pl.nearest(state.pos)];
        const off = state.pos.clone().sub(near);
        const h = off.dot(pl.up);
        off.addScaledVector(pl.up, -h);
        if (off.length() > pl.leash) off.setLength(pl.leash);
        state.pos.copy(near).add(off).addScaledVector(pl.up, h * Math.exp(-4 * dt));
        state.autoD = pl.D[pl.nearest(state.pos)];
      }
      limitHeading(dt);
    }
    // near the end of this place: offer the way onward
    const atEnd = state.index < places.length - 1 && state.autoD > pl.pathLen * 0.85;
    if (onward.hidden === atEnd) {
      onward.hidden = !atEnd;
      if (atEnd) onward.textContent = `המשך אל: ${places[state.index + 1].title || `חלל ${state.index + 2}`}  ⏎`;
    }
  }

  camera.position.copy(state.pos);
  camera.up.copy(pl.up);
  camera.lookAt(state.pos.clone().add(forward()));
  renderer.render(scene, camera);
  // a hidden or collapsed frame has no pixels to read
  if (!PLAIN && canvas.width && canvas.height) { if (++frames % 2 === 0) paintAmbient(); else readEdges(); }
});

await go(clamp((Number(q.get('place')) || 1) - 1, 0, places.length - 1));
canvas.focus();

// for checks from the console
window.__tour = { state, camera, places, go, edges };
