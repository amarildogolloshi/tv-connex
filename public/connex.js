
// ================================
// Connex — TV Path Puzzle (Zip-style)
// Rules: Free movement | Allow backdraw ONLY to previous cell (pop last segment) | Block all other revisits
// Win only if: full coverage + numbers first-visited in order + end on last number.
// ================================

// ---------- Modes in one dropdown (uses #levelSelect) ----------
const MODES = [
  { key: "zip",      label: "Zip 6×6 (12)",    kind: "zip" },
  { key: "beginner", label: "Beginner (6×6)",  kind: "level", cols: 6, rows: 6, K: 10, minGap: 2, wallPct: 0.00, targetMs: 45_000 },
  { key: "standard", label: "Standard (6×6)",  kind: "level", cols: 6, rows: 6, K: 12, minGap: 3, wallPct: 0.04, targetMs: 60_000 },
  { key: "advanced", label: "Advanced (6×6)",  kind: "level", cols: 6, rows: 6, K: 12, minGap: 5, wallPct: 0.08, targetMs: 75_000 },
  { key: "expert",   label: "Expert (6×6)",    kind: "level", cols: 6, rows: 6, K: 12, minGap: 7, wallPct: 0.12, targetMs: 90_000 }
];

// ---------- Canvas / UI refs ----------
const canvas   = document.getElementById("game");
const ctx      = canvas.getContext("2d");
const statusEl = document.getElementById("status");
const levelSel = document.getElementById("levelSelect");

// Focus so Arrow keys work
canvas.setAttribute('tabindex', '0');
window.addEventListener('load', () => canvas.focus());
canvas.addEventListener('pointerdown', () => canvas.focus());
canvas.addEventListener('touchstart', () => canvas.focus());

// ---------- Grid sizing ----------
let COLS = 6, ROWS = 6;
let CELL = Math.floor(canvas.width / COLS);

// ---------- Mode & timing ----------
let lastModeKey = "zip";           // default Zip
let currentTargetMs = 60_000;

// ---------- Game State ----------
let grid, player, goal;
let trail = [];                    // [{x,y}] ordered path
let visitedCells = new Set();      // distinct coverage ("x,y")
let savedLayout = null;

let anchors = [];                  // [{x,y,n}] n = 1..K
let anchorsMap = new Map();        // "x,y" -> n
let walls = new Set();             // "x,y|right" or "x,y|down"

// ---------- Timer ----------
let startTime = null, elapsed = 0, timerId = null, hasStarted = false;
let gameOver = false;

// ---------- Utils ----------
function formatTime(ms) {
  ms = Math.max(0, ms|0);
  const mm = Math.floor(ms/60000), ss = Math.floor((ms%60000)/1000), ms3 = ms%1000;
  return `${String(mm).padStart(2,'0')}:${String(ss).padStart(2,'0')}.${String(ms3).padStart(3,'0')}`;
}
function keyOf(x, y) { return `${x},${y}`; }
function tell(msg) { statusEl.textContent = msg; /* console.log(msg); */ }
function getCellNumber(x, y) { return anchorsMap.get(keyOf(x, y)) ?? null; }
function K() { return anchors.length; }

// First-visit order of numbers along the trail
function numbersFirstOrder() {
  const seen = new Set();
  const order = [];
  for (const p of trail) {
    const n = getCellNumber(p.x, p.y);
    if (n != null && !seen.has(n)) { seen.add(n); order.push(n); }
  }
  return order; // e.g., [1,2,3,...]
}
function nextRequiredNumber() {
  const seen = new Set(numbersFirstOrder());
  for (let n = 1; n <= K(); n++) if (!seen.has(n)) return n;
  return null; // all collected (at least once)
}
function updateTimeTargetDisplay(ms) {
  const el = document.getElementById('timeTarget');
  if (!el) return;
  const nextN = nextRequiredNumber();
  const nextLabel = (nextN == null) ? "✓" : String(nextN);
  el.innerHTML = `<span class="label">⏱</span> ${formatTime(ms)}
                  <span class="label">|</span>
                  <span class="label">🎯 Target:</span> ${formatTime(currentTargetMs)}
                  <span class="label">|</span>
                  <span class="label">Next:</span> ${nextLabel}`;
}
function startTimer() {
  if (hasStarted) return;
  hasStarted = true;
  startTime = performance.now();
  const tick = () => { elapsed = performance.now() - startTime; updateTimeTargetDisplay(elapsed); timerId = requestAnimationFrame(tick); };
  timerId = requestAnimationFrame(tick);
}
function stopTimer() { if (timerId) cancelAnimationFrame(timerId); timerId = null; updateTimeTargetDisplay(elapsed); }

// ---------- Path & walls ----------
function buildSnakePath(cols, rows) {
  // Serpentine path: visits every cell exactly once
  const path = [];
  for (let y = 0; y < rows; y++) {
    if (y % 2 === 0) for (let x = 0; x < cols; x++) path.push({ x, y });
    else             for (let x = cols - 1; x >= 0; x--) path.push({ x, y });
  }
  return path; // length == cols*rows
}
function blockedByWall(x0, y0, nx, ny) {
  const dx = nx - x0, dy = ny - y0;
  if      (dx === 1 && dy === 0) return walls.has(`${x0},${y0}|right`);
  else if (dx === -1 && dy === 0) return walls.has(`${nx},${ny}|right`);
  else if (dx === 0 && dy === 1)  return walls.has(`${x0},${y0}|down`);
  else if (dx === 0 && dy === -1) return walls.has(`${nx},${ny}|down`);
  return false;
}
function neighborsUnblocked(x, y) {
  const out = [];
  if (x > 0             && !blockedByWall(x, y, x-1, y)) out.push({x: x-1, y});
  if (x < COLS - 1      && !blockedByWall(x, y, x+1, y)) out.push({x: x+1, y});
  if (y > 0             && !blockedByWall(x, y, x, y-1)) out.push({x, y: y-1});
  if (y < ROWS - 1      && !blockedByWall(x, y, x, y+1)) out.push({x, y: y+1});
  return out;
}

// ---------- Random anchor picking with spacing (no fixed ends) ----------
function pickIndicesWithMinGap(len, K, minGap) {
  // Shuffle pool [0..len-1]
  const pool = Array.from({ length: len }, (_, i) => i);
  for (let i = pool.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [pool[i], pool[j]] = [pool[j], pool[i]];
  }
  const picks = [];
  for (const idx of pool) {
    if (picks.length === K) break;
    if (picks.every(p => Math.abs(p - idx) >= minGap)) picks.push(idx);
  }
  // If spacing too strict, fill remaining positions anyway
  let fill = 0;
  while (picks.length < K && fill < pool.length) {
    if (!picks.includes(pool[fill])) picks.push(pool[fill]);
    fill++;
  }
  // Sort so numbers are in snake order (1..K along the path)
  return picks.sort((a, b) => a - b);
}

function buildShortcutWallsFromSnake(snake, wallPct) {
  walls.clear();
  // Add walls only on edges that are NOT snake-adjacent to block shortcuts,
  // and never on the snake itself so solvability is preserved.
  for (let y = 0; y < ROWS; y++) {
    for (let x = 0; x < COLS; x++) {
      // right neighbor
      if (x < COLS - 1) {
        const a = keyOf(x, y), b = keyOf(x+1, y);
        const i = snake.findIndex(s => keyOf(s.x, s.y) === a);
        const j = snake.findIndex(s => keyOf(s.x, s.y) === b);
        const consecutive = Math.abs(i - j) === 1;
        if (!consecutive && Math.random() < wallPct) walls.add(`${x},${y}|right`);
      }
      // down neighbor
      if (y < ROWS - 1) {
        const a = keyOf(x, y), b = keyOf(x, y+1);
        const i = snake.findIndex(s => keyOf(s.x, s.y) === a);
        const j = snake.findIndex(s => keyOf(s.x, s.y) === b);
        const consecutive = Math.abs(i - j) === 1;
        if (!consecutive && Math.random() < wallPct) walls.add(`${x},${y}|down`);
      }
    }
  }
}

// ---------- Drawing ----------
function drawWalls() {
  if (!walls.size) return;
  ctx.save();
  ctx.strokeStyle = "#e8eaed";
  ctx.lineWidth = Math.max(3, Math.floor(CELL * 0.12));
  for (const w of walls) {
    const [xy, dir] = w.split("|");
    const [xStr, yStr] = xy.split(",");
    const x = parseInt(xStr, 10), y = parseInt(yStr, 10);
    const px = x * CELL, py = y * CELL;
    if (dir === "right") { ctx.beginPath(); ctx.moveTo(px + CELL, py); ctx.lineTo(px + CELL, py + CELL); ctx.stroke(); }
    else {                 ctx.beginPath(); ctx.moveTo(px, py + CELL); ctx.lineTo(px + CELL, py + CELL); ctx.stroke(); }
  }
  ctx.restore();
}
function drawNumbers() {
  ctx.save();
  ctx.fillStyle = "#e8eaed";
  ctx.textAlign = "center";
  ctx.textBaseline = "middle";
  ctx.font = `${Math.max(14, Math.floor(CELL * 0.5))}px system-ui, -apple-system, Segoe UI, Roboto, Arial, sans-serif`;
  for (const a of anchors) {
    ctx.save();
    ctx.shadowColor = "rgba(0,0,0,0.6)";
    ctx.shadowBlur  = Math.max(3, Math.floor(CELL * 0.15));
    ctx.fillText(String(a.n), a.x * CELL + CELL / 2, a.y * CELL + CELL / 2);
    ctx.restore();
  }
  ctx.restore();
}
function draw() {
  if (!grid) return;
  ctx.clearRect(0, 0, canvas.width, canvas.height);

  ctx.strokeStyle = "#808995"; ctx.lineWidth = 2;
  for (let y = 0; y <= ROWS; y++) { ctx.beginPath(); ctx.moveTo(0, y * CELL); ctx.lineTo(COLS * CELL, y * CELL); ctx.stroke(); }
  for (let x = 0; x <= COLS; x++) { ctx.beginPath(); ctx.moveTo(x * CELL, 0); ctx.lineTo(x * CELL, ROWS * CELL); ctx.stroke(); }

  drawWalls();

//   const pad = Math.max(6, Math.floor(CELL * 0.12));
//   ctx.save();
//   ctx.fillStyle = "#2ecc71"; ctx.shadowColor = "rgba(46,204,113,0.55)"; ctx.shadowBlur = Math.max(10, Math.floor(CELL * 0.45));
//   ctx.fillRect(goal.x * CELL + pad, goal.y * CELL + pad, CELL - pad * 2, CELL - pad * 2);
//   ctx.restore();

  drawNumbers();

  if (trail.length) {
    ctx.save();
    ctx.strokeStyle = "#00bcd4";
    ctx.lineWidth = Math.max(4, Math.floor(CELL * 0.18));
    ctx.lineJoin = "round"; ctx.lineCap = "round";
    ctx.shadowColor = "rgba(0, 188, 212, 0.45)"; ctx.shadowBlur  = Math.max(8, Math.floor(CELL * 0.35));
    ctx.beginPath();
    const p0 = trail[0]; ctx.moveTo(p0.x * CELL + CELL/2, p0.y * CELL + CELL/2);
    for (let i = 1; i < trail.length; i++) { const p = trail[i]; ctx.lineTo(p.x * CELL + CELL/2, p.y * CELL + CELL/2); }
    ctx.stroke();
    ctx.restore();
  }

  ctx.save();
  ctx.fillStyle = "#e74c3c"; ctx.shadowColor = "rgba(231,76,60,0.6)"; ctx.shadowBlur = Math.max(12, Math.floor(CELL * 0.5));
  ctx.beginPath(); ctx.arc(player.x * CELL + CELL/2, player.y * CELL + CELL/2, Math.max(8, CELL/3), 0, Math.PI*2); ctx.fill();
  ctx.restore();
}

// ---------- Layout ----------
function buildGrid(cols, rows) {
  COLS = cols; ROWS = rows;
  CELL = Math.floor(canvas.width / COLS);
  grid = Array.from({ length: ROWS }, (_, y) => Array.from({ length: COLS }, (_, x) => ({ x, y })));
}
function generateZip6x6() {
  buildGrid(6, 6);
  const snake = buildSnakePath(6, 6);
  anchors = []; anchorsMap.clear(); walls.clear();

  const idxs = pickIndicesWithMinGap(snake.length, 12, 2);
  for (let n = 1; n <= 12; n++) {
    const { x, y } = snake[idxs[n - 1]];
    anchors.push({ x, y, n }); anchorsMap.set(keyOf(x, y), n);
  }
  const startA = anchors.find(a => a.n === 1);
  const finalA = anchors.find(a => a.n === 12);

  player = { x: startA.x, y: startA.y };
  goal   = { x: finalA.x, y: finalA.y };
  trail  = [{ x: player.x, y: player.y }];
  visitedCells = new Set([ keyOf(player.x, player.y) ]);

  gameOver = false; hasStarted = false; elapsed = 0; startTime = null;
}
function generateLevel(def) {
  buildGrid(def.cols, def.rows);
  const snake = buildSnakePath(def.cols, def.rows);

  anchors = []; anchorsMap.clear(); walls.clear();
  const idxs = pickIndicesWithMinGap(snake.length, def.K, def.minGap);
  for (let n = 1; n <= def.K; n++) {
    const { x, y } = snake[idxs[n - 1]];
    anchors.push({ x, y, n }); anchorsMap.set(keyOf(x, y), n);
  }
  buildShortcutWallsFromSnake(snake, def.wallPct);

  const startA = anchors.find(a => a.n === 1);
  const finalA = anchors.find(a => a.n === def.K);

  player = { x: startA.x, y: startA.y };
  goal   = { x: finalA.x, y: finalA.y };
  trail  = [{ x: player.x, y: player.y }];
  visitedCells = new Set([ keyOf(player.x, player.y) ]);

  gameOver = false; hasStarted = false; elapsed = 0; startTime = null;
}

// ---------- Movement (FREE; allow backdraw ONLY 1 step; block other revisits) ----------
function isImmediateBack(nx, ny) {
  if (trail.length < 2) return false;
  const prev = trail[trail.length - 2];
  return prev.x === nx && prev.y === ny;
}
function move(dir) {
  if (gameOver) return;

  const x0 = player.x, y0 = player.y;
  let nx = x0, ny = y0;
  if (dir === "up")    ny--;
  if (dir === "right") nx++;
  if (dir === "down")  ny++;
  if (dir === "left")  nx--;

  // bounds + walls
  if (nx < 0 || ny < 0 || nx >= COLS || ny >= ROWS) return;
  if (blockedByWall(x0, y0, nx, ny)) { tell("Blocked by wall."); return; }

  // If target is already in trail:
  const idx = trail.findIndex(p => p.x === nx && p.y === ny);
  if (idx !== -1) {
    // Allow ONLY immediate previous cell backdraw
    if (isImmediateBack(nx, ny)) {
      // Pop last segment and move player to previous cell (trail already ends there)
      trail.pop(); // remove the current cell (last step)
      player.x = nx; player.y = ny;

      // Keep visitedCells as-is (coverage credit remains)
      draw(); updateTimeTargetDisplay(elapsed);
      tell("Step back: removed last segment.");
      return;
    } else {
      tell("Cell already walked. You can only step back 1 cell.");
      return;
    }
  }

  // Start timer on first movement
  if (!hasStarted && (nx !== x0 || ny !== y0)) startTimer();

  // Forward move — append to trail
  player.x = nx; player.y = ny;
  trail.push({ x: player.x, y: player.y });

  // Track distinct coverage
  visitedCells.add(keyOf(player.x, player.y));

  draw(); updateTimeTargetDisplay(elapsed);

  // ----- Win condition -----
  // A) full coverage
  const walkedAll = visitedCells.size === COLS * ROWS;

  // B) numbers first-visit order is 1..K
  const order = numbersFirstOrder();
  const must  = Array.from({ length: K() }, (_, i) => i + 1);
  const visitedInOrder = (order.length === K()) && order.every((n, i) => n === must[i]);

  // C) standing on the last number's cell
  const finalA = anchors.find(a => a.n === K());
  const atGoal = player.x === finalA.x && player.y === finalA.y;

  if (walkedAll && visitedInOrder && atGoal) {
    gameOver = true; stopTimer();
    const star = (elapsed <= currentTargetMs) ? " ⭐" : "";
    tell(`You win! ${formatTime(elapsed)} (Target: ${formatTime(currentTargetMs)})${star}`);
  }
}

// ---------- Keyboard (Arrows + WASD + TV D‑pad names + keyCode) ----------
function mapKeyToDir(e) {
  const k = e.key || e.code || "";
  const kc = e.keyCode || e.which || 0;

  // Desktop arrows & WASD
  if (k === "ArrowUp"    || k === "w" || k === "W") return "up";
  if (k === "ArrowRight" || k === "d" || k === "D") return "right";
  if (k === "ArrowDown"  || k === "s" || k === "S") return "down";
  if (k === "ArrowLeft"  || k === "a" || k === "A") return "left";

  // TV remote common names
  if (k === "Up"      || k === "DPadUp"    || k === "DPAD_UP")    return "up";
  if (k === "Right"   || k === "DPadRight" || k === "DPAD_RIGHT") return "right";
  if (k === "Down"    || k === "DPadDown"  || k === "DPAD_DOWN")  return "down";
  if (k === "Left"    || k === "DPadLeft"  || k === "DPAD_LEFT")  return "left";

  // keyCode fallback
  if (kc === 38) return "up";
  if (kc === 39) return "right";
  if (kc === 40) return "down";
  if (kc === 37) return "left";

  return null;
}
document.addEventListener("keydown", (e) => {
  const dir = mapKeyToDir(e);
  if (!dir) return;
  move(dir);
  e.preventDefault(); // block page scroll on arrows
});

// ---------- UI ----------
function populateModes() {
  if (!levelSel) return;
  levelSel.innerHTML = "";
  MODES.forEach((m, i) => {
    const opt = document.createElement("option");
    opt.value = m.key; opt.textContent = `${i+1}. ${m.label}`;
    levelSel.appendChild(opt);
  });
  levelSel.value = lastModeKey;
}
levelSel?.addEventListener("change", (e) => {
  const key = e.target.value;
  const def = MODES.find(m => m.key === key);
  if (!def) return;
  lastModeKey = key;
  if (def.kind === "zip") {
    generateZip6x6();
    currentTargetMs = 60_000;
  } else {
    generateLevel(def);
    currentTargetMs = def.targetMs ?? 60_000;
  }
  updateTimeTargetDisplay(0);
  draw();
  tell(`Mode: ${def.label}`);
});

document.getElementById("new")?.addEventListener("click", () => {
  const def = MODES.find(m => m.key === lastModeKey);
  if (!def || def.kind === "zip") {
    generateZip6x6();
    currentTargetMs = 60_000;
    tell("New Zip layout.");
  } else {
    generateLevel(def);
    currentTargetMs = def.targetMs ?? 60_000;
    tell(`New ${def.label} layout.`);
  }
  updateTimeTargetDisplay(0);
  // save layout for restart
  savedLayout = {
    mode: lastModeKey,
    cols: COLS, rows: ROWS,
    playerStart: { ...player }, goalPos: { ...goal },
    anchors: anchors.map(a => ({ ...a })), walls: Array.from(walls)
  };
  draw();
});

document.getElementById("restart")?.addEventListener("click", () => {
   if (!savedLayout) { tell("No saved layout yet. Click New first."); return; }
  // rebuild from savedLayout
  COLS = savedLayout.cols; ROWS = savedLayout.rows; CELL = Math.floor(canvas.width / COLS);
  grid = Array.from({ length: ROWS }, (_, y) => Array.from({ length: COLS }, (_, x) => ({ x, y })));
  player = { ...savedLayout.playerStart };
  goal   = { ...savedLayout.goalPos };
  anchors = savedLayout.anchors.map(a => ({ ...a }));
  anchorsMap.clear(); for (const a of anchors) anchorsMap.set(keyOf(a.x, a.y), a.n);
  walls.clear(); savedLayout.walls?.forEach(w => walls.add(w));

  trail = [{ x: player.x, y: player.y }];
  visitedCells = new Set([ keyOf(player.x, player.y) ]);
  gameOver = false; hasStarted = false; elapsed = 0; startTime = null;
  updateTimeTargetDisplay(0);
  draw();
  tell("Restarted same layout.");
});

// ---------- Resize & init ----------
function fitCanvas() {
  const size = Math.min(window.innerWidth * 0.9, window.innerHeight * 0.7);
  const s = Math.max(360, Math.min(1080, Math.floor(size)));
  canvas.width = s; canvas.height = s;
  CELL = Math.floor(canvas.width / COLS);
  draw();
}
window.addEventListener("resize", fitCanvas);

// Init
populateModes();
fitCanvas();
generateZip6x6();
currentTargetMs = 60_000;
updateTimeTargetDisplay(0);
draw();
