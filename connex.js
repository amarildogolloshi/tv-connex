
// ================================
// Connex — TV Path Puzzle (Zip-style)
// Randomized path + rotated labels; free movement; backdraw only 1 step; block other revisits.
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

function numbersFirstOrder() {
  // First-visit order of numbers along the current trail.
  const seen = new Set();
  const order = [];
  for (const p of trail) {
    const n = getCellNumber(p.x, p.y);
    if (n != null && !seen.has(n)) { seen.add(n); order.push(n); }
  }
  return order;
}
function nextRequiredNumber() {
  const seen = new Set(numbersFirstOrder());
  for (let n = 1; n <= K(); n++) if (!seen.has(n)) return n;
  return null; // all collected at least once
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

// ---------- Path building (randomized snake) ----------
function buildSnakePathBase(cols, rows) {
  const path = [];
  for (let y = 0; y < rows; y++) {
    if (y % 2 === 0) for (let x = 0; x < cols; x++) path.push({ x, y });
    else             for (let x = cols - 1; x >= 0; x--) path.push({ x, y });
  }
  return path;
}
function rotatePoint(p, rot, cols, rows) {
  const { x, y } = p;
  switch (rot % 4) {
    case 0:  return { x, y };                                             // 0°
    case 1:  return { x: y, y: cols - 1 - x };                            // 90°
    case 2:  return { x: cols - 1 - x, y: rows - 1 - y };                 // 180°
    case 3:  return { x: rows - 1 - y, y: x };                            // 270°
  }
}
// small in-place shuffle
function shuffleArray(arr) {
  for (let i = arr.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
}

// DFS-style Hamiltonian path generator (backtracking with Warnsdorff-like heuristic)
function buildDFSHamiltonian(cols, rows) {
  const total = cols * rows;
  const dirs = [[0,-1],[1,0],[0,1],[-1,0]];

  function neighbors(x, y, visited) {
    const out = [];
    for (const [dx, dy] of dirs) {
      const nx = x + dx, ny = y + dy;
      if (nx < 0 || ny < 0 || nx >= cols || ny >= rows) continue;
      if (!visited[ny][nx]) out.push({ x: nx, y: ny });
    }
    return out;
  }

  const maxAttempts = 8;
  const timeBudgetMs = 200; // per attempt

  for (let attempt = 0; attempt < maxAttempts; attempt++) {
    const visited = Array.from({ length: rows }, () => Array(cols).fill(false));
    const path = [];

    // choose a random start
    const sx = Math.floor(Math.random() * cols);
    const sy = Math.floor(Math.random() * rows);

    let found = false;
    const deadline = performance.now() + timeBudgetMs;

    function dfs(x, y) {
      if (performance.now() > deadline || found) return;
      visited[y][x] = true; path.push({ x, y });
      if (path.length === total) { found = true; return; }

      // neighbors with Warnsdorff heuristic (fewest onward moves first)
      let neigh = neighbors(x, y, visited);
      // randomize then sort to break ties
      shuffleArray(neigh);
      neigh.sort((a, b) => neighbors(a.x, a.y, visited).length - neighbors(b.x, b.y, visited).length);

      for (const n of neigh) {
        if (found || performance.now() > deadline) break;
        dfs(n.x, n.y);
      }

      if (!found) { visited[y][x] = false; path.pop(); }
    }

    dfs(sx, sy);
    if (found && path.length === total) return path;
  }

  // fallback: failed to build a DFS Hamiltonian within attempts/time
  return null;
}

function buildSpiralSnakePath(cols, rows) {
  const path = [];
  let left = 0, top = 0, right = cols - 1, bottom = rows - 1;
  while (left <= right && top <= bottom) {
    for (let x = left; x <= right; x++) path.push({ x, y: top });
    for (let y = top + 1; y <= bottom; y++) path.push({ x: right, y });
    if (top < bottom) for (let x = right - 1; x >= left; x--) path.push({ x, y: bottom });
    if (left < right) for (let y = bottom - 1; y > top; y--) path.push({ x: left, y });
    left++; right--; top++; bottom--;
  }
  return path;
}

function buildColumnSnakePath(cols, rows) {
  const path = [];
  for (let x = 0; x < cols; x++) {
    if (x % 2 === 0) for (let y = 0; y < rows; y++) path.push({ x, y });
    else for (let y = rows - 1; y >= 0; y--) path.push({ x, y });
  }
  return path;
}

function buildDiagonalSnakePath(cols, rows) {
  const path = [];
  for (let s = 0; s <= cols + rows - 2; s++) {
    const diag = [];
    const xStart = Math.max(0, s - (rows - 1));
    const xEnd = Math.min(cols - 1, s);
    for (let x = xStart; x <= xEnd; x++) {
      const y = s - x;
      diag.push({ x, y });
    }
    // reverse every other diagonal to make the path continuous
    if (s % 2 === 0) diag.reverse();
    for (const p of diag) path.push(p);
  }
  return path;
}

function buildCenterSpiralPath(cols, rows) {
  const total = cols * rows;
  const visited = Array.from({ length: rows }, () => Array(cols).fill(false));
  const path = [];
  let x = Math.floor((cols - 1) / 2), y = Math.floor((rows - 1) / 2);
  visited[y][x] = true; path.push({ x, y });
  const dirs = [[1,0],[0,1],[-1,0],[0,-1]];
  let len = 1;
  while (path.length < total) {
    for (let d = 0; d < 4 && path.length < total; d++) {
      for (let step = 0; step < len && path.length < total; step++) {
        x += dirs[d][0]; y += dirs[d][1];
        if (x >= 0 && y >= 0 && x < cols && y < rows && !visited[y][x]) {
          visited[y][x] = true; path.push({ x, y });
        }
      }
      if (d % 2 === 1) len++;
    }
  }
  // Fill any missed cells with base snake if necessary
  if (path.length !== total) {
    const base = buildSnakePathBase(cols, rows);
    for (const p of base) if (!path.some(q => q.x === p.x && q.y === p.y)) path.push(p);
  }
  return path;
}

function buildRingsPath(cols, rows) {
  const path = [];
  const layers = Math.ceil(Math.min(cols, rows) / 2);
  for (let layer = 0; layer < layers; layer++) {
    const left = layer, top = layer, right = cols - 1 - layer, bottom = rows - 1 - layer;
    const ring = [];
    if (top <= bottom && left <= right) {
      for (let x = left; x <= right; x++) ring.push({ x, y: top });
      for (let y = top + 1; y <= bottom; y++) ring.push({ x: right, y });
      if (bottom > top) for (let x = right - 1; x >= left; x--) ring.push({ x, y: bottom });
      if (left < right) for (let y = bottom - 1; y > top; y--) ring.push({ x: left, y });
    }
    if (!ring.length) continue;
    if (!path.length) { path.push(...ring); }
    else {
      const last = path[path.length - 1];
      let idx = ring.findIndex(p => Math.abs(p.x - last.x) + Math.abs(p.y - last.y) === 1);
      if (idx === -1) {
        ring.reverse(); idx = ring.findIndex(p => Math.abs(p.x - last.x) + Math.abs(p.y - last.y) === 1);
      }
      if (idx !== -1) {
        const rotated = ring.slice(idx).concat(ring.slice(0, idx));
        path.push(...rotated);
      } else {
        path.push(...ring);
      }
    }
  }
  // Fill any missing cells
  const total = cols * rows;
  if (path.length !== total) {
    const base = buildSnakePathBase(cols, rows);
    for (const p of base) if (!path.some(q => q.x === p.x && q.y === p.y)) path.push(p);
  }
  return path;
}

function buildBlockSnakePath(cols, rows) {
  const path = [];
  for (let by = 0; by < rows; by += 2) {
    const top = by;
    const bottom = Math.min(by + 1, rows - 1);
    const leftToRight = Math.floor(by / 2) % 2 === 0;
    if (leftToRight) {
      for (let x = 0; x < cols; x++) {
        path.push({ x, y: top });
        if (bottom !== top) path.push({ x, y: bottom });
      }
    } else {
      for (let x = cols - 1; x >= 0; x--) {
        path.push({ x, y: top });
        if (bottom !== top) path.push({ x, y: bottom });
      }
    }
  }
  return path;
}

function buildTileSnakePath(cols, rows) {
  const path = [];
  for (let ty = 0; ty < rows; ty += 2) {
    const tiles = [];
    for (let tx = 0; tx < cols; tx += 2) {
      const xs = [tx, Math.min(tx + 1, cols - 1)];
      const ys = [ty, Math.min(ty + 1, rows - 1)];
      const cells = [];
      cells.push({ x: xs[0], y: ys[0] });
      if (xs[1] !== xs[0] || ys[0] !== ys[0]) cells.push({ x: xs[1], y: ys[0] });
      if (ys[1] !== ys[0]) cells.push({ x: xs[1], y: ys[1] });
      if (xs[1] !== xs[0]) cells.push({ x: xs[0], y: ys[1] });
      tiles.push(cells);
    }
    if ((ty / 2) % 2 === 1) tiles.reverse();
    for (const t of tiles) for (const p of t) path.push(p);
  }
  // If something is missing (odd sizes), fill with base snake order
  const total = cols * rows;
  if (path.length !== total) {
    const base = buildSnakePathBase(cols, rows);
    for (const p of base) if (!path.some(q => q.x === p.x && q.y === p.y)) path.push(p);
  }
  return path;
}

function buildCheckerboardPath(cols, rows) {
  // Checkerboard-like appearance by traversing 2-column stripes that alternate
  // vertical direction — yields a visually alternating pattern while remaining
  // a single contiguous snake covering every cell.
  const path = [];
  for (let x = 0; x < cols; x += 2) {
    const left = x;
    const right = Math.min(x + 1, cols - 1);
    const stripe = Math.floor(x / 2);
    if (stripe % 2 === 0) {
      for (let y = 0; y < rows; y++) {
        path.push({ x: left, y });
        if (right !== left) path.push({ x: right, y });
      }
    } else {
      for (let y = rows - 1; y >= 0; y--) {
        path.push({ x: left, y });
        if (right !== left) path.push({ x: right, y });
      }
    }
  }
  // If something is missing (odd sizes), fill with base snake order
  const total = cols * rows;
  if (path.length !== total) {
    const base = buildSnakePathBase(cols, rows);
    for (const p of base) if (!path.some(q => q.x === p.x && q.y === p.y)) path.push(p);
  }
  return path;
}

function buildCornerSpiralPath(cols, rows) {
  // Outward spiral starting at a corner (top-left), grows until all cells visited
  const total = cols * rows;
  const visited = Array.from({ length: rows }, () => Array(cols).fill(false));
  const path = [];
  // start top-left
  let x = 0, y = 0;
  visited[y][x] = true; path.push({ x, y });
  const dirs = [[1,0],[0,1],[-1,0],[0,-1]]; // right, down, left, up
  let stepLen = 1;
  let dirIdx = 0;
  while (path.length < total) {
    for (let rep = 0; rep < 2 && path.length < total; rep++) {
      const [dx, dy] = dirs[dirIdx % 4];
      for (let s = 0; s < stepLen && path.length < total; s++) {
        const nx = x + dx, ny = y + dy;
        if (nx < 0 || ny < 0 || nx >= cols || ny >= rows || visited[ny][nx]) {
          // try to find nearest unvisited neighbor (fallback)
          let found = false;
          for (const [fx, fy] of [[1,0],[-1,0],[0,1],[0,-1]]) {
            const fxn = x + fx, fyn = y + fy;
            if (fxn >= 0 && fyn >= 0 && fxn < cols && fyn < rows && !visited[fyn][fxn]) {
              x = fxn; y = fyn; visited[y][x] = true; path.push({ x, y }); found = true; break;
            }
          }
          if (!found) break;
        } else {
          x = nx; y = ny; visited[y][x] = true; path.push({ x, y });
        }
      }
      dirIdx++;
    }
    stepLen++;
    // safety: if stuck, fill remaining with base snake order
    if (path.length < total && path.length === new Set(path.map(p => `${p.x},${p.y}`)).size) break;
  }
  if (path.length !== total) {
    const base = buildSnakePathBase(cols, rows);
    for (const p of base) if (!path.some(q => q.x === p.x && q.y === p.y)) path.push(p);
  }
  return path;
}

function buildSpokesPath(cols, rows) {
  // 'Radial' spokes implemented as columns starting from center column and alternating
  // outwards; each column is traversed top-to-bottom or bottom-to-top to keep continuity.
  const path = [];
  const total = cols * rows;
  const cx = Math.floor((cols - 1) / 2);
  const colsOrder = [];
  for (let d = 0; d < cols; d++) {
    const offset = Math.floor((d + 1) / 2) * (d % 2 === 0 ? 0 : 1);
    // alternate left/right from center: sequence 0, +1, -1, +2, -2, ...
    let pos;
    if (d === 0) pos = cx;
    else if (d % 2 === 1) pos = cx + Math.ceil(d / 2);
    else pos = cx - Math.ceil(d / 2);
    if (pos < 0) pos = 0; if (pos >= cols) pos = cols - 1;
    if (!colsOrder.includes(pos)) colsOrder.push(pos);
  }
  for (let i = 0; i < colsOrder.length; i++) {
    const col = colsOrder[i];
    if (i % 2 === 0) {
      for (let y = 0; y < rows; y++) path.push({ x: col, y });
    } else {
      for (let y = rows - 1; y >= 0; y--) path.push({ x: col, y });
    }
  }
  // fill any missing cells (in case of duplicates or odd shapes)
  if (path.length !== total) {
    const base = buildSnakePathBase(cols, rows);
    for (const p of base) if (!path.some(q => q.x === p.x && q.y === p.y)) path.push(p);
  }
  return path;
}

function buildCheckerboard2x2Path(cols, rows) {
  // Traverse 2×2 blocks in a checkerboard arrangement.
  const path = [];
  for (let by = 0; by < rows; by += 2) {
    const blockRow = Math.floor(by / 2);
    const blockCols = [];
    for (let bx = 0; bx < cols; bx += 2) blockCols.push(bx);
    if (blockRow % 2 === 1) blockCols.reverse();
    for (const bx of blockCols) {
      const xs = [bx, Math.min(bx + 1, cols - 1)];
      const ys = [by, Math.min(by + 1, rows - 1)];
      // Within a block, traverse in a serpentine to keep continuity
      if ((bx / 2 + blockRow) % 2 === 0) {
        for (let y = ys[0]; y <= ys[1]; y++) {
          for (let x of xs) path.push({ x, y });
        }
      } else {
        for (let y = ys[1]; y >= ys[0]; y--) {
          for (let x of xs) path.push({ x, y });
        }
      }
    }
  }
  // Fill remainder if needed
  const total = cols * rows;
  if (path.length !== total) {
    const base = buildSnakePathBase(cols, rows);
    for (const p of base) if (!path.some(q => q.x === p.x && q.y === p.y)) path.push(p);
  }
  return path;
}

function buildDiagonalStripesPath(cols, rows) {
  // Diagonal stripes: process diagonals in groups of two to create stripe bands
  const path = [];
  const maxS = cols + rows - 2;
  for (let s = 0; s <= maxS; s += 2) {
    const group = [];
    for (let k = 0; k < 2 && s + k <= maxS; k++) {
      const ss = s + k;
      const diag = [];
      const xStart = Math.max(0, ss - (rows - 1));
      const xEnd = Math.min(cols - 1, ss);
      for (let x = xStart; x <= xEnd; x++) {
        const y = ss - x;
        diag.push({ x, y });
      }
      // alternate direction for each stripe for continuity
      if ((Math.floor(s / 2) % 2) === 0) diag.reverse();
      for (const p of diag) group.push(p);
    }
    for (const p of group) path.push(p);
  }
  // Fill remainder
  const total = cols * rows;
  if (path.length !== total) {
    const base = buildSnakePathBase(cols, rows);
    for (const p of base) if (!path.some(q => q.x === p.x && q.y === p.y)) path.push(p);
  }
  return path;
}

function buildPerimeterFirstPath(cols, rows) {
  // Visit full perimeter frames outward->inward, stitching between frames.
  const path = [];
  const layers = Math.ceil(Math.min(cols, rows) / 2);
  for (let layer = 0; layer < layers; layer++) {
    const left = layer, top = layer, right = cols - 1 - layer, bottom = rows - 1 - layer;
    const ring = [];
    for (let x = left; x <= right; x++) ring.push({ x, y: top });
    for (let y = top + 1; y <= bottom; y++) ring.push({ x: right, y });
    if (bottom > top) for (let x = right - 1; x >= left; x--) ring.push({ x, y: bottom });
    if (left < right) for (let y = bottom - 1; y > top; y--) ring.push({ x: left, y });
    if (!ring.length) continue;
    if (!path.length) { path.push(...ring); }
    else {
      // find adjacency and rotate ring to connect
      const last = path[path.length - 1];
      let idx = ring.findIndex(p => Math.abs(p.x - last.x) + Math.abs(p.y - last.y) === 1);
      if (idx === -1) { ring.reverse(); idx = ring.findIndex(p => Math.abs(p.x - last.x) + Math.abs(p.y - last.y) === 1); }
      if (idx !== -1) {
        const rotated = ring.slice(idx).concat(ring.slice(0, idx));
        path.push(...rotated);
      } else {
        path.push(...ring);
      }
    }
  }
  // fill any missing cells
  const total = cols * rows;
  if (path.length !== total) {
    const base = buildSnakePathBase(cols, rows);
    for (const p of base) if (!path.some(q => q.x === p.x && q.y === p.y)) path.push(p);
  }
  return path;
}

function bresenhamLine(x0, y0, x1, y1) {
  const pts = [];
  let dx = Math.abs(x1 - x0), sx = x0 < x1 ? 1 : -1;
  let dy = -Math.abs(y1 - y0), sy = y0 < y1 ? 1 : -1;
  let err = dx + dy;
  while (true) {
    pts.push({ x: x0, y: y0 });
    if (x0 === x1 && y0 === y1) break;
    const e2 = 2 * err;
    if (e2 >= dy) { err += dy; x0 += sx; }
    if (e2 <= dx) { err += dx; y0 += sy; }
  }
  return pts;
}

function buildTrueSpokesPath(cols, rows) {
  // Create radial spokes from center to edge using Bresenham lines, append new unique cells
  const cx = (cols - 1) / 2, cy = (rows - 1) / 2;
  const targets = [];
  // top edge
  for (let x = 0; x < cols; x++) targets.push({ x, y: 0 });
  // right edge
  for (let y = 1; y < rows; y++) targets.push({ x: cols - 1, y });
  // bottom edge
  for (let x = cols - 2; x >= 0; x--) targets.push({ x, y: rows - 1 });
  // left edge
  for (let y = rows - 2; y > 0; y--) targets.push({ x: 0, y });
  const seen = new Set();
  const path = [];
  for (const t of targets) {
    const pts = bresenhamLine(Math.round(cx), Math.round(cy), t.x, t.y);
    for (const p of pts) {
      const k = `${p.x},${p.y}`;
      if (!seen.has(k)) { path.push({ x: p.x, y: p.y }); seen.add(k); }
    }
  }
  // fill missing cells
  const total = cols * rows;
  if (path.length !== total) {
    const base = buildSnakePathBase(cols, rows);
    for (const p of base) if (!path.some(q => q.x === p.x && q.y === p.y)) path.push(p);
  }
  return path;
}

function buildHilbertLikePath(cols, rows) {
  // Recursive split snake: recursively split the longer dimension into slabs and concatenate
  function rec(x0, y0, w, h) {
    if (w === 1) {
      const out = [];
      for (let y = y0; y < y0 + h; y++) out.push({ x: x0, y });
      return out;
    }
    if (h === 1) {
      const out = [];
      for (let x = x0; x < x0 + w; x++) out.push({ x, y: y0 });
      return out;
    }
    if (w >= h) {
      const w1 = Math.floor(w / 2), w2 = w - w1;
      const left = rec(x0, y0, w1, h);
      const right = rec(x0 + w1, y0, w2, h);
      // ensure adjacency: if last(left) adjacent to first(right) OK; else reverse right
      const lastL = left[left.length - 1], firstR = right[0];
      if (Math.abs(lastL.x - firstR.x) + Math.abs(lastL.y - firstR.y) === 1) return left.concat(right);
      else return left.concat(right.reverse());
    } else {
      const h1 = Math.floor(h / 2), h2 = h - h1;
      const top = rec(x0, y0, w, h1);
      const bottom = rec(x0, y0 + h1, w, h2);
      const lastT = top[top.length - 1], firstB = bottom[0];
      if (Math.abs(lastT.x - firstB.x) + Math.abs(lastT.y - firstB.y) === 1) return top.concat(bottom);
      else return top.concat(bottom.reverse());
    }
  }
  const path = rec(0, 0, cols, rows);
  // fill guarantee
  const total = cols * rows;
  if (path.length !== total) {
    const base = buildSnakePathBase(cols, rows);
    for (const p of base) if (!path.some(q => q.x === p.x && q.y === p.y)) path.push(p);
  }
  return path;
}

function buildRandomSnakePath(cols, rows, template = 'auto') {
  // if template specified, choose it deterministically
  if (template && template !== 'auto') {
    let snake = null;
    if (template === 'dfs') {
      const dfspath = buildDFSHamiltonian(cols, rows);
      if (dfspath && dfspath.length === cols * rows) snake = dfspath;
    } else if (template === 'serpentine') snake = buildSnakePathBase(cols, rows);
    else if (template === 'spiral') snake = buildSpiralSnakePath(cols, rows);
    else if (template === 'column') snake = buildColumnSnakePath(cols, rows);
    else if (template === 'diagonal') snake = buildDiagonalSnakePath(cols, rows);
    else if (template === 'center') snake = buildCenterSpiralPath(cols, rows);
    else if (template === 'rings') snake = buildRingsPath(cols, rows);
    else if (template === 'block') snake = buildBlockSnakePath(cols, rows);
    else if (template === 'tile') snake = buildTileSnakePath(cols, rows);
    else if (template === 'checkerboard') snake = buildCheckerboardPath(cols, rows);
    else if (template === 'spokes') snake = buildSpokesPath(cols, rows);
    else if (template === 'truespokes') snake = buildTrueSpokesPath(cols, rows);
    else if (template === 'perimeter') snake = buildPerimeterFirstPath(cols, rows);
    else if (template === 'diagstripes') snake = buildDiagonalStripesPath(cols, rows);
    else if (template === 'checker2') snake = buildCheckerboard2x2Path(cols, rows);
    else if (template === 'hilbert') snake = buildHilbertLikePath(cols, rows);
    else if (template === 'corner') snake = buildCornerSpiralPath(cols, rows);
    // fallback
    if (!snake) snake = buildSnakePathBase(cols, rows);
    // transforms still apply
    const rot = Math.floor(Math.random() * 4);
    snake = snake.map(pt => rotatePoint(pt, rot, cols, rows));
    if (Math.random() < 0.5) snake = snake.map(pt => ({ x: cols - 1 - pt.x, y: pt.y }));
    if (Math.random() < 0.5) snake = snake.map(pt => ({ x: pt.x, y: rows - 1 - pt.y }));
    if (Math.random() < 0.5) snake.reverse();
    return snake;
  }

  // Choose template with weights: DFS 24%, serpentine 20%, spiral 14%, column 14%, diagonal 9%, center 9%, rings 6%, block 2%, tile 2%
  const r = Math.random();
  let snake = null;

  if (r < 0.24) {
    const dfspath = buildDFSHamiltonian(cols, rows);
    if (dfspath && dfspath.length === cols * rows) snake = dfspath;
  } else if (r < 0.42) {
    snake = buildSnakePathBase(cols, rows);
  } else if (r < 0.56) {
    snake = buildSpiralSnakePath(cols, rows);
  } else if (r < 0.70) {
    snake = buildColumnSnakePath(cols, rows);
  } else if (r < 0.78) {
    snake = buildDiagonalSnakePath(cols, rows);
  } else if (r < 0.87) {
    snake = buildCenterSpiralPath(cols, rows);
  } else if (r < 0.90) {
    snake = buildRingsPath(cols, rows);
  } else if (r < 0.93) {
    snake = buildCheckerboardPath(cols, rows);
  } else if (r < 0.95) {
    snake = buildCheckerboard2x2Path(cols, rows);
  } else if (r < 0.96) {
    snake = buildSpokesPath(cols, rows);
  } else if (r < 0.97) {
    snake = buildTrueSpokesPath(cols, rows);
  } else if (r < 0.98) {
    snake = buildCornerSpiralPath(cols, rows);
  } else if (r < 0.985) {
    snake = buildPerimeterFirstPath(cols, rows);
  } else if (r < 0.99) {
    snake = buildDiagonalStripesPath(cols, rows);
  } else if (r < 0.995) {
    snake = buildHilbertLikePath(cols, rows);
  } else {
    snake = buildBlockSnakePath(cols, rows);
  }

  // fallback
  if (!snake) snake = buildSnakePathBase(cols, rows);

  // Random rotation, flips, reversal
  const rot = Math.floor(Math.random() * 4);
  snake = snake.map(pt => rotatePoint(pt, rot, cols, rows));
  if (Math.random() < 0.5) snake = snake.map(pt => ({ x: cols - 1 - pt.x, y: pt.y }));
  if (Math.random() < 0.5) snake = snake.map(pt => ({ x: pt.x, y: rows - 1 - pt.y }));
  if (Math.random() < 0.5) snake.reverse();
  return snake;
}

// ---------- Walls ----------
function blockedByWall(x0, y0, nx, ny) {
  const dx = nx - x0, dy = ny - y0;
  if      (dx === 1 && dy === 0) return walls.has(`${x0},${y0}|right`);
  else if (dx === -1 && dy === 0) return walls.has(`${nx},${ny}|right`);
  else if (dx === 0 && dy === 1)  return walls.has(`${x0},${y0}|down`);
  else if (dx === 0 && dy === -1) return walls.has(`${nx},${ny}|down`);
  return false;
}
function buildShortcutWallsFromSnake(snake, wallPct) {
  walls.clear();
  // Add walls only on edges that are NOT consecutive on the snake (block shortcuts)
  for (let y = 0; y < ROWS; y++) {
    for (let x = 0; x < COLS; x++) {
      if (x < COLS - 1) {
        const a = keyOf(x, y), b = keyOf(x+1, y);
        const i = snake.findIndex(s => keyOf(s.x, s.y) === a);
        const j = snake.findIndex(s => keyOf(s.x, s.y) === b);
        const consecutive = Math.abs(i - j) === 1;
        if (!consecutive && Math.random() < wallPct) walls.add(`${x},${y}|right`);
      }
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

// ---------- Anchors picking (spacing; no fixed ends) ----------
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
  // Sort so anchors are placed along the path order
  return picks.sort((a, b) => a - b);
}

// ---------- Solvability check (Hamiltonian + numbers-in-order) ----------
function isLayoutSolvable(startX, startY, goalX, goalY, timeBudgetMs = 200) {
  // DFS search with pruning: numbered anchors must be visited in strict ascending order
  const total = COLS * ROWS;
  const dirs = [[0,-1],[1,0],[0,1],[-1,0]];

  function canReachAllFrom(sx, sy, visited) {
    // BFS on unvisited cells to ensure they are all reachable from (sx,sy)
    const q = [{ x: sx, y: sy }];
    const seen = new Set([ keyOf(sx, sy) ]);
    let count = 0;
    while (q.length) {
      const p = q.shift();
      for (const [dx, dy] of dirs) {
        const nx = p.x + dx, ny = p.y + dy;
        if (nx < 0 || ny < 0 || nx >= COLS || ny >= ROWS) continue;
        if (blockedByWall(p.x, p.y, nx, ny)) continue;
        const k = keyOf(nx, ny);
        if (visited.has(k) || seen.has(k)) continue;
        seen.add(k); q.push({ x: nx, y: ny }); count++;
      }
    }
    const remaining = total - visited.size;
    // include starting cell in reachable count
    return (count + 1) >= remaining;
  }

  const Knum = K();

  const startNum = getCellNumber(startX, startY);
  if (startNum != null && startNum !== 1) return false; // cannot start on a later-numbered anchor

  let deadline = performance.now() + timeBudgetMs; // allow configurable budget for deeper checks
  let found = false;

  function dfs(x, y, visitedSet, nextRequired) {
    if (found) return;
    if (performance.now() > deadline) return; // give up if taking too long

    // quick connectivity pruning
    if (!canReachAllFrom(x, y, visitedSet)) return;

    if (visitedSet.size === total) {
      // full coverage: require we are on the goal and all numbers were collected
      if (x === goalX && y === goalY && (nextRequired === null)) {
        found = true; return;
      }
      return;
    }

    // neighbors (prioritize cells that satisfy the next required number)
    const neigh = [];
    for (const [dx, dy] of dirs) {
      const nx = x + dx, ny = y + dy;
      if (nx < 0 || ny < 0 || nx >= COLS || ny >= ROWS) continue;
      if (blockedByWall(x, y, nx, ny)) continue;
      const kk = keyOf(nx, ny);
      if (visitedSet.has(kk)) continue;
      neigh.push({ x: nx, y: ny });
    }
    neigh.sort((a, b) => {
      const an = getCellNumber(a.x, a.y), bn = getCellNumber(b.x, b.y);
      if (an === nextRequired) return -1; if (bn === nextRequired) return 1; return 0;
    });

    for (const nb of neigh) {
      if (found) return;
      const kk = keyOf(nb.x, nb.y);
      const num = getCellNumber(nb.x, nb.y);
      // if this cell has a number and it's not the next required, skip
      if (num != null && num !== nextRequired) continue;

      visitedSet.add(kk);
      const savedNext = nextRequired;
      let newNext = nextRequired;
      if (num != null && num === nextRequired) {
        newNext = (nextRequired === Knum) ? null : nextRequired + 1;
      }

      dfs(nb.x, nb.y, visitedSet, newNext);
      if (found) return;
      visitedSet.delete(kk);
      nextRequired = savedNext;
      if (performance.now() > deadline) return;
    }
  }

  const startKey = keyOf(startX, startY);
  const visited = new Set([ startKey ]);
  let initialNext = 1;
  if (startNum === 1) initialNext = (Knum === 1 ? null : 2);
  dfs(startX, startY, visited, initialNext);
  // debug: indicate whether we found a solution within time budget
  if (found) console.debug('isLayoutSolvable: FOUND (budget ' + timeBudgetMs + 'ms)');
  else console.debug('isLayoutSolvable: NOT FOUND (budget ' + timeBudgetMs + 'ms)');
  return found;
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
    // (Goal background removed by request; we just draw the number)
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

  // base grid
  ctx.strokeStyle = "#808995"; ctx.lineWidth = 2;
  for (let y = 0; y <= ROWS; y++) { ctx.beginPath(); ctx.moveTo(0, y * CELL); ctx.lineTo(COLS * CELL, y * CELL); ctx.stroke(); }
  for (let x = 0; x <= COLS; x++) { ctx.beginPath(); ctx.moveTo(x * CELL, 0); ctx.lineTo(x * CELL, ROWS * CELL); ctx.stroke(); }

  // walls (level modes only)
  drawWalls();

  // (Goal background removed)

  // numbers
  drawNumbers();

  // trail (continuous line)
  if (trail.length) {
    ctx.save();
    ctx.strokeStyle = "#00bcd4";
    ctx.lineWidth = Math.max(4, Math.floor(CELL * 0.18));
    ctx.lineJoin = "round"; ctx.lineCap = "round";
    ctx.shadowColor = "rgba(0, 188, 212, 0.45)";
    ctx.shadowBlur  = Math.max(8, Math.floor(CELL * 0.35));
    ctx.beginPath();
    const p0 = trail[0]; ctx.moveTo(p0.x * CELL + CELL/2, p0.y * CELL + CELL/2);
    for (let i = 1; i < trail.length; i++) { const p = trail[i]; ctx.lineTo(p.x * CELL + CELL/2, p.y * CELL + CELL/2); }
    ctx.stroke();
    ctx.restore();
  }

  // player dot (glow)
  ctx.save();
  ctx.fillStyle = "#e74c3c"; ctx.shadowColor = "rgba(231,76,60,0.6)";
  ctx.shadowBlur = Math.max(12, Math.floor(CELL * 0.5));
  ctx.beginPath(); ctx.arc(player.x * CELL + CELL/2, player.y * CELL + CELL/2, Math.max(8, CELL/3), 0, Math.PI*2); ctx.fill();
  ctx.restore();
}

// ---------- Layout helpers ----------
function buildGrid(cols, rows) {
  COLS = cols; ROWS = rows;
  CELL = Math.floor(canvas.width / COLS);
  grid = Array.from({ length: ROWS }, (_, y) => Array.from({ length: COLS }, (_, x) => ({ x, y })));
}

// Zip generator: randomized snake + rotated labels (moves where 12 lands)
async function generateZip6x6() {
  // Attempt generation until we find a layout that passes the solver (rare failures possible)
  const MAX_ATTEMPTS = 50;
  let attempt = 0;
  let solvable = false;

  while (attempt < MAX_ATTEMPTS && !solvable) {
    attempt++;
    buildGrid(6, 6);

    const snake = buildRandomSnakePath(6, 6, document.getElementById('templateSelect')?.value ?? 'auto');
    anchors = []; anchorsMap.clear(); walls.clear();

    const Knum = 12;
    const idxs = pickIndicesWithMinGap(snake.length, Knum, 2);
    const shift = Math.floor(Math.random() * Knum); // rotate labels so "1" starts at a random anchor

    for (let j = 0; j < Knum; j++) {
      const idx = idxs[j];
      const num = ((j - shift + Knum) % Knum) + 1; // cyclic rotation: 1..K along path
      const { x, y } = snake[idx];
      anchors.push({ x, y, n: num });
      anchorsMap.set(`${x},${y}`, num);
    }

    const startA = anchors.find(a => a.n === 1);
    const finalA = anchors.find(a => a.n === Knum);

    player = { x: startA.x, y: startA.y };
    goal   = { x: finalA.x, y: finalA.y };
    trail  = [{ x: player.x, y: player.y }];
    visitedCells = new Set([ `${player.x},${player.y}` ]);

    gameOver = false; hasStarted = false; elapsed = 0; startTime = null;

    // Let UI update
    tell(`Searching for solvable layout (attempt ${attempt}/${MAX_ATTEMPTS})...`);
    await new Promise(r => setTimeout(r, 0));

    // Validate solvability (fast check with pruning). If not solvable, retry.
    solvable = isLayoutSolvable(player.x, player.y, goal.x, goal.y, 400);
    if (solvable) {
      // perform a stricter confirmation check (longer budget) to reduce false positives
      const confirmed = isLayoutSolvable(player.x, player.y, goal.x, goal.y, 2000);
      if (!confirmed) {
        solvable = false;
        console.warn(`Solvability quick-check passed but confirmation failed (attempt ${attempt}). Retrying...`);
        tell(`Generated zip layout uncertainly solvable (attempt ${attempt}). Retrying...`);
        await new Promise(r => setTimeout(r, 0));
      }
    } else {
      tell(`Generated zip layout not solvable (attempt ${attempt}). Retrying...`);
      await new Promise(r => setTimeout(r, 0));
    }
  }

  if (!solvable) {
    tell(`Couldn't generate a solvable Zip layout after ${MAX_ATTEMPTS} attempts. Try again.`);
  } else {
    // success
    currentTargetMs = 60_000; updateTimeTargetDisplay(0);
    savedLayout = { mode: "zip", cols: COLS, rows: ROWS, playerStart: { ...player }, goalPos: { ...goal }, anchors: anchors.map(a => ({ ...a })), walls: Array.from(walls), template: document.getElementById('templateSelect')?.value ?? 'auto' };
    tell("New Zip layout — solvable.");
    draw();
  }
}

// Level generator: randomized snake + rotated labels + optional shortcut walls
async function generateLevel(def) {
  // Attempt generation until we find a layout that passes the solver
  const MAX_ATTEMPTS = 50;
  let attempt = 0;
  let solvable = false;

  while (attempt < MAX_ATTEMPTS && !solvable) {
    attempt++;
    buildGrid(def.cols, def.rows);

    const snake = buildRandomSnakePath(def.cols, def.rows, document.getElementById('templateSelect')?.value ?? 'auto');
    anchors = []; anchorsMap.clear(); walls.clear();

    const Knum = def.K;
    const idxs = pickIndicesWithMinGap(snake.length, Knum, def.minGap);
    const shift = Math.floor(Math.random() * Knum);

    for (let j = 0; j < Knum; j++) {
      const idx = idxs[j];
      const num = ((j - shift + Knum) % Knum) + 1;
      const { x, y } = snake[idx];
      anchors.push({ x, y, n: num });
      anchorsMap.set(`${x},${y}`, num);
    }

    buildShortcutWallsFromSnake(snake, def.wallPct);

    const startA = anchors.find(a => a.n === 1);
    const finalA = anchors.find(a => a.n === Knum);

    player = { x: startA.x, y: startA.y };
    goal   = { x: finalA.x, y: finalA.y };
    trail  = [{ x: player.x, y: player.y }];
    visitedCells = new Set([ `${player.x},${player.y}` ]);

    gameOver = false; hasStarted = false; elapsed = 0; startTime = null;

    // Allow UI to update
    tell(`Searching for solvable ${def.label} layout (attempt ${attempt}/${MAX_ATTEMPTS})...`);
    await new Promise(r => setTimeout(r, 0));

    // Quick + confirmation checks
    solvable = isLayoutSolvable(player.x, player.y, goal.x, goal.y, 400);
    if (solvable) {
      const confirmed = isLayoutSolvable(player.x, player.y, goal.x, goal.y, 2000);
      if (!confirmed) {
        solvable = false;
        console.warn(`Level solvability confirmation failed (attempt ${attempt}). Retrying...`);
        tell(`Generated ${def.label} layout uncertainly solvable (attempt ${attempt}). Retrying...`);
        await new Promise(r => setTimeout(r, 0));
      }
    } else {
      tell(`Generated ${def.label} layout not solvable (attempt ${attempt}). Retrying...`);
      await new Promise(r => setTimeout(r, 0));
    }
  }

  if (!solvable) {
    tell(`Couldn't generate a solvable ${def.label} layout after ${MAX_ATTEMPTS} attempts. Try again.`);
  } else {
    // success
    currentTargetMs = def.targetMs ?? 60_000;
    savedLayout = { mode: def.key ?? "level", cols: COLS, rows: ROWS, playerStart: { ...player }, goalPos: { ...goal }, anchors: anchors.map(a => ({ ...a })), walls: Array.from(walls), template: document.getElementById('templateSelect')?.value ?? 'auto' };
    tell(`New ${def.label} layout — solvable.`);
    updateTimeTargetDisplay(0);
    draw();
  }
}

// ---------- Movement (free; allow backdraw ONLY 1 step; block other revisits) ----------
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

  // If target already in trail:
  const idx = trail.findIndex(p => p.x === nx && p.y === ny);
  if (idx !== -1) {
    // Allow ONLY immediate previous cell backdraw
    if (isImmediateBack(nx, ny)) {
      // Pop last segment and move player to previous cell (trail already ends there)
      trail.pop();
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
  visitedCells.add(`${player.x},${player.y}`);

  draw(); updateTimeTargetDisplay(elapsed);

  // ----- Win condition -----
  // A) full coverage: REQUIRE the current trail to include EVERY cell (no lingering visited credit)
  const walkedAll = trail.length === COLS * ROWS;

  // B) numbers first-visit order is 1..K (derived from the current trail)
  const order = numbersFirstOrder();
  const must  = Array.from({ length: K() }, (_, i) => i + 1);
  const visitedInOrder = (order.length === K() && order.every((n, i) => n === must[i]));

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


levelSel?.addEventListener("change", async (e) => {
  const key = e.target.value;
  const def = MODES.find(m => m.key === key);
  if (!def) return;
  lastModeKey = key;
  if (def.kind === "zip") { currentTargetMs = 60_000; await generateZip6x6(); }
  else { currentTargetMs = def.targetMs ?? 60_000; await generateLevel(def); }
  updateTimeTargetDisplay(0);
  draw();
  tell(`Mode: ${def.label}`);
});

// Announce template selection changes
const tplSel = document.getElementById('templateSelect');
if (tplSel) tplSel.addEventListener('change', (e) => { tell(`Template: ${e.target.selectedOptions[0].text}`); });

document.getElementById("new")?.addEventListener("click", async () => {
  const def = MODES.find(m => m.key === lastModeKey);
  if (!def || def.kind === "zip") { currentTargetMs = 60_000; tell("New Zip layout."); await generateZip6x6(); }
  else { currentTargetMs = def.targetMs ?? 60_000; tell(`New ${def.label} layout.`); await generateLevel(def); }
  updateTimeTargetDisplay(0);
  // save layout for restart
  savedLayout = { mode: lastModeKey, cols: COLS, rows: ROWS, playerStart: { ...player }, goalPos: { ...goal }, anchors: anchors.map(a => ({ ...a })), walls: Array.from(walls), template: document.getElementById('templateSelect')?.value ?? 'auto' };
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
  // restore template selection if available
  const tplSel = document.getElementById('templateSelect');
  if (tplSel && savedLayout.template) tplSel.value = savedLayout.template;
  draw();
   tell("Restarted same layout.");
});

// Verify button: run extended solvability check and report
document.getElementById('verifySolvable')?.addEventListener('click', () => {
  if (!player || !goal) { tell('No layout loaded yet.'); return; }
  tell('Running extended solvability check...');
  // run with a larger budget and report
  setTimeout(() => {
    const ok = isLayoutSolvable(player.x, player.y, goal.x, goal.y, 2000);
    if (ok) {
      tell('Verification: layout is solvable ✅');
      console.info('Verification: layout is solvable');
    } else {
      tell('Verification: layout NOT solvable ⚠️');
      console.warn('Verification: layout NOT solvable');
      // dump layout to console and attempt to copy to clipboard for sharing/debug
      const dump = { cols: COLS, rows: ROWS, anchors: anchors.map(a => ({...a})), walls: Array.from(walls), player: {...player}, goal: {...goal} };
      console.info('Layout dump (copy/share):', dump);
      try { navigator.clipboard.writeText(JSON.stringify(dump)); tell('Layout copied to clipboard for debugging.'); }
      catch (e) { /* ignore */ }
    }
  }, 20);
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
// Default start: Zip 6×6 (12)
currentTargetMs = 60_000;
generateZip6x6();
