(function () {
  'use strict';

  // ─── Pool ball colours (1–15) ────────────────────────────────────────────────
  const BALL_COLORS = [
    '#f5de00', // 1  yellow
    '#0057a8', // 2  blue
    '#cc2200', // 3  red
    '#7b2d8b', // 4  purple
    '#e87000', // 5  orange
    '#007a3d', // 6  green
    '#8b2020', // 7  maroon
    '#111111', // 8  black
    '#f5de00', // 9  yellow  (stripe)
    '#0057a8', // 10 blue    (stripe)
    '#cc2200', // 11 red     (stripe)
    '#7b2d8b', // 12 purple  (stripe)
    '#e87000', // 13 orange  (stripe)
    '#007a3d', // 14 green   (stripe)
    '#8b2020', // 15 maroon  (stripe)
  ];

  // ─── Physics ─────────────────────────────────────────────────────────────────
  const FRICTION_K   = 1.4;
  const WALL_REST    = 0.62;
  const BALL_REST    = 0.90;
  const HIT_COOLDOWN = 380;
  const PHYS_ITERS   = 5;
  const SPEEDS = { slow: 220, normal: 130, fast: 68 };
  const POWERS = { low: 320, med: 580, high: 950, max: 1500 };

  // ─── Mutable settings (live-editable during play) ────────────────────────────
  const settings = {
    speed:       'normal',
    power:       'med',
    ballCount:   10,
    timeLimits:  [20, 50, 70],
    multipliers: [6, 4, 2],
  };

  // ─── Game state ───────────────────────────────────────────────────────────────
  // 'start' | 'playing' | 'round_clear' | 'gameover'
  let gameState = 'start';
  let snake, dir, nextDir;
  let balls, pottedBalls;
  let score, bestScore, totalScore;
  let roundNumber, completedRounds;
  let lastRoundScore, lastRoundMultiplier;
  let gameStartTime, elapsed;
  let lastStepTime;
  let msgText, msgExpiry;
  let growPending = 0;
  let lastFrameTime = 0;
  let comboCount = 0;
  let lastPotTime = 0;
  const COMBO_WINDOW = 5000;
  const COMBO_MAX = 6;

  // ─── Canvas / layout globals ──────────────────────────────────────────────────
  let canvas, ctx, W, H;
  let CUSHION, TABLE_X, TABLE_Y, TABLE_W, TABLE_H;
  let POTTED_H;
  let POCKET_R, POCKETS;
  let INNER_LEFT, INNER_TOP, INNER_W, INNER_H;
  let CELL_W, GRID_COLS, GRID_ROWS, GRID_TOP;
  let BALL_R;

  // ─────────────────────────────────────────────────────────────────────────────
  // Layout
  // ─────────────────────────────────────────────────────────────────────────────
  function calcLayout() {
    const wrap = canvas.parentElement;
    const size = wrap.clientWidth;
    const dpr  = window.devicePixelRatio || 1;
    canvas.width  = size * dpr;
    canvas.height = size * dpr;
    canvas.style.width  = size + 'px';
    canvas.style.height = size + 'px';
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    W = size;
    H = size;

    CUSHION  = Math.max(20, Math.round(W * 0.052));
    POTTED_H = Math.round(H * 0.11);

    TABLE_X = CUSHION;
    TABLE_Y = CUSHION;
    TABLE_W = W - 2 * CUSHION;
    TABLE_H = H - 2 * CUSHION - POTTED_H;

    POCKET_R = Math.max(10, CUSHION * 0.82);

    // Corner pockets: same visual but larger detection zone.
    // Mid pockets: same visual size as corners, directional-only potting.
    const midDrawR = POCKET_R;
    const midPotR  = POCKET_R * 1.30;
    const crnPotR  = POCKET_R * 1.50;

    POCKETS = [
      { x: TABLE_X,               y: TABLE_Y,           drawR: POCKET_R, potR: crnPotR, directional: false }, // TL
      { x: TABLE_X + TABLE_W / 2, y: TABLE_Y,           drawR: midDrawR, potR: midPotR, directional: true  }, // TM
      { x: TABLE_X + TABLE_W,     y: TABLE_Y,           drawR: POCKET_R, potR: crnPotR, directional: false }, // TR
      { x: TABLE_X,               y: TABLE_Y + TABLE_H, drawR: POCKET_R, potR: crnPotR, directional: false }, // BL
      { x: TABLE_X + TABLE_W / 2, y: TABLE_Y + TABLE_H, drawR: midDrawR, potR: midPotR, directional: true  }, // BM
      { x: TABLE_X + TABLE_W,     y: TABLE_Y + TABLE_H, drawR: POCKET_R, potR: crnPotR, directional: false }, // BR
    ];

    // Snake grid sits inside the table, clear of corner pockets
    const pad  = POCKET_R * 0.55;
    INNER_LEFT = TABLE_X + pad;
    INNER_TOP  = TABLE_Y + pad;
    INNER_W    = TABLE_W - 2 * pad;
    INNER_H    = TABLE_H - 2 * pad;

    GRID_COLS = 18;
    CELL_W    = INNER_W / GRID_COLS;
    GRID_ROWS = Math.max(1, Math.floor(INNER_H / CELL_W)) + 1;
    GRID_TOP  = INNER_TOP + (INNER_H - GRID_ROWS * CELL_W) / 2;
    BALL_R    = CELL_W * 0.74;
  }

  function cellToPixel(gx, gy) {
    return {
      x: INNER_LEFT + (gx + 0.5) * CELL_W,
      y: GRID_TOP   + (gy + 0.5) * CELL_W,
    };
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Triangle rack builder
  // ─────────────────────────────────────────────────────────────────────────────
  function createTriangle(count) {
    const rowMap  = { 6: 3, 10: 4, 15: 5 };
    const numRows = rowMap[count] || 4;

    const spacing = BALL_R * 2.08;
    const dx      = spacing * Math.sqrt(3) / 2;

    const triW  = (numRows - 1) * dx;
    const apexX = TABLE_X + TABLE_W * 0.62 - triW / 2;
    const apexY = TABLE_Y + TABLE_H * 0.5;

    const list = [];
    let n = 0;
    for (let r = 0; r < numRows && n < count; r++) {
      const rowX    = apexX + r * dx;
      const numBall = r + 1;
      const startY  = apexY - (numBall - 1) * spacing / 2;
      for (let i = 0; i < numBall && n < count; i++) {
        list.push({
          x:              rowX,
          y:              startY + i * spacing,
          vx:             0,
          vy:             0,
          radius:         BALL_R,
          number:         n + 1,
          stripe:         n >= 8,
          color:          BALL_COLORS[n],
          potted:         false,
          hitCooldown:    0,
          wallBounces:    0,
          chainHot:       false,
          chainHotExpiry: 0,
        });
        n++;
      }
    }
    return list;
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Physics step (every animation frame)
  // ─────────────────────────────────────────────────────────────────────────────
  function physicsStep(dt) {
    const dtS   = dt / 1000;
    const decay = Math.exp(-FRICTION_K * dtS);
    const minX  = TABLE_X + BALL_R;
    const maxX  = TABLE_X + TABLE_W - BALL_R;
    const minY  = TABLE_Y + BALL_R;
    const maxY  = TABLE_Y + TABLE_H - BALL_R;

    for (const b of balls) {
      if (b.potted) continue;

      b.x += b.vx * dtS;
      b.y += b.vy * dtS;
      b.vx *= decay;
      b.vy *= decay;

      if (Math.sqrt(b.vx * b.vx + b.vy * b.vy) < 1.5) { b.vx = 0; b.vy = 0; }

      // Cushion bounces
      if (b.x < minX) { b.x = minX; b.vx =  Math.abs(b.vx) * WALL_REST; b.wallBounces++; }
      if (b.x > maxX) { b.x = maxX; b.vx = -Math.abs(b.vx) * WALL_REST; b.wallBounces++; }
      if (b.y < minY) { b.y = minY; b.vy =  Math.abs(b.vy) * WALL_REST; b.wallBounces++; }
      if (b.y > maxY) { b.y = maxY; b.vy = -Math.abs(b.vy) * WALL_REST; b.wallBounces++; }

      // Pocket detection
      for (const p of POCKETS) {
        const pdx  = b.x - p.x;
        const pdy  = b.y - p.y;
        const dist = Math.sqrt(pdx * pdx + pdy * pdy);
        if (dist < p.potR + BALL_R * 0.25) {
          if (p.directional) {
            const dot = b.vx * (-pdx) + b.vy * (-pdy);
            if (dot <= 0) continue;
          }
          potBall(b);
          break;
        }
      }

      if (b.hitCooldown > 0) b.hitCooldown = Math.max(0, b.hitCooldown - dt);
    }

    // Ball–ball elastic collisions
    const active = balls.filter(b => !b.potted);
    for (let iter = 0; iter < PHYS_ITERS; iter++) {
      for (let i = 0; i < active.length; i++) {
        for (let j = i + 1; j < active.length; j++) {
          resolvePair(active[i], active[j]);
        }
      }
    }
  }

  function resolvePair(a, b) {
    const dx   = b.x - a.x;
    const dy   = b.y - a.y;
    const dist = Math.sqrt(dx * dx + dy * dy);
    const min  = a.radius + b.radius;
    if (dist >= min || dist < 0.001) return;

    const nx  = dx / dist;
    const ny  = dy / dist;
    const sep = (min - dist) / 2;
    a.x -= nx * sep;  a.y -= ny * sep;
    b.x += nx * sep;  b.y += ny * sep;

    const dvx = a.vx - b.vx;
    const dvy = a.vy - b.vy;
    const dot = dvx * nx + dvy * ny;
    if (dot <= 0) return;

    const imp = dot * BALL_REST;
    a.vx -= imp * nx;  a.vy -= imp * ny;
    b.vx += imp * nx;  b.vy += imp * ny;

    // Mark chain-hot: if one ball was freshly hit by the snake, the other is now "in play"
    const CHAIN_HOT_MS = 3000;
    const CHAIN_THRESHOLD = 60;
    if (imp > CHAIN_THRESHOLD) {
      const now = performance.now();
      if (a.hitCooldown > HIT_COOLDOWN * 0.4 && !b.chainHot) {
        b.chainHot = true; b.chainHotExpiry = now + CHAIN_HOT_MS;
      }
      if (b.hitCooldown > HIT_COOLDOWN * 0.4 && !a.chainHot) {
        a.chainHot = true; a.chainHotExpiry = now + CHAIN_HOT_MS;
      }
    }
  }

  function potBall(ball) {
    ball.potted = true;
    ball.vx = 0;
    ball.vy = 0;
    pottedBalls.push({ ...ball });

    // Combo multiplier
    const now = performance.now();
    if (comboCount > 0 && now - lastPotTime < COMBO_WINDOW) {
      comboCount = Math.min(comboCount + 1, COMBO_MAX);
    } else {
      comboCount = 1;
    }
    lastPotTime = now;

    let ballScore = comboCount;
    let msg = comboCount > 1 ? 'COMBO \xD7' + comboCount + '!' : 'POT! +1';

    // Bank shot bonus (+1 per cushion bounce, max +3)
    const bankBonus = Math.min(ball.wallBounces, 3);
    if (bankBonus > 0) {
      ballScore += bankBonus;
      msg = 'BANK \xD7' + ball.wallBounces + '! +' + ballScore;
    }

    // Chain reaction bonus (+2 if ball was knocked in by another ball)
    if (ball.chainHot && now < ball.chainHotExpiry) {
      ballScore += 2;
      msg = 'CHAIN! +' + ballScore;
    }

    score += ballScore;
    growPending += 1;
    updateScoreUI();
    showMsg(msg);
    if (pottedBalls.length === balls.length) completeRound();
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Snake
  // ─────────────────────────────────────────────────────────────────────────────
  function initGame() {
    // Full reset — snake back to 3 segments
    const midRow = Math.floor(GRID_ROWS / 2);
    snake = [
      { x: 2, y: midRow },
      { x: 1, y: midRow },
      { x: 0, y: midRow },
    ];
    dir     = { dx: 1, dy: 0 };
    nextDir = null;

    balls            = createTriangle(settings.ballCount);
    pottedBalls      = [];
    score            = 0;
    totalScore       = 0;
    roundNumber      = 1;
    completedRounds  = 0;
    lastRoundScore   = 0;
    lastRoundMultiplier = 0;
    elapsed          = 0;
    growPending      = 0;
    comboCount       = 0;
    lastPotTime      = 0;
    gameStartTime    = performance.now();
    lastStepTime     = performance.now();
    msgText          = '';
    msgExpiry        = 0;
    gameState        = 'playing';
    updateScoreUI();
  }

  function startNextRound() {
    // Re-rack balls; snake keeps its current length and direction
    roundNumber++;
    balls       = createTriangle(settings.ballCount);
    pottedBalls = [];
    score       = 0;
    elapsed     = 0;
    comboCount  = 0;
    lastPotTime = 0;
    gameStartTime = performance.now();
    lastStepTime  = performance.now();
    msgText     = '';
    msgExpiry   = 0;
    gameState   = 'playing';
    setButtonVisibility('playing');
    updateScoreUI();
  }

  function setButtonVisibility(state) {
    const actionBtn    = document.getElementById('action-btn');
    const nextRoundBtn = document.getElementById('next-round-btn');
    const restartBtn   = document.getElementById('restart-btn');
    if (!actionBtn) return;
    if (state === 'round_clear') {
      actionBtn.hidden    = true;
      nextRoundBtn.hidden = false;
      restartBtn.hidden   = false;
    } else if (state === 'playing') {
      actionBtn.hidden    = true;
      nextRoundBtn.hidden = true;
      restartBtn.hidden   = false;
    } else { // gameover / start
      actionBtn.hidden    = false;
      nextRoundBtn.hidden = true;
      restartBtn.hidden   = true;
    }
  }

  function snakeStep() {
    if (nextDir) { dir = nextDir; nextDir = null; }

    const head = snake[0];
    const nx   = head.x + dir.dx;
    const ny   = head.y + dir.dy;

    // Wrap around walls
    const wx = (nx + GRID_COLS) % GRID_COLS;
    const wy = (ny + GRID_ROWS) % GRID_ROWS;

    // Self-collision → game over
    for (let i = 0; i < snake.length - 1; i++) {
      if (snake[i].x === wx && snake[i].y === wy) {
        endGame();
        return;
      }
    }

    snake.unshift({ x: wx, y: wy });
    if (growPending > 0) {
      growPending--;
    } else {
      snake.pop();
    }

    // Hit any ball that overlaps the new head cell
    const { x: hx, y: hy } = cellToPixel(wx, wy);
    for (const b of balls) {
      if (b.potted || b.hitCooldown > 0) continue;
      const ddx = b.x - hx;
      const ddy = b.y - hy;
      const dist = Math.sqrt(ddx * ddx + ddy * ddy);
      if (dist < b.radius + CELL_W * 0.5) {
        // Push along collision normal (head→ball centre)
        const cnx = dist > 0.001 ? ddx / dist : dir.dx;
        const cny = dist > 0.001 ? ddy / dist : dir.dy;
        b.vx += cnx * POWERS[settings.power];
        b.vy += cny * POWERS[settings.power];
        b.hitCooldown    = HIT_COOLDOWN;
        b.wallBounces    = 0;
        b.chainHot       = false;
      }
    }
  }

  function queueDir(dx, dy) {
    if (dx === -dir.dx && dy === -dir.dy) return;
    nextDir = { dx, dy };
  }

  // Called when all balls in a round are potted
  function completeRound() {
    elapsed = (performance.now() - gameStartTime) / 1000;
    const [t1, t2, t3] = settings.timeLimits;
    const [m1, m2, m3] = settings.multipliers;
    if      (elapsed <= t1) lastRoundMultiplier = m1;
    else if (elapsed <= t2) lastRoundMultiplier = m2;
    else if (elapsed <= t3) lastRoundMultiplier = m3;
    else                    lastRoundMultiplier = 1;
    lastRoundScore = Math.round(score * lastRoundMultiplier);
    totalScore    += lastRoundScore;
    completedRounds++;
    saveBest();
    gameState = 'round_clear';
    setButtonVisibility('round_clear');
    updateScoreUI();
  }

  // Called when snake eats itself
  function endGame() {
    elapsed = (performance.now() - gameStartTime) / 1000;
    totalScore += score; // partial round at ×1
    saveBest();
    gameState = 'gameover';
    setButtonVisibility('gameover');
    updateScoreUI();
  }

  function saveBest() {
    if (totalScore > bestScore) {
      bestScore = totalScore;
      localStorage.setItem('poolsnake_best', String(bestScore));
    }
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Rendering
  // ─────────────────────────────────────────────────────────────────────────────
  function draw(ts) {
    ctx.clearRect(0, 0, W, H);
    drawTable();
    if (gameState !== 'start') {
      drawGrid();
      drawSnake();
      drawBalls();
    }
    drawPottedStrip();
    drawHUD(ts);
    if (gameState !== 'playing') drawOverlay(ts);
  }

  // ── Table & pockets ────────────────────────────────────────────────────────
  function drawTable() {
    ctx.fillStyle = '#080808';
    ctx.fillRect(0, 0, W, H);

    ctx.fillStyle = '#155724';
    rrFill(
      CUSHION * 0.32, CUSHION * 0.32,
      W - CUSHION * 0.64, H - CUSHION * 0.64 - POTTED_H,
      CUSHION * 0.5
    );

    ctx.fillStyle = '#1b5e20';
    ctx.fillRect(TABLE_X, TABLE_Y, TABLE_W, TABLE_H);

    ctx.strokeStyle = 'rgba(0,0,0,0.06)';
    ctx.lineWidth = 1;
    for (let y = TABLE_Y; y < TABLE_Y + TABLE_H; y += 7) {
      ctx.beginPath();
      ctx.moveTo(TABLE_X, y);
      ctx.lineTo(TABLE_X + TABLE_W, y);
      ctx.stroke();
    }

    ctx.strokeStyle = 'rgba(255,255,255,0.07)';
    ctx.lineWidth = 1.5;
    ctx.strokeRect(TABLE_X, TABLE_Y, TABLE_W, TABLE_H);

    // Pockets — recessed socket look
    for (const p of POCKETS) {
      const pr = p.drawR;

      ctx.beginPath();
      ctx.arc(p.x, p.y, pr * 1.22, 0, Math.PI * 2);
      ctx.fillStyle = '#080808';
      ctx.fill();

      ctx.beginPath();
      ctx.arc(p.x, p.y, pr * 1.10, 0, Math.PI * 2);
      ctx.fillStyle = '#1a1008';
      ctx.fill();

      ctx.beginPath();
      ctx.arc(p.x, p.y, pr, 0, Math.PI * 2);
      ctx.fillStyle = '#020202';
      ctx.fill();

      const grad = ctx.createRadialGradient(p.x, p.y, pr * 0.2, p.x, p.y, pr);
      grad.addColorStop(0,   'rgba(0,0,0,0.92)');
      grad.addColorStop(0.7, 'rgba(0,0,0,0.45)');
      grad.addColorStop(1,   'rgba(0,0,0,0)');
      ctx.beginPath();
      ctx.arc(p.x, p.y, pr, 0, Math.PI * 2);
      ctx.fillStyle = grad;
      ctx.fill();

      ctx.beginPath();
      ctx.arc(p.x, p.y, pr, Math.PI * 1.08, Math.PI * 1.72);
      ctx.strokeStyle = 'rgba(255,240,180,0.22)';
      ctx.lineWidth = 1.5;
      ctx.stroke();
    }

    ctx.fillStyle = '#0c0c0c';
    ctx.fillRect(0, H - POTTED_H, W, POTTED_H);
    ctx.strokeStyle = 'rgba(255,255,255,0.07)';
    ctx.lineWidth = 1;
    ctx.beginPath();
    ctx.moveTo(0, H - POTTED_H);
    ctx.lineTo(W, H - POTTED_H);
    ctx.stroke();
  }

  // ── Grid ───────────────────────────────────────────────────────────────────
  function drawGrid() {
    const gridW = GRID_COLS * CELL_W;
    const gridH = GRID_ROWS * CELL_W;

    ctx.strokeStyle = 'rgba(255,255,255,0.035)';
    ctx.lineWidth = 0.5;
    for (let c = 0; c <= GRID_COLS; c++) {
      const x = INNER_LEFT + c * CELL_W;
      ctx.beginPath();
      ctx.moveTo(x, GRID_TOP);
      ctx.lineTo(x, GRID_TOP + gridH);
      ctx.stroke();
    }
    for (let r = 0; r <= GRID_ROWS; r++) {
      const y = GRID_TOP + r * CELL_W;
      ctx.beginPath();
      ctx.moveTo(INNER_LEFT, y);
      ctx.lineTo(INNER_LEFT + gridW, y);
      ctx.stroke();
    }

    // Visible boundary showing the snake's playfield
    ctx.strokeStyle = 'rgba(0,255,65,0.28)';
    ctx.lineWidth = 1.5;
    ctx.setLineDash([4, 6]);
    ctx.strokeRect(INNER_LEFT, GRID_TOP, gridW, gridH);
    ctx.setLineDash([]);
  }

  // ── Snake ──────────────────────────────────────────────────────────────────
  function drawSnake() {
    const len = snake.length;
    for (let i = len - 1; i >= 0; i--) {
      const { x: px, y: py } = cellToPixel(snake[i].x, snake[i].y);
      const pad   = CELL_W * 0.12;
      const sz    = CELL_W - pad * 2;
      const alpha = i === 0 ? 1 : Math.max(0.25, 1 - (i / len) * 0.78);
      ctx.globalAlpha = alpha;
      if (i === 0) { ctx.shadowColor = '#00ff41'; ctx.shadowBlur = 14; }
      ctx.fillStyle = '#00ff41';
      rrFill(px - sz / 2, py - sz / 2, sz, sz, sz * 0.28);
      ctx.shadowBlur = 0;
    }
    ctx.globalAlpha = 1;
  }

  // ── Balls ──────────────────────────────────────────────────────────────────
  function drawBalls() {
    for (const b of balls) {
      if (!b.potted) drawOneBall(b.x, b.y, b.color, b.number, b.stripe, 1);
    }
  }

  function drawOneBall(x, y, color, number, stripe, alpha) {
    const r = BALL_R;
    ctx.globalAlpha = alpha;
    ctx.shadowColor = color;
    ctx.shadowBlur  = 9;

    ctx.beginPath();
    ctx.arc(x, y, r, 0, Math.PI * 2);
    ctx.fillStyle = stripe ? '#f0f0f0' : color;
    ctx.fill();

    if (stripe) {
      ctx.save();
      ctx.beginPath();
      ctx.arc(x, y, r, 0, Math.PI * 2);
      ctx.clip();
      ctx.fillStyle = color;
      ctx.fillRect(x - r, y - r * 0.42, r * 2, r * 0.84);
      ctx.restore();
    }

    ctx.shadowBlur = 0;

    if (r > 9) {
      ctx.beginPath();
      ctx.arc(x, y, r * 0.4, 0, Math.PI * 2);
      ctx.fillStyle = '#ffffff';
      ctx.fill();
      ctx.fillStyle = '#111111';
      ctx.font = 'bold ' + Math.max(7, Math.floor(r * 0.52)) + 'px sans-serif';
      ctx.textAlign    = 'center';
      ctx.textBaseline = 'middle';
      ctx.fillText(number, x, y + r * 0.04);
    }

    ctx.beginPath();
    ctx.arc(x - r * 0.28, y - r * 0.28, r * 0.19, 0, Math.PI * 2);
    ctx.fillStyle = 'rgba(255,255,255,0.48)';
    ctx.fill();

    ctx.globalAlpha = 1;
  }

  // ── Potted strip ───────────────────────────────────────────────────────────
  function drawPottedStrip() {
    if (!pottedBalls || pottedBalls.length === 0) return;

    const stripY  = H - POTTED_H;
    const labelSz = Math.max(6, Math.floor(POTTED_H * 0.16));
    const r       = Math.min(BALL_R * 0.56, POTTED_H * 0.29);

    ctx.fillStyle    = 'rgba(255,255,255,0.27)';
    ctx.font         = labelSz + 'px "Press Start 2P", monospace';
    ctx.textAlign    = 'left';
    ctx.textBaseline = 'middle';
    ctx.fillText('POTTED', CUSHION * 0.5, stripY + POTTED_H * 0.27);

    const startX  = CUSHION * 0.5 + W * 0.13;
    const ballY   = stripY + POTTED_H * 0.66;
    const spacing = r * 2.5;

    for (let i = 0; i < pottedBalls.length; i++) {
      const b = pottedBalls[i];
      drawOneBall(startX + i * spacing, ballY, b.color, b.number, b.stripe, 0.92);
    }
  }

  // ── HUD ────────────────────────────────────────────────────────────────────
  function drawHUD(ts) {
    if (gameState === 'playing') {
      elapsed = (performance.now() - gameStartTime) / 1000;
    }

    if (gameState === 'start') return;

    const sz = Math.max(7, Math.floor(CUSHION * 0.56));
    ctx.font         = sz + 'px "Press Start 2P", monospace';
    ctx.textBaseline = 'top';
    ctx.fillStyle    = 'rgba(255,255,255,0.6)';

    ctx.textAlign = 'left';
    ctx.fillText(fmtTime(elapsed), TABLE_X + 6, TABLE_Y + 5);

    if (gameState === 'playing' && balls.length > 0) {
      const rem = balls.length - pottedBalls.length;
      ctx.textAlign = 'right';
      ctx.fillText(rem + ' LEFT', TABLE_X + TABLE_W - 6, TABLE_Y + 5);

      // Combo counter
      if (comboCount > 1) {
        const timeSincePot = performance.now() - lastPotTime;
        const progress = Math.max(0, 1 - timeSincePot / COMBO_WINDOW);
        const cx = TABLE_X + TABLE_W / 2;
        const cy = TABLE_Y + sz * 1.6;
        const arcR = sz * 1.1;

        // Background arc track
        ctx.beginPath();
        ctx.arc(cx, cy, arcR, -Math.PI / 2, Math.PI * 1.5);
        ctx.strokeStyle = 'rgba(255,215,0,0.18)';
        ctx.lineWidth = 2.5;
        ctx.stroke();

        // Progress arc
        ctx.beginPath();
        ctx.arc(cx, cy, arcR, -Math.PI / 2, -Math.PI / 2 + Math.PI * 2 * progress);
        ctx.strokeStyle = '#ffd700';
        ctx.lineWidth = 2.5;
        ctx.stroke();

        ctx.fillStyle = '#ffd700';
        ctx.font = 'bold ' + sz + 'px "Press Start 2P", monospace';
        ctx.textAlign = 'center';
        ctx.textBaseline = 'middle';
        ctx.fillText('\xD7' + comboCount, cx, cy);
        ctx.textBaseline = 'top';
      }
    }

    drawBonusTierHint(sz, ts);

    if (msgText && ts < msgExpiry) {
      const a = Math.min(1, (msgExpiry - ts) / 320);
      ctx.globalAlpha  = a;
      ctx.fillStyle    = '#ffeb3b';
      ctx.shadowColor  = '#ffeb3b';
      ctx.shadowBlur   = 14;
      ctx.font         = 'bold ' + Math.max(11, sz * 1.35) + 'px "Press Start 2P", monospace';
      ctx.textAlign    = 'center';
      ctx.textBaseline = 'middle';
      ctx.fillText(msgText, W / 2, TABLE_Y + TABLE_H * 0.1);
      ctx.shadowBlur   = 0;
      ctx.globalAlpha  = 1;
    }
  }

  function drawBonusTierHint(sz) {
    if (gameState !== 'playing') return;
    const [t1, t2, t3] = settings.timeLimits;
    const [m1, m2, m3] = settings.multipliers;
    const tiers = [
      { t: t1, m: m1, color: '#ffd700' },
      { t: t2, m: m2, color: '#aaaaaa' },
      { t: t3, m: m3, color: '#cd7f32' },
    ];
    const hsz = Math.max(5, Math.floor(sz * 0.68));
    ctx.font         = hsz + 'px "Press Start 2P", monospace';
    ctx.textBaseline = 'bottom';
    let x = TABLE_X + 6;
    const y = TABLE_Y + TABLE_H - 4;
    for (const tier of tiers) {
      const active = elapsed < tier.t;
      ctx.globalAlpha = active ? 1 : 0.32;
      ctx.fillStyle   = tier.color;
      ctx.textAlign   = 'left';
      const label = '\xD7' + tier.m + '<' + tier.t + 's  ';
      ctx.fillText(label, x, y);
      x += ctx.measureText(label).width;
    }
    ctx.globalAlpha = 1;
  }

  // ── Overlay screens ────────────────────────────────────────────────────────
  function drawOverlay(ts) {
    ctx.fillStyle = 'rgba(0,0,0,0.74)';
    ctx.fillRect(TABLE_X, TABLE_Y, TABLE_W, TABLE_H);

    const cx = TABLE_X + TABLE_W / 2;
    const cy = TABLE_Y + TABLE_H / 2;
    const px = Math.max(9, Math.floor(CUSHION * 0.72));

    ctx.textAlign    = 'center';
    ctx.textBaseline = 'middle';

    if (gameState === 'start') {
      ctx.shadowColor = '#00ff41';
      ctx.shadowBlur  = 18;
      ctx.fillStyle   = '#00ff41';
      ctx.font        = px * 1.4 + 'px "Press Start 2P", monospace';
      ctx.fillText('POOL SNAKE', cx, cy - px * 3.5);
      ctx.shadowBlur  = 0;

      ctx.fillStyle = 'rgba(255,255,255,0.58)';
      ctx.font      = px * 0.63 + 'px "Press Start 2P", monospace';
      ctx.fillText('GUIDE SNAKE → BREAK THE RACK', cx, cy - px * 1.3);
      ctx.fillText('POT ALL BALLS FOR TIME BONUS', cx, cy + px * 0.15);

      if (Math.sin(ts / 520) > 0) {
        ctx.fillStyle = '#00ff41';
        ctx.font      = px * 0.78 + 'px "Press Start 2P", monospace';
        ctx.fillText('PRESS SPACE TO START', cx, cy + px * 2.3);
      }

    } else if (gameState === 'round_clear') {
      ctx.shadowColor = '#00ff41';
      ctx.shadowBlur  = 20;
      ctx.fillStyle   = '#00ff41';
      ctx.font        = px * 1.05 + 'px "Press Start 2P", monospace';
      ctx.fillText('ROUND ' + roundNumber + ' CLEAR!', cx, cy - px * 3.8);
      ctx.shadowBlur  = 0;

      ctx.fillStyle = 'rgba(255,255,255,0.72)';
      ctx.font      = px * 0.63 + 'px "Press Start 2P", monospace';
      ctx.fillText('TIME:   ' + fmtTime(elapsed),                         cx, cy - px * 2.1);
      ctx.fillText('BALLS:  ' + score + '  \xD7' + lastRoundMultiplier,  cx, cy - px * 0.9);

      ctx.shadowColor = '#ffd700';
      ctx.shadowBlur  = 10;
      ctx.fillStyle   = '#ffd700';
      ctx.font        = px * 0.78 + 'px "Press Start 2P", monospace';
      ctx.fillText('ROUND:  +' + lastRoundScore + ' pts',                 cx, cy + px * 0.6);
      ctx.fillText('TOTAL:  ' + totalScore + ' pts',                      cx, cy + px * 1.9);
      ctx.shadowBlur  = 0;

      if (Math.sin(ts / 520) > 0) {
        ctx.fillStyle = 'rgba(255,255,255,0.52)';
        ctx.font      = px * 0.63 + 'px "Press Start 2P", monospace';
        ctx.fillText('SPACE TO CONTINUE', cx, cy + px * 3.5);
      }

    } else if (gameState === 'gameover') {
      ctx.shadowColor = '#cc2200';
      ctx.shadowBlur  = 16;
      ctx.fillStyle   = '#cc2200';
      ctx.font        = px * 1.3 + 'px "Press Start 2P", monospace';
      ctx.fillText('GAME OVER', cx, cy - px * 3.4);
      ctx.shadowBlur  = 0;

      ctx.fillStyle = 'rgba(255,255,255,0.6)';
      ctx.font      = px * 0.6 + 'px "Press Start 2P", monospace';
      ctx.fillText('ROUNDS CLEARED: ' + completedRounds, cx, cy - px * 1.7);
      ctx.fillText('ROUND ' + roundNumber + ':  ' + score + ' balls \xD71', cx, cy - px * 0.55);

      ctx.shadowColor = '#ffd700';
      ctx.shadowBlur  = 12;
      ctx.fillStyle   = '#ffd700';
      ctx.font        = px * 1.0 + 'px "Press Start 2P", monospace';
      ctx.fillText('TOTAL:  ' + totalScore, cx, cy + px * 0.9);
      ctx.shadowBlur  = 0;

      if (totalScore >= bestScore && totalScore > 0) {
        ctx.fillStyle = '#ff80ab';
        ctx.font      = px * 0.58 + 'px "Press Start 2P", monospace';
        ctx.fillText('★ NEW BEST ★', cx, cy + px * 2.3);
      }

      if (Math.sin(ts / 520) > 0) {
        ctx.fillStyle = '#00ff41';
        ctx.font      = px * 0.68 + 'px "Press Start 2P", monospace';
        ctx.fillText('PRESS SPACE TO RETRY', cx, cy + px * 3.6);
      }
    }
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Utilities
  // ─────────────────────────────────────────────────────────────────────────────
  function rrFill(x, y, w, h, r) {
    r = Math.min(r, w / 2, h / 2);
    ctx.beginPath();
    ctx.moveTo(x + r, y);
    ctx.lineTo(x + w - r, y);
    ctx.arcTo(x + w, y,     x + w, y + r,     r);
    ctx.lineTo(x + w, y + h - r);
    ctx.arcTo(x + w, y + h, x + w - r, y + h, r);
    ctx.lineTo(x + r, y + h);
    ctx.arcTo(x,     y + h, x,     y + h - r, r);
    ctx.lineTo(x, y + r);
    ctx.arcTo(x,     y,     x + r, y,         r);
    ctx.closePath();
    ctx.fill();
  }

  function fmtTime(secs) {
    const s = Math.floor(secs || 0);
    const d = Math.floor(((secs || 0) - s) * 10);
    if (s < 60) return String(s).padStart(2, '0') + '.' + d + 's';
    return Math.floor(s / 60) + 'm' + String(s % 60).padStart(2, '0') + '.' + d + 's';
  }

  function showMsg(text) {
    msgText   = text;
    msgExpiry = performance.now() + 1050;
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Game loop
  // ─────────────────────────────────────────────────────────────────────────────
  function gameLoop(ts) {
    requestAnimationFrame(gameLoop);
    const dt = Math.min(50, ts - (lastFrameTime || ts));
    lastFrameTime = ts;

    if (gameState === 'playing') {
      physicsStep(dt);
      if (ts - lastStepTime >= SPEEDS[settings.speed]) {
        lastStepTime = ts;
        snakeStep();
      }
    }

    draw(ts);
    updateNavScore();
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // UI wiring
  // ─────────────────────────────────────────────────────────────────────────────
  function updateScoreUI() {
    const sv = document.getElementById('score-val');
    const hv = document.getElementById('hi-val');
    const ov = document.getElementById('on-val');
    if (sv) sv.textContent = totalScore || 0;
    if (hv) hv.textContent = bestScore  || 0;
    if (ov) {
      if (gameState === 'playing' && balls) {
        ov.textContent = balls.length - pottedBalls.length;
      } else {
        ov.textContent = '-';
      }
    }
  }

  function updateNavScore() {
    const ns = document.getElementById('nav-score-val');
    if (ns) ns.textContent = totalScore || 0;
  }

  function setupSettingsUI() {
    document.querySelectorAll('[data-setting="ballCount"]').forEach(btn => {
      btn.addEventListener('click', () => {
        if (gameState === 'playing') return;
        settings.ballCount = parseInt(btn.dataset.value, 10);
        document.querySelectorAll('[data-setting="ballCount"]').forEach(b =>
          b.classList.toggle('setting-btn--active', b === btn));
      });
    });

    document.querySelectorAll('[data-setting="speed"]').forEach(btn => {
      btn.addEventListener('click', () => {
        settings.speed = btn.dataset.value;
        document.querySelectorAll('[data-setting="speed"]').forEach(b =>
          b.classList.toggle('setting-btn--active', b === btn));
      });
    });

    document.querySelectorAll('[data-setting="power"]').forEach(btn => {
      btn.addEventListener('click', () => {
        settings.power = btn.dataset.value;
        document.querySelectorAll('[data-setting="power"]').forEach(b =>
          b.classList.toggle('setting-btn--active', b === btn));
      });
    });

    document.querySelectorAll('[data-timelimit]').forEach(input => {
      const idx = parseInt(input.dataset.timelimit, 10);
      input.value = settings.timeLimits[idx];
      input.addEventListener('input', () => {
        const v = parseInt(input.value, 10);
        if (v >= 1) settings.timeLimits[idx] = v;
      });
    });

    document.querySelectorAll('[data-multiplier]').forEach(input => {
      const idx = parseInt(input.dataset.multiplier, 10);
      input.value = settings.multipliers[idx];
      input.addEventListener('input', () => {
        const v = parseInt(input.value, 10);
        if (v >= 1) settings.multipliers[idx] = v;
      });
    });

    const actionBtn    = document.getElementById('action-btn');
    const nextRoundBtn = document.getElementById('next-round-btn');
    const restartBtn   = document.getElementById('restart-btn');

    if (actionBtn) {
      actionBtn.addEventListener('click', () => {
        if (gameState !== 'playing') {
          initGame();
          setButtonVisibility('playing');
        }
      });
    }
    if (nextRoundBtn) {
      nextRoundBtn.addEventListener('click', () => {
        if (gameState === 'round_clear') startNextRound();
      });
    }
    if (restartBtn) {
      restartBtn.addEventListener('click', () => {
        initGame();
        setButtonVisibility('playing');
      });
    }
  }

  function setupInput() {
    const actionBtn  = document.getElementById('action-btn');
    const restartBtn = document.getElementById('restart-btn');

    function startOrQueue(dx, dy) {
      if (gameState === 'round_clear') {
        startNextRound();
      } else if (gameState !== 'playing') {
        initGame();
        if (actionBtn)  actionBtn.hidden  = true;
        if (restartBtn) restartBtn.hidden = false;
      } else if (dx !== undefined) {
        queueDir(dx, dy);
      }
    }

    document.addEventListener('keydown', e => {
      if (document.activeElement && document.activeElement.tagName === 'INPUT') return;

      const map = {
        ArrowUp: [0, -1], ArrowDown: [0, 1], ArrowLeft: [-1, 0], ArrowRight: [1, 0],
        w: [0, -1], s: [0, 1], a: [-1, 0], d: [1, 0],
        W: [0, -1], S: [0, 1], A: [-1, 0], D: [1, 0],
      };
      const dd = map[e.key];
      if (dd) {
        e.preventDefault();
        if (gameState === 'playing') queueDir(dd[0], dd[1]);
      }
      if (e.key === ' ' || e.key === 'Enter') {
        e.preventDefault();
        startOrQueue();
      }
    });

    let tx0 = 0, ty0 = 0;
    canvas.addEventListener('touchstart', e => {
      tx0 = e.touches[0].clientX;
      ty0 = e.touches[0].clientY;
    }, { passive: true });
    canvas.addEventListener('touchend', e => {
      if (!e.changedTouches.length) return;
      const ddx = e.changedTouches[0].clientX - tx0;
      const ddy = e.changedTouches[0].clientY - ty0;
      const ad  = Math.abs(ddx), ay = Math.abs(ddy);
      if (Math.max(ad, ay) < 18) {
        startOrQueue();
      } else if (ad > ay) {
        startOrQueue(ddx > 0 ? 1 : -1, 0);
      } else {
        startOrQueue(0, ddy > 0 ? 1 : -1);
      }
    }, { passive: true });

    const dirMap = { up: [0, -1], down: [0, 1], left: [-1, 0], right: [1, 0] };
    document.querySelectorAll('.dpad-btn').forEach(btn => {
      const handler = () => {
        const dd = dirMap[btn.dataset.dir];
        if (dd) startOrQueue(dd[0], dd[1]);
      };
      btn.addEventListener('mousedown', handler);
      btn.addEventListener('touchstart', handler, { passive: true });
    });
  }

  // ─────────────────────────────────────────────────────────────────────────────
  // Boot
  // ─────────────────────────────────────────────────────────────────────────────
  function boot() {
    canvas    = document.getElementById('game-canvas');
    ctx       = canvas.getContext('2d');
    bestScore = parseInt(localStorage.getItem('poolsnake_best') || '0', 10);

    calcLayout();
    window.addEventListener('resize', () => {
      calcLayout();
      if (gameState !== 'playing') draw(0);
    });

    balls            = [];
    pottedBalls      = [];
    snake            = [];
    score            = 0;
    totalScore       = 0;
    elapsed          = 0;
    completedRounds  = 0;
    roundNumber      = 1;
    lastRoundScore   = 0;
    lastRoundMultiplier = 0;
    msgText          = '';
    msgExpiry        = 0;

    setupInput();
    setupSettingsUI();
    updateScoreUI();

    requestAnimationFrame(gameLoop);
  }

  document.addEventListener('DOMContentLoaded', boot);
}());
