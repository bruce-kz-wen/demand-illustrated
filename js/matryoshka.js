/*
 * Tab "Matryoshka basis": a function of (delta, p) typed by the reader, its L2
 * approximation by the first N functions of the dictionary, and the error.
 *
 * The numbers come from js/core.js. This file draws them:
 *   part 1  the function            (expression, examples, weights, degree)
 *   part 2  the sum of N pieces     (dolls, three heat maps, cross-section, error curve)
 *   part 3  the pieces themselves   (chain of curves, grid of products, one piece, table)
 *   part 4  against the full grid   (same curves with every product: errors, and sizes as inputs are added)
 */
(function () {
  'use strict';
  const { el, svg, tex, fmt } = Viz;
  const $ = (id) => document.getElementById(id);
  const clamp = (v, lo, hi) => Math.min(hi, Math.max(lo, v));

  const PRESETS = [
    { name: 'Logit', expr: '1 / (1 + exp(-(6*delta - 5*p - 1)))' },
    { name: 'Mixed logit', expr: '0.5*logistic(8*delta - 2*p - 3) + 0.5*logistic(3*delta - 12*p + 2)' },
    { name: 'Probit', expr: 'normcdf(4*delta - 3*p - 0.5)' },
    { name: 'Kinked', expr: 'max(0, 0.2 + delta - 1.2*p)' },
    { name: 'Cliff', expr: 'step(delta - p)' },
    { name: 'Waves', expr: '0.5 + 0.4*sin(7*delta)*cos(5*p)' },
    { name: 'Bump', expr: 'exp(-40*((delta - 0.6)^2 + (p - 0.3)^2))' },
    { name: 'Polynomial', expr: 'delta^2 * (1 - p)' },
  ];
  const WEIGHTS = [
    { a: [0.5, 1], label: '(½, 1)' },
    { a: [0.5, 2], label: '(½, 2)' },
    { a: [1, 1], label: '(1, 1)' },
  ];
  const DEGREES = [{ kappa: 1, label: 'linear' }, { kappa: 2, label: 'quadratic' }, { kappa: 3, label: 'cubic' }];
  const SHAPES = ['constant', 'line', 'parabola', 'cubic'];
  const LEVEL_LABELS = [['knot at ½', '½'], ['¼ and ¾', '¼ ¾'], ['eighths', '⅛…'],
                        ['sixteenths', '1/16…'], ['thirty-seconds', '1/32…']];
  const MAX_PIECES = 170;   // the dictionary is cut at the last whole level with at most this many pieces
  const G = 160;            // heat maps are G x G, at cell centers
  const S = 200;            // a cross-section has S + 1 points
  const T = 32;             // thumbnails are T x T
  const MAX_PRODUCTS = 50;  // part 4 goes from 1 to this many products
  const LEVELS = [1, 2, 3, 4];

  // Part 4, many inputs: the share of product 1 among J products and an outside good in the
  // probit design of the note's simulations (dgp_errors.py, kind "probit"). A consumer gets
  // delta_j + alpha_i p_j + sigma e_ij from product j and sigma e_i0 from the outside good,
  // with independent standard normal e and sigma^2 = pi^2 / 6, and alpha_i ~ N(-1, 0.15^2),
  // here by the three-point Gauss-Hermite rule: [share of consumers, alpha]. delta and p are
  // rescaled to [0, 1] from [0.5, 3.5] and [0.5, 3.7], about the ranges of the simulated data.
  const PROBIT_CONSUMERS = [[2 / 3, -1], [1 / 6, -1 - 0.15 * Math.sqrt(3)], [1 / 6, -1 + 0.15 * Math.sqrt(3)]]
    .map(([share, alpha]) => ({ share, utility: (d, p) => (0.5 + 3 * d) + alpha * (0.5 + 3.2 * p) }));

  const state = {
    kappa: 3,
    weights: 0,
    n: 9,                               // pieces in the sum
    cutAxis: 'p',                       // the coordinate held fixed in the cross-section
    cut: { delta: 0.5, p: 0.5 },
    magnify: true,                      // rescale the error colors to the current error
    focus: null,                        // piece under the pointer, or null for the newest
    playing: false,
    products: 50,                       // part 4: number of products J, for 2J inputs
    level: 1,                           // part 4: resolution level m of the full grid that is singled out
  };

  // The dictionary, the current function and its projection.
  let dict, projector, fn, fit;
  let coef;                             // coefficients of the current sum, as a (K_delta + 1) x (K_p + 1) matrix
  let valueLo = 0, valueHi = 1;         // color range of the target
  let section = null;                   // the cross-section last drawn
  const gridX = Float64Array.from({ length: G }, (_, i) => (i + 0.5) / G);
  const sliceX = Float64Array.from({ length: S + 1 }, (_, i) => i / S);
  const thumbX = Float64Array.from({ length: T }, (_, i) => (i + 0.5) / T);
  let psiG, psiS, psiT;                 // psi[m][i]: the chain on the three grids
  let peakG, peakT;                     // max |psi_m| on the grid
  const targetG = new Float64Array(G * G), approxG = new Float64Array(G * G);   // [i * G + j] at (delta_i, p_j)

  // Elements filled in by start().
  let input, statusBox, slider, playButton, sliceChart, errorChart, compareChart, systemChart, scalingChart, timer = null;
  let sizes = null;                     // part 4: { ours[J], grid[J] } at state.level, as BigInt, J = 1..MAX_PRODUCTS
  let system = null;                    // part 4: errors of the J-product demand, and a cache of them by J
  const systemCache = new Map();
  let dolls = [], chainFigures = [], termRows = [], shownN = 0;
  const maps = {};
  const sprite = document.createElement('canvas');
  const detailImage = document.createElement('canvas');

  // ---------------------------------------------------------------------------
  // Words and formulas
  // ---------------------------------------------------------------------------

  const subscript = (n) => String(n).split('').map((ch) => String.fromCharCode(0x2080 + Number(ch))).join('');
  const psiName = (m, variable) => `ψ${subscript(m)}(${variable})`;
  const plural = (n, word) => `${n} ${word}${n === 1 ? '' : 's'}`;
  const weightText = (a) => (a === 0.5 ? '½' : String(a));

  function describeCurve(m) {
    return m <= state.kappa ? SHAPES[m] : 'knot at ' + Viz.fraction(dict.chain.info[m].knot);
  }

  const POLYNOMIAL_TEX = [
    () => '1',
    (v) => `2${v}-1`,
    (v) => `6${v}^2-6${v}+1`,
    (v) => `20${v}^3-30${v}^2+12${v}-1`,
  ];

  /** psi_k(delta, p) written out, as in Table 2 of the note; spline factors keep their name. */
  function pieceTeX(k) {
    const variables = ['\\delta', 'p'], polynomials = [], splines = [];
    let norm = 1;
    k.forEach((m, c) => {
      if (m === 0) return;
      if (m <= state.kappa) { norm *= 2 * m + 1; polynomials.push(`(${POLYNOMIAL_TEX[m](variables[c])})`); }
      else splines.push(`\\psi_{${m}}(${variables[c]})`);
    });
    const root = Math.sqrt(norm);
    const lead = norm === 1 ? '' : Number.isInteger(root) ? String(root) : `\\sqrt{${norm}}`;
    const parts = [];
    if (lead || polynomials.length) parts.push(lead + (lead && polynomials.length ? '\\,' : '') + polynomials.join(''));
    if (splines.length) parts.push(splines.join('\\,'));
    return parts.length ? parts.join('\\,') : '1';
  }

  // ---------------------------------------------------------------------------
  // Numbers
  // ---------------------------------------------------------------------------

  function buildDictionary() {
    dict = Matryoshka.dictionary2D({ kappa: state.kappa, a: WEIGHTS[state.weights].a, nCap: MAX_PIECES });
    projector = Matryoshka.projector(dict);
    psiG = dict.chain.evaluate(gridX);
    psiS = dict.chain.evaluate(sliceX);
    psiT = dict.chain.evaluate(thumbX);
    const peaks = (psi) => psi.map((row) => row.reduce((mx, v) => Math.max(mx, Math.abs(v)), 0));
    peakG = peaks(psiG);
    peakT = peaks(psiT);
    coef = new Float64Array((dict.K[0] + 1) * (dict.K[1] + 1));
    state.n = clamp(state.n, 1, dict.N);
    state.focus = null;
    slider.max = dict.N;
  }

  /** Project f, and tabulate it on the heat map grid. Returns { fit, target } or { error }. */
  function projectFunction(f) {
    const notFinite = (at) => `At δ = ${at.delta.toFixed(2)}, p = ${at.p.toFixed(2)} this is ${Number.isNaN(at.value) ? 'not a number' : 'infinite'}. ` +
      'The function has to be finite on the whole square.';
    const result = projector.project(f);
    if (result.error) return { error: notFinite(result.error) };
    const target = new Float64Array(G * G);
    for (let i = 0; i < G; i++) {
      for (let j = 0; j < G; j++) {
        const value = f(gridX[i], gridX[j]);
        if (!Number.isFinite(value)) return { error: notFinite({ delta: gridX[i], p: gridX[j], value }) };
        target[i * G + j] = value;
      }
    }
    return { fit: result, target };
  }

  /** The sum of the first n pieces on the heat map grid. */
  function approximate(n) {
    const K1 = dict.K[0] + 1, K2 = dict.K[1] + 1;
    coef.fill(0);
    for (let i = 0; i < n; i++) coef[dict.pieces[i].k[0] * K2 + dict.pieces[i].k[1]] = fit.theta[i];
    const partial = new Float64Array(K2);
    for (let i = 0; i < G; i++) {
      for (let k2 = 0; k2 < K2; k2++) {
        let s = 0;
        for (let k1 = 0; k1 < K1; k1++) s += psiG[k1][i] * coef[k1 * K2 + k2];
        partial[k2] = s;
      }
      for (let j = 0; j < G; j++) {
        let s = 0;
        for (let k2 = 0; k2 < K2; k2++) s += partial[k2] * psiG[k2][j];
        approxG[i * G + j] = s;
      }
    }
  }

  /** Target and sum along the cross-section, from the coefficients set by approximate(). */
  function crossSection() {
    const alongDelta = state.cutAxis === 'p';
    const at = alongDelta ? state.cut.p : state.cut.delta;
    const K1 = dict.K[0] + 1, K2 = dict.K[1] + 1;
    const fixed = dict.chain.evaluate([at]);
    const weights = new Float64Array(alongDelta ? K1 : K2);
    for (let k1 = 0; k1 < K1; k1++) {
      for (let k2 = 0; k2 < K2; k2++) {
        const c = coef[k1 * K2 + k2];
        if (c === 0) continue;
        if (alongDelta) weights[k1] += c * fixed[k2][0]; else weights[k2] += c * fixed[k1][0];
      }
    }
    const target = [], sum = [];
    for (let s = 0; s <= S; s++) {
      const x = sliceX[s];
      let v = 0;
      for (let m = 0; m < weights.length; m++) v += weights[m] * psiS[m][s];
      target.push([x, alongDelta ? fn(x, at) : fn(at, x)]);
      sum.push([x, v]);
    }
    return { alongDelta, at, target, sum };
  }

  // ---------------------------------------------------------------------------
  // Part 1: the function
  // ---------------------------------------------------------------------------

  function showStatus(message, isError) {
    statusBox.textContent = '';
    statusBox.classList.toggle('error', !!isError);
    input.setAttribute('aria-invalid', String(!!isError));
    if (isError) {
      el('span', { class: 'bang', text: '!', 'aria-hidden': 'true' }, statusBox);
      el('span', { text: message + (fit ? ' The figures still show the last function that worked.' : '') }, statusBox);
    } else {
      el('span', { class: 'label', text: 'Read as' }, statusBox);
      tex(el('span', {}, statusBox), `\\displaystyle f(\\delta,\\,p) = ${message}`);
    }
  }

  function applyExpression() {
    for (const chip of $('mk-presets').querySelectorAll('.chip')) {
      chip.setAttribute('aria-pressed', String(chip.dataset.expr === input.value.trim()));
    }
    let parsed;
    try {
      parsed = MathExpr.parse(input.value);
    } catch (error) {
      if (!(error instanceof MathExpr.ExprError)) throw error;
      showStatus(error.message, true);
      return;
    }
    const result = projectFunction(parsed.fn);
    if (result.error) { showStatus(result.error, true); return; }
    fn = parsed.fn;
    fit = result.fit;
    targetG.set(result.target);
    showStatus(parsed.tex, false);
    drawFit();
  }

  /** Everything that depends on the weights and the degree but not on the function. */
  function build() {
    buildDictionary();
    buildDolls();
    buildChain();
    buildSprites();
    buildTerms();
    buildSizes();
    buildSystem();
    drawMany();
  }

  /** After a change of weights or degree: new dictionary, same function. */
  function rebuild() {
    pause();
    build();
    const result = projectFunction(fn);
    if (result.error) {                 // not finite on the new grid: start over from the first example
      input.value = PRESETS[0].expr;
      applyExpression();
      return;
    }
    fit = result.fit;
    targetG.set(result.target);
    drawFit();
  }

  function segmented(host, labels, current, onPick) {
    const buttons = labels.map((label, i) => {
      const button = el('button', { type: 'button', text: label, 'aria-pressed': String(i === current) }, host);
      button.addEventListener('click', () => {
        buttons.forEach((b, j) => b.setAttribute('aria-pressed', String(j === i)));
        onPick(i);
      });
      return button;
    });
  }

  // ---------------------------------------------------------------------------
  // Part 2: N, the dolls, the numbers
  // ---------------------------------------------------------------------------

  const ICON = {
    play: 'M2 1l9 5-9 5z',
    pause: 'M2 1h3v10H2zM7 1h3v10H7z',
  };
  function drawPlayButton() {
    playButton.textContent = '';
    const icon = svg('svg', { viewBox: '0 0 12 12', 'aria-hidden': 'true' }, playButton);
    svg('path', { d: state.playing ? ICON.pause : ICON.play }, icon);
    playButton.appendChild(document.createTextNode(state.playing ? 'Pause' : state.n >= dict.N ? 'Replay' : 'Play'));
  }

  function pause() {
    if (!state.playing) return;
    state.playing = false;
    clearTimeout(timer);
    drawPlayButton();
  }

  function play() {
    state.playing = true;
    if (state.n >= dict.N) setN(1); else setN(state.n + 1);
    const step = () => {
      if (!state.playing) return;
      if (state.n >= dict.N) { pause(); return; }
      setN(state.n + 1);
      timer = setTimeout(step, pace(state.n));
    };
    timer = setTimeout(step, pace(state.n));
    drawPlayButton();
  }
  // Slow while each piece changes the picture, faster once the changes are fine.
  const pace = (n) => (n < 10 ? 320 : n < 30 ? 170 : n < 80 ? 85 : 45);

  function setN(n) {
    n = clamp(Math.round(n), 1, dict.N);
    if (n === state.n) return;
    state.n = n;
    drawN();
  }

  // A doll in a 40 x 56 box: body, head, and the seam where it opens.
  const DOLL = 'M20 2C27 2 31.5 7 31.5 13.5C31.5 17 30.5 19.5 29.5 21.5C34.5 25 38 31 38 38C38 47 34 54 27 54' +
               'L13 54C6 54 2 47 2 38C2 31 5.5 25 10.5 21.5C9.5 19.5 8.5 17 8.5 13.5C8.5 7 13 2 20 2Z';
  const SEAM = 'M2.6 34.5Q20 39.5 37.4 34.5';

  function buildDolls() {
    const host = $('mk-dolls'), last = dict.levels.length - 1;
    host.textContent = '';
    dolls = dict.levels.map((count, m) => {
      const width = Math.round((30 + 34 * (last ? m / last : 1)) * 40 / 56);
      const button = el('button', {
        class: 'doll', type: 'button',
        title: `Level ${m}: the ${plural(count, 'piece')} of cost ${m} or less`,
        'aria-label': `Level ${m}, ${plural(count, 'piece')}`,
      }, host);
      const figure = svg('svg', { viewBox: '0 0 40 56', 'aria-hidden': 'true' }, button);
      figure.style.width = width + 'px';             // shrinks with the row on a narrow screen
      const clipId = `mk-doll-clip-${m}`;
      const level = svg('rect', { x: -2, width: 44, y: 56, height: 0 }, svg('clipPath', { id: clipId }, figure));
      svg('path', { class: 'shell', d: DOLL }, figure);
      svg('circle', { class: 'shell', cx: 20, cy: 13, r: 6 }, figure);
      svg('path', { class: 'shell', d: SEAM, fill: 'none' }, figure);
      const filled = svg('g', { 'clip-path': `url(#${clipId})` }, figure);
      svg('path', { class: 'fill', d: DOLL }, filled);
      svg('circle', { class: 'face', cx: 20, cy: 13, r: 6 }, filled);
      svg('path', { class: 'seam', d: SEAM }, filled);
      el('span', { class: 'count', text: count }, button);
      button.addEventListener('click', () => { pause(); setN(count); });
      return { button, level, count, before: m ? dict.levels[m - 1] : 0 };
    });
  }

  function drawDolls() {
    for (const doll of dolls) {
      const share = clamp((state.n - doll.before) / (doll.count - doll.before), 0, 1);
      doll.level.setAttribute('y', 56 * (1 - share));
      doll.level.setAttribute('height', 56 * share + 2);
      doll.button.classList.toggle('done', share === 1);
      doll.button.classList.toggle('partial', share > 0 && share < 1);
    }
  }

  /** An error as text; "0" once it is rounding noise next to the size of f. */
  const isExact = (error) => error <= 1e-12 * Math.max(fit.norm, 1e-300);
  const errorText = (error) => (isExact(error) ? '0' : fmt(error));

  function stat(id, value, note) {
    const node = $(id);
    node.textContent = value;
    if (note) el('small', { text: note }, node);
  }

  function drawStats() {
    const n = state.n, exact = isExact(fit.rms[n]);
    stat('mk-stat-n', String(n), `of ${dict.N}`);
    stat('mk-stat-level', String(dict.completeLevel(n) + 1), `of ${dict.levels.length}`);
    stat('mk-stat-rms', errorText(fit.rms[n]), exact ? 'exact' : '');
    stat('mk-stat-sup', errorText(fit.sup[n]), exact ? 'exact' : '');
    $('mk-n-out').textContent = `N = ${n}`;
    $('mk-map-sum-title').textContent = n === 1 ? 'The first piece alone' : `Sum of the first ${n} pieces`;
    slider.value = n;
  }

  // ---------------------------------------------------------------------------
  // Part 2: heat maps
  // ---------------------------------------------------------------------------

  const PAD = { left: 46, right: 6, top: 6, bottom: 46 };   // around the square plot of a map

  function paintTarget() {
    valueLo = Infinity; valueHi = -Infinity;
    for (let i = 0; i < targetG.length; i++) {
      if (targetG[i] < valueLo) valueLo = targetG[i];
      if (targetG[i] > valueHi) valueHi = targetG[i];
    }
    if (!(valueHi - valueLo > 1e-12 * Math.max(Math.abs(valueLo), Math.abs(valueHi), 1e-300))) { valueLo -= 0.5; valueHi += 0.5; }
    const ramp = Viz.theme().sequential;
    Viz.paint(maps.target.image, G, G, ramp, (col, row) => (targetG[col * G + row] - valueLo) / (valueHi - valueLo));
    drawScale(maps.target.scale, ramp, fmt(valueLo, 3), fmt(valueHi, 3));
    drawScale(maps.approx.scale, ramp, fmt(valueLo, 3), fmt(valueHi, 3));
  }

  function paintSum() {
    const theme = Viz.theme();
    Viz.paint(maps.approx.image, G, G, theme.sequential, (col, row) => (approxG[col * G + row] - valueLo) / (valueHi - valueLo));
    let largest = 0;
    for (let i = 0; i < targetG.length; i++) largest = Math.max(largest, Math.abs(targetG[i] - approxG[i]));
    // Never magnify rounding noise: the scale stops shrinking nine digits below the size of f.
    const floor = 1e-9 * Math.max(Math.abs(valueLo), Math.abs(valueHi));
    const scale = Math.max(state.magnify ? largest : fit.sup[1], floor);
    Viz.paint(maps.error.image, G, G, theme.diverging, (col, row) => 0.5 + 0.5 * (targetG[col * G + row] - approxG[col * G + row]) / scale);
    drawScale(maps.error.scale, theme.diverging, fmt(-scale), fmt(scale));
  }

  function drawScale(node, ramp, low, high) {
    node.textContent = '';
    el('span', { text: low }, node);
    el('span', { class: 'bar' }, node).style.background = ramp.css;
    el('span', { text: high }, node);
  }

  function drawMap(map) {
    const { ctx, w } = Viz.fitCanvas(map.canvas);
    if (!w) return;
    const theme = Viz.theme(), size = w - PAD.left - PAD.right, x0 = PAD.left, y0 = PAD.top;
    ctx.imageSmoothingEnabled = true;
    ctx.imageSmoothingQuality = 'high';
    ctx.drawImage(map.image, x0, y0, size, size);

    ctx.fillStyle = theme.muted;
    ctx.font = '11px system-ui, sans-serif';
    ctx.textBaseline = 'top';
    for (const t of [0, 0.5, 1]) {
      ctx.textAlign = t === 0 ? 'left' : t === 1 ? 'right' : 'center';
      ctx.fillText(String(t), x0 + t * size, y0 + size + 6);
    }
    ctx.textAlign = 'right';
    for (const t of [0, 0.5, 1]) {
      ctx.textBaseline = t === 0 ? 'bottom' : t === 1 ? 'top' : 'middle';
      ctx.fillText(String(t), x0 - 6, y0 + (1 - t) * size);
    }
    ctx.fillStyle = theme.ink2;
    ctx.font = 'italic 15px KaTeX_Math, "Times New Roman", serif';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'alphabetic';
    ctx.fillText('δ', x0 + size / 2, y0 + size + 34);
    ctx.fillText('p', 9, y0 + size / 2 + 4);

    // The cross-section: a hairline in ink over a wider line in the surface color.
    ctx.save();
    ctx.beginPath();
    ctx.rect(x0, y0, size, size);
    ctx.clip();
    const horizontal = state.cutAxis === 'p';
    const at = Math.round(horizontal ? y0 + (1 - state.cut.p) * size : x0 + state.cut.delta * size) + 0.5;
    for (const [color, width, alpha] of [[theme.surface, 3, 0.75], [theme.ink, 1, 1]]) {
      ctx.strokeStyle = color; ctx.lineWidth = width; ctx.globalAlpha = alpha;
      ctx.beginPath();
      if (horizontal) { ctx.moveTo(x0, at); ctx.lineTo(x0 + size, at); } else { ctx.moveTo(at, y0); ctx.lineTo(at, y0 + size); }
      ctx.stroke();
    }
    ctx.restore();
  }
  const drawMaps = () => Object.values(maps).forEach(drawMap);

  function mapPoint(map, event) {
    const box = map.canvas.getBoundingClientRect(), size = box.width - PAD.left - PAD.right;
    const delta = (event.clientX - box.left - PAD.left) / size, p = 1 - (event.clientY - box.top - PAD.top) / size;
    return delta >= 0 && delta <= 1 && p >= 0 && p <= 1 ? { delta, p } : null;
  }

  function setCut(point) {
    state.cut = { delta: Math.round(point.delta * 200) / 200, p: Math.round(point.p * 200) / 200 };
    drawCut();
  }

  function watchMap(map) {
    map.canvas.addEventListener('pointermove', (event) => {
      const point = mapPoint(map, event);
      if (!point || !fit) { Viz.tip.hide(); return; }
      if (event.buttons & 1) setCut(point);
      const i = Math.min(G - 1, Math.floor(point.delta * G)), j = Math.min(G - 1, Math.floor(point.p * G));
      const target = targetG[i * G + j], sum = approxG[i * G + j];
      Viz.tip.show(event.clientX, event.clientY, `δ = ${point.delta.toFixed(2)}, p = ${point.p.toFixed(2)}`, [
        { label: 'Target', value: fmt(target, 3) },
        { label: 'Sum', value: fmt(sum, 3) },
        { label: 'Error', value: fmt(target - sum, 2) },
      ]);
    });
    map.canvas.addEventListener('pointerdown', (event) => { const point = mapPoint(map, event); if (point) setCut(point); });
    map.canvas.addEventListener('pointerleave', () => Viz.tip.hide());
  }

  // ---------------------------------------------------------------------------
  // Part 2: cross-section and error curve
  // ---------------------------------------------------------------------------

  function drawSlice() {
    section = crossSection();
    const theme = Viz.theme(), pad = 0.06 * (valueHi - valueLo), lo = valueLo - pad, hi = valueHi + pad;
    const name = section.alongDelta ? 'p' : 'δ';
    $('mk-cut').value = section.at;
    $('mk-cut-out').textContent = `${name} = ${section.at.toFixed(2)}`;
    sliceChart.draw({
      x: [0, 1], y: [lo, hi],
      xTicks: [0, 0.25, 0.5, 0.75, 1].map((value) => ({ value, label: String(value) })),
      yTicks: Viz.ticks(lo, hi, 5).map((value) => ({ value, label: fmt(value, 3) })),
      xTitle: section.alongDelta ? 'index δ' : 'price p',
      series: [{ color: theme.series[0], points: section.target }, { color: theme.series[1], points: section.sum }],
    });
  }

  function hoverSlice(x) {
    if (!section) return null;
    const s = clamp(Math.round(x * S), 0, S), theme = Viz.theme();
    const target = section.target[s][1], sum = section.sum[s][1];
    const moving = section.alongDelta ? 'δ' : 'p', held = section.alongDelta ? 'p' : 'δ';
    return {
      x: sliceX[s],
      title: `${moving} = ${sliceX[s].toFixed(2)}, ${held} = ${section.at.toFixed(2)}`,
      rows: [
        { color: theme.series[0], label: 'Target', value: fmt(target, 3) },
        { color: theme.series[1], label: 'Sum', value: fmt(sum, 3) },
        { label: 'Error', value: fmt(target - sum, 2) },
      ],
      dots: [{ y: target, color: theme.series[0] }, { y: sum, color: theme.series[1] }],
    };
  }

  /**
   * A log axis for errors: decades 10^e0 to 10^e1 covering `values`, and clip(v) to
   * draw a value on it. The axis stops nine decades below the size of f, where an
   * error is rounding noise.
   */
  function errorAxis(values) {
    let top = 0;
    for (const v of values) top = Math.max(top, v);
    const floor = 1e-9 * Math.max(fit.norm, top) || 1e-12;
    top = Math.max(top, 10 * floor);
    const clip = (v) => Math.max(v, floor);
    let low = top;
    for (const v of values) low = Math.min(low, clip(v));
    const e1 = Math.ceil(Math.log10(top) - 1e-9), e0 = Math.min(e1 - 1, Math.floor(Math.log10(low) + 1e-9));
    return { e0, e1, clip };
  }
  const sumErrors = () => fit.rms.subarray(1);            // RMS error of the first n pieces, n = 1..N

  function drawErrorChart() {
    const theme = Viz.theme(), { e0, e1, clip } = errorAxis(sumErrors()), points = [];
    for (let n = 1; n <= dict.N; n++) points.push([n, clip(fit.rms[n])]);
    errorChart.draw({
      x: [1, dict.N], y: [10 ** e0, 10 ** e1], yLog: true,
      xTicks: Viz.ticks(0, dict.N, 5).map((v) => ({ value: Math.max(1, v), label: String(Math.max(1, v)) })),
      yTicks: Viz.decades(e0, e1),
      xTitle: 'pieces in the sum, N',
      series: [{ color: theme.series[2], points }],
      marker: { x: state.n, label: `N = ${state.n}`, dots: [{ y: clip(fit.rms[state.n]), color: theme.series[2] }] },
    });
  }

  function hoverError(x) {
    const n = clamp(Math.round(x), 1, dict.N), theme = Viz.theme();
    return {
      x: n,
      title: `N = ${n}`,
      rows: [
        { color: theme.series[2], label: 'RMS error', value: errorText(fit.rms[n]) },
        { label: 'Largest error', value: errorText(fit.sup[n]) },
      ],
      dots: [{ y: errorAxis(sumErrors()).clip(fit.rms[n]), color: theme.series[2] }],
    };
  }

  // ---------------------------------------------------------------------------
  // Part 3: curves
  // ---------------------------------------------------------------------------

  /**
   * A chain function inside `box`, filled red where positive and blue where negative,
   * with its knots on the zero line. With options.vertical the variable runs upward
   * and the value to the right, to sit beside the p axis of a heat map.
   */
  function drawCurve(ctx, box, values, vmax, options) {
    const theme = Viz.theme(), n = values.length, vertical = !!options.vertical;
    const amplitude = ((vertical ? box.w : box.h) / 2 - 3) / vmax;
    const along = (t) => (vertical ? box.y + box.h - t * box.h : box.x + t * box.w);
    const zero = vertical ? box.x + box.w / 2 : box.y + box.h / 2;
    const point = (t, v) => (vertical ? [zero + v * amplitude, along(t)] : [along(t), zero - v * amplitude]);

    const area = new Path2D(), line = new Path2D();
    area.moveTo(...point(0.5 / n, 0));
    for (let i = 0; i < n; i++) {
      const [x, y] = point((i + 0.5) / n, values[i]);
      area.lineTo(x, y);
      if (i) line.lineTo(x, y); else line.moveTo(x, y);
    }
    area.lineTo(...point(1 - 0.5 / n, 0));
    area.closePath();
    for (const sign of [1, -1]) {
      ctx.save();
      ctx.beginPath();
      if (vertical) ctx.rect(sign > 0 ? zero : box.x, box.y, box.w / 2, box.h);
      else ctx.rect(box.x, sign > 0 ? box.y : zero, box.w, box.h / 2);
      ctx.clip();
      ctx.globalAlpha = 0.55;
      ctx.fillStyle = theme.diverging.at(sign > 0 ? 0.78 : 0.22);
      ctx.fill(area);
      ctx.restore();
    }

    const z = Math.round(zero) + 0.5;
    ctx.strokeStyle = theme.axis;
    ctx.lineWidth = 1;
    ctx.beginPath();
    if (vertical) { ctx.moveTo(z, box.y); ctx.lineTo(z, box.y + box.h); } else { ctx.moveTo(box.x, z); ctx.lineTo(box.x + box.w, z); }
    ctx.stroke();

    ctx.strokeStyle = theme.ink2;
    ctx.lineWidth = 1.5;
    ctx.lineJoin = 'round';
    ctx.stroke(line);

    for (const knot of options.knots || []) {
      const [x, y] = point(knot, 0);
      if (knot === options.newKnot) {
        ctx.fillStyle = theme.ink;
        ctx.beginPath();
        ctx.arc(x, y, 2.75, 0, 2 * Math.PI);
        ctx.fill();
      } else {
        ctx.strokeStyle = theme.muted;
        ctx.beginPath();
        if (vertical) { ctx.moveTo(z - 3.5, Math.round(y) + 0.5); ctx.lineTo(z + 3.5, Math.round(y) + 0.5); }
        else { ctx.moveTo(Math.round(x) + 0.5, z - 3.5); ctx.lineTo(Math.round(x) + 0.5, z + 3.5); }
        ctx.lineWidth = 1;
        ctx.stroke();
      }
    }
  }

  const curveOptions = (m, vertical) => ({ vertical, knots: dict.chain.info[m].knots, newKnot: dict.chain.info[m].knot });

  function buildChain() {
    const host = $('mk-chain'), kappa = state.kappa, top = Math.min(dict.chain.M, kappa + 7);
    const shapes = SHAPES.slice(0, kappa + 1).map((shape) => 'a ' + shape);
    const listed = shapes.slice(0, -1).join(', ') + ' and ' + shapes[shapes.length - 1];
    $('mk-chain-text').textContent =
      `With one input the pieces form a chain of curves. The first ${['', '', 'two', 'three', 'four'][kappa + 1]} are polynomials: ${listed}. ` +
      `Each curve after that is a spline that adds one knot, a point where the curve may pass from one ${SHAPES[kappa]} to another. ` +
      'The knots halve the gaps left by the earlier ones: ½, then ¼ and ¾, then the eighths. ' +
      'Every curve is made orthogonal to all the curves before it, so it adds only detail that they cannot express.';
    host.textContent = '';
    chainFigures = [];
    for (let m = 0; m <= top; m++) {
      const figure = el('figure', {}, host);
      const canvas = el('canvas', {}, figure);
      const name = el('div', { class: 'name' }, figure);
      tex(el('span', {}, name), `\\psi_{${m}}`);
      el('span', { class: 'what', text: describeCurve(m) }, name);
      chainFigures.push({ canvas, m });
    }
  }

  function drawChain() {
    for (const { canvas, m } of chainFigures) {       // each curve at its own scale: the shape is the point
      const { ctx, w, h } = Viz.fitCanvas(canvas);
      if (w) drawCurve(ctx, { x: 0, y: 0, w, h }, psiG[m], peakG[m], curveOptions(m, false));
    }
  }

  // ---------------------------------------------------------------------------
  // Part 3: the grid of products
  // ---------------------------------------------------------------------------

  /** One T x T thumbnail per piece, laid out by (k_delta, k_p), in the diverging ramp. */
  function buildSprites() {
    const cols = dict.K[0] + 1, rows = dict.K[1] + 1, ramp = Viz.theme().diverging.packed;
    sprite.width = cols * T;
    sprite.height = rows * T;
    const ctx = sprite.getContext('2d'), image = ctx.createImageData(sprite.width, sprite.height);
    const pixels = new Uint32Array(image.data.buffer);
    for (const { k } of dict.pieces) {
      const a = psiT[k[0]], b = psiT[k[1]], scale = 0.5 / (peakT[k[0]] * peakT[k[1]]);
      for (let row = 0; row < T; row++) {
        const bv = b[T - 1 - row] * scale, base = (k[1] * T + row) * sprite.width + k[0] * T;
        for (let col = 0; col < T; col++) pixels[base + col] = ramp[((0.5 + a[col] * bv) * 255 + 0.5) | 0];
      }
    }
    ctx.putImageData(image, 0, 0);
  }

  const LATTICE = { left: 42, right: 10, top: 8, bottom: 62 };
  let cell = 24;

  function drawLattice() {
    const canvas = $('mk-lattice'), cols = dict.K[0] + 1, rows = dict.K[1] + 1, theme = Viz.theme();
    const room = canvas.parentNode.clientWidth - LATTICE.left - LATTICE.right;
    if (room <= 0) return;
    cell = clamp(Math.min(Math.floor(room / cols), Math.floor(380 / rows)), 14, 30);
    const width = LATTICE.left + cols * cell + LATTICE.right, height = LATTICE.top + rows * cell + LATTICE.bottom;
    const { ctx } = Viz.fitCanvas(canvas, width, height);
    const left = (k1) => LATTICE.left + k1 * cell, top = (k2) => LATTICE.top + (rows - 1 - k2) * cell;
    ctx.imageSmoothingQuality = 'high';

    for (let k1 = 0; k1 < cols; k1++) {
      for (let k2 = 0; k2 < rows; k2++) {
        const i = dict.indexOf(k1, k2);
        if (i < 0) {
          ctx.fillStyle = theme.axis;
          ctx.beginPath();
          ctx.arc(left(k1) + cell / 2, top(k2) + cell / 2, 1.5, 0, 2 * Math.PI);
          ctx.fill();
          continue;
        }
        ctx.globalAlpha = i < state.n ? 1 : 0.4;
        ctx.drawImage(sprite, k1 * T, k2 * T, T, T, left(k1) + 1, top(k2) + 1, cell - 2, cell - 2);
      }
    }
    ctx.globalAlpha = 1;
    const ring = (i, color, lineWidth) => {
      const [k1, k2] = dict.pieces[i].k;
      ctx.strokeStyle = color;
      ctx.lineWidth = lineWidth;
      ctx.strokeRect(left(k1), top(k2), cell, cell);
    };
    if (state.focus !== null && state.focus !== state.n - 1) ring(state.focus, theme.muted, 2);
    ring(state.n - 1, theme.ink, 2);

    // Which curve: its number, and under the delta axis the kind of curve.
    const floorY = LATTICE.top + rows * cell;
    ctx.fillStyle = theme.muted;
    ctx.font = '10px system-ui, sans-serif';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'top';
    const every = cell >= 20 ? 1 : 2;
    for (let k1 = 0; k1 < cols; k1 += every) ctx.fillText(String(k1), left(k1) + cell / 2, floorY + 5);
    ctx.textAlign = 'right';
    ctx.textBaseline = 'middle';
    for (let k2 = 0; k2 < rows; k2++) ctx.fillText(String(k2), LATTICE.left - 6, top(k2) + cell / 2);

    const groups = [{ from: 0, to: state.kappa, labels: ['polynomials', 'poly.'] }];
    for (let level = 0; state.kappa + 2 ** level < cols; level++) {
      groups.push({ from: state.kappa + 2 ** level, to: Math.min(cols - 1, state.kappa + 2 ** (level + 1) - 1), labels: LEVEL_LABELS[level] || [] });
    }
    ctx.font = '11px system-ui, sans-serif';
    ctx.textAlign = 'center';
    ctx.textBaseline = 'top';
    ctx.strokeStyle = theme.axis;
    ctx.lineWidth = 1;
    for (const group of groups) {
      const x1 = left(group.from) + 3, x2 = left(group.to) + cell - 3, y = floorY + 22.5;
      ctx.beginPath();
      ctx.moveTo(x1 + 0.5, y - 3); ctx.lineTo(x1 + 0.5, y); ctx.lineTo(x2 - 0.5, y); ctx.lineTo(x2 - 0.5, y - 3);
      ctx.stroke();
      const label = group.labels.find((text) => ctx.measureText(text).width <= x2 - x1 + 8);
      if (label) ctx.fillText(label, (x1 + x2) / 2, y + 4);
    }
    ctx.fillStyle = theme.ink2;
    ctx.font = '12px system-ui, sans-serif';
    ctx.fillText('which curve in δ', LATTICE.left + cols * cell / 2, floorY + 44);
    ctx.save();
    ctx.translate(11, LATTICE.top + rows * cell / 2);
    ctx.rotate(-Math.PI / 2);
    ctx.textBaseline = 'middle';
    ctx.fillText('which curve in p', 0, 0);
    ctx.restore();
  }

  function latticePiece(event) {
    const box = $('mk-lattice').getBoundingClientRect(), rows = dict.K[1] + 1;
    const k1 = Math.floor((event.clientX - box.left - LATTICE.left) / cell);
    const k2 = rows - 1 - Math.floor((event.clientY - box.top - LATTICE.top) / cell);
    return k1 >= 0 && k1 <= dict.K[0] && k2 >= 0 && k2 < rows ? dict.indexOf(k1, k2) : -1;
  }

  function setFocus(i) {
    if (i === state.focus) return;
    state.focus = i;
    drawLattice();
    drawDetail();
  }

  // ---------------------------------------------------------------------------
  // Part 3: one piece, and the table of all of them
  // ---------------------------------------------------------------------------

  function drawDetail() {
    const i = state.focus !== null ? state.focus : state.n - 1;
    const piece = dict.pieces[i], [k1, k2] = piece.k, theme = Viz.theme(), a = dict.a;
    const title = $('mk-detail-title');
    title.textContent = `Piece ${i + 1} of ${dict.N}`;
    el('small', { text: state.focus === null ? 'the newest in the sum' : i < state.n ? 'in the sum' : 'not in the sum yet' }, title);

    const { ctx } = Viz.fitCanvas($('mk-detail-canvas'), 236, 236);
    const map = { x: 4, y: 64, size: 168 }, strip = 52;
    Viz.paint(detailImage, G, G, theme.diverging, (col, row) => 0.5 + 0.5 * psiG[k1][col] * psiG[k2][row] / (peakG[k1] * peakG[k2]));
    ctx.imageSmoothingQuality = 'high';
    ctx.drawImage(detailImage, map.x, map.y, map.size, map.size);
    drawCurve(ctx, { x: map.x, y: 4, w: map.size, h: strip }, psiG[k1], peakG[k1], curveOptions(k1, false));
    drawCurve(ctx, { x: map.x + map.size + 8, y: map.y, w: strip, h: map.size }, psiG[k2], peakG[k2], curveOptions(k2, true));
    ctx.fillStyle = theme.muted;
    ctx.font = '11px system-ui, sans-serif';
    ctx.textAlign = 'right';
    ctx.textBaseline = 'alphabetic';
    ctx.fillText('← in δ', 232, 26);
    ctx.fillText('in p ↓', 232, 50);

    const product = `\\psi_{${k1}}(\\delta)\\,\\psi_{${k2}}(p)`, written = pieceTeX(piece.k);
    const formula = $('mk-detail-formula');
    formula.textContent = '';
    tex(el('div', {}, formula), product);
    if (written !== product) tex(el('div', {}, formula), `=\\; ${written}`);
    const c1 = dict.chain.info[k1].weight, c2 = dict.chain.info[k2].weight;
    const facts = $('mk-detail-facts');
    facts.textContent = '';
    const fact = (name, value) => { el('dt', { text: name }, facts); el('dd', { text: value }, facts); };
    fact('In δ', `${psiName(k1, 'δ')}: ${describeCurve(k1)}, cost ${c1}`);
    fact('In p', `${psiName(k2, 'p')}: ${describeCurve(k2)}, cost ${c2}`);
    fact('Cost', `${weightText(a[0])} × ${c1} + ${weightText(a[1])} × ${c2} = ${piece.omega}`);
    fact('Weight', weightValue(i));
    fact('RMS error', `from ${errorText(fit.rms[i])} to ${errorText(fit.rms[i + 1])}`);
  }

  const weightValue = (i) => (isExact(Math.abs(fit.theta[i])) ? '0' : fmt(fit.theta[i], 3));

  function buildTerms() {
    const body = $('mk-terms');
    body.textContent = '';
    shownN = 0;
    termRows = dict.pieces.map((piece, i) => {
      const row = el('tr', { class: 'off' }, body);
      el('td', { class: 'num', text: i + 1 }, row);
      const name = el('div', { class: 'piece' }, el('td', {}, row));
      const thumb = el('canvas', { width: 44, height: 44 }, name);
      thumb.getContext('2d').drawImage(sprite, piece.k[0] * T, piece.k[1] * T, T, T, 0, 0, 44, 44);
      tex(el('span', {}, name), pieceTeX(piece.k));
      el('td', { class: 'num', text: piece.omega }, row);
      const value = el('td', { class: 'num' }, row);
      const rms = el('td', { class: 'num' }, row);
      row.addEventListener('click', () => { pause(); setN(i + 1); });
      row.addEventListener('pointerenter', () => setFocus(i));
      return { row, thumb, value, rms };
    });
  }

  /** Thumbnails again, after the theme changed the ramp. */
  function drawTermThumbs() {
    termRows.forEach(({ thumb }, i) => {
      const k = dict.pieces[i].k, ctx = thumb.getContext('2d');
      ctx.clearRect(0, 0, 44, 44);
      ctx.drawImage(sprite, k[0] * T, k[1] * T, T, T, 0, 0, 44, 44);
    });
  }

  function drawTermValues() {
    termRows.forEach(({ value, rms }, i) => {
      value.textContent = weightValue(i);
      rms.textContent = errorText(fit.rms[i + 1]);
    });
  }

  function drawTermMarks() {
    const n = state.n;
    for (let i = Math.min(shownN, n) - 1; i < Math.max(shownN, n); i++) {
      if (i < 0 || i >= termRows.length) continue;
      termRows[i].row.classList.toggle('off', i >= n);
      termRows[i].row.classList.toggle('current', i === n - 1);
    }
    shownN = n;
    const scroller = $('mk-terms-scroll'), row = termRows[n - 1].row;
    if (!scroller.matches(':hover') && (row.offsetTop < scroller.scrollTop + 34 || row.offsetTop + row.offsetHeight > scroller.scrollTop + scroller.clientHeight)) {
      scroller.scrollTop = Math.max(0, row.offsetTop - scroller.clientHeight / 2);
    }
  }

  // ---------------------------------------------------------------------------
  // Part 4: two inputs, with and without the sparsity
  // ---------------------------------------------------------------------------

  /** The full grid with the same curves as the first n pieces. */
  const boxAt = (n) => dict.boxes[dict.boxOf[n]];
  const boxName = (box) => `${box.k[0] + 1} × ${box.k[1] + 1}`;
  const bothErrors = () => Array.from(sumErrors()).concat(fit.boxRms);     // one axis for the two curves

  const BOX = { left: 26, right: 6, top: 6, bottom: 24 };

  /** The grid of part 3 in outline: the pieces of the sum, and the rectangle the full grid fills. */
  function drawBox() {
    const canvas = $('mk-box'), cols = dict.K[0] + 1, rows = dict.K[1] + 1, theme = Viz.theme(), box = boxAt(state.n);
    const room = canvas.parentNode.clientWidth - BOX.left - BOX.right;
    if (room <= 0) return;
    const size = clamp(Math.min(Math.floor(room / cols), Math.floor(230 / rows)), 5, 16), gap = size >= 9 ? 2 : 1;
    const { ctx } = Viz.fitCanvas(canvas, BOX.left + cols * size + BOX.right, BOX.top + rows * size + BOX.bottom);
    const floorY = BOX.top + rows * size;
    for (let k1 = 0; k1 < cols; k1++) {
      for (let k2 = 0; k2 < rows; k2++) {
        const x = BOX.left + k1 * size, y = floorY - (k2 + 1) * size, i = dict.indexOf(k1, k2);
        if (i >= 0 && i < state.n) {
          ctx.globalAlpha = 1;
          ctx.fillStyle = theme.series[2];
          ctx.fillRect(x + gap / 2, y + gap / 2, size - gap, size - gap);
        } else if (k1 <= box.k[0] && k2 <= box.k[1]) {
          ctx.globalAlpha = 0.4;
          ctx.fillStyle = theme.muted;
          ctx.fillRect(x + gap / 2, y + gap / 2, size - gap, size - gap);
        } else {
          ctx.globalAlpha = 1;
          ctx.fillStyle = theme.axis;
          ctx.beginPath();
          ctx.arc(x + size / 2, y + size / 2, 1, 0, 2 * Math.PI);
          ctx.fill();
        }
      }
    }
    ctx.globalAlpha = 1;
    const width = (box.k[0] + 1) * size, height = (box.k[1] + 1) * size;
    ctx.strokeStyle = theme.ink;
    ctx.lineWidth = 1.5;
    ctx.strokeRect(BOX.left - 1.25, floorY - height - 1.25, width + 2.5, height + 2.5);
    ctx.fillStyle = theme.ink2;
    ctx.font = '11px system-ui, sans-serif';
    ctx.textAlign = 'left';
    ctx.textBaseline = 'top';
    ctx.fillText(`${plural(box.k[0] + 1, 'curve')} in δ`, BOX.left, floorY + 8);
    ctx.save();
    ctx.translate(BOX.left - 12, floorY);
    ctx.rotate(-Math.PI / 2);
    ctx.textBaseline = 'middle';
    ctx.fillText(`${box.k[1] + 1} in p`, 0, 0);
    ctx.restore();
  }

  function drawCompareTable() {
    const body = $('mk-compare-rows'), theme = Viz.theme(), n = state.n, box = boxAt(n);
    body.textContent = '';
    const row = (color, label, count, error) => {
      const line = el('tr', {}, body), name = el('td', {}, line);
      el('span', { class: 'swatch' }, name).style.background = color;
      name.appendChild(document.createTextNode(label));
      el('td', { class: 'num', text: count }, line);
      el('td', { class: 'num', text: error }, line);
    };
    row(theme.series[2], n === 1 ? 'Matryoshka, the first piece' : `Matryoshka, the first ${n} pieces`, n, errorText(fit.rms[n]));
    row(theme.ink2, `Full grid with the same curves, ${boxName(box)}`, box.size, errorText(fit.boxRms[dict.boxOf[n]]));
    if (box.size !== n) {
      const shown = box.size <= dict.N;
      row(theme.series[2], 'Matryoshka at the size of that grid', box.size, shown ? errorText(fit.rms[box.size]) : `past the ${dict.N} shown`);
    }
  }

  function drawCompareChart() {
    const theme = Viz.theme(), last = dict.boxes[dict.boxes.length - 1].size;
    const { e0, e1, clip } = errorAxis(bothErrors());
    const ours = [], grids = dict.boxes.map((box, b) => [box.size, clip(fit.boxRms[b])]);
    for (let n = 1; n <= dict.N; n++) ours.push([n, clip(fit.rms[n])]);
    const n = state.n, box = boxAt(n);
    const mine = { x: n, y: clip(fit.rms[n]), color: theme.series[2] };
    const theirs = { x: box.size, y: clip(fit.boxRms[dict.boxOf[n]]), color: theme.ink2 };
    compareChart.draw({
      x: [1, last * 1.12], y: [10 ** e0, 10 ** e1], xLog: true, yLog: true,
      xTicks: [1, 2, 5, 10, 20, 50, 100, 200, 500, 1000].filter((v) => v <= last * 1.12).map((value) => ({ value, label: String(value) })),
      yTicks: Viz.decades(e0, e1),
      xTitle: 'number of parameters',
      series: [{ color: theme.ink2, points: grids, dots: true }, { color: theme.series[2], points: ours }],
      link: [[theirs.x, theirs.y], [mine.x, mine.y]],
      highlights: [theirs, mine],
    });
  }

  /** At a size on the chart: the Matryoshka sum of that size, and the full grid nearest in size. */
  function hoverCompare(x) {
    const theme = Viz.theme(), { clip } = errorAxis(bothErrors());
    let b = 0;
    dict.boxes.forEach((box, i) => { if (Math.abs(Math.log(box.size / x)) < Math.abs(Math.log(dict.boxes[b].size / x))) b = i; });
    const box = dict.boxes[b], n = Math.round(x);
    const gridRow = { color: theme.ink2, label: `Full grid ${boxName(box)}, ${plural(box.size, 'parameter')}`, value: errorText(fit.boxRms[b]) };
    const gridDot = { x: box.size, y: clip(fit.boxRms[b]), color: theme.ink2 };
    if (n > dict.N) return { x: box.size, title: 'RMS error', rows: [gridRow], dots: [gridDot] };
    return {
      x: Math.max(1, n),
      title: 'RMS error',
      rows: [{ color: theme.series[2], label: `Matryoshka, ${plural(Math.max(1, n), 'parameter')}`, value: errorText(fit.rms[Math.max(1, n)]) }, gridRow],
      dots: [gridDot, { y: clip(fit.rms[Math.max(1, n)]), color: theme.series[2] }],
    };
  }

  // ---------------------------------------------------------------------------
  // Part 4: many inputs
  // ---------------------------------------------------------------------------

  /** Ordering weights with J products: those of part 1 on the own index and price, 1 on every rival coordinate. */
  const weightsFor = (products) => WEIGHTS[state.weights].a.concat(new Array(2 * products - 2).fill(1));
  const levelName = (level) => (Number.isInteger(level) ? String(level) : (Math.floor(level) || '') + '½');
  const parameters = (size) => `${Viz.count(size)} parameter${size === 1n ? '' : 's'}`;
  /** A share of the error of a constant, as a percentage: 29%, 6.4%, 0.89%. */
  const percent = (share) => { const v = 100 * share; return (v >= 10 ? Math.round(v) : Number(v.toPrecision(2))) + '%'; };

  function buildSystem() {
    system = Matryoshka.demandSystem({
      types: PROBIT_CONSUMERS, shocks: Matryoshka.SHOCKS.probit,
      a: WEIGHTS[state.weights].a, kappa: state.kappa, maxLevel: LEVELS[LEVELS.length - 1],
    });
    systemCache.clear();
  }

  /**
   * The J-product demand at every half level: for the prefix set and for the full grid with
   * the same curves, the number of parameters and the RMS error as a share of a constant's.
   */
  function systemAt(J) {
    if (!systemCache.has(J)) {
      const result = system.at(J), a = weightsFor(J), scale = result.constant || 1;
      systemCache.set(J, result.levels.map((entry) => ({
        level: entry.level,
        ours: { size: Matryoshka.prefixSize(a, entry.level, state.kappa), error: entry.ours / scale },
        grid: { size: Matryoshka.gridSize(a, entry.level, state.kappa), error: entry.grid / scale },
      })));
    }
    return systemCache.get(J);
  }

  function buildSizes() {
    sizes = { ours: [null], grid: [null] };
    for (let J = 1; J <= MAX_PRODUCTS; J++) {
      sizes.ours.push(Matryoshka.prefixSize(weightsFor(J), state.level, state.kappa));
      sizes.grid.push(Matryoshka.gridSize(weightsFor(J), state.level, state.kappa));
    }
  }

  /** The level singled out: the full grid of that level, the prefix set of the same level, and the first prefix set as accurate as the grid. */
  function systemPicks() {
    const levels = systemAt(state.products), same = levels[2 * state.level];
    const match = levels.find((entry) => entry.ours.error <= same.grid.error * (1 + 1e-9));
    return { levels, same, match: match || null };
  }

  function drawSystem() {
    const theme = Viz.theme(), J = state.products, { levels, same, match } = systemPicks(), last = levels[levels.length - 1];
    $('mk-products').value = J;
    $('mk-products-out').textContent = `J = ${J}, ${2 * J} inputs`;
    $('mk-level-hint').textContent =
      `With one product, level ${state.level} is the doll of ${Viz.count(sizes.ours[1])} pieces in part 2, and its full grid has ${Viz.count(sizes.grid[1])}.`;

    // In words
    const grid = `With ${plural(J, 'product')}, the full grid of level ${state.level} has ${Viz.count(same.grid.size)} parameters and an error of ${percent(same.grid.error)}.`;
    $('mk-system-summary').textContent = !match
      ? `${grid} The Matryoshka dictionary has not caught up by level ${levelName(last.level)}, where it has ${Viz.count(last.ours.size)} parameters and an error of ${percent(last.ours.error)}.`
      : match.ours.size === same.grid.size
        ? `${grid} With so few inputs it is the same set of pieces as the Matryoshka dictionary of that level.`
        : `${grid} The Matryoshka dictionary does at least as well with ${Viz.count(match.ours.size)}.`;

    // In a table
    const body = $('mk-system-rows');
    body.textContent = '';
    const row = (color, label, count, error) => {
      const line = el('tr', {}, body), name = el('td', {}, line);
      el('span', { class: 'swatch' }, name).style.background = color;
      name.appendChild(document.createTextNode(label));
      el('td', { class: 'num', text: count }, line);
      el('td', { class: 'num', text: error }, line);
    };
    row(theme.series[2], `Matryoshka, level ${state.level}`, Viz.count(same.ours.size), percent(same.ours.error));
    row(theme.ink2, 'Full grid with the same curves', Viz.count(same.grid.size), percent(same.grid.error));
    if (!match) row(theme.series[2], `Matryoshka: no level up to ${levelName(last.level)} does as well as that grid`, '', '');
    else if (match !== same) row(theme.series[2], `Matryoshka, level ${levelName(match.level)}: the first to do as well as that grid`, Viz.count(match.ours.size), percent(match.ours.error));

    // As a chart: error against the number of parameters, both on log scales
    $('mk-system-title').textContent = 'RMS error against the number of parameters';
    el('small', { text: `${plural(J, 'product')}, log scales` }, $('mk-system-title'));
    const floor = 1e-6, clip = (v) => Math.max(v, floor);
    const line = (which) => levels.map((entry) => [Number(entry[which].size), clip(entry[which].error)]);
    let lowest = 1;
    for (const entry of levels) lowest = Math.min(lowest, clip(entry.grid.error));
    const e0 = Math.min(-1, Math.floor(Math.log10(lowest) + 1e-9)), top = Math.log10(Number(last.grid.size));
    const xTicks = top > 3.5
      ? Viz.decades(0, Math.ceil(top), 8)
      : [1, 2, 5, 10, 20, 50, 100, 200, 500, 1000, 2000].filter((v) => v <= 10 ** top).map((value) => ({ value, label: String(value) }));
    const point = (entry, which, extra) => Object.assign({ x: Number(entry[which].size), y: clip(entry[which].error), color: which === 'grid' ? theme.ink2 : theme.series[2] }, extra);
    const highlights = [point(same, 'ours'), point(same, 'grid', { label: Viz.count(same.grid.size) })];
    if (match && match !== same) highlights.push(point(match, 'ours', { label: Viz.count(match.ours.size), below: true }));
    systemChart.draw({
      x: [1, 10 ** (top * 1.06 + 0.15)], y: [10 ** e0, 1], xLog: true, yLog: true,
      xTicks,
      yTicks: Viz.decades(e0, 0).map((tick) => ({ value: tick.value, label: Number((100 * tick.value).toPrecision(1)) + '%' })),
      xTitle: 'number of parameters',
      series: [{ color: theme.ink2, points: line('grid'), dots: true }, { color: theme.series[2], points: line('ours'), dots: true }],
      link: match && match !== same ? [[Number(same.grid.size), clip(same.grid.error)], [Number(match.ours.size), clip(match.ours.error)]] : null,
      highlights,
    });
  }

  /** The level whose point, of either curve, is nearest in size. */
  function hoverSystem(x) {
    const theme = Viz.theme(), levels = systemAt(state.products), distance = (size) => Math.abs(Math.log(Number(size) / x));
    let best = levels[0], which = 'ours';
    for (const entry of levels) {
      for (const side of ['ours', 'grid']) if (distance(entry[side].size) < distance(best[which].size)) { best = entry; which = side; }
    }
    const clip = (v) => Math.max(v, 1e-6);
    return {
      x: Number(best[which].size),
      title: `Level ${levelName(best.level)}`,
      rows: [
        { color: theme.series[2], label: `Matryoshka, ${parameters(best.ours.size)}`, value: percent(best.ours.error) },
        { color: theme.ink2, label: `Full grid, ${parameters(best.grid.size)}`, value: percent(best.grid.error) },
      ],
      dots: [{ x: Number(best.grid.size), y: clip(best.grid.error), color: theme.ink2 }, { x: Number(best.ours.size), y: clip(best.ours.error), color: theme.series[2] }],
    };
  }

  function drawSizes() {
    const theme = Viz.theme(), J = state.products, ours = sizes.ours[J], grid = sizes.grid[J];
    const top = Math.ceil(Math.log10(Number(sizes.grid[MAX_PRODUCTS])));
    const line = (values) => values.slice(1).map((v, i) => [i + 1, Number(v)]);
    $('mk-scaling-note').textContent = `at level ${state.level}, log scale`;
    scalingChart.draw({
      x: [1, MAX_PRODUCTS], y: [1, 10 ** top], yLog: true,
      xTicks: [1, 10, 20, 30, 40, 50].map((value) => ({ value, label: String(value) })),
      yTicks: Viz.decades(0, top, 7),
      xTitle: 'products J',
      series: [{ color: theme.ink2, points: line(sizes.grid) }, { color: theme.series[2], points: line(sizes.ours) }],
      marker: { x: J, dots: [{ y: Number(grid), color: theme.ink2 }, { y: Number(ours), color: theme.series[2] }] },
    });
  }

  function hoverSizes(x) {
    const J = clamp(Math.round(x), 1, MAX_PRODUCTS), theme = Viz.theme();
    return {
      x: J,
      title: `${plural(J, 'product')}, ${2 * J} inputs`,
      rows: [
        { color: theme.ink2, label: 'Full grid', value: Viz.count(sizes.grid[J]) },
        { color: theme.series[2], label: 'Matryoshka', value: Viz.count(sizes.ours[J]) },
      ],
      dots: [{ y: Number(sizes.grid[J]), color: theme.ink2 }, { y: Number(sizes.ours[J]), color: theme.series[2] }],
    };
  }

  /** Both charts of the many-input figure, and the words and the table above them. */
  function drawMany() {
    drawSystem();
    drawSizes();
  }

  // ---------------------------------------------------------------------------
  // Drawing, by what changed
  // ---------------------------------------------------------------------------

  /** N changed (or everything did). */
  function drawN() {
    approximate(state.n);
    paintSum();
    drawMaps();
    drawSlice();
    drawErrorChart();
    drawStats();
    drawDolls();
    drawLattice();
    drawTermMarks();
    drawDetail();
    drawBox();
    drawCompareTable();
    drawCompareChart();
    drawPlayButton();
  }

  /** The function or the dictionary changed. */
  function drawFit() {
    paintTarget();
    drawTermValues();
    drawChain();
    drawN();
  }

  /** The cross-section moved. */
  function drawCut() {
    drawMaps();
    drawSlice();
  }

  /** The window or the theme changed. */
  function redraw(themeChanged) {
    if (!fit) return;
    if (themeChanged) { buildSprites(); drawTermThumbs(); drawLegends(); }
    drawFit();
    drawMany();
  }

  /** Legends: a stroke of the color for a line, a square for a filled cell. */
  function drawLegends() {
    const theme = Viz.theme();
    const legend = (id, mark, items) => {
      const host = $(id);
      host.textContent = '';
      for (const [label, color, opacity] of items) {
        const item = el('span', {}, host), key = el('span', { class: mark }, item);
        if (mark === 'key') key.style.borderColor = color; else key.style.background = color;
        if (opacity) key.style.opacity = opacity;
        item.appendChild(document.createTextNode(label));
      }
    };
    const both = [['Matryoshka', theme.series[2]], ['Full grid', theme.ink2]];
    legend('mk-slice-legend', 'key', [['Target', theme.series[0]], ['Sum of the pieces', theme.series[1]]]);
    legend('mk-compare-legend', 'key', both);
    legend('mk-scaling-legend', 'key', both);
    legend('mk-system-legend', 'key', both);
    legend('mk-box-legend', 'swatch', [['in the Matryoshka sum', theme.series[2]], ['added by the full grid', theme.muted, 0.4]]);
  }

  // ---------------------------------------------------------------------------
  // Start
  // ---------------------------------------------------------------------------

  function start(panel) {
    input = $('mk-expr');
    statusBox = $('mk-expr-status');
    slider = $('mk-n');
    playButton = $('mk-play');
    for (const name of ['target', 'approx', 'error']) {
      maps[name] = { canvas: $('mk-map-' + name), scale: $('mk-scale-' + name), image: document.createElement('canvas') };
      watchMap(maps[name]);
    }
    sliceChart = Viz.lineChart($('mk-slice'), { label: 'Target and sum along the cross-section', hover: hoverSlice });
    errorChart = Viz.lineChart($('mk-error'), {
      label: 'RMS error against the number of pieces',
      hover: hoverError,
      pick: (x) => { pause(); setN(x); },
    });
    compareChart = Viz.lineChart($('mk-compare'), {
      label: 'RMS error against the number of parameters, for the Matryoshka sum and for full grids',
      hover: hoverCompare,
      pick: (x) => { pause(); setN(x); },
    });
    systemChart = Viz.lineChart($('mk-system'), {
      label: 'RMS error against the number of parameters with J products, for the Matryoshka dictionary and for full grids',
      height: 280,
      margin: { top: 26 },
      hover: hoverSystem,
    });
    scalingChart = Viz.lineChart($('mk-scaling'), {
      label: 'Number of parameters against the number of products, for the full grid and for the Matryoshka dictionary',
      height: 280,
      margin: { top: 26 },
      hover: hoverSizes,
      pick: (x) => { state.products = clamp(Math.round(x), 1, MAX_PRODUCTS); drawMany(); },
    });

    // Part 1
    const presets = $('mk-presets');
    for (const preset of PRESETS) {
      const chip = el('button', { class: 'chip', type: 'button', text: preset.name, 'data-expr': preset.expr, 'aria-pressed': 'false' }, presets);
      chip.addEventListener('click', () => { input.value = preset.expr; applyExpression(); });
    }
    input.value = PRESETS[0].expr;
    let typing = null;
    input.addEventListener('input', () => { clearTimeout(typing); typing = setTimeout(applyExpression, 220); });
    segmented($('mk-weights'), WEIGHTS.map((w) => w.label), state.weights, (i) => { state.weights = i; rebuild(); });
    segmented($('mk-kappa'), DEGREES.map((d) => d.label), DEGREES.findIndex((d) => d.kappa === state.kappa), (i) => { state.kappa = DEGREES[i].kappa; rebuild(); });

    // Part 2
    playButton.addEventListener('click', () => (state.playing ? pause() : play()));
    slider.addEventListener('input', () => { pause(); setN(Number(slider.value)); });
    segmented($('mk-cut-axis'), ['along δ', 'along p'], 0, (i) => { state.cutAxis = i === 0 ? 'p' : 'delta'; drawCut(); });
    $('mk-cut').addEventListener('input', (event) => {
      state.cut[state.cutAxis] = Number(event.target.value);
      drawCut();
    });
    $('mk-magnify').addEventListener('change', (event) => { state.magnify = event.target.checked; paintSum(); drawMaps(); });

    // Part 3
    const lattice = $('mk-lattice');
    lattice.addEventListener('pointermove', (event) => {
      const i = latticePiece(event);
      lattice.style.cursor = i >= 0 ? 'pointer' : 'default';
      setFocus(i >= 0 ? i : null);
      if (i < 0) { Viz.tip.hide(); return; }
      const [k1, k2] = dict.pieces[i].k;
      Viz.tip.show(event.clientX, event.clientY, `Piece ${i + 1}: ${psiName(k1, 'δ')} × ${psiName(k2, 'p')}`, [
        { label: 'Cost', value: String(dict.pieces[i].omega) },
        { label: 'Weight in the sum', value: weightValue(i) },
      ]);
    });
    lattice.addEventListener('pointerleave', () => { setFocus(null); Viz.tip.hide(); });
    lattice.addEventListener('click', (event) => { const i = latticePiece(event); if (i >= 0) { pause(); setN(i + 1); } });
    $('mk-terms').addEventListener('pointerleave', () => setFocus(null));

    // Part 4
    $('mk-products').max = MAX_PRODUCTS;
    $('mk-products').addEventListener('input', (event) => { state.products = Number(event.target.value); drawMany(); });
    segmented($('mk-level'), LEVELS.map(String), LEVELS.indexOf(state.level), (i) => { state.level = LEVELS[i]; buildSizes(); drawMany(); });

    drawLegends();
    build();
    applyExpression();

    let frame = null, width = panel.clientWidth;
    new ResizeObserver(() => {
      if (panel.clientWidth === width) return;
      width = panel.clientWidth;
      cancelAnimationFrame(frame);
      frame = requestAnimationFrame(() => redraw(false));
    }).observe(panel);
    Viz.onThemeChange(() => redraw(true));
    if (document.fonts && document.fonts.ready) document.fonts.ready.then(drawMaps);
  }

  App.register('matryoshka', start);
})();
