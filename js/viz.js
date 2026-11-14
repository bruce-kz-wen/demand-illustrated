/*
 * Shared drawing helpers for the illustrations: theme colors, color ramps,
 * canvases, number formats, a tooltip and a small SVG line chart.
 */
(function () {
  'use strict';
  const Viz = {};

  // ---------------------------------------------------------------------------
  // Theme
  // ---------------------------------------------------------------------------

  const darkQuery = window.matchMedia('(prefers-color-scheme: dark)');
  const listeners = [];
  let cached = null;
  // The reader's choice (data-theme on <html>, set by the header button) wins over the system setting.
  const isDark = () => {
    const chosen = document.documentElement.dataset.theme;
    return chosen ? chosen === 'dark' : darkQuery.matches;
  };
  const themeChanged = () => { cached = null; listeners.forEach((fn) => fn()); };

  /** Colors of the current theme, from the tokens of css/style.css. */
  Viz.theme = function () {
    if (cached) return cached;
    const style = getComputedStyle(document.documentElement);
    const token = (name) => style.getPropertyValue(name).trim();
    const dark = isDark();
    cached = {
      dark,
      surface: token('--surface'), ink: token('--ink'), ink2: token('--ink-2'), muted: token('--muted'),
      grid: token('--grid'), axis: token('--axis'),
      series: [token('--series-1'), token('--series-2'), token('--series-3')],
      sequential: makeRamp(dark ? SEQUENTIAL.slice().reverse() : SEQUENTIAL),
      diverging: makeRamp(divergingStops(dark)),
    };
    return cached;
  };
  Viz.onThemeChange = (fn) => listeners.push(fn);
  darkQuery.addEventListener('change', themeChanged);
  /** Switch between light and dark, and remember the choice on this device. */
  Viz.toggleTheme = function () {
    const next = isDark() ? 'light' : 'dark';
    document.documentElement.dataset.theme = next;
    try { localStorage.setItem('theme', next); } catch (error) { /* private window: the choice lasts for this visit */ }
    themeChanged();
  };

  // ---------------------------------------------------------------------------
  // Color ramps
  // ---------------------------------------------------------------------------

  // Sequential: one hue, light to dark; reversed on a dark surface so that small
  // values recede toward the surface in both themes.
  const SEQUENTIAL = ['#cde2fb', '#b7d3f6', '#9ec5f4', '#86b6ef', '#6da7ec', '#5598e7', '#3987e5',
                      '#2a78d6', '#256abf', '#1c5cab', '#184f95', '#104281', '#0d366b'];
  // Diverging: blue for negative, red for positive, a neutral gray at zero. The red
  // steps have the lightness and chroma of the blue steps (OKLCH), so the two arms
  // read as equally strong.
  const DIVERGING = {
    light: { mid: '#f0efec', neg: ['#9ec5f4', '#5598e7', '#256abf', '#104281'], pos: ['#f3ada7', '#e06e68', '#b43b3a', '#781e1f'] },
    dark: { mid: '#383835', neg: ['#1c5cab', '#3987e5', '#86b6ef', '#cde2fb'], pos: ['#a1302f', '#da5450', '#ec9992', '#fbd5d1'] },
  };
  function divergingStops(dark) {
    const d = dark ? DIVERGING.dark : DIVERGING.light;
    return d.neg.slice().reverse().concat([d.mid], d.pos);
  }

  const toLinear = (c) => (c <= 0.04045 ? c / 12.92 : ((c + 0.055) / 1.055) ** 2.4);
  const toGamma = (c) => (c <= 0.0031308 ? 12.92 * c : 1.055 * c ** (1 / 2.4) - 0.055);
  function hexToOklab(hex) {
    const r = toLinear(parseInt(hex.slice(1, 3), 16) / 255);
    const g = toLinear(parseInt(hex.slice(3, 5), 16) / 255);
    const b = toLinear(parseInt(hex.slice(5, 7), 16) / 255);
    const l = Math.cbrt(0.4122214708 * r + 0.5363325363 * g + 0.0514459929 * b);
    const m = Math.cbrt(0.2119034982 * r + 0.6806995451 * g + 0.1073969566 * b);
    const s = Math.cbrt(0.0883024619 * r + 0.2817188376 * g + 0.6299787005 * b);
    return [0.2104542553 * l + 0.793617785 * m - 0.0040720468 * s,
            1.9779984951 * l - 2.428592205 * m + 0.4505937099 * s,
            0.0259040371 * l + 0.7827717662 * m - 0.808675766 * s];
  }
  function oklabToRgb(L, a, b) {
    const l = (L + 0.3963377774 * a + 0.2158037573 * b) ** 3;
    const m = (L - 0.1055613458 * a - 0.0638541728 * b) ** 3;
    const s = (L - 0.0894841775 * a - 1.291485548 * b) ** 3;
    const channel = (v) => Math.round(255 * Math.min(1, Math.max(0, toGamma(Math.min(1, Math.max(0, v))))));
    return [channel(4.0767416621 * l - 3.3077115913 * m + 0.2309699292 * s),
            channel(-1.2684380046 * l + 2.6097574011 * m - 0.3413193965 * s),
            channel(-0.0041960863 * l - 0.7034186147 * m + 1.707614701 * s)];
  }

  /** 256 colors through evenly spaced stops, interpolated in OKLab. */
  function makeRamp(stops) {
    const lab = stops.map(hexToOklab);
    const rgb = new Uint8Array(256 * 3), packed = new Uint32Array(256);
    for (let i = 0; i < 256; i++) {
      const t = i / 255 * (stops.length - 1), j = Math.min(stops.length - 2, Math.floor(t)), u = t - j;
      const c = oklabToRgb(lab[j][0] + u * (lab[j + 1][0] - lab[j][0]),
                           lab[j][1] + u * (lab[j + 1][1] - lab[j][1]),
                           lab[j][2] + u * (lab[j + 1][2] - lab[j][2]));
      rgb.set(c, i * 3);
      packed[i] = (255 << 24) | (c[2] << 16) | (c[1] << 8) | c[0];      // little-endian RGBA
    }
    return {
      packed,
      css: `linear-gradient(to right, ${stops.join(', ')})`,
      /** CSS color at t in [0, 1]. */
      at: (t) => { const i = Math.round(255 * Math.min(1, Math.max(0, t))) * 3; return `rgb(${rgb[i]}, ${rgb[i + 1]}, ${rgb[i + 2]})`; },
    };
  }

  /**
   * Paint an nx x ny image on `canvas`: get(col, row) is the ramp position in [0, 1]
   * of the pixel in column `col` and in row `row` counted from the bottom.
   */
  Viz.paint = function (canvas, nx, ny, ramp, get) {
    if (canvas.width !== nx || canvas.height !== ny) { canvas.width = nx; canvas.height = ny; }
    const ctx = canvas.getContext('2d');
    const image = ctx.createImageData(nx, ny);
    const pixels = new Uint32Array(image.data.buffer);
    for (let row = 0; row < ny; row++) {
      const base = (ny - 1 - row) * nx;
      for (let col = 0; col < nx; col++) {
        const t = get(col, row);
        pixels[base + col] = ramp.packed[t <= 0 ? 0 : t >= 1 ? 255 : (t * 255 + 0.5) | 0];
      }
    }
    ctx.putImageData(image, 0, 0);
    return canvas;
  };

  // ---------------------------------------------------------------------------
  // Canvas, SVG, DOM
  // ---------------------------------------------------------------------------

  /** Size the backing store to the element (or to w x h CSS pixels) and return a cleared context in CSS pixels. */
  Viz.fitCanvas = function (canvas, w, h) {
    const dpr = Math.min(window.devicePixelRatio || 1, 3);
    if (w === undefined) { w = canvas.clientWidth; h = canvas.clientHeight; }
    else { canvas.style.width = w + 'px'; canvas.style.height = h + 'px'; }
    const pw = Math.max(1, Math.round(w * dpr)), ph = Math.max(1, Math.round(h * dpr));
    if (canvas.width !== pw || canvas.height !== ph) { canvas.width = pw; canvas.height = ph; }
    const ctx = canvas.getContext('2d');
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    ctx.clearRect(0, 0, w, h);
    return { ctx, w, h };
  };

  Viz.svg = function (tag, attrs, parent) {
    const el = document.createElementNS('http://www.w3.org/2000/svg', tag);
    for (const name in attrs) el.setAttribute(name, attrs[name]);
    if (parent) parent.appendChild(el);
    return el;
  };

  Viz.el = function (tag, props, parent) {
    const el = document.createElement(tag);
    if (props) {
      for (const name in props) {
        if (name === 'text') el.textContent = props[name];
        else if (name === 'class') el.className = props[name];
        else el.setAttribute(name, props[name]);
      }
    }
    if (parent) parent.appendChild(el);
    return el;
  };

  /** Typeset TeX into an element (the raw TeX stays readable if KaTeX is missing). */
  Viz.tex = function (el, source, display) {
    if (window.katex) window.katex.render(source, el, { throwOnError: false, displayMode: !!display });
    else el.textContent = source;
    return el;
  };

  // ---------------------------------------------------------------------------
  // Numbers
  // ---------------------------------------------------------------------------

  const SUPERSCRIPT = { '-': '⁻', 0: '⁰', 1: '¹', 2: '²', 3: '³', 4: '⁴', 5: '⁵', 6: '⁶', 7: '⁷', 8: '⁸', 9: '⁹' };
  Viz.superscript = (n) => String(n).split('').map((ch) => SUPERSCRIPT[ch]).join('');

  /** A number to `digits` significant digits: 0.0031, 12, 3.1×10⁻⁵, with a true minus sign. */
  Viz.fmt = function (v, digits) {
    if (!Number.isFinite(v)) return '–';
    if (v === 0) return '0';
    digits = digits || 2;
    const a = Math.abs(v), sign = v < 0 ? '−' : '';
    if (a >= 1e-3 && a < 1e6) return sign + String(Number(a.toPrecision(digits)));
    const [mantissa, exponent] = a.toExponential(digits - 1).split('e');
    return `${sign}${Number(mantissa)}×10${Viz.superscript(Number(exponent))}`;
  };

  /** Round tick values covering [lo, hi]. */
  Viz.ticks = function (lo, hi, count) {
    const span = hi - lo;
    if (!(span > 0)) return [lo];
    const raw = span / (count || 5), mag = 10 ** Math.floor(Math.log10(raw)), norm = raw / mag;
    const step = (norm < 1.5 ? 1 : norm < 3 ? 2 : norm < 7 ? 5 : 10) * mag;
    const out = [];
    for (let v = Math.ceil(lo / step - 1e-9) * step; v <= hi + step * 1e-9; v += step) out.push(Math.abs(v) < step * 1e-9 ? 0 : Number(v.toPrecision(12)));
    return out;
  };

  /** A whole number of any size (BigInt): 1,835,008 up to nine digits, then 2.2×10³⁰. */
  Viz.count = function (n) {
    const digits = n.toString();
    if (digits.length <= 9) return digits.replace(/\B(?=(\d{3})+$)/g, ',');
    const lead = Math.round(Number(digits.slice(0, 3)) / 10);        // two significant digits
    return lead === 100 ? `1×10${Viz.superscript(digits.length)}` : `${lead / 10}×10${Viz.superscript(digits.length - 1)}`;
  };

  /** Powers of ten covering [10^e0, 10^e1] as axis ticks, thinned to at most `most`. */
  Viz.decades = function (e0, e1, most) {
    const steps = [1, 2, 5, 10, 20, 50], every = steps.find((step) => (e1 - e0) / step <= (most || 6)) || 100;
    const ticks = [];
    for (let e = Math.ceil(e0 / every) * every; e <= e1; e += every) ticks.push({ value: 10 ** e, label: e === 0 ? '1' : '10' + Viz.superscript(e) });
    return ticks;
  };

  const FRACTIONS = { '1/2': '½', '1/4': '¼', '3/4': '¾', '1/8': '⅛', '3/8': '⅜', '5/8': '⅝', '7/8': '⅞' };
  /** A dyadic number in (0, 1) as a fraction: ½, ⅜, 5/16. */
  Viz.fraction = function (x) {
    let den = 1;
    while (x * den !== Math.round(x * den) && den < 4096) den *= 2;
    const text = `${Math.round(x * den)}/${den}`;
    return FRACTIONS[text] || text;
  };

  // ---------------------------------------------------------------------------
  // Tooltip
  // ---------------------------------------------------------------------------

  let tipEl = null;
  Viz.tip = {
    /** rows: [{ label, value, color? }]; text goes in as text, never as markup. */
    show(clientX, clientY, title, rows) {
      if (!tipEl) tipEl = Viz.el('div', { class: 'tooltip', role: 'status' }, document.body);
      tipEl.textContent = '';
      if (title) Viz.el('div', { class: 'tt-title', text: title }, tipEl);
      for (const row of rows) {
        const line = Viz.el('div', { class: 'tt-row' }, tipEl);
        const key = Viz.el('span', { class: 'tt-key' + (row.color ? '' : ' none') }, line);
        if (row.color) key.style.borderColor = row.color;
        Viz.el('span', { text: row.label }, line);
        Viz.el('b', { text: row.value }, line);
      }
      tipEl.hidden = false;
      const box = tipEl.getBoundingClientRect();
      let x = clientX + 14, y = clientY + 14;
      if (x + box.width > window.innerWidth - 8) x = clientX - 14 - box.width;
      if (y + box.height > window.innerHeight - 8) y = clientY - 14 - box.height;
      tipEl.style.left = Math.max(8, x) + 'px';
      tipEl.style.top = Math.max(8, y) + 'px';
    },
    hide() { if (tipEl) tipEl.hidden = true; },
  };
  // A tooltip belongs to what is under the pointer, which scrolling changes.
  window.addEventListener('scroll', () => Viz.tip.hide(), { passive: true });

  // ---------------------------------------------------------------------------
  // Line chart
  // ---------------------------------------------------------------------------

  /**
   * A line chart in SVG, redrawn in full by draw(spec):
   *
   *   spec = {
   *     x: [lo, hi], y: [lo, hi], xLog, yLog, xTicks: [{ value, label }], yTicks: [{ value, label }],
   *     xTitle, series: [{ color, points: [[x, y], ...], dots, endLabel }],
   *                                    (a non-finite y breaks the line; dots: true marks every
   *                                     point; endLabel is written above the last point)
   *     marker: { x, label, dots: [{ y, color }] }                  (optional: the current position)
   *     link: [[x, y], [x, y]], highlights: [{ x, y, color, label, below }]
   *   }                                (optional: points to single out, each with a label above
   *                                     or below it, and a hairline joining two of them)
   *
   * options.hover(xValue) returns { x, title, rows, dots } for the crosshair and the
   * tooltip (a dot sits on the crosshair unless it has its own x), and
   * options.pick(xValue) is called on click and drag.
   */
  Viz.lineChart = function (host, options) {
    const height = options.height || 240;
    const margin = Object.assign({ top: 12, right: 16, bottom: 38, left: 46 }, options.margin);
    const svg = Viz.svg('svg', { role: 'img', 'aria-label': options.label || 'Line chart' }, host);
    const clipId = 'clip-' + Math.random().toString(36).slice(2);
    let spec = null, width = 0, hoverLayer = null, dragging = false;

    const unit = (v, [lo, hi], log) => (log ? Math.log(v / lo) / Math.log(hi / lo) : (v - lo) / (hi - lo));
    const sx = (v) => margin.left + unit(v, spec.x, spec.xLog) * (width - margin.left - margin.right);
    const sy = (v) => height - margin.bottom - unit(v, spec.y, spec.yLog) * (height - margin.top - margin.bottom);
    const dot = (parent, x, y, color) => Viz.svg('circle', { class: 'dot', cx: x, cy: y, r: 4.5, fill: color }, parent);

    function draw(next) {
      if (next) spec = next;
      if (!spec) return;
      width = host.clientWidth;
      if (!width) return;
      svg.textContent = '';
      svg.setAttribute('width', width);
      svg.setAttribute('height', height);
      svg.setAttribute('viewBox', `0 0 ${width} ${height}`);
      const left = margin.left, right = width - margin.right, top = margin.top, bottom = height - margin.bottom;
      const defs = Viz.svg('defs', {}, svg);
      Viz.svg('rect', { x: left, y: top - 4, width: right - left, height: bottom - top + 8 }, Viz.svg('clipPath', { id: clipId }, defs));

      for (const tick of spec.yTicks) {
        const y = Math.round(sy(tick.value)) + 0.5;
        Viz.svg('line', { class: 'gridline', x1: left, x2: right, y1: y, y2: y }, svg);
        Viz.svg('text', { class: 'tick', x: left - 8, y: y + 4, 'text-anchor': 'end' }, svg).textContent = tick.label;
      }
      Viz.svg('line', { class: 'baseline', x1: left, x2: right, y1: bottom + 0.5, y2: bottom + 0.5 }, svg);
      for (const tick of spec.xTicks) {
        Viz.svg('text', { class: 'tick', x: sx(tick.value), y: bottom + 16, 'text-anchor': 'middle' }, svg).textContent = tick.label;
      }
      if (spec.xTitle) Viz.svg('text', { class: 'axis-title', x: (left + right) / 2, y: height - 4, 'text-anchor': 'middle' }, svg).textContent = spec.xTitle;

      const plot = Viz.svg('g', { 'clip-path': `url(#${clipId})` }, svg);
      for (const series of spec.series) {
        let d = '', pen = false;
        for (const [x, y] of series.points) {
          if (!Number.isFinite(y)) { pen = false; continue; }
          d += `${pen ? 'L' : 'M'}${sx(x).toFixed(1)},${sy(y).toFixed(1)}`;
          pen = true;
        }
        Viz.svg('path', { class: 'series', d, stroke: series.color }, plot);
        if (series.dots) {
          for (const [x, y] of series.points) {
            if (Number.isFinite(y)) Viz.svg('circle', { class: 'dot', cx: sx(x), cy: sy(y), r: 3.5, fill: series.color }, plot);
          }
        }
        if (series.endLabel) {
          const [x, y] = series.points[series.points.length - 1];
          Viz.svg('text', { class: 'end-label', x: sx(x), y: sy(y) - 8, 'text-anchor': 'end' }, svg).textContent = series.endLabel;
        }
      }
      if (spec.link) {
        const [[x1, y1], [x2, y2]] = spec.link;
        Viz.svg('line', { class: 'link', x1: sx(x1), y1: sy(y1), x2: sx(x2), y2: sy(y2) }, svg);
      }
      for (const point of spec.highlights || []) {
        if (!Number.isFinite(point.y)) continue;
        const px = sx(point.x), py = sy(point.y), flip = px > right - 90;
        Viz.svg('circle', { class: 'dot', cx: px, cy: py, r: 5.5, fill: point.color }, svg);
        if (point.label) {
          // beside a falling curve the free corners are the upper right and the lower left
          Viz.svg('text', { class: 'end-label', x: px + (flip ? -9 : 9), y: py + (point.below || flip ? 17 : -9), 'text-anchor': flip ? 'end' : 'start' }, svg).textContent = point.label;
        }
      }
      if (spec.marker) {
        const x = Math.round(sx(spec.marker.x)) + 0.5;
        Viz.svg('line', { class: 'marker-line', x1: x, x2: x, y1: top, y2: bottom }, svg);
        for (const d of spec.marker.dots || []) if (Number.isFinite(d.y)) dot(svg, x, sy(d.y), d.color);
        if (spec.marker.label) {
          const flip = x > right - 70;
          Viz.svg('text', { class: 'marker-label', x: x + (flip ? -7 : 7), y: top + 10, 'text-anchor': flip ? 'end' : 'start' }, svg).textContent = spec.marker.label;
        }
      }
      hoverLayer = Viz.svg('g', {}, svg);
      const hit = Viz.svg('rect', { x: left, y: top, width: right - left, height: bottom - top, fill: 'transparent' }, svg);
      if (options.pick) hit.style.cursor = 'ew-resize';
      attach(hit);
    }

    function valueAt(event) {
      const box = svg.getBoundingClientRect();
      const t = Math.min(1, Math.max(0, (event.clientX - box.left - margin.left) / (width - margin.left - margin.right)));
      return spec.xLog ? spec.x[0] * (spec.x[1] / spec.x[0]) ** t : spec.x[0] + t * (spec.x[1] - spec.x[0]);
    }

    function attach(hit) {
      hit.addEventListener('pointermove', (event) => {
        const v = valueAt(event);
        if (dragging && options.pick) { options.pick(v); return; }      // pick redraws; the next move hovers
        if (!options.hover) return;
        const info = options.hover(v);
        hoverLayer.textContent = '';
        if (!info) { Viz.tip.hide(); return; }
        const x = Math.round(sx(info.x)) + 0.5;
        Viz.svg('line', { class: 'cross', x1: x, x2: x, y1: margin.top, y2: height - margin.bottom }, hoverLayer);
        for (const d of info.dots || []) if (Number.isFinite(d.y)) dot(hoverLayer, d.x === undefined ? x : sx(d.x), sy(d.y), d.color);
        Viz.tip.show(event.clientX, event.clientY, info.title, info.rows);
      });
      hit.addEventListener('pointerleave', () => { hoverLayer.textContent = ''; Viz.tip.hide(); });
      if (options.pick) {
        hit.addEventListener('pointerdown', (event) => {
          dragging = true;
          Viz.tip.hide();
          options.pick(valueAt(event));
        });
      }
    }
    window.addEventListener('pointerup', () => { dragging = false; });

    return { draw };
  };

  window.Viz = Viz;
})();
