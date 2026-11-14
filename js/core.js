/*
 * The Matryoshka dictionary of Section 2.1 of the note: numerics only, no DOM.
 *
 *   buildChain(kappa, M)        the univariate chain psi_0, ..., psi_M on [0, 1]
 *   order(d, nMax, a, kappa)    the first nMax multi-indices, in the order of the estimator's code
 *   dictionary2D(options)       chain + order for two coordinates, cut at a whole resolution level
 *   projector(dictionary)       L2 projection of a function of two variables onto the dictionary
 *
 * Loads as a plain script (window.Matryoshka) and as a node module (tests/core.test.js).
 */
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.Matryoshka = factory();
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  // ---------------------------------------------------------------------------
  // Knots and weights
  // ---------------------------------------------------------------------------

  /** The first n dyadic knots in insertion order: 1/2, 1/4, 3/4, 1/8, 3/8, ... */
  function dyadicKnots(n) {
    const out = [];
    for (let den = 2; out.length < n; den *= 2) {
      for (let num = 1; num < den && out.length < n; num += 2) out.push(num / den);
    }
    return out;
  }

  /** Dyadic level of the i-th knot, i >= 1: 0 for 1/2, 1 for 1/4 and 3/4, 2 for the eighths, ... */
  function knotLevel(i) {
    let level = 0;
    while (2 ** (level + 1) <= i) level++;
    return level;
  }

  /** c_kappa(m): m up to the degree, then kappa + 2^level, the same for every knot of one level. */
  function resolutionWeight(m, kappa) {
    return m <= kappa ? m : kappa + 2 ** knotLevel(m - kappa);
  }

  // ---------------------------------------------------------------------------
  // Quadrature and Legendre polynomials
  // ---------------------------------------------------------------------------

  /** Gauss-Legendre nodes and weights on [-1, 1], exact for polynomials of degree 2n - 1. */
  function gaussLegendre(n) {
    const x = new Float64Array(n), w = new Float64Array(n);
    for (let i = 0; i < (n + 1) >> 1; i++) {
      let z = Math.cos(Math.PI * (i + 0.75) / (n + 0.5)), dp = 0;
      for (let iter = 0; iter < 100; iter++) {
        let p1 = 1, p2 = 0;
        for (let j = 0; j < n; j++) {
          const p3 = p2;
          p2 = p1;
          p1 = ((2 * j + 1) * z * p2 - j * p3) / (j + 1);
        }
        dp = n * (z * p1 - p2) / (z * z - 1);
        const step = p1 / dp;
        z -= step;
        if (Math.abs(step) < 1e-15) break;
      }
      x[i] = -z;
      x[n - 1 - i] = z;
      w[i] = w[n - 1 - i] = 2 / ((1 - z * z) * dp * dp);
    }
    return { x, w };
  }

  /** out[i] = P_i(t), i = 0..n, the Legendre polynomials on [-1, 1]. */
  function legendreValues(t, n, out) {
    out[0] = 1;
    if (n >= 1) out[1] = t;
    for (let i = 2; i <= n; i++) out[i] = ((2 * i - 1) * t * out[i - 1] - (i - 1) * out[i - 2]) / i;
    return out;
  }

  function dot(u, v) {
    let s = 0;
    for (let i = 0; i < u.length; i++) s += u[i] * v[i];
    return s;
  }

  // ---------------------------------------------------------------------------
  // The univariate chain
  // ---------------------------------------------------------------------------

  /**
   * psi_0, ..., psi_M, orthonormal in L2[0, 1], with span{psi_0..psi_m} = V_m:
   * the shifted Legendre polynomials up to degree kappa, then for each new knot tau
   * the truncated power (x - tau)_+^kappa minus its projection on the functions before
   * it, normalized.
   *
   * Every function is a polynomial of degree kappa on each cell of the finest dyadic
   * mesh, so it is stored by its coefficients in an orthonormal Legendre basis of
   * each cell. L2 inner products are then plain dot products, exact up to rounding.
   */
  function buildChain(kappa, M) {
    const nKnots = Math.max(M - kappa, 0);
    const knots = dyadicKnots(nKnots);
    const cells = nKnots > 0 ? 2 ** (knotLevel(nKnots) + 1) : 1;
    const P = kappa + 1, h = 1 / cells;
    const gl = gaussLegendre(P);
    const scale = new Float64Array(P);
    for (let i = 0; i < P; i++) scale[i] = Math.sqrt((2 * i + 1) / h);
    const E = [];                                   // E[q][i]: local basis function i at Gauss node q
    for (let q = 0; q < P; q++) {
      const row = legendreValues(gl.x[q], kappa, new Float64Array(P));
      for (let i = 0; i < P; i++) row[i] *= scale[i];
      E.push(row);
    }

    function localCoefficients(g) {
      const c = new Float64Array(cells * P);
      for (let j = 0; j < cells; j++) {
        for (let q = 0; q < P; q++) {
          const v = g((j + 0.5 * (gl.x[q] + 1)) * h) * gl.w[q] * 0.5 * h;
          if (v !== 0) for (let i = 0; i < P; i++) c[j * P + i] += v * E[q][i];
        }
      }
      return c;
    }

    const coef = [], info = [];
    const leg = new Float64Array(kappa + 1);
    for (let m = 0; m <= M; m++) {
      let v;
      if (m <= kappa) {
        const norm = Math.sqrt(2 * m + 1);
        v = localCoefficients((x) => norm * legendreValues(2 * x - 1, m, leg)[m]);
        info.push({ m, kind: 'poly', degree: m, weight: m, knots: [] });
      } else {
        const tau = knots[m - kappa - 1];
        v = localCoefficients((x) => (x > tau ? (x - tau) ** kappa : 0));
        for (let pass = 0; pass < 2; pass++) {      // Gram-Schmidt, twice for rounding
          for (let i = 0; i < m; i++) {
            const s = dot(v, coef[i]), ci = coef[i];
            for (let r = 0; r < v.length; r++) v[r] -= s * ci[r];
          }
        }
        const norm = Math.sqrt(dot(v, v));
        for (let r = 0; r < v.length; r++) v[r] /= norm;
        info.push({
          m, kind: 'spline', knot: tau, level: knotLevel(m - kappa),
          weight: resolutionWeight(m, kappa),
          knots: knots.slice(0, m - kappa).sort((p, q) => p - q),
        });
      }
      coef.push(v);
    }

    /** Values psi_m(xs[i]) for m = 0..mMax, as an array of Float64Array. */
    function evaluate(xs, mMax) {
      if (mMax === undefined) mMax = M;
      const out = [];
      for (let m = 0; m <= mMax; m++) out.push(new Float64Array(xs.length));
      const b = new Float64Array(P);
      for (let i = 0; i < xs.length; i++) {
        const x = Math.min(1, Math.max(0, xs[i]));
        const j = Math.min(cells - 1, Math.floor(x * cells));
        legendreValues(2 * (x * cells - j) - 1, kappa, b);
        for (let r = 0; r < P; r++) b[r] *= scale[r];
        for (let m = 0; m <= mMax; m++) {
          const c = coef[m];
          let s = 0;
          for (let r = 0; r < P; r++) s += c[j * P + r] * b[r];
          out[m][i] = s;
        }
      }
      return out;
    }

    return { kappa, M, cells, knots, coef, info, evaluate };
  }

  // ---------------------------------------------------------------------------
  // Python's random.Random(str), as far as the ordering needs it
  // ---------------------------------------------------------------------------

  /**
   * The tie-break of `chainets_order` draws from random.Random("0:balanced").randrange.
   * To give the same order as the estimator's code, this is the Mersenne Twister
   * with CPython's string seeding and its rejection sampling for randrange.
   */
  class PyRandom {
    constructor(key) {
      this.mt = new Uint32Array(624);
      this.index = 624;
      this.initByArray(key);
    }
    initGenrand(s) {
      const mt = this.mt;
      mt[0] = s >>> 0;
      for (let i = 1; i < 624; i++) {
        const x = mt[i - 1] ^ (mt[i - 1] >>> 30);
        mt[i] = (Math.imul(1812433253, x) + i) >>> 0;
      }
    }
    initByArray(key) {
      const mt = this.mt, N = 624;
      this.initGenrand(19650218);
      let i = 1, j = 0;
      for (let k = Math.max(N, key.length); k > 0; k--) {
        const x = mt[i - 1] ^ (mt[i - 1] >>> 30);
        mt[i] = ((mt[i] ^ Math.imul(x, 1664525)) + key[j] + j) >>> 0;
        i++; j++;
        if (i >= N) { mt[0] = mt[N - 1]; i = 1; }
        if (j >= key.length) j = 0;
      }
      for (let k = N - 1; k > 0; k--) {
        const x = mt[i - 1] ^ (mt[i - 1] >>> 30);
        mt[i] = ((mt[i] ^ Math.imul(x, 1566083941)) - i) >>> 0;
        i++;
        if (i >= N) { mt[0] = mt[N - 1]; i = 1; }
      }
      mt[0] = 0x80000000;
      this.index = N;
    }
    uint32() {
      const mt = this.mt, N = 624, M = 397;
      if (this.index >= N) {
        for (let k = 0; k < N; k++) {
          const y = (mt[k] & 0x80000000) | (mt[(k + 1) % N] & 0x7fffffff);
          mt[k] = mt[(k + M) % N] ^ (y >>> 1) ^ (y & 1 ? 0x9908b0df : 0);
        }
        this.index = 0;
      }
      let y = mt[this.index++];
      y ^= y >>> 11;
      y ^= (y << 7) & 0x9d2c5680;
      y ^= (y << 15) & 0xefc60000;
      y ^= y >>> 18;
      return y >>> 0;
    }
    /** random.randrange(n) for 0 < n < 2^32. */
    randbelow(n) {
      const shift = Math.clz32(n);                 // 32 - n.bit_length()
      let r = this.uint32() >>> shift;
      while (r >= n) r = this.uint32() >>> shift;
      return r;
    }
  }

  // random.seed(s) for a string hashes s to int.from_bytes(s + sha512(s)). The digest
  // below is sha512("0:balanced"), the seed string of chainets_order(seed=0).
  const SEED_TEXT = '0:balanced';
  const SEED_SHA512 = '697fcca07a6dcc00ee9fa02b9ae1827a64662b77ee88e2c15928daa74e984f99' +
                      '639924448ef36ee4db1b41a6094f21850dd4bab95a084e2da47cf06b655c769f';

  function seedKey() {
    const bytes = [];
    for (let i = 0; i < SEED_TEXT.length; i++) bytes.push(SEED_TEXT.charCodeAt(i));
    for (let i = 0; i < SEED_SHA512.length; i += 2) bytes.push(parseInt(SEED_SHA512.slice(i, i + 2), 16));
    const key = [];                                 // 32-bit words, least significant first
    for (let end = bytes.length; end > 0; end -= 4) {
      let word = 0;
      for (let i = Math.max(0, end - 4); i < end; i++) word = word * 256 + bytes[i];
      key.push(word);
    }
    return key;
  }

  // ---------------------------------------------------------------------------
  // The ordered multi-index dictionary
  // ---------------------------------------------------------------------------

  /** Weighted total resolution omega(k) = sum_c a_c c_kappa(k_c). */
  function omega(k, a, kappa) {
    let w = 0;
    for (let c = 0; c < k.length; c++) w += a[c] * resolutionWeight(k[c], kappa);
    return Math.round(w * 1e9) / 1e9;
  }

  function supportSize(k) {
    let s = 0;
    for (let c = 0; c < k.length; c++) if (k[c] > 0) s++;
    return s;
  }

  /** Every k in N^d with omega(k) <= L. */
  function enumerate(d, a, L, kappa) {
    const out = [], prefix = [];
    (function rec(c, budget) {
      if (c === d) { out.push(prefix.slice()); return; }
      for (let kc = 0; a[c] * resolutionWeight(kc, kappa) <= budget + 1e-9; kc++) {
        prefix.push(kc);
        rec(c + 1, budget - a[c] * resolutionWeight(kc, kappa));
        prefix.pop();
      }
    })(0, L);
    return out;
  }

  function lexCompare(k1, k2) {
    for (let c = 0; c < k1.length; c++) if (k1[c] !== k2[c]) return k1[c] - k2[c];
    return 0;
  }

  /**
   * The first nMax multi-indices of N^d by the key (omega(k), #supp(k), pi(k)). Inside
   * a tied group, the next index is one that minimizes the load sum_{c: k_c > 0} N_c
   * of the coordinates it uses, and remaining ties are drawn at random with a fixed
   * seed. A line-by-line port of `chainets_order` in chain.py (seed 0).
   */
  function order(d, nMax, a, kappa) {
    if (kappa === undefined) kappa = 3;
    let L = 0.5, ks = enumerate(d, a, L, kappa);
    while (ks.length < nMax) { L += 0.5; ks = enumerate(d, a, L, kappa); }
    const groups = new Map();
    for (const k of ks) {
      const w = omega(k, a, kappa), s = supportSize(k), id = w + '|' + s;
      if (!groups.has(id)) groups.set(id, { w, s, members: [] });
      groups.get(id).members.push(k);
    }
    const sorted = Array.from(groups.values()).sort((g1, g2) => g1.w - g2.w || g1.s - g2.s);
    const rng = new PyRandom(seedKey());
    const out = [];
    for (const group of sorted) {
      const members = group.members.sort(lexCompare), n = members.length;
      const counts = new Array(d).fill(0), alive = new Array(n).fill(true), load = new Array(n);
      for (let step = 0; step < n; step++) {
        let best = Infinity;
        for (let i = 0; i < n; i++) {
          if (!alive[i]) continue;
          let s = 0;
          for (let c = 0; c < d; c++) if (members[i][c] > 0) s += counts[c];
          load[i] = s;
          if (s < best) best = s;
        }
        const candidates = [];
        for (let i = 0; i < n; i++) if (alive[i] && load[i] === best) candidates.push(i);
        const pick = candidates.length > 1 ? candidates[rng.randbelow(candidates.length)] : candidates[0];
        alive[pick] = false;
        out.push({ k: members[pick], omega: group.w, support: group.s });
        for (let c = 0; c < d; c++) if (members[pick][c] > 0) counts[c]++;
      }
      if (out.length >= nMax) break;
    }
    return out.slice(0, nMax);
  }

  // ---------------------------------------------------------------------------
  // Sizes, in any number of coordinates
  // ---------------------------------------------------------------------------

  /**
   * |P^m| = #{k in N^d : sum_c a_c c_kappa(k_c) <= m}, with d = a.length, as a BigInt.
   * Counted one coordinate at a time over the budget in units of 1/2, so the weights
   * and m must be multiples of 1/2.
   */
  function prefixSize(a, m, kappa) {
    const budget = Math.round(2 * m);
    let ways = new Array(budget + 1).fill(0n);      // ways[b]: indices of total cost b / 2 so far
    ways[0] = 1n;
    for (const weight of a) {
      const next = new Array(budget + 1).fill(0n);
      for (let k = 0; ; k++) {
        const cost = 2 * weight * resolutionWeight(k, kappa), step = Math.round(cost);
        if (Math.abs(cost - step) > 1e-9) throw new Error('prefixSize: weights must be multiples of 1/2');
        if (step > budget) break;
        for (let b = step; b <= budget; b++) next[b] += ways[b - step];
      }
      ways = next;
    }
    return ways.reduce((sum, v) => sum + v, 0n);
  }

  /**
   * The full grid with the curves of P^m: every product of the curves that level m
   * reaches in each coordinate, prod_c #{k : a_c c_kappa(k) <= m}, as a BigInt.
   */
  function gridSize(a, m, kappa) {
    let size = 1n;
    for (const weight of a) {
      let curves = 0;
      while (weight * resolutionWeight(curves, kappa) <= m + 1e-9) curves++;
      size *= BigInt(curves);
    }
    return size;
  }

  // ---------------------------------------------------------------------------
  // Two coordinates
  // ---------------------------------------------------------------------------

  /**
   * The dictionary on (delta, p) with ordering weights a = [a_delta, a_p], cut at the
   * largest whole resolution index m whose prefix set P^m has at most nCap functions
   * and needs no knot finer than `maxKnotLevel`.
   *
   *   pieces[n] = { k: [k_delta, k_p], omega, support }   in order, n = 0..N-1
   *   levels[m] = |P^m|, m = 0..mMax, so levels[mMax] = N
   */
  function dictionary2D(options) {
    const kappa = options.kappa === undefined ? 3 : options.kappa;
    const a = options.a || [0.5, 1];
    const nCap = options.nCap || 170;
    const maxIndex = kappa + 2 ** ((options.maxKnotLevel === undefined ? 4 : options.maxKnotLevel) + 1) - 1;
    const levels = [];
    for (let m = 0; ; m++) {
      const ks = enumerate(2, a, m, kappa);
      const top = ks.reduce((mx, k) => Math.max(mx, k[0], k[1]), 0);
      if (m > 0 && (ks.length > nCap || top > maxIndex)) break;
      levels.push(ks.length);
    }
    const N = levels[levels.length - 1];
    const pieces = order(2, N, a, kappa);
    const K = [0, 0];
    for (const piece of pieces) {
      K[0] = Math.max(K[0], piece.k[0]);
      K[1] = Math.max(K[1], piece.k[1]);
    }
    const chain = buildChain(kappa, Math.max(K[0], K[1]));
    const index = new Map();
    pieces.forEach((piece, n) => index.set(piece.k[0] + ',' + piece.k[1], n));
    // The full grid with the same curves as the first n pieces: every product of
    // psi_0..psi_K1 in delta and psi_0..psi_K2 in p, where K1 and K2 are the finest
    // curves among those pieces. boxes lists the distinct grids in the order they
    // appear, and boxOf[n] is the one that goes with the first n pieces.
    const boxes = [], boxOf = [0];
    let k1 = 0, k2 = 0;
    pieces.forEach((piece, n) => {
      k1 = Math.max(k1, piece.k[0]);
      k2 = Math.max(k2, piece.k[1]);
      const last = boxes[boxes.length - 1];
      if (!last || last.k[0] !== k1 || last.k[1] !== k2) boxes.push({ k: [k1, k2], size: (k1 + 1) * (k2 + 1), first: n + 1 });
      boxOf.push(boxes.length - 1);
    });
    return {
      kappa, a, N, levels, pieces, chain, K, boxes, boxOf,
      /** Position of (k_delta, k_p) in the order, or -1 if it is not in the dictionary. */
      indexOf: (k1, k2) => (index.has(k1 + ',' + k2) ? index.get(k1 + ',' + k2) : -1),
      /** m_N: the largest whole m with |P^m| <= n. */
      completeLevel: (n) => { let m = -1; while (m + 1 < levels.length && levels[m + 1] <= n) m++; return m; },
    };
  }

  /**
   * L2([0,1]^2) projection onto the dictionary. The pieces are orthonormal, so the
   * coefficient of a piece is its inner product with f and does not depend on which
   * other pieces are in the sum.
   *
   *   project(f) -> { theta[n], rms[n], sup[n], boxRms[b], ... }, where rms[n] and sup[n]
   *   are the L2 and the largest absolute error of the sum of the first n pieces,
   *   n = 0..N, and boxRms[b] is the L2 error of the full grid dictionary.boxes[b].
   */
  function projector(dictionary, nodesPerCell) {
    const { chain, pieces, N, K, boxes } = dictionary;
    const nq = nodesPerCell || 6;
    const gl = gaussLegendre(nq);
    const cells = Math.max(chain.cells, 8);
    const Q = cells * nq;
    const x = new Float64Array(Q), w = new Float64Array(Q);
    for (let j = 0; j < cells; j++) {
      for (let q = 0; q < nq; q++) {
        x[j * nq + q] = (j + 0.5 * (gl.x[q] + 1)) / cells;
        w[j * nq + q] = 0.5 * gl.w[q] / cells;
      }
    }
    const psi = chain.evaluate(x);                  // psi[m][i]

    function project(f) {
      const F = new Float64Array(Q * Q);            // F[i * Q + j] = f(x_i, x_j)
      let bad = null, fmin = Infinity, fmax = -Infinity, mean = 0, norm2 = 0;
      for (let i = 0; i < Q; i++) {
        for (let j = 0; j < Q; j++) {
          const v = f(x[i], x[j]);
          if (!Number.isFinite(v)) { if (!bad) bad = { delta: x[i], p: x[j], value: v }; continue; }
          F[i * Q + j] = v;
          if (v < fmin) fmin = v;
          if (v > fmax) fmax = v;
          mean += w[i] * w[j] * v;
          norm2 += w[i] * w[j] * v * v;
        }
      }
      if (bad) return { error: bad };

      // T[k2][i] = integral over p of f(x_i, p) psi_k2(p)
      const T = [];
      for (let k2 = 0; k2 <= K[1]; k2++) {
        const row = new Float64Array(Q), b = psi[k2];
        for (let i = 0; i < Q; i++) {
          let s = 0;
          for (let j = 0; j < Q; j++) s += F[i * Q + j] * w[j] * b[j];
          row[i] = s;
        }
        T.push(row);
      }
      // grid[k1 * C2 + k2]: the coefficient of every product of the curves in the dictionary
      const C1 = K[0] + 1, C2 = K[1] + 1;
      const grid = new Float64Array(C1 * C2);
      for (let k1 = 0; k1 < C1; k1++) {
        const a1 = psi[k1];
        for (let k2 = 0; k2 < C2; k2++) {
          const row = T[k2];
          let s = 0;
          for (let i = 0; i < Q; i++) s += w[i] * a1[i] * row[i];
          grid[k1 * C2 + k2] = s;
        }
      }
      const theta = new Float64Array(N);
      for (let n = 0; n < N; n++) theta[n] = grid[pieces[n].k[0] * C2 + pieces[n].k[1]];

      // Error of a full grid: by orthogonality, the squared error of the largest grid
      // (measured on its residual) plus the squares of the coefficients left out.
      let largest2 = 0;
      const partial = new Float64Array(C2);
      for (let i = 0; i < Q; i++) {
        for (let k2 = 0; k2 < C2; k2++) {
          let s = 0;
          for (let k1 = 0; k1 < C1; k1++) s += psi[k1][i] * grid[k1 * C2 + k2];
          partial[k2] = s;
        }
        let row = 0;
        for (let j = 0; j < Q; j++) {
          let r = F[i * Q + j];
          for (let k2 = 0; k2 < C2; k2++) r -= partial[k2] * psi[k2][j];
          row += w[j] * r * r;
        }
        largest2 += w[i] * row;
      }
      const boxRms = boxes.map((box) => {
        let left = 0;
        for (let k1 = 0; k1 < C1; k1++) {
          for (let k2 = 0; k2 < C2; k2++) if (k1 > box.k[0] || k2 > box.k[1]) left += grid[k1 * C2 + k2] ** 2;
        }
        return Math.sqrt(largest2 + left);
      });

      // Errors after each piece, on the residual itself (not by Parseval, which
      // loses digits once the error is far below the size of f).
      const rms = new Float64Array(N + 1), sup = new Float64Array(N + 1);
      const R = F;                                  // overwritten: F is not needed again
      const measure = (n) => {
        let s2 = 0, mx = 0;
        for (let i = 0; i < Q; i++) {
          let row = 0;
          for (let j = 0; j < Q; j++) {
            const r = R[i * Q + j];
            row += w[j] * r * r;
            if (r > mx) mx = r; else if (-r > mx) mx = -r;
          }
          s2 += w[i] * row;
        }
        rms[n] = Math.sqrt(s2);
        sup[n] = mx;
      };
      measure(0);
      for (let n = 0; n < N; n++) {
        const a1 = psi[pieces[n].k[0]], b1 = psi[pieces[n].k[1]], t = theta[n];
        if (t !== 0) {
          for (let i = 0; i < Q; i++) {
            const ti = t * a1[i];
            for (let j = 0; j < Q; j++) R[i * Q + j] -= ti * b1[j];
          }
        }
        measure(n + 1);
      }
      return { theta, rms, sup, boxRms, fmin, fmax, mean, norm: Math.sqrt(norm2) };
    }

    return { project, nodes: x, weights: w };
  }

  // ---------------------------------------------------------------------------
  // A demand system with any number of products
  // ---------------------------------------------------------------------------

  function erf(x) {
    const ax = Math.abs(x);
    if (ax >= 6) return Math.sign(x);
    let term = ax, sum = ax;
    for (let n = 1; n < 400; n++) {
      term *= 2 * ax * ax / (2 * n + 1);
      sum += term;
      if (term < 1e-17 * sum) break;
    }
    return Math.sign(x) * 2 / Math.sqrt(Math.PI) * Math.exp(-ax * ax) * sum;
  }

  /**
   * Taste shocks: scale * e with e drawn from `cdf` (density `pdf`). `lower` and `upper`
   * are where the density of e stops mattering, and `step` is a mesh in e fine enough for
   * the trapezoid rule below with fifty products (probit: the error of a share is below
   * 1e-9 of it at step 1/4, and at rounding at 1/6).
   *
   *   probit   standard normal shocks scaled to the variance of the logit's, pi^2 / 6,
   *            as in the probit design of the note (dgp_errors.py, kind "probit")
   *   logit    extreme value shocks: the shares have a closed form, which the tests use
   */
  const SHOCKS = {
    probit: {
      cdf: (x) => 0.5 * (1 + erf(x / Math.SQRT2)),
      pdf: (x) => Math.exp(-0.5 * x * x) / Math.sqrt(2 * Math.PI),
      scale: Math.PI / Math.sqrt(6), lower: -8.5, upper: 8.5, step: 0.2,
    },
    logit: {
      cdf: (x) => Math.exp(-Math.exp(-x)),
      pdf: (x) => Math.exp(-x - Math.exp(-x)),
      scale: 1, lower: -4.5, upper: 38, step: 0.3,
    },
  };

  /**
   * The share of product 1 among J products and an outside good when tastes are
   * independent shocks: a consumer of some type gets v(delta_j, p_j) + scale * e_j from
   * product j and scale * e_0 from the outside good, and takes the best. With t the
   * utility of product 1,
   *
   *   f(delta_1, p_1, ..., delta_J, p_J)
   *     = sum_types share * int pdf_s(t - v_1) cdf_s(t) prod_{j >= 2} cdf_s(t - v_j) dt,     v_j = v(delta_j, p_j),
   *
   * where pdf_s and cdf_s are those of scale * e. Every input is in [0, 1]. The function
   * returns the L2 error of approximating f by the prefix sets P^m of the dictionary and
   * by the full grids with the same curves, for ANY J.
   *
   * With 2J inputs the integrals cannot be taken on a grid of points. They can be taken
   * because, for each t, the integrand is a product of functions of one product's
   * (delta, p) each. On a mesh in t (the trapezoid rule, which converges geometrically
   * for these integrands) f is a sum over S nodes of such products. A squared norm is
   * then a sum over pairs of nodes of a two-dimensional inner product for product 1
   * times the (J - 1)-th power of one for a rival, and J enters only through that power:
   *
   *   full grid    the inner product of the projections on a rectangle of curves;
   *   prefix set   the same, with the pieces of both products collected by cost, the
   *                costs added as a product of polynomials, and the sum cut at the budget.
   *
   *   options  = { types: [{ share, utility(delta, p) }], shocks: SHOCKS.probit, a: [a_delta, a_p], kappa, maxLevel }
   *   at(J)    = { constant, levels: [{ level, ours, grid }] }   for the levels 0, 1/2, 1, ..., maxLevel,
   *              where ours and grid are the two RMS errors and constant is that of the best constant
   *   share(z) = f at z = [[delta_1, p_1], ..., [delta_J, p_J]], from the same nodes in t
   *
   * The ordering weights are a on the index and price of product 1, and 1 on every rival's.
   */
  function demandSystem(options) {
    const kappa = options.kappa === undefined ? 3 : options.kappa;
    const a = options.a || [0.5, 1];
    const types = options.types, shocks = options.shocks || SHOCKS.probit;
    const budget = Math.round(2 * (options.maxLevel === undefined ? 4 : options.maxLevel));   // in units of 1/2
    const cost = (weight, k) => Math.round(2 * weight * resolutionWeight(k, kappa));
    const finest = (weight) => { let k = 0; while (cost(weight, k + 1) <= budget) k++; return k; };
    const own = [finest(a[0]) + 1, finest(a[1]) + 1], rival = finest(1) + 1;        // curves kept per coordinate
    const chain = buildChain(kappa, Math.max(own[0], own[1], rival) - 1);

    // Nodes in (delta, p): Gauss-Legendre on the cells of the chain, or finer.
    const cells = Math.max(chain.cells, 8), nq = 4, gl = gaussLegendre(nq), Q = cells * nq;
    const x = new Float64Array(Q), w = new Float64Array(Q);
    for (let j = 0; j < cells; j++) {
      for (let q = 0; q < nq; q++) {
        x[j * nq + q] = (j + 0.5 * (gl.x[q] + 1)) / cells;
        w[j * nq + q] = 0.5 * gl.w[q] / cells;
      }
    }
    const psi = chain.evaluate(x);

    /** c[k1 * n2 + k2] = integral of values(delta, p) psi_k1(delta) psi_k2(p), values on the Q x Q nodes. */
    function coefficients(values, n1, n2) {
      const out = new Float64Array(n1 * n2), inner = new Float64Array(Q);
      for (let k2 = 0; k2 < n2; k2++) {
        const b = psi[k2];
        for (let i = 0; i < Q; i++) {
          let sum = 0;
          for (let j = 0; j < Q; j++) sum += w[j] * b[j] * values[i * Q + j];
          inner[i] = sum;
        }
        for (let k1 = 0; k1 < n1; k1++) {
          const c = psi[k1];
          let sum = 0;
          for (let i = 0; i < Q; i++) sum += w[i] * c[i] * inner[i];
          out[k1 * n2 + k2] = sum;
        }
      }
      return out;
    }

    // Nodes in t, for every type: a uniform mesh over the utilities product 1 can reach.
    // Each node carries its weight (with the factor of the outside good), the factor of
    // product 1 and the factor of a rival on the (delta, p) nodes, scaled by the square
    // roots of the weights there so that inner products are dot products, and the
    // coefficients of the two factors. Nodes that cannot matter are left out.
    const { cdf, pdf, scale } = shocks, step = scale * shocks.step;
    const root = new Float64Array(Q * Q);
    for (let i = 0; i < Q; i++) for (let j = 0; j < Q; j++) root[i * Q + j] = Math.sqrt(w[i] * w[j]);
    const mesh = [];
    for (const type of types) {
      const v = new Float64Array(Q * Q);
      const corners = [type.utility(0, 0), type.utility(0, 1), type.utility(1, 0), type.utility(1, 1)];
      let low = Math.min(...corners), high = Math.max(...corners);
      for (let i = 0; i < Q; i++) {
        for (let j = 0; j < Q; j++) {
          v[i * Q + j] = type.utility(x[i], x[j]);
          low = Math.min(low, v[i * Q + j]);
          high = Math.max(high, v[i * Q + j]);
        }
      }
      for (let t = low + scale * shocks.lower; t <= high + scale * shocks.upper; t += step) {
        mesh.push({ type, v, t, weight: type.share * step * cdf(t / scale) });
      }
    }
    let largest = 0;
    for (const node of mesh) {
      const g = new Float64Array(Q * Q);
      let peak = 0;
      for (let i = 0; i < Q * Q; i++) { g[i] = pdf((node.t - node.v[i]) / scale) / scale; if (g[i] > peak) peak = g[i]; }
      node.g = g;
      node.size = node.weight * peak;
      largest = Math.max(largest, node.size);
    }
    const nodes = mesh.filter((node) => node.size > 1e-15 * largest);
    for (const node of nodes) {
      const h = new Float64Array(Q * Q), g = node.g;
      for (let i = 0; i < Q * Q; i++) h[i] = cdf((node.t - node.v[i]) / scale);
      node.o = coefficients(g, own[0], own[1]);
      node.r = coefficients(h, rival, rival);
      for (let i = 0; i < Q * Q; i++) { h[i] *= root[i]; g[i] *= root[i]; }
      node.h = h;
    }

    // For each pair of nodes: the weight, the two full inner products, and the inner
    // products of the coefficients collected by cost. "sum" collects a piece under the
    // sum of the costs of its two curves (the prefix sets), "max" under the larger of
    // the two (a piece is in the rectangle of level b when both costs are at most b).
    const ownSum = [], ownMax = [], rivalSum = [], rivalMax = [];
    for (let k1 = 0; k1 < own[0]; k1++) {
      for (let k2 = 0; k2 < own[1]; k2++) { ownSum.push(cost(a[0], k1) + cost(a[1], k2)); ownMax.push(Math.max(cost(a[0], k1), cost(a[1], k2))); }
    }
    for (let k1 = 0; k1 < rival; k1++) {
      for (let k2 = 0; k2 < rival; k2++) { rivalSum.push(cost(1, k1) + cost(1, k2)); rivalMax.push(Math.max(cost(1, k1), cost(1, k2))); }
    }
    const S = nodes.length, pairs = S * (S + 1) / 2, L = budget + 1;
    const pairWeight = new Float64Array(pairs), normOwn = new Float64Array(pairs), normRival = new Float64Array(pairs);
    const oSum = new Float64Array(pairs * L), oMax = new Float64Array(pairs * L), rSum = new Float64Array(pairs * L), rMax = new Float64Array(pairs * L);
    for (let s = 0, pair = 0; s < S; s++) {
      for (let s2 = s; s2 < S; s2++, pair++) {
        const A = nodes[s], B = nodes[s2];
        pairWeight[pair] = A.weight * B.weight * (s === s2 ? 1 : 2);
        normOwn[pair] = dot(A.g, B.g);
        normRival[pair] = dot(A.h, B.h);
        for (let i = 0; i < A.o.length; i++) {
          const v = A.o[i] * B.o[i];
          if (ownSum[i] <= budget) oSum[pair * L + ownSum[i]] += v;
          oMax[pair * L + ownMax[i]] += v;
        }
        for (let i = 0; i < A.r.length; i++) {
          const v = A.r[i] * B.r[i];
          if (rivalSum[i] <= budget) rSum[pair * L + rivalSum[i]] += v;
          rMax[pair * L + rivalMax[i]] += v;
        }
      }
    }

    const power = (v, n) => { let out = 1; for (; n > 0; n >>= 1, v *= v) if (n & 1) out *= v; return out; };
    /** out = p * q as polynomials in the cost, cut at the budget. */
    function multiply(p, q, out) {
      out.fill(0);
      for (let i = 0; i < L; i++) {
        if (p[i] === 0) continue;
        for (let j = 0; i + j < L; j++) out[i + j] += p[i] * q[j];
      }
    }

    function at(J) {
      let norm2 = 0;
      const ours = new Float64Array(L), grid = new Float64Array(L);
      let acc = new Float64Array(L), base = new Float64Array(L), next = new Float64Array(L);
      for (let pair = 0; pair < pairs; pair++) {
        const weight = pairWeight[pair], at0 = pair * L;
        norm2 += weight * normOwn[pair] * power(normRival[pair], J - 1);
        // rectangle of level b: both factors are running sums over the larger cost
        let o = 0, r = 0;
        for (let b = 0; b < L; b++) {
          o += oMax[at0 + b];
          r += rMax[at0 + b];
          grid[b] += weight * o * power(r, J - 1);
        }
        // prefix set of level b: (own polynomial) * (rival polynomial)^(J - 1), summed up to degree b
        acc.fill(0);
        acc[0] = 1;
        for (let b = 0; b < L; b++) base[b] = rSum[at0 + b];
        for (let n = J - 1; n > 0; n >>= 1) {
          if (n & 1) { multiply(acc, base, next); [acc, next] = [next, acc]; }
          if (n > 1) { multiply(base, base, next); [base, next] = [next, base]; }
        }
        multiply(acc, oSum.subarray(at0, at0 + L), next);
        let running = 0;
        for (let b = 0; b < L; b++) { running += next[b]; ours[b] += weight * running; }
      }
      const rms = (energy) => Math.sqrt(Math.max(0, norm2 - energy));
      const levels = [];
      for (let b = 0; b < L; b++) levels.push({ level: b / 2, ours: rms(ours[b]), grid: rms(grid[b]) });
      return { norm: Math.sqrt(norm2), constant: rms(ours[0]), levels };
    }

    function share(z) {
      let sum = 0;
      for (const node of nodes) {
        let term = node.weight * pdf((node.t - node.type.utility(z[0][0], z[0][1])) / scale) / scale;
        for (let j = 1; j < z.length && term !== 0; j++) term *= cdf((node.t - node.type.utility(z[j][0], z[j][1])) / scale);
        sum += term;
      }
      return sum;
    }

    return { at, share, maxLevel: budget / 2, nodes: nodes.length };
  }

  return {
    dyadicKnots, knotLevel, resolutionWeight, gaussLegendre, buildChain,
    omega, enumerate, order, prefixSize, gridSize, dictionary2D, projector, demandSystem, SHOCKS,
  };
});
