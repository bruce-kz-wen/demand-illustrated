/*
 * A small parser for functions of (delta, p) typed by the reader.
 *
 *   MathExpr.parse(text) -> { fn(delta, p), tex }   or throws MathExpr.ExprError
 *
 * The text is parsed into a tree and evaluated from the tree; nothing is passed to
 * eval. Accepts + - * / ^, parentheses, implied multiplication (2p, 3(delta - p)),
 * the names in FUNCTIONS and CONSTANTS below, and delta (or d, or the Greek letter)
 * and p as the two variables.
 */
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory();
  else root.MathExpr = factory();
})(typeof self !== 'undefined' ? self : this, function () {
  'use strict';

  class ExprError extends Error {
    constructor(message, position) {
      super(message);
      this.name = 'ExprError';
      this.position = position;
    }
  }

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

  // name -> [number of arguments (0 = one or more), function, TeX name]
  const FUNCTIONS = {
    exp: [1, Math.exp, '\\exp'],
    log: [1, Math.log, '\\ln'],
    ln: [1, Math.log, '\\ln'],
    log10: [1, Math.log10, '\\log_{10}'],
    log2: [1, Math.log2, '\\log_{2}'],
    sqrt: [1, Math.sqrt, null],
    abs: [1, Math.abs, null],
    sin: [1, Math.sin, '\\sin'],
    cos: [1, Math.cos, '\\cos'],
    tan: [1, Math.tan, '\\tan'],
    asin: [1, Math.asin, '\\arcsin'],
    acos: [1, Math.acos, '\\arccos'],
    atan: [1, Math.atan, '\\arctan'],
    sinh: [1, Math.sinh, '\\sinh'],
    cosh: [1, Math.cosh, '\\cosh'],
    tanh: [1, Math.tanh, '\\tanh'],
    floor: [1, Math.floor, '\\operatorname{floor}'],
    ceil: [1, Math.ceil, '\\operatorname{ceil}'],
    round: [1, Math.round, '\\operatorname{round}'],
    sign: [1, Math.sign, '\\operatorname{sign}'],
    min: [0, Math.min, '\\min'],
    max: [0, Math.max, '\\max'],
    pow: [2, Math.pow, null],
    logistic: [1, (x) => 1 / (1 + Math.exp(-x)), '\\Lambda'],
    sigmoid: [1, (x) => 1 / (1 + Math.exp(-x)), '\\Lambda'],
    normcdf: [1, (x) => 0.5 * (1 + erf(x / Math.SQRT2)), '\\Phi'],
    normpdf: [1, (x) => Math.exp(-0.5 * x * x) / Math.sqrt(2 * Math.PI), '\\varphi'],
    erf: [1, erf, '\\operatorname{erf}'],
    step: [1, (x) => (x >= 0 ? 1 : 0), null],
    pos: [1, (x) => (x > 0 ? x : 0), null],
  };
  const CONSTANTS = { pi: [Math.PI, '\\pi'], e: [Math.E, 'e'] };
  const VARIABLES = { delta: 0, d: 0, p: 1 };
  const SPLITTABLE = ['delta', 'pi', 'd', 'p', 'e'];   // "dp" reads as d times p

  // ---- tokens ----------------------------------------------------------------

  function tokenize(text) {
    const src = text
      .replace(/[−–]/g, '-')
      .replace(/[×·⋅]/g, '*')
      .replace(/÷/g, '/')
      .replace(/²/g, '^2')
      .replace(/³/g, '^3')
      .replace(/\*\*/g, '^ ');
    const tokens = [];
    const number = /^(?:\d+\.?\d*|\.\d+)(?:[eE][+-]?\d+)?/;
    const name = /^[A-Za-z_δΔπ][A-Za-z0-9_]*/;
    let i = 0;
    while (i < src.length) {
      const ch = src[i];
      if (/\s/.test(ch)) { i++; continue; }
      const rest = src.slice(i);
      let m = number.exec(rest);
      if (m) { tokens.push({ type: 'num', value: parseFloat(m[0]), pos: i }); i += m[0].length; continue; }
      m = name.exec(rest);
      if (m) {
        const word = m[0].toLowerCase().replace(/[δΔ]/g, 'delta').replace(/π/g, 'pi');
        tokens.push({ type: 'name', value: word, pos: i });
        i += m[0].length;
        continue;
      }
      if ('+-*/^(),'.includes(ch)) { tokens.push({ type: ch, pos: i }); i++; continue; }
      throw new ExprError(`"${ch}" is not something I can read here.`, i);
    }
    tokens.push({ type: 'end', pos: src.length });
    return tokens;
  }

  /** "dp" -> ["d", "p"] when the whole word is made of variable and constant names. */
  function splitName(word) {
    if (word === '') return [];
    for (const head of SPLITTABLE) {
      if (word.startsWith(head)) {
        const tail = splitName(word.slice(head.length));
        if (tail) return [head].concat(tail);
      }
    }
    return null;
  }

  // ---- parser ------------------------------------------------------------------
  //   sum     := product (('+' | '-') product)*
  //   product := unary (('*' | '/') unary | unary-without-sign)*
  //   unary   := ('+' | '-') unary | power
  //   power   := atom ('^' unary)?

  function parseTokens(tokens) {
    let at = 0;
    const peek = () => tokens[at];
    const take = () => tokens[at++];
    const expect = (type, what) => {
      if (peek().type !== type) throw new ExprError(`Expected ${what}.`, peek().pos);
      return take();
    };

    function sum() {
      let node = product();
      while (peek().type === '+' || peek().type === '-') {
        const op = take().type;
        node = { t: 'bin', op, a: node, b: product() };
      }
      return node;
    }

    function product() {
      let node = unary();
      for (;;) {
        const type = peek().type;
        if (type === '*' || type === '/') {
          take();
          node = { t: 'bin', op: type, a: node, b: unary() };
        } else if (type === 'num' || type === 'name' || type === '(') {
          node = { t: 'bin', op: '*', a: node, b: power() };
        } else {
          return node;
        }
      }
    }

    function unary() {
      if (peek().type === '-') { take(); return { t: 'neg', a: unary() }; }
      if (peek().type === '+') { take(); return unary(); }
      return power();
    }

    function power() {
      const base = atom();
      if (peek().type === '^') { take(); return { t: 'bin', op: '^', a: base, b: unary() }; }
      return base;
    }

    function named(word, pos) {
      if (Object.prototype.hasOwnProperty.call(VARIABLES, word)) return { t: 'var', i: VARIABLES[word] };
      if (Object.prototype.hasOwnProperty.call(CONSTANTS, word)) return { t: 'const', name: word };
      const parts = splitName(word);
      if (!parts) {
        throw new ExprError(`I don't know "${word}". The variables are delta (or d) and p.`, pos);
      }
      return parts.map((part) => named(part, pos)).reduce((a, b) => ({ t: 'bin', op: '*', a, b }));
    }

    function atom() {
      const token = take();
      if (token.type === 'num') return { t: 'num', v: token.value };
      if (token.type === '(') {
        const inner = sum();
        expect(')', 'a closing parenthesis');
        return { t: 'group', a: inner };
      }
      if (token.type === 'name') {
        const isFunction = Object.prototype.hasOwnProperty.call(FUNCTIONS, token.value);
        if (isFunction && peek().type === '(') {
          take();
          const args = [sum()];
          while (peek().type === ',') { take(); args.push(sum()); }
          expect(')', 'a closing parenthesis');
          const arity = FUNCTIONS[token.value][0];
          if (arity > 0 && args.length !== arity) {
            throw new ExprError(`${token.value}() takes ${arity} argument${arity > 1 ? 's' : ''}.`, token.pos);
          }
          return { t: 'call', name: token.value, args };
        }
        if (isFunction) throw new ExprError(`${token.value} needs parentheses: ${token.value}(...)`, token.pos);
        return named(token.value, token.pos);
      }
      if (token.type === 'end') throw new ExprError('The expression stops too early.', token.pos);
      throw new ExprError(`Unexpected "${token.type}".`, token.pos);
    }

    const tree = sum();
    if (peek().type !== 'end') {
      throw new ExprError(peek().type === ')' ? 'There is a closing parenthesis too many.' : 'I could not read past this point.', peek().pos);
    }
    return tree;
  }

  // ---- evaluation ----------------------------------------------------------------

  function compile(node) {
    switch (node.t) {
      case 'num': { const v = node.v; return () => v; }
      case 'const': { const v = CONSTANTS[node.name][0]; return () => v; }
      case 'var': return node.i === 0 ? (d) => d : (d, p) => p;
      case 'group': return compile(node.a);
      case 'neg': { const a = compile(node.a); return (d, p) => -a(d, p); }
      case 'bin': {
        const a = compile(node.a), b = compile(node.b);
        switch (node.op) {
          case '+': return (d, p) => a(d, p) + b(d, p);
          case '-': return (d, p) => a(d, p) - b(d, p);
          case '*': return (d, p) => a(d, p) * b(d, p);
          case '/': return (d, p) => a(d, p) / b(d, p);
          default: return (d, p) => Math.pow(a(d, p), b(d, p));
        }
      }
      default: {
        const fn = FUNCTIONS[node.name][1], args = node.args.map(compile);
        if (args.length === 1) { const a = args[0]; return (d, p) => fn(a(d, p)); }
        if (args.length === 2) { const a = args[0], b = args[1]; return (d, p) => fn(a(d, p), b(d, p)); }
        return (d, p) => fn.apply(null, args.map((g) => g(d, p)));
      }
    }
  }

  // ---- TeX -------------------------------------------------------------------------

  const strip = (node) => (node.t === 'group' ? strip(node.a) : node);
  const isSum = (node) => node.t === 'bin' && (node.op === '+' || node.op === '-');
  const paren = (s) => `\\left(${s}\\right)`;

  function numberTeX(v) {
    const s = String(v);
    const m = /^(.*)e([+-]?\d+)$/.exec(s);
    return m ? `${m[1]}\\times 10^{${Number(m[2])}}` : s;
  }

  function tex(node) {
    node = strip(node);
    switch (node.t) {
      case 'num': return numberTeX(node.v);
      case 'const': return CONSTANTS[node.name][1];
      case 'var': return node.i === 0 ? '\\delta' : 'p';
      case 'neg': {
        const a = strip(node.a);
        return '-' + (isSum(a) || a.t === 'neg' ? paren(tex(a)) : tex(a));
      }
      case 'bin': {
        const a = strip(node.a), b = strip(node.b);
        if (node.op === '+') return `${tex(a)} + ${b.t === 'neg' ? paren(tex(b)) : tex(b)}`;
        if (node.op === '-') return `${tex(a)} - ${isSum(b) || b.t === 'neg' ? paren(tex(b)) : tex(b)}`;
        if (node.op === '/') return `\\frac{${tex(a)}}{${tex(b)}}`;
        if (node.op === '*') {
          const left = isSum(a) || a.t === 'neg' ? paren(tex(a)) : tex(a);
          const right = isSum(b) || b.t === 'neg' ? paren(tex(b)) : tex(b);
          const leadsWithDigit = b.t === 'num' || (b.t === 'bin' && (b.op === '^' || b.op === '*') && strip(b.a).t === 'num');
          return leadsWithDigit ? `${left} \\cdot ${right}` : `${left}\\,${right}`;
        }
        const simple = a.t === 'var' || a.t === 'const' || (a.t === 'num' && a.v >= 0);
        return `{${simple ? tex(a) : paren(tex(a))}}^{${tex(b)}}`;
      }
      default: {
        const args = node.args.map(tex);
        switch (node.name) {
          case 'sqrt': return `\\sqrt{${args[0]}}`;
          case 'abs': return `\\left|${args[0]}\\right|`;
          case 'pow': return `{${paren(args[0])}}^{${args[1]}}`;
          case 'step': return `\\mathbf{1}\\!\\left\\{${args[0]} \\ge 0\\right\\}`;
          case 'pos': return `${paren(args[0])}_{+}`;
          default: return `${FUNCTIONS[node.name][2]}${paren(args.join(',\\,'))}`;
        }
      }
    }
  }

  function parse(text) {
    if (!text || !text.trim()) throw new ExprError('Type a function of delta and p.', 0);
    const tree = parseTokens(tokenize(text));
    return { fn: compile(tree), tex: tex(tree) };
  }

  return { parse, ExprError, functionNames: Object.keys(FUNCTIONS) };
});
