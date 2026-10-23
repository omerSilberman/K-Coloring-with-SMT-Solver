// Turns cvc5's SMT-LIB terms into readable math (HTML).
//   (set.member node_1 (set.insert 0 1 (as set.empty (Set Int))))   ->   node₁ ∈ {0, 1}
// parse() builds a tree of strings and arrays, render() returns {html, prec}:
// prec is the binding strength of the outermost operator, used to add parentheses.
"use strict";

const Pretty = (() => {
  // ---- parsing ------------------------------------------------------------
  function tokenize(text) {
    const tokens = [];
    let i = 0;
    while (i < text.length) {
      const c = text[i];
      if (c === "(" || c === ")") { tokens.push(c); i++; }
      else if (/\s/.test(c)) { i++; }
      else if (c === '"') {                       // string literal, "" escapes a quote
        let j = i + 1;
        while (j < text.length && !(text[j] === '"' && text[j + 1] !== '"')) j += text[j] === '"' ? 2 : 1;
        tokens.push(text.slice(i, j + 1)); i = j + 1;
      } else if (c === "|") {                     // |quoted symbol|
        const j = text.indexOf("|", i + 1);
        tokens.push(text.slice(i, j + 1)); i = j + 1;
      } else {
        let j = i;
        while (j < text.length && !/[\s()]/.test(text[j])) j++;
        tokens.push(text.slice(i, j)); i = j;
      }
    }
    return tokens;
  }

  function parse(text) {
    const tokens = tokenize(text);
    let pos = 0;
    function read() {
      if (pos >= tokens.length) throw new Error("unexpected end");
      const t = tokens[pos++];
      if (t === ")") throw new Error("unexpected )");
      if (t !== "(") return t;
      const list = [];
      while (tokens[pos] !== ")") {
        if (pos >= tokens.length) throw new Error("missing )");
        list.push(read());
      }
      pos++;
      return list;
    }
    const tree = read();
    if (pos !== tokens.length) throw new Error("trailing input");
    return tree;
  }

  // (let ((_let_1 e1) ...) body) -> body with the bindings substituted
  function expandLets(t, env = {}) {
    if (typeof t === "string") return t in env ? env[t] : t;
    if (t[0] === "let" && Array.isArray(t[1])) {
      const inner = { ...env };
      for (const [name, value] of t[1]) inner[name] = expandLets(value, inner);
      return expandLets(t[2], inner);
    }
    return t.map(x => expandLets(x, env));
  }

  // ---- rendering helpers --------------------------------------------------
  const ATOM = 9;
  const esc = s => s.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
  const span = (cls, html) => `<span class="${cls}">${html}</span>`;
  const op = s => span("op", s);
  const atom = html => ({ html, prec: ATOM });
  // Parenthesize r inside an operator of strength min. Two different operators of the
  // same strength (E ⋈ C ∩ C) get parentheses too, so the reader never has to know the rule.
  const paren = (r, min, parent) => (r.prec < min || (parent && r.op && r.op !== parent.op && r.prec === parent.prec)
    ? `<span class="paren">(</span>${r.html}<span class="paren">)</span>` : r.html);

  function symbol(name) {
    // node_12 -> node₁₂ (as a subscript), A_2_1 -> A₂,₁, @Elem_5 -> Elem₅
    const clean = name.replace(/^\|(.*)\|$/, "$1").replace(/^@/, "");
    const m = clean.match(/^([A-Za-z][A-Za-z]*)_(\d+(?:_\d+)*)$/);
    if (m) return atom(span("v", esc(m[1]) + `<sub>${m[2].replace(/_/g, ",")}</sub>`));
    return atom(span("v", esc(clean)));
  }

  function literal(t) {
    if (/^-?\d+(\.\d+)?$/.test(t)) return atom(span("n", t.replace(/\.0+$/, "")));
    if (/^#b[01]+$/.test(t)) {
      const bits = t.slice(2);
      if (bits.length <= 8) return atom(span("n", bits + "<sub>2</sub>"));
      return atom(span("n", BigInt("0b" + bits).toString() + `<sub>bv${bits.length}</sub>`));
    }
    if (/^#x[0-9a-fA-F]+$/.test(t)) return atom(span("n", BigInt("0x" + t.slice(2)).toString() + `<sub>bv${4 * (t.length - 2)}</sub>`));
    let m = t.match(/^#f(\d+)m(\d+)$/);
    if (m) return atom(span("n", m[1] + `<sub>𝔽${m[2]}</sub>`));
    if (t.startsWith('"')) {
      const body = t.slice(1, -1).replace(/""/g, '"');
      return atom(body === "" ? span("s", "ε") : span("s", "“" + esc(body) + "”"));
    }
    if (t === "real.pi") return atom(span("n", "π"));
    if (t === "true" || t === "false") return atom(span("kw", t));
    if (t === "sep.emp") return atom(span("kw", "emp"));
    return symbol(t);
  }

  function floatValue(sign, exp, frac) {
    // (fp #b0 #b01111111 #b000...) -> its decimal value
    const s = sign.slice(2), e = exp.slice(2), f = frac.slice(2);
    const bias = 2 ** (e.length - 1) - 1, ev = parseInt(e, 2), fv = parseInt(f, 2) / 2 ** f.length;
    let v;
    if (ev === 2 ** e.length - 1) v = fv ? NaN : Infinity;
    else v = ev === 0 ? fv * 2 ** (1 - bias) : (1 + fv) * 2 ** (ev - bias);
    if (s === "1") v = -v;
    const text = Number.isFinite(v) ? String(Number(v.toPrecision(10))) : String(v);
    return atom(span("n", text + `<sub>fp</sub>`));
  }

  const call = (name, args) => atom(span("kw", esc(name)) + `<span class="paren">(</span>`
    + args.map(a => a.html).join(", ") + `<span class="paren">)</span>`);

  // n-ary infix operators: [symbol, precedence, associative]
  const INFIX = {
    "=>": ["⇒", 1, false], "or": ["∨", 2, true], "and": ["∧", 3, true], "sep": ["∗", 3, true],
    "=": ["=", 5, false], "fp.eq": ["=", 5, false], "<": ["&lt;", 5], "<=": ["≤", 5], ">": ["&gt;", 5], ">=": ["≥", 5],
    "bvult": ["&lt;<sub>u</sub>", 5], "bvule": ["≤<sub>u</sub>", 5], "bvugt": ["&gt;<sub>u</sub>", 5], "bvuge": ["≥<sub>u</sub>", 5],
    "bvslt": ["&lt;<sub>s</sub>", 5], "bvsle": ["≤<sub>s</sub>", 5], "bvsgt": ["&gt;<sub>s</sub>", 5], "bvsge": ["≥<sub>s</sub>", 5],
    "fp.lt": ["&lt;", 5], "fp.leq": ["≤", 5], "fp.gt": ["&gt;", 5], "fp.geq": ["≥", 5],
    "str.<": ["&lt;<sub>lex</sub>", 5], "str.<=": ["≤<sub>lex</sub>", 5],
    "set.member": ["∈", 5], "set.subset": ["⊆", 5], "str.in_re": ["∈", 5], "pto": ["↦", 5],
    "+": ["+", 6, true], "-": ["−", 6], "bvadd": ["+", 6, true], "bvsub": ["−", 6], "ff.add": ["+", 6, true],
    "set.union": ["∪", 6, true], "set.minus": ["∖", 6], "re.union": ["|", 6, true], "bvor": ["|", 6, true], "bvxor": ["⊕", 6, true],
    "*": ["·", 7, true], "bvmul": ["·", 7, true], "ff.mul": ["·", 7, true], "/": ["/", 7], "div": ["div", 7], "mod": ["mod", 7],
    "bvurem": ["mod", 7], "bvudiv": ["÷", 7], "bvand": ["&amp;", 7, true], "set.inter": ["∩", 7, true],
    "rel.product": ["×", 7], "rel.join": ["⋈", 7], "str.++": ["·", 7, true], "re.++": ["·", 7, true], "concat": ["∘", 7, true],
    "bvshl": ["≪", 7], "bvlshr": ["≫", 7], "wand": ["−∗", 2],
  };
  const NEGATED = { "=": "≠", "fp.eq": "≠", "set.member": "∉", "set.subset": "⊈", "str.in_re": "∉" };
  const isEmptySet = t => Array.isArray(t) && t[0] === "as" && t[1] === "set.empty";
  // The members of a literal set ({a}, {a, b}, ∅), or null if t is not one
  function literalMembers(t) {
    if (isEmptySet(t)) return [];
    if (!Array.isArray(t)) return null;
    if (t[0] === "set.singleton") return [t[1]];
    if (t[0] === "set.insert" && isEmptySet(t[t.length - 1])) return t.slice(1, -1);
    if (t[0] === "set.union") {
      const parts = t.slice(1).map(literalMembers);
      return parts.every(p => p) ? parts.flat() : null;
    }
    return null;
  }
  // Sort members the way a reader expects: numbers numerically, everything else by its text
  function sortMembers(members) {
    const key = m => (typeof m === "string" ? m : JSON.stringify(m));
    const numeric = members.every(m => typeof m === "string" && /^-?\d+(\.\d+)?$/.test(m));
    return [...members].sort((a, b) => (numeric ? Number(a) - Number(b) : key(a).localeCompare(key(b), undefined, { numeric: true })));
  }

  function infix(symbolHtml, prec, assoc, args) {
    const parts = args.map((a, i) => paren(render(a), assoc || i === 0 ? prec : prec + 1, { op: symbolHtml, prec }));
    return { html: parts.join(` ${op(symbolHtml)} `), prec, op: symbolHtml };
  }

  function render(t) {
    if (typeof t === "string") return literal(t);
    if (t.length === 0) return atom("()");
    const [head, ...args] = t;

    if (Array.isArray(head)) {
      // ((_ is S) x), ((_ extract i j) x), ...
      if (head[0] === "_" && head[1] === "is") return call(`is-${head[2]}`, args.map(render));
      if (head[0] === "_" && head[1] === "extract") return atom(paren(render(args[0]), ATOM) + `[${head[2]}:${head[3]}]`);
      return call(head.flat(Infinity).join(" "), args.map(render));
    }

    switch (head) {
      case "_":  // indexed symbols: (_ fmf.card Color K) is |Color| ≤ K
        if (args[0] === "fmf.card") return { html: `|${render(args[1]).html}| ${op("≤")} ${render(args[2]).html}`, prec: 5 };
        return atom(span("kw", esc(args.flat(Infinity).join(" "))));
      case "as":
        if (args[0] === "set.empty") return atom(span("n", "∅"));
        return render(args[0]);
      case "let": return render(expandLets(t));
      case "fp": if (args.length === 3) return floatValue(...args); break;
      case "not": {
        const inner = args[0];
        if (Array.isArray(inner) && NEGATED[inner[0]] && inner.length === 3) {
          return infix(NEGATED[inner[0]], 5, false, inner.slice(1));
        }
        return { html: op("¬") + paren(render(inner), ATOM), prec: 4 };
      }
      case "distinct":
        if (args.length === 2) return infix("≠", 5, false, args);
        return call("distinct", args.map(render));
      case "-": if (args.length === 1) return { html: op("−") + paren(render(args[0]), ATOM), prec: 8 }; break;
      case "bvnot": return { html: op("~") + paren(render(args[0]), ATOM), prec: 8 };
      case "ff.neg": case "bvneg": return { html: op("−") + paren(render(args[0]), ATOM), prec: 8 };
      case "int.pow2": return atom(span("n", "2") + `<sup>${render(args[0]).html}</sup>`);
      case "select": return atom(paren(render(args[0]), ATOM) + `[${render(args[1]).html}]`);
      case "store": return atom(paren(render(args[0]), ATOM) + `[${render(args[1]).html} ${op("↦")} ${render(args[2]).html}]`);
      case "set.singleton": return atom(`{${render(args[0]).html}}`);
      case "set.union": {
        // models print {0, 1} as (set.union (set.singleton 0) (set.singleton 1))
        const members = literalMembers(t);
        if (members) return atom(`{${sortMembers(members).map(m => render(m).html).join(", ")}}`);
        break;
      }
      case "set.insert": {
        const base = args[args.length - 1];
        const members = `{${args.slice(0, -1).map(a => render(a).html).join(", ")}}`;
        if (isEmptySet(base)) return atom(members);
        return { html: `${members} ${op("∪")} ${paren(render(base), 6)}`, prec: 6 };
      }
      case "set.card": case "str.len": case "abs": return atom(`|${render(args[0]).html}|`);
      case "set.complement": return atom(paren(render(args[0]), ATOM) + "<sup>c</sup>");
      case "rel.transpose": return atom(paren(render(args[0]), ATOM) + "<sup>T</sup>");
      case "tuple": return atom(`⟨${args.map(a => render(a).html).join(", ")}⟩`);
      case "str.to_re": return render(args[0]);
      case "re.*": return atom(paren(render(args[0]), ATOM) + "<sup>*</sup>");
      case "re.+": return atom(paren(render(args[0]), ATOM) + "<sup>+</sup>");
      case "str.to_int": return call("int", args.map(render));
      case "str.from_int": return call("str", args.map(render));
      case "ite": return { html: `${span("kw", "if")} ${render(args[0]).html} ${span("kw", "then")} ${render(args[1]).html} ${span("kw", "else")} ${render(args[2]).html}`, prec: 0 };
    }
    if (INFIX[head] && args.length >= 2) {
      const [sym, prec, assoc] = INFIX[head];
      return infix(sym, prec, !!assoc, args);
    }
    if (args.length === 0) return literal(head);
    return call(head, args.map(render));
  }

  // HTML for one term, or null if it does not parse (the caller shows it raw)
  function toHtml(text) {
    try { return render(parse(text)).html; }
    catch (e) { return null; }
  }

  return { toHtml, parse, render };
})();
