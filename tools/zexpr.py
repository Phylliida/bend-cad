# Drafting macros for certificate proofs (expanded before @-shorthand):
#   @ATOMS name = a=term,, b=term,, m:=macro-expr,, ...   (a line; removed)
#   @ZEQ[set | lhs | rhs]          FR.fring_eq call proving {lhs == rhs}
#   @FT[set | expr]                the field term of expr
#   @CERT[set | x | c1 ; r1 | ... || hyps]     FO.certN call proving {x == 0}
#   @CERTEQ[set | X | Y | c1 ; r1 | ... || hyps]  FO.eq_of_sub(...) proving {X == Y}
#   @RING[set | target | source]   R.ring_eq call proving {target == source} in Z
#   @ZT[set | expr]                the integer term of expr
# "set" is a name defined by @ATOMS, or an inline atom list. Atoms are
# "name=term" (or a bare name, its own term); "m:=expr" is a textual macro.
import re

def tokenize(s):
    toks = re.findall(r'[A-Za-z_][A-Za-z_0-9]*|\d+|[-+*()]', s)
    assert "".join(toks) == re.sub(r'\s+', '', s), s
    return toks

def pos(n):
    if n == 1: return "S.XH{}"
    return ("S.XI{" if n % 2 else "S.XO{") + pos(n // 2) + "}"

def parse(s):
    toks = tokenize(s); i = [0]
    def peek(): return toks[i[0]] if i[0] < len(toks) else None
    def eat(t=None):
        tok = toks[i[0]]; assert t is None or tok == t, (t, tok, s); i[0] += 1; return tok
    def expr():
        x = term()
        while peek() in ('+', '-'):
            op = eat(); y = term(); x = (op, x, y)
        return x
    def term():
        x = unary()
        while peek() == '*':
            eat(); y = unary(); x = ('*', x, y)
        return x
    def unary():
        if peek() == '-':
            eat(); return ('neg', unary())
        return atom()
    def atom():
        t = eat()
        if t == '(':
            x = expr(); eat(')'); return x
        if t.isdigit(): return ('num', int(t))
        return ('var', t)
    x = expr(); assert peek() is None, s
    return x

def z(ast, names):
    k = ast[0]
    if k == 'var':
        assert ast[1] in names, (ast[1], names); return "E.ZVar{" + str(names.index(ast[1])) + "n}"
    if k == 'num': return "E.ZCst{S.Z0{}}" if ast[1] == 0 else "E.ZCst{S.Zpos{" + pos(ast[1]) + "}}"
    if k == 'neg': return "E.ZNeg{" + z(ast[1], names) + "}"
    tag = {'+': 'ZAdd', '-': 'ZSub', '*': 'ZMul'}[k]
    return "E." + tag + "{" + z(ast[1], names) + ", " + z(ast[2], names) + "}"

def f(ast, names, terms):
    k = ast[0]
    if k == 'var': return terms[names.index(ast[1])]
    if k == 'num':
        if ast[1] == 0: return "O.zero(F)"
        if ast[1] == 1: return "O.one(F)"
        return "O.ofz(~F, S.Zpos{" + pos(ast[1]) + "})"
    if k == 'neg': return "O.neg(F, " + f(ast[1], names, terms) + ")"
    a, b = f(ast[1], names, terms), f(ast[2], names, terms)
    return {'+': "O.add(F, %s, %s)", '-': "O.sub(~F, %s, %s)", '*': "O.mul(F, %s, %s)"}[k] % (a, b)

def zt(ast, names, terms):
    k = ast[0]
    if k == 'var': return terms[names.index(ast[1])]
    if k == 'num': return "S.Z0{}" if ast[1] == 0 else "S.Zpos{" + pos(ast[1]) + "}"
    if k == 'neg': return "S.Z.neg(" + zt(ast[1], names, terms) + ")"
    a, b = zt(ast[1], names, terms), zt(ast[2], names, terms)
    return {'+': "S.Z.add(%s, %s)", '-': "S.Z.sub(%s, %s)", '*': "S.Z.mul(%s, %s)"}[k] % (a, b)

SETS = {}
def atomset(spec):
    spec = spec.strip()
    if re.fullmatch(r'\w+', spec) and spec in SETS: return SETS[spec]
    names, terms, macros = [], [], []
    for a in [a.strip() for a in spec.split(',,')]:
        if ':=' in a:
            n, t = a.split(':=', 1); macros.append((n.strip(), t.strip())); continue
        if '=' in a:
            n, t = a.split('=', 1); names.append(n.strip()); terms.append(t.strip())
        else:
            names.append(a); terms.append(a)
    return (names, terms, macros)

def subst(e, macros):
    for n, t in reversed(macros):
        e = re.sub(r'\b' + n + r'\b', '(' + t + ')', e)
    return e

def P(e, st): return parse(subst(e, st[2]))

def find_close(src, k):
    depth = 0; m = k
    while True:
        c = src[m]
        if c == '[': depth += 1
        elif c == ']':
            depth -= 1
            if depth == 0: return m
        m += 1

def cert(st, x_ast, pairs, hyps):
    names, terms, _ = st
    n = len(pairs)
    sum_ast = None
    for c, r in pairs:
        t = ('*', c, r); sum_ast = t if sum_ast is None else ('+', sum_ast, t)
    args = [f(x_ast, names, terms)]
    for c, r in pairs:
        args += [f(c, names, terms), f(r, names, terms)]
    zeq = "FR.fring_eq(~F, [" + ", ".join(terms) + "], " + z(x_ast, names) + ", " + z(sum_ast, names) + ", {==})"
    return "FO.cert%d(~F, %s, %s, %s)" % (n, ", ".join(args), zeq, hyps)

def expand(src):
    lines = []
    for line in src.splitlines(keepends=True):
        m = re.match(r'\s*@ATOMS (\w+) = (.*)$', line)
        if m:
            SETS[m.group(1)] = atomset(m.group(2)); continue
        lines.append(line)
    src = "".join(lines)
    for tag in ["@CERTEQ[", "@CERT[", "@ZEQ[", "@FT[", "@RING[", "@ZT["]:
        while True:
            k = src.find(tag)
            if k < 0: break
            m = find_close(src, k + len(tag) - 1)
            body = src[k + len(tag):m]
            if '||' in body: body, hyps = body.split('||', 1); hyps = hyps.strip()
            else: hyps = ''
            parts = [p.strip() for p in body.split('|')]
            st = atomset(parts[0])
            names, terms, _ = st
            if tag == "@ZEQ[":
                out = "FR.fring_eq(~F, [" + ", ".join(terms) + "], " + z(P(parts[1], st), names) + ", " + z(P(parts[2], st), names) + ", {==})"
            elif tag == "@RING[":
                out = "R.ring_eq([" + ", ".join(terms) + "], " + z(P(parts[1], st), names) + ", " + z(P(parts[2], st), names) + ", {==})"
            elif tag == "@ZT[":
                out = zt(P(parts[1], st), names, terms)
            elif tag == "@FT[":
                out = f(P(parts[1], st), names, terms)
            elif tag == "@CERT[":
                pairs = [tuple(P(q, st) for q in p.split(';')) for p in parts[2:]]
                out = cert(st, P(parts[1], st), pairs, hyps)
            else:
                X, Y = P(parts[1], st), P(parts[2], st)
                pairs = [tuple(P(q, st) for q in p.split(';')) for p in parts[3:]]
                out = "FO.eq_of_sub(~F, %s, %s, %s)" % (f(X, names, terms), f(Y, names, terms), cert(st, ('-', X, Y), pairs, hyps))
            src = src[:k] + out + src[m + 1:]
    return src
