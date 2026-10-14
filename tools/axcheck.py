#!/usr/bin/env python3
"""Check that lean/BendCad/Axioms.lean transcribes the Bend axioms exactly.

Parses every field of spec/field.bend's `OField` record and spec/real.bend's
`Complete` record, and the same fields of the Lean structures, into one
normal form (binders without their types, implications, equalities without
their type annotation, `Or`, `False`, applications with the field argument
`F` dropped) and requires them to be identical, field by field, in order.
The derived definitions (sub, le, bnd, nat, eps, cauchy) are printed side
by side for reading; they are short. Run from bend-cad/.
"""
import re, sys

def tokens(s, lean):
    pat = r'\s+|(->|→|==|∀|∨|∧|ℕ|&2|[(){}<>@:,=+]|~?[A-Za-z_][A-Za-z_0-9.]*|[0-9]+n?)'
    out = []
    pos = 0
    while pos < len(s):
        m = re.compile(pat).match(s, pos)
        if not m:
            raise SystemExit('cannot tokenize: ' + s[pos:pos + 30])
        if m.group(1):
            out.append(m.group(1))
        pos = m.end()
    return out

def name(n):
    n = n.lstrip('~')
    for p in ('O.', 'M.', 'CR.', 'F.'):
        if n.startswith(p):
            n = n[len(p):]
    return {'Nat.add': 'natadd', 'Empty': 'False', 'ℕ': 'Nat', 'Data': 'Prop'}.get(n, n)

class Bend:
    """Bend types: @x: T -> T | A -> T | A; A: {E == E : T} | (T) | app."""
    def __init__(self, toks):
        self.t, self.i = toks, 0
    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None
    def eat(self, x=None):
        tok = self.t[self.i]
        if x is not None and tok != x:
            raise SystemExit('bend: expected %s, got %s at %s' % (x, tok, self.t[self.i:self.i + 8]))
        self.i += 1
        return tok
    def ty(self):
        if self.peek() == '@':
            self.eat('@'); v = self.eat(); self.eat(':')
            self.atom()  # the binder's type is dropped
            self.eat('->')
            return ('pi', v, self.ty())
        a = self.atom()
        if self.peek() == '->':
            self.eat('->')
            return ('imp', a, self.ty())
        return a
    def atom(self):
        if self.peek() == '{':
            self.eat('{'); l = self.ty(); self.eat('=='); r = self.ty(); self.eat(':'); self.ty(); self.eat('}')
            return ('eq', l, r)
        if self.peek() == '(':
            self.eat('('); x = self.ty(); self.eat(')')
            return x
        f = name(self.eat())
        if f == '1n' and self.peek() == '+':
            self.eat('+')
            return ('succ', self.atom())
        if f == 'Either' and self.peek() == '<':
            self.eat('<'); self.eat('&2'); self.eat(','); self.eat('&2'); self.eat(',')
            a = self.ty(); self.eat(','); b = self.ty(); self.eat('>')
            return ('or', a, b)
        args = []
        if self.peek() == '(':
            self.eat('(')
            while True:
                args.append(self.ty())
                if self.peek() == ',':
                    self.eat(',')
                else:
                    break
            self.eat(')')
        if args and args[0] in (('app', 'F'), ('app', '~F')):
            args = args[1:]
        if f == 'Or':
            return ('or', args[0], args[1])
        if f == 'Both':
            return ('and', args[0], args[1])
        if f == 'C':
            return ('app', 'C')
        return ('app', f) + tuple(args)

class Lean:
    """Lean types: ∀ xs, T | O → T | O; O: E ∨ O | E; E: S = S | S; S: P + P | P; P: application."""
    def __init__(self, toks):
        self.t, self.i = toks, 0
    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None
    def eat(self, x=None):
        tok = self.t[self.i]
        if x is not None and tok != x:
            raise SystemExit('lean: expected %s, got %s at %s' % (x, tok, self.t[self.i:self.i + 8]))
        self.i += 1
        return tok
    def ty(self):
        if self.peek() == '∀':
            self.eat('∀'); vs = []
            while self.peek() != ',':
                vs.append(self.eat())
            self.eat(',')
            body = self.ty()
            for v in reversed(vs):
                body = ('pi', v, body)
            return body
        a = self.disj()
        if self.peek() == '→':
            self.eat('→')
            return ('imp', a, self.ty())
        return a
    def disj(self):
        a = self.conj()
        if self.peek() == '∨':
            self.eat('∨')
            return ('or', a, self.disj())
        return a
    def conj(self):
        a = self.eqn()
        if self.peek() == '∧':
            self.eat('∧')
            return ('and', a, self.conj())
        return a
    def eqn(self):
        a = self.sum()
        if self.peek() == '=':
            self.eat('=')
            return ('eq', a, self.sum())
        return a
    def sum(self):
        a = self.appl()
        while self.peek() == '+':
            self.eat('+')
            b = self.appl()
            a = ('succ', a) if b == ('app', '1') else ('app', 'natadd', a, b)
        return a
    def prim(self):
        if self.peek() == '(':
            self.eat('('); x = self.ty(); self.eat(')')
            return x
        return ('app', name(self.eat()))
    def appl(self):
        f = self.prim()
        args = []
        while self.peek() is not None and self.peek() not in (')', ',', '→', '∨', '∧', '=', '+'):
            args.append(self.prim())
        if not args:
            return f
        if f[0] != 'app' or len(f) != 2:
            raise SystemExit('lean: applying a non-name')
        return f + tuple(args)

def bend_fields(src, record):
    body = src[src.index(record + '{') + len(record) + 1:]
    depth, end = 0, 0
    for j, ch in enumerate(body):
        if ch in '({':
            depth += 1
        elif ch in ')}':
            if depth == 0:
                end = j
                break
            depth -= 1
    body = body[:end]
    fields, depth, cur = [], 0, ''
    for ch in body:
        if ch in '({':
            depth += 1
        elif ch in ')}':
            depth -= 1
        if ch == ',' and depth == 0:
            fields.append(cur); cur = ''
        else:
            cur += ch
    fields.append(cur)
    out = []
    for f in fields:
        nm, ty = f.split(':', 1)
        out.append((nm.strip(), ' '.join(ty.split())))
    return out

def lean_fields(src, struct):
    body = src[src.index('structure ' + struct):]
    body = body[body.index(' where') + 6:]
    out = []
    for line in body.split('\n')[1:]:
        if not line.startswith('  ') or not line.strip():
            break
        nm, ty = line.strip().split(' : ', 1)
        out.append((nm, ty))
    return out

def compare(bsrc, lsrc, record, struct):
    # the carrier, a field of Bend's record, is the Lean structure's parameter
    bf = [(n, t) for n, t in bend_fields(bsrc, record) if not (record == 'OField' and n == 'C')]
    lf = lean_fields(lsrc, struct)
    ok = [n for n, _ in bf] == [n for n, _ in lf]
    if not ok:
        print('FIELD NAMES DIFFER:', [n for n, _ in bf], [n for n, _ in lf])
    for (bn, bt), (ln, lt) in zip(bf, lf):
        b, l = Bend(tokens(bt, False)), Lean(tokens(lt, True))
        bx, lx = b.ty(), l.ty()
        if b.i != len(b.t) or l.i != len(l.t):
            raise SystemExit('trailing tokens in ' + bn)
        same = bx == lx
        ok = ok and same
        print('%-4s %s' % ('ok' if same else 'DIFF', bn))
        if not same:
            print('   bend:', bx)
            print('   lean:', lx)
    return ok

# a one-line Bend def's body
def bend_def(src, nm):
    i = src.index('\ndef ' + nm + '(')
    return src[i + 1:].split('\n')[1].strip()

def lean_def(src, nm):
    i = src.index('\ndef OField.' + nm + ' ')
    rest = src[i + 1:]
    body = rest[rest.index(':=') + 2:]
    out = []
    for l in body.split('\n'):
        if not l.strip():
            if out:
                break
            continue
        out.append(l.strip())
    return ' '.join(out)

def compare_defs(srcs, lsrc, names):
    ok = True
    for nm, src in zip(names, srcs):
        b, l = Bend(tokens(bend_def(src, nm), False)), Lean(tokens(lean_def(lsrc, nm), True))
        bx, lx = b.ty(), l.ty()
        same = bx == lx and b.i == len(b.t) and l.i == len(l.t)
        ok = ok and same
        print('%-4s def %s' % ('ok' if same else 'DIFF', nm))
        if not same:
            print('   bend:', bx)
            print('   lean:', lx)
    return ok

field_b = open('spec/field.bend').read()
real_b = open('spec/real.bend').read()
lean = open('lean/BendCad/Axioms.lean').read()
ok = compare(field_b, lean, 'OField', 'OField')
ok = compare(real_b, lean, 'Complete', 'Complete') and ok
mat_b = open('spec/mat.bend').read()
ok = compare_defs([field_b, field_b, mat_b, real_b, real_b], lean, ['sub', 'le', 'bnd', 'eps', 'cauchy']) and ok
print('by eye: nat (a two-case match)')
print('  bend:', ' '.join(real_b[real_b.index('def nat('):real_b.index('# 1/(k+1)')].split()))
print('  lean:', ' '.join(lean[lean.index('def OField.nat'):lean.index('/-- `spec/real.bend`: 1/(k+1)')].split()))
print('ALL AXIOMS MATCH' if ok else 'MISMATCH')
sys.exit(0 if ok else 1)
