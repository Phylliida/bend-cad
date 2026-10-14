# Reducing a rational by the gcd of its parts, a runtime choice to keep
# sizes down (DESIGN §3, R10). The division and the gcd are untrusted:
# reduce checks its answer by multiplying back (n = n' g and d = d' g),
# and returns x unchanged if the check fails. So Q.eq(reduce x, x) needs no
# theory of divisibility (q_reduce, below).

import Base
import ./zring.bend as R
import ./zord.bend as ZO
import ../spec/num.bend as S
import ../spec/ring.bend as E

# Division (untrusted)
# --------------------

type Dv is Data:
  Dv{q: S.Z, r: S.Z}

def Dv.q(p: Dv) -> S.Z:
  match p:
    case Dv{q, r}:
      q

# one step of long division: q2 = 2q, r2 = 2r + bit; subtract d if it fits
def div.adj(c: Cmp, +q2: S.Z, +r2: S.Z, +d: S.Pos) -> Dv:
  match c:
    case LT{}:
      Dv{q2, r2}
    case EQ{}:
      Dv{S.Z.add(q2, S.Zpos{S.XH{}}), S.Z.sub(r2, S.Zpos{d})}
    case GT{}:
      Dv{S.Z.add(q2, S.Zpos{S.XH{}}), S.Z.sub(r2, S.Zpos{d})}

def div.step(+d: S.Pos, bit: Bool, p: Dv) -> Dv:
  match bit p:
    case False{} Dv{q, +r}:
      div.adj(S.Z.cmp(S.Z.double(r), S.Zpos{d}), S.Z.double(q), S.Z.double(r), d)
    case True{} Dv{q, +r}:
      div.adj(S.Z.cmp(S.Z.succ_double(r), S.Zpos{d}), S.Z.double(q), S.Z.succ_double(r), d)

# n = q d + r with 0 <= r < d, most significant bit first
def div(n: S.Pos, +d: S.Pos) -> Dv:
  match n:
    case S.XH{}:
      div.adj(S.Z.cmp(S.Zpos{S.XH{}}, S.Zpos{d}), S.Z0{}, S.Zpos{S.XH{}}, d)
    case S.XO{m}:
      div.step(d, False{}, div(m, d))
    case S.XI{m}:
      div.step(d, True{}, div(m, d))

def Dv.r(p: Dv) -> S.Z:
  match p:
    case Dv{q, r}:
      r

# the number of binary digits
def size(p: S.Pos) -> Nat:
  match p:
    case S.XH{}:
      1n
    case S.XO{q}:
      1n+size(q)
    case S.XI{q}:
      1n+size(q)

# Euclid, with fuel enough for its steps (each halves a remainder at worst)
def gcd.go(fuel: Nat, +a: S.Pos, b: S.Z) -> S.Pos:
  match fuel b:
    case 0n b:
      a
    case 1n+f S.Zpos{+p}:
      gcd.go(f, p, Dv.r(div(a, p)))
    case 1n+f S.Z0{}:
      a
    case 1n+f S.Zneg{p}:
      a

def gcd(+a: S.Pos, +b: S.Pos) -> S.Pos:
  gcd.go(Nat.add(Nat.double(size(a)), Nat.double(size(b))), a, S.Zpos{b})

# |n| / g with n's sign
def zdiv(n: S.Z, +g: S.Pos) -> S.Z:
  match n:
    case S.Z0{}:
      S.Z0{}
    case S.Zpos{p}:
      Dv.q(div(p, g))
    case S.Zneg{p}:
      S.Z.neg(Dv.q(div(p, g)))

# the gcd of n and d (d for n = 0)
def gnum(n: S.Z, +d: S.Pos) -> S.Pos:
  match n:
    case S.Z0{}:
      d
    case S.Zpos{p}:
      gcd(p, d)
    case S.Zneg{p}:
      gcd(p, d)

# Reduction (checked)
# -------------------

# n' / d' when n' g = n and d' g = d (both comparisons EQ), else x
def reduce.fin3(nq: S.Z, dq: S.Z, +x: S.Q) -> S.Q:
  match dq:
    case S.Zpos{e}:
      S.Q{nq, e}
    case S.Z0{}:
      x
    case S.Zneg{e}:
      x

def reduce.fin2(c2: Cmp, nq: S.Z, dq: S.Z, +x: S.Q) -> S.Q:
  match c2:
    case EQ{}:
      reduce.fin3(nq, dq, x)
    case LT{}:
      x
    case GT{}:
      x

def reduce.fin(c1: Cmp, c2: Cmp, nq: S.Z, dq: S.Z, +x: S.Q) -> S.Q:
  match c1:
    case EQ{}:
      reduce.fin2(c2, nq, dq, x)
    case LT{}:
      x
    case GT{}:
      x

def reduce.go(+n: S.Z, +d: S.Pos, +g: S.Pos, +x: S.Q) -> S.Q:
  reduce.fin(S.Z.cmp(S.Z.mul(zdiv(n, g), S.Zpos{g}), n), S.Z.cmp(S.Z.mul(Dv.q(div(d, g)), S.Zpos{g}), S.Zpos{d}), zdiv(n, g), Dv.q(div(d, g)), x)

def reduce(+x: S.Q) -> S.Q:
  reduce.go(S.Q.num(x), S.Q.den(x), gnum(S.Q.num(x), S.Q.den(x)), x)

# Reduction keeps the rational
# ----------------------------

# from n' g = n and e g = d: n' / e = n / d
def reduce_ok.eq(+nq: S.Z, +e: S.Pos, +n: S.Z, +d: S.Pos, +g: S.Pos, h1: {S.Z.mul(nq, S.Zpos{g}) == n : S.Z}, h2: {S.Z.mul(S.Zpos{e}, S.Zpos{g}) == S.Zpos{d} : S.Z}) -> {S.Z.mul(nq, S.Zpos{d}) == S.Z.mul(n, S.Zpos{e}) : S.Z}:
  %h2 : {S.Z.mul(nq, _) == S.Z.mul(n, S.Zpos{e}) : S.Z}
  %h1 : {S.Z.mul(nq, S.Z.mul(S.Zpos{e}, S.Zpos{g})) == S.Z.mul(_, S.Zpos{e}) : S.Z}
  R.ring_eq([nq, S.Zpos{e}, S.Zpos{g}], E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{1n}}, {==})

def reduce_ok.fin3(+nq: S.Z, dq: S.Z, +x: S.Q, +g: S.Pos,
  h1: {S.Z.mul(nq, S.Zpos{g}) == S.Q.num(x) : S.Z},
  e2: {S.Z.cmp(S.Z.mul(dq, S.Zpos{g}), S.Zpos{S.Q.den(x)}) == EQ{} : Cmp}) -> S.Q.eq(reduce.fin3(nq, dq, x), x):
  match dq:
    case S.Zpos{+e}:
      reduce_ok.eq(nq, e, S.Q.num(x), S.Q.den(x), g, h1,
        ZO.sub_eq(S.Z.mul(S.Zpos{e}, S.Zpos{g}), S.Zpos{S.Q.den(x)}, ZO.eq_zero(S.Z.mul(S.Zpos{e}, S.Zpos{g}), S.Zpos{S.Q.den(x)}, e2)))
    case S.Z0{}:
      {==}
    case S.Zneg{e}:
      {==}

def reduce_ok.fin2(c2: Cmp, +nq: S.Z, +dq: S.Z, +x: S.Q, +g: S.Pos,
  h1: {S.Z.mul(nq, S.Zpos{g}) == S.Q.num(x) : S.Z},
  e2: {S.Z.cmp(S.Z.mul(dq, S.Zpos{g}), S.Zpos{S.Q.den(x)}) == c2 : Cmp}) -> S.Q.eq(reduce.fin2(c2, nq, dq, x), x):
  match c2:
    case EQ{}:
      reduce_ok.fin3(nq, dq, x, g, h1, e2)
    case LT{}:
      {==}
    case GT{}:
      {==}

def reduce_ok.fin(c1: Cmp, c2: Cmp, +nq: S.Z, +dq: S.Z, +x: S.Q, +g: S.Pos,
  e1: {S.Z.cmp(S.Z.mul(nq, S.Zpos{g}), S.Q.num(x)) == c1 : Cmp},
  e2: {S.Z.cmp(S.Z.mul(dq, S.Zpos{g}), S.Zpos{S.Q.den(x)}) == c2 : Cmp}) -> S.Q.eq(reduce.fin(c1, c2, nq, dq, x), x):
  match c1:
    case EQ{}:
      reduce_ok.fin2(c2, nq, dq, x, g, ZO.sub_eq(S.Z.mul(nq, S.Zpos{g}), S.Q.num(x), ZO.eq_zero(S.Z.mul(nq, S.Zpos{g}), S.Q.num(x), e1)), e2)
    case LT{}:
      {==}
    case GT{}:
      {==}

def reduce_ok(+x: S.Q) -> S.Q.eq(reduce(x), x):
  reduce_ok.fin(S.Z.cmp(S.Z.mul(zdiv(S.Q.num(x), gnum(S.Q.num(x), S.Q.den(x))), S.Zpos{gnum(S.Q.num(x), S.Q.den(x))}), S.Q.num(x)),
    S.Z.cmp(S.Z.mul(Dv.q(div(S.Q.den(x), gnum(S.Q.num(x), S.Q.den(x)))), S.Zpos{gnum(S.Q.num(x), S.Q.den(x))}), S.Zpos{S.Q.den(x)}),
    zdiv(S.Q.num(x), gnum(S.Q.num(x), S.Q.den(x))), Dv.q(div(S.Q.den(x), gnum(S.Q.num(x), S.Q.den(x)))), x, gnum(S.Q.num(x), S.Q.den(x)), {==}, {==})
