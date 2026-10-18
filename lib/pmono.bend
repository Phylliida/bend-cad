# bend-cad: monotone polynomials, reflected (DESIGN §10.4 "C6 plan",
# C6a). Proofs only.
# Generated: python3 tools/expand.py tools/drafts/pmono.draft lib/pmono.bend
#
# A PE is a polynomial over atoms 0, 1, ... built with + and * only, read
# in F at a list of values (peval). Each atom i carries a bound c_i and a
# flag: fixed (0 <= a_i <= c_i) or small (0 <= a_i <= t c_i), for one
# scale 0 <= t <= 1 (Bnd). Then peval(a, P) <= peval(c, P) (pe_mono); when
# every monomial of P has a small atom (d1), peval(a, P) <= t peval(c, P)
# (pe_lin); when every monomial has two (d2), peval(a, P) <= t (t
# peval(c, P)) (pe_quad). The solver's constants (C5) are pevals of
# reflected expressions by conversion, so each smallness hypothesis
# becomes one of these.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ./fring.bend as FR
import ./ford.bend as FO
import ./fmat.bend as FM
import ./dmat.bend as DM
import ./fvec.bend as FV
import ./karith.bend as KA

type PE is Data:
  PAt{i: Nat}
  PPlus{p: PE, q: PE}
  PTimes{p: PE, q: PE}

def peval(~F: O.OField, +env: List<&2, O.C(F)>, e: PE) -> O.C(F):
  match e:
    case PAt{i}:
      O.lookup(~F, env, i)
    case PPlus{p, q}:
      O.add(F, peval(~F, env, p), peval(~F, env, q))
    case PTimes{p, q}:
      O.mul(F, peval(~F, env, p), peval(~F, env, q))

# Flags
# -----

def pand(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      False{}

def por(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      True{}
    case False{}:
      b

def bget(sm: List<&2, Bool>, i: Nat) -> Bool:
  match sm i:
    case Nil{} i:
      False{}
    case Con{s, ss} 0n:
      s
    case Con{s, ss} 1n+j:
      bget(ss, j)

# every monomial has a small atom
def d1(+sm: List<&2, Bool>, e: PE) -> Bool:
  match e:
    case PAt{i}:
      bget(sm, i)
    case PPlus{p, q}:
      pand(d1(sm, p), d1(sm, q))
    case PTimes{p, q}:
      por(d1(sm, p), d1(sm, q))

# every monomial has two small atoms (counted with multiplicity)
def d2(+sm: List<&2, Bool>, e: PE) -> Bool:
  match e:
    case PAt{i}:
      False{}
    case PPlus{p, q}:
      pand(d2(sm, p), d2(sm, q))
    case PTimes{+p, +q}:
      por(d2(sm, p), por(d2(sm, q), pand(d1(sm, p), d1(sm, q))))


def absurd(-A: Type, x: Empty) -> A:
  match x:

def pand_l(a: Bool, +b: Bool, h: {pand(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def pand_r(a: Bool, +b: Bool, h: {pand(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      absurd({b == True{} : Bool}, KA.ft(h))

# Order
# -----

# a <= b and b2 = b give a <= b2
def le_r(~F: O.OField, +a: O.C(F), +b: O.C(F), +b2: O.C(F), e: {b2 == b : O.C(F)}, h: O.le(~F, a, b)) -> O.le(~F, a, b2):
  %Equal.sym(O.C(F), b2, b, e) : O.le(~F, a, _)
  h

def le_add2(~F: O.OField, +a: O.C(F), +b: O.C(F), +c: O.C(F), +d: O.C(F), h1: O.le(~F, a, b), h2: O.le(~F, c, d)) -> O.le(~F, O.add(F, a, c), O.add(F, b, d)):
  FV.le_of_sub(~F, O.add(F, a, c), O.add(F, b, d), FM.nn_eq(~F, O.sub(~F, O.add(F, b, d), O.add(F, a, c)), O.add(F, O.sub(~F, b, a), O.sub(~F, d, c)), FR.fring_eq(~F, [a, b, c, d], E.ZAdd{E.ZSub{E.ZVar{1n}, E.ZVar{0n}}, E.ZSub{E.ZVar{3n}, E.ZVar{2n}}}, E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{3n}}, E.ZAdd{E.ZVar{0n}, E.ZVar{2n}}}, {==}), FO.nonneg_add(~F, O.sub(~F, b, a), O.sub(~F, d, c), FM.sub_nonneg(~F, a, b, h1), FM.sub_nonneg(~F, c, d, h2))))

# a <= b and c <= d give a c <= b d, for 0 <= c and 0 <= b
def le_mul2(~F: O.OField, +a: O.C(F), +b: O.C(F), +c: O.C(F), +d: O.C(F), h1: O.le(~F, a, b), h2: O.le(~F, c, d), hc: O.le(~F, O.zero(F), c), +hb: O.le(~F, O.zero(F), b)) -> O.le(~F, O.mul(F, a, c), O.mul(F, b, d)):
  DM.le_trans(~F, O.mul(F, a, c), O.mul(F, b, c), O.mul(F, b, d), FV.mul_le_r(~F, a, b, c, hc, h1), FV.mul_le(~F, b, c, d, hb, h2))

# t y <= y, for t <= 1 and 0 <= y
def tle(~F: O.OField, +t: O.C(F), +y: O.C(F), ht1: O.le(~F, t, O.one(F)), hy: O.le(~F, O.zero(F), y)) -> O.le(~F, O.mul(F, t, y), y):
  le_r(~F, O.mul(F, t, y), O.mul(F, O.one(F), y), y, FR.fring_eq(~F, [y], E.ZVar{0n}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, {==}), FV.mul_le_r(~F, t, O.one(F), y, hy, ht1))

# Atoms
# -----
# an atom's value a, its bound c and whether it is small

type Atm<-A: Data> is Data:
  Atm{a: A, c: A, s: Bool}

def avs(~F: O.OField, env: List<&2, Atm<O.C(F)>>) -> List<&2, O.C(F)>:
  match env:
    case Nil{}:
      Nil{}
    case Con{Atm{x, y, s}, r}:
      Con{x, avs(~F, r)}

def cvs(~F: O.OField, env: List<&2, Atm<O.C(F)>>) -> List<&2, O.C(F)>:
  match env:
    case Nil{}:
      Nil{}
    case Con{Atm{x, y, s}, r}:
      Con{y, cvs(~F, r)}

def svs(~F: O.OField, env: List<&2, Atm<O.C(F)>>) -> List<&2, Bool>:
  match env:
    case Nil{}:
      Nil{}
    case Con{Atm{x, y, s}, r}:
      Con{s, svs(~F, r)}

def AtB(~F: O.OField, +x: O.C(F), +y: O.C(F), s: Bool, +t: O.C(F)) -> Data:
  match s:
    case True{}:
      O.le(~F, x, O.mul(F, t, y))
    case False{}:
      O.le(~F, x, y)

# 0 <= x, 0 <= y, and x <= y (fixed) or x <= t y (small)
def At(~F: O.OField, +x: O.C(F), +y: O.C(F), +s: Bool, +t: O.C(F)) -> Data:
  M.Both(O.le(~F, O.zero(F), x), M.Both(O.le(~F, O.zero(F), y), AtB(~F, x, y, s, t)))

def Bnd(~F: O.OField, env: List<&2, Atm<O.C(F)>>, +t: O.C(F)) -> Data:
  match env:
    case Nil{}:
      Unit
    case Con{Atm{+x, +y, +s}, r}:
      M.Both(At(~F, x, y, s, t), Bnd(~F, r, t))


def bnd_hd(~F: O.OField, +x: O.C(F), +y: O.C(F), +s: Bool, r: List<&2, Atm<O.C(F)>>, +t: O.C(F), h: M.Both(At(~F, x, y, s, t), Bnd(~F, r, t))) -> At(~F, x, y, s, t):
  (h1, h2) = h
  h1

def bnd_tl(~F: O.OField, +x: O.C(F), +y: O.C(F), +s: Bool, r: List<&2, Atm<O.C(F)>>, +t: O.C(F), h: M.Both(At(~F, x, y, s, t), Bnd(~F, r, t))) -> Bnd(~F, r, t):
  (h1, h2) = h
  h2

def bnd_at(~F: O.OField, env: List<&2, Atm<O.C(F)>>, +t: O.C(F), h: Bnd(~F, env, t), i: Nat) -> At(~F, O.lookup(~F, avs(~F, env), i), O.lookup(~F, cvs(~F, env), i), bget(svs(~F, env), i), t):
  match env i:
    case Nil{} i:
      (FO.le_refl(~F, O.zero(F)), (FO.le_refl(~F, O.zero(F)), FO.le_refl(~F, O.zero(F))))
    case Con{Atm{+x, +y, +s}, +r} 0n:
      bnd_hd(~F, x, y, s, r, t, h)
    case Con{Atm{+x, +y, +s}, +r} 1n+j:
      bnd_at(~F, r, t, bnd_tl(~F, x, y, s, r, t, h), j)

def at_nn(~F: O.OField, +x: O.C(F), +y: O.C(F), +s: Bool, +t: O.C(F), h: At(~F, x, y, s, t)) -> O.le(~F, O.zero(F), x):
  (h1, h2) = h
  h1

def at_cnn.go(~F: O.OField, +x: O.C(F), +y: O.C(F), +s: Bool, +t: O.C(F), h: M.Both(O.le(~F, O.zero(F), y), AtB(~F, x, y, s, t))) -> O.le(~F, O.zero(F), y):
  (h1, h2) = h
  h1

def at_cnn(~F: O.OField, +x: O.C(F), +y: O.C(F), +s: Bool, +t: O.C(F), h: At(~F, x, y, s, t)) -> O.le(~F, O.zero(F), y):
  (h1, h2) = h
  at_cnn.go(~F, x, y, s, t, h2)

def at_le.go(~F: O.OField, +x: O.C(F), +y: O.C(F), s: Bool, +t: O.C(F), +ht1: O.le(~F, t, O.one(F)), +hy: O.le(~F, O.zero(F), y), h: AtB(~F, x, y, s, t)) -> O.le(~F, x, y):
  match s:
    case True{}:
      DM.le_trans(~F, x, O.mul(F, t, y), y, h, tle(~F, t, y, ht1, hy))
    case False{}:
      h

def at_le.b(~F: O.OField, +x: O.C(F), +y: O.C(F), +s: Bool, +t: O.C(F), +ht1: O.le(~F, t, O.one(F)), h: M.Both(O.le(~F, O.zero(F), y), AtB(~F, x, y, s, t))) -> O.le(~F, x, y):
  (h1, h2) = h
  at_le.go(~F, x, y, s, t, ht1, h1, h2)

# an atom is at most its bound
def at_le(~F: O.OField, +x: O.C(F), +y: O.C(F), +s: Bool, +t: O.C(F), +ht1: O.le(~F, t, O.one(F)), h: At(~F, x, y, s, t)) -> O.le(~F, x, y):
  (h1, h2) = h
  at_le.b(~F, x, y, s, t, ht1, h2)

def at_lin.go(~F: O.OField, +x: O.C(F), +y: O.C(F), s: Bool, +t: O.C(F), hs: {s == True{} : Bool}, h: AtB(~F, x, y, s, t)) -> O.le(~F, x, O.mul(F, t, y)):
  match s:
    case True{}:
      h
    case False{}:
      absurd(O.le(~F, x, O.mul(F, t, y)), KA.ft(hs))

def at_lin.b(~F: O.OField, +x: O.C(F), +y: O.C(F), +s: Bool, +t: O.C(F), hs: {s == True{} : Bool}, h: M.Both(O.le(~F, O.zero(F), y), AtB(~F, x, y, s, t))) -> O.le(~F, x, O.mul(F, t, y)):
  (h1, h2) = h
  at_lin.go(~F, x, y, s, t, hs, h2)

# a small atom is at most t times its bound
def at_lin(~F: O.OField, +x: O.C(F), +y: O.C(F), +s: Bool, +t: O.C(F), hs: {s == True{} : Bool}, h: At(~F, x, y, s, t)) -> O.le(~F, x, O.mul(F, t, y)):
  (h1, h2) = h
  at_lin.b(~F, x, y, s, t, hs, h2)

# Bounds
# ------

def pe_nn(~F: O.OField, +env: List<&2, Atm<O.C(F)>>, +t: O.C(F), +h: Bnd(~F, env, t), e: PE) -> O.le(~F, O.zero(F), peval(~F, avs(~F, env), e)):
  match e:
    case PAt{+i}:
      at_nn(~F, O.lookup(~F, avs(~F, env), i), O.lookup(~F, cvs(~F, env), i), bget(svs(~F, env), i), t, bnd_at(~F, env, t, h, i))
    case PPlus{+p, +q}:
      FO.nonneg_add(~F, peval(~F, avs(~F, env), p), peval(~F, avs(~F, env), q), pe_nn(~F, env, t, h, p), pe_nn(~F, env, t, h, q))
    case PTimes{+p, +q}:
      FO.mul_nonneg(~F, peval(~F, avs(~F, env), p), peval(~F, avs(~F, env), q), pe_nn(~F, env, t, h, p), pe_nn(~F, env, t, h, q))

def pe_cnn(~F: O.OField, +env: List<&2, Atm<O.C(F)>>, +t: O.C(F), +h: Bnd(~F, env, t), e: PE) -> O.le(~F, O.zero(F), peval(~F, cvs(~F, env), e)):
  match e:
    case PAt{+i}:
      at_cnn(~F, O.lookup(~F, avs(~F, env), i), O.lookup(~F, cvs(~F, env), i), bget(svs(~F, env), i), t, bnd_at(~F, env, t, h, i))
    case PPlus{+p, +q}:
      FO.nonneg_add(~F, peval(~F, cvs(~F, env), p), peval(~F, cvs(~F, env), q), pe_cnn(~F, env, t, h, p), pe_cnn(~F, env, t, h, q))
    case PTimes{+p, +q}:
      FO.mul_nonneg(~F, peval(~F, cvs(~F, env), p), peval(~F, cvs(~F, env), q), pe_cnn(~F, env, t, h, p), pe_cnn(~F, env, t, h, q))

# P at the values is at most P at the bounds
def pe_mono(~F: O.OField, +env: List<&2, Atm<O.C(F)>>, +t: O.C(F), +h: Bnd(~F, env, t), +ht1: O.le(~F, t, O.one(F)), e: PE) -> O.le(~F, peval(~F, avs(~F, env), e), peval(~F, cvs(~F, env), e)):
  match e:
    case PAt{+i}:
      at_le(~F, O.lookup(~F, avs(~F, env), i), O.lookup(~F, cvs(~F, env), i), bget(svs(~F, env), i), t, ht1, bnd_at(~F, env, t, h, i))
    case PPlus{+p, +q}:
      le_add2(~F, peval(~F, avs(~F, env), p), peval(~F, cvs(~F, env), p), peval(~F, avs(~F, env), q), peval(~F, cvs(~F, env), q), pe_mono(~F, env, t, h, ht1, p), pe_mono(~F, env, t, h, ht1, q))
    case PTimes{+p, +q}:
      le_mul2(~F, peval(~F, avs(~F, env), p), peval(~F, cvs(~F, env), p), peval(~F, avs(~F, env), q), peval(~F, cvs(~F, env), q), pe_mono(~F, env, t, h, ht1, p), pe_mono(~F, env, t, h, ht1, q), pe_nn(~F, env, t, h, q), pe_cnn(~F, env, t, h, p))

# With a small atom in every monomial
# -----------------------------------

def lin_add(~F: O.OField, +t: O.C(F), +a1: O.C(F), +a2: O.C(F), +c1: O.C(F), +c2: O.C(F), h1: O.le(~F, a1, O.mul(F, t, c1)), h2: O.le(~F, a2, O.mul(F, t, c2))) -> O.le(~F, O.add(F, a1, a2), O.mul(F, t, O.add(F, c1, c2))):
  le_r(~F, O.add(F, a1, a2), O.add(F, O.mul(F, t, c1), O.mul(F, t, c2)), O.mul(F, t, O.add(F, c1, c2)), FR.fring_eq(~F, [t, c1, c2], E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, {==}), le_add2(~F, a1, O.mul(F, t, c1), a2, O.mul(F, t, c2), h1, h2))

def lin_mul_l(~F: O.OField, +t: O.C(F), +a1: O.C(F), +a2: O.C(F), +c1: O.C(F), +c2: O.C(F), h1: O.le(~F, a1, O.mul(F, t, c1)), h2: O.le(~F, a2, c2), ha2: O.le(~F, O.zero(F), a2), hc1: O.le(~F, O.zero(F), c1), ht0: O.le(~F, O.zero(F), t)) -> O.le(~F, O.mul(F, a1, a2), O.mul(F, t, O.mul(F, c1, c2))):
  le_r(~F, O.mul(F, a1, a2), O.mul(F, O.mul(F, t, c1), c2), O.mul(F, t, O.mul(F, c1, c2)), FR.fring_eq(~F, [t, c1, c2], E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, {==}), le_mul2(~F, a1, O.mul(F, t, c1), a2, c2, h1, h2, ha2, FO.mul_nonneg(~F, t, c1, ht0, hc1)))

def lin_mul_r(~F: O.OField, +t: O.C(F), +a1: O.C(F), +a2: O.C(F), +c1: O.C(F), +c2: O.C(F), h1: O.le(~F, a1, c1), h2: O.le(~F, a2, O.mul(F, t, c2)), ha2: O.le(~F, O.zero(F), a2), hc1: O.le(~F, O.zero(F), c1)) -> O.le(~F, O.mul(F, a1, a2), O.mul(F, t, O.mul(F, c1, c2))):
  le_r(~F, O.mul(F, a1, a2), O.mul(F, c1, O.mul(F, t, c2)), O.mul(F, t, O.mul(F, c1, c2)), FR.fring_eq(~F, [t, c1, c2], E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZMul{E.ZVar{1n}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, {==}), le_mul2(~F, a1, c1, a2, O.mul(F, t, c2), h1, h2, ha2, hc1))


def lin_times(~F: O.OField, +env: List<&2, Atm<O.C(F)>>, +t: O.C(F), +h: Bnd(~F, env, t), +ht0: O.le(~F, O.zero(F), t), +ht1: O.le(~F, t, O.one(F)), +p: PE, +q: PE, b: Bool, eb: {d1(svs(~F, env), p) == b : Bool}, hd: {por(b, d1(svs(~F, env), q)) == True{} : Bool}, ihp: {d1(svs(~F, env), p) == True{} : Bool} -> O.le(~F, peval(~F, avs(~F, env), p), O.mul(F, t, peval(~F, cvs(~F, env), p))), ihq: {d1(svs(~F, env), q) == True{} : Bool} -> O.le(~F, peval(~F, avs(~F, env), q), O.mul(F, t, peval(~F, cvs(~F, env), q)))) -> O.le(~F, O.mul(F, peval(~F, avs(~F, env), p), peval(~F, avs(~F, env), q)), O.mul(F, t, O.mul(F, peval(~F, cvs(~F, env), p), peval(~F, cvs(~F, env), q)))):
  match b:
    case True{}:
      lin_mul_l(~F, t, peval(~F, avs(~F, env), p), peval(~F, avs(~F, env), q), peval(~F, cvs(~F, env), p), peval(~F, cvs(~F, env), q), ihp(eb), pe_mono(~F, env, t, h, ht1, q), pe_nn(~F, env, t, h, q), pe_cnn(~F, env, t, h, p), ht0)
    case False{}:
      lin_mul_r(~F, t, peval(~F, avs(~F, env), p), peval(~F, avs(~F, env), q), peval(~F, cvs(~F, env), p), peval(~F, cvs(~F, env), q), pe_mono(~F, env, t, h, ht1, p), ihq(hd), pe_nn(~F, env, t, h, q), pe_cnn(~F, env, t, h, p))

# every monomial with a small atom: P at the values is at most t times P
# at the bounds
def pe_lin(~F: O.OField, +env: List<&2, Atm<O.C(F)>>, +t: O.C(F), +h: Bnd(~F, env, t), +ht0: O.le(~F, O.zero(F), t), +ht1: O.le(~F, t, O.one(F)), e: PE, +hd: {d1(svs(~F, env), e) == True{} : Bool}) -> O.le(~F, peval(~F, avs(~F, env), e), O.mul(F, t, peval(~F, cvs(~F, env), e))):
  match e:
    case PAt{+i}:
      at_lin(~F, O.lookup(~F, avs(~F, env), i), O.lookup(~F, cvs(~F, env), i), bget(svs(~F, env), i), t, hd, bnd_at(~F, env, t, h, i))
    case PPlus{+p, +q}:
      lin_add(~F, t, peval(~F, avs(~F, env), p), peval(~F, avs(~F, env), q), peval(~F, cvs(~F, env), p), peval(~F, cvs(~F, env), q), pe_lin(~F, env, t, h, ht0, ht1, p, pand_l(d1(svs(~F, env), p), d1(svs(~F, env), q), hd)), pe_lin(~F, env, t, h, ht0, ht1, q, pand_r(d1(svs(~F, env), p), d1(svs(~F, env), q), hd)))
    case PTimes{+p, +q}:
      lin_times(~F, env, t, h, ht0, ht1, p, q, d1(svs(~F, env), p), {==}, hd, hp => pe_lin(~F, env, t, h, ht0, ht1, p, hp), hq => pe_lin(~F, env, t, h, ht0, ht1, q, hq))

# With two small atoms in every monomial
# --------------------------------------

def quad_add(~F: O.OField, +t: O.C(F), +a1: O.C(F), +a2: O.C(F), +c1: O.C(F), +c2: O.C(F), h1: O.le(~F, a1, O.mul(F, t, O.mul(F, t, c1))), h2: O.le(~F, a2, O.mul(F, t, O.mul(F, t, c2)))) -> O.le(~F, O.add(F, a1, a2), O.mul(F, t, O.mul(F, t, O.add(F, c1, c2)))):
  le_r(~F, O.add(F, a1, a2), O.add(F, O.mul(F, t, O.mul(F, t, c1)), O.mul(F, t, O.mul(F, t, c2))), O.mul(F, t, O.mul(F, t, O.add(F, c1, c2))), FR.fring_eq(~F, [t, c1, c2], E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}}, {==}), le_add2(~F, a1, O.mul(F, t, O.mul(F, t, c1)), a2, O.mul(F, t, O.mul(F, t, c2)), h1, h2))

def quad_mul_l(~F: O.OField, +t: O.C(F), +a1: O.C(F), +a2: O.C(F), +c1: O.C(F), +c2: O.C(F), h1: O.le(~F, a1, O.mul(F, t, O.mul(F, t, c1))), h2: O.le(~F, a2, c2), ha2: O.le(~F, O.zero(F), a2), +hc1: O.le(~F, O.zero(F), c1), +ht0: O.le(~F, O.zero(F), t)) -> O.le(~F, O.mul(F, a1, a2), O.mul(F, t, O.mul(F, t, O.mul(F, c1, c2)))):
  le_r(~F, O.mul(F, a1, a2), O.mul(F, O.mul(F, t, O.mul(F, t, c1)), c2), O.mul(F, t, O.mul(F, t, O.mul(F, c1, c2))), FR.fring_eq(~F, [t, c1, c2], E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, E.ZVar{2n}}, {==}), le_mul2(~F, a1, O.mul(F, t, O.mul(F, t, c1)), a2, c2, h1, h2, ha2, FO.mul_nonneg(~F, t, O.mul(F, t, c1), ht0, FO.mul_nonneg(~F, t, c1, ht0, hc1))))

def quad_mul_r(~F: O.OField, +t: O.C(F), +a1: O.C(F), +a2: O.C(F), +c1: O.C(F), +c2: O.C(F), h1: O.le(~F, a1, c1), h2: O.le(~F, a2, O.mul(F, t, O.mul(F, t, c2))), ha2: O.le(~F, O.zero(F), a2), hc1: O.le(~F, O.zero(F), c1)) -> O.le(~F, O.mul(F, a1, a2), O.mul(F, t, O.mul(F, t, O.mul(F, c1, c2)))):
  le_r(~F, O.mul(F, a1, a2), O.mul(F, c1, O.mul(F, t, O.mul(F, t, c2))), O.mul(F, t, O.mul(F, t, O.mul(F, c1, c2))), FR.fring_eq(~F, [t, c1, c2], E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZMul{E.ZVar{1n}, E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}}, {==}), le_mul2(~F, a1, c1, a2, O.mul(F, t, O.mul(F, t, c2)), h1, h2, ha2, hc1))

def quad_mul_b(~F: O.OField, +t: O.C(F), +a1: O.C(F), +a2: O.C(F), +c1: O.C(F), +c2: O.C(F), h1: O.le(~F, a1, O.mul(F, t, c1)), h2: O.le(~F, a2, O.mul(F, t, c2)), ha2: O.le(~F, O.zero(F), a2), hc1: O.le(~F, O.zero(F), c1), ht0: O.le(~F, O.zero(F), t)) -> O.le(~F, O.mul(F, a1, a2), O.mul(F, t, O.mul(F, t, O.mul(F, c1, c2)))):
  le_r(~F, O.mul(F, a1, a2), O.mul(F, O.mul(F, t, c1), O.mul(F, t, c2)), O.mul(F, t, O.mul(F, t, O.mul(F, c1, c2))), FR.fring_eq(~F, [t, c1, c2], E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, {==}), le_mul2(~F, a1, O.mul(F, t, c1), a2, O.mul(F, t, c2), h1, h2, ha2, FO.mul_nonneg(~F, t, c1, ht0, hc1)))

def quad_times2(~F: O.OField, +env: List<&2, Atm<O.C(F)>>, +t: O.C(F), +h: Bnd(~F, env, t), +ht0: O.le(~F, O.zero(F), t), +ht1: O.le(~F, t, O.one(F)), +p: PE, +q: PE, b: Bool, eb: {d2(svs(~F, env), q) == b : Bool}, +hd: {por(b, pand(d1(svs(~F, env), p), d1(svs(~F, env), q))) == True{} : Bool}, ihq: {d2(svs(~F, env), q) == True{} : Bool} -> O.le(~F, peval(~F, avs(~F, env), q), O.mul(F, t, O.mul(F, t, peval(~F, cvs(~F, env), q))))) -> O.le(~F, O.mul(F, peval(~F, avs(~F, env), p), peval(~F, avs(~F, env), q)), O.mul(F, t, O.mul(F, t, O.mul(F, peval(~F, cvs(~F, env), p), peval(~F, cvs(~F, env), q))))):
  match b:
    case True{}:
      quad_mul_r(~F, t, peval(~F, avs(~F, env), p), peval(~F, avs(~F, env), q), peval(~F, cvs(~F, env), p), peval(~F, cvs(~F, env), q), pe_mono(~F, env, t, h, ht1, p), ihq(eb), pe_nn(~F, env, t, h, q), pe_cnn(~F, env, t, h, p))
    case False{}:
      quad_mul_b(~F, t, peval(~F, avs(~F, env), p), peval(~F, avs(~F, env), q), peval(~F, cvs(~F, env), p), peval(~F, cvs(~F, env), q), pe_lin(~F, env, t, h, ht0, ht1, p, pand_l(d1(svs(~F, env), p), d1(svs(~F, env), q), hd)), pe_lin(~F, env, t, h, ht0, ht1, q, pand_r(d1(svs(~F, env), p), d1(svs(~F, env), q), hd)), pe_nn(~F, env, t, h, q), pe_cnn(~F, env, t, h, p), ht0)

def quad_times(~F: O.OField, +env: List<&2, Atm<O.C(F)>>, +t: O.C(F), +h: Bnd(~F, env, t), +ht0: O.le(~F, O.zero(F), t), +ht1: O.le(~F, t, O.one(F)), +p: PE, +q: PE, b: Bool, eb: {d2(svs(~F, env), p) == b : Bool}, hd: {por(b, por(d2(svs(~F, env), q), pand(d1(svs(~F, env), p), d1(svs(~F, env), q)))) == True{} : Bool}, ihp: {d2(svs(~F, env), p) == True{} : Bool} -> O.le(~F, peval(~F, avs(~F, env), p), O.mul(F, t, O.mul(F, t, peval(~F, cvs(~F, env), p)))), ihq: {d2(svs(~F, env), q) == True{} : Bool} -> O.le(~F, peval(~F, avs(~F, env), q), O.mul(F, t, O.mul(F, t, peval(~F, cvs(~F, env), q))))) -> O.le(~F, O.mul(F, peval(~F, avs(~F, env), p), peval(~F, avs(~F, env), q)), O.mul(F, t, O.mul(F, t, O.mul(F, peval(~F, cvs(~F, env), p), peval(~F, cvs(~F, env), q))))):
  match b:
    case True{}:
      quad_mul_l(~F, t, peval(~F, avs(~F, env), p), peval(~F, avs(~F, env), q), peval(~F, cvs(~F, env), p), peval(~F, cvs(~F, env), q), ihp(eb), pe_mono(~F, env, t, h, ht1, q), pe_nn(~F, env, t, h, q), pe_cnn(~F, env, t, h, p), ht0)
    case False{}:
      quad_times2(~F, env, t, h, ht0, ht1, p, q, d2(svs(~F, env), q), {==}, hd, ihq)

# every monomial with two small atoms: P at the values is at most t (t P)
# at the bounds
def pe_quad(~F: O.OField, +env: List<&2, Atm<O.C(F)>>, +t: O.C(F), +h: Bnd(~F, env, t), +ht0: O.le(~F, O.zero(F), t), +ht1: O.le(~F, t, O.one(F)), e: PE, +hd: {d2(svs(~F, env), e) == True{} : Bool}) -> O.le(~F, peval(~F, avs(~F, env), e), O.mul(F, t, O.mul(F, t, peval(~F, cvs(~F, env), e)))):
  match e:
    case PAt{+i}:
      absurd(O.le(~F, O.lookup(~F, avs(~F, env), i), O.mul(F, t, O.mul(F, t, O.lookup(~F, cvs(~F, env), i)))), KA.ft(hd))
    case PPlus{+p, +q}:
      quad_add(~F, t, peval(~F, avs(~F, env), p), peval(~F, avs(~F, env), q), peval(~F, cvs(~F, env), p), peval(~F, cvs(~F, env), q), pe_quad(~F, env, t, h, ht0, ht1, p, pand_l(d2(svs(~F, env), p), d2(svs(~F, env), q), hd)), pe_quad(~F, env, t, h, ht0, ht1, q, pand_r(d2(svs(~F, env), p), d2(svs(~F, env), q), hd)))
    case PTimes{+p, +q}:
      quad_times(~F, env, t, h, ht0, ht1, p, q, d2(svs(~F, env), p), {==}, hd, hp => pe_quad(~F, env, t, h, ht0, ht1, p, hp), hq => pe_quad(~F, env, t, h, ht0, ht1, q, hq))
