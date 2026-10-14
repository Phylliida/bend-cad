# Arithmetic in a checker's computing numbers K (spec/knum.bend), and what
# it means in every ordered field F that K maps into. Untrusted: each
# operation comes with a lemma sending it through the map H. Mirrors the
# dyadic copy in spec/mat.bend and lib/dmat.bend, generic over K.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./fmat.bend as FM

# The map's laws, turned to rewrite F's operations into K's
# --------------------------------------------------------

def ez(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>) -> {O.zero(F) == N.emap(K, F, H, N.nzero(K)) : O.C(F)}:
  Equal.sym(O.C(F), N.emap(K, F, H, N.nzero(K)), O.zero(F), N.e_zero(K, F, H))

def eo(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>) -> {O.one(F) == N.emap(K, F, H, N.none(K)) : O.C(F)}:
  Equal.sym(O.C(F), N.emap(K, F, H, N.none(K)), O.one(F), N.e_one(K, F, H))

def ea(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), +b: N.NC(K)) -> {O.add(F, N.emap(K, F, H, a), N.emap(K, F, H, b)) == N.emap(K, F, H, N.nadd(K, a, b)) : O.C(F)}:
  Equal.sym(O.C(F), N.emap(K, F, H, N.nadd(K, a, b)), O.add(F, N.emap(K, F, H, a), N.emap(K, F, H, b)), N.e_add(K, F, H)(a, b))

def em(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), +b: N.NC(K)) -> {O.mul(F, N.emap(K, F, H, a), N.emap(K, F, H, b)) == N.emap(K, F, H, N.nmul(K, a, b)) : O.C(F)}:
  Equal.sym(O.C(F), N.emap(K, F, H, N.nmul(K, a, b)), O.mul(F, N.emap(K, F, H, a), N.emap(K, F, H, b)), N.e_mul(K, F, H)(a, b))

def en(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K)) -> {O.neg(F, N.emap(K, F, H, a)) == N.emap(K, F, H, N.nneg(K, a)) : O.C(F)}:
  Equal.sym(O.C(F), N.emap(K, F, H, N.nneg(K, a)), O.neg(F, N.emap(K, F, H, a)), N.e_neg(K, F, H)(a))

# Scalars
# -------

def ksub(~K: N.Num, a: N.NC(K), b: N.NC(K)) -> N.NC(K):
  N.nadd(K, a, N.nneg(K, b))

def es(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), +b: N.NC(K)) -> {O.sub(~F, N.emap(K, F, H, a), N.emap(K, F, H, b)) == N.emap(K, F, H, ksub(~K, a, b)) : O.C(F)}:
  %ea(~K, ~F, ~H, a, N.nneg(K, b)) : {O.sub(~F, N.emap(K, F, H, a), N.emap(K, F, H, b)) == _ : O.C(F)}
  %en(~K, ~F, ~H, b) : {O.sub(~F, N.emap(K, F, H, a), N.emap(K, F, H, b)) == O.add(F, N.emap(K, F, H, a), _) : O.C(F)}
  {==}

def kabs.go(~K: N.Num, c: Cmp, a: N.NC(K)) -> N.NC(K):
  match c:
    case LT{}:
      N.nneg(K, a)
    case EQ{}:
      a
    case GT{}:
      a

# |a|, by the sign of a
def kabs(~K: N.Num, +a: N.NC(K)) -> N.NC(K):
  kabs.go(~K, N.ncmp(K, a, N.nzero(K)), a)

def kle.go(c: Cmp) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

# a <= b
def kle(~K: N.Num, a: N.NC(K), b: N.NC(K)) -> Bool:
  kle.go(N.ncmp(K, a, b))

def klt.go(c: Cmp) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      False{}
    case GT{}:
      False{}

# a < b
def klt(~K: N.Num, a: N.NC(K), b: N.NC(K)) -> Bool:
  klt.go(N.ncmp(K, a, b))

def band(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      False{}

def ftp(b: Bool) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      Empty

# False is not True
def ft(e: {False{} == True{} : Bool}) -> Empty:
  %e : ftp(_)
  Unit{}

def band_l(a: Bool, +b: Bool, h: {band(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def band_r(a: Bool, +b: Bool, h: {band(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      FO.absurd({b == True{} : Bool}, ft(h))

# Order in F from K's verdicts
# ----------------------------

# a comparison's verdict, read in F
def kcmp_ok(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), +b: N.NC(K), c: Cmp, e: {N.ncmp(K, a, b) == c : Cmp}) -> N.cmeans(F, c, N.emap(K, F, H, a), N.emap(K, F, H, b)):
  %e : N.cmeans(F, _, N.emap(K, F, H, a), N.emap(K, F, H, b))
  N.e_cmp(K, F, H)(a, b)

# |x| <= x when 0 <= x
def bnd_self(~F: O.OField, +x: O.C(F), +h: O.le(~F, O.zero(F), x)) -> M.bnd(~F, x, x):
  (FM.nn_eq(~F, O.sub(~F, x, x), O.zero(F), Equal.sym(O.C(F), O.sub(~F, x, x), O.zero(F), O.add_neg(F)(x)), FO.le_refl(~F, O.zero(F))), FO.nonneg_add(~F, x, x, h, h))

# |x| <= -x when x < 0
def bnd_negself(~F: O.OField, +x: O.C(F), h: O.lt(F, x, O.zero(F))) -> M.bnd(~F, x, O.neg(F, x)):
  +p = FO.lt_le(~F, O.zero(F), O.neg(F, x), FO.neg_pos(~F, x, h))
  (FO.nonneg_add(~F, O.neg(F, x), O.neg(F, x), p, p), FM.nn_eq(~F, O.add(F, O.neg(F, x), x), O.zero(F), Equal.sym(O.C(F), O.add(F, O.neg(F, x), x), O.zero(F), FL.neg_add_l(~F, x)), FO.le_refl(~F, O.zero(F))))

def kabs_bnd.go(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, c: Cmp, +a: N.NC(K), e: {N.ncmp(K, a, N.nzero(K)) == c : Cmp}) -> M.bnd(~F, N.emap(K, F, H, a), N.emap(K, F, H, kabs.go(~K, c, a))):
  match c:
    case LT{}:
      %en(~K, ~F, ~H, a) : M.bnd(~F, N.emap(K, F, H, a), _)
      bnd_negself(~F, N.emap(K, F, H, a), FO.lt_subst_r(~F, N.emap(K, F, H, N.nzero(K)), O.zero(F), N.emap(K, F, H, a), N.e_zero(K, F, H), kcmp_ok(~K, ~F, ~H, a, N.nzero(K), LT{}, e)))
    case EQ{}:
      bnd_self(~F, N.emap(K, F, H, a), Inr{Equal.sym(O.C(F), N.emap(K, F, H, a), O.zero(F), Equal.trans(O.C(F), N.emap(K, F, H, a), N.emap(K, F, H, N.nzero(K)), O.zero(F), kcmp_ok(~K, ~F, ~H, a, N.nzero(K), EQ{}, e), N.e_zero(K, F, H)))})
    case GT{}:
      bnd_self(~F, N.emap(K, F, H, a), Inl{FO.lt_subst_l(~F, N.emap(K, F, H, N.nzero(K)), O.zero(F), N.emap(K, F, H, a), N.e_zero(K, F, H), kcmp_ok(~K, ~F, ~H, a, N.nzero(K), GT{}, e))})

# |H a| <= H |a|
def kabs_bnd(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K)) -> M.bnd(~F, N.emap(K, F, H, a), N.emap(K, F, H, kabs(~K, a))):
  kabs_bnd.go(~K, ~F, ~H, N.ncmp(K, a, N.nzero(K)), a, {==})

def kabs_nonneg(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K)) -> O.le(~F, O.zero(F), N.emap(K, F, H, kabs(~K, a))):
  FM.bnd_nonneg(~F, N.emap(K, F, H, a), N.emap(K, F, H, kabs(~K, a)), kabs_bnd(~K, ~F, ~H, a))

def kle_ok.go(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, c: Cmp, +a: N.NC(K), +b: N.NC(K), e: {N.ncmp(K, a, b) == c : Cmp}, h: {kle.go(c) == True{} : Bool}) -> O.le(~F, N.emap(K, F, H, a), N.emap(K, F, H, b)):
  match c:
    case LT{}:
      Inl{kcmp_ok(~K, ~F, ~H, a, b, LT{}, e)}
    case EQ{}:
      Inr{kcmp_ok(~K, ~F, ~H, a, b, EQ{}, e)}
    case GT{}:
      FO.absurd(O.le(~F, N.emap(K, F, H, a), N.emap(K, F, H, b)), ft(h))

# K says a <= b, so H a <= H b
def kle_ok(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), +b: N.NC(K), h: {kle(~K, a, b) == True{} : Bool}) -> O.le(~F, N.emap(K, F, H, a), N.emap(K, F, H, b)):
  kle_ok.go(~K, ~F, ~H, N.ncmp(K, a, b), a, b, {==}, h)

def klt_ok.go(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, c: Cmp, +a: N.NC(K), +b: N.NC(K), e: {N.ncmp(K, a, b) == c : Cmp}, h: {klt.go(c) == True{} : Bool}) -> O.lt(F, N.emap(K, F, H, a), N.emap(K, F, H, b)):
  match c:
    case LT{}:
      kcmp_ok(~K, ~F, ~H, a, b, LT{}, e)
    case EQ{}:
      FO.absurd(O.lt(F, N.emap(K, F, H, a), N.emap(K, F, H, b)), ft(h))
    case GT{}:
      FO.absurd(O.lt(F, N.emap(K, F, H, a), N.emap(K, F, H, b)), ft(h))

# K says a < b, so H a < H b
def klt_ok(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), +b: N.NC(K), h: {klt(~K, a, b) == True{} : Bool}) -> O.lt(F, N.emap(K, F, H, a), N.emap(K, F, H, b)):
  klt_ok.go(~K, ~F, ~H, N.ncmp(K, a, b), a, b, {==}, h)
