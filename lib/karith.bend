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
import ./fvec.bend as FV
import ../spec/cert.bend as C

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

# Vectors and matrices over K (the generic copy of spec/mat.bend's dyadic
# operations)
# ------------------------------------------------------------------------

def kvadd(~K: N.Num, u: N.KVec(~K), w: N.KVec(~K)) -> N.KVec(~K):
  match u w:
    case Nil{} w:
      w
    case Con{a, us} Nil{}:
      Con{a, us}
    case Con{a, us} Con{b, ws}:
      Con{N.nadd(K, a, b), kvadd(~K, us, ws)}

def kvneg(~K: N.Num, u: N.KVec(~K)) -> N.KVec(~K):
  match u:
    case Nil{}:
      Nil{}
    case Con{a, us}:
      Con{N.nneg(K, a), kvneg(~K, us)}

def kvscale(~K: N.Num, +c: N.NC(K), u: N.KVec(~K)) -> N.KVec(~K):
  match u:
    case Nil{}:
      Nil{}
    case Con{a, us}:
      Con{N.nmul(K, c, a), kvscale(~K, c, us)}

def kdot(~K: N.Num, a: N.KVec(~K), v: N.KVec(~K)) -> N.NC(K):
  match a v:
    case Nil{} v:
      N.nzero(K)
    case Con{x, xs} Nil{}:
      N.nzero(K)
    case Con{x, xs} Con{y, ys}:
      N.nadd(K, N.nmul(K, x, y), kdot(~K, xs, ys))

def kmatvec(~K: N.Num, a: N.KMat(~K), +v: N.KVec(~K)) -> N.KVec(~K):
  match a:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{kdot(~K, r, v), kmatvec(~K, rs, v)}

def kvecmat(~K: N.Num, a: N.KVec(~K), b: N.KMat(~K)) -> N.KVec(~K):
  match a b:
    case Nil{} b:
      Nil{}
    case Con{x, xs} Nil{}:
      Nil{}
    case Con{x, xs} Con{r, rs}:
      kvadd(~K, kvscale(~K, x, r), kvecmat(~K, xs, rs))

def kmatmul(~K: N.Num, a: N.KMat(~K), +b: N.KMat(~K)) -> N.KMat(~K):
  match a:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{kvecmat(~K, r, b), kmatmul(~K, rs, b)}

def kmadd(~K: N.Num, a: N.KMat(~K), b: N.KMat(~K)) -> N.KMat(~K):
  match a b:
    case Nil{} b:
      b
    case Con{r, rs} Nil{}:
      Con{r, rs}
    case Con{r, rs} Con{t, ts}:
      Con{kvadd(~K, r, t), kmadd(~K, rs, ts)}

def kmneg(~K: N.Num, a: N.KMat(~K)) -> N.KMat(~K):
  match a:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{kvneg(~K, r), kmneg(~K, rs)}

def kshift(~K: N.Num, a: N.KMat(~K)) -> N.KMat(~K):
  match a:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{Con{N.nzero(K), r}, kshift(~K, rs)}

def kident(~K: N.Num, n: Nat) -> N.KMat(~K):
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{[N.none(K)], kshift(~K, kident(~K, k))}

# Vector and matrix operations of K are F's
# ------------------------------------------

def kvadd_ofk(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, u: N.KVec(~K), w: N.KVec(~K)) -> {M.vadd(~F, N.ofkv(~K, ~F, ~H, u), N.ofkv(~K, ~F, ~H, w)) == N.ofkv(~K, ~F, ~H, kvadd(~K, u, w)) : M.Vec(~F)}:
  match u w:
    case Nil{} w:
      {==}
    case Con{+a, +us} Nil{}:
      {==}
    case Con{+a, +us} Con{+b, +ws}:
      %ea(~K, ~F, ~H, a, b) : {Con{O.add(F, N.emap(K, F, H, a), N.emap(K, F, H, b)), M.vadd(~F, N.ofkv(~K, ~F, ~H, us), N.ofkv(~K, ~F, ~H, ws))} == Con{_, N.ofkv(~K, ~F, ~H, kvadd(~K, us, ws))} : M.Vec(~F)}
      %kvadd_ofk(~K, ~F, ~H, us, ws) : {Con{O.add(F, N.emap(K, F, H, a), N.emap(K, F, H, b)), M.vadd(~F, N.ofkv(~K, ~F, ~H, us), N.ofkv(~K, ~F, ~H, ws))} == Con{O.add(F, N.emap(K, F, H, a), N.emap(K, F, H, b)), _} : M.Vec(~F)}
      {==}

def kvneg_ofk(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, u: N.KVec(~K)) -> {M.vneg(~F, N.ofkv(~K, ~F, ~H, u)) == N.ofkv(~K, ~F, ~H, kvneg(~K, u)) : M.Vec(~F)}:
  match u:
    case Nil{}:
      {==}
    case Con{+a, +us}:
      %en(~K, ~F, ~H, a) : {Con{O.neg(F, N.emap(K, F, H, a)), M.vneg(~F, N.ofkv(~K, ~F, ~H, us))} == Con{_, N.ofkv(~K, ~F, ~H, kvneg(~K, us))} : M.Vec(~F)}
      %kvneg_ofk(~K, ~F, ~H, us) : {Con{O.neg(F, N.emap(K, F, H, a)), M.vneg(~F, N.ofkv(~K, ~F, ~H, us))} == Con{O.neg(F, N.emap(K, F, H, a)), _} : M.Vec(~F)}
      {==}

def kvscale_ofk(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: N.NC(K), u: N.KVec(~K)) -> {M.vscale(~F, N.emap(K, F, H, c), N.ofkv(~K, ~F, ~H, u)) == N.ofkv(~K, ~F, ~H, kvscale(~K, c, u)) : M.Vec(~F)}:
  match u:
    case Nil{}:
      {==}
    case Con{+a, +us}:
      %em(~K, ~F, ~H, c, a) : {Con{O.mul(F, N.emap(K, F, H, c), N.emap(K, F, H, a)), M.vscale(~F, N.emap(K, F, H, c), N.ofkv(~K, ~F, ~H, us))} == Con{_, N.ofkv(~K, ~F, ~H, kvscale(~K, c, us))} : M.Vec(~F)}
      %kvscale_ofk(~K, ~F, ~H, c, us) : {Con{O.mul(F, N.emap(K, F, H, c), N.emap(K, F, H, a)), M.vscale(~F, N.emap(K, F, H, c), N.ofkv(~K, ~F, ~H, us))} == Con{O.mul(F, N.emap(K, F, H, c), N.emap(K, F, H, a)), _} : M.Vec(~F)}
      {==}

def kdot_ofk(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, a: N.KVec(~K), v: N.KVec(~K)) -> {M.dot(~F, N.ofkv(~K, ~F, ~H, a), N.ofkv(~K, ~F, ~H, v)) == N.emap(K, F, H, kdot(~K, a, v)) : O.C(F)}:
  match a v:
    case Nil{} v:
      ez(~K, ~F, ~H)
    case Con{+x, +xs} Nil{}:
      ez(~K, ~F, ~H)
    case Con{+x, +xs} Con{+y, +ys}:
      %ea(~K, ~F, ~H, N.nmul(K, x, y), kdot(~K, xs, ys)) : {O.add(F, O.mul(F, N.emap(K, F, H, x), N.emap(K, F, H, y)), M.dot(~F, N.ofkv(~K, ~F, ~H, xs), N.ofkv(~K, ~F, ~H, ys))) == _ : O.C(F)}
      %em(~K, ~F, ~H, x, y) : {O.add(F, O.mul(F, N.emap(K, F, H, x), N.emap(K, F, H, y)), M.dot(~F, N.ofkv(~K, ~F, ~H, xs), N.ofkv(~K, ~F, ~H, ys))) == O.add(F, _, N.emap(K, F, H, kdot(~K, xs, ys))) : O.C(F)}
      %kdot_ofk(~K, ~F, ~H, xs, ys) : {O.add(F, O.mul(F, N.emap(K, F, H, x), N.emap(K, F, H, y)), M.dot(~F, N.ofkv(~K, ~F, ~H, xs), N.ofkv(~K, ~F, ~H, ys))) == O.add(F, O.mul(F, N.emap(K, F, H, x), N.emap(K, F, H, y)), _) : O.C(F)}
      {==}

def kmatvec_ofk(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, a: N.KMat(~K), +v: N.KVec(~K)) -> {M.matvec(~F, N.ofkm(~K, ~F, ~H, a), N.ofkv(~K, ~F, ~H, v)) == N.ofkv(~K, ~F, ~H, kmatvec(~K, a, v)) : M.Vec(~F)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %kdot_ofk(~K, ~F, ~H, r, v) : {Con{M.dot(~F, N.ofkv(~K, ~F, ~H, r), N.ofkv(~K, ~F, ~H, v)), M.matvec(~F, N.ofkm(~K, ~F, ~H, rs), N.ofkv(~K, ~F, ~H, v))} == Con{_, N.ofkv(~K, ~F, ~H, kmatvec(~K, rs, v))} : M.Vec(~F)}
      %kmatvec_ofk(~K, ~F, ~H, rs, v) : {Con{M.dot(~F, N.ofkv(~K, ~F, ~H, r), N.ofkv(~K, ~F, ~H, v)), M.matvec(~F, N.ofkm(~K, ~F, ~H, rs), N.ofkv(~K, ~F, ~H, v))} == Con{M.dot(~F, N.ofkv(~K, ~F, ~H, r), N.ofkv(~K, ~F, ~H, v)), _} : M.Vec(~F)}
      {==}

def kvecmat_ofk(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, a: N.KVec(~K), b: N.KMat(~K)) -> {M.vecmat(~F, N.ofkv(~K, ~F, ~H, a), N.ofkm(~K, ~F, ~H, b)) == N.ofkv(~K, ~F, ~H, kvecmat(~K, a, b)) : M.Vec(~F)}:
  match a b:
    case Nil{} b:
      {==}
    case Con{+x, +xs} Nil{}:
      {==}
    case Con{+x, +xs} Con{+r, +rs}:
      %kvadd_ofk(~K, ~F, ~H, kvscale(~K, x, r), kvecmat(~K, xs, rs)) : {M.vadd(~F, M.vscale(~F, N.emap(K, F, H, x), N.ofkv(~K, ~F, ~H, r)), M.vecmat(~F, N.ofkv(~K, ~F, ~H, xs), N.ofkm(~K, ~F, ~H, rs))) == _ : M.Vec(~F)}
      %kvscale_ofk(~K, ~F, ~H, x, r) : {M.vadd(~F, M.vscale(~F, N.emap(K, F, H, x), N.ofkv(~K, ~F, ~H, r)), M.vecmat(~F, N.ofkv(~K, ~F, ~H, xs), N.ofkm(~K, ~F, ~H, rs))) == M.vadd(~F, _, N.ofkv(~K, ~F, ~H, kvecmat(~K, xs, rs))) : M.Vec(~F)}
      %kvecmat_ofk(~K, ~F, ~H, xs, rs) : {M.vadd(~F, M.vscale(~F, N.emap(K, F, H, x), N.ofkv(~K, ~F, ~H, r)), M.vecmat(~F, N.ofkv(~K, ~F, ~H, xs), N.ofkm(~K, ~F, ~H, rs))) == M.vadd(~F, M.vscale(~F, N.emap(K, F, H, x), N.ofkv(~K, ~F, ~H, r)), _) : M.Vec(~F)}
      {==}

def kmatmul_ofk(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, a: N.KMat(~K), +b: N.KMat(~K)) -> {M.matmul(~F, N.ofkm(~K, ~F, ~H, a), N.ofkm(~K, ~F, ~H, b)) == N.ofkm(~K, ~F, ~H, kmatmul(~K, a, b)) : M.Mat(~F)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %kvecmat_ofk(~K, ~F, ~H, r, b) : {Con{M.vecmat(~F, N.ofkv(~K, ~F, ~H, r), N.ofkm(~K, ~F, ~H, b)), M.matmul(~F, N.ofkm(~K, ~F, ~H, rs), N.ofkm(~K, ~F, ~H, b))} == Con{_, N.ofkm(~K, ~F, ~H, kmatmul(~K, rs, b))} : M.Mat(~F)}
      %kmatmul_ofk(~K, ~F, ~H, rs, b) : {Con{M.vecmat(~F, N.ofkv(~K, ~F, ~H, r), N.ofkm(~K, ~F, ~H, b)), M.matmul(~F, N.ofkm(~K, ~F, ~H, rs), N.ofkm(~K, ~F, ~H, b))} == Con{M.vecmat(~F, N.ofkv(~K, ~F, ~H, r), N.ofkm(~K, ~F, ~H, b)), _} : M.Mat(~F)}
      {==}

def kmadd_ofk(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, a: N.KMat(~K), b: N.KMat(~K)) -> {M.madd(~F, N.ofkm(~K, ~F, ~H, a), N.ofkm(~K, ~F, ~H, b)) == N.ofkm(~K, ~F, ~H, kmadd(~K, a, b)) : M.Mat(~F)}:
  match a b:
    case Nil{} b:
      {==}
    case Con{+r, +rs} Nil{}:
      {==}
    case Con{+r, +rs} Con{+t, +ts}:
      %kvadd_ofk(~K, ~F, ~H, r, t) : {Con{M.vadd(~F, N.ofkv(~K, ~F, ~H, r), N.ofkv(~K, ~F, ~H, t)), M.madd(~F, N.ofkm(~K, ~F, ~H, rs), N.ofkm(~K, ~F, ~H, ts))} == Con{_, N.ofkm(~K, ~F, ~H, kmadd(~K, rs, ts))} : M.Mat(~F)}
      %kmadd_ofk(~K, ~F, ~H, rs, ts) : {Con{M.vadd(~F, N.ofkv(~K, ~F, ~H, r), N.ofkv(~K, ~F, ~H, t)), M.madd(~F, N.ofkm(~K, ~F, ~H, rs), N.ofkm(~K, ~F, ~H, ts))} == Con{M.vadd(~F, N.ofkv(~K, ~F, ~H, r), N.ofkv(~K, ~F, ~H, t)), _} : M.Mat(~F)}
      {==}

def kmneg_ofk(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, a: N.KMat(~K)) -> {M.mneg(~F, N.ofkm(~K, ~F, ~H, a)) == N.ofkm(~K, ~F, ~H, kmneg(~K, a)) : M.Mat(~F)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %kvneg_ofk(~K, ~F, ~H, r) : {Con{M.vneg(~F, N.ofkv(~K, ~F, ~H, r)), M.mneg(~F, N.ofkm(~K, ~F, ~H, rs))} == Con{_, N.ofkm(~K, ~F, ~H, kmneg(~K, rs))} : M.Mat(~F)}
      %kmneg_ofk(~K, ~F, ~H, rs) : {Con{M.vneg(~F, N.ofkv(~K, ~F, ~H, r)), M.mneg(~F, N.ofkm(~K, ~F, ~H, rs))} == Con{M.vneg(~F, N.ofkv(~K, ~F, ~H, r)), _} : M.Mat(~F)}
      {==}

def kshift_ofk(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, a: N.KMat(~K)) -> {M.shift(~F, N.ofkm(~K, ~F, ~H, a)) == N.ofkm(~K, ~F, ~H, kshift(~K, a)) : M.Mat(~F)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %ez(~K, ~F, ~H) : {Con{Con{O.zero(F), N.ofkv(~K, ~F, ~H, r)}, M.shift(~F, N.ofkm(~K, ~F, ~H, rs))} == Con{Con{_, N.ofkv(~K, ~F, ~H, r)}, N.ofkm(~K, ~F, ~H, kshift(~K, rs))} : M.Mat(~F)}
      %kshift_ofk(~K, ~F, ~H, rs) : {Con{Con{O.zero(F), N.ofkv(~K, ~F, ~H, r)}, M.shift(~F, N.ofkm(~K, ~F, ~H, rs))} == Con{Con{O.zero(F), N.ofkv(~K, ~F, ~H, r)}, _} : M.Mat(~F)}
      {==}

def kident_ofk(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, n: Nat) -> {M.ident(~F, n) == N.ofkm(~K, ~F, ~H, kident(~K, n)) : M.Mat(~F)}:
  match n:
    case 0n:
      {==}
    case 1n++k:
      %eo(~K, ~F, ~H) : {Con{[O.one(F)], M.shift(~F, M.ident(~F, k))} == Con{[_], N.ofkm(~K, ~F, ~H, kshift(~K, kident(~K, k)))} : M.Mat(~F)}
      %kshift_ofk(~K, ~F, ~H, kident(~K, k)) : {Con{[O.one(F)], M.shift(~F, M.ident(~F, k))} == Con{[O.one(F)], _} : M.Mat(~F)}
      %kident_ofk(~K, ~F, ~H, k) : {Con{[O.one(F)], M.shift(~F, M.ident(~F, k))} == Con{[O.one(F)], M.shift(~F, _)} : M.Mat(~F)}
      {==}


# More vector helpers for the checker
# -----------------------------------

def kvabs(~K: N.Num, u: N.KVec(~K)) -> N.KVec(~K):
  match u:
    case Nil{}:
      Nil{}
    case Con{a, us}:
      Con{kabs(~K, a), kvabs(~K, us)}

def kmabs(~K: N.Num, a: N.KMat(~K)) -> N.KMat(~K):
  match a:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{kvabs(~K, r), kmabs(~K, rs)}

# u's first n entries (zeros past its end)
def kfit(~K: N.Num, n: Nat, u: N.KVec(~K)) -> N.KVec(~K):
  match n u:
    case 0n u:
      Nil{}
    case 1n+k Nil{}:
      Con{N.nzero(K), kfit(~K, k, Nil{})}
    case 1n+k Con{a, rest}:
      Con{a, kfit(~K, k, rest)}

# u without its first n entries
def kdrop(~K: N.Num, n: Nat, u: N.KVec(~K)) -> N.KVec(~K):
  match n u:
    case 0n u:
      u
    case 1n+k Nil{}:
      Nil{}
    case 1n+k Con{a, rest}:
      kdrop(~K, k, rest)

def kapp(~K: N.Num, u: N.KVec(~K), w: N.KVec(~K)) -> N.KVec(~K):
  match u:
    case Nil{}:
      w
    case Con{a, us}:
      Con{a, kapp(~K, us, w)}

def kones(~K: N.Num, n: Nat) -> N.KVec(~K):
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{N.none(K), kones(~K, k)}

# u_i <= w_i for every i (zeros past each end)
def kvle(~K: N.Num, u: N.KVec(~K), w: N.KVec(~K)) -> Bool:
  match u w:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{b, ws}:
      band(kle(~K, N.nzero(K), b), kvle(~K, Nil{}, ws))
    case Con{a, us} Nil{}:
      band(kle(~K, a, N.nzero(K)), kvle(~K, us, Nil{}))
    case Con{a, us} Con{b, ws}:
      band(kle(~K, a, b), kvle(~K, us, ws))

# u_i < w_i for every i of w (u read with zeros past its end)
def kvlt(~K: N.Num, u: N.KVec(~K), w: N.KVec(~K)) -> Bool:
  match u w:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{b, ws}:
      band(klt(~K, N.nzero(K), b), kvlt(~K, Nil{}, ws))
    case Con{a, us} Nil{}:
      True{}
    case Con{a, us} Con{b, ws}:
      band(klt(~K, a, b), kvlt(~K, us, ws))

# Lengths
# -------

def klen(~K: N.Num, u: N.KVec(~K)) -> Nat:
  match u:
    case Nil{}:
      0n
    case Con{a, us}:
      1n+klen(~K, us)

def nateq(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+j:
      False{}
    case 1n+i 0n:
      False{}
    case 1n+i 1n+j:
      nateq(i, j)

def natle(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n b:
      True{}
    case 1n+i 0n:
      False{}
    case 1n+i 1n+j:
      natle(i, j)

# Vector verdicts in F
# --------------------

def kle0_ok(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +b: N.NC(K), h: {kle(~K, N.nzero(K), b) == True{} : Bool}) -> O.le(~F, O.zero(F), N.emap(K, F, H, b)):
  %N.e_zero(K, F, H) : O.le(~F, _, N.emap(K, F, H, b))
  kle_ok(~K, ~F, ~H, N.nzero(K), b, h)

def kle0r_ok(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), h: {kle(~K, a, N.nzero(K)) == True{} : Bool}) -> O.le(~F, N.emap(K, F, H, a), O.zero(F)):
  %N.e_zero(K, F, H) : O.le(~F, N.emap(K, F, H, a), _)
  kle_ok(~K, ~F, ~H, a, N.nzero(K), h)

# K says u <= w entrywise, so H u <= H w entrywise
def kvle_ok(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, u: N.KVec(~K), w: N.KVec(~K), +h: {kvle(~K, u, w) == True{} : Bool}) -> FV.rle(~F, N.ofkv(~K, ~F, ~H, u), N.ofkv(~K, ~F, ~H, w)):
  match u w:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} Con{+b, +ws}:
      (kle0_ok(~K, ~F, ~H, b, band_l(kle(~K, N.nzero(K), b), kvle(~K, Nil{}, ws), h)), kvle_ok(~K, ~F, ~H, Nil{}, ws, band_r(kle(~K, N.nzero(K), b), kvle(~K, Nil{}, ws), h)))
    case Con{+a, +us} Nil{}:
      (kle0r_ok(~K, ~F, ~H, a, band_l(kle(~K, a, N.nzero(K)), kvle(~K, us, Nil{}), h)), kvle_ok(~K, ~F, ~H, us, Nil{}, band_r(kle(~K, a, N.nzero(K)), kvle(~K, us, Nil{}), h)))
    case Con{+a, +us} Con{+b, +ws}:
      (kle_ok(~K, ~F, ~H, a, b, band_l(kle(~K, a, b), kvle(~K, us, ws), h)), kvle_ok(~K, ~F, ~H, us, ws, band_r(kle(~K, a, b), kvle(~K, us, ws), h)))

# |H a| <= H |a|, entrywise
def kvabs_bnd(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, u: N.KVec(~K)) -> C.rbnd(~F, N.ofkv(~K, ~F, ~H, u), N.ofkv(~K, ~F, ~H, kvabs(~K, u))):
  match u:
    case Nil{}:
      Unit{}
    case Con{+a, us}:
      (kabs_bnd(~K, ~F, ~H, a), kvabs_bnd(~K, ~F, ~H, us))

def kvabs_nn(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, u: N.KVec(~K)) -> FV.rnn(~F, N.ofkv(~K, ~F, ~H, kvabs(~K, u))):
  match u:
    case Nil{}:
      Unit{}
    case Con{+a, us}:
      (kabs_nonneg(~K, ~F, ~H, a), kvabs_nn(~K, ~F, ~H, us))

def kmabs_bnd(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, a: N.KMat(~K)) -> FV.mbnd(~F, N.ofkm(~K, ~F, ~H, a), N.ofkm(~K, ~F, ~H, kmabs(~K, a))):
  match a:
    case Nil{}:
      Unit{}
    case Con{r, rs}:
      (kvabs_bnd(~K, ~F, ~H, r), kmabs_bnd(~K, ~F, ~H, rs))

def kmabs_nn(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, a: N.KMat(~K)) -> FV.mnn(~F, N.ofkm(~K, ~F, ~H, kmabs(~K, a))):
  match a:
    case Nil{}:
      Unit{}
    case Con{r, rs}:
      (kvabs_nn(~K, ~F, ~H, r), kmabs_nn(~K, ~F, ~H, rs))
