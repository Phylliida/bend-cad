# Linear algebra in every ordered field (spec/mat.bend). Matrix-vector
# products compose, distribute over sums and negation and have an
# identity; bounds (|a| <= s, ||v|| <= s) add, negate, multiply and grow.
# Lists are read with trailing zeros, so the identities need no shape
# conditions. Lemmas are stated {target == source}, so a rewrite
# %lemma(..) : P turns the source form into the target form. Each
# inequality is a sum of products of nonnegative quantities, matched to
# the goal by one normalizer call.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO

# Products of vectors
# -------------------

# u . v + w . v = (u + w) . v
def dot_vadd(~F: O.OField, u: M.Vec(~F), w: M.Vec(~F), +v: M.Vec(~F)) -> {O.add(F, M.dot(~F, u, v), M.dot(~F, w, v)) == M.dot(~F, M.vadd(~F, u, w), v) : O.C(F)}:
  match u w v:
    case Nil{} w v:
      FL.zero_add(~F, M.dot(~F, w, v))
    case Con{+a, +us} Nil{} v:
      Equal.sym(O.C(F), M.dot(~F, Con{a, us}, v), O.add(F, M.dot(~F, Con{a, us}, v), O.zero(F)), FL.add_zero(~F, M.dot(~F, Con{a, us}, v)))
    case Con{+a, +us} Con{+b, +ws} Nil{}:
      Equal.sym(O.C(F), O.zero(F), O.add(F, O.zero(F), O.zero(F)), FL.add_zero(~F, O.zero(F)))
    case Con{+a, +us} Con{+b, +ws} Con{+y, +ys}:
      %dot_vadd(~F, us, ws, ys) : {O.add(F, O.add(F, O.mul(F, a, y), M.dot(~F, us, ys)), O.add(F, O.mul(F, b, y), M.dot(~F, ws, ys))) == O.add(F, O.mul(F, O.add(F, a, b), y), _) : O.C(F)}
      FR.fring_eq(~F, [a, b, y, M.dot(~F, us, ys), M.dot(~F, ws, ys)], E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{3n}}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{4n}}}, E.ZAdd{E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZAdd{E.ZVar{3n}, E.ZVar{4n}}}, {==})

# -(u . v) = (-u) . v
def dot_vneg(~F: O.OField, u: M.Vec(~F), +v: M.Vec(~F)) -> {O.neg(F, M.dot(~F, u, v)) == M.dot(~F, M.vneg(~F, u), v) : O.C(F)}:
  match u v:
    case Nil{} v:
      Equal.sym(O.C(F), O.zero(F), O.neg(F, O.zero(F)), FL.neg_zero(~F))
    case Con{+a, +us} Nil{}:
      Equal.sym(O.C(F), O.zero(F), O.neg(F, O.zero(F)), FL.neg_zero(~F))
    case Con{+a, +us} Con{+y, +ys}:
      %dot_vneg(~F, us, ys) : {O.neg(F, O.add(F, O.mul(F, a, y), M.dot(~F, us, ys))) == O.add(F, O.mul(F, O.neg(F, a), y), _) : O.C(F)}
      FR.fring_eq(~F, [a, y, M.dot(~F, us, ys)], E.ZNeg{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}, E.ZAdd{E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZVar{1n}}, E.ZNeg{E.ZVar{2n}}}, {==})

# c (u . v) = (c u) . v
def dot_vscale(~F: O.OField, +c: O.C(F), u: M.Vec(~F), +v: M.Vec(~F)) -> {O.mul(F, c, M.dot(~F, u, v)) == M.dot(~F, M.vscale(~F, c, u), v) : O.C(F)}:
  match u v:
    case Nil{} v:
      Equal.sym(O.C(F), O.zero(F), O.mul(F, c, O.zero(F)), FL.mul_zero(~F, c))
    case Con{+a, +us} Nil{}:
      Equal.sym(O.C(F), O.zero(F), O.mul(F, c, O.zero(F)), FL.mul_zero(~F, c))
    case Con{+a, +us} Con{+y, +ys}:
      %dot_vscale(~F, c, us, ys) : {O.mul(F, c, O.add(F, O.mul(F, a, y), M.dot(~F, us, ys))) == O.add(F, O.mul(F, O.mul(F, c, a), y), _) : O.C(F)}
      FR.fring_eq(~F, [c, a, y, M.dot(~F, us, ys)], E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{3n}}}, E.ZAdd{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}, {==})

# a . (B v) = (a B) . v
def vecmat_dot(~F: O.OField, a: M.Vec(~F), b: M.Mat(~F), +v: M.Vec(~F)) -> {M.dot(~F, a, M.matvec(~F, b, v)) == M.dot(~F, M.vecmat(~F, a, b), v) : O.C(F)}:
  match a b:
    case Nil{} b:
      {==}
    case Con{+x, +xs} Nil{}:
      {==}
    case Con{+x, +xs} Con{+r, +rs}:
      %dot_vadd(~F, M.vscale(~F, x, r), M.vecmat(~F, xs, rs), v) : {O.add(F, O.mul(F, x, M.dot(~F, r, v)), M.dot(~F, xs, M.matvec(~F, rs, v))) == _ : O.C(F)}
      %dot_vscale(~F, x, r, v) : {O.add(F, O.mul(F, x, M.dot(~F, r, v)), M.dot(~F, xs, M.matvec(~F, rs, v))) == O.add(F, _, M.dot(~F, M.vecmat(~F, xs, rs), v)) : O.C(F)}
      %vecmat_dot(~F, xs, rs, v) : {O.add(F, O.mul(F, x, M.dot(~F, r, v)), M.dot(~F, xs, M.matvec(~F, rs, v))) == O.add(F, O.mul(F, x, M.dot(~F, r, v)), _) : O.C(F)}
      {==}

# Products of matrices and vectors
# --------------------------------

# A (B v) = (A B) v
def mat_assoc(~F: O.OField, a: M.Mat(~F), +b: M.Mat(~F), +v: M.Vec(~F)) -> {M.matvec(~F, a, M.matvec(~F, b, v)) == M.matvec(~F, M.matmul(~F, a, b), v) : M.Vec(~F)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %vecmat_dot(~F, r, b, v) : {Con{M.dot(~F, r, M.matvec(~F, b, v)), M.matvec(~F, rs, M.matvec(~F, b, v))} == Con{_, M.matvec(~F, M.matmul(~F, rs, b), v)} : M.Vec(~F)}
      %mat_assoc(~F, rs, b, v) : {Con{M.dot(~F, r, M.matvec(~F, b, v)), M.matvec(~F, rs, M.matvec(~F, b, v))} == Con{M.dot(~F, r, M.matvec(~F, b, v)), _} : M.Vec(~F)}
      {==}

# A v + B v = (A + B) v
def mat_add(~F: O.OField, a: M.Mat(~F), b: M.Mat(~F), +v: M.Vec(~F)) -> {M.vadd(~F, M.matvec(~F, a, v), M.matvec(~F, b, v)) == M.matvec(~F, M.madd(~F, a, b), v) : M.Vec(~F)}:
  match a b:
    case Nil{} b:
      {==}
    case Con{+r, +rs} Nil{}:
      {==}
    case Con{+r, +rs} Con{+t, +ts}:
      %dot_vadd(~F, r, t, v) : {Con{O.add(F, M.dot(~F, r, v), M.dot(~F, t, v)), M.vadd(~F, M.matvec(~F, rs, v), M.matvec(~F, ts, v))} == Con{_, M.matvec(~F, M.madd(~F, rs, ts), v)} : M.Vec(~F)}
      %mat_add(~F, rs, ts, v) : {Con{O.add(F, M.dot(~F, r, v), M.dot(~F, t, v)), M.vadd(~F, M.matvec(~F, rs, v), M.matvec(~F, ts, v))} == Con{O.add(F, M.dot(~F, r, v), M.dot(~F, t, v)), _} : M.Vec(~F)}
      {==}

# -(A v) = (-A) v
def mat_neg(~F: O.OField, a: M.Mat(~F), +v: M.Vec(~F)) -> {M.vneg(~F, M.matvec(~F, a, v)) == M.matvec(~F, M.mneg(~F, a), v) : M.Vec(~F)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %dot_vneg(~F, r, v) : {Con{O.neg(F, M.dot(~F, r, v)), M.vneg(~F, M.matvec(~F, rs, v))} == Con{_, M.matvec(~F, M.mneg(~F, rs), v)} : M.Vec(~F)}
      %mat_neg(~F, rs, v) : {Con{O.neg(F, M.dot(~F, r, v)), M.vneg(~F, M.matvec(~F, rs, v))} == Con{O.neg(F, M.dot(~F, r, v)), _} : M.Vec(~F)}
      {==}

# A ys = (shift A) (y, ys)
def shift_matvec(~F: O.OField, a: M.Mat(~F), +y: O.C(F), +ys: M.Vec(~F)) -> {M.matvec(~F, a, ys) == M.matvec(~F, M.shift(~F, a), Con{y, ys}) : M.Vec(~F)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %FR.fring_eq(~F, [y, M.dot(~F, r, ys)], E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZVar{1n}}, {==}) : {Con{M.dot(~F, r, ys), M.matvec(~F, rs, ys)} == Con{_, M.matvec(~F, M.shift(~F, rs), Con{y, ys})} : M.Vec(~F)}
      %shift_matvec(~F, rs, y, ys) : {Con{M.dot(~F, r, ys), M.matvec(~F, rs, ys)} == Con{M.dot(~F, r, ys), _} : M.Vec(~F)}
      {==}

# v = I v, for the identity of v's length
def mat_ident(~F: O.OField, v: M.Vec(~F)) -> {v == M.matvec(~F, M.ident(~F, M.len(~F, v)), v) : M.Vec(~F)}:
  match v:
    case Nil{}:
      {==}
    case Con{+y, +ys}:
      %shift_matvec(~F, M.ident(~F, M.len(~F, ys)), y, ys) : {Con{y, ys} == Con{O.add(F, O.mul(F, O.one(F), y), O.zero(F)), _} : M.Vec(~F)}
      %mat_ident(~F, ys) : {Con{y, ys} == Con{O.add(F, O.mul(F, O.one(F), y), O.zero(F)), _} : M.Vec(~F)}
      %FR.fring_eq(~F, [y], E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, E.ZCst{S.Z0{}}}, {==}) : {Con{y, ys} == Con{_, ys} : M.Vec(~F)}
      {==}

# Order helpers
# -------------

# nonnegativity moves along b = a
def nn_eq(~F: O.OField, +a: O.C(F), +b: O.C(F), e: {b == a : O.C(F)}, h: O.le(~F, O.zero(F), b)) -> O.le(~F, O.zero(F), a):
  %e : O.le(~F, O.zero(F), _)
  h

# 0 <= x + x gives 0 <= x
def twice_nonneg.go(~F: O.OField, +x: O.C(F), +h: O.le(~F, O.zero(F), O.add(F, x, x)), t: Or(O.lt(F, x, O.zero(F)), Or({x == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), x)))) -> O.le(~F, O.zero(F), x):
  match t:
    case Inl{+l}:
      FO.absurd(O.le(~F, O.zero(F), x), O.lt_irrefl(F)(O.zero(F))(FO.le_lt_trans(~F, O.zero(F), O.add(F, x, x), O.zero(F), h, O.lt_trans(F)(O.add(F, x, x), x, O.zero(F))(FO.lt_subst_r(~F, O.add(F, O.zero(F), x), x, O.add(F, x, x), FL.zero_add(~F, x), O.lt_add(F)(x, O.zero(F), x)(l)))(l))))
    case Inr{Inl{e}}:
      %Equal.sym(O.C(F), x, O.zero(F), e) : O.le(~F, O.zero(F), _)
      FO.le_refl(~F, O.zero(F))
    case Inr{Inr{g}}:
      FO.lt_le(~F, O.zero(F), x, g)

def twice_nonneg(~F: O.OField, +x: O.C(F), +h: O.le(~F, O.zero(F), O.add(F, x, x))) -> O.le(~F, O.zero(F), x):
  twice_nonneg.go(~F, x, h, O.lt_total(F)(x, O.zero(F)))

# s <= t gives 0 <= t - s
def sub_nonneg(~F: O.OField, +s: O.C(F), +t: O.C(F), h: O.le(~F, s, t)) -> O.le(~F, O.zero(F), O.sub(~F, t, s)):
  match h:
    case Inl{l}:
      FO.lt_le(~F, O.zero(F), O.sub(~F, t, s), FO.lt_subst_l(~F, O.add(F, s, O.neg(F, s)), O.zero(F), O.sub(~F, t, s), O.add_neg(F)(s), O.lt_add(F)(s, t, O.neg(F, s))(l)))
    case Inr{e}:
      %e : O.le(~F, O.zero(F), O.sub(~F, _, s))
      nn_eq(~F, O.sub(~F, s, s), O.zero(F), Equal.sym(O.C(F), O.sub(~F, s, s), O.zero(F), O.add_neg(F)(s)), FO.le_refl(~F, O.zero(F)))

# x <= y and 0 <= s give 0 <= y s - x s
def mono_mul(~F: O.OField, +x: O.C(F), +y: O.C(F), +s: O.C(F), h: O.le(~F, x, y), hs: O.le(~F, O.zero(F), s)) -> O.le(~F, O.zero(F), O.sub(~F, O.mul(F, y, s), O.mul(F, x, s))):
  nn_eq(~F, O.sub(~F, O.mul(F, y, s), O.mul(F, x, s)), O.mul(F, O.sub(~F, y, x), s), FR.fring_eq(~F, [x, y, s], E.ZMul{E.ZSub{E.ZVar{1n}, E.ZVar{0n}}, E.ZVar{2n}}, E.ZSub{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, {==}), FO.mul_nonneg(~F, O.sub(~F, y, x), s, sub_nonneg(~F, x, y, h), hs))

# Bounds
# ------

def bnd_add(~F: O.OField, +a: O.C(F), +s: O.C(F), +b: O.C(F), +t: O.C(F), ha: M.bnd(~F, a, s), hb: M.bnd(~F, b, t)) -> M.bnd(~F, O.add(F, a, b), O.add(F, s, t)):
  (h1, h2) = ha
  (h3, h4) = hb
  (nn_eq(~F, O.sub(~F, O.add(F, s, t), O.add(F, a, b)), O.add(F, O.sub(~F, s, a), O.sub(~F, t, b)), FR.fring_eq(~F, [a, s, b, t], E.ZAdd{E.ZSub{E.ZVar{1n}, E.ZVar{0n}}, E.ZSub{E.ZVar{3n}, E.ZVar{2n}}}, E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZVar{3n}}, E.ZAdd{E.ZVar{0n}, E.ZVar{2n}}}, {==}), FO.nonneg_add(~F, O.sub(~F, s, a), O.sub(~F, t, b), h1, h3)),
   nn_eq(~F, O.add(F, O.add(F, s, t), O.add(F, a, b)), O.add(F, O.add(F, s, a), O.add(F, t, b)), FR.fring_eq(~F, [a, s, b, t], E.ZAdd{E.ZAdd{E.ZVar{1n}, E.ZVar{0n}}, E.ZAdd{E.ZVar{3n}, E.ZVar{2n}}}, E.ZAdd{E.ZAdd{E.ZVar{1n}, E.ZVar{3n}}, E.ZAdd{E.ZVar{0n}, E.ZVar{2n}}}, {==}), FO.nonneg_add(~F, O.add(F, s, a), O.add(F, t, b), h2, h4)))

def bnd_neg(~F: O.OField, +a: O.C(F), +s: O.C(F), h: M.bnd(~F, a, s)) -> M.bnd(~F, O.neg(F, a), s):
  (h1, h2) = h
  (nn_eq(~F, O.sub(~F, s, O.neg(F, a)), O.add(F, s, a), FR.fring_eq(~F, [a, s], E.ZAdd{E.ZVar{1n}, E.ZVar{0n}}, E.ZSub{E.ZVar{1n}, E.ZNeg{E.ZVar{0n}}}, {==}), h2), h1)

# |a b| <= s t: twice s t -/+ a b is a sum of products of nonnegatives
def bnd_mul(~F: O.OField, +a: O.C(F), +s: O.C(F), +b: O.C(F), +t: O.C(F), ha: M.bnd(~F, a, s), hb: M.bnd(~F, b, t)) -> M.bnd(~F, O.mul(F, a, b), O.mul(F, s, t)):
  (+h1, +h2) = ha
  (+h3, +h4) = hb
  (twice_nonneg(~F, O.sub(~F, O.mul(F, s, t), O.mul(F, a, b)), nn_eq(~F, O.add(F, O.sub(~F, O.mul(F, s, t), O.mul(F, a, b)), O.sub(~F, O.mul(F, s, t), O.mul(F, a, b))), O.add(F, O.mul(F, O.sub(~F, s, a), O.add(F, t, b)), O.mul(F, O.add(F, s, a), O.sub(~F, t, b))),
      FR.fring_eq(~F, [a, s, b, t], E.ZAdd{E.ZMul{E.ZSub{E.ZVar{1n}, E.ZVar{0n}}, E.ZAdd{E.ZVar{3n}, E.ZVar{2n}}}, E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZVar{0n}}, E.ZSub{E.ZVar{3n}, E.ZVar{2n}}}}, E.ZAdd{E.ZSub{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, E.ZSub{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}}, {==}),
      FO.nonneg_add(~F, O.mul(F, O.sub(~F, s, a), O.add(F, t, b)), O.mul(F, O.add(F, s, a), O.sub(~F, t, b)), FO.mul_nonneg(~F, O.sub(~F, s, a), O.add(F, t, b), h1, h4), FO.mul_nonneg(~F, O.add(F, s, a), O.sub(~F, t, b), h2, h3)))),
   twice_nonneg(~F, O.add(F, O.mul(F, s, t), O.mul(F, a, b)), nn_eq(~F, O.add(F, O.add(F, O.mul(F, s, t), O.mul(F, a, b)), O.add(F, O.mul(F, s, t), O.mul(F, a, b))), O.add(F, O.mul(F, O.sub(~F, s, a), O.sub(~F, t, b)), O.mul(F, O.add(F, s, a), O.add(F, t, b))),
      FR.fring_eq(~F, [a, s, b, t], E.ZAdd{E.ZMul{E.ZSub{E.ZVar{1n}, E.ZVar{0n}}, E.ZSub{E.ZVar{3n}, E.ZVar{2n}}}, E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZVar{0n}}, E.ZAdd{E.ZVar{3n}, E.ZVar{2n}}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}}, {==}),
      FO.nonneg_add(~F, O.mul(F, O.sub(~F, s, a), O.sub(~F, t, b)), O.mul(F, O.add(F, s, a), O.add(F, t, b)), FO.mul_nonneg(~F, O.sub(~F, s, a), O.sub(~F, t, b), h1, h3), FO.mul_nonneg(~F, O.add(F, s, a), O.add(F, t, b), h2, h4)))))

# |a| <= s and 0 <= t - s give |a| <= t
def bnd_mono(~F: O.OField, +a: O.C(F), +s: O.C(F), +t: O.C(F), h: M.bnd(~F, a, s), +d: O.le(~F, O.zero(F), O.sub(~F, t, s))) -> M.bnd(~F, a, t):
  (h1, h2) = h
  (nn_eq(~F, O.sub(~F, t, a), O.add(F, O.sub(~F, t, s), O.sub(~F, s, a)), FR.fring_eq(~F, [a, s, t], E.ZAdd{E.ZSub{E.ZVar{2n}, E.ZVar{1n}}, E.ZSub{E.ZVar{1n}, E.ZVar{0n}}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, {==}), FO.nonneg_add(~F, O.sub(~F, t, s), O.sub(~F, s, a), d, h1)),
   nn_eq(~F, O.add(F, t, a), O.add(F, O.sub(~F, t, s), O.add(F, s, a)), FR.fring_eq(~F, [a, s, t], E.ZAdd{E.ZSub{E.ZVar{2n}, E.ZVar{1n}}, E.ZAdd{E.ZVar{1n}, E.ZVar{0n}}}, E.ZAdd{E.ZVar{2n}, E.ZVar{0n}}, {==}), FO.nonneg_add(~F, O.sub(~F, t, s), O.add(F, s, a), d, h2)))

# |a| <= s gives 0 <= s
def bnd_nonneg(~F: O.OField, +a: O.C(F), +s: O.C(F), h: M.bnd(~F, a, s)) -> O.le(~F, O.zero(F), s):
  (h1, h2) = h
  twice_nonneg(~F, s, nn_eq(~F, O.add(F, s, s), O.add(F, O.sub(~F, s, a), O.add(F, s, a)), FR.fring_eq(~F, [a, s], E.ZAdd{E.ZSub{E.ZVar{1n}, E.ZVar{0n}}, E.ZAdd{E.ZVar{1n}, E.ZVar{0n}}}, E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, {==}), FO.nonneg_add(~F, O.sub(~F, s, a), O.add(F, s, a), h1, h2)))

# |0| <= s for 0 <= s
def bnd_zero(~F: O.OField, +s: O.C(F), +h: O.le(~F, O.zero(F), s)) -> M.bnd(~F, O.zero(F), s):
  (nn_eq(~F, O.sub(~F, s, O.zero(F)), s, FR.fring_eq(~F, [s], E.ZVar{0n}, E.ZSub{E.ZVar{0n}, E.ZCst{S.Z0{}}}, {==}), h), nn_eq(~F, O.add(F, s, O.zero(F)), s, FR.fring_eq(~F, [s], E.ZVar{0n}, E.ZAdd{E.ZVar{0n}, E.ZCst{S.Z0{}}}, {==}), h))

# bounds move along s = t
def bnd_eq(~F: O.OField, +a: O.C(F), +s: O.C(F), +t: O.C(F), e: {s == t : O.C(F)}, h: M.bnd(~F, a, s)) -> M.bnd(~F, a, t):
  %e : M.bnd(~F, a, _)
  h

# Vector bounds
# -------------

def vall_mono(~F: O.OField, v: M.Vec(~F), +s: O.C(F), +t: O.C(F), h: M.vbnd.all(~F, v, s), +d: O.le(~F, O.zero(F), O.sub(~F, t, s))) -> M.vbnd.all(~F, v, t):
  match v:
    case Nil{}:
      Unit{}
    case Con{+x, +xs}:
      (hx, hxs) = h
      (bnd_mono(~F, x, s, t, hx, d), vall_mono(~F, xs, s, t, hxs, d))

def vall_add(~F: O.OField, u: M.Vec(~F), +s: O.C(F), w: M.Vec(~F), +t: O.C(F), hu: M.vbnd.all(~F, u, s), hw: M.vbnd.all(~F, w, t), +hs: O.le(~F, O.zero(F), s), +ht: O.le(~F, O.zero(F), t)) -> M.vbnd.all(~F, M.vadd(~F, u, w), O.add(F, s, t)):
  match u w:
    case Nil{} w:
      vall_mono(~F, w, t, O.add(F, s, t), hw, nn_eq(~F, O.sub(~F, O.add(F, s, t), t), s, FR.fring_eq(~F, [s, t], E.ZVar{0n}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{1n}}, {==}), hs))
    case Con{+x, +xs} Nil{}:
      vall_mono(~F, Con{x, xs}, s, O.add(F, s, t), hu, nn_eq(~F, O.sub(~F, O.add(F, s, t), s), t, FR.fring_eq(~F, [s, t], E.ZVar{1n}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{0n}}, {==}), ht))
    case Con{+x, +xs} Con{+y, +ys}:
      (hx, hxs) = hu
      (hy, hys) = hw
      (bnd_add(~F, x, s, y, t, hx, hy), vall_add(~F, xs, s, ys, t, hxs, hys, hs, ht))

def vall_neg(~F: O.OField, u: M.Vec(~F), +s: O.C(F), h: M.vbnd.all(~F, u, s)) -> M.vbnd.all(~F, M.vneg(~F, u), s):
  match u:
    case Nil{}:
      Unit{}
    case Con{+x, +xs}:
      (hx, hxs) = h
      (bnd_neg(~F, x, s, hx), vall_neg(~F, xs, s, hxs))

def vbnd_add(~F: O.OField, +u: M.Vec(~F), +s: O.C(F), +w: M.Vec(~F), +t: O.C(F), hu: M.vbnd(~F, u, s), hw: M.vbnd(~F, w, t)) -> M.vbnd(~F, M.vadd(~F, u, w), O.add(F, s, t)):
  (+hs, hu2) = hu
  (+ht, hw2) = hw
  (FO.nonneg_add(~F, s, t, hs, ht), vall_add(~F, u, s, w, t, hu2, hw2, hs, ht))

def vbnd_neg(~F: O.OField, +u: M.Vec(~F), +s: O.C(F), h: M.vbnd(~F, u, s)) -> M.vbnd(~F, M.vneg(~F, u), s):
  (hs, hu) = h
  (hs, vall_neg(~F, u, s, hu))

def vbnd_mono(~F: O.OField, +u: M.Vec(~F), +s: O.C(F), +t: O.C(F), h: M.vbnd(~F, u, s), hst: O.le(~F, s, t)) -> M.vbnd(~F, u, t):
  (hs, hu) = h
  +d = sub_nonneg(~F, s, t, hst)
  (nn_eq(~F, t, O.add(F, s, O.sub(~F, t, s)), FR.fring_eq(~F, [s, t], E.ZAdd{E.ZVar{0n}, E.ZSub{E.ZVar{1n}, E.ZVar{0n}}}, E.ZVar{1n}, {==}), FO.nonneg_add(~F, s, O.sub(~F, t, s), hs, d)), vall_mono(~F, u, s, t, hu, d))
