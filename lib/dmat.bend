# Dyadic vectors and matrices mean field ones (spec/mat.bend). ofd is a
# ring map, so each dyadic operation becomes the field operation on the
# images. And the dyadic norms bound: |ofd x| <= ofd |x|, a max is above
# both arguments, and a matrix majorized by B sends a vector of norm s to
# one of norm ||B|| s. Lemmas are stated {target == source}.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./dyadic.bend as LD
import ./qord.bend as LQO
import ./qemb.bend as QE
import ./fmat.bend as FM

# ofd is a ring map
# -----------------

def ofd_add(~F: O.OField, +x: S.D, +y: S.D) -> {O.add(F, M.ofd(~F, x), M.ofd(~F, y)) == M.ofd(~F, S.D.add(x, y)) : O.C(F)}:
  Equal.trans(O.C(F), O.add(F, M.ofd(~F, x), M.ofd(~F, y)), O.ofq(~F, S.Q.add(S.D.toq(x), S.D.toq(y))), M.ofd(~F, S.D.add(x, y)),
    Equal.sym(O.C(F), O.ofq(~F, S.Q.add(S.D.toq(x), S.D.toq(y))), O.add(F, M.ofd(~F, x), M.ofd(~F, y)), QE.ofq_add(~F, S.D.toq(x), S.D.toq(y))),
    Equal.sym(O.C(F), M.ofd(~F, S.D.add(x, y)), O.ofq(~F, S.Q.add(S.D.toq(x), S.D.toq(y))), QE.ofq_eq(~F, S.D.toq(S.D.add(x, y)), S.Q.add(S.D.toq(x), S.D.toq(y)), LD.toq_add(x, y))))

def ofd_mul(~F: O.OField, +x: S.D, +y: S.D) -> {O.mul(F, M.ofd(~F, x), M.ofd(~F, y)) == M.ofd(~F, S.D.mul(x, y)) : O.C(F)}:
  Equal.trans(O.C(F), O.mul(F, M.ofd(~F, x), M.ofd(~F, y)), O.ofq(~F, S.Q.mul(S.D.toq(x), S.D.toq(y))), M.ofd(~F, S.D.mul(x, y)),
    Equal.sym(O.C(F), O.ofq(~F, S.Q.mul(S.D.toq(x), S.D.toq(y))), O.mul(F, M.ofd(~F, x), M.ofd(~F, y)), QE.ofq_mul(~F, S.D.toq(x), S.D.toq(y))),
    Equal.sym(O.C(F), M.ofd(~F, S.D.mul(x, y)), O.ofq(~F, S.Q.mul(S.D.toq(x), S.D.toq(y))), QE.ofq_eq(~F, S.D.toq(S.D.mul(x, y)), S.Q.mul(S.D.toq(x), S.D.toq(y)), LD.toq_mul(x, y))))

def ofd_neg(~F: O.OField, +x: S.D) -> {O.neg(F, M.ofd(~F, x)) == M.ofd(~F, S.D.neg(x)) : O.C(F)}:
  Equal.trans(O.C(F), O.neg(F, M.ofd(~F, x)), O.ofq(~F, S.Q.neg(S.D.toq(x))), M.ofd(~F, S.D.neg(x)),
    Equal.sym(O.C(F), O.ofq(~F, S.Q.neg(S.D.toq(x))), O.neg(F, M.ofd(~F, x)), QE.ofq_neg(~F, S.D.toq(x))),
    Equal.sym(O.C(F), M.ofd(~F, S.D.neg(x)), O.ofq(~F, S.Q.neg(S.D.toq(x))), QE.ofq_eq(~F, S.D.toq(S.D.neg(x)), S.Q.neg(S.D.toq(x)), LD.toq_neg(x))))

def ofd_zero(~F: O.OField) -> {O.zero(F) == M.ofd(~F, M.d0()) : O.C(F)}:
  Equal.sym(O.C(F), M.ofd(~F, M.d0()), O.zero(F), QE.ofq_zero(~F))

def ofd_one(~F: O.OField) -> {O.one(F) == M.ofd(~F, M.d1()) : O.C(F)}:
  Equal.sym(O.C(F), M.ofd(~F, M.d1()), O.one(F), QE.ofq_one(~F))

# Dyadic operations are field operations
# --------------------------------------

def dvadd_ofd(~F: O.OField, u: M.DVec(), w: M.DVec()) -> {M.vadd(~F, M.ofdv(~F, u), M.ofdv(~F, w)) == M.ofdv(~F, M.dvadd(u, w)) : M.Vec(~F)}:
  match u w:
    case Nil{} w:
      {==}
    case Con{+a, +us} Nil{}:
      {==}
    case Con{+a, +us} Con{+b, +ws}:
      %ofd_add(~F, a, b) : {Con{O.add(F, M.ofd(~F, a), M.ofd(~F, b)), M.vadd(~F, M.ofdv(~F, us), M.ofdv(~F, ws))} == Con{_, M.ofdv(~F, M.dvadd(us, ws))} : M.Vec(~F)}
      %dvadd_ofd(~F, us, ws) : {Con{O.add(F, M.ofd(~F, a), M.ofd(~F, b)), M.vadd(~F, M.ofdv(~F, us), M.ofdv(~F, ws))} == Con{O.add(F, M.ofd(~F, a), M.ofd(~F, b)), _} : M.Vec(~F)}
      {==}

def dvneg_ofd(~F: O.OField, u: M.DVec()) -> {M.vneg(~F, M.ofdv(~F, u)) == M.ofdv(~F, M.dvneg(u)) : M.Vec(~F)}:
  match u:
    case Nil{}:
      {==}
    case Con{+a, +us}:
      %ofd_neg(~F, a) : {Con{O.neg(F, M.ofd(~F, a)), M.vneg(~F, M.ofdv(~F, us))} == Con{_, M.ofdv(~F, M.dvneg(us))} : M.Vec(~F)}
      %dvneg_ofd(~F, us) : {Con{O.neg(F, M.ofd(~F, a)), M.vneg(~F, M.ofdv(~F, us))} == Con{O.neg(F, M.ofd(~F, a)), _} : M.Vec(~F)}
      {==}

def dvscale_ofd(~F: O.OField, +c: S.D, u: M.DVec()) -> {M.vscale(~F, M.ofd(~F, c), M.ofdv(~F, u)) == M.ofdv(~F, M.dvscale(c, u)) : M.Vec(~F)}:
  match u:
    case Nil{}:
      {==}
    case Con{+a, +us}:
      %ofd_mul(~F, c, a) : {Con{O.mul(F, M.ofd(~F, c), M.ofd(~F, a)), M.vscale(~F, M.ofd(~F, c), M.ofdv(~F, us))} == Con{_, M.ofdv(~F, M.dvscale(c, us))} : M.Vec(~F)}
      %dvscale_ofd(~F, c, us) : {Con{O.mul(F, M.ofd(~F, c), M.ofd(~F, a)), M.vscale(~F, M.ofd(~F, c), M.ofdv(~F, us))} == Con{O.mul(F, M.ofd(~F, c), M.ofd(~F, a)), _} : M.Vec(~F)}
      {==}

def ddot_ofd(~F: O.OField, a: M.DVec(), v: M.DVec()) -> {M.dot(~F, M.ofdv(~F, a), M.ofdv(~F, v)) == M.ofd(~F, M.ddot(a, v)) : O.C(F)}:
  match a v:
    case Nil{} v:
      ofd_zero(~F)
    case Con{+x, +xs} Nil{}:
      ofd_zero(~F)
    case Con{+x, +xs} Con{+y, +ys}:
      %ofd_add(~F, S.D.mul(x, y), M.ddot(xs, ys)) : {O.add(F, O.mul(F, M.ofd(~F, x), M.ofd(~F, y)), M.dot(~F, M.ofdv(~F, xs), M.ofdv(~F, ys))) == _ : O.C(F)}
      %ofd_mul(~F, x, y) : {O.add(F, O.mul(F, M.ofd(~F, x), M.ofd(~F, y)), M.dot(~F, M.ofdv(~F, xs), M.ofdv(~F, ys))) == O.add(F, _, M.ofd(~F, M.ddot(xs, ys))) : O.C(F)}
      %ddot_ofd(~F, xs, ys) : {O.add(F, O.mul(F, M.ofd(~F, x), M.ofd(~F, y)), M.dot(~F, M.ofdv(~F, xs), M.ofdv(~F, ys))) == O.add(F, O.mul(F, M.ofd(~F, x), M.ofd(~F, y)), _) : O.C(F)}
      {==}

def dmatvec_ofd(~F: O.OField, a: M.DMat(), +v: M.DVec()) -> {M.matvec(~F, M.ofdm(~F, a), M.ofdv(~F, v)) == M.ofdv(~F, M.dmatvec(a, v)) : M.Vec(~F)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %ddot_ofd(~F, r, v) : {Con{M.dot(~F, M.ofdv(~F, r), M.ofdv(~F, v)), M.matvec(~F, M.ofdm(~F, rs), M.ofdv(~F, v))} == Con{_, M.ofdv(~F, M.dmatvec(rs, v))} : M.Vec(~F)}
      %dmatvec_ofd(~F, rs, v) : {Con{M.dot(~F, M.ofdv(~F, r), M.ofdv(~F, v)), M.matvec(~F, M.ofdm(~F, rs), M.ofdv(~F, v))} == Con{M.dot(~F, M.ofdv(~F, r), M.ofdv(~F, v)), _} : M.Vec(~F)}
      {==}

def dvecmat_ofd(~F: O.OField, a: M.DVec(), b: M.DMat()) -> {M.vecmat(~F, M.ofdv(~F, a), M.ofdm(~F, b)) == M.ofdv(~F, M.dvecmat(a, b)) : M.Vec(~F)}:
  match a b:
    case Nil{} b:
      {==}
    case Con{+x, +xs} Nil{}:
      {==}
    case Con{+x, +xs} Con{+r, +rs}:
      %dvadd_ofd(~F, M.dvscale(x, r), M.dvecmat(xs, rs)) : {M.vadd(~F, M.vscale(~F, M.ofd(~F, x), M.ofdv(~F, r)), M.vecmat(~F, M.ofdv(~F, xs), M.ofdm(~F, rs))) == _ : M.Vec(~F)}
      %dvscale_ofd(~F, x, r) : {M.vadd(~F, M.vscale(~F, M.ofd(~F, x), M.ofdv(~F, r)), M.vecmat(~F, M.ofdv(~F, xs), M.ofdm(~F, rs))) == M.vadd(~F, _, M.ofdv(~F, M.dvecmat(xs, rs))) : M.Vec(~F)}
      %dvecmat_ofd(~F, xs, rs) : {M.vadd(~F, M.vscale(~F, M.ofd(~F, x), M.ofdv(~F, r)), M.vecmat(~F, M.ofdv(~F, xs), M.ofdm(~F, rs))) == M.vadd(~F, M.vscale(~F, M.ofd(~F, x), M.ofdv(~F, r)), _) : M.Vec(~F)}
      {==}

def dmatmul_ofd(~F: O.OField, a: M.DMat(), +b: M.DMat()) -> {M.matmul(~F, M.ofdm(~F, a), M.ofdm(~F, b)) == M.ofdm(~F, M.dmatmul(a, b)) : M.Mat(~F)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %dvecmat_ofd(~F, r, b) : {Con{M.vecmat(~F, M.ofdv(~F, r), M.ofdm(~F, b)), M.matmul(~F, M.ofdm(~F, rs), M.ofdm(~F, b))} == Con{_, M.ofdm(~F, M.dmatmul(rs, b))} : M.Mat(~F)}
      %dmatmul_ofd(~F, rs, b) : {Con{M.vecmat(~F, M.ofdv(~F, r), M.ofdm(~F, b)), M.matmul(~F, M.ofdm(~F, rs), M.ofdm(~F, b))} == Con{M.vecmat(~F, M.ofdv(~F, r), M.ofdm(~F, b)), _} : M.Mat(~F)}
      {==}

def dmadd_ofd(~F: O.OField, a: M.DMat(), b: M.DMat()) -> {M.madd(~F, M.ofdm(~F, a), M.ofdm(~F, b)) == M.ofdm(~F, M.dmadd(a, b)) : M.Mat(~F)}:
  match a b:
    case Nil{} b:
      {==}
    case Con{+r, +rs} Nil{}:
      {==}
    case Con{+r, +rs} Con{+t, +ts}:
      %dvadd_ofd(~F, r, t) : {Con{M.vadd(~F, M.ofdv(~F, r), M.ofdv(~F, t)), M.madd(~F, M.ofdm(~F, rs), M.ofdm(~F, ts))} == Con{_, M.ofdm(~F, M.dmadd(rs, ts))} : M.Mat(~F)}
      %dmadd_ofd(~F, rs, ts) : {Con{M.vadd(~F, M.ofdv(~F, r), M.ofdv(~F, t)), M.madd(~F, M.ofdm(~F, rs), M.ofdm(~F, ts))} == Con{M.vadd(~F, M.ofdv(~F, r), M.ofdv(~F, t)), _} : M.Mat(~F)}
      {==}

def dmneg_ofd(~F: O.OField, a: M.DMat()) -> {M.mneg(~F, M.ofdm(~F, a)) == M.ofdm(~F, M.dmneg(a)) : M.Mat(~F)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %dvneg_ofd(~F, r) : {Con{M.vneg(~F, M.ofdv(~F, r)), M.mneg(~F, M.ofdm(~F, rs))} == Con{_, M.ofdm(~F, M.dmneg(rs))} : M.Mat(~F)}
      %dmneg_ofd(~F, rs) : {Con{M.vneg(~F, M.ofdv(~F, r)), M.mneg(~F, M.ofdm(~F, rs))} == Con{M.vneg(~F, M.ofdv(~F, r)), _} : M.Mat(~F)}
      {==}

def dshift_ofd(~F: O.OField, a: M.DMat()) -> {M.shift(~F, M.ofdm(~F, a)) == M.ofdm(~F, M.dshift(a)) : M.Mat(~F)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %ofd_zero(~F) : {Con{Con{O.zero(F), M.ofdv(~F, r)}, M.shift(~F, M.ofdm(~F, rs))} == Con{Con{_, M.ofdv(~F, r)}, M.ofdm(~F, M.dshift(rs))} : M.Mat(~F)}
      %dshift_ofd(~F, rs) : {Con{Con{O.zero(F), M.ofdv(~F, r)}, M.shift(~F, M.ofdm(~F, rs))} == Con{Con{O.zero(F), M.ofdv(~F, r)}, _} : M.Mat(~F)}
      {==}

def dident_ofd(~F: O.OField, n: Nat) -> {M.ident(~F, n) == M.ofdm(~F, M.dident(n)) : M.Mat(~F)}:
  match n:
    case 0n:
      {==}
    case 1n++k:
      %ofd_one(~F) : {Con{[O.one(F)], M.shift(~F, M.ident(~F, k))} == Con{[_], M.ofdm(~F, M.dshift(M.dident(k)))} : M.Mat(~F)}
      %dshift_ofd(~F, M.dident(k)) : {Con{[O.one(F)], M.shift(~F, M.ident(~F, k))} == Con{[O.one(F)], _} : M.Mat(~F)}
      %dident_ofd(~F, k) : {Con{[O.one(F)], M.shift(~F, M.ident(~F, k))} == Con{[O.one(F)], M.shift(~F, _)} : M.Mat(~F)}
      {==}

# Order helpers
# -------------

def le_trans(~F: O.OField, +a: O.C(F), +b: O.C(F), +c: O.C(F), h1: O.le(~F, a, b), h2: O.le(~F, b, c)) -> O.le(~F, a, c):
  match h1:
    case Inl{l}:
      Inl{FO.lt_le_trans(~F, a, b, c, l, h2)}
    case Inr{e}:
      %Equal.sym(O.C(F), a, b, e) : O.le(~F, _, c)
      h2

# 0 < ofd (p / 2^e)
def dpos(~F: O.OField, +p: S.Pos, +e: Nat) -> O.lt(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{p}, e})):
  FO.lt_subst_l(~F, O.ofq(~F, S.Q{S.Z0{}, S.XH{}}), O.zero(F), M.ofd(~F, S.D{S.Zpos{p}, e}), QE.ofq_zero(~F), QE.ofq_lt(~F, S.Q{S.Z0{}, S.XH{}}, S.Q{S.Zpos{p}, S.Pos.pow2(e)}, {==}))

# Absolute values and maxima
# --------------------------

# |ofd x| <= ofd |x|, by the sign of x's mantissa
def dabs_bnd.go(~F: O.OField, m: S.Z, +e: Nat) -> M.bnd(~F, M.ofd(~F, S.D{m, e}), M.ofd(~F, S.D{M.zabs(m), e})):
  match m:
    case S.Z0{}:
      (FM.nn_eq(~F, O.sub(~F, O.mul(F, O.zero(F), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))), O.mul(F, O.zero(F), O.inv(F, O.ofp(~F, S.Pos.pow2(e))))), O.zero(F), FR.fring_eq(~F, [O.inv(F, O.ofp(~F, S.Pos.pow2(e)))], E.ZCst{S.Z0{}}, E.ZSub{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}}, {==}), FO.le_refl(~F, O.zero(F))),
       FM.nn_eq(~F, O.add(F, O.mul(F, O.zero(F), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))), O.mul(F, O.zero(F), O.inv(F, O.ofp(~F, S.Pos.pow2(e))))), O.zero(F), FR.fring_eq(~F, [O.inv(F, O.ofp(~F, S.Pos.pow2(e)))], E.ZCst{S.Z0{}}, E.ZAdd{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}}, {==}), FO.le_refl(~F, O.zero(F))))
    case S.Zpos{+p}:
      +h = FO.lt_le(~F, O.zero(F), O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))), dpos(~F, p, e))
      (FM.nn_eq(~F, O.sub(~F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))), O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e))))), O.zero(F), FR.fring_eq(~F, [O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))], E.ZCst{S.Z0{}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, {==}), FO.le_refl(~F, O.zero(F))),
       FO.nonneg_add(~F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))), O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))), h, h))
    case S.Zneg{+p}:
      +h = FO.lt_le(~F, O.zero(F), O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))), dpos(~F, p, e))
      (FM.nn_eq(~F, O.sub(~F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))), O.mul(F, O.neg(F, O.ofp(~F, p)), O.inv(F, O.ofp(~F, S.Pos.pow2(e))))), O.add(F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))), O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e))))), FR.fring_eq(~F, [O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZVar{1n}}}, {==}), FO.nonneg_add(~F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))), O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))), h, h)),
       FM.nn_eq(~F, O.add(F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))), O.mul(F, O.neg(F, O.ofp(~F, p)), O.inv(F, O.ofp(~F, S.Pos.pow2(e))))), O.zero(F), FR.fring_eq(~F, [O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))], E.ZCst{S.Z0{}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZVar{1n}}}, {==}), FO.le_refl(~F, O.zero(F))))

def dabs_bnd(~F: O.OField, x: S.D) -> M.bnd(~F, M.ofd(~F, x), M.ofd(~F, M.dabs(x))):
  match x:
    case S.D{m, e}:
      dabs_bnd.go(~F, m, e)

def dabs_nonneg(~F: O.OField, +x: S.D) -> O.le(~F, O.zero(F), M.ofd(~F, M.dabs(x))):
  FM.bnd_nonneg(~F, M.ofd(~F, x), M.ofd(~F, M.dabs(x)), dabs_bnd(~F, x))

# a <= max a b and b <= max a b, by the comparison's verdict c
def dmax_l.go(~F: O.OField, c: Cmp, +a: S.D, +b: S.D, e: {S.Q.cmp(S.D.toq(a), S.D.toq(b)) == c : Cmp}) -> O.le(~F, M.ofd(~F, a), M.ofd(~F, M.dmax.go(c, a, b))):
  match c:
    case LT{}:
      FO.lt_le(~F, M.ofd(~F, a), M.ofd(~F, b), QE.ofq_lt(~F, S.D.toq(a), S.D.toq(b), e))
    case EQ{}:
      FO.le_refl(~F, M.ofd(~F, a))
    case GT{}:
      FO.le_refl(~F, M.ofd(~F, a))

def dmax_r.go(~F: O.OField, c: Cmp, +a: S.D, +b: S.D, e: {S.Q.cmp(S.D.toq(a), S.D.toq(b)) == c : Cmp}) -> O.le(~F, M.ofd(~F, b), M.ofd(~F, M.dmax.go(c, a, b))):
  match c:
    case LT{}:
      FO.le_refl(~F, M.ofd(~F, b))
    case EQ{}:
      Inr{Equal.sym(O.C(F), M.ofd(~F, a), M.ofd(~F, b), QE.ofq_eq(~F, S.D.toq(a), S.D.toq(b), LQO.q_cmp_eq(S.D.toq(a), S.D.toq(b), e)))}
    case GT{}:
      FO.lt_le(~F, M.ofd(~F, b), M.ofd(~F, a), QE.ofq_lt(~F, S.D.toq(b), S.D.toq(a), LQO.q_cmp_gt(S.D.toq(a), S.D.toq(b), e)))

def dmax_l(~F: O.OField, +a: S.D, +b: S.D) -> O.le(~F, M.ofd(~F, a), M.ofd(~F, M.dmax(a, b))):
  dmax_l.go(~F, S.Q.cmp(S.D.toq(a), S.D.toq(b)), a, b, {==})

def dmax_r(~F: O.OField, +a: S.D, +b: S.D) -> O.le(~F, M.ofd(~F, b), M.ofd(~F, M.dmax(a, b))):
  dmax_r.go(~F, S.Q.cmp(S.D.toq(a), S.D.toq(b)), a, b, {==})

# Norms are not negative
# ----------------------

def d0_nonneg(~F: O.OField) -> O.le(~F, O.zero(F), M.ofd(~F, M.d0())):
  FM.nn_eq(~F, M.ofd(~F, M.d0()), O.zero(F), ofd_zero(~F), FO.le_refl(~F, O.zero(F)))

def drowabs_nonneg(~F: O.OField, r: M.DVec()) -> O.le(~F, O.zero(F), M.ofd(~F, M.drowabs(r))):
  match r:
    case Nil{}:
      d0_nonneg(~F)
    case Con{+x, +xs}:
      FM.nn_eq(~F, M.ofd(~F, S.D.add(M.dabs(x), M.drowabs(xs))), O.add(F, M.ofd(~F, M.dabs(x)), M.ofd(~F, M.drowabs(xs))), ofd_add(~F, M.dabs(x), M.drowabs(xs)),
        FO.nonneg_add(~F, M.ofd(~F, M.dabs(x)), M.ofd(~F, M.drowabs(xs)), dabs_nonneg(~F, x), drowabs_nonneg(~F, xs)))

def dnorm_nonneg(~F: O.OField, a: M.DMat()) -> O.le(~F, O.zero(F), M.ofd(~F, M.dnorm(a))):
  match a:
    case Nil{}:
      d0_nonneg(~F)
    case Con{+r, +rs}:
      le_trans(~F, O.zero(F), M.ofd(~F, M.dnorm(rs)), M.ofd(~F, M.dmax(M.drowabs(r), M.dnorm(rs))), dnorm_nonneg(~F, rs), dmax_r(~F, M.drowabs(r), M.dnorm(rs)))

def dvnorm_nonneg(~F: O.OField, v: M.DVec()) -> O.le(~F, O.zero(F), M.ofd(~F, M.dvnorm(v))):
  match v:
    case Nil{}:
      d0_nonneg(~F)
    case Con{+x, +xs}:
      le_trans(~F, O.zero(F), M.ofd(~F, M.dabs(x)), M.ofd(~F, M.dmax(M.dabs(x), M.dvnorm(xs))), dabs_nonneg(~F, x), dmax_l(~F, M.dabs(x), M.dvnorm(xs)))

# Bounds through majorants
# ------------------------

# |0| <= ofd(rowabs b) s
def row0(~F: O.OField, +b: M.DVec(), +s: O.C(F), +hs: O.le(~F, O.zero(F), s)) -> M.bnd(~F, O.zero(F), O.mul(F, M.ofd(~F, M.drowabs(b)), s)):
  FM.bnd_zero(~F, O.mul(F, M.ofd(~F, M.drowabs(b)), s), FO.mul_nonneg(~F, M.ofd(~F, M.drowabs(b)), s, drowabs_nonneg(~F, b), hs))

# ofd |c| s + ofd(rowabs cs) s = ofd(rowabs (c, cs)) s
def row_eq(~F: O.OField, +c: S.D, +cs: M.DVec(), +s: O.C(F)) -> {O.add(F, O.mul(F, M.ofd(~F, M.dabs(c)), s), O.mul(F, M.ofd(~F, M.drowabs(cs)), s)) == O.mul(F, M.ofd(~F, M.drowabs(Con{c, cs})), s) : O.C(F)}:
  %ofd_add(~F, M.dabs(c), M.drowabs(cs)) : {O.add(F, O.mul(F, M.ofd(~F, M.dabs(c)), s), O.mul(F, M.ofd(~F, M.drowabs(cs)), s)) == O.mul(F, _, s) : O.C(F)}
  FL.mul_add_r(~F, M.ofd(~F, M.dabs(c)), M.ofd(~F, M.drowabs(cs)), s)

# a row majorized by b, against a vector bounded by s
def row_bnd(~F: O.OField, m: M.Vec(~F), v: M.Vec(~F), b: M.DVec(), +s: O.C(F), hm: M.vmaj(~F, m, b), hv: M.vbnd.all(~F, v, s), +hs: O.le(~F, O.zero(F), s)) -> M.bnd(~F, M.dot(~F, m, v), O.mul(F, M.ofd(~F, M.drowabs(b)), s)):
  match m v b:
    case Nil{} v b:
      row0(~F, b, s, hs)
    case Con{+x, +xs} Nil{} b:
      row0(~F, b, s, hs)
    case Con{+x, +xs} Con{+y, +ys} Nil{}:
      (hx, hxs) = hm
      (hy, hys) = hv
      FM.bnd_eq(~F, O.add(F, O.mul(F, x, y), M.dot(~F, xs, ys)), O.add(F, O.mul(F, O.zero(F), s), O.mul(F, O.mul(F, O.zero(F), O.inv(F, O.one(F))), s)), O.mul(F, O.mul(F, O.zero(F), O.inv(F, O.one(F))), s), FR.fring_eq(~F, [x, y, s, M.dot(~F, xs, ys), O.inv(F, O.one(F))], E.ZAdd{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{2n}}, E.ZMul{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{4n}}, E.ZVar{2n}}}, E.ZMul{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{4n}}, E.ZVar{2n}}, {==}),
        FM.bnd_add(~F, O.mul(F, x, y), O.mul(F, O.zero(F), s), M.dot(~F, xs, ys), O.mul(F, O.mul(F, O.zero(F), O.inv(F, O.one(F))), s), FM.bnd_mul(~F, x, O.zero(F), y, s, hx, hy), row_bnd(~F, xs, ys, Nil{}, s, hxs, hys, hs)))
    case Con{+x, +xs} Con{+y, +ys} Con{+c, +cs}:
      (hx, hxs) = hm
      (hy, hys) = hv
      FM.bnd_eq(~F, O.add(F, O.mul(F, x, y), M.dot(~F, xs, ys)), O.add(F, O.mul(F, M.ofd(~F, M.dabs(c)), s), O.mul(F, M.ofd(~F, M.drowabs(cs)), s)), O.mul(F, M.ofd(~F, M.drowabs(Con{c, cs})), s), row_eq(~F, c, cs, s),
        FM.bnd_add(~F, O.mul(F, x, y), O.mul(F, M.ofd(~F, M.dabs(c)), s), M.dot(~F, xs, ys), O.mul(F, M.ofd(~F, M.drowabs(cs)), s), FM.bnd_mul(~F, x, M.ofd(~F, M.dabs(c)), y, s, hx, hy), row_bnd(~F, xs, ys, cs, s, hxs, hys, hs)))

# the rows of M v, for M majorized by B
def rows_bnd(~F: O.OField, m: M.Mat(~F), b: M.DMat(), +v: M.Vec(~F), +s: O.C(F), hm: M.mmaj(~F, m, b), +hv: M.vbnd.all(~F, v, s), +hs: O.le(~F, O.zero(F), s)) -> M.vbnd.all(~F, M.matvec(~F, m, v), O.mul(F, M.ofd(~F, M.dnorm(b)), s)):
  match m b:
    case Nil{} b:
      Unit{}
    case Con{+r, +rs} Nil{}:
      (hr, hrs) = hm
      (row_bnd(~F, r, v, Nil{}, s, hr, hv, hs), rows_bnd(~F, rs, Nil{}, v, s, hrs, hv, hs))
    case Con{+r, +rs} Con{+t, +ts}:
      (hr, hrs) = hm
      (FM.bnd_mono(~F, M.dot(~F, r, v), O.mul(F, M.ofd(~F, M.drowabs(t)), s), O.mul(F, M.ofd(~F, M.dmax(M.drowabs(t), M.dnorm(ts))), s), row_bnd(~F, r, v, t, s, hr, hv, hs),
         FM.mono_mul(~F, M.ofd(~F, M.drowabs(t)), M.ofd(~F, M.dmax(M.drowabs(t), M.dnorm(ts))), s, dmax_l(~F, M.drowabs(t), M.dnorm(ts)), hs)),
       FM.vall_mono(~F, M.matvec(~F, rs, v), O.mul(F, M.ofd(~F, M.dnorm(ts)), s), O.mul(F, M.ofd(~F, M.dmax(M.drowabs(t), M.dnorm(ts))), s), rows_bnd(~F, rs, ts, v, s, hrs, hv, hs),
         FM.mono_mul(~F, M.ofd(~F, M.dnorm(ts)), M.ofd(~F, M.dmax(M.drowabs(t), M.dnorm(ts))), s, dmax_r(~F, M.drowabs(t), M.dnorm(ts)), hs)))

# ||M v|| <= ||B|| s, for M majorized by B and ||v|| <= s
def maj_matvec(~F: O.OField, +m: M.Mat(~F), +b: M.DMat(), +v: M.Vec(~F), +s: O.C(F), hm: M.mmaj(~F, m, b), hv: M.vbnd(~F, v, s)) -> M.vbnd(~F, M.matvec(~F, m, v), O.mul(F, M.ofd(~F, M.dnorm(b)), s)):
  (+hs, +hv2) = hv
  (FO.mul_nonneg(~F, M.ofd(~F, M.dnorm(b)), s, dnorm_nonneg(~F, b), hs), rows_bnd(~F, m, b, v, s, hm, hv2, hs))

# a dyadic matrix is majorized by itself
def vmaj_ofd(~F: O.OField, r: M.DVec()) -> M.vmaj(~F, M.ofdv(~F, r), r):
  match r:
    case Nil{}:
      Unit{}
    case Con{+x, +xs}:
      (dabs_bnd(~F, x), vmaj_ofd(~F, xs))

def maj_ofd(~F: O.OField, a: M.DMat()) -> M.mmaj(~F, M.ofdm(~F, a), a):
  match a:
    case Nil{}:
      Unit{}
    case Con{+r, +rs}:
      (vmaj_ofd(~F, r), maj_ofd(~F, rs))

# ||ofd v|| <= ofd ||v||
def vall_ofd(~F: O.OField, v: M.DVec()) -> M.vbnd.all(~F, M.ofdv(~F, v), M.ofd(~F, M.dvnorm(v))):
  match v:
    case Nil{}:
      Unit{}
    case Con{+x, +xs}:
      (FM.bnd_mono(~F, M.ofd(~F, x), M.ofd(~F, M.dabs(x)), M.ofd(~F, M.dmax(M.dabs(x), M.dvnorm(xs))), dabs_bnd(~F, x), FM.sub_nonneg(~F, M.ofd(~F, M.dabs(x)), M.ofd(~F, M.dmax(M.dabs(x), M.dvnorm(xs))), dmax_l(~F, M.dabs(x), M.dvnorm(xs)))),
       FM.vall_mono(~F, M.ofdv(~F, xs), M.ofd(~F, M.dvnorm(xs)), M.ofd(~F, M.dmax(M.dabs(x), M.dvnorm(xs))), vall_ofd(~F, xs), FM.sub_nonneg(~F, M.ofd(~F, M.dvnorm(xs)), M.ofd(~F, M.dmax(M.dabs(x), M.dvnorm(xs))), dmax_r(~F, M.dabs(x), M.dvnorm(xs)))))

def vbnd_ofd(~F: O.OField, +v: M.DVec()) -> M.vbnd(~F, M.ofdv(~F, v), M.ofd(~F, M.dvnorm(v))):
  (dvnorm_nonneg(~F, v), vall_ofd(~F, v))
