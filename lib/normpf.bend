# bend-cad: norms and perturbation, for solve_complete (DESIGN §10.4, C3c).
# Proofs only.
#
# A vector's norm is its largest |entry| (vn, lib/fvec.bend's vmaxabs); a
# matrix's norm over n columns is its largest row sum of |entries| among
# the first n columns (mnorm), so |A v| <= |A| |v| for v of length n
# (mv_n). "J has an inverse of norm at most c" (InvB) is Data: the
# inverse, its n rows and the bound; it gives |v| <= c |J v| as often as
# needed (lowb). Perturbation (pert): if J has such an inverse with bound
# b, and |J' - J| <= d with 2 b d <= 1, then |v| <= 2b |J' v|; so J' is
# injective, hence (lib/gjpf.bend) invertible, and each row of its inverse,
# read against the signs of its own entries, sums to at most 2b in size:
# J' has an inverse of norm at most 2b.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/deriv.bend as DV
import ./karith.bend as KA
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./fmat.bend as FM
import ./fvec.bend as FV
import ./dmat.bend as DM
import ./kball.bend as KB
import ./real.bend as RL
import ./gjpf.bend as GJ

# Norms
# -----

# a vector's norm: its largest |entry|
def vn(~F: O.OField, v: M.Vec(~F)) -> O.C(F):
  FV.vmaxabs(~F, v)

# the sum of |r_j| over j < n
def rowabs(~F: O.OField, r: M.Vec(~F), n: Nat) -> O.C(F):
  match r n:
    case Nil{} 0n:
      O.zero(F)
    case Nil{} 1n+k:
      O.zero(F)
    case Con{x, t} 0n:
      O.zero(F)
    case Con{x, t} 1n+k:
      O.add(F, FV.fabs(~F, x), rowabs(~F, t, k))

def rowabs_nn(~F: O.OField, r: M.Vec(~F), n: Nat) -> O.le(~F, O.zero(F), rowabs(~F, r, n)):
  match r n:
    case Nil{} 0n:
      FO.le_refl(~F, O.zero(F))
    case Nil{} 1n++k:
      FO.le_refl(~F, O.zero(F))
    case Con{+x, +t} 0n:
      FO.le_refl(~F, O.zero(F))
    case Con{+x, +t} 1n++k:
      FO.nonneg_add(~F, FV.fabs(~F, x), rowabs(~F, t, k), FV.fabs_nn(~F, x), rowabs_nn(~F, t, k))

# a matrix's norm over n columns: its largest rowabs
def mnorm(~F: O.OField, a: M.Mat(~F), +n: Nat) -> O.C(F):
  match a:
    case Nil{}:
      O.zero(F)
    case Con{r, t}:
      FV.fmax(~F, rowabs(~F, r, n), mnorm(~F, t, n))

def mnorm_nn(~F: O.OField, a: M.Mat(~F), +n: Nat) -> O.le(~F, O.zero(F), mnorm(~F, a, n)):
  match a:
    case Nil{}:
      FO.le_refl(~F, O.zero(F))
    case Con{+r, +t}:
      DM.le_trans(~F, O.zero(F), rowabs(~F, r, n), FV.fmax(~F, rowabs(~F, r, n), mnorm(~F, t, n)), rowabs_nn(~F, r, n), FV.fmax_l(~F, rowabs(~F, r, n), mnorm(~F, t, n)))

# |0| <= 0 s
def zb(~F: O.OField, +s: O.C(F)) -> M.bnd(~F, O.zero(F), O.mul(F, O.zero(F), s)):
  FM.bnd_eq(~F, O.zero(F), O.zero(F), O.mul(F, O.zero(F), s), Equal.sym(O.C(F), O.mul(F, O.zero(F), s), O.zero(F), FL.zero_mul(~F, s)), FM.bnd_zero(~F, O.zero(F), FO.le_refl(~F, O.zero(F))))

# |r . v| <= rowabs(r, len v) s, for |v_j| <= s
def dot_le(~F: O.OField, r: M.Vec(~F), v: M.Vec(~F), +s: O.C(F), hv: M.vbnd.all(~F, v, s), +hs: O.le(~F, O.zero(F), s)) -> M.bnd(~F, M.dot(~F, r, v), O.mul(F, rowabs(~F, r, M.len(~F, v)), s)):
  match r v:
    case Nil{} Nil{}:
      zb(~F, s)
    case Nil{} Con{+y, +ys}:
      zb(~F, s)
    case Con{+x, +xs} Nil{}:
      zb(~F, s)
    case Con{+x, +xs} Con{+y, +ys}:
      (hy, hys) = hv
      FM.bnd_eq(~F, O.add(F, O.mul(F, x, y), M.dot(~F, xs, ys)), O.add(F, O.mul(F, FV.fabs(~F, x), s), O.mul(F, rowabs(~F, xs, M.len(~F, ys)), s)), O.mul(F, O.add(F, FV.fabs(~F, x), rowabs(~F, xs, M.len(~F, ys))), s), FR.fring_eq(~F, [FV.fabs(~F, x), rowabs(~F, xs, M.len(~F, ys)), s], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, {==}),
        FM.bnd_add(~F, O.mul(F, x, y), O.mul(F, FV.fabs(~F, x), s), M.dot(~F, xs, ys), O.mul(F, rowabs(~F, xs, M.len(~F, ys)), s), FM.bnd_mul(~F, x, FV.fabs(~F, x), y, s, FV.fabs_bnd(~F, x), hy), dot_le(~F, xs, ys, s, hys, hs)))

# |A v| <= mnorm(A, len v) s entrywise, for |v_j| <= s
def mv_le(~F: O.OField, a: M.Mat(~F), +v: M.Vec(~F), +s: O.C(F), +hv: M.vbnd.all(~F, v, s), +hs: O.le(~F, O.zero(F), s)) -> M.vbnd.all(~F, M.matvec(~F, a, v), O.mul(F, mnorm(~F, a, M.len(~F, v)), s)):
  match a:
    case Nil{}:
      Unit{}
    case Con{+r, +t}:
      (FM.bnd_mono(~F, M.dot(~F, r, v), O.mul(F, rowabs(~F, r, M.len(~F, v)), s), O.mul(F, FV.fmax(~F, rowabs(~F, r, M.len(~F, v)), mnorm(~F, t, M.len(~F, v))), s), dot_le(~F, r, v, s, hv, hs), FM.sub_nonneg(~F, O.mul(F, rowabs(~F, r, M.len(~F, v)), s), O.mul(F, FV.fmax(~F, rowabs(~F, r, M.len(~F, v)), mnorm(~F, t, M.len(~F, v))), s), FV.mul_le_r(~F, rowabs(~F, r, M.len(~F, v)), FV.fmax(~F, rowabs(~F, r, M.len(~F, v)), mnorm(~F, t, M.len(~F, v))), s, hs, FV.fmax_l(~F, rowabs(~F, r, M.len(~F, v)), mnorm(~F, t, M.len(~F, v)))))),
       FM.vall_mono(~F, M.matvec(~F, t, v), O.mul(F, mnorm(~F, t, M.len(~F, v)), s), O.mul(F, FV.fmax(~F, rowabs(~F, r, M.len(~F, v)), mnorm(~F, t, M.len(~F, v))), s), mv_le(~F, t, v, s, hv, hs), FM.sub_nonneg(~F, O.mul(F, mnorm(~F, t, M.len(~F, v)), s), O.mul(F, FV.fmax(~F, rowabs(~F, r, M.len(~F, v)), mnorm(~F, t, M.len(~F, v))), s), FV.mul_le_r(~F, mnorm(~F, t, M.len(~F, v)), FV.fmax(~F, rowabs(~F, r, M.len(~F, v)), mnorm(~F, t, M.len(~F, v))), s, hs, FV.fmax_r(~F, rowabs(~F, r, M.len(~F, v)), mnorm(~F, t, M.len(~F, v)))))))

# |A v| <= |A| |v| for v of length n
def mv_n(~F: O.OField, +a: M.Mat(~F), +n: Nat, +v: M.Vec(~F), lv: {M.len(~F, v) == n : Nat}) -> O.le(~F, vn(~F, M.matvec(~F, a, v)), O.mul(F, mnorm(~F, a, n), vn(~F, v))):
  %lv : O.le(~F, vn(~F, M.matvec(~F, a, v)), O.mul(F, mnorm(~F, a, _), vn(~F, v)))
  FV.vmax_lub(~F, M.matvec(~F, a, v), O.mul(F, mnorm(~F, a, M.len(~F, v)), vn(~F, v)), mv_le(~F, a, v, vn(~F, v), FV.vmax_all(~F, v), FV.vmax_nn(~F, v)), FO.mul_nonneg(~F, mnorm(~F, a, M.len(~F, v)), vn(~F, v), mnorm_nn(~F, a, M.len(~F, v)), FV.vmax_nn(~F, v)))

# Inverses of bounded norm
# ------------------------

# J has an inverse with n rows, of norm (over n columns) at most c
def InvB(~F: O.OField, +j: M.Mat(~F), +n: Nat, +c: O.C(F)) -> Data:
  Sigma<&2, &2, M.Mat(~F), z => M.Both(DV.Inverse(~F, j, z, n), M.Both({GJ.nrows(~F, z) == n : Nat}, O.le(~F, mnorm(~F, z, n), c)))>

def lowb.go(~F: O.OField, +j: M.Mat(~F), +n: Nat, +c: O.C(F), +z: M.Mat(~F), hinv: DV.Inverse(~F, j, z, n), +hz: {GJ.nrows(~F, z) == n : Nat}, +hc: O.le(~F, mnorm(~F, z, n), c), +hj: {GJ.nrows(~F, j) == n : Nat}, +v: M.Vec(~F), +lv: {M.len(~F, v) == n : Nat}) -> O.le(~F, vn(~F, v), O.mul(F, c, vn(~F, M.matvec(~F, j, v)))):
  %GJ.inv_l(~F, j, z, n, hinv, hz, v, lv) : O.le(~F, vn(~F, _), O.mul(F, c, vn(~F, M.matvec(~F, j, v))))
  DM.le_trans(~F, vn(~F, M.matvec(~F, z, M.matvec(~F, j, v))), O.mul(F, mnorm(~F, z, n), vn(~F, M.matvec(~F, j, v))), O.mul(F, c, vn(~F, M.matvec(~F, j, v))), mv_n(~F, z, n, M.matvec(~F, j, v), GJ.len_mv(~F, j, n, v, hj)), FV.mul_le_r(~F, mnorm(~F, z, n), c, vn(~F, M.matvec(~F, j, v)), FV.vmax_nn(~F, M.matvec(~F, j, v)), hc))

# |v| <= c |J v| for v of length n
def lowb(~F: O.OField, +j: M.Mat(~F), +n: Nat, +c: O.C(F), h: InvB(~F, j, n, c), +hj: {GJ.nrows(~F, j) == n : Nat}, +v: M.Vec(~F), +lv: {M.len(~F, v) == n : Nat}) -> O.le(~F, vn(~F, v), O.mul(F, c, vn(~F, M.matvec(~F, j, v)))):
  match h:
    case (+z, p):
      match p:
        case (hinv, q):
          match q:
            case (hz, hc):
              lowb.go(~F, j, n, c, z, hinv, hz, hc, hj, v, lv)

# the bound of an inverse is not negative
def invb_nn(~F: O.OField, +j: M.Mat(~F), +n: Nat, +c: O.C(F), h: InvB(~F, j, n, c)) -> O.le(~F, O.zero(F), c):
  match h:
    case (+z, p):
      match p:
        case (hinv, q):
          match q:
            case (hz, hc):
              DM.le_trans(~F, O.zero(F), mnorm(~F, z, n), c, mnorm_nn(~F, z, n), hc)

# Perturbation
# ------------

def one_nn(~F: O.OField) -> O.le(~F, O.zero(F), O.one(F)):
  Inl{O.zero_lt_one(F)}

def cadd(~F: O.OField, +a1: O.C(F), +a2: O.C(F), +b1: O.C(F), +b2: O.C(F), ea: {a1 == a2 : O.C(F)}, eb: {b1 == b2 : O.C(F)}) -> {O.add(F, a1, b1) == O.add(F, a2, b2) : O.C(F)}:
  %ea : {O.add(F, a1, b1) == O.add(F, _, b2) : O.C(F)}
  %eb : {O.add(F, a1, b1) == O.add(F, a1, _) : O.C(F)}
  {==}

def bnd_lo(~F: O.OField, +v: O.C(F), +s: O.C(F), h: M.bnd(~F, v, s)) -> O.le(~F, v, s):
  (h1, h2) = h
  FV.le_of_sub(~F, v, s, h1)

def vh(~F: O.OField, +a: O.C(F), +xs: M.Vec(~F), +s: O.C(F), h: M.vbnd.all(~F, Con{a, xs}, s)) -> M.bnd(~F, a, s):
  (h1, h2) = h
  h1

def vt(~F: O.OField, +a: O.C(F), +xs: M.Vec(~F), +s: O.C(F), h: M.vbnd.all(~F, Con{a, xs}, s)) -> M.vbnd.all(~F, xs, s):
  (h1, h2) = h
  h2

# |-w| <= t gives |w| <= s + t, for 0 <= s
def vneg_bound(~F: O.OField, w: M.Vec(~F), +s: O.C(F), +t: O.C(F), +hs: O.le(~F, O.zero(F), s), h: M.vbnd.all(~F, M.vneg(~F, w), t)) -> M.vbnd.all(~F, w, O.add(F, s, t)):
  match w:
    case Nil{}:
      Unit{}
    case Con{+y, +ys}:
      (h1, h2) = h
      (FM.bnd_mono(~F, y, t, O.add(F, s, t), KB.bnd_val(~F, O.neg(F, O.neg(F, y)), y, t, FL.neg_neg(~F, y), FM.bnd_neg(~F, O.neg(F, y), t, h1)), FM.nn_eq(~F, O.sub(~F, O.add(F, s, t), t), s, FR.fring_eq(~F, [s, t], E.ZVar{0n}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{1n}}, {==}), hs)),
       vneg_bound(~F, ys, s, t, hs, h2))

def vsub_go(~F: O.OField, +x: O.C(F), +y: O.C(F), +s: O.C(F), +t: O.C(F), hx: M.bnd(~F, x, s), hd: M.bnd(~F, O.add(F, x, O.neg(F, y)), t)) -> M.bnd(~F, y, O.add(F, s, t)):
  KB.bnd_val(~F, O.add(F, x, O.neg(F, O.add(F, x, O.neg(F, y)))), y, O.add(F, s, t), FR.fring_eq(~F, [x, y], E.ZAdd{E.ZVar{0n}, E.ZNeg{E.ZAdd{E.ZVar{0n}, E.ZNeg{E.ZVar{1n}}}}}, E.ZVar{1n}, {==}), FM.bnd_add(~F, x, s, O.neg(F, O.add(F, x, O.neg(F, y))), t, hx, FM.bnd_neg(~F, O.add(F, x, O.neg(F, y)), t, hd)))

# |u| <= s and |u - w| <= t give |w| <= s + t (entrywise)
def vsub_bound(~F: O.OField, u: M.Vec(~F), w: M.Vec(~F), +s: O.C(F), +t: O.C(F), +hs: O.le(~F, O.zero(F), s), +hu: M.vbnd.all(~F, u, s), +hd: M.vbnd.all(~F, M.vadd(~F, u, M.vneg(~F, w)), t)) -> M.vbnd.all(~F, w, O.add(F, s, t)):
  match u w:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} Con{+y, +ys}:
      vneg_bound(~F, Con{y, ys}, s, t, hs, hd)
    case Con{+x, +xs} Nil{}:
      Unit{}
    case Con{+x, +xs} Con{+y, +ys}:
      (vsub_go(~F, x, y, s, t, vh(~F, x, xs, s, hu), vh(~F, O.add(F, x, O.neg(F, y)), M.vadd(~F, xs, M.vneg(~F, ys)), t, hd)),
       vsub_bound(~F, xs, ys, s, t, hs, vt(~F, x, xs, s, hu), vt(~F, O.add(F, x, O.neg(F, y)), M.vadd(~F, xs, M.vneg(~F, ys)), t, hd)))

def dmat_eq(~F: O.OField, +j: M.Mat(~F), +j2: M.Mat(~F), +v: M.Vec(~F)) -> {M.vadd(~F, M.matvec(~F, j2, v), M.vneg(~F, M.matvec(~F, j, v))) == M.matvec(~F, M.madd(~F, j2, M.mneg(~F, j)), v) : M.Vec(~F)}:
  %Equal.sym(M.Vec(~F), M.vneg(~F, M.matvec(~F, j, v)), M.matvec(~F, M.mneg(~F, j), v), FM.mat_neg(~F, j, v)) : {M.vadd(~F, M.matvec(~F, j2, v), _) == M.matvec(~F, M.madd(~F, j2, M.mneg(~F, j)), v) : M.Vec(~F)}
  FM.mat_add(~F, j2, M.mneg(~F, j), v)

def dvb.mv(~F: O.OField, +j: M.Mat(~F), +j2: M.Mat(~F), +n: Nat, +v: M.Vec(~F), lv: {M.len(~F, v) == n : Nat}) -> M.vbnd.all(~F, M.matvec(~F, M.madd(~F, j2, M.mneg(~F, j)), v), O.mul(F, mnorm(~F, M.madd(~F, j2, M.mneg(~F, j)), n), vn(~F, v))):
  %lv : M.vbnd.all(~F, M.matvec(~F, M.madd(~F, j2, M.mneg(~F, j)), v), O.mul(F, mnorm(~F, M.madd(~F, j2, M.mneg(~F, j)), _), vn(~F, v)))
  mv_le(~F, M.madd(~F, j2, M.mneg(~F, j)), v, vn(~F, v), FV.vmax_all(~F, v), FV.vmax_nn(~F, v))

# |(J' - J) v| <= d |v|, as J' v - J v
def dvb(~F: O.OField, +j: M.Mat(~F), +j2: M.Mat(~F), +n: Nat, +d: O.C(F), +v: M.Vec(~F), +lv: {M.len(~F, v) == n : Nat}, +hd: O.le(~F, mnorm(~F, M.madd(~F, j2, M.mneg(~F, j)), n), d)) -> M.vbnd.all(~F, M.vadd(~F, M.matvec(~F, j2, v), M.vneg(~F, M.matvec(~F, j, v))), O.mul(F, d, vn(~F, v))):
  %Equal.sym(M.Vec(~F), M.vadd(~F, M.matvec(~F, j2, v), M.vneg(~F, M.matvec(~F, j, v))), M.matvec(~F, M.madd(~F, j2, M.mneg(~F, j)), v), dmat_eq(~F, j, j2, v)) : M.vbnd.all(~F, _, O.mul(F, d, vn(~F, v)))
  FM.vall_mono(~F, M.matvec(~F, M.madd(~F, j2, M.mneg(~F, j)), v), O.mul(F, mnorm(~F, M.madd(~F, j2, M.mneg(~F, j)), n), vn(~F, v)), O.mul(F, d, vn(~F, v)), dvb.mv(~F, j, j2, n, v, lv), FM.sub_nonneg(~F, O.mul(F, mnorm(~F, M.madd(~F, j2, M.mneg(~F, j)), n), vn(~F, v)), O.mul(F, d, vn(~F, v)), FV.mul_le_r(~F, mnorm(~F, M.madd(~F, j2, M.mneg(~F, j)), n), d, vn(~F, v), FV.vmax_nn(~F, v), hd)))

# |J v| <= |J' v| + d |v|
def jv_le(~F: O.OField, +j: M.Mat(~F), +j2: M.Mat(~F), +n: Nat, +d: O.C(F), +v: M.Vec(~F), +lv: {M.len(~F, v) == n : Nat}, +hd: O.le(~F, mnorm(~F, M.madd(~F, j2, M.mneg(~F, j)), n), d)) -> O.le(~F, vn(~F, M.matvec(~F, j, v)), O.add(F, vn(~F, M.matvec(~F, j2, v)), O.mul(F, d, vn(~F, v)))):
  +hd0 = DM.le_trans(~F, O.zero(F), mnorm(~F, M.madd(~F, j2, M.mneg(~F, j)), n), d, mnorm_nn(~F, M.madd(~F, j2, M.mneg(~F, j)), n), hd)
  FV.vmax_lub(~F, M.matvec(~F, j, v), O.add(F, vn(~F, M.matvec(~F, j2, v)), O.mul(F, d, vn(~F, v))),
    vsub_bound(~F, M.matvec(~F, j2, v), M.matvec(~F, j, v), vn(~F, M.matvec(~F, j2, v)), O.mul(F, d, vn(~F, v)), FV.vmax_nn(~F, M.matvec(~F, j2, v)), FV.vmax_all(~F, M.matvec(~F, j2, v)), dvb(~F, j, j2, n, d, v, lv, hd)),
    FO.nonneg_add(~F, vn(~F, M.matvec(~F, j2, v)), O.mul(F, d, vn(~F, v)), FV.vmax_nn(~F, M.matvec(~F, j2, v)), FO.mul_nonneg(~F, d, vn(~F, v), hd0, FV.vmax_nn(~F, v))))


# |v| <= 2b |J' v|, for J with an inverse of norm <= b, |J' - J| <= d and
# 2 b d <= 1
def low2(~F: O.OField, +j: M.Mat(~F), +j2: M.Mat(~F), +n: Nat, +b: O.C(F), +d: O.C(F), +h: InvB(~F, j, n, b), +hj: {GJ.nrows(~F, j) == n : Nat}, +hd: O.le(~F, mnorm(~F, M.madd(~F, j2, M.mneg(~F, j)), n), d), +hbd: O.le(~F, O.add(F, O.mul(F, b, d), O.mul(F, b, d)), O.one(F)), +v: M.Vec(~F), +lv: {M.len(~F, v) == n : Nat}) -> O.le(~F, vn(~F, v), O.mul(F, O.add(F, b, b), vn(~F, M.matvec(~F, j2, v)))):
  +hb = invb_nn(~F, j, n, b, h)
  +s1 = FM.sub_nonneg(~F, vn(~F, v), O.mul(F, b, vn(~F, M.matvec(~F, j, v))), lowb(~F, j, n, b, h, hj, v, lv))
  +s2 = FM.sub_nonneg(~F, vn(~F, M.matvec(~F, j, v)), O.add(F, vn(~F, M.matvec(~F, j2, v)), O.mul(F, d, vn(~F, v))), jv_le(~F, j, j2, n, d, v, lv, hd))
  +s3 = FM.sub_nonneg(~F, O.add(F, O.mul(F, b, d), O.mul(F, b, d)), O.one(F), hbd)
  FV.le_of_sub(~F, vn(~F, v), O.mul(F, O.add(F, b, b), vn(~F, M.matvec(~F, j2, v))), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.add(F, b, b), vn(~F, M.matvec(~F, j2, v))), vn(~F, v)), O.add(F, O.add(F, O.add(F, O.sub(~F, O.mul(F, b, vn(~F, M.matvec(~F, j, v))), vn(~F, v)), O.sub(~F, O.mul(F, b, vn(~F, M.matvec(~F, j, v))), vn(~F, v))), O.mul(F, O.add(F, b, b), O.sub(~F, O.add(F, vn(~F, M.matvec(~F, j2, v)), O.mul(F, d, vn(~F, v))), vn(~F, M.matvec(~F, j, v))))), O.mul(F, vn(~F, v), O.sub(~F, O.one(F), O.add(F, O.mul(F, b, d), O.mul(F, b, d))))), FR.fring_eq(~F, [b, d, vn(~F, v), vn(~F, M.matvec(~F, j2, v)), vn(~F, M.matvec(~F, j, v))], E.ZAdd{E.ZAdd{E.ZAdd{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}, E.ZVar{2n}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}, E.ZVar{2n}}}, E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZSub{E.ZAdd{E.ZVar{3n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZVar{4n}}}}, E.ZMul{E.ZVar{2n}, E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZVar{3n}}, E.ZVar{2n}}, {==}),
    FO.nonneg_add(~F, O.add(F, O.add(F, O.sub(~F, O.mul(F, b, vn(~F, M.matvec(~F, j, v))), vn(~F, v)), O.sub(~F, O.mul(F, b, vn(~F, M.matvec(~F, j, v))), vn(~F, v))), O.mul(F, O.add(F, b, b), O.sub(~F, O.add(F, vn(~F, M.matvec(~F, j2, v)), O.mul(F, d, vn(~F, v))), vn(~F, M.matvec(~F, j, v))))), O.mul(F, vn(~F, v), O.sub(~F, O.one(F), O.add(F, O.mul(F, b, d), O.mul(F, b, d)))),
      FO.nonneg_add(~F, O.add(F, O.sub(~F, O.mul(F, b, vn(~F, M.matvec(~F, j, v))), vn(~F, v)), O.sub(~F, O.mul(F, b, vn(~F, M.matvec(~F, j, v))), vn(~F, v))), O.mul(F, O.add(F, b, b), O.sub(~F, O.add(F, vn(~F, M.matvec(~F, j2, v)), O.mul(F, d, vn(~F, v))), vn(~F, M.matvec(~F, j, v)))), FO.nonneg_add(~F, O.sub(~F, O.mul(F, b, vn(~F, M.matvec(~F, j, v))), vn(~F, v)), O.sub(~F, O.mul(F, b, vn(~F, M.matvec(~F, j, v))), vn(~F, v)), s1, s1), FO.mul_nonneg(~F, O.add(F, b, b), O.sub(~F, O.add(F, vn(~F, M.matvec(~F, j2, v)), O.mul(F, d, vn(~F, v))), vn(~F, M.matvec(~F, j, v))), FO.nonneg_add(~F, b, b, hb, hb), s2)),
      FO.mul_nonneg(~F, vn(~F, v), O.sub(~F, O.one(F), O.add(F, O.mul(F, b, d), O.mul(F, b, d))), FV.vmax_nn(~F, v), s3))))

# Injectivity
# -----------

def vall_zeros(~F: O.OField, n: Nat) -> M.vbnd.all(~F, GJ.zeros(~F, n), O.zero(F)):
  match n:
    case 0n:
      Unit{}
    case 1n+k:
      (FM.bnd_zero(~F, O.zero(F), FO.le_refl(~F, O.zero(F))), vall_zeros(~F, k))

def vn_z(~F: O.OField, +n: Nat) -> O.le(~F, vn(~F, GJ.zeros(~F, n)), O.zero(F)):
  FV.vmax_lub(~F, GJ.zeros(~F, n), O.zero(F), vall_zeros(~F, n), FO.le_refl(~F, O.zero(F)))

def vzero.go(~F: O.OField, +x: O.C(F), +t: M.Vec(~F), ex: {x == O.zero(F) : O.C(F)}, et: {t == GJ.zeros(~F, M.len(~F, t)) : M.Vec(~F)}) -> {Con{x, t} == GJ.zeros(~F, 1n+M.len(~F, t)) : M.Vec(~F)}:
  %Equal.sym(O.C(F), x, O.zero(F), ex) : {Con{_, t} == GJ.zeros(~F, 1n+M.len(~F, t)) : M.Vec(~F)}
  %Equal.sym(M.Vec(~F), t, GJ.zeros(~F, M.len(~F, t)), et) : {Con{O.zero(F), _} == GJ.zeros(~F, 1n+M.len(~F, t)) : M.Vec(~F)}
  {==}

# every |v_i| <= 0: v is zero
def vzero(~F: O.OField, v: M.Vec(~F), h: M.vbnd.all(~F, v, O.zero(F))) -> {v == GJ.zeros(~F, M.len(~F, v)) : M.Vec(~F)}:
  match v:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      (hx, ht) = h
      vzero.go(~F, x, t, RL.bnd0_eq(~F, x, hx), vzero(~F, t, ht))

# J' w = 0 gives w = 0
def inj2(~F: O.OField, +j: M.Mat(~F), +j2: M.Mat(~F), +n: Nat, +b: O.C(F), +d: O.C(F), +h: InvB(~F, j, n, b), +hj: {GJ.nrows(~F, j) == n : Nat}, +hd: O.le(~F, mnorm(~F, M.madd(~F, j2, M.mneg(~F, j)), n), d), +hbd: O.le(~F, O.add(F, O.mul(F, b, d), O.mul(F, b, d)), O.one(F)), +w: M.Vec(~F), +lw: {M.len(~F, w) == n : Nat}, e: {M.matvec(~F, j2, w) == GJ.zeros(~F, n) : M.Vec(~F)}) -> {w == GJ.zeros(~F, n) : M.Vec(~F)}:
  +hb = invb_nn(~F, j, n, b, h)
  %lw : {w == GJ.zeros(~F, _) : M.Vec(~F)}
  vzero(~F, w, FM.vall_mono(~F, w, vn(~F, w), O.zero(F), FV.vmax_all(~F, w), FM.sub_nonneg(~F, vn(~F, w), O.zero(F), DM.le_trans(~F, vn(~F, w), O.mul(F, O.add(F, b, b), vn(~F, GJ.zeros(~F, n))), O.zero(F),
    (%e : O.le(~F, vn(~F, w), O.mul(F, O.add(F, b, b), vn(~F, _)))
      low2(~F, j, j2, n, b, d, h, hj, hd, hbd, w, lw)),
    FV.sle0(~F, O.add(F, b, b), vn(~F, GJ.zeros(~F, n)), FO.nonneg_add(~F, b, b, hb, hb), vn_z(~F, n))))))

# Signs
# -----

def fsgn.go(~F: O.OField, +x: O.C(F), t: Or(O.lt(F, x, O.zero(F)), Or({x == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), x)))) -> O.C(F):
  match t:
    case Inl{l}:
      O.neg(F, O.one(F))
    case Inr{r}:
      O.one(F)

# -1 for x < 0, else 1
def fsgn(~F: O.OField, +x: O.C(F)) -> O.C(F):
  fsgn.go(~F, x, O.lt_total(F)(x, O.zero(F)))

def sgn_mul.go(~F: O.OField, +x: O.C(F), t: Or(O.lt(F, x, O.zero(F)), Or({x == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), x)))) -> {O.mul(F, x, fsgn.go(~F, x, t)) == FV.fabs.go(~F, x, t) : O.C(F)}:
  match t:
    case Inl{l}:
      FR.fring_eq(~F, [x], E.ZMul{E.ZVar{0n}, E.ZNeg{E.ZCst{S.Zpos{S.XH{}}}}}, E.ZNeg{E.ZVar{0n}}, {==})
    case Inr{r}:
      FR.fring_eq(~F, [x], E.ZMul{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{0n}, {==})

# x sgn(x) = |x|
def sgn_mul(~F: O.OField, +x: O.C(F)) -> {O.mul(F, x, fsgn(~F, x)) == FV.fabs(~F, x) : O.C(F)}:
  sgn_mul.go(~F, x, O.lt_total(F)(x, O.zero(F)))

def sgn_bnd.go(~F: O.OField, +x: O.C(F), t: Or(O.lt(F, x, O.zero(F)), Or({x == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), x)))) -> M.bnd(~F, fsgn.go(~F, x, t), O.one(F)):
  match t:
    case Inl{l}:
      FM.bnd_neg(~F, O.one(F), O.one(F), FV.bnd_self(~F, O.one(F), one_nn(~F)))
    case Inr{r}:
      FV.bnd_self(~F, O.one(F), one_nn(~F))

def sgn_bnd(~F: O.OField, +x: O.C(F)) -> M.bnd(~F, fsgn(~F, x), O.one(F)):
  sgn_bnd.go(~F, x, O.lt_total(F)(x, O.zero(F)))

# the signs of r's first n entries (1 past its end)
def sgnv(~F: O.OField, r: M.Vec(~F), n: Nat) -> M.Vec(~F):
  match r n:
    case Nil{} 0n:
      Nil{}
    case Nil{} 1n+k:
      Con{O.one(F), sgnv(~F, Nil{}, k)}
    case Con{x, t} 0n:
      Nil{}
    case Con{x, t} 1n+k:
      Con{fsgn(~F, x), sgnv(~F, t, k)}

def sgnv_len(~F: O.OField, r: M.Vec(~F), n: Nat) -> {M.len(~F, sgnv(~F, r, n)) == n : Nat}:
  match r n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+k:
      Equal.cong(Nat, Nat, z => 1n+z, M.len(~F, sgnv(~F, Nil{}, k)), k, sgnv_len(~F, Nil{}, k))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+k:
      Equal.cong(Nat, Nat, z => 1n+z, M.len(~F, sgnv(~F, t, k)), k, sgnv_len(~F, t, k))

def sgnv_all(~F: O.OField, r: M.Vec(~F), n: Nat) -> M.vbnd.all(~F, sgnv(~F, r, n), O.one(F)):
  match r n:
    case Nil{} 0n:
      Unit{}
    case Nil{} 1n+k:
      (FV.bnd_self(~F, O.one(F), one_nn(~F)), sgnv_all(~F, Nil{}, k))
    case Con{x, t} 0n:
      Unit{}
    case Con{x, t} 1n+k:
      (sgn_bnd(~F, x), sgnv_all(~F, t, k))

def sgnv_vn(~F: O.OField, +r: M.Vec(~F), +n: Nat) -> O.le(~F, vn(~F, sgnv(~F, r, n)), O.one(F)):
  FV.vmax_lub(~F, sgnv(~F, r, n), O.one(F), sgnv_all(~F, r, n), one_nn(~F))

# r read against its signs is rowabs
def sgnv_dot(~F: O.OField, r: M.Vec(~F), n: Nat) -> {M.dot(~F, r, sgnv(~F, r, n)) == rowabs(~F, r, n) : O.C(F)}:
  match r n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+k:
      {==}
    case Con{+x, +t} 0n:
      {==}
    case Con{+x, +t} 1n++k:
      cadd(~F, O.mul(F, x, fsgn(~F, x)), FV.fabs(~F, x), M.dot(~F, t, sgnv(~F, t, k)), rowabs(~F, t, k), sgn_mul(~F, x), sgnv_dot(~F, t, k))

# Rows of an inverse
# ------------------

# a with its first k rows dropped
def mdrop(~F: O.OField, k: Nat, a: M.Mat(~F)) -> M.Mat(~F):
  match k a:
    case 0n Nil{}:
      Nil{}
    case 0n Con{r, t}:
      Con{r, t}
    case 1n+j Nil{}:
      Nil{}
    case 1n+j Con{r, t}:
      mdrop(~F, j, t)

def mdrop0(~F: O.OField, a: M.Mat(~F)) -> {mdrop(~F, 0n, a) == a : M.Mat(~F)}:
  match a:
    case Nil{}:
      {==}
    case Con{r, t}:
      {==}

def mtl(~F: O.OField, m: M.Mat(~F)) -> M.Mat(~F):
  match m:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      t

def mnilp(~F: O.OField, m: M.Mat(~F)) -> Type:
  match m:
    case Nil{}:
      Unit
    case Con{r, t}:
      Empty

def nil_con(~F: O.OField, +r: M.Vec(~F), +t: M.Mat(~F), e: {Nil{} == Con{r, t} : M.Mat(~F)}) -> Empty:
  %e : mnilp(~F, _)
  Unit{}

def drop_succ(~F: O.OField, k: Nat, a: M.Mat(~F), +r: M.Vec(~F), +t: M.Mat(~F), e: {mdrop(~F, k, a) == Con{r, t} : M.Mat(~F)}) -> {mdrop(~F, 1n+k, a) == t : M.Mat(~F)}:
  match k a:
    case 0n Nil{}:
      FO.absurd({Nil{} == t : M.Mat(~F)}, nil_con(~F, r, t, e))
    case 0n Con{+r2, +t2}:
      Equal.trans(M.Mat(~F), mdrop(~F, 0n, t2), t2, t, mdrop0(~F, t2), Equal.cong(M.Mat(~F), M.Mat(~F), m => mtl(~F, m), Con{r2, t2}, Con{r, t}, e))
    case 1n+i Nil{}:
      FO.absurd({Nil{} == t : M.Mat(~F)}, nil_con(~F, r, t, e))
    case 1n+i Con{+r2, +t2}:
      drop_succ(~F, i, t2, r, t, e)

# dropping rows shortens A s
def drop_mv(~F: O.OField, k: Nat, a: M.Mat(~F), +s: M.Vec(~F)) -> O.le(~F, vn(~F, M.matvec(~F, mdrop(~F, k, a), s)), vn(~F, M.matvec(~F, a, s))):
  match k a:
    case 0n Nil{}:
      FO.le_refl(~F, O.zero(F))
    case 0n Con{+r, +t}:
      FO.le_refl(~F, vn(~F, M.matvec(~F, Con{r, t}, s)))
    case 1n++j Nil{}:
      FO.le_refl(~F, O.zero(F))
    case 1n++j Con{+r, +t}:
      DM.le_trans(~F, vn(~F, M.matvec(~F, mdrop(~F, j, t), s)), vn(~F, M.matvec(~F, t, s)), vn(~F, M.matvec(~F, Con{r, t}, s)), drop_mv(~F, j, t, s), FV.fmax_r(~F, FV.fabs(~F, M.dot(~F, r, s)), vn(~F, M.matvec(~F, t, s))))

# every row's rowabs is at most c
def rowsle(~F: O.OField, a: M.Mat(~F), +n: Nat, +c: O.C(F)) -> Data:
  match a:
    case Nil{}:
      Unit
    case Con{r, t}:
      M.Both(O.le(~F, rowabs(~F, r, n), c), rowsle(~F, t, n, c))

def mnorm_lub(~F: O.OField, a: M.Mat(~F), +n: Nat, +c: O.C(F), h: rowsle(~F, a, n, c), +hc: O.le(~F, O.zero(F), c)) -> O.le(~F, mnorm(~F, a, n), c):
  match a:
    case Nil{}:
      hc
    case Con{+r, +t}:
      (h1, h2) = h
      FV.fmax_lub(~F, rowabs(~F, r, n), mnorm(~F, t, n), c, h1, mnorm_lub(~F, t, n, c, h2, hc))

# An inverse from a lower bound
# ------------------------------
# A has an inverse with n rows and |u| <= c |A u| for every u of length n
# (lb, a lemma passed as a template so that it can be used for every row):
# the inverse has norm at most c, read row by row against each row's signs.

# |Z s| <= c for |s| <= 1, Z an inverse of A
def zs_gen(~F: O.OField, ~a: M.Mat(~F), ~n: Nat, ~c: O.C(F), ~lb: @u: M.Vec(~F) -> {M.len(~F, u) == n : Nat} -> O.le(~F, vn(~F, u), O.mul(F, c, vn(~F, M.matvec(~F, a, u)))), +hc: O.le(~F, O.zero(F), c), +ha: {GJ.nrows(~F, a) == n : Nat}, +z: M.Mat(~F), +hinv: DV.Inverse(~F, a, z, n), +hz: {GJ.nrows(~F, z) == n : Nat}, +s: M.Vec(~F), +ls: {M.len(~F, s) == n : Nat}, +hs1: O.le(~F, vn(~F, s), O.one(F))) -> O.le(~F, vn(~F, M.matvec(~F, z, s)), c):
  DM.le_trans(~F, vn(~F, M.matvec(~F, z, s)), O.mul(F, c, vn(~F, s)), c,
    (%GJ.inv_r(~F, a, z, n, hinv, ha, s, ls) : O.le(~F, vn(~F, M.matvec(~F, z, s)), O.mul(F, c, vn(~F, _)))
      lb(M.matvec(~F, z, s), GJ.len_mv(~F, z, n, s, hz))),
    FV.le_rw_r(~F, O.mul(F, c, vn(~F, s)), O.mul(F, c, O.one(F)), c, FR.fring_eq(~F, [c], E.ZMul{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{0n}, {==}), FV.mul_le(~F, c, vn(~F, s), O.one(F), hc, hs1)))

# the row r of Z (r leads its rows from k on) has rowabs <= c
def row_gen(~F: O.OField, ~a: M.Mat(~F), ~n: Nat, ~c: O.C(F), ~lb: @u: M.Vec(~F) -> {M.len(~F, u) == n : Nat} -> O.le(~F, vn(~F, u), O.mul(F, c, vn(~F, M.matvec(~F, a, u)))), +hc: O.le(~F, O.zero(F), c), +ha: {GJ.nrows(~F, a) == n : Nat}, +z: M.Mat(~F), +hinv: DV.Inverse(~F, a, z, n), +hz: {GJ.nrows(~F, z) == n : Nat}, +k: Nat, +r: M.Vec(~F), +t: M.Mat(~F), e: {mdrop(~F, k, z) == Con{r, t} : M.Mat(~F)}) -> O.le(~F, rowabs(~F, r, n), c):
  %sgnv_dot(~F, r, n) : O.le(~F, _, c)
  DM.le_trans(~F, M.dot(~F, r, sgnv(~F, r, n)), vn(~F, M.matvec(~F, Con{r, t}, sgnv(~F, r, n))), c,
    DM.le_trans(~F, M.dot(~F, r, sgnv(~F, r, n)), FV.fabs(~F, M.dot(~F, r, sgnv(~F, r, n))), vn(~F, M.matvec(~F, Con{r, t}, sgnv(~F, r, n))), bnd_lo(~F, M.dot(~F, r, sgnv(~F, r, n)), FV.fabs(~F, M.dot(~F, r, sgnv(~F, r, n))), FV.fabs_bnd(~F, M.dot(~F, r, sgnv(~F, r, n)))), FV.fmax_l(~F, FV.fabs(~F, M.dot(~F, r, sgnv(~F, r, n))), vn(~F, M.matvec(~F, t, sgnv(~F, r, n))))),
    DM.le_trans(~F, vn(~F, M.matvec(~F, Con{r, t}, sgnv(~F, r, n))), vn(~F, M.matvec(~F, z, sgnv(~F, r, n))), c,
      (%e : O.le(~F, vn(~F, M.matvec(~F, _, sgnv(~F, r, n))), vn(~F, M.matvec(~F, z, sgnv(~F, r, n))))
        drop_mv(~F, k, z, sgnv(~F, r, n))),
      zs_gen(~F, ~a, ~n, ~c, ~lb, hc, ha, z, hinv, hz, sgnv(~F, r, n), sgnv_len(~F, r, n), sgnv_vn(~F, r, n))))

# the rows of Z from k on
def rows_gen(~F: O.OField, ~a: M.Mat(~F), ~n: Nat, ~c: O.C(F), ~lb: @u: M.Vec(~F) -> {M.len(~F, u) == n : Nat} -> O.le(~F, vn(~F, u), O.mul(F, c, vn(~F, M.matvec(~F, a, u)))), rest: M.Mat(~F), +hc: O.le(~F, O.zero(F), c), +ha: {GJ.nrows(~F, a) == n : Nat}, +z: M.Mat(~F), +hinv: DV.Inverse(~F, a, z, n), +hz: {GJ.nrows(~F, z) == n : Nat}, +k: Nat, +e: {mdrop(~F, k, z) == rest : M.Mat(~F)}) -> rowsle(~F, rest, n, c):
  match rest:
    case Nil{}:
      Unit{}
    case Con{+r, +t}:
      (row_gen(~F, ~a, ~n, ~c, ~lb, hc, ha, z, hinv, hz, k, r, t, e), rows_gen(~F, ~a, ~n, ~c, ~lb, t, hc, ha, z, hinv, hz, 1n+k, drop_succ(~F, k, z, r, t, e)))

def invb_low.fin(~F: O.OField, ~a: M.Mat(~F), ~n: Nat, ~c: O.C(F), ~lb: @u: M.Vec(~F) -> {M.len(~F, u) == n : Nat} -> O.le(~F, vn(~F, u), O.mul(F, c, vn(~F, M.matvec(~F, a, u)))), +hc: O.le(~F, O.zero(F), c), +ha: {GJ.nrows(~F, a) == n : Nat}, +z: M.Mat(~F), +hinv: DV.Inverse(~F, a, z, n), +hz: {GJ.nrows(~F, z) == n : Nat}) -> InvB(~F, a, n, c):
  (z, (hinv, (hz, mnorm_lub(~F, z, n, c, rows_gen(~F, ~a, ~n, ~c, ~lb, z, hc, ha, z, hinv, hz, 0n, mdrop0(~F, z)), hc))))

# an inverse and |u| <= c |A u| give an inverse of norm at most c
def invb_low(~F: O.OField, ~a: M.Mat(~F), ~n: Nat, ~c: O.C(F), ~lb: @u: M.Vec(~F) -> {M.len(~F, u) == n : Nat} -> O.le(~F, vn(~F, u), O.mul(F, c, vn(~F, M.matvec(~F, a, u)))), +hc: O.le(~F, O.zero(F), c), +ha: {GJ.nrows(~F, a) == n : Nat}, inv: GJ.InvN(~F, a, n)) -> InvB(~F, a, n, c):
  match inv:
    case (z, p):
      match p:
        case (hinv, hz):
          invb_low.fin(~F, ~a, ~n, ~c, ~lb, hc, ha, z, hinv, hz)

# |u| <= c |A u| makes A injective
def inj_low(~F: O.OField, ~a: M.Mat(~F), ~n: Nat, ~c: O.C(F), ~lb: @u: M.Vec(~F) -> {M.len(~F, u) == n : Nat} -> O.le(~F, vn(~F, u), O.mul(F, c, vn(~F, M.matvec(~F, a, u)))), +hc: O.le(~F, O.zero(F), c), +w: M.Vec(~F), +lw: {M.len(~F, w) == n : Nat}, e: {M.matvec(~F, a, w) == GJ.zeros(~F, n) : M.Vec(~F)}) -> {w == GJ.zeros(~F, n) : M.Vec(~F)}:
  %lw : {w == GJ.zeros(~F, _) : M.Vec(~F)}
  vzero(~F, w, FM.vall_mono(~F, w, vn(~F, w), O.zero(F), FV.vmax_all(~F, w), FM.sub_nonneg(~F, vn(~F, w), O.zero(F), DM.le_trans(~F, vn(~F, w), O.mul(F, c, vn(~F, GJ.zeros(~F, n))), O.zero(F),
    (%e : O.le(~F, vn(~F, w), O.mul(F, c, vn(~F, _)))
      lb(w, lw)),
    FV.sle0(~F, c, vn(~F, GJ.zeros(~F, n)), hc, vn_z(~F, n))))))

# a square A (n rows of n entries) with |u| <= c |A u| has an inverse of
# norm at most c
def invb_of_low(~F: O.OField, ~a: M.Mat(~F), ~n: Nat, ~c: O.C(F), ~lb: @u: M.Vec(~F) -> {M.len(~F, u) == n : Nat} -> O.le(~F, vn(~F, u), O.mul(F, c, vn(~F, M.matvec(~F, a, u)))), +hc: O.le(~F, O.zero(F), c), +ha: {GJ.nrows(~F, a) == n : Nat}, hw: GJ.All(~(i => GJ.roww(~F, a, n, i)), n)) -> InvB(~F, a, n, c):
  invb_low(~F, ~a, ~n, ~c, ~lb, hc, ha, GJ.inv_of_inj(~F, a, n, ha, hw, w => lw => e => inj_low(~F, ~a, ~n, ~c, ~lb, hc, w, lw, e)))

# Perturbation: J has an inverse of norm <= b and |J' - J| <= d with
# 2 b d <= 1: J' has an inverse of norm <= 2b
def pert(~F: O.OField, +j: M.Mat(~F), +j2: M.Mat(~F), +n: Nat, +b: O.C(F), +d: O.C(F), +h: InvB(~F, j, n, b), +hj: {GJ.nrows(~F, j) == n : Nat}, +hj2: {GJ.nrows(~F, j2) == n : Nat}, hw2: GJ.All(~(i => GJ.roww(~F, j2, n, i)), n), +hd: O.le(~F, mnorm(~F, M.madd(~F, j2, M.mneg(~F, j)), n), d), +hbd: O.le(~F, O.add(F, O.mul(F, b, d), O.mul(F, b, d)), O.one(F))) -> InvB(~F, j2, n, O.add(F, b, b)):
  +hb = invb_nn(~F, j, n, b, h)
  invb_low(~F, ~j2, ~n, ~O.add(F, b, b), ~(u => lu => low2(~F, j, j2, n, b, d, h, hj, hd, hbd, u, lu)), FO.nonneg_add(~F, b, b, hb, hb), hj2, GJ.inv_of_inj(~F, j2, n, hj2, hw2, w => lw => e => inj2(~F, j, j2, n, b, d, h, hj, hd, hbd, w, lw, e)))
