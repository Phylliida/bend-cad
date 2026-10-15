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
