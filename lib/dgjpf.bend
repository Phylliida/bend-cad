# bend-cad: the rounded elimination, for solve_complete (DESIGN §10.4, C4).
# Proofs only.
#
# lib/numer.bend's dinverse eliminates over the dyadics with every result
# rounded to w significant bits and partial pivoting. This file reads it in
# every ordered field F (through ofd): the rows it builds are an exact row
# operation of the previous ones plus a rounding error of size 2^-w times
# their entries (C4a, C4b), the pivot it picks is bounded below (C4c), and
# the inverse it returns is good (C4d).

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
import ./qemb.bend as QE
import ./kball.bend as KB
import ./gjpf.bend as GJ
import ./numer.bend as NU
import ./roundpf.bend as RP
import ./normpf.bend as NP
import ./real.bend as RL
import ./slope.bend as SL
import ./nat.bend as LN
import ./kinst.bend as KI
import ./bndpf.bend as BP
import ../spec/knum.bend as N

# Dyadic rows in F
# ----------------

def dget_ofd(~F: O.OField, xs: List<&2, S.D>, k: Nat) -> {M.ofd(~F, NU.dget(xs, k)) == O.lookup(~F, M.ofdv(~F, xs), k) : O.C(F)}:
  match xs k:
    case Nil{} 0n:
      Equal.sym(O.C(F), O.zero(F), M.ofd(~F, M.d0()), DM.ofd_zero(~F))
    case Nil{} 1n+j:
      Equal.sym(O.C(F), O.zero(F), M.ofd(~F, M.d0()), DM.ofd_zero(~F))
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+j:
      dget_ofd(~F, t, j)

def drow_ofd(~F: O.OField, rows: List<&2, List<&2, S.D>>, k: Nat) -> {M.ofdv(~F, NU.drow(rows, k)) == DV.mrow(~F, M.ofdm(~F, rows), k) : M.Vec(~F)}:
  match rows k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+j:
      drow_ofd(~F, t, j)

def dset_ofd(~F: O.OField, rows: List<&2, List<&2, S.D>>, k: Nat, +r: List<&2, S.D>) -> {M.ofdm(~F, NU.dset(rows, k, r)) == GJ.mset(~F, M.ofdm(~F, rows), k, M.ofdv(~F, r)) : M.Mat(~F)}:
  match rows k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{+h, t} 1n+j:
      Equal.cong(M.Mat(~F), M.Mat(~F), m => Con{M.ofdv(~F, h), m}, M.ofdm(~F, NU.dset(t, j, r)), GJ.mset(~F, M.ofdm(~F, t), j, M.ofdv(~F, r)), dset_ofd(~F, t, j, r))

# swapping rows commutes with reading them in F
def dswap_ofd(~F: O.OField, +rows: List<&2, List<&2, S.D>>, +a: Nat, +b: Nat) -> {M.ofdm(~F, NU.dswap(rows, a, b)) == GJ.mswap(~F, M.ofdm(~F, rows), a, b) : M.Mat(~F)}:
  %Equal.sym(M.Mat(~F), M.ofdm(~F, NU.dset(NU.dset(rows, a, NU.drow(rows, b)), b, NU.drow(rows, a))), GJ.mset(~F, M.ofdm(~F, NU.dset(rows, a, NU.drow(rows, b))), b, M.ofdv(~F, NU.drow(rows, a))), dset_ofd(~F, NU.dset(rows, a, NU.drow(rows, b)), b, NU.drow(rows, a))) : {_ == GJ.mswap(~F, M.ofdm(~F, rows), a, b) : M.Mat(~F)}
  %Equal.sym(M.Mat(~F), M.ofdm(~F, NU.dset(rows, a, NU.drow(rows, b))), GJ.mset(~F, M.ofdm(~F, rows), a, M.ofdv(~F, NU.drow(rows, b))), dset_ofd(~F, rows, a, NU.drow(rows, b))) : {GJ.mset(~F, _, b, M.ofdv(~F, NU.drow(rows, a))) == GJ.mswap(~F, M.ofdm(~F, rows), a, b) : M.Mat(~F)}
  %Equal.sym(M.Vec(~F), M.ofdv(~F, NU.drow(rows, b)), DV.mrow(~F, M.ofdm(~F, rows), b), drow_ofd(~F, rows, b)) : {GJ.mset(~F, GJ.mset(~F, M.ofdm(~F, rows), a, _), b, M.ofdv(~F, NU.drow(rows, a))) == GJ.mswap(~F, M.ofdm(~F, rows), a, b) : M.Mat(~F)}
  %Equal.sym(M.Vec(~F), M.ofdv(~F, NU.drow(rows, a)), DV.mrow(~F, M.ofdm(~F, rows), a), drow_ofd(~F, rows, a)) : {GJ.mset(~F, GJ.mset(~F, M.ofdm(~F, rows), a, DV.mrow(~F, M.ofdm(~F, rows), b)), b, _) == GJ.mswap(~F, M.ofdm(~F, rows), a, b) : M.Mat(~F)}
  {==}

# Rounded arithmetic
# ------------------

# |x| <= t gives |x| <= t read through dabs
def dabs_le(~F: O.OField, x: S.D, +t: O.C(F), h: M.bnd(~F, M.ofd(~F, x), t)) -> O.le(~F, M.ofd(~F, M.dabs(x)), t):
  match x:
    case S.D{S.Z0{}, +e}:
      NP.bnd_lo(~F, M.ofd(~F, S.D{S.Z0{}, e}), t, h)
    case S.D{S.Zpos{+p}, +e}:
      NP.bnd_lo(~F, M.ofd(~F, S.D{S.Zpos{p}, e}), t, h)
    case S.D{S.Zneg{+p}, +e}:
      (h1, h2) = h
      FV.le_of_sub(~F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))), t, FM.nn_eq(~F, O.sub(~F, t, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e))))), O.add(F, t, O.mul(F, O.neg(F, O.ofp(~F, p)), O.inv(F, O.ofp(~F, S.Pos.pow2(e))))), FR.fring_eq(~F, [t, O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))], E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZNeg{E.ZVar{1n}}, E.ZVar{2n}}}, E.ZSub{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, {==}), h2))

def u_nn(~F: O.OField, +w: Nat) -> O.le(~F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})):
  FO.lt_le(~F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), DM.dpos(~F, S.XH{}, w))

# a rounding with |x| <= t errs by at most t 2^-w
def dsig_t(~F: O.OField, +x: S.D, +w: Nat, +t: O.C(F), h: M.bnd(~F, M.ofd(~F, x), t)) -> M.bnd(~F, O.sub(~F, M.ofd(~F, NU.dsig(x, w)), M.ofd(~F, x)), O.mul(F, t, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))):
  FM.bnd_mono(~F, O.sub(~F, M.ofd(~F, NU.dsig(x, w)), M.ofd(~F, x)), O.mul(F, M.ofd(~F, M.dabs(x)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, t, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), RP.dsig_err(~F, x, w), FM.sub_nonneg(~F, O.mul(F, M.ofd(~F, M.dabs(x)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, t, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FV.mul_le_r(~F, M.ofd(~F, M.dabs(x)), t, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), u_nn(~F, w), dabs_le(~F, x, t, h))))

# |dsmul(w, a, b) - a b| <= A B 2^-w for |a| <= A, |b| <= B
def smul_err(~F: O.OField, +w: Nat, +a: S.D, +b: S.D, +aa: O.C(F), +bb: O.C(F), ha: M.bnd(~F, M.ofd(~F, a), aa), hb: M.bnd(~F, M.ofd(~F, b), bb)) -> M.bnd(~F, O.sub(~F, M.ofd(~F, NU.dsmul(w, a, b)), O.mul(F, M.ofd(~F, a), M.ofd(~F, b))), O.mul(F, O.mul(F, aa, bb), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))):
  %Equal.sym(O.C(F), O.mul(F, M.ofd(~F, a), M.ofd(~F, b)), M.ofd(~F, S.D.mul(a, b)), DM.ofd_mul(~F, a, b)) : M.bnd(~F, O.sub(~F, M.ofd(~F, NU.dsmul(w, a, b)), _), O.mul(F, O.mul(F, aa, bb), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))
  dsig_t(~F, S.D.mul(a, b), w, O.mul(F, aa, bb), (%DM.ofd_mul(~F, a, b) : M.bnd(~F, _, O.mul(F, aa, bb))
    FM.bnd_mul(~F, M.ofd(~F, a), aa, M.ofd(~F, b), bb, ha, hb)))

# |dsadd(w, a, b) - (a + b)| <= (A + B) 2^-w for |a| <= A, |b| <= B
def sadd_err(~F: O.OField, +w: Nat, +a: S.D, +b: S.D, +aa: O.C(F), +bb: O.C(F), ha: M.bnd(~F, M.ofd(~F, a), aa), hb: M.bnd(~F, M.ofd(~F, b), bb)) -> M.bnd(~F, O.sub(~F, M.ofd(~F, NU.dsadd(w, a, b)), O.add(F, M.ofd(~F, a), M.ofd(~F, b))), O.mul(F, O.add(F, aa, bb), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))):
  %Equal.sym(O.C(F), O.add(F, M.ofd(~F, a), M.ofd(~F, b)), M.ofd(~F, S.D.add(a, b)), DM.ofd_add(~F, a, b)) : M.bnd(~F, O.sub(~F, M.ofd(~F, NU.dsadd(w, a, b)), _), O.mul(F, O.add(F, aa, bb), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))
  dsig_t(~F, S.D.add(a, b), w, O.add(F, aa, bb), (%DM.ofd_add(~F, a, b) : M.bnd(~F, _, O.add(F, aa, bb))
    FM.bnd_add(~F, M.ofd(~F, a), aa, M.ofd(~F, b), bb, ha, hb)))

# 2^-w <= 1
def u_le1(~F: O.OField, +w: Nat) -> O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F)):
  +r = QE.ofp_rel(~F, S.Pos.pow2(w))
  FV.le_of_sub(~F, O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.Pos.pow2(w)))), O.one(F), FM.nn_eq(~F, O.sub(~F, O.one(F), O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.Pos.pow2(w))))), O.mul(F, O.sub(~F, O.ofp(~F, S.Pos.pow2(w)), O.one(F)), O.inv(F, O.ofp(~F, S.Pos.pow2(w)))),
    FO.eq_of_sub(~F, O.mul(F, O.sub(~F, O.ofp(~F, S.Pos.pow2(w)), O.one(F)), O.inv(F, O.ofp(~F, S.Pos.pow2(w)))), O.sub(~F, O.one(F), O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.Pos.pow2(w))))), FO.cert1(~F, O.sub(~F, O.mul(F, O.sub(~F, O.ofp(~F, S.Pos.pow2(w)), O.one(F)), O.inv(F, O.ofp(~F, S.Pos.pow2(w)))), O.sub(~F, O.one(F), O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.Pos.pow2(w)))))), O.one(F), O.sub(~F, O.mul(F, O.ofp(~F, S.Pos.pow2(w)), O.inv(F, O.ofp(~F, S.Pos.pow2(w)))), O.one(F)), FR.fring_eq(~F, [O.ofp(~F, S.Pos.pow2(w)), O.inv(F, O.ofp(~F, S.Pos.pow2(w)))], E.ZSub{E.ZMul{E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{1n}}, E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{1n}}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), r)),
    FO.mul_nonneg(~F, O.sub(~F, O.ofp(~F, S.Pos.pow2(w)), O.one(F)), O.inv(F, O.ofp(~F, S.Pos.pow2(w))), FM.sub_nonneg(~F, O.one(F), O.ofp(~F, S.Pos.pow2(w)), RP.ofp_ge1(~F, S.Pos.pow2(w))), RP.inv_nn(~F, S.Pos.pow2(w)))))


# q = 1/x as the solver divides: q x = 1, for x not 0
def div_rel(~F: O.OField, x: S.D, hz: {M.ofd(~F, x) == O.zero(F) : O.C(F)} -> Empty) -> {O.mul(F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(x))), M.ofd(~F, x)) == O.one(F) : O.C(F)}:
  match x:
    case S.D{S.Z0{}, +e}:
      FO.absurd({O.mul(F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(S.D{S.Z0{}, e}))), M.ofd(~F, S.D{S.Z0{}, e})) == O.one(F) : O.C(F)}, hz(FR.fring_eq(~F, [O.inv(F, O.ofp(~F, S.Pos.pow2(e)))], E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZCst{S.Z0{}}, {==})))
    case S.D{S.Zpos{+p}, +e}:
      FO.eq_of_sub(~F, O.mul(F, O.mul(F, O.ofp(~F, S.Pos.pow2(e)), O.inv(F, O.ofp(~F, p))), O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e))))), O.one(F), FO.cert2(~F, O.sub(~F, O.mul(F, O.mul(F, O.ofp(~F, S.Pos.pow2(e)), O.inv(F, O.ofp(~F, p))), O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e))))), O.one(F)), O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, p))), O.sub(~F, O.mul(F, O.ofp(~F, S.Pos.pow2(e)), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))), O.one(F)), O.one(F), O.sub(~F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, p))), O.one(F)), FR.fring_eq(~F, [O.ofp(~F, S.Pos.pow2(e)), O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e))), O.inv(F, O.ofp(~F, p))], E.ZSub{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZMul{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), QE.ofp_rel(~F, S.Pos.pow2(e)), QE.ofp_rel(~F, p)))
    case S.D{S.Zneg{+p}, +e}:
      FO.eq_of_sub(~F, O.mul(F, O.mul(F, O.neg(F, O.ofp(~F, S.Pos.pow2(e))), O.inv(F, O.ofp(~F, p))), O.mul(F, O.neg(F, O.ofp(~F, p)), O.inv(F, O.ofp(~F, S.Pos.pow2(e))))), O.one(F), FO.cert2(~F, O.sub(~F, O.mul(F, O.mul(F, O.neg(F, O.ofp(~F, S.Pos.pow2(e))), O.inv(F, O.ofp(~F, p))), O.mul(F, O.neg(F, O.ofp(~F, p)), O.inv(F, O.ofp(~F, S.Pos.pow2(e))))), O.one(F)), O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, p))), O.sub(~F, O.mul(F, O.ofp(~F, S.Pos.pow2(e)), O.inv(F, O.ofp(~F, S.Pos.pow2(e)))), O.one(F)), O.one(F), O.sub(~F, O.mul(F, O.ofp(~F, p), O.inv(F, O.ofp(~F, p))), O.one(F)), FR.fring_eq(~F, [O.ofp(~F, S.Pos.pow2(e)), O.ofp(~F, p), O.inv(F, O.ofp(~F, S.Pos.pow2(e))), O.inv(F, O.ofp(~F, p))], E.ZSub{E.ZMul{E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZVar{3n}}, E.ZMul{E.ZNeg{E.ZVar{1n}}, E.ZVar{2n}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZMul{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), QE.ofp_rel(~F, S.Pos.pow2(e)), QE.ofp_rel(~F, p)))

# the rounded reciprocal: |s - 1/x| <= |1/x| 2^-w
def s_err(~F: O.OField, +w: Nat, +x: S.D) -> M.bnd(~F, O.sub(~F, M.ofd(~F, NU.dsdiv(w, NU.done(), x)), O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(x)))), O.mul(F, FV.fabs(~F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(x)))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))):
  RP.qsig_err(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(x)), w)


# one entry of x - c y, rounded twice: within (X + 3 C Y) 2^-w
def axpy_ent(~F: O.OField, +w: Nat, +x: S.D, +c: S.D, +y: S.D, +xx: O.C(F), +cc: O.C(F), +yy: O.C(F), hx: M.bnd(~F, M.ofd(~F, x), xx), +hc: M.bnd(~F, M.ofd(~F, c), cc), +hy: M.bnd(~F, M.ofd(~F, y), yy), +hu: O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F))) -> M.bnd(~F, O.sub(~F, M.ofd(~F, NU.dsadd(w, x, S.D.neg(NU.dsmul(w, c, y)))), O.add(F, M.ofd(~F, x), O.mul(F, O.neg(F, M.ofd(~F, c)), M.ofd(~F, y)))), O.mul(F, O.add(F, xx, O.add(F, O.add(F, O.mul(F, cc, yy), O.mul(F, cc, yy)), O.mul(F, cc, yy))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))):
  +ht = smul_err(~F, w, c, y, cc, yy, hc, hy)
  +hcy = FM.bnd_mul(~F, M.ofd(~F, c), cc, M.ofd(~F, y), yy, hc, hy)
  +h0 = FO.mul_nonneg(~F, cc, yy, FM.bnd_nonneg(~F, M.ofd(~F, c), cc, hc), FM.bnd_nonneg(~F, M.ofd(~F, y), yy, hy))
  +htb = FM.bnd_mono(~F, M.ofd(~F, NU.dsmul(w, c, y)), O.add(F, O.mul(F, cc, yy), O.mul(F, O.mul(F, cc, yy), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.add(F, O.mul(F, cc, yy), O.mul(F, cc, yy)),
    KB.bnd_val(~F, O.add(F, O.mul(F, M.ofd(~F, c), M.ofd(~F, y)), O.sub(~F, M.ofd(~F, NU.dsmul(w, c, y)), O.mul(F, M.ofd(~F, c), M.ofd(~F, y)))), M.ofd(~F, NU.dsmul(w, c, y)), O.add(F, O.mul(F, cc, yy), O.mul(F, O.mul(F, cc, yy), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), FR.fring_eq(~F, [M.ofd(~F, x), M.ofd(~F, c), M.ofd(~F, y), M.ofd(~F, NU.dsmul(w, c, y)), M.ofd(~F, NU.dsadd(w, x, S.D.neg(NU.dsmul(w, c, y)))), xx, cc, yy, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})], E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZSub{E.ZVar{3n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZVar{3n}, {==}), FM.bnd_add(~F, O.mul(F, M.ofd(~F, c), M.ofd(~F, y)), O.mul(F, cc, yy), O.sub(~F, M.ofd(~F, NU.dsmul(w, c, y)), O.mul(F, M.ofd(~F, c), M.ofd(~F, y))), O.mul(F, O.mul(F, cc, yy), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), hcy, ht)),
    FM.nn_eq(~F, O.sub(~F, O.add(F, O.mul(F, cc, yy), O.mul(F, cc, yy)), O.add(F, O.mul(F, cc, yy), O.mul(F, O.mul(F, cc, yy), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, O.mul(F, cc, yy), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), FR.fring_eq(~F, [M.ofd(~F, x), M.ofd(~F, c), M.ofd(~F, y), M.ofd(~F, NU.dsmul(w, c, y)), M.ofd(~F, NU.dsadd(w, x, S.D.neg(NU.dsmul(w, c, y)))), xx, cc, yy, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})], E.ZMul{E.ZMul{E.ZVar{6n}, E.ZVar{7n}}, E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{8n}}}, E.ZSub{E.ZAdd{E.ZMul{E.ZVar{6n}, E.ZVar{7n}}, E.ZMul{E.ZVar{6n}, E.ZVar{7n}}}, E.ZAdd{E.ZMul{E.ZVar{6n}, E.ZVar{7n}}, E.ZMul{E.ZMul{E.ZVar{6n}, E.ZVar{7n}}, E.ZVar{8n}}}}, {==}), FO.mul_nonneg(~F, O.mul(F, cc, yy), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), h0, FM.sub_nonneg(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F), hu))))
  +hs = sadd_err(~F, w, x, S.D.neg(NU.dsmul(w, c, y)), xx, O.add(F, O.mul(F, cc, yy), O.mul(F, cc, yy)), hx, (%DM.ofd_neg(~F, NU.dsmul(w, c, y)) : M.bnd(~F, _, O.add(F, O.mul(F, cc, yy), O.mul(F, cc, yy)))
    FM.bnd_neg(~F, M.ofd(~F, NU.dsmul(w, c, y)), O.add(F, O.mul(F, cc, yy), O.mul(F, cc, yy)), htb)))
  KB.bnd_val(~F, O.add(F, O.sub(~F, M.ofd(~F, NU.dsadd(w, x, S.D.neg(NU.dsmul(w, c, y)))), O.add(F, M.ofd(~F, x), O.neg(F, M.ofd(~F, NU.dsmul(w, c, y))))), O.neg(F, O.sub(~F, M.ofd(~F, NU.dsmul(w, c, y)), O.mul(F, M.ofd(~F, c), M.ofd(~F, y))))), O.sub(~F, M.ofd(~F, NU.dsadd(w, x, S.D.neg(NU.dsmul(w, c, y)))), O.add(F, M.ofd(~F, x), O.mul(F, O.neg(F, M.ofd(~F, c)), M.ofd(~F, y)))), O.mul(F, O.add(F, xx, O.add(F, O.add(F, O.mul(F, cc, yy), O.mul(F, cc, yy)), O.mul(F, cc, yy))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FR.fring_eq(~F, [M.ofd(~F, x), M.ofd(~F, c), M.ofd(~F, y), M.ofd(~F, NU.dsmul(w, c, y)), M.ofd(~F, NU.dsadd(w, x, S.D.neg(NU.dsmul(w, c, y)))), xx, cc, yy, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})], E.ZAdd{E.ZSub{E.ZVar{4n}, E.ZAdd{E.ZVar{0n}, E.ZNeg{E.ZVar{3n}}}}, E.ZNeg{E.ZSub{E.ZVar{3n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}}, E.ZSub{E.ZVar{4n}, E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZNeg{E.ZVar{1n}}, E.ZVar{2n}}}}, {==}),
    FM.bnd_eq(~F, O.add(F, O.sub(~F, M.ofd(~F, NU.dsadd(w, x, S.D.neg(NU.dsmul(w, c, y)))), O.add(F, M.ofd(~F, x), O.neg(F, M.ofd(~F, NU.dsmul(w, c, y))))), O.neg(F, O.sub(~F, M.ofd(~F, NU.dsmul(w, c, y)), O.mul(F, M.ofd(~F, c), M.ofd(~F, y))))), O.add(F, O.mul(F, O.add(F, xx, O.add(F, O.mul(F, cc, yy), O.mul(F, cc, yy))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.mul(F, cc, yy), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.add(F, xx, O.add(F, O.add(F, O.mul(F, cc, yy), O.mul(F, cc, yy)), O.mul(F, cc, yy))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FR.fring_eq(~F, [M.ofd(~F, x), M.ofd(~F, c), M.ofd(~F, y), M.ofd(~F, NU.dsmul(w, c, y)), M.ofd(~F, NU.dsadd(w, x, S.D.neg(NU.dsmul(w, c, y)))), xx, cc, yy, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})], E.ZAdd{E.ZMul{E.ZAdd{E.ZVar{5n}, E.ZAdd{E.ZMul{E.ZVar{6n}, E.ZVar{7n}}, E.ZMul{E.ZVar{6n}, E.ZVar{7n}}}}, E.ZVar{8n}}, E.ZMul{E.ZMul{E.ZVar{6n}, E.ZVar{7n}}, E.ZVar{8n}}}, E.ZMul{E.ZAdd{E.ZVar{5n}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{6n}, E.ZVar{7n}}, E.ZMul{E.ZVar{6n}, E.ZVar{7n}}}, E.ZMul{E.ZVar{6n}, E.ZVar{7n}}}}, E.ZVar{8n}}, {==}),
      FM.bnd_add(~F, O.sub(~F, M.ofd(~F, NU.dsadd(w, x, S.D.neg(NU.dsmul(w, c, y)))), O.add(F, M.ofd(~F, x), O.neg(F, M.ofd(~F, NU.dsmul(w, c, y))))), O.mul(F, O.add(F, xx, O.add(F, O.mul(F, cc, yy), O.mul(F, cc, yy))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.neg(F, O.sub(~F, M.ofd(~F, NU.dsmul(w, c, y)), O.mul(F, M.ofd(~F, c), M.ofd(~F, y)))), O.mul(F, O.mul(F, cc, yy), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), (%Equal.sym(O.C(F), O.neg(F, M.ofd(~F, NU.dsmul(w, c, y))), M.ofd(~F, S.D.neg(NU.dsmul(w, c, y))), DM.ofd_neg(~F, NU.dsmul(w, c, y))) : M.bnd(~F, O.sub(~F, M.ofd(~F, NU.dsadd(w, x, S.D.neg(NU.dsmul(w, c, y)))), O.add(F, M.ofd(~F, x), _)), O.mul(F, O.add(F, xx, O.add(F, O.mul(F, cc, yy), O.mul(F, cc, yy))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))
        hs), FM.bnd_neg(~F, O.sub(~F, M.ofd(~F, NU.dsmul(w, c, y)), O.mul(F, M.ofd(~F, c), M.ofd(~F, y))), O.mul(F, O.mul(F, cc, yy), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), ht))))

# Rounded rows
# ------------

def natz(m: Nat) -> Type:
  match m:
    case 0n:
      Unit
    case 1n+j:
      Empty

def zs_ne(+k: Nat, e: {0n == 1n+k : Nat}) -> Empty:
  %e : natz(_)
  Unit{}

def sz_ne(+k: Nat, e: {1n+k == 0n : Nat}) -> Empty:
  zs_ne(k, Equal.sym(Nat, 1n+k, 0n, e))

# the scaled row s xs, rounded: within S X 2^-w of the exact one
def dscale_err(~F: O.OField, +w: Nat, +s: S.D, xs: List<&2, S.D>, +ss: O.C(F), +xx: O.C(F), +hs: M.bnd(~F, M.ofd(~F, s), ss), hx: M.vbnd.all(~F, M.ofdv(~F, xs), xx)) -> M.vbnd.all(~F, M.vadd(~F, M.ofdv(~F, NU.dscale(w, s, xs)), M.vneg(~F, M.vscale(~F, M.ofd(~F, s), M.ofdv(~F, xs)))), O.mul(F, O.mul(F, ss, xx), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+x, +t}:
      (h1, h2) = hx
      (smul_err(~F, w, s, x, ss, xx, hs, h1), dscale_err(~F, w, s, t, ss, xx, hs, h2))

# the row xs - c ys, rounded: within (X + 3 C Y) 2^-w of the exact one,
# for rows of one length
def daxpy_err(~F: O.OField, +w: Nat, xs: List<&2, S.D>, +c: S.D, ys: List<&2, S.D>, +xx: O.C(F), +cc: O.C(F), +yy: O.C(F), +hx: M.vbnd.all(~F, M.ofdv(~F, xs), xx), +hc: M.bnd(~F, M.ofd(~F, c), cc), +hy: M.vbnd.all(~F, M.ofdv(~F, ys), yy), hl: {M.len(~F, M.ofdv(~F, xs)) == M.len(~F, M.ofdv(~F, ys)) : Nat}, +hu: O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F))) -> M.vbnd.all(~F, M.vadd(~F, M.ofdv(~F, NU.daxpy(w, xs, c, ys)), M.vneg(~F, M.vadd(~F, M.ofdv(~F, xs), M.vscale(~F, O.neg(F, M.ofd(~F, c)), M.ofdv(~F, ys))))), O.mul(F, O.add(F, xx, O.add(F, O.add(F, O.mul(F, cc, yy), O.mul(F, cc, yy)), O.mul(F, cc, yy))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))):
  match xs ys:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} Con{+y, +yt}:
      FO.absurd(M.vbnd.all(~F, M.vadd(~F, M.ofdv(~F, NU.daxpy(w, Nil{}, c, Con{y, yt})), M.vneg(~F, M.vadd(~F, M.ofdv(~F, Nil{}), M.vscale(~F, O.neg(F, M.ofd(~F, c)), M.ofdv(~F, Con{y, yt}))))), O.mul(F, O.add(F, xx, O.add(F, O.add(F, O.mul(F, cc, yy), O.mul(F, cc, yy)), O.mul(F, cc, yy))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), zs_ne(M.len(~F, M.ofdv(~F, yt)), hl))
    case Con{+x, +xt} Nil{}:
      FO.absurd(M.vbnd.all(~F, M.vadd(~F, M.ofdv(~F, NU.daxpy(w, Con{x, xt}, c, Nil{})), M.vneg(~F, M.vadd(~F, M.ofdv(~F, Con{x, xt}), M.vscale(~F, O.neg(F, M.ofd(~F, c)), Nil{})))), O.mul(F, O.add(F, xx, O.add(F, O.add(F, O.mul(F, cc, yy), O.mul(F, cc, yy)), O.mul(F, cc, yy))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), sz_ne(M.len(~F, M.ofdv(~F, xt)), hl))
    case Con{+x, +xt} Con{+y, +yt}:
      (axpy_ent(~F, w, x, c, y, xx, cc, yy, NP.vh(~F, M.ofd(~F, x), M.ofdv(~F, xt), xx, hx), hc, NP.vh(~F, M.ofd(~F, y), M.ofdv(~F, yt), yy, hy), hu),
       daxpy_err(~F, w, xt, c, yt, xx, cc, yy, NP.vt(~F, M.ofd(~F, x), M.ofdv(~F, xt), xx, hx), hc, NP.vt(~F, M.ofd(~F, y), M.ofdv(~F, yt), yy, hy), FV.succ_inj(M.len(~F, M.ofdv(~F, xt)), M.len(~F, M.ofdv(~F, yt)), hl), hu))

# Lookups, drops and columns
# --------------------------

def lnil(~F: O.OField, k: Nat) -> {O.lookup(~F, Nil{}, k) == O.zero(F) : O.C(F)}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      {==}

def vadd_nil_l(~F: O.OField, x: M.Vec(~F)) -> {M.vadd(~F, Nil{}, x) == x : M.Vec(~F)}:
  match x:
    case Nil{}:
      {==}
    case Con{a, t}:
      {==}

# entry k of a B is a read against column k of B
def look_vecmat(~F: O.OField, a: M.Vec(~F), b: M.Mat(~F), +k: Nat) -> {O.lookup(~F, M.vecmat(~F, a, b), k) == M.dot(~F, a, GJ.mcol(~F, b, k)) : O.C(F)}:
  match a b:
    case Nil{} Nil{}:
      lnil(~F, k)
    case Nil{} Con{+r, +rs}:
      lnil(~F, k)
    case Con{+x, +xs} Nil{}:
      lnil(~F, k)
    case Con{+x, +xs} Con{+r, +rs}:
      %GJ.look_vadd(~F, M.vscale(~F, x, r), M.vecmat(~F, xs, rs), k) : {_ == O.add(F, O.mul(F, x, O.lookup(~F, r, k)), M.dot(~F, xs, GJ.mcol(~F, rs, k))) : O.C(F)}
      %GJ.look_vscale(~F, x, r, k) : {O.add(F, _, O.lookup(~F, M.vecmat(~F, xs, rs), k)) == O.add(F, O.mul(F, x, O.lookup(~F, r, k)), M.dot(~F, xs, GJ.mcol(~F, rs, k))) : O.C(F)}
      %Equal.sym(O.C(F), O.lookup(~F, M.vecmat(~F, xs, rs), k), M.dot(~F, xs, GJ.mcol(~F, rs, k)), look_vecmat(~F, xs, rs, k)) : {O.add(F, O.mul(F, x, O.lookup(~F, r, k)), _) == O.add(F, O.mul(F, x, O.lookup(~F, r, k)), M.dot(~F, xs, GJ.mcol(~F, rs, k))) : O.C(F)}
      {==}

def drop_vadd(~F: O.OField, k: Nat, u: M.Vec(~F), w: M.Vec(~F)) -> {M.vadd(~F, GJ.vdrop(~F, k, u), GJ.vdrop(~F, k, w)) == GJ.vdrop(~F, k, M.vadd(~F, u, w)) : M.Vec(~F)}:
  match k u w:
    case 0n Nil{} Nil{}:
      {==}
    case 0n Nil{} Con{b, bs}:
      {==}
    case 0n Con{a, as} Nil{}:
      {==}
    case 0n Con{a, as} Con{b, bs}:
      {==}
    case 1n+j Nil{} Nil{}:
      {==}
    case 1n+j Nil{} Con{b, bs}:
      vadd_nil_l(~F, GJ.vdrop(~F, j, bs))
    case 1n+j Con{a, as} Nil{}:
      Equal.sym(M.Vec(~F), GJ.vdrop(~F, j, as), M.vadd(~F, GJ.vdrop(~F, j, as), Nil{}), FV.vadd_nil_r(~F, GJ.vdrop(~F, j, as)))
    case 1n+j Con{a, as} Con{b, bs}:
      drop_vadd(~F, j, as, bs)

def drop_vneg(~F: O.OField, k: Nat, u: M.Vec(~F)) -> {M.vneg(~F, GJ.vdrop(~F, k, u)) == GJ.vdrop(~F, k, M.vneg(~F, u)) : M.Vec(~F)}:
  match k u:
    case 0n Nil{}:
      {==}
    case 0n Con{a, as}:
      {==}
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{a, as}:
      drop_vneg(~F, j, as)

def drop_vscale(~F: O.OField, k: Nat, +s: O.C(F), u: M.Vec(~F)) -> {M.vscale(~F, s, GJ.vdrop(~F, k, u)) == GJ.vdrop(~F, k, M.vscale(~F, s, u)) : M.Vec(~F)}:
  match k u:
    case 0n Nil{}:
      {==}
    case 0n Con{a, as}:
      {==}
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{a, as}:
      drop_vscale(~F, j, s, as)

# Row defects
# -----------
# A row x of [L | R] (n entries each) has defect L - R J; its entry k is
# x_k minus x's right part read against column k of J.

def dk(~F: O.OField, +n: Nat, +j: M.Mat(~F), +x: M.Vec(~F), +k: Nat) -> O.C(F):
  O.sub(~F, O.lookup(~F, x, k), M.dot(~F, GJ.vdrop(~F, n, x), GJ.mcol(~F, j, k)))


# the defect of x - y
def dk_sub(~F: O.OField, +n: Nat, +j: M.Mat(~F), +x: M.Vec(~F), +y: M.Vec(~F), +k: Nat) -> {dk(~F, n, j, M.vadd(~F, x, M.vneg(~F, y)), k) == O.sub(~F, dk(~F, n, j, x, k), dk(~F, n, j, y, k)) : O.C(F)}:
  %GJ.look_vadd(~F, x, M.vneg(~F, y), k) : {O.sub(~F, _, M.dot(~F, GJ.vdrop(~F, n, M.vadd(~F, x, M.vneg(~F, y))), GJ.mcol(~F, j, k))) == O.sub(~F, dk(~F, n, j, x, k), dk(~F, n, j, y, k)) : O.C(F)}
  %GJ.look_vneg(~F, y, k) : {O.sub(~F, O.add(F, O.lookup(~F, x, k), _), M.dot(~F, GJ.vdrop(~F, n, M.vadd(~F, x, M.vneg(~F, y))), GJ.mcol(~F, j, k))) == O.sub(~F, dk(~F, n, j, x, k), dk(~F, n, j, y, k)) : O.C(F)}
  %drop_vadd(~F, n, x, M.vneg(~F, y)) : {O.sub(~F, O.add(F, O.lookup(~F, x, k), O.neg(F, O.lookup(~F, y, k))), M.dot(~F, _, GJ.mcol(~F, j, k))) == O.sub(~F, dk(~F, n, j, x, k), dk(~F, n, j, y, k)) : O.C(F)}
  %drop_vneg(~F, n, y) : {O.sub(~F, O.add(F, O.lookup(~F, x, k), O.neg(F, O.lookup(~F, y, k))), M.dot(~F, M.vadd(~F, GJ.vdrop(~F, n, x), _), GJ.mcol(~F, j, k))) == O.sub(~F, dk(~F, n, j, x, k), dk(~F, n, j, y, k)) : O.C(F)}
  %FM.dot_vadd(~F, GJ.vdrop(~F, n, x), M.vneg(~F, GJ.vdrop(~F, n, y)), GJ.mcol(~F, j, k)) : {O.sub(~F, O.add(F, O.lookup(~F, x, k), O.neg(F, O.lookup(~F, y, k))), _) == O.sub(~F, dk(~F, n, j, x, k), dk(~F, n, j, y, k)) : O.C(F)}
  %FM.dot_vneg(~F, GJ.vdrop(~F, n, y), GJ.mcol(~F, j, k)) : {O.sub(~F, O.add(F, O.lookup(~F, x, k), O.neg(F, O.lookup(~F, y, k))), O.add(F, M.dot(~F, GJ.vdrop(~F, n, x), GJ.mcol(~F, j, k)), _)) == O.sub(~F, dk(~F, n, j, x, k), dk(~F, n, j, y, k)) : O.C(F)}
  FR.fring_eq(~F, [O.lookup(~F, x, k), O.lookup(~F, y, k), M.dot(~F, GJ.vdrop(~F, n, x), GJ.mcol(~F, j, k)), M.dot(~F, GJ.vdrop(~F, n, y), GJ.mcol(~F, j, k))], E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZNeg{E.ZVar{1n}}}, E.ZAdd{E.ZVar{2n}, E.ZNeg{E.ZVar{3n}}}}, E.ZSub{E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, E.ZSub{E.ZVar{1n}, E.ZVar{3n}}}, {==})

# the defect of s x
def dk_scale(~F: O.OField, +n: Nat, +j: M.Mat(~F), +s: O.C(F), +x: M.Vec(~F), +k: Nat) -> {dk(~F, n, j, M.vscale(~F, s, x), k) == O.mul(F, s, dk(~F, n, j, x, k)) : O.C(F)}:
  %GJ.look_vscale(~F, s, x, k) : {O.sub(~F, _, M.dot(~F, GJ.vdrop(~F, n, M.vscale(~F, s, x)), GJ.mcol(~F, j, k))) == O.mul(F, s, dk(~F, n, j, x, k)) : O.C(F)}
  %drop_vscale(~F, n, s, x) : {O.sub(~F, O.mul(F, s, O.lookup(~F, x, k)), M.dot(~F, _, GJ.mcol(~F, j, k))) == O.mul(F, s, dk(~F, n, j, x, k)) : O.C(F)}
  %FM.dot_vscale(~F, s, GJ.vdrop(~F, n, x), GJ.mcol(~F, j, k)) : {O.sub(~F, O.mul(F, s, O.lookup(~F, x, k)), _) == O.mul(F, s, dk(~F, n, j, x, k)) : O.C(F)}
  FR.fring_eq(~F, [O.lookup(~F, x, k), M.dot(~F, GJ.vdrop(~F, n, x), GJ.mcol(~F, j, k)), s], E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{0n}}, E.ZMul{E.ZVar{2n}, E.ZVar{1n}}}, E.ZMul{E.ZVar{2n}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}}, {==})

# the defect of x + (-m) p
def dk_axpy(~F: O.OField, +n: Nat, +j: M.Mat(~F), +x: M.Vec(~F), +m: O.C(F), +p: M.Vec(~F), +k: Nat) -> {dk(~F, n, j, M.vadd(~F, x, M.vscale(~F, O.neg(F, m), p)), k) == O.add(F, dk(~F, n, j, x, k), O.mul(F, O.neg(F, m), dk(~F, n, j, p, k))) : O.C(F)}:
  %GJ.look_vadd(~F, x, M.vscale(~F, O.neg(F, m), p), k) : {O.sub(~F, _, M.dot(~F, GJ.vdrop(~F, n, M.vadd(~F, x, M.vscale(~F, O.neg(F, m), p))), GJ.mcol(~F, j, k))) == O.add(F, dk(~F, n, j, x, k), O.mul(F, O.neg(F, m), dk(~F, n, j, p, k))) : O.C(F)}
  %GJ.look_vscale(~F, O.neg(F, m), p, k) : {O.sub(~F, O.add(F, O.lookup(~F, x, k), _), M.dot(~F, GJ.vdrop(~F, n, M.vadd(~F, x, M.vscale(~F, O.neg(F, m), p))), GJ.mcol(~F, j, k))) == O.add(F, dk(~F, n, j, x, k), O.mul(F, O.neg(F, m), dk(~F, n, j, p, k))) : O.C(F)}
  %drop_vadd(~F, n, x, M.vscale(~F, O.neg(F, m), p)) : {O.sub(~F, O.add(F, O.lookup(~F, x, k), O.mul(F, O.neg(F, m), O.lookup(~F, p, k))), M.dot(~F, _, GJ.mcol(~F, j, k))) == O.add(F, dk(~F, n, j, x, k), O.mul(F, O.neg(F, m), dk(~F, n, j, p, k))) : O.C(F)}
  %drop_vscale(~F, n, O.neg(F, m), p) : {O.sub(~F, O.add(F, O.lookup(~F, x, k), O.mul(F, O.neg(F, m), O.lookup(~F, p, k))), M.dot(~F, M.vadd(~F, GJ.vdrop(~F, n, x), _), GJ.mcol(~F, j, k))) == O.add(F, dk(~F, n, j, x, k), O.mul(F, O.neg(F, m), dk(~F, n, j, p, k))) : O.C(F)}
  %FM.dot_vadd(~F, GJ.vdrop(~F, n, x), M.vscale(~F, O.neg(F, m), GJ.vdrop(~F, n, p)), GJ.mcol(~F, j, k)) : {O.sub(~F, O.add(F, O.lookup(~F, x, k), O.mul(F, O.neg(F, m), O.lookup(~F, p, k))), _) == O.add(F, dk(~F, n, j, x, k), O.mul(F, O.neg(F, m), dk(~F, n, j, p, k))) : O.C(F)}
  %FM.dot_vscale(~F, O.neg(F, m), GJ.vdrop(~F, n, p), GJ.mcol(~F, j, k)) : {O.sub(~F, O.add(F, O.lookup(~F, x, k), O.mul(F, O.neg(F, m), O.lookup(~F, p, k))), O.add(F, M.dot(~F, GJ.vdrop(~F, n, x), GJ.mcol(~F, j, k)), _)) == O.add(F, dk(~F, n, j, x, k), O.mul(F, O.neg(F, m), dk(~F, n, j, p, k))) : O.C(F)}
  FR.fring_eq(~F, [O.lookup(~F, x, k), O.lookup(~F, p, k), M.dot(~F, GJ.vdrop(~F, n, x), GJ.mcol(~F, j, k)), M.dot(~F, GJ.vdrop(~F, n, p), GJ.mcol(~F, j, k)), m], E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZNeg{E.ZVar{4n}}, E.ZVar{1n}}}, E.ZAdd{E.ZVar{2n}, E.ZMul{E.ZNeg{E.ZVar{4n}}, E.ZVar{3n}}}}, E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZNeg{E.ZVar{4n}}, E.ZSub{E.ZVar{1n}, E.ZVar{3n}}}}, {==})

# Entry bounds
# ------------

def look_bnd(~F: O.OField, v: M.Vec(~F), k: Nat, +t: O.C(F), h: M.vbnd.all(~F, v, t), +ht: O.le(~F, O.zero(F), t)) -> M.bnd(~F, O.lookup(~F, v, k), t):
  match v k:
    case Nil{} 0n:
      FM.bnd_zero(~F, t, ht)
    case Nil{} 1n+j:
      FM.bnd_zero(~F, t, ht)
    case Con{a, xs} 0n:
      (h1, h2) = h
      h1
    case Con{a, xs} 1n+j:
      (h1, h2) = h
      look_bnd(~F, xs, j, t, h2, ht)

def all_shift(~Q: Nat -> Data, m: Nat, h: GJ.All(~Q, 1n+m)) -> GJ.All(~(k => Q(1n+k)), m):
  match m:
    case 0n:
      Unit{}
    case 1n++j:
      match h:
        case (h1, q):
          (all_shift(~Q, j, h1), q)

# bounds on every entry by index give the bound on the list
def vall_of_all(~F: O.OField, v: M.Vec(~F), +t: O.C(F), +h: GJ.All(~(k => M.bnd(~F, O.lookup(~F, v, k), t)), M.len(~F, v))) -> M.vbnd.all(~F, v, t):
  match v:
    case Nil{}:
      Unit{}
    case Con{+a, +xs}:
      (GJ.all_at(~(k => M.bnd(~F, O.lookup(~F, Con{a, xs}, k), t)), 1n+M.len(~F, xs), h, 0n, {==}),
       vall_of_all(~F, xs, t, all_shift(~(k => M.bnd(~F, O.lookup(~F, Con{a, xs}, k), t)), M.len(~F, xs), h)))

def ofn_nn(~F: O.OField, m: Nat) -> O.le(~F, O.zero(F), FR.ofn(~F, m)):
  match m:
    case 0n:
      FO.le_refl(~F, O.zero(F))
    case 1n++k:
      FO.nonneg_add(~F, O.one(F), FR.ofn(~F, k), NP.one_nn(~F), ofn_nn(~F, k))

# m entries of size at most t sum to at most m t
def rowabs_le(~F: O.OField, r: M.Vec(~F), m: Nat, +t: O.C(F), h: M.vbnd.all(~F, r, t), +ht: O.le(~F, O.zero(F), t)) -> O.le(~F, NP.rowabs(~F, r, m), O.mul(F, FR.ofn(~F, m), t)):
  match r m:
    case Nil{} 0n:
      FV.le_rw_r(~F, O.zero(F), O.zero(F), O.mul(F, O.zero(F), t), Equal.sym(O.C(F), O.mul(F, O.zero(F), t), O.zero(F), FL.zero_mul(~F, t)), FO.le_refl(~F, O.zero(F)))
    case Nil{} 1n++k:
      FO.mul_nonneg(~F, FR.ofn(~F, 1n+k), t, ofn_nn(~F, 1n+k), ht)
    case Con{+a, +xs} 0n:
      FV.le_rw_r(~F, O.zero(F), O.zero(F), O.mul(F, O.zero(F), t), Equal.sym(O.C(F), O.mul(F, O.zero(F), t), O.zero(F), FL.zero_mul(~F, t)), FO.le_refl(~F, O.zero(F)))
    case Con{+a, +xs} 1n++k:
      (h1, h2) = h
      FV.le_rw_r(~F, NP.rowabs(~F, Con{a, xs}, 1n+k), O.add(F, t, O.mul(F, FR.ofn(~F, k), t)), O.mul(F, FR.ofn(~F, 1n+k), t), FR.fring_eq(~F, [t, FR.ofn(~F, k)], E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{0n}}}, E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{1n}}, E.ZVar{0n}}, {==}), RP.le_add2(~F, FV.fabs(~F, a), t, NP.rowabs(~F, xs, k), O.mul(F, FR.ofn(~F, k), t), FV.fabs_le(~F, a, t, h1), rowabs_le(~F, xs, k, t, h2, ht)))

# every entry of a is at most g
def mall(~F: O.OField, a: M.Mat(~F), +g: O.C(F)) -> Data:
  match a:
    case Nil{}:
      Unit
    case Con{r, t}:
      M.Both(M.vbnd.all(~F, r, g), mall(~F, t, g))

def vall_mcol(~F: O.OField, a: M.Mat(~F), +k: Nat, +g: O.C(F), h: mall(~F, a, g), +hg: O.le(~F, O.zero(F), g)) -> M.vbnd.all(~F, GJ.mcol(~F, a, k), g):
  match a:
    case Nil{}:
      Unit{}
    case Con{+r, +t}:
      (h1, h2) = h
      (look_bnd(~F, r, k, g, h1, hg), vall_mcol(~F, t, k, g, h2, hg))

def len_mcol(~F: O.OField, a: M.Mat(~F), +k: Nat) -> {M.len(~F, GJ.mcol(~F, a, k)) == GJ.nrows(~F, a) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{r, t}:
      Equal.cong(Nat, Nat, z => 1n+z, M.len(~F, GJ.mcol(~F, t, k)), GJ.nrows(~F, t), len_mcol(~F, t, k))

def vall_drop(~F: O.OField, k: Nat, v: M.Vec(~F), +t: O.C(F), h: M.vbnd.all(~F, v, t)) -> M.vbnd.all(~F, GJ.vdrop(~F, k, v), t):
  match k v:
    case 0n Nil{}:
      h
    case 0n Con{a, xs}:
      h
    case 1n+j Nil{}:
      Unit{}
    case 1n+j Con{a, xs}:
      (h1, h2) = h
      vall_drop(~F, j, xs, t, h2)


# the defect of an error row: |dk(e, k)| <= eps (1 + n g)
def dk_err(~F: O.OField, +n: Nat, +j: M.Mat(~F), +e: M.Vec(~F), +k: Nat, +ep: O.C(F), +g: O.C(F), +he: M.vbnd.all(~F, e, ep), +hep: O.le(~F, O.zero(F), ep), hj: mall(~F, j, g), +hg: O.le(~F, O.zero(F), g), hn: {GJ.nrows(~F, j) == n : Nat}) -> M.bnd(~F, dk(~F, n, j, e, k), O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))):
  KB.bnd_val(~F, O.add(F, O.lookup(~F, e, k), O.neg(F, M.dot(~F, GJ.vdrop(~F, n, e), GJ.mcol(~F, j, k)))), O.sub(~F, O.lookup(~F, e, k), M.dot(~F, GJ.vdrop(~F, n, e), GJ.mcol(~F, j, k))), O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g))), FR.fring_eq(~F, [O.lookup(~F, e, k), M.dot(~F, GJ.vdrop(~F, n, e), GJ.mcol(~F, j, k)), NP.rowabs(~F, GJ.vdrop(~F, n, e), n), FR.ofn(~F, n), ep, g], E.ZAdd{E.ZVar{0n}, E.ZNeg{E.ZVar{1n}}}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, {==}),
    FM.bnd_eq(~F, O.add(F, O.lookup(~F, e, k), O.neg(F, M.dot(~F, GJ.vdrop(~F, n, e), GJ.mcol(~F, j, k)))), O.add(F, ep, O.mul(F, O.mul(F, FR.ofn(~F, n), ep), g)), O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g))), FR.fring_eq(~F, [O.lookup(~F, e, k), M.dot(~F, GJ.vdrop(~F, n, e), GJ.mcol(~F, j, k)), NP.rowabs(~F, GJ.vdrop(~F, n, e), n), FR.ofn(~F, n), ep, g], E.ZAdd{E.ZVar{4n}, E.ZMul{E.ZMul{E.ZVar{3n}, E.ZVar{4n}}, E.ZVar{5n}}}, E.ZMul{E.ZVar{4n}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZVar{3n}, E.ZVar{5n}}}}, {==}),
      FM.bnd_add(~F, O.lookup(~F, e, k), ep, O.neg(F, M.dot(~F, GJ.vdrop(~F, n, e), GJ.mcol(~F, j, k))), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), g), look_bnd(~F, e, k, ep, he, hep),
        FM.bnd_neg(~F, M.dot(~F, GJ.vdrop(~F, n, e), GJ.mcol(~F, j, k)), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), g), FM.bnd_mono(~F, M.dot(~F, GJ.vdrop(~F, n, e), GJ.mcol(~F, j, k)), O.mul(F, NP.rowabs(~F, GJ.vdrop(~F, n, e), n), g), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), g),
          (%Equal.trans(Nat, M.len(~F, GJ.mcol(~F, j, k)), GJ.nrows(~F, j), n, len_mcol(~F, j, k), hn) : M.bnd(~F, M.dot(~F, GJ.vdrop(~F, n, e), GJ.mcol(~F, j, k)), O.mul(F, NP.rowabs(~F, GJ.vdrop(~F, n, e), _), g))
            NP.dot_le(~F, GJ.vdrop(~F, n, e), GJ.mcol(~F, j, k), g, vall_mcol(~F, j, k, g, hj, hg), hg)),
          FM.sub_nonneg(~F, O.mul(F, NP.rowabs(~F, GJ.vdrop(~F, n, e), n), g), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), g), FV.mul_le_r(~F, NP.rowabs(~F, GJ.vdrop(~F, n, e), n), O.mul(F, FR.ofn(~F, n), ep), g, hg, rowabs_le(~F, GJ.vdrop(~F, n, e), n, ep, vall_drop(~F, n, e, ep, he), hep))))))))

# Entries by index
# ----------------

def look_diff(~F: O.OField, +w: M.Vec(~F), +u: M.Vec(~F), +k: Nat) -> {O.lookup(~F, M.vadd(~F, w, M.vneg(~F, u)), k) == O.sub(~F, O.lookup(~F, w, k), O.lookup(~F, u, k)) : O.C(F)}:
  %GJ.look_vadd(~F, w, M.vneg(~F, u), k) : {_ == O.sub(~F, O.lookup(~F, w, k), O.lookup(~F, u, k)) : O.C(F)}
  %GJ.look_vneg(~F, u, k) : {O.add(F, O.lookup(~F, w, k), _) == O.sub(~F, O.lookup(~F, w, k), O.lookup(~F, u, k)) : O.C(F)}
  {==}

# a bound on every entry, by index, bounds the list
def vall_by(~F: O.OField, ~v: M.Vec(~F), ~t: O.C(F), ~f: @k: Nat -> M.bnd(~F, O.lookup(~F, v, k), t)) -> M.vbnd.all(~F, v, t):
  vall_of_all(~F, v, t, GJ.all_mk(~M.len(~F, v), ~(k => M.bnd(~F, O.lookup(~F, v, k), t)), ~(k => hk => f(k)), M.len(~F, v), GJ.le_refl(M.len(~F, v))))

def ne_lt(j: Nat, c: Nat, h: {KA.natle(1n+j, c) == True{} : Bool}) -> {KA.nateq(c, j) == False{} : Bool}:
  match j c:
    case 0n 0n:
      FO.absurd({KA.nateq(0n, 0n) == False{} : Bool}, KA.ft(h))
    case 0n 1n+b:
      {==}
    case 1n+a 0n:
      FO.absurd({KA.nateq(0n, 1n+a) == False{} : Bool}, KA.ft(h))
    case 1n+a 1n+b:
      ne_lt(a, b, h)

def neg_contra(~F: O.OField, +x: O.C(F), hl: O.le(~F, x, O.zero(F)), e: {x == O.one(F) : O.C(F)}) -> Empty:
  O.lt_irrefl(F)(O.zero(F))(FO.lt_le_trans(~F, O.zero(F), x, O.zero(F), FO.lt_subst_r(~F, O.one(F), x, O.zero(F), Equal.sym(O.C(F), x, O.one(F), e), O.zero_lt_one(F)), hl))

def fabs_inv.go(~F: O.OField, +q: O.C(F), +p: O.C(F), tq: Or(O.lt(F, q, O.zero(F)), Or({q == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), q))), tp: Or(O.lt(F, p, O.zero(F)), Or({p == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), p))), +e: {O.mul(F, q, p) == O.one(F) : O.C(F)}) -> {O.mul(F, FV.fabs.go(~F, q, tq), FV.fabs.go(~F, p, tp)) == O.one(F) : O.C(F)}:
  match tq tp:
    case Inl{lq} Inl{lp}:
      Equal.trans(O.C(F), O.mul(F, O.neg(F, q), O.neg(F, p)), O.mul(F, q, p), O.one(F), FR.fring_eq(~F, [q, p], E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZNeg{E.ZVar{1n}}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, {==}), e)
    case Inl{lq} Inr{rp}:
      FO.absurd({O.mul(F, O.neg(F, q), p) == O.one(F) : O.C(F)}, neg_contra(~F, O.mul(F, q, p), RL.le_rw_l(~F, O.mul(F, p, q), O.mul(F, q, p), O.zero(F), FR.fring_eq(~F, [q, p], E.ZMul{E.ZVar{1n}, E.ZVar{0n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, {==}), FV.sle0(~F, p, q, FV.nn_of_ge.go(~F, p, rp), FO.lt_le(~F, q, O.zero(F), lq))), e))
    case Inr{rq} Inl{lp}:
      FO.absurd({O.mul(F, q, O.neg(F, p)) == O.one(F) : O.C(F)}, neg_contra(~F, O.mul(F, q, p), FV.sle0(~F, q, p, FV.nn_of_ge.go(~F, q, rq), FO.lt_le(~F, p, O.zero(F), lp)), e))
    case Inr{rq} Inr{rp}:
      e

# q p = 1 gives |q| |p| = 1
def fabs_inv(~F: O.OField, +q: O.C(F), +p: O.C(F), +e: {O.mul(F, q, p) == O.one(F) : O.C(F)}) -> {O.mul(F, FV.fabs(~F, q), FV.fabs(~F, p)) == O.one(F) : O.C(F)}:
  fabs_inv.go(~F, q, p, O.lt_total(F)(q, O.zero(F)), O.lt_total(F)(p, O.zero(F)), e)

# Rows during the elimination
# ---------------------------
# A row x at index i after c columns: 2n entries, each at most G; its
# defect entries at most D; its first c entries within P of the unit
# vector's.

def fin(~F: O.OField, +x: M.Vec(~F), +i: Nat, +c: Nat, +ph: O.C(F)) -> Data:
  GJ.All(~(j => M.bnd(~F, O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, KA.nateq(i, j))), ph)), c)

def dfb(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +dd: O.C(F)) -> Data:
  GJ.All(~(k => M.bnd(~F, dk(~F, n, jm, x, k), dd)), n)

def rowinv(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +i: Nat, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F)) -> Data:
  M.Both({M.len(~F, x) == Nat.add(n, n) : Nat}, M.Both(M.vbnd.all(~F, x, gg), M.Both(dfb(~F, n, jm, x, dd), fin(~F, x, i, c, ph))))

def ri_mk(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +i: Nat, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), hl: {M.len(~F, x) == Nat.add(n, n) : Nat}, he: M.vbnd.all(~F, x, gg), hd: dfb(~F, n, jm, x, dd), hf: fin(~F, x, i, c, ph)) -> rowinv(~F, n, jm, x, i, c, gg, dd, ph):
  (hl, (he, (hd, hf)))

def ri_len(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +i: Nat, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), h: rowinv(~F, n, jm, x, i, c, gg, dd, ph)) -> {M.len(~F, x) == Nat.add(n, n) : Nat}:
  (a, b) = h
  a

def ri_r1(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +i: Nat, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), h: rowinv(~F, n, jm, x, i, c, gg, dd, ph)) -> M.Both(M.vbnd.all(~F, x, gg), M.Both(dfb(~F, n, jm, x, dd), fin(~F, x, i, c, ph))):
  (a, b) = h
  b

def ri_e.go(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +i: Nat, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), h: M.Both(M.vbnd.all(~F, x, gg), M.Both(dfb(~F, n, jm, x, dd), fin(~F, x, i, c, ph)))) -> M.vbnd.all(~F, x, gg):
  (a, b) = h
  a

def ri_r2(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +i: Nat, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), h: M.Both(M.vbnd.all(~F, x, gg), M.Both(dfb(~F, n, jm, x, dd), fin(~F, x, i, c, ph)))) -> M.Both(dfb(~F, n, jm, x, dd), fin(~F, x, i, c, ph)):
  (a, b) = h
  b

def ri_d.go(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +i: Nat, +c: Nat, +dd: O.C(F), +ph: O.C(F), h: M.Both(dfb(~F, n, jm, x, dd), fin(~F, x, i, c, ph))) -> dfb(~F, n, jm, x, dd):
  (a, b) = h
  a

def ri_f.go(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +i: Nat, +c: Nat, +dd: O.C(F), +ph: O.C(F), h: M.Both(dfb(~F, n, jm, x, dd), fin(~F, x, i, c, ph))) -> fin(~F, x, i, c, ph):
  (a, b) = h
  b

def ri_e(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +i: Nat, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), h: rowinv(~F, n, jm, x, i, c, gg, dd, ph)) -> M.vbnd.all(~F, x, gg):
  ri_e.go(~F, n, jm, x, i, c, gg, dd, ph, ri_r1(~F, n, jm, x, i, c, gg, dd, ph, h))

def ri_d(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +i: Nat, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), h: rowinv(~F, n, jm, x, i, c, gg, dd, ph)) -> dfb(~F, n, jm, x, dd):
  ri_d.go(~F, n, jm, x, i, c, dd, ph, ri_r2(~F, n, jm, x, i, c, gg, dd, ph, ri_r1(~F, n, jm, x, i, c, gg, dd, ph, h)))

def ri_f(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +i: Nat, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), h: rowinv(~F, n, jm, x, i, c, gg, dd, ph)) -> fin(~F, x, i, c, ph):
  ri_f.go(~F, n, jm, x, i, c, dd, ph, ri_r2(~F, n, jm, x, i, c, gg, dd, ph, ri_r1(~F, n, jm, x, i, c, gg, dd, ph, h)))

# The pivot row
# -------------
# p = s x rounded (x the pivot row, s near q = 1/x_c): its entries, defect
# and finished columns, column c now among them.

# |p_k - s x_k| <= eps
def diff_ent(~F: O.OField, +p: M.Vec(~F), +s: O.C(F), +x: M.Vec(~F), +k: Nat, +ep: O.C(F), +hp: M.vbnd.all(~F, M.vadd(~F, p, M.vneg(~F, M.vscale(~F, s, x))), ep), +hep: O.le(~F, O.zero(F), ep)) -> M.bnd(~F, O.sub(~F, O.lookup(~F, p, k), O.mul(F, s, O.lookup(~F, x, k))), ep):
  %Equal.sym(O.C(F), O.mul(F, s, O.lookup(~F, x, k)), O.lookup(~F, M.vscale(~F, s, x), k), GJ.look_vscale(~F, s, x, k)) : M.bnd(~F, O.sub(~F, O.lookup(~F, p, k), _), ep)
  %look_diff(~F, p, M.vscale(~F, s, x), k) : M.bnd(~F, _, ep)
  look_bnd(~F, M.vadd(~F, p, M.vneg(~F, M.vscale(~F, s, x))), k, ep, hp, hep)

# |dk(p) - s dk(x)| <= eps (1 + n g)
def diff_dk(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +p: M.Vec(~F), +s: O.C(F), +x: M.Vec(~F), +k: Nat, +ep: O.C(F), +g: O.C(F), +hp: M.vbnd.all(~F, M.vadd(~F, p, M.vneg(~F, M.vscale(~F, s, x))), ep), +hep: O.le(~F, O.zero(F), ep), +hj: mall(~F, jm, g), +hg: O.le(~F, O.zero(F), g), +hn: {GJ.nrows(~F, jm) == n : Nat}) -> M.bnd(~F, O.sub(~F, dk(~F, n, jm, p, k), O.mul(F, s, dk(~F, n, jm, x, k))), O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))):
  %dk_scale(~F, n, jm, s, x, k) : M.bnd(~F, O.sub(~F, dk(~F, n, jm, p, k), _), O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g))))
  %dk_sub(~F, n, jm, p, M.vscale(~F, s, x), k) : M.bnd(~F, _, O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g))))
  dk_err(~F, n, jm, M.vadd(~F, p, M.vneg(~F, M.vscale(~F, s, x))), k, ep, g, hp, hep, hj, hg, hn)

# y = s z + (y - s z): |y| <= sg zz + eps
def near_bnd(~F: O.OField, +y: O.C(F), +s: O.C(F), +z: O.C(F), +sg: O.C(F), +zz: O.C(F), +ep: O.C(F), hs: M.bnd(~F, s, sg), hz: M.bnd(~F, z, zz), hd: M.bnd(~F, O.sub(~F, y, O.mul(F, s, z)), ep)) -> M.bnd(~F, y, O.add(F, O.mul(F, sg, zz), ep)):
  KB.bnd_val(~F, O.add(F, O.mul(F, s, z), O.sub(~F, y, O.mul(F, s, z))), y, O.add(F, O.mul(F, sg, zz), ep), FR.fring_eq(~F, [y, s, z], E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZSub{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZVar{0n}, {==}), FM.bnd_add(~F, O.mul(F, s, z), O.mul(F, sg, zz), O.sub(~F, y, O.mul(F, s, z)), ep, FM.bnd_mul(~F, s, sg, z, zz, hs, hz), hd))

def prow_e(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +hx: rowinv(~F, n, jm, x, c, c, gg, dd, ph), +hgg: O.le(~F, O.zero(F), gg), +s: O.C(F), +sg: O.C(F), +hsg: M.bnd(~F, s, sg), +p: M.Vec(~F), +ep: O.C(F), +hp: M.vbnd.all(~F, M.vadd(~F, p, M.vneg(~F, M.vscale(~F, s, x))), ep), +hep: O.le(~F, O.zero(F), ep), +k: Nat) -> M.bnd(~F, O.lookup(~F, p, k), O.add(F, O.mul(F, sg, gg), ep)):
  near_bnd(~F, O.lookup(~F, p, k), s, O.lookup(~F, x, k), sg, gg, ep, hsg, look_bnd(~F, x, k, gg, ri_e(~F, n, jm, x, c, c, gg, dd, ph, hx), hgg), diff_ent(~F, p, s, x, k, ep, hp, hep))

def prow_d(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +hx: rowinv(~F, n, jm, x, c, c, gg, dd, ph), +s: O.C(F), +sg: O.C(F), +hsg: M.bnd(~F, s, sg), +p: M.Vec(~F), +ep: O.C(F), +hp: M.vbnd.all(~F, M.vadd(~F, p, M.vneg(~F, M.vscale(~F, s, x))), ep), +hep: O.le(~F, O.zero(F), ep), +g: O.C(F), +hj: mall(~F, jm, g), +hg: O.le(~F, O.zero(F), g), +hn: {GJ.nrows(~F, jm) == n : Nat}, +k: Nat, hk: {KA.natle(1n+k, n) == True{} : Bool}) -> M.bnd(~F, dk(~F, n, jm, p, k), O.add(F, O.mul(F, sg, dd), O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g))))):
  near_bnd(~F, dk(~F, n, jm, p, k), s, dk(~F, n, jm, x, k), sg, dd, O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g))), hsg, GJ.all_at(~(i => M.bnd(~F, dk(~F, n, jm, x, i), dd)), n, ri_d(~F, n, jm, x, c, c, gg, dd, ph, hx), k, hk), diff_dk(~F, n, jm, p, s, x, k, ep, g, hp, hep, hj, hg, hn))

# the earlier columns of p: within sg ph + eps of 0
def pf_lt(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +hx: rowinv(~F, n, jm, x, c, c, gg, dd, ph), +s: O.C(F), +sg: O.C(F), +hsg: M.bnd(~F, s, sg), +p: M.Vec(~F), +ep: O.C(F), +hp: M.vbnd.all(~F, M.vadd(~F, p, M.vneg(~F, M.vscale(~F, s, x))), ep), +hep: O.le(~F, O.zero(F), ep), +u: O.C(F), +hu: O.le(~F, O.zero(F), u), +j: Nat, +hj: {KA.natle(1n+j, c) == True{} : Bool}) -> M.bnd(~F, O.sub(~F, O.lookup(~F, p, j), GJ.dl(~F, KA.nateq(c, j))), O.add(F, O.add(F, O.mul(F, sg, ph), u), ep)):
  %Equal.sym(Bool, KA.nateq(c, j), False{}, ne_lt(j, c, hj)) : M.bnd(~F, O.sub(~F, O.lookup(~F, p, j), GJ.dl(~F, _)), O.add(F, O.add(F, O.mul(F, sg, ph), u), ep))
  FM.bnd_mono(~F, O.sub(~F, O.lookup(~F, p, j), O.zero(F)), O.add(F, O.mul(F, sg, ph), ep), O.add(F, O.add(F, O.mul(F, sg, ph), u), ep),
    near_bnd(~F, O.sub(~F, O.lookup(~F, p, j), O.zero(F)), s, O.sub(~F, O.lookup(~F, x, j), O.zero(F)), sg, ph, ep, hsg,
      (%ne_lt(j, c, hj) : M.bnd(~F, O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, _)), ph)
        GJ.all_at(~(i => M.bnd(~F, O.sub(~F, O.lookup(~F, x, i), GJ.dl(~F, KA.nateq(c, i))), ph)), c, ri_f(~F, n, jm, x, c, c, gg, dd, ph, hx), j, hj)),
      KB.bnd_val(~F, O.sub(~F, O.lookup(~F, p, j), O.mul(F, s, O.lookup(~F, x, j))), O.sub(~F, O.sub(~F, O.lookup(~F, p, j), O.zero(F)), O.mul(F, s, O.sub(~F, O.lookup(~F, x, j), O.zero(F)))), ep, FR.fring_eq(~F, [O.lookup(~F, p, j), O.lookup(~F, x, j), s], E.ZSub{E.ZVar{0n}, E.ZMul{E.ZVar{2n}, E.ZVar{1n}}}, E.ZSub{E.ZSub{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZMul{E.ZVar{2n}, E.ZSub{E.ZVar{1n}, E.ZCst{S.Z0{}}}}}, {==}), diff_ent(~F, p, s, x, j, ep, hp, hep))),
    FM.nn_eq(~F, O.sub(~F, O.add(F, O.add(F, O.mul(F, sg, ph), u), ep), O.add(F, O.mul(F, sg, ph), ep)), u, FR.fring_eq(~F, [O.mul(F, sg, ph), u, ep], E.ZVar{1n}, E.ZSub{E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZAdd{E.ZVar{0n}, E.ZVar{2n}}}, {==}), hu))


# column c of p: within u + eps of 1
def pf_c(~F: O.OField, +x: M.Vec(~F), +c: Nat, +ph: O.C(F), +s: O.C(F), +sg: O.C(F), +q: O.C(F), +u: O.C(F), +hsg: M.bnd(~F, s, sg), +hph: O.le(~F, O.zero(F), ph), +hq: {O.mul(F, q, O.lookup(~F, x, c)) == O.one(F) : O.C(F)}, hs: M.bnd(~F, O.sub(~F, s, q), O.mul(F, FV.fabs(~F, q), u)), +p: M.Vec(~F), +ep: O.C(F), +hp: M.vbnd.all(~F, M.vadd(~F, p, M.vneg(~F, M.vscale(~F, s, x))), ep), +hep: O.le(~F, O.zero(F), ep)) -> M.bnd(~F, O.sub(~F, O.lookup(~F, p, c), GJ.dl(~F, KA.nateq(c, c))), O.add(F, O.add(F, O.mul(F, sg, ph), u), ep)):
  %Equal.sym(Bool, KA.nateq(c, c), True{}, SL.nateq_refl(c)) : M.bnd(~F, O.sub(~F, O.lookup(~F, p, c), GJ.dl(~F, _)), O.add(F, O.add(F, O.mul(F, sg, ph), u), ep))
  FM.bnd_mono(~F, O.sub(~F, O.lookup(~F, p, c), O.one(F)), O.add(F, u, ep), O.add(F, O.add(F, O.mul(F, sg, ph), u), ep),
    KB.bnd_val(~F, O.add(F, O.mul(F, O.sub(~F, s, q), O.lookup(~F, x, c)), O.sub(~F, O.lookup(~F, p, c), O.mul(F, s, O.lookup(~F, x, c)))), O.sub(~F, O.lookup(~F, p, c), O.one(F)), O.add(F, u, ep), FO.eq_of_sub(~F, O.add(F, O.mul(F, O.sub(~F, s, q), O.lookup(~F, x, c)), O.sub(~F, O.lookup(~F, p, c), O.mul(F, s, O.lookup(~F, x, c)))), O.sub(~F, O.lookup(~F, p, c), O.one(F)), FO.cert1(~F, O.sub(~F, O.add(F, O.mul(F, O.sub(~F, s, q), O.lookup(~F, x, c)), O.sub(~F, O.lookup(~F, p, c), O.mul(F, s, O.lookup(~F, x, c)))), O.sub(~F, O.lookup(~F, p, c), O.one(F))), O.neg(F, O.one(F)), O.sub(~F, O.mul(F, q, O.lookup(~F, x, c)), O.one(F)), FR.fring_eq(~F, [O.lookup(~F, p, c), O.lookup(~F, x, c), s, q, u, FV.fabs(~F, q), FV.fabs(~F, O.lookup(~F, x, c))], E.ZSub{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{3n}}, E.ZVar{1n}}, E.ZSub{E.ZVar{0n}, E.ZMul{E.ZVar{2n}, E.ZVar{1n}}}}, E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZNeg{E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZMul{E.ZVar{3n}, E.ZVar{1n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), FO.sub_of_eq(~F, O.mul(F, q, O.lookup(~F, x, c)), O.one(F), hq))),
      FM.bnd_add(~F, O.mul(F, O.sub(~F, s, q), O.lookup(~F, x, c)), u, O.sub(~F, O.lookup(~F, p, c), O.mul(F, s, O.lookup(~F, x, c))), ep,
        FM.bnd_eq(~F, O.mul(F, O.sub(~F, s, q), O.lookup(~F, x, c)), O.mul(F, O.mul(F, FV.fabs(~F, q), u), FV.fabs(~F, O.lookup(~F, x, c))), u, FO.eq_of_sub(~F, O.mul(F, O.mul(F, FV.fabs(~F, q), u), FV.fabs(~F, O.lookup(~F, x, c))), u, FO.cert1(~F, O.sub(~F, O.mul(F, O.mul(F, FV.fabs(~F, q), u), FV.fabs(~F, O.lookup(~F, x, c))), u), u, O.sub(~F, O.mul(F, FV.fabs(~F, q), FV.fabs(~F, O.lookup(~F, x, c))), O.one(F)), FR.fring_eq(~F, [O.lookup(~F, p, c), O.lookup(~F, x, c), s, q, u, FV.fabs(~F, q), FV.fabs(~F, O.lookup(~F, x, c))], E.ZSub{E.ZMul{E.ZMul{E.ZVar{5n}, E.ZVar{4n}}, E.ZVar{6n}}, E.ZVar{4n}}, E.ZMul{E.ZVar{4n}, E.ZSub{E.ZMul{E.ZVar{5n}, E.ZVar{6n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), FO.sub_of_eq(~F, O.mul(F, FV.fabs(~F, q), FV.fabs(~F, O.lookup(~F, x, c))), O.one(F), fabs_inv(~F, q, O.lookup(~F, x, c), hq)))),
          FM.bnd_mul(~F, O.sub(~F, s, q), O.mul(F, FV.fabs(~F, q), u), O.lookup(~F, x, c), FV.fabs(~F, O.lookup(~F, x, c)), hs, FV.fabs_bnd(~F, O.lookup(~F, x, c)))),
        diff_ent(~F, p, s, x, c, ep, hp, hep))),
    FM.nn_eq(~F, O.sub(~F, O.add(F, O.add(F, O.mul(F, sg, ph), u), ep), O.add(F, u, ep)), O.mul(F, sg, ph), FR.fring_eq(~F, [O.mul(F, sg, ph), u, ep], E.ZVar{0n}, E.ZSub{E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}, {==}), FO.mul_nonneg(~F, sg, ph, FM.bnd_nonneg(~F, s, sg, hsg), hph)))

# the rounded pivot row satisfies the invariant after column c
def prow(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +hx: rowinv(~F, n, jm, x, c, c, gg, dd, ph), +hgg: O.le(~F, O.zero(F), gg), +hph: O.le(~F, O.zero(F), ph), +s: O.C(F), +sg: O.C(F), +q: O.C(F), +u: O.C(F), +hsg: M.bnd(~F, s, sg), +hq: {O.mul(F, q, O.lookup(~F, x, c)) == O.one(F) : O.C(F)}, +hs: M.bnd(~F, O.sub(~F, s, q), O.mul(F, FV.fabs(~F, q), u)), +hu: O.le(~F, O.zero(F), u), +p: M.Vec(~F), +lp: {M.len(~F, p) == Nat.add(n, n) : Nat}, +ep: O.C(F), +hp: M.vbnd.all(~F, M.vadd(~F, p, M.vneg(~F, M.vscale(~F, s, x))), ep), +hep: O.le(~F, O.zero(F), ep), +g: O.C(F), +hj: mall(~F, jm, g), +hg: O.le(~F, O.zero(F), g), +hn: {GJ.nrows(~F, jm) == n : Nat}) -> rowinv(~F, n, jm, p, c, 1n+c, O.add(F, O.mul(F, sg, gg), ep), O.add(F, O.mul(F, sg, dd), O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))), O.add(F, O.add(F, O.mul(F, sg, ph), u), ep)):
  ri_mk(~F, n, jm, p, c, 1n+c, O.add(F, O.mul(F, sg, gg), ep), O.add(F, O.mul(F, sg, dd), O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))), O.add(F, O.add(F, O.mul(F, sg, ph), u), ep), lp,
    vall_by(~F, ~p, ~O.add(F, O.mul(F, sg, gg), ep), ~(k => prow_e(~F, n, jm, x, c, gg, dd, ph, hx, hgg, s, sg, hsg, p, ep, hp, hep, k))),
    GJ.all_mk(~n, ~(k => M.bnd(~F, dk(~F, n, jm, p, k), O.add(F, O.mul(F, sg, dd), O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))))), ~(k => hk => prow_d(~F, n, jm, x, c, gg, dd, ph, hx, s, sg, hsg, p, ep, hp, hep, g, hj, hg, hn, k, hk)), n, GJ.le_refl(n)),
    (GJ.all_mk(~c, ~(j => M.bnd(~F, O.sub(~F, O.lookup(~F, p, j), GJ.dl(~F, KA.nateq(c, j))), O.add(F, O.add(F, O.mul(F, sg, ph), u), ep))), ~(j => hj => pf_lt(~F, n, jm, x, c, gg, dd, ph, hx, s, sg, hsg, p, ep, hp, hep, u, hu, j, hj)), c, GJ.le_refl(c)),
     pf_c(~F, x, c, ph, s, sg, q, u, hsg, hph, hq, hs, p, ep, hp, hep)))

# The other rows
# --------------
# x' = x - m p rounded, m = x_c: entries, defect and finished columns.

# y near a + mm b: |y| <= A + M B + E
def three(~F: O.OField, +y: O.C(F), +a: O.C(F), +mm: O.C(F), +b: O.C(F), +aa: O.C(F), +mb: O.C(F), +bb: O.C(F), +ee: O.C(F), ha: M.bnd(~F, a, aa), hm: M.bnd(~F, mm, mb), hb: M.bnd(~F, b, bb), hd: M.bnd(~F, O.sub(~F, y, O.add(F, a, O.mul(F, mm, b))), ee)) -> M.bnd(~F, y, O.add(F, O.add(F, aa, O.mul(F, mb, bb)), ee)):
  KB.bnd_val(~F, O.add(F, O.add(F, a, O.mul(F, mm, b)), O.sub(~F, y, O.add(F, a, O.mul(F, mm, b)))), y, O.add(F, O.add(F, aa, O.mul(F, mb, bb)), ee), FR.fring_eq(~F, [y, a, mm, b], E.ZAdd{E.ZAdd{E.ZVar{1n}, E.ZMul{E.ZVar{2n}, E.ZVar{3n}}}, E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZMul{E.ZVar{2n}, E.ZVar{3n}}}}}, E.ZVar{0n}, {==}),
    FM.bnd_add(~F, O.add(F, a, O.mul(F, mm, b)), O.add(F, aa, O.mul(F, mb, bb)), O.sub(~F, y, O.add(F, a, O.mul(F, mm, b))), ee, FM.bnd_add(~F, a, aa, O.mul(F, mm, b), O.mul(F, mb, bb), ha, FM.bnd_mul(~F, mm, mb, b, bb, hm, hb)), hd))

# |x'_k - (x_k - m p_k)| <= eps
def oent(~F: O.OField, +x2: M.Vec(~F), +x: M.Vec(~F), +m: O.C(F), +p: M.Vec(~F), +k: Nat, +ep: O.C(F), +he: M.vbnd.all(~F, M.vadd(~F, x2, M.vneg(~F, M.vadd(~F, x, M.vscale(~F, O.neg(F, m), p)))), ep), +hep: O.le(~F, O.zero(F), ep)) -> M.bnd(~F, O.sub(~F, O.lookup(~F, x2, k), O.add(F, O.lookup(~F, x, k), O.mul(F, O.neg(F, m), O.lookup(~F, p, k)))), ep):
  %Equal.sym(O.C(F), O.mul(F, O.neg(F, m), O.lookup(~F, p, k)), O.lookup(~F, M.vscale(~F, O.neg(F, m), p), k), GJ.look_vscale(~F, O.neg(F, m), p, k)) : M.bnd(~F, O.sub(~F, O.lookup(~F, x2, k), O.add(F, O.lookup(~F, x, k), _)), ep)
  %Equal.sym(O.C(F), O.add(F, O.lookup(~F, x, k), O.lookup(~F, M.vscale(~F, O.neg(F, m), p), k)), O.lookup(~F, M.vadd(~F, x, M.vscale(~F, O.neg(F, m), p)), k), GJ.look_vadd(~F, x, M.vscale(~F, O.neg(F, m), p), k)) : M.bnd(~F, O.sub(~F, O.lookup(~F, x2, k), _), ep)
  %look_diff(~F, x2, M.vadd(~F, x, M.vscale(~F, O.neg(F, m), p)), k) : M.bnd(~F, _, ep)
  look_bnd(~F, M.vadd(~F, x2, M.vneg(~F, M.vadd(~F, x, M.vscale(~F, O.neg(F, m), p)))), k, ep, he, hep)

# |dk(x') - (dk(x) - m dk(p))| <= eps (1 + n g)
def odk(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x2: M.Vec(~F), +x: M.Vec(~F), +m: O.C(F), +p: M.Vec(~F), +k: Nat, +ep: O.C(F), +g: O.C(F), +he: M.vbnd.all(~F, M.vadd(~F, x2, M.vneg(~F, M.vadd(~F, x, M.vscale(~F, O.neg(F, m), p)))), ep), +hep: O.le(~F, O.zero(F), ep), +hj: mall(~F, jm, g), +hg: O.le(~F, O.zero(F), g), +hn: {GJ.nrows(~F, jm) == n : Nat}) -> M.bnd(~F, O.sub(~F, dk(~F, n, jm, x2, k), O.add(F, dk(~F, n, jm, x, k), O.mul(F, O.neg(F, m), dk(~F, n, jm, p, k)))), O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))):
  %dk_axpy(~F, n, jm, x, m, p, k) : M.bnd(~F, O.sub(~F, dk(~F, n, jm, x2, k), _), O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g))))
  %dk_sub(~F, n, jm, x2, M.vadd(~F, x, M.vscale(~F, O.neg(F, m), p)), k) : M.bnd(~F, _, O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g))))
  dk_err(~F, n, jm, M.vadd(~F, x2, M.vneg(~F, M.vadd(~F, x, M.vscale(~F, O.neg(F, m), p)))), k, ep, g, he, hep, hj, hg, hn)

def orow_e(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x2: M.Vec(~F), +x: M.Vec(~F), +i: Nat, +c: Nat, +p: M.Vec(~F), +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +gp: O.C(F), +dp: O.C(F), +pp: O.C(F), +ep: O.C(F), +g: O.C(F), +hx: rowinv(~F, n, jm, x, i, c, gg, dd, ph), +hp: rowinv(~F, n, jm, p, c, 1n+c, gp, dp, pp), +he: M.vbnd.all(~F, M.vadd(~F, x2, M.vneg(~F, M.vadd(~F, x, M.vscale(~F, O.neg(F, O.lookup(~F, x, c)), p)))), ep), +hgg: O.le(~F, O.zero(F), gg), +hgp: O.le(~F, O.zero(F), gp), +hph: O.le(~F, O.zero(F), ph), +hep: O.le(~F, O.zero(F), ep), +hj: mall(~F, jm, g), +hg: O.le(~F, O.zero(F), g), +hn: {GJ.nrows(~F, jm) == n : Nat}, +k: Nat) -> M.bnd(~F, O.lookup(~F, x2, k), O.add(F, O.add(F, gg, O.mul(F, gg, gp)), ep)):
  three(~F, O.lookup(~F, x2, k), O.lookup(~F, x, k), O.neg(F, O.lookup(~F, x, c)), O.lookup(~F, p, k), gg, gg, gp, ep, look_bnd(~F, x, k, gg, ri_e(~F, n, jm, x, i, c, gg, dd, ph, hx), hgg), FM.bnd_neg(~F, O.lookup(~F, x, c), gg, look_bnd(~F, x, c, gg, ri_e(~F, n, jm, x, i, c, gg, dd, ph, hx), hgg)), look_bnd(~F, p, k, gp, ri_e(~F, n, jm, p, c, 1n+c, gp, dp, pp, hp), hgp), oent(~F, x2, x, O.lookup(~F, x, c), p, k, ep, he, hep))

def orow_d(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x2: M.Vec(~F), +x: M.Vec(~F), +i: Nat, +c: Nat, +p: M.Vec(~F), +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +gp: O.C(F), +dp: O.C(F), +pp: O.C(F), +ep: O.C(F), +g: O.C(F), +hx: rowinv(~F, n, jm, x, i, c, gg, dd, ph), +hp: rowinv(~F, n, jm, p, c, 1n+c, gp, dp, pp), +he: M.vbnd.all(~F, M.vadd(~F, x2, M.vneg(~F, M.vadd(~F, x, M.vscale(~F, O.neg(F, O.lookup(~F, x, c)), p)))), ep), +hgg: O.le(~F, O.zero(F), gg), +hgp: O.le(~F, O.zero(F), gp), +hph: O.le(~F, O.zero(F), ph), +hep: O.le(~F, O.zero(F), ep), +hj: mall(~F, jm, g), +hg: O.le(~F, O.zero(F), g), +hn: {GJ.nrows(~F, jm) == n : Nat}, +k: Nat, +hk: {KA.natle(1n+k, n) == True{} : Bool}) -> M.bnd(~F, dk(~F, n, jm, x2, k), O.add(F, O.add(F, dd, O.mul(F, gg, dp)), O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g))))):
  three(~F, dk(~F, n, jm, x2, k), dk(~F, n, jm, x, k), O.neg(F, O.lookup(~F, x, c)), dk(~F, n, jm, p, k), dd, gg, dp, O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g))), GJ.all_at(~(z => M.bnd(~F, dk(~F, n, jm, x, z), dd)), n, ri_d(~F, n, jm, x, i, c, gg, dd, ph, hx), k, hk), FM.bnd_neg(~F, O.lookup(~F, x, c), gg, look_bnd(~F, x, c, gg, ri_e(~F, n, jm, x, i, c, gg, dd, ph, hx), hgg)), GJ.all_at(~(z => M.bnd(~F, dk(~F, n, jm, p, z), dp)), n, ri_d(~F, n, jm, p, c, 1n+c, gp, dp, pp, hp), k, hk), odk(~F, n, jm, x2, x, O.lookup(~F, x, c), p, k, ep, g, he, hep, hj, hg, hn))

# an earlier column j < c
def orow_flt(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x2: M.Vec(~F), +x: M.Vec(~F), +i: Nat, +c: Nat, +p: M.Vec(~F), +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +gp: O.C(F), +dp: O.C(F), +pp: O.C(F), +ep: O.C(F), +g: O.C(F), +hx: rowinv(~F, n, jm, x, i, c, gg, dd, ph), +hp: rowinv(~F, n, jm, p, c, 1n+c, gp, dp, pp), +he: M.vbnd.all(~F, M.vadd(~F, x2, M.vneg(~F, M.vadd(~F, x, M.vscale(~F, O.neg(F, O.lookup(~F, x, c)), p)))), ep), +hgg: O.le(~F, O.zero(F), gg), +hgp: O.le(~F, O.zero(F), gp), +hph: O.le(~F, O.zero(F), ph), +hep: O.le(~F, O.zero(F), ep), +hj: mall(~F, jm, g), +hg: O.le(~F, O.zero(F), g), +hn: {GJ.nrows(~F, jm) == n : Nat}, +j: Nat, +hjc: {KA.natle(1n+j, c) == True{} : Bool}) -> M.bnd(~F, O.sub(~F, O.lookup(~F, x2, j), GJ.dl(~F, KA.nateq(i, j))), O.add(F, O.add(F, ph, O.mul(F, gg, pp)), ep)):
  three(~F, O.sub(~F, O.lookup(~F, x2, j), GJ.dl(~F, KA.nateq(i, j))), O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, KA.nateq(i, j))), O.neg(F, O.lookup(~F, x, c)), O.sub(~F, O.lookup(~F, p, j), O.zero(F)), ph, gg, pp, ep,
    GJ.all_at(~(z => M.bnd(~F, O.sub(~F, O.lookup(~F, x, z), GJ.dl(~F, KA.nateq(i, z))), ph)), c, ri_f(~F, n, jm, x, i, c, gg, dd, ph, hx), j, hjc),
    FM.bnd_neg(~F, O.lookup(~F, x, c), gg, look_bnd(~F, x, c, gg, ri_e(~F, n, jm, x, i, c, gg, dd, ph, hx), hgg)),
    (%ne_lt(j, c, hjc) : M.bnd(~F, O.sub(~F, O.lookup(~F, p, j), GJ.dl(~F, _)), pp)
      GJ.all_at(~(z => M.bnd(~F, O.sub(~F, O.lookup(~F, p, z), GJ.dl(~F, KA.nateq(c, z))), pp)), 1n+c, ri_f(~F, n, jm, p, c, 1n+c, gp, dp, pp, hp), j, GJ.le_succ(1n+j, c, hjc))),
    KB.bnd_val(~F, O.sub(~F, O.lookup(~F, x2, j), O.add(F, O.lookup(~F, x, j), O.mul(F, O.neg(F, O.lookup(~F, x, c)), O.lookup(~F, p, j)))), O.sub(~F, O.sub(~F, O.lookup(~F, x2, j), GJ.dl(~F, KA.nateq(i, j))), O.add(F, O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, KA.nateq(i, j))), O.mul(F, O.neg(F, O.lookup(~F, x, c)), O.sub(~F, O.lookup(~F, p, j), O.zero(F))))), ep, FR.fring_eq(~F, [O.lookup(~F, x2, j), O.lookup(~F, x, j), O.lookup(~F, x, c), O.lookup(~F, p, j), GJ.dl(~F, KA.nateq(i, j))], E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZMul{E.ZNeg{E.ZVar{2n}}, E.ZVar{3n}}}}, E.ZSub{E.ZSub{E.ZVar{0n}, E.ZVar{4n}}, E.ZAdd{E.ZSub{E.ZVar{1n}, E.ZVar{4n}}, E.ZMul{E.ZNeg{E.ZVar{2n}}, E.ZSub{E.ZVar{3n}, E.ZCst{S.Z0{}}}}}}, {==}), oent(~F, x2, x, O.lookup(~F, x, c), p, j, ep, he, hep)))

# column c itself (i is not c)
def orow_fc(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x2: M.Vec(~F), +x: M.Vec(~F), +i: Nat, +c: Nat, +p: M.Vec(~F), +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +gp: O.C(F), +dp: O.C(F), +pp: O.C(F), +ep: O.C(F), +g: O.C(F), +hx: rowinv(~F, n, jm, x, i, c, gg, dd, ph), +hp: rowinv(~F, n, jm, p, c, 1n+c, gp, dp, pp), +he: M.vbnd.all(~F, M.vadd(~F, x2, M.vneg(~F, M.vadd(~F, x, M.vscale(~F, O.neg(F, O.lookup(~F, x, c)), p)))), ep), +hgg: O.le(~F, O.zero(F), gg), +hgp: O.le(~F, O.zero(F), gp), +hph: O.le(~F, O.zero(F), ph), +hep: O.le(~F, O.zero(F), ep), +hj: mall(~F, jm, g), +hg: O.le(~F, O.zero(F), g), +hn: {GJ.nrows(~F, jm) == n : Nat}, +hic: {KA.nateq(i, c) == False{} : Bool}) -> M.bnd(~F, O.sub(~F, O.lookup(~F, x2, c), GJ.dl(~F, KA.nateq(i, c))), O.add(F, O.add(F, ph, O.mul(F, gg, pp)), ep)):
  %Equal.sym(Bool, KA.nateq(i, c), False{}, hic) : M.bnd(~F, O.sub(~F, O.lookup(~F, x2, c), GJ.dl(~F, _)), O.add(F, O.add(F, ph, O.mul(F, gg, pp)), ep))
  three(~F, O.sub(~F, O.lookup(~F, x2, c), O.zero(F)), O.zero(F), O.neg(F, O.lookup(~F, x, c)), O.sub(~F, O.lookup(~F, p, c), O.one(F)), ph, gg, pp, ep, FM.bnd_zero(~F, ph, hph), FM.bnd_neg(~F, O.lookup(~F, x, c), gg, look_bnd(~F, x, c, gg, ri_e(~F, n, jm, x, i, c, gg, dd, ph, hx), hgg)),
    (%SL.nateq_refl(c) : M.bnd(~F, O.sub(~F, O.lookup(~F, p, c), GJ.dl(~F, _)), pp)
      GJ.all_at(~(z => M.bnd(~F, O.sub(~F, O.lookup(~F, p, z), GJ.dl(~F, KA.nateq(c, z))), pp)), 1n+c, ri_f(~F, n, jm, p, c, 1n+c, gp, dp, pp, hp), c, GJ.le_refl(c))),
    KB.bnd_val(~F, O.sub(~F, O.lookup(~F, x2, c), O.add(F, O.lookup(~F, x, c), O.mul(F, O.neg(F, O.lookup(~F, x, c)), O.lookup(~F, p, c)))), O.sub(~F, O.sub(~F, O.lookup(~F, x2, c), O.zero(F)), O.add(F, O.zero(F), O.mul(F, O.neg(F, O.lookup(~F, x, c)), O.sub(~F, O.lookup(~F, p, c), O.one(F))))), ep, FR.fring_eq(~F, [O.lookup(~F, x2, c), O.lookup(~F, x, c), O.lookup(~F, p, c)], E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZMul{E.ZNeg{E.ZVar{1n}}, E.ZVar{2n}}}}, E.ZSub{E.ZSub{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZAdd{E.ZCst{S.Z0{}}, E.ZMul{E.ZNeg{E.ZVar{1n}}, E.ZSub{E.ZVar{2n}, E.ZCst{S.Zpos{S.XH{}}}}}}}, {==}), oent(~F, x2, x, O.lookup(~F, x, c), p, c, ep, he, hep)))

# another row x' = x - x_c p rounded keeps the invariant after column c
def orow(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x2: M.Vec(~F), +x: M.Vec(~F), +i: Nat, +c: Nat, +p: M.Vec(~F), +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +gp: O.C(F), +dp: O.C(F), +pp: O.C(F), +ep: O.C(F), +g: O.C(F), +hx: rowinv(~F, n, jm, x, i, c, gg, dd, ph), +hp: rowinv(~F, n, jm, p, c, 1n+c, gp, dp, pp), +he: M.vbnd.all(~F, M.vadd(~F, x2, M.vneg(~F, M.vadd(~F, x, M.vscale(~F, O.neg(F, O.lookup(~F, x, c)), p)))), ep), +hgg: O.le(~F, O.zero(F), gg), +hgp: O.le(~F, O.zero(F), gp), +hph: O.le(~F, O.zero(F), ph), +hep: O.le(~F, O.zero(F), ep), +hj: mall(~F, jm, g), +hg: O.le(~F, O.zero(F), g), +hn: {GJ.nrows(~F, jm) == n : Nat}, +lx2: {M.len(~F, x2) == Nat.add(n, n) : Nat}, +hic: {KA.nateq(i, c) == False{} : Bool}) -> rowinv(~F, n, jm, x2, i, 1n+c, O.add(F, O.add(F, gg, O.mul(F, gg, gp)), ep), O.add(F, O.add(F, dd, O.mul(F, gg, dp)), O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))), O.add(F, O.add(F, ph, O.mul(F, gg, pp)), ep)):
  ri_mk(~F, n, jm, x2, i, 1n+c, O.add(F, O.add(F, gg, O.mul(F, gg, gp)), ep), O.add(F, O.add(F, dd, O.mul(F, gg, dp)), O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))), O.add(F, O.add(F, ph, O.mul(F, gg, pp)), ep), lx2,
    vall_by(~F, ~x2, ~O.add(F, O.add(F, gg, O.mul(F, gg, gp)), ep), ~(k => orow_e(~F, n, jm, x2, x, i, c, p, gg, dd, ph, gp, dp, pp, ep, g, hx, hp, he, hgg, hgp, hph, hep, hj, hg, hn, k))),
    GJ.all_mk(~n, ~(k => M.bnd(~F, dk(~F, n, jm, x2, k), O.add(F, O.add(F, dd, O.mul(F, gg, dp)), O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))))), ~(k => hk => orow_d(~F, n, jm, x2, x, i, c, p, gg, dd, ph, gp, dp, pp, ep, g, hx, hp, he, hgg, hgp, hph, hep, hj, hg, hn, k, hk)), n, GJ.le_refl(n)),
    (GJ.all_mk(~c, ~(z => M.bnd(~F, O.sub(~F, O.lookup(~F, x2, z), GJ.dl(~F, KA.nateq(i, z))), O.add(F, O.add(F, ph, O.mul(F, gg, pp)), ep))), ~(z => hz => orow_flt(~F, n, jm, x2, x, i, c, p, gg, dd, ph, gp, dp, pp, ep, g, hx, hp, he, hgg, hgp, hph, hep, hj, hg, hn, z, hz)), c, GJ.le_refl(c)),
     orow_fc(~F, n, jm, x2, x, i, c, p, gg, dd, ph, gp, dp, pp, ep, g, hx, hp, he, hgg, hgp, hph, hep, hj, hg, hn, hic)))

# All the rows
# ------------

def all_map(~Q1: Nat -> Data, ~Q2: Nat -> Data, ~f: @i: Nat -> Q1(i) -> Q2(i), k: Nat, h: GJ.All(~Q1, k)) -> GJ.All(~Q2, k):
  match k:
    case 0n:
      Unit{}
    case 1n++j:
      match h:
        case (h1, q):
          (all_map(~Q1, ~Q2, ~f, j, h1), f(j, q))

# larger constants
def ri_mono(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +i: Nat, +c: Nat, +g1: O.C(F), +d1: O.C(F), +p1: O.C(F), +g2: O.C(F), +d2: O.C(F), +p2: O.C(F), +h: rowinv(~F, n, jm, x, i, c, g1, d1, p1), +eg: O.le(~F, g1, g2), +ed: O.le(~F, d1, d2), +ep: O.le(~F, p1, p2)) -> rowinv(~F, n, jm, x, i, c, g2, d2, p2):
  ri_mk(~F, n, jm, x, i, c, g2, d2, p2, ri_len(~F, n, jm, x, i, c, g1, d1, p1, h), FM.vall_mono(~F, x, g1, g2, ri_e(~F, n, jm, x, i, c, g1, d1, p1, h), FM.sub_nonneg(~F, g1, g2, eg)),
    all_map(~(k => M.bnd(~F, dk(~F, n, jm, x, k), d1)), ~(k => M.bnd(~F, dk(~F, n, jm, x, k), d2)), ~(k => hb => FM.bnd_mono(~F, dk(~F, n, jm, x, k), d1, d2, hb, FM.sub_nonneg(~F, d1, d2, ed))), n, ri_d(~F, n, jm, x, i, c, g1, d1, p1, h)),
    all_map(~(j => M.bnd(~F, O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, KA.nateq(i, j))), p1)), ~(j => M.bnd(~F, O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, KA.nateq(i, j))), p2)), ~(j => hb => FM.bnd_mono(~F, O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, KA.nateq(i, j))), p1, p2, hb, FM.sub_nonneg(~F, p1, p2, ep))), c, ri_f(~F, n, jm, x, i, c, g1, d1, p1, h)))

# every row, rows numbered from i
def rinv(~F: O.OField, +n: Nat, +jm: M.Mat(~F), s: M.Mat(~F), +i: Nat, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F)) -> Data:
  match s:
    case Nil{}:
      Unit
    case Con{x, t}:
      M.Both(rowinv(~F, n, jm, x, i, c, gg, dd, ph), rinv(~F, n, jm, t, 1n+i, c, gg, dd, ph))

# the constants after one column: pivot row's plus the other rows'
def gnew(~F: O.OField, +gg: O.C(F), +gp: O.C(F), +ep: O.C(F)) -> O.C(F):
  O.add(F, gp, O.add(F, O.add(F, gg, O.mul(F, gg, gp)), ep))

def dnew(~F: O.OField, +n: Nat, +g: O.C(F), +gg: O.C(F), +dd: O.C(F), +dp: O.C(F), +ep: O.C(F)) -> O.C(F):
  O.add(F, dp, O.add(F, O.add(F, dd, O.mul(F, gg, dp)), O.mul(F, ep, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))))

def pnew(~F: O.OField, +gg: O.C(F), +ph: O.C(F), +pp: O.C(F), +ep: O.C(F)) -> O.C(F):
  O.add(F, pp, O.add(F, O.add(F, ph, O.mul(F, gg, pp)), ep))

def le_addr(~F: O.OField, +a: O.C(F), +b: O.C(F), hb: O.le(~F, O.zero(F), b)) -> O.le(~F, a, O.add(F, a, b)):
  FV.le_of_sub(~F, a, O.add(F, a, b), FM.nn_eq(~F, O.sub(~F, O.add(F, a, b), a), b, FR.fring_eq(~F, [a, b], E.ZVar{1n}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{0n}}, {==}), hb))

def le_addl(~F: O.OField, +a: O.C(F), +b: O.C(F), ha: O.le(~F, O.zero(F), a)) -> O.le(~F, b, O.add(F, a, b)):
  FV.le_of_sub(~F, b, O.add(F, a, b), FM.nn_eq(~F, O.sub(~F, O.add(F, a, b), b), a, FR.fring_eq(~F, [a, b], E.ZVar{0n}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{1n}}, {==}), ha))

def len_dscale(~F: O.OField, +w: Nat, +s: S.D, xs: List<&2, S.D>) -> {M.len(~F, M.ofdv(~F, NU.dscale(w, s, xs))) == M.len(~F, M.ofdv(~F, xs)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      Equal.cong(Nat, Nat, z => 1n+z, M.len(~F, M.ofdv(~F, NU.dscale(w, s, t))), M.len(~F, M.ofdv(~F, t)), len_dscale(~F, w, s, t))

def len_daxpy(~F: O.OField, +w: Nat, xs: List<&2, S.D>, +c: S.D, ys: List<&2, S.D>, hl: {M.len(~F, M.ofdv(~F, xs)) == M.len(~F, M.ofdv(~F, ys)) : Nat}) -> {M.len(~F, M.ofdv(~F, NU.daxpy(w, xs, c, ys))) == M.len(~F, M.ofdv(~F, xs)) : Nat}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+y, +yt}:
      {==}
    case Con{+x, +xt} Nil{}:
      {==}
    case Con{+x, +xt} Con{+y, +yt}:
      Equal.cong(Nat, Nat, z => 1n+z, M.len(~F, M.ofdv(~F, NU.daxpy(w, xt, c, yt))), M.len(~F, M.ofdv(~F, xt)), len_daxpy(~F, w, xt, c, yt, FV.succ_inj(M.len(~F, M.ofdv(~F, xt)), M.len(~F, M.ofdv(~F, yt)), hl)))

# one row of the cleared matrix
def row_ok(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +w: Nat, +p: List<&2, S.D>, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +gp: O.C(F), +dp: O.C(F), +pp: O.C(F), +g: O.C(F), +hp: rowinv(~F, n, jm, M.ofdv(~F, p), c, 1n+c, gp, dp, pp), +hgg: O.le(~F, O.zero(F), gg), +hdd: O.le(~F, O.zero(F), dd), +hph: O.le(~F, O.zero(F), ph), +hgp: O.le(~F, O.zero(F), gp), +hdp: O.le(~F, O.zero(F), dp), +hpp: O.le(~F, O.zero(F), pp), +hj: mall(~F, jm, g), +hg: O.le(~F, O.zero(F), g), +hn: {GJ.nrows(~F, jm) == n : Nat}, +hu: O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F)), b: Bool, +i: Nat, +e: {KA.nateq(i, c) == b : Bool}, +r: List<&2, S.D>, +hx: rowinv(~F, n, jm, M.ofdv(~F, r), i, c, gg, dd, ph)) -> rowinv(~F, n, jm, M.ofdv(~F, NU.dclear.go(b, w, r, p, c)), i, 1n+c, gnew(~F, gg, gp, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), dnew(~F, n, g, gg, dd, dp, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), pnew(~F, gg, ph, pp, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))):
  match b:
    case True{}:
      %Equal.sym(Nat, i, c, GJ.nateq_ok(i, c, e)) : rowinv(~F, n, jm, M.ofdv(~F, p), _, 1n+c, gnew(~F, gg, gp, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), dnew(~F, n, g, gg, dd, dp, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), pnew(~F, gg, ph, pp, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))
      ri_mono(~F, n, jm, M.ofdv(~F, p), c, 1n+c, gp, dp, pp, gnew(~F, gg, gp, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), dnew(~F, n, g, gg, dd, dp, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), pnew(~F, gg, ph, pp, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), hp, le_addr(~F, gp, O.add(F, O.add(F, gg, O.mul(F, gg, gp)), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), FO.nonneg_add(~F, O.add(F, gg, O.mul(F, gg, gp)), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FO.nonneg_add(~F, gg, O.mul(F, gg, gp), hgg, FO.mul_nonneg(~F, gg, gp, hgg, hgp)), FO.mul_nonneg(~F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), FO.nonneg_add(~F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp)), hgg, FO.nonneg_add(~F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp), FO.nonneg_add(~F, O.mul(F, gg, gp), O.mul(F, gg, gp), FO.mul_nonneg(~F, gg, gp, hgg, hgp), FO.mul_nonneg(~F, gg, gp, hgg, hgp)), FO.mul_nonneg(~F, gg, gp, hgg, hgp))), u_nn(~F, w)))), le_addr(~F, dp, O.add(F, O.add(F, dd, O.mul(F, gg, dp)), O.mul(F, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))), FO.nonneg_add(~F, O.add(F, dd, O.mul(F, gg, dp)), O.mul(F, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g))), FO.nonneg_add(~F, dd, O.mul(F, gg, dp), hdd, FO.mul_nonneg(~F, gg, dp, hgg, hdp)), FO.mul_nonneg(~F, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)), FO.mul_nonneg(~F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), FO.nonneg_add(~F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp)), hgg, FO.nonneg_add(~F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp), FO.nonneg_add(~F, O.mul(F, gg, gp), O.mul(F, gg, gp), FO.mul_nonneg(~F, gg, gp, hgg, hgp), FO.mul_nonneg(~F, gg, gp, hgg, hgp)), FO.mul_nonneg(~F, gg, gp, hgg, hgp))), u_nn(~F, w)), FO.nonneg_add(~F, O.one(F), O.mul(F, FR.ofn(~F, n), g), NP.one_nn(~F), FO.mul_nonneg(~F, FR.ofn(~F, n), g, ofn_nn(~F, n), hg))))), le_addr(~F, pp, O.add(F, O.add(F, ph, O.mul(F, gg, pp)), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), FO.nonneg_add(~F, O.add(F, ph, O.mul(F, gg, pp)), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FO.nonneg_add(~F, ph, O.mul(F, gg, pp), hph, FO.mul_nonneg(~F, gg, pp, hgg, hpp)), FO.mul_nonneg(~F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), FO.nonneg_add(~F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp)), hgg, FO.nonneg_add(~F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp), FO.nonneg_add(~F, O.mul(F, gg, gp), O.mul(F, gg, gp), FO.mul_nonneg(~F, gg, gp, hgg, hgp), FO.mul_nonneg(~F, gg, gp, hgg, hgp)), FO.mul_nonneg(~F, gg, gp, hgg, hgp))), u_nn(~F, w)))))
    case False{}:
      ri_mono(~F, n, jm, M.ofdv(~F, NU.daxpy(w, r, NU.dget(r, c), p)), i, 1n+c, O.add(F, O.add(F, gg, O.mul(F, gg, gp)), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.add(F, O.add(F, dd, O.mul(F, gg, dp)), O.mul(F, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))), O.add(F, O.add(F, ph, O.mul(F, gg, pp)), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), gnew(~F, gg, gp, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), dnew(~F, n, g, gg, dd, dp, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), pnew(~F, gg, ph, pp, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))),
        orow(~F, n, jm, M.ofdv(~F, NU.daxpy(w, r, NU.dget(r, c), p)), M.ofdv(~F, r), i, c, M.ofdv(~F, p), gg, dd, ph, gp, dp, pp, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), g, hx, hp,
          (%dget_ofd(~F, r, c) : M.vbnd.all(~F, M.vadd(~F, M.ofdv(~F, NU.daxpy(w, r, NU.dget(r, c), p)), M.vneg(~F, M.vadd(~F, M.ofdv(~F, r), M.vscale(~F, O.neg(F, _), M.ofdv(~F, p))))), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))
            daxpy_err(~F, w, r, NU.dget(r, c), p, gg, gg, gp, ri_e(~F, n, jm, M.ofdv(~F, r), i, c, gg, dd, ph, hx), (%Equal.sym(O.C(F), M.ofd(~F, NU.dget(r, c)), O.lookup(~F, M.ofdv(~F, r), c), dget_ofd(~F, r, c)) : M.bnd(~F, _, gg)
              look_bnd(~F, M.ofdv(~F, r), c, gg, ri_e(~F, n, jm, M.ofdv(~F, r), i, c, gg, dd, ph, hx), hgg)), ri_e(~F, n, jm, M.ofdv(~F, p), c, 1n+c, gp, dp, pp, hp), Equal.trans(Nat, M.len(~F, M.ofdv(~F, r)), Nat.add(n, n), M.len(~F, M.ofdv(~F, p)), ri_len(~F, n, jm, M.ofdv(~F, r), i, c, gg, dd, ph, hx), Equal.sym(Nat, M.len(~F, M.ofdv(~F, p)), Nat.add(n, n), ri_len(~F, n, jm, M.ofdv(~F, p), c, 1n+c, gp, dp, pp, hp))), hu)),
          hgg, hgp, hph, FO.mul_nonneg(~F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), FO.nonneg_add(~F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp)), hgg, FO.nonneg_add(~F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp), FO.nonneg_add(~F, O.mul(F, gg, gp), O.mul(F, gg, gp), FO.mul_nonneg(~F, gg, gp, hgg, hgp), FO.mul_nonneg(~F, gg, gp, hgg, hgp)), FO.mul_nonneg(~F, gg, gp, hgg, hgp))), u_nn(~F, w)), hj, hg, hn, Equal.trans(Nat, M.len(~F, M.ofdv(~F, NU.daxpy(w, r, NU.dget(r, c), p))), M.len(~F, M.ofdv(~F, r)), Nat.add(n, n), len_daxpy(~F, w, r, NU.dget(r, c), p, Equal.trans(Nat, M.len(~F, M.ofdv(~F, r)), Nat.add(n, n), M.len(~F, M.ofdv(~F, p)), ri_len(~F, n, jm, M.ofdv(~F, r), i, c, gg, dd, ph, hx), Equal.sym(Nat, M.len(~F, M.ofdv(~F, p)), Nat.add(n, n), ri_len(~F, n, jm, M.ofdv(~F, p), c, 1n+c, gp, dp, pp, hp)))), ri_len(~F, n, jm, M.ofdv(~F, r), i, c, gg, dd, ph, hx)), e),
        le_addl(~F, gp, O.add(F, O.add(F, gg, O.mul(F, gg, gp)), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), hgp), le_addl(~F, dp, O.add(F, O.add(F, dd, O.mul(F, gg, dp)), O.mul(F, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))), hdp), le_addl(~F, pp, O.add(F, O.add(F, ph, O.mul(F, gg, pp)), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), hpp))

# every row of the cleared matrix, rows numbered from i
def clear_ok(~F: O.OField, rows: List<&2, List<&2, S.D>>, +n: Nat, +jm: M.Mat(~F), +w: Nat, +p: List<&2, S.D>, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +gp: O.C(F), +dp: O.C(F), +pp: O.C(F), +g: O.C(F), +hp: rowinv(~F, n, jm, M.ofdv(~F, p), c, 1n+c, gp, dp, pp), +hgg: O.le(~F, O.zero(F), gg), +hdd: O.le(~F, O.zero(F), dd), +hph: O.le(~F, O.zero(F), ph), +hgp: O.le(~F, O.zero(F), gp), +hdp: O.le(~F, O.zero(F), dp), +hpp: O.le(~F, O.zero(F), pp), +hj: mall(~F, jm, g), +hg: O.le(~F, O.zero(F), g), +hn: {GJ.nrows(~F, jm) == n : Nat}, +hu: O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F)), +i: Nat, h: rinv(~F, n, jm, M.ofdm(~F, rows), i, c, gg, dd, ph)) -> rinv(~F, n, jm, M.ofdm(~F, NU.dclear(rows, w, p, c, i)), i, 1n+c, gnew(~F, gg, gp, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), dnew(~F, n, g, gg, dd, dp, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), pnew(~F, gg, ph, pp, O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))):
  match rows:
    case Nil{}:
      Unit{}
    case Con{+r, +t}:
      (h1, h2) = h
      (row_ok(~F, n, jm, w, p, c, gg, dd, ph, gp, dp, pp, g, hp, hgg, hdd, hph, hgp, hdp, hpp, hj, hg, hn, hu, KA.nateq(i, c), i, {==}, r, h1), clear_ok(~F, t, n, jm, w, p, c, gg, dd, ph, gp, dp, pp, g, hp, hgg, hdd, hph, hgp, hdp, hpp, hj, hg, hn, hu, 1n+i, h2))

# The swap
# --------

def all_map_lt(~n: Nat, ~Q1: Nat -> Data, ~Q2: Nat -> Data, ~f: @i: Nat -> {KA.natle(1n+i, n) == True{} : Bool} -> Q1(i) -> Q2(i), k: Nat, +hk: {KA.natle(k, n) == True{} : Bool}, h: GJ.All(~Q1, k)) -> GJ.All(~Q2, k):
  match k:
    case 0n:
      Unit{}
    case 1n++j:
      match h:
        case (h1, q):
          (all_map_lt(~n, ~Q1, ~Q2, ~f, j, GJ.le_trans(j, 1n+j, n, GJ.le_succ(j, j, GJ.le_refl(j)), hk), h1), f(j, hk, q))

def fin_move.ent(~F: O.OField, +x: M.Vec(~F), +a: Nat, +b: Nat, +c: Nat, +ph: O.C(F), +ha: {KA.natle(c, a) == True{} : Bool}, +hb: {KA.natle(c, b) == True{} : Bool}, +j: Nat, +hj: {KA.natle(1n+j, c) == True{} : Bool}, q: M.bnd(~F, O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, KA.nateq(a, j))), ph)) -> M.bnd(~F, O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, KA.nateq(b, j))), ph):
  %Equal.sym(Bool, KA.nateq(b, j), False{}, ne_lt(j, b, GJ.le_trans(1n+j, c, b, hj, hb))) : M.bnd(~F, O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, _)), ph)
  (%ne_lt(j, a, GJ.le_trans(1n+j, c, a, hj, ha)) : M.bnd(~F, O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, _)), ph)
    q)

# a row's index can move among indices >= c
def ri_move(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +a: Nat, +b: Nat, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +h: rowinv(~F, n, jm, x, a, c, gg, dd, ph), +ha: {KA.natle(c, a) == True{} : Bool}, +hb: {KA.natle(c, b) == True{} : Bool}) -> rowinv(~F, n, jm, x, b, c, gg, dd, ph):
  ri_mk(~F, n, jm, x, b, c, gg, dd, ph, ri_len(~F, n, jm, x, a, c, gg, dd, ph, h), ri_e(~F, n, jm, x, a, c, gg, dd, ph, h), ri_d(~F, n, jm, x, a, c, gg, dd, ph, h),
    all_map_lt(~c, ~(j => M.bnd(~F, O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, KA.nateq(a, j))), ph)), ~(j => M.bnd(~F, O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, KA.nateq(b, j))), ph)), ~(j => hj => q => fin_move.ent(~F, x, a, b, c, ph, ha, hb, j, hj, q)), c, GJ.le_refl(c), ri_f(~F, n, jm, x, a, c, gg, dd, ph, h)))

# row k of the rows numbered from i0
def ri_at(~F: O.OField, +n: Nat, +jm: M.Mat(~F), s: M.Mat(~F), +i0: Nat, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), k: Nat, h: rinv(~F, n, jm, s, i0, c, gg, dd, ph), hk: {KA.natle(1n+k, GJ.nrows(~F, s)) == True{} : Bool}) -> rowinv(~F, n, jm, DV.mrow(~F, s, k), Nat.add(k, i0), c, gg, dd, ph):
  match s k:
    case Nil{} 0n:
      FO.absurd(rowinv(~F, n, jm, Nil{}, i0, c, gg, dd, ph), KA.ft(hk))
    case Nil{} 1n++j:
      FO.absurd(rowinv(~F, n, jm, Nil{}, 1n+Nat.add(j, i0), c, gg, dd, ph), KA.ft(hk))
    case Con{x, t} 0n:
      (h1, h2) = h
      h1
    case Con{x, t} 1n++j:
      (h1, h2) = h
      %Equal.sym(Nat, 1n+Nat.add(j, i0), Nat.add(j, 1n+i0), LN.add_succ(j, i0)) : rowinv(~F, n, jm, DV.mrow(~F, t, j), _, c, gg, dd, ph)
      ri_at(~F, n, jm, t, 1n+i0, c, gg, dd, ph, j, h2, hk)

# replacing row k by a row good at its index
def rinv_set(~F: O.OField, +n: Nat, +jm: M.Mat(~F), s: M.Mat(~F), +i0: Nat, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), k: Nat, +x: M.Vec(~F), h: rinv(~F, n, jm, s, i0, c, gg, dd, ph), hx: rowinv(~F, n, jm, x, Nat.add(k, i0), c, gg, dd, ph)) -> rinv(~F, n, jm, GJ.mset(~F, s, k, x), i0, c, gg, dd, ph):
  match s k:
    case Nil{} 0n:
      Unit{}
    case Nil{} 1n++j:
      Unit{}
    case Con{y, t} 0n:
      (h1, h2) = h
      (hx, h2)
    case Con{y, t} 1n++j:
      (h1, h2) = h
      (h1, rinv_set(~F, n, jm, t, 1n+i0, c, gg, dd, ph, j, x, h2, (%LN.add_succ(j, i0) : rowinv(~F, n, jm, x, _, c, gg, dd, ph)
        hx)))

# swapping rows c and r (both at least c) keeps the invariant
def swap_ok(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +rows: List<&2, List<&2, S.D>>, +c: Nat, +r: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +h: rinv(~F, n, jm, M.ofdm(~F, rows), 0n, c, gg, dd, ph), +hn: {GJ.nrows(~F, M.ofdm(~F, rows)) == n : Nat}, +hc: {KA.natle(1n+c, n) == True{} : Bool}, +hr1: {KA.natle(c, r) == True{} : Bool}, +hr2: {KA.natle(1n+r, n) == True{} : Bool}) -> rinv(~F, n, jm, M.ofdm(~F, NU.dswap(rows, c, r)), 0n, c, gg, dd, ph):
  %Equal.sym(M.Mat(~F), M.ofdm(~F, NU.dswap(rows, c, r)), GJ.mswap(~F, M.ofdm(~F, rows), c, r), dswap_ofd(~F, rows, c, r)) : rinv(~F, n, jm, _, 0n, c, gg, dd, ph)
  rinv_set(~F, n, jm, GJ.mset(~F, M.ofdm(~F, rows), c, DV.mrow(~F, M.ofdm(~F, rows), r)), 0n, c, gg, dd, ph, r, DV.mrow(~F, M.ofdm(~F, rows), c),
    rinv_set(~F, n, jm, M.ofdm(~F, rows), 0n, c, gg, dd, ph, c, DV.mrow(~F, M.ofdm(~F, rows), r), h,
      (%LN.add_zero(c) : rowinv(~F, n, jm, DV.mrow(~F, M.ofdm(~F, rows), r), _, c, gg, dd, ph)
        ri_move(~F, n, jm, DV.mrow(~F, M.ofdm(~F, rows), r), r, c, c, gg, dd, ph, (%Equal.sym(Nat, r, Nat.add(r, 0n), LN.add_zero(r)) : rowinv(~F, n, jm, DV.mrow(~F, M.ofdm(~F, rows), r), _, c, gg, dd, ph)
        ri_at(~F, n, jm, M.ofdm(~F, rows), 0n, c, gg, dd, ph, r, h, (%Equal.sym(Nat, GJ.nrows(~F, M.ofdm(~F, rows)), n, hn) : {KA.natle(1n+r, _) == True{} : Bool}
          hr2))), hr1, GJ.le_refl(c)))),
    (%LN.add_zero(r) : rowinv(~F, n, jm, DV.mrow(~F, M.ofdm(~F, rows), c), _, c, gg, dd, ph)
      ri_move(~F, n, jm, DV.mrow(~F, M.ofdm(~F, rows), c), c, r, c, gg, dd, ph, (%Equal.sym(Nat, c, Nat.add(c, 0n), LN.add_zero(c)) : rowinv(~F, n, jm, DV.mrow(~F, M.ofdm(~F, rows), c), _, c, gg, dd, ph)
        ri_at(~F, n, jm, M.ofdm(~F, rows), 0n, c, gg, dd, ph, c, h, (%Equal.sym(Nat, GJ.nrows(~F, M.ofdm(~F, rows)), n, hn) : {KA.natle(1n+c, _) == True{} : Bool}
          hc))), GJ.le_refl(c), hr1)))

# One column
# ----------

# s is near q = 1/pivot: |s| <= |q| (1 + u)
def s_bnd(~F: O.OField, +w: Nat, +x: S.D) -> M.bnd(~F, M.ofd(~F, NU.dsdiv(w, NU.done(), x)), O.add(F, FV.fabs(~F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(x)))), O.mul(F, FV.fabs(~F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(x)))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))):
  KB.bnd_val(~F, O.add(F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(x))), O.sub(~F, M.ofd(~F, NU.dsdiv(w, NU.done(), x)), O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(x))))), M.ofd(~F, NU.dsdiv(w, NU.done(), x)), O.add(F, FV.fabs(~F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(x)))), O.mul(F, FV.fabs(~F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(x)))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), FR.fring_eq(~F, [O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(x))), M.ofd(~F, NU.dsdiv(w, NU.done(), x))], E.ZAdd{E.ZVar{0n}, E.ZSub{E.ZVar{1n}, E.ZVar{0n}}}, E.ZVar{1n}, {==}),
    FM.bnd_add(~F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(x))), FV.fabs(~F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(x)))), O.sub(~F, M.ofd(~F, NU.dsdiv(w, NU.done(), x)), O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(x)))), O.mul(F, FV.fabs(~F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(x)))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FV.fabs_bnd(~F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(x)))), s_err(~F, w, x)))

# the pivot row's invariant, read at index c
def col_hx(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +rows: List<&2, List<&2, S.D>>, +c: Nat, +r: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +hs: rinv(~F, n, jm, M.ofdm(~F, NU.dswap(rows, c, r)), 0n, c, gg, dd, ph), +hnt: {GJ.nrows(~F, M.ofdm(~F, NU.dswap(rows, c, r))) == n : Nat}, +hc: {KA.natle(1n+c, n) == True{} : Bool}) -> rowinv(~F, n, jm, M.ofdv(~F, NU.drow(NU.dswap(rows, c, r), c)), c, c, gg, dd, ph):
  (%Equal.sym(M.Vec(~F), M.ofdv(~F, NU.drow(NU.dswap(rows, c, r), c)), DV.mrow(~F, M.ofdm(~F, NU.dswap(rows, c, r)), c), drow_ofd(~F, NU.dswap(rows, c, r), c)) : rowinv(~F, n, jm, _, c, c, gg, dd, ph)
      (%Equal.sym(Nat, c, Nat.add(c, 0n), LN.add_zero(c)) : rowinv(~F, n, jm, DV.mrow(~F, M.ofdm(~F, NU.dswap(rows, c, r)), c), _, c, gg, dd, ph)
        ri_at(~F, n, jm, M.ofdm(~F, NU.dswap(rows, c, r)), 0n, c, gg, dd, ph, c, hs, (%Equal.sym(Nat, GJ.nrows(~F, M.ofdm(~F, NU.dswap(rows, c, r))), n, hnt) : {KA.natle(1n+c, _) == True{} : Bool}
          hc))))

# one column of the elimination, pivot row r: swap, scale, clear
def col_step(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +w: Nat, +rows: List<&2, List<&2, S.D>>, +c: Nat, +r: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +g: O.C(F), +sg: O.C(F), +h: rinv(~F, n, jm, M.ofdm(~F, rows), 0n, c, gg, dd, ph), +hn: {GJ.nrows(~F, M.ofdm(~F, rows)) == n : Nat}, +hnt: {GJ.nrows(~F, M.ofdm(~F, NU.dswap(rows, c, r))) == n : Nat}, +hc: {KA.natle(1n+c, n) == True{} : Bool}, +hr1: {KA.natle(c, r) == True{} : Bool}, +hr2: {KA.natle(1n+r, n) == True{} : Bool}, hz: {M.ofd(~F, NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)) == O.zero(F) : O.C(F)} -> Empty, +hsg: M.bnd(~F, M.ofd(~F, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c))), sg), +hgg: O.le(~F, O.zero(F), gg), +hdd: O.le(~F, O.zero(F), dd), +hph: O.le(~F, O.zero(F), ph), +hj: mall(~F, jm, g), +hg: O.le(~F, O.zero(F), g), +hnj: {GJ.nrows(~F, jm) == n : Nat}, +hu: O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F))) -> rinv(~F, n, jm, M.ofdm(~F, NU.delim(w, NU.dswap(rows, c, r), c)), 0n, 1n+c, gnew(~F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), dnew(~F, n, g, gg, dd, O.add(F, O.mul(F, sg, dd), O.mul(F, O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), pnew(~F, gg, ph, O.add(F, O.add(F, O.mul(F, sg, ph), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))):
  +hs = swap_ok(~F, n, jm, rows, c, r, gg, dd, ph, h, hn, hc, hr1, hr2)
  +hx = col_hx(~F, n, jm, rows, c, r, gg, dd, ph, hs, hnt, hc)
  clear_ok(~F, NU.dswap(rows, c, r), n, jm, w, NU.dscale(w, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), NU.drow(NU.dswap(rows, c, r), c)), c, gg, dd, ph, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.add(F, O.mul(F, sg, dd), O.mul(F, O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))), O.add(F, O.add(F, O.mul(F, sg, ph), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), g,
    prow(~F, n, jm, M.ofdv(~F, NU.drow(NU.dswap(rows, c, r), c)), c, gg, dd, ph, hx, hgg, hph, M.ofd(~F, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c))), sg, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), hsg, (%dget_ofd(~F, NU.drow(NU.dswap(rows, c, r), c), c) : {O.mul(F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)))), _) == O.one(F) : O.C(F)}
      div_rel(~F, NU.dget(NU.drow(NU.dswap(rows, c, r), c), c), hz)), s_err(~F, w, NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), u_nn(~F, w), M.ofdv(~F, NU.dscale(w, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), NU.drow(NU.dswap(rows, c, r), c))), Equal.trans(Nat, M.len(~F, M.ofdv(~F, NU.dscale(w, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), NU.drow(NU.dswap(rows, c, r), c)))), M.len(~F, M.ofdv(~F, NU.drow(NU.dswap(rows, c, r), c))), Nat.add(n, n), len_dscale(~F, w, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), NU.drow(NU.dswap(rows, c, r), c)), ri_len(~F, n, jm, M.ofdv(~F, NU.drow(NU.dswap(rows, c, r), c)), c, c, gg, dd, ph, hx)), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), dscale_err(~F, w, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), NU.drow(NU.dswap(rows, c, r), c), sg, gg, hsg, ri_e(~F, n, jm, M.ofdv(~F, NU.drow(NU.dswap(rows, c, r), c)), c, c, gg, dd, ph, hx)), FO.mul_nonneg(~F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), FO.mul_nonneg(~F, sg, gg, FM.bnd_nonneg(~F, M.ofd(~F, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c))), sg, hsg), hgg), u_nn(~F, w)), g, hj, hg, hnj),
    hgg, hdd, hph, FO.nonneg_add(~F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FO.mul_nonneg(~F, sg, gg, FM.bnd_nonneg(~F, M.ofd(~F, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c))), sg, hsg), hgg), FO.mul_nonneg(~F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), FO.mul_nonneg(~F, sg, gg, FM.bnd_nonneg(~F, M.ofd(~F, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c))), sg, hsg), hgg), u_nn(~F, w))), FO.nonneg_add(~F, O.mul(F, sg, dd), O.mul(F, O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g))), FO.mul_nonneg(~F, sg, dd, FM.bnd_nonneg(~F, M.ofd(~F, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c))), sg, hsg), hdd), FO.mul_nonneg(~F, O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)), FO.mul_nonneg(~F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), FO.mul_nonneg(~F, sg, gg, FM.bnd_nonneg(~F, M.ofd(~F, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c))), sg, hsg), hgg), u_nn(~F, w)), FO.nonneg_add(~F, O.one(F), O.mul(F, FR.ofn(~F, n), g), NP.one_nn(~F), FO.mul_nonneg(~F, FR.ofn(~F, n), g, ofn_nn(~F, n), hg)))), FO.nonneg_add(~F, O.add(F, O.mul(F, sg, ph), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FO.nonneg_add(~F, O.mul(F, sg, ph), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), FO.mul_nonneg(~F, sg, ph, FM.bnd_nonneg(~F, M.ofd(~F, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c))), sg, hsg), hph), u_nn(~F, w)), FO.mul_nonneg(~F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), FO.mul_nonneg(~F, sg, gg, FM.bnd_nonneg(~F, M.ofd(~F, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c))), sg, hsg), hgg), u_nn(~F, w))), hj, hg, hnj, hu, 0n, hs)

# Right halves
# ------------
# The right parts R of the rows keep an inverse of bounded norm. Read
# against a vector u, a row x gives zr(x) = R_x . u; one column step
# changes these numbers by the step's row operations and a rounding term,
# and inverting that by hand bounds |R u| by |R' u| and |u|.

def zr(~F: O.OField, +n: Nat, +x: M.Vec(~F), +u: M.Vec(~F)) -> O.C(F):
  M.dot(~F, GJ.vdrop(~F, n, x), u)

# zr of x - y
def zr_sub(~F: O.OField, +n: Nat, +x: M.Vec(~F), +y: M.Vec(~F), +u: M.Vec(~F)) -> {zr(~F, n, M.vadd(~F, x, M.vneg(~F, y)), u) == O.sub(~F, zr(~F, n, x, u), zr(~F, n, y, u)) : O.C(F)}:
  %drop_vadd(~F, n, x, M.vneg(~F, y)) : {M.dot(~F, _, u) == O.sub(~F, zr(~F, n, x, u), zr(~F, n, y, u)) : O.C(F)}
  %drop_vneg(~F, n, y) : {M.dot(~F, M.vadd(~F, GJ.vdrop(~F, n, x), _), u) == O.sub(~F, zr(~F, n, x, u), zr(~F, n, y, u)) : O.C(F)}
  %FM.dot_vadd(~F, GJ.vdrop(~F, n, x), M.vneg(~F, GJ.vdrop(~F, n, y)), u) : {_ == O.sub(~F, zr(~F, n, x, u), zr(~F, n, y, u)) : O.C(F)}
  %FM.dot_vneg(~F, GJ.vdrop(~F, n, y), u) : {O.add(F, M.dot(~F, GJ.vdrop(~F, n, x), u), _) == O.sub(~F, zr(~F, n, x, u), zr(~F, n, y, u)) : O.C(F)}
  FR.fring_eq(~F, [M.dot(~F, GJ.vdrop(~F, n, x), u), M.dot(~F, GJ.vdrop(~F, n, y), u)], E.ZAdd{E.ZVar{0n}, E.ZNeg{E.ZVar{1n}}}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, {==})

# zr of x + (-m) p
def zr_axpy(~F: O.OField, +n: Nat, +x: M.Vec(~F), +m: O.C(F), +p: M.Vec(~F), +u: M.Vec(~F)) -> {zr(~F, n, M.vadd(~F, x, M.vscale(~F, O.neg(F, m), p)), u) == O.add(F, zr(~F, n, x, u), O.mul(F, O.neg(F, m), zr(~F, n, p, u))) : O.C(F)}:
  %drop_vadd(~F, n, x, M.vscale(~F, O.neg(F, m), p)) : {M.dot(~F, _, u) == O.add(F, zr(~F, n, x, u), O.mul(F, O.neg(F, m), zr(~F, n, p, u))) : O.C(F)}
  %drop_vscale(~F, n, O.neg(F, m), p) : {M.dot(~F, M.vadd(~F, GJ.vdrop(~F, n, x), _), u) == O.add(F, zr(~F, n, x, u), O.mul(F, O.neg(F, m), zr(~F, n, p, u))) : O.C(F)}
  %FM.dot_vadd(~F, GJ.vdrop(~F, n, x), M.vscale(~F, O.neg(F, m), GJ.vdrop(~F, n, p)), u) : {_ == O.add(F, zr(~F, n, x, u), O.mul(F, O.neg(F, m), zr(~F, n, p, u))) : O.C(F)}
  %FM.dot_vscale(~F, O.neg(F, m), GJ.vdrop(~F, n, p), u) : {O.add(F, M.dot(~F, GJ.vdrop(~F, n, x), u), _) == O.add(F, zr(~F, n, x, u), O.mul(F, O.neg(F, m), zr(~F, n, p, u))) : O.C(F)}
  {==}

# zr of s x
def zr_scale(~F: O.OField, +n: Nat, +s: O.C(F), +x: M.Vec(~F), +u: M.Vec(~F)) -> {zr(~F, n, M.vscale(~F, s, x), u) == O.mul(F, s, zr(~F, n, x, u)) : O.C(F)}:
  %drop_vscale(~F, n, s, x) : {M.dot(~F, _, u) == O.mul(F, s, zr(~F, n, x, u)) : O.C(F)}
  %FM.dot_vscale(~F, s, GJ.vdrop(~F, n, x), u) : {_ == O.mul(F, s, zr(~F, n, x, u)) : O.C(F)}
  {==}

# an error row: |zr(e)| <= n eps |u|
def zerr(~F: O.OField, +n: Nat, +e: M.Vec(~F), +u: M.Vec(~F), +ep: O.C(F), +he: M.vbnd.all(~F, e, ep), +hep: O.le(~F, O.zero(F), ep), lu: {M.len(~F, u) == n : Nat}) -> M.bnd(~F, zr(~F, n, e, u), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u))):
  FM.bnd_mono(~F, zr(~F, n, e, u), O.mul(F, NP.rowabs(~F, GJ.vdrop(~F, n, e), n), NP.vn(~F, u)), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u)),
    (%lu : M.bnd(~F, zr(~F, n, e, u), O.mul(F, NP.rowabs(~F, GJ.vdrop(~F, n, e), _), NP.vn(~F, u)))
      NP.dot_le(~F, GJ.vdrop(~F, n, e), u, NP.vn(~F, u), FV.vmax_all(~F, u), FV.vmax_nn(~F, u))),
    FM.sub_nonneg(~F, O.mul(F, NP.rowabs(~F, GJ.vdrop(~F, n, e), n), NP.vn(~F, u)), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u)), FV.mul_le_r(~F, NP.rowabs(~F, GJ.vdrop(~F, n, e), n), O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u), FV.vmax_nn(~F, u), rowabs_le(~F, GJ.vdrop(~F, n, e), n, ep, vall_drop(~F, n, e, ep, he), hep))))


# a row other than the pivot: x2 = x - m p + err, so
# |zr(x)| <= |zr(x2)| + |m| |zr(p)| + n eps |u|
def zo_bnd(~F: O.OField, +n: Nat, +x2: M.Vec(~F), +x: M.Vec(~F), +m: O.C(F), +p: M.Vec(~F), +u: M.Vec(~F), +ep: O.C(F), +he: M.vbnd.all(~F, M.vadd(~F, x2, M.vneg(~F, M.vadd(~F, x, M.vscale(~F, O.neg(F, m), p)))), ep), +hep: O.le(~F, O.zero(F), ep), +lu: {M.len(~F, u) == n : Nat}, +y: O.C(F), +gg: O.C(F), +h2: M.bnd(~F, zr(~F, n, x2, u), y), +hm: M.bnd(~F, m, gg), +hp: M.bnd(~F, zr(~F, n, p, u), y)) -> M.bnd(~F, zr(~F, n, x, u), O.add(F, O.add(F, y, O.mul(F, gg, y)), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u)))):
  three(~F, zr(~F, n, x, u), zr(~F, n, x2, u), m, zr(~F, n, p, u), y, gg, y, O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u)), h2, hm, hp,
    KB.bnd_val(~F, O.neg(F, O.sub(~F, zr(~F, n, x2, u), O.add(F, zr(~F, n, x, u), O.mul(F, O.neg(F, m), zr(~F, n, p, u))))), O.sub(~F, zr(~F, n, x, u), O.add(F, zr(~F, n, x2, u), O.mul(F, m, zr(~F, n, p, u)))), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u)), FR.fring_eq(~F, [zr(~F, n, x, u), zr(~F, n, x2, u), zr(~F, n, p, u), m], E.ZNeg{E.ZSub{E.ZVar{1n}, E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZNeg{E.ZVar{3n}}, E.ZVar{2n}}}}}, E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZMul{E.ZVar{3n}, E.ZVar{2n}}}}, {==}),
      FM.bnd_neg(~F, O.sub(~F, zr(~F, n, x2, u), O.add(F, zr(~F, n, x, u), O.mul(F, O.neg(F, m), zr(~F, n, p, u)))), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u)),
        (%zr_axpy(~F, n, x, m, p, u) : M.bnd(~F, O.sub(~F, zr(~F, n, x2, u), _), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u)))
          (%zr_sub(~F, n, x2, M.vadd(~F, x, M.vscale(~F, O.neg(F, m), p)), u) : M.bnd(~F, _, O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u)))
            zerr(~F, n, M.vadd(~F, x2, M.vneg(~F, M.vadd(~F, x, M.vscale(~F, O.neg(F, m), p)))), u, ep, he, hep, lu))))))


# the pivot row: p = s x + err, so |s zr(x)| <= |zr(p)| + n eps |u|
def zp_bnd(~F: O.OField, +n: Nat, +x: M.Vec(~F), +s: O.C(F), +p: M.Vec(~F), +u: M.Vec(~F), +ep: O.C(F), +he: M.vbnd.all(~F, M.vadd(~F, p, M.vneg(~F, M.vscale(~F, s, x))), ep), +hep: O.le(~F, O.zero(F), ep), +lu: {M.len(~F, u) == n : Nat}, +y: O.C(F), +hp: M.bnd(~F, zr(~F, n, p, u), y)) -> M.bnd(~F, O.mul(F, s, zr(~F, n, x, u)), O.add(F, y, O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u)))):
  KB.bnd_val(~F, O.add(F, zr(~F, n, p, u), O.neg(F, O.sub(~F, zr(~F, n, p, u), O.mul(F, s, zr(~F, n, x, u))))), O.mul(F, s, zr(~F, n, x, u)), O.add(F, y, O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u))), FR.fring_eq(~F, [zr(~F, n, x, u), zr(~F, n, p, u), s], E.ZAdd{E.ZVar{1n}, E.ZNeg{E.ZSub{E.ZVar{1n}, E.ZMul{E.ZVar{2n}, E.ZVar{0n}}}}}, E.ZMul{E.ZVar{2n}, E.ZVar{0n}}, {==}),
    FM.bnd_add(~F, zr(~F, n, p, u), y, O.neg(F, O.sub(~F, zr(~F, n, p, u), O.mul(F, s, zr(~F, n, x, u)))), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u)), hp,
      FM.bnd_neg(~F, O.sub(~F, zr(~F, n, p, u), O.mul(F, s, zr(~F, n, x, u))), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u)),
        (%zr_scale(~F, n, s, x, u) : M.bnd(~F, O.sub(~F, zr(~F, n, p, u), _), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u)))
          (%zr_sub(~F, n, p, M.vscale(~F, s, x), u) : M.bnd(~F, _, O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u)))
            zerr(~F, n, M.vadd(~F, p, M.vneg(~F, M.vscale(~F, s, x))), u, ep, he, hep, lu))))))


# dividing by the rounded pivot reciprocal loses at most a factor 2G:
# q pi = 1, |pi| <= G, |s - q| <= |q| u and 2 G |q| u <= 1 give
# |z| <= 2G |s z|
def piv_low(~F: O.OField, +z: O.C(F), +s: O.C(F), +q: O.C(F), +pi: O.C(F), +gg: O.C(F), +u: O.C(F), +y: O.C(F), +hq: {O.mul(F, q, pi) == O.one(F) : O.C(F)}, +hpi: M.bnd(~F, pi, gg), +hs: M.bnd(~F, O.sub(~F, s, q), O.mul(F, FV.fabs(~F, q), u)), +hsm: O.le(~F, O.add(F, O.mul(F, gg, O.mul(F, FV.fabs(~F, q), u)), O.mul(F, gg, O.mul(F, FV.fabs(~F, q), u))), O.one(F)), +hy: M.bnd(~F, O.mul(F, s, z), y)) -> M.bnd(~F, z, O.mul(F, O.add(F, gg, gg), y)):
  +h2 = KB.bnd_val(~F, O.add(F, O.mul(F, s, z), O.neg(F, O.mul(F, O.sub(~F, s, q), z))), O.mul(F, q, z), O.add(F, y, O.mul(F, O.mul(F, FV.fabs(~F, q), u), FV.fabs(~F, z))), FR.fring_eq(~F, [z, s, q, pi, gg, u, y, FV.fabs(~F, z), FV.fabs(~F, q)], E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{0n}}, E.ZNeg{E.ZMul{E.ZSub{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{0n}}}}, E.ZMul{E.ZVar{2n}, E.ZVar{0n}}, {==}),
    FM.bnd_add(~F, O.mul(F, s, z), y, O.neg(F, O.mul(F, O.sub(~F, s, q), z)), O.mul(F, O.mul(F, FV.fabs(~F, q), u), FV.fabs(~F, z)), hy, FM.bnd_neg(~F, O.mul(F, O.sub(~F, s, q), z), O.mul(F, O.mul(F, FV.fabs(~F, q), u), FV.fabs(~F, z)), FM.bnd_mul(~F, O.sub(~F, s, q), O.mul(F, FV.fabs(~F, q), u), z, FV.fabs(~F, z), hs, FV.fabs_bnd(~F, z)))))
  +h4 = FV.fabs_le(~F, z, O.mul(F, gg, O.add(F, y, O.mul(F, O.mul(F, FV.fabs(~F, q), u), FV.fabs(~F, z)))), KB.bnd_val(~F, O.mul(F, pi, O.mul(F, q, z)), z, O.mul(F, gg, O.add(F, y, O.mul(F, O.mul(F, FV.fabs(~F, q), u), FV.fabs(~F, z)))), FO.eq_of_sub(~F, O.mul(F, pi, O.mul(F, q, z)), z, FO.cert1(~F, O.sub(~F, O.mul(F, pi, O.mul(F, q, z)), z), z, O.sub(~F, O.mul(F, q, pi), O.one(F)), FR.fring_eq(~F, [z, s, q, pi, gg, u, y, FV.fabs(~F, z), FV.fabs(~F, q)], E.ZSub{E.ZMul{E.ZVar{3n}, E.ZMul{E.ZVar{2n}, E.ZVar{0n}}}, E.ZVar{0n}}, E.ZMul{E.ZVar{0n}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), FO.sub_of_eq(~F, O.mul(F, q, pi), O.one(F), hq))),
    FM.bnd_mul(~F, pi, gg, O.mul(F, q, z), O.add(F, y, O.mul(F, O.mul(F, FV.fabs(~F, q), u), FV.fabs(~F, z))), hpi, h2)))
  +s1 = FM.sub_nonneg(~F, FV.fabs(~F, z), O.mul(F, gg, O.add(F, y, O.mul(F, O.mul(F, FV.fabs(~F, q), u), FV.fabs(~F, z)))), h4)
  +s3 = FM.sub_nonneg(~F, O.add(F, O.mul(F, gg, O.mul(F, FV.fabs(~F, q), u)), O.mul(F, gg, O.mul(F, FV.fabs(~F, q), u))), O.one(F), hsm)
  FM.bnd_mono(~F, z, FV.fabs(~F, z), O.mul(F, O.add(F, gg, gg), y), FV.fabs_bnd(~F, z), FM.sub_nonneg(~F, FV.fabs(~F, z), O.mul(F, O.add(F, gg, gg), y),
    FV.le_of_sub(~F, FV.fabs(~F, z), O.mul(F, O.add(F, gg, gg), y), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.add(F, gg, gg), y), FV.fabs(~F, z)), O.add(F, O.add(F, O.sub(~F, O.mul(F, gg, O.add(F, y, O.mul(F, O.mul(F, FV.fabs(~F, q), u), FV.fabs(~F, z)))), FV.fabs(~F, z)), O.sub(~F, O.mul(F, gg, O.add(F, y, O.mul(F, O.mul(F, FV.fabs(~F, q), u), FV.fabs(~F, z)))), FV.fabs(~F, z))), O.mul(F, FV.fabs(~F, z), O.sub(~F, O.one(F), O.add(F, O.mul(F, gg, O.mul(F, FV.fabs(~F, q), u)), O.mul(F, gg, O.mul(F, FV.fabs(~F, q), u)))))), FR.fring_eq(~F, [z, s, q, pi, gg, u, y, FV.fabs(~F, z), FV.fabs(~F, q)], E.ZAdd{E.ZAdd{E.ZSub{E.ZMul{E.ZVar{4n}, E.ZAdd{E.ZVar{6n}, E.ZMul{E.ZMul{E.ZVar{8n}, E.ZVar{5n}}, E.ZVar{7n}}}}, E.ZVar{7n}}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZAdd{E.ZVar{6n}, E.ZMul{E.ZMul{E.ZVar{8n}, E.ZVar{5n}}, E.ZVar{7n}}}}, E.ZVar{7n}}}, E.ZMul{E.ZVar{7n}, E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZMul{E.ZVar{4n}, E.ZMul{E.ZVar{8n}, E.ZVar{5n}}}, E.ZMul{E.ZVar{4n}, E.ZMul{E.ZVar{8n}, E.ZVar{5n}}}}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZVar{4n}, E.ZVar{4n}}, E.ZVar{6n}}, E.ZVar{7n}}, {==}),
      FO.nonneg_add(~F, O.add(F, O.sub(~F, O.mul(F, gg, O.add(F, y, O.mul(F, O.mul(F, FV.fabs(~F, q), u), FV.fabs(~F, z)))), FV.fabs(~F, z)), O.sub(~F, O.mul(F, gg, O.add(F, y, O.mul(F, O.mul(F, FV.fabs(~F, q), u), FV.fabs(~F, z)))), FV.fabs(~F, z))), O.mul(F, FV.fabs(~F, z), O.sub(~F, O.one(F), O.add(F, O.mul(F, gg, O.mul(F, FV.fabs(~F, q), u)), O.mul(F, gg, O.mul(F, FV.fabs(~F, q), u))))), FO.nonneg_add(~F, O.sub(~F, O.mul(F, gg, O.add(F, y, O.mul(F, O.mul(F, FV.fabs(~F, q), u), FV.fabs(~F, z)))), FV.fabs(~F, z)), O.sub(~F, O.mul(F, gg, O.add(F, y, O.mul(F, O.mul(F, FV.fabs(~F, q), u), FV.fabs(~F, z)))), FV.fabs(~F, z)), s1, s1), FO.mul_nonneg(~F, FV.fabs(~F, z), O.sub(~F, O.one(F), O.add(F, O.mul(F, gg, O.mul(F, FV.fabs(~F, q), u)), O.mul(F, gg, O.mul(F, FV.fabs(~F, q), u)))), FV.fabs_nn(~F, z), s3))))))

# the right parts of a matrix's rows
def rmat(~F: O.OField, +n: Nat, a: M.Mat(~F)) -> M.Mat(~F):
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{GJ.vdrop(~F, n, r), rmat(~F, n, t)}

def vdrop_nil(~F: O.OField, n: Nat) -> {Nil{} == GJ.vdrop(~F, n, Nil{}) : M.Vec(~F)}:
  match n:
    case 0n:
      {==}
    case 1n+j:
      {==}

def mrow_rmat(~F: O.OField, +n: Nat, a: M.Mat(~F), k: Nat) -> {DV.mrow(~F, rmat(~F, n, a), k) == GJ.vdrop(~F, n, DV.mrow(~F, a, k)) : M.Vec(~F)}:
  match a k:
    case Nil{} k:
      vdrop_nil(~F, n)
    case Con{r, t} 0n:
      {==}
    case Con{r, t} 1n+j:
      mrow_rmat(~F, n, t, j)

def nrows_rmat(~F: O.OField, +n: Nat, a: M.Mat(~F)) -> {GJ.nrows(~F, rmat(~F, n, a)) == GJ.nrows(~F, a) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{r, t}:
      %Equal.sym(Nat, GJ.nrows(~F, rmat(~F, n, t)), GJ.nrows(~F, t), nrows_rmat(~F, n, t)) : {1n+_ == 1n+GJ.nrows(~F, t) : Nat}
      {==}

# entry k of R u reads row k's right part against u
def look_rmv(~F: O.OField, +n: Nat, +a: M.Mat(~F), +u: M.Vec(~F), +k: Nat) -> {O.lookup(~F, M.matvec(~F, rmat(~F, n, a), u), k) == zr(~F, n, DV.mrow(~F, a, k), u) : O.C(F)}:
  %mrow_rmat(~F, n, a, k) : {O.lookup(~F, M.matvec(~F, rmat(~F, n, a), u), k) == M.dot(~F, _, u) : O.C(F)}
  GJ.look_matvec(~F, rmat(~F, n, a), u, k)

def len_rmv(~F: O.OField, +n: Nat, +a: M.Mat(~F), +u: M.Vec(~F)) -> {M.len(~F, M.matvec(~F, rmat(~F, n, a), u)) == GJ.nrows(~F, a) : Nat}:
  Equal.trans(Nat, M.len(~F, M.matvec(~F, rmat(~F, n, a), u)), GJ.nrows(~F, rmat(~F, n, a)), GJ.nrows(~F, a), Equal.sym(Nat, GJ.nrows(~F, rmat(~F, n, a)), M.len(~F, M.matvec(~F, rmat(~F, n, a), u)), GJ.len_matvec(~F, rmat(~F, n, a), u)), nrows_rmat(~F, n, a))

def len_vdrop(~F: O.OField, k: Nat, x: M.Vec(~F), +m: Nat, h: {M.len(~F, x) == Nat.add(k, m) : Nat}) -> {M.len(~F, GJ.vdrop(~F, k, x)) == m : Nat}:
  match k x:
    case 0n x:
      h
    case 1n+j Nil{}:
      FO.absurd({0n == m : Nat}, GJ.zero_ne(Nat.add(j, m), h))
    case 1n++j Con{a, +xs}:
      len_vdrop(~F, j, xs, m, GJ.succ_inj(M.len(~F, xs), Nat.add(j, m), h))

# the rows of R have n entries
def rw_all(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +s: M.Mat(~F), +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +h: rinv(~F, n, jm, s, 0n, c, gg, dd, ph), +hn: {GJ.nrows(~F, s) == n : Nat}) -> GJ.All(~(i => GJ.roww(~F, rmat(~F, n, s), n, i)), n):
  GJ.all_mk(~n, ~(i => GJ.roww(~F, rmat(~F, n, s), n, i)), ~(i => hi =>
    (%Equal.sym(M.Vec(~F), DV.mrow(~F, rmat(~F, n, s), i), GJ.vdrop(~F, n, DV.mrow(~F, s, i)), mrow_rmat(~F, n, s, i)) : {M.len(~F, _) == n : Nat}
      len_vdrop(~F, n, DV.mrow(~F, s, i), n, ri_len(~F, n, jm, DV.mrow(~F, s, i), Nat.add(i, 0n), c, gg, dd, ph, ri_at(~F, n, jm, s, 0n, c, gg, dd, ph, i, h, (%Equal.sym(Nat, GJ.nrows(~F, s), n, hn) : {KA.natle(1n+i, _) == True{} : Bool} hi)))))), n, GJ.le_refl(n))

# row k of the cleared rows is the pivot row (k = c) or row k less a
# multiple of it
def drow_dclear(~F: O.OField, rows: List<&2, List<&2, S.D>>, +w: Nat, +p: List<&2, S.D>, +c: Nat, +i: Nat, k: Nat, hk: {KA.natle(1n+k, GJ.nrows(~F, M.ofdm(~F, rows))) == True{} : Bool}) -> {NU.drow(NU.dclear(rows, w, p, c, i), k) == NU.dclear.go(KA.nateq(Nat.add(k, i), c), w, NU.drow(rows, k), p, c) : List<&2, S.D>}:
  match rows k:
    case Nil{} 0n:
      FO.absurd({NU.drow(Nil{}, 0n) == NU.dclear.go(KA.nateq(i, c), w, NU.drow(Nil{}, 0n), p, c) : List<&2, S.D>}, KA.ft(hk))
    case Nil{} 1n++j:
      FO.absurd({NU.drow(Nil{}, 1n+j) == NU.dclear.go(KA.nateq(1n+Nat.add(j, i), c), w, NU.drow(Nil{}, 1n+j), p, c) : List<&2, S.D>}, KA.ft(hk))
    case Con{r, t} 0n:
      {==}
    case Con{r, t} 1n++j:
      %Equal.sym(Nat, 1n+Nat.add(j, i), Nat.add(j, 1n+i), LN.add_succ(j, i)) : {NU.drow(NU.dclear(t, w, p, c, 1n+i), j) == NU.dclear.go(KA.nateq(_, c), w, NU.drow(t, j), p, c) : List<&2, S.D>}
      drow_dclear(~F, t, w, p, c, 1n+i, j, hk)

# row k's invariant, read from the rows' invariant
def row_at(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +rows: List<&2, List<&2, S.D>>, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +k: Nat, +hs: rinv(~F, n, jm, M.ofdm(~F, rows), 0n, c, gg, dd, ph), +hk: {KA.natle(1n+k, GJ.nrows(~F, M.ofdm(~F, rows))) == True{} : Bool}) -> rowinv(~F, n, jm, M.ofdv(~F, NU.drow(rows, k)), k, c, gg, dd, ph):
  (%Equal.sym(M.Vec(~F), M.ofdv(~F, NU.drow(rows, k)), DV.mrow(~F, M.ofdm(~F, rows), k), drow_ofd(~F, rows, k)) : rowinv(~F, n, jm, _, k, c, gg, dd, ph)
    (%Equal.sym(Nat, k, Nat.add(k, 0n), LN.add_zero(k)) : rowinv(~F, n, jm, DV.mrow(~F, M.ofdm(~F, rows), k), _, c, gg, dd, ph)
      ri_at(~F, n, jm, M.ofdm(~F, rows), 0n, c, gg, dd, ph, k, hs, hk)))

# a per-index bound below the length
def vall_lt(~F: O.OField, ~v: M.Vec(~F), ~t: O.C(F), ~f: @k: Nat -> {KA.natle(1n+k, M.len(~F, v)) == True{} : Bool} -> M.bnd(~F, O.lookup(~F, v, k), t)) -> M.vbnd.all(~F, v, t):
  vall_of_all(~F, v, t, GJ.all_mk(~M.len(~F, v), ~(k => M.bnd(~F, O.lookup(~F, v, k), t)), ~f, M.len(~F, v), GJ.le_refl(M.len(~F, v))))

# |R u|: the size of rows2's right parts read against u
def yv(~F: O.OField, +n: Nat, +rows2: List<&2, List<&2, S.D>>, +u: M.Vec(~F)) -> O.C(F):
  NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, rows2)), u))

def zat(~F: O.OField, +n: Nat, +rows2: List<&2, List<&2, S.D>>, +u: M.Vec(~F), +k: Nat) -> {O.lookup(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, rows2)), u), k) == zr(~F, n, M.ofdv(~F, NU.drow(rows2, k)), u) : O.C(F)}:
  %Equal.sym(M.Vec(~F), M.ofdv(~F, NU.drow(rows2, k)), DV.mrow(~F, M.ofdm(~F, rows2), k), drow_ofd(~F, rows2, k)) : {O.lookup(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, rows2)), u), k) == zr(~F, n, _, u) : O.C(F)}
  look_rmv(~F, n, M.ofdm(~F, rows2), u, k)

def yat(~F: O.OField, +n: Nat, +rows2: List<&2, List<&2, S.D>>, +u: M.Vec(~F), +k: Nat) -> M.bnd(~F, zr(~F, n, M.ofdv(~F, NU.drow(rows2, k)), u), yv(~F, n, rows2, u)):
  %zat(~F, n, rows2, u, k) : M.bnd(~F, _, yv(~F, n, rows2, u))
  look_bnd(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, rows2)), u), k, yv(~F, n, rows2, u), FV.vmax_all(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, rows2)), u)), FV.vmax_nn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, rows2)), u)))

# the cleared row k against the new |R' u|
def ynew(~F: O.OField, +n: Nat, +tr: List<&2, List<&2, S.D>>, +w: Nat, +p: List<&2, S.D>, +c: Nat, +u: M.Vec(~F), +k: Nat, +hk: {KA.natle(1n+k, GJ.nrows(~F, M.ofdm(~F, tr))) == True{} : Bool}) -> M.bnd(~F, zr(~F, n, M.ofdv(~F, NU.dclear.go(KA.nateq(k, c), w, NU.drow(tr, k), p, c)), u), yv(~F, n, NU.dclear(tr, w, p, c, 0n), u)):
  %Equal.sym(Nat, k, Nat.add(k, 0n), LN.add_zero(k)) : M.bnd(~F, zr(~F, n, M.ofdv(~F, NU.dclear.go(KA.nateq(_, c), w, NU.drow(tr, k), p, c)), u), yv(~F, n, NU.dclear(tr, w, p, c, 0n), u))
  %drow_dclear(~F, tr, w, p, c, 0n, k, hk) : M.bnd(~F, zr(~F, n, M.ofdv(~F, _), u), yv(~F, n, NU.dclear(tr, w, p, c, 0n), u))
  yat(~F, n, NU.dclear(tr, w, p, c, 0n), u, k)

# the new pivot row against |R' u|
def ypiv(~F: O.OField, +n: Nat, +tr: List<&2, List<&2, S.D>>, +w: Nat, +p: List<&2, S.D>, +c: Nat, +u: M.Vec(~F), +hc: {KA.natle(1n+c, GJ.nrows(~F, M.ofdm(~F, tr))) == True{} : Bool}) -> M.bnd(~F, zr(~F, n, M.ofdv(~F, p), u), yv(~F, n, NU.dclear(tr, w, p, c, 0n), u)):
  %GJ.nateq_refl(c) : M.bnd(~F, zr(~F, n, M.ofdv(~F, NU.dclear.go(_, w, NU.drow(tr, c), p, c)), u), yv(~F, n, NU.dclear(tr, w, p, c, 0n), u))
  ynew(~F, n, tr, w, p, c, u, c, hc)


# a cleared row's rounding: (G + 3 G G_P) u
def ekx(~F: O.OField, +gg: O.C(F), +gp: O.C(F), +w: Nat) -> O.C(F):
  O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))

def ek_nn(~F: O.OField, +gg: O.C(F), +gp: O.C(F), +w: Nat, +hgg: O.le(~F, O.zero(F), gg), +hgp0: O.le(~F, O.zero(F), gp)) -> O.le(~F, O.zero(F), ekx(~F, gg, gp, w)):
  FO.mul_nonneg(~F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), FO.nonneg_add(~F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp)), hgg, FO.nonneg_add(~F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp), FO.nonneg_add(~F, O.mul(F, gg, gp), O.mul(F, gg, gp), FO.mul_nonneg(~F, gg, gp, hgg, hgp0), FO.mul_nonneg(~F, gg, gp, hgg, hgp0)), FO.mul_nonneg(~F, gg, gp, hgg, hgp0))), u_nn(~F, w))

# the bounds on a row's |zr| from the two cases, and their sum
def xk(~F: O.OField, +n: Nat, +gg: O.C(F), +gp: O.C(F), +w: Nat, +y: O.C(F), +uv: O.C(F)) -> O.C(F):
  O.add(F, O.add(F, y, O.mul(F, gg, y)), O.mul(F, O.mul(F, FR.ofn(~F, n), ekx(~F, gg, gp, w)), uv))

def xp(~F: O.OField, +n: Nat, +gg: O.C(F), +ep: O.C(F), +y: O.C(F), +uv: O.C(F)) -> O.C(F):
  O.mul(F, O.add(F, gg, gg), O.add(F, y, O.mul(F, O.mul(F, FR.ofn(~F, n), ep), uv)))

def xk_nn(~F: O.OField, +n: Nat, +gg: O.C(F), +gp: O.C(F), +w: Nat, +y: O.C(F), +uv: O.C(F), +hgg: O.le(~F, O.zero(F), gg), +hgp0: O.le(~F, O.zero(F), gp), +hy: O.le(~F, O.zero(F), y), +hv: O.le(~F, O.zero(F), uv)) -> O.le(~F, O.zero(F), xk(~F, n, gg, gp, w, y, uv)):
  FO.nonneg_add(~F, O.add(F, y, O.mul(F, gg, y)), O.mul(F, O.mul(F, FR.ofn(~F, n), ekx(~F, gg, gp, w)), uv), FO.nonneg_add(~F, y, O.mul(F, gg, y), hy, FO.mul_nonneg(~F, gg, y, hgg, hy)), FO.mul_nonneg(~F, O.mul(F, FR.ofn(~F, n), ekx(~F, gg, gp, w)), uv, FO.mul_nonneg(~F, FR.ofn(~F, n), ekx(~F, gg, gp, w), ofn_nn(~F, n), ek_nn(~F, gg, gp, w, hgg, hgp0)), hv))

def xp_nn(~F: O.OField, +n: Nat, +gg: O.C(F), +ep: O.C(F), +y: O.C(F), +uv: O.C(F), +hgg: O.le(~F, O.zero(F), gg), +hep: O.le(~F, O.zero(F), ep), +hy: O.le(~F, O.zero(F), y), +hv: O.le(~F, O.zero(F), uv)) -> O.le(~F, O.zero(F), xp(~F, n, gg, ep, y, uv)):
  FO.mul_nonneg(~F, O.add(F, gg, gg), O.add(F, y, O.mul(F, O.mul(F, FR.ofn(~F, n), ep), uv)), FO.nonneg_add(~F, gg, gg, hgg, hgg), FO.nonneg_add(~F, y, O.mul(F, O.mul(F, FR.ofn(~F, n), ep), uv), hy, FO.mul_nonneg(~F, O.mul(F, FR.ofn(~F, n), ep), uv, FO.mul_nonneg(~F, FR.ofn(~F, n), ep, ofn_nn(~F, n), hep), hv)))

# entry k of R u, bounded by |R' u| and |u|: the pivot row (k = c)
# through piv_low, the others through zo_bnd
def low_at.go(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +w: Nat, +tr: List<&2, List<&2, S.D>>, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +p: List<&2, S.D>, +s: O.C(F), +q: O.C(F), +gp: O.C(F), +ep: O.C(F), +h: rinv(~F, n, jm, M.ofdm(~F, tr), 0n, c, gg, dd, ph), +hc: {KA.natle(1n+c, GJ.nrows(~F, M.ofdm(~F, tr))) == True{} : Bool}, +hq: {O.mul(F, q, O.lookup(~F, M.ofdv(~F, NU.drow(tr, c)), c)) == O.one(F) : O.C(F)}, +hs: M.bnd(~F, O.sub(~F, s, q), O.mul(F, FV.fabs(~F, q), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), +hsm: O.le(~F, O.add(F, O.mul(F, gg, O.mul(F, FV.fabs(~F, q), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, gg, O.mul(F, FV.fabs(~F, q), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.one(F)), +hpe: M.vbnd.all(~F, M.vadd(~F, M.ofdv(~F, p), M.vneg(~F, M.vscale(~F, s, M.ofdv(~F, NU.drow(tr, c))))), ep), +hep: O.le(~F, O.zero(F), ep), +hgp: M.vbnd.all(~F, M.ofdv(~F, p), gp), +lp: {M.len(~F, M.ofdv(~F, p)) == Nat.add(n, n) : Nat}, +hgg: O.le(~F, O.zero(F), gg), +hgp0: O.le(~F, O.zero(F), gp), +hu: O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F)), +u: M.Vec(~F), +lu: {M.len(~F, u) == n : Nat}, +k: Nat, +hk: {KA.natle(1n+k, GJ.nrows(~F, M.ofdm(~F, tr))) == True{} : Bool}, b: Bool, e: {KA.nateq(k, c) == b : Bool}) -> M.bnd(~F, zr(~F, n, M.ofdv(~F, NU.drow(tr, k)), u), O.add(F, xk(~F, n, gg, gp, w, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), xp(~F, n, gg, ep, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)))):
  match b:
    case True{}:
      +hy = FV.vmax_nn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, NU.dclear(tr, w, p, c, 0n))), u))
      +hv = FV.vmax_nn(~F, u)
      %Equal.sym(Nat, k, c, GJ.nateq_ok(k, c, e)) : M.bnd(~F, zr(~F, n, M.ofdv(~F, NU.drow(tr, _)), u), O.add(F, xk(~F, n, gg, gp, w, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), xp(~F, n, gg, ep, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u))))
      FM.bnd_mono(~F, zr(~F, n, M.ofdv(~F, NU.drow(tr, c)), u), xp(~F, n, gg, ep, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), O.add(F, xk(~F, n, gg, gp, w, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), xp(~F, n, gg, ep, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u))),
        piv_low(~F, zr(~F, n, M.ofdv(~F, NU.drow(tr, c)), u), s, q, O.lookup(~F, M.ofdv(~F, NU.drow(tr, c)), c), gg, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.add(F, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u))), hq, look_bnd(~F, M.ofdv(~F, NU.drow(tr, c)), c, gg, ri_e(~F, n, jm, M.ofdv(~F, NU.drow(tr, c)), c, c, gg, dd, ph, row_at(~F, n, jm, tr, c, gg, dd, ph, c, h, hc)), hgg), hs, hsm,
          zp_bnd(~F, n, M.ofdv(~F, NU.drow(tr, c)), s, M.ofdv(~F, p), u, ep, hpe, hep, lu, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), ypiv(~F, n, tr, w, p, c, u, hc))),
        FM.sub_nonneg(~F, xp(~F, n, gg, ep, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), O.add(F, xk(~F, n, gg, gp, w, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), xp(~F, n, gg, ep, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u))), le_addl(~F, xk(~F, n, gg, gp, w, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), xp(~F, n, gg, ep, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), xk_nn(~F, n, gg, gp, w, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u), hgg, hgp0, hy, hv))))
    case False{}:
      +hy = FV.vmax_nn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, NU.dclear(tr, w, p, c, 0n))), u))
      +hv = FV.vmax_nn(~F, u)
      +rk = row_at(~F, n, jm, tr, c, gg, dd, ph, k, h, hk)
      FM.bnd_mono(~F, zr(~F, n, M.ofdv(~F, NU.drow(tr, k)), u), xk(~F, n, gg, gp, w, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), O.add(F, xk(~F, n, gg, gp, w, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), xp(~F, n, gg, ep, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u))),
        zo_bnd(~F, n, M.ofdv(~F, NU.daxpy(w, NU.drow(tr, k), NU.dget(NU.drow(tr, k), c), p)), M.ofdv(~F, NU.drow(tr, k)), O.lookup(~F, M.ofdv(~F, NU.drow(tr, k)), c), M.ofdv(~F, p), u, ekx(~F, gg, gp, w),
          (%dget_ofd(~F, NU.drow(tr, k), c) : M.vbnd.all(~F, M.vadd(~F, M.ofdv(~F, NU.daxpy(w, NU.drow(tr, k), NU.dget(NU.drow(tr, k), c), p)), M.vneg(~F, M.vadd(~F, M.ofdv(~F, NU.drow(tr, k)), M.vscale(~F, O.neg(F, _), M.ofdv(~F, p))))), ekx(~F, gg, gp, w))
            daxpy_err(~F, w, NU.drow(tr, k), NU.dget(NU.drow(tr, k), c), p, gg, gg, gp, ri_e(~F, n, jm, M.ofdv(~F, NU.drow(tr, k)), k, c, gg, dd, ph, rk), (%Equal.sym(O.C(F), M.ofd(~F, NU.dget(NU.drow(tr, k), c)), O.lookup(~F, M.ofdv(~F, NU.drow(tr, k)), c), dget_ofd(~F, NU.drow(tr, k), c)) : M.bnd(~F, _, gg)
              look_bnd(~F, M.ofdv(~F, NU.drow(tr, k)), c, gg, ri_e(~F, n, jm, M.ofdv(~F, NU.drow(tr, k)), k, c, gg, dd, ph, rk), hgg)), hgp, Equal.trans(Nat, M.len(~F, M.ofdv(~F, NU.drow(tr, k))), Nat.add(n, n), M.len(~F, M.ofdv(~F, p)), ri_len(~F, n, jm, M.ofdv(~F, NU.drow(tr, k)), k, c, gg, dd, ph, rk), Equal.sym(Nat, M.len(~F, M.ofdv(~F, p)), Nat.add(n, n), lp)), hu)),
          ek_nn(~F, gg, gp, w, hgg, hgp0), lu, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), gg,
          (%e : M.bnd(~F, zr(~F, n, M.ofdv(~F, NU.dclear.go(_, w, NU.drow(tr, k), p, c)), u), yv(~F, n, NU.dclear(tr, w, p, c, 0n), u))
            ynew(~F, n, tr, w, p, c, u, k, hk)),
          look_bnd(~F, M.ofdv(~F, NU.drow(tr, k)), c, gg, ri_e(~F, n, jm, M.ofdv(~F, NU.drow(tr, k)), k, c, gg, dd, ph, rk), hgg),
          ypiv(~F, n, tr, w, p, c, u, hc)),
        FM.sub_nonneg(~F, xk(~F, n, gg, gp, w, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), O.add(F, xk(~F, n, gg, gp, w, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), xp(~F, n, gg, ep, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u))), le_addr(~F, xk(~F, n, gg, gp, w, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), xp(~F, n, gg, ep, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), xp_nn(~F, n, gg, ep, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u), hgg, hep, hy, hv))))

# the step's constants: |u| <= H |R u| <= H (A |R' u| + B |u|)
def aco(~F: O.OField, +gg: O.C(F)) -> O.C(F):
  O.add(F, O.add(F, O.one(F), gg), O.add(F, gg, gg))

def bco(~F: O.OField, +n: Nat, +gg: O.C(F), +gp: O.C(F), +ep: O.C(F), +w: Nat) -> O.C(F):
  O.add(F, O.mul(F, FR.ofn(~F, n), ekx(~F, gg, gp, w)), O.mul(F, O.add(F, gg, gg), O.mul(F, FR.ofn(~F, n), ep)))


# the lower bound for R': |u| <= 2 H A |R' u| once 2 H B <= 1
def low_vec(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +w: Nat, +tr: List<&2, List<&2, S.D>>, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +p: List<&2, S.D>, +s: O.C(F), +q: O.C(F), +gp: O.C(F), +ep: O.C(F), +h: rinv(~F, n, jm, M.ofdm(~F, tr), 0n, c, gg, dd, ph), +hc: {KA.natle(1n+c, GJ.nrows(~F, M.ofdm(~F, tr))) == True{} : Bool}, +hq: {O.mul(F, q, O.lookup(~F, M.ofdv(~F, NU.drow(tr, c)), c)) == O.one(F) : O.C(F)}, +hs: M.bnd(~F, O.sub(~F, s, q), O.mul(F, FV.fabs(~F, q), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), +hsm: O.le(~F, O.add(F, O.mul(F, gg, O.mul(F, FV.fabs(~F, q), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, gg, O.mul(F, FV.fabs(~F, q), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.one(F)), +hpe: M.vbnd.all(~F, M.vadd(~F, M.ofdv(~F, p), M.vneg(~F, M.vscale(~F, s, M.ofdv(~F, NU.drow(tr, c))))), ep), +hep: O.le(~F, O.zero(F), ep), +hgp: M.vbnd.all(~F, M.ofdv(~F, p), gp), +lp: {M.len(~F, M.ofdv(~F, p)) == Nat.add(n, n) : Nat}, +hgg: O.le(~F, O.zero(F), gg), +hgp0: O.le(~F, O.zero(F), gp), +hu: O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F)), +hnt: {GJ.nrows(~F, M.ofdm(~F, tr)) == n : Nat}, +hh: O.C(F), +hH: NP.InvB(~F, rmat(~F, n, M.ofdm(~F, tr)), n, hh), +hB: O.le(~F, O.add(F, O.mul(F, hh, bco(~F, n, gg, gp, ep, w)), O.mul(F, hh, bco(~F, n, gg, gp, ep, w))), O.one(F)), +u: M.Vec(~F), +lu: {M.len(~F, u) == n : Nat}) -> O.le(~F, NP.vn(~F, u), O.mul(F, O.mul(F, O.add(F, hh, hh), aco(~F, gg)), NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, NU.dclear(tr, w, p, c, 0n))), u)))):
  +hy = FV.vmax_nn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, NU.dclear(tr, w, p, c, 0n))), u))
  +hv = FV.vmax_nn(~F, u)
  +hx = FV.vmax_lub(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, tr)), u), O.add(F, xk(~F, n, gg, gp, w, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), xp(~F, n, gg, ep, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u))), vall_lt(~F, ~M.matvec(~F, rmat(~F, n, M.ofdm(~F, tr)), u), ~O.add(F, xk(~F, n, gg, gp, w, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), xp(~F, n, gg, ep, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u))), ~(k => hk =>
      (%Equal.sym(O.C(F), O.lookup(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, tr)), u), k), zr(~F, n, M.ofdv(~F, NU.drow(tr, k)), u), zat(~F, n, tr, u, k)) : M.bnd(~F, _, O.add(F, xk(~F, n, gg, gp, w, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), xp(~F, n, gg, ep, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u))))
        low_at.go(~F, n, jm, w, tr, c, gg, dd, ph, p, s, q, gp, ep, h, hc, hq, hs, hsm, hpe, hep, hgp, lp, hgg, hgp0, hu, u, lu, k, (%len_rmv(~F, n, M.ofdm(~F, tr), u) : {KA.natle(1n+k, _) == True{} : Bool} hk), KA.nateq(k, c), {==})))),
    FO.nonneg_add(~F, xk(~F, n, gg, gp, w, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), xp(~F, n, gg, ep, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), xk_nn(~F, n, gg, gp, w, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u), hgg, hgp0, hy, hv), xp_nn(~F, n, gg, ep, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u), hgg, hep, hy, hv)))
  +hl = NP.lowb(~F, rmat(~F, n, M.ofdm(~F, tr)), n, hh, hH, Equal.trans(Nat, GJ.nrows(~F, rmat(~F, n, M.ofdm(~F, tr))), GJ.nrows(~F, M.ofdm(~F, tr)), n, nrows_rmat(~F, n, M.ofdm(~F, tr)), hnt), u, lu)
  +hh0 = NP.invb_nn(~F, rmat(~F, n, M.ofdm(~F, tr)), n, hh, hH)
  +s1 = FM.sub_nonneg(~F, NP.vn(~F, u), O.mul(F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, tr)), u))), hl)
  +s2 = FM.sub_nonneg(~F, NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, tr)), u)), O.add(F, xk(~F, n, gg, gp, w, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u)), xp(~F, n, gg, ep, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u))), hx)
  +s3 = FM.sub_nonneg(~F, O.add(F, O.mul(F, hh, bco(~F, n, gg, gp, ep, w)), O.mul(F, hh, bco(~F, n, gg, gp, ep, w))), O.one(F), hB)
  FV.le_of_sub(~F, NP.vn(~F, u), O.mul(F, O.mul(F, O.add(F, hh, hh), aco(~F, gg)), yv(~F, n, NU.dclear(tr, w, p, c, 0n), u)), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.mul(F, O.add(F, hh, hh), O.add(F, O.add(F, O.one(F), gg), O.add(F, gg, gg))), yv(~F, n, NU.dclear(tr, w, p, c, 0n), u)), NP.vn(~F, u)), O.add(F, O.add(F, O.add(F, O.sub(~F, O.mul(F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, tr)), u))), NP.vn(~F, u)), O.sub(~F, O.mul(F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, tr)), u))), NP.vn(~F, u))), O.mul(F, O.add(F, hh, hh), O.sub(~F, O.add(F, O.add(F, O.add(F, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), O.mul(F, gg, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u))), O.mul(F, O.mul(F, FR.ofn(~F, n), ekx(~F, gg, gp, w)), NP.vn(~F, u))), O.mul(F, O.add(F, gg, gg), O.add(F, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u))))), NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, tr)), u))))), O.mul(F, NP.vn(~F, u), O.sub(~F, O.one(F), O.add(F, O.mul(F, hh, O.add(F, O.mul(F, FR.ofn(~F, n), ekx(~F, gg, gp, w)), O.mul(F, O.add(F, gg, gg), O.mul(F, FR.ofn(~F, n), ep)))), O.mul(F, hh, O.add(F, O.mul(F, FR.ofn(~F, n), ekx(~F, gg, gp, w)), O.mul(F, O.add(F, gg, gg), O.mul(F, FR.ofn(~F, n), ep)))))))),
    FR.fring_eq(~F, [yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), NP.vn(~F, u), NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, tr)), u)), gg, hh, FR.ofn(~F, n), ekx(~F, gg, gp, w), ep], E.ZAdd{E.ZAdd{E.ZAdd{E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{2n}}, E.ZVar{1n}}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{2n}}, E.ZVar{1n}}}, E.ZMul{E.ZAdd{E.ZVar{4n}, E.ZVar{4n}}, E.ZSub{E.ZAdd{E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZVar{3n}, E.ZVar{0n}}}, E.ZMul{E.ZMul{E.ZVar{5n}, E.ZVar{6n}}, E.ZVar{1n}}}, E.ZMul{E.ZAdd{E.ZVar{3n}, E.ZVar{3n}}, E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZMul{E.ZVar{5n}, E.ZVar{7n}}, E.ZVar{1n}}}}}, E.ZVar{2n}}}}, E.ZMul{E.ZVar{1n}, E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZMul{E.ZVar{4n}, E.ZAdd{E.ZMul{E.ZVar{5n}, E.ZVar{6n}}, E.ZMul{E.ZAdd{E.ZVar{3n}, E.ZVar{3n}}, E.ZMul{E.ZVar{5n}, E.ZVar{7n}}}}}, E.ZMul{E.ZVar{4n}, E.ZAdd{E.ZMul{E.ZVar{5n}, E.ZVar{6n}}, E.ZMul{E.ZAdd{E.ZVar{3n}, E.ZVar{3n}}, E.ZMul{E.ZVar{5n}, E.ZVar{7n}}}}}}}}}, E.ZSub{E.ZMul{E.ZMul{E.ZAdd{E.ZVar{4n}, E.ZVar{4n}}, E.ZAdd{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{3n}}, E.ZAdd{E.ZVar{3n}, E.ZVar{3n}}}}, E.ZVar{0n}}, E.ZVar{1n}}, {==}),
    FO.nonneg_add(~F, O.add(F, O.add(F, O.sub(~F, O.mul(F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, tr)), u))), NP.vn(~F, u)), O.sub(~F, O.mul(F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, tr)), u))), NP.vn(~F, u))), O.mul(F, O.add(F, hh, hh), O.sub(~F, O.add(F, O.add(F, O.add(F, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), O.mul(F, gg, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u))), O.mul(F, O.mul(F, FR.ofn(~F, n), ekx(~F, gg, gp, w)), NP.vn(~F, u))), O.mul(F, O.add(F, gg, gg), O.add(F, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u))))), NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, tr)), u))))), O.mul(F, NP.vn(~F, u), O.sub(~F, O.one(F), O.add(F, O.mul(F, hh, O.add(F, O.mul(F, FR.ofn(~F, n), ekx(~F, gg, gp, w)), O.mul(F, O.add(F, gg, gg), O.mul(F, FR.ofn(~F, n), ep)))), O.mul(F, hh, O.add(F, O.mul(F, FR.ofn(~F, n), ekx(~F, gg, gp, w)), O.mul(F, O.add(F, gg, gg), O.mul(F, FR.ofn(~F, n), ep))))))),
      FO.nonneg_add(~F, O.add(F, O.sub(~F, O.mul(F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, tr)), u))), NP.vn(~F, u)), O.sub(~F, O.mul(F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, tr)), u))), NP.vn(~F, u))), O.mul(F, O.add(F, hh, hh), O.sub(~F, O.add(F, O.add(F, O.add(F, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), O.mul(F, gg, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u))), O.mul(F, O.mul(F, FR.ofn(~F, n), ekx(~F, gg, gp, w)), NP.vn(~F, u))), O.mul(F, O.add(F, gg, gg), O.add(F, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u))))), NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, tr)), u)))), FO.nonneg_add(~F, O.sub(~F, O.mul(F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, tr)), u))), NP.vn(~F, u)), O.sub(~F, O.mul(F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, tr)), u))), NP.vn(~F, u)), s1, s1),
        FO.mul_nonneg(~F, O.add(F, hh, hh), O.sub(~F, O.add(F, O.add(F, O.add(F, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), O.mul(F, gg, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u))), O.mul(F, O.mul(F, FR.ofn(~F, n), ekx(~F, gg, gp, w)), NP.vn(~F, u))), O.mul(F, O.add(F, gg, gg), O.add(F, yv(~F, n, NU.dclear(tr, w, p, c, 0n), u), O.mul(F, O.mul(F, FR.ofn(~F, n), ep), NP.vn(~F, u))))), NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, tr)), u))), FO.nonneg_add(~F, hh, hh, hh0, hh0), s2)),
      FO.mul_nonneg(~F, NP.vn(~F, u), O.sub(~F, O.one(F), O.add(F, O.mul(F, hh, O.add(F, O.mul(F, FR.ofn(~F, n), ekx(~F, gg, gp, w)), O.mul(F, O.add(F, gg, gg), O.mul(F, FR.ofn(~F, n), ep)))), O.mul(F, hh, O.add(F, O.mul(F, FR.ofn(~F, n), ekx(~F, gg, gp, w)), O.mul(F, O.add(F, gg, gg), O.mul(F, FR.ofn(~F, n), ep)))))), hv, s3))))

# one column step keeps an inverse of the right halves, of norm at most
# 2 H A
def col_low(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +w: Nat, +tr: List<&2, List<&2, S.D>>, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +p: List<&2, S.D>, +s: O.C(F), +q: O.C(F), +gp: O.C(F), +ep: O.C(F), +h: rinv(~F, n, jm, M.ofdm(~F, tr), 0n, c, gg, dd, ph), +hc: {KA.natle(1n+c, GJ.nrows(~F, M.ofdm(~F, tr))) == True{} : Bool}, +hq: {O.mul(F, q, O.lookup(~F, M.ofdv(~F, NU.drow(tr, c)), c)) == O.one(F) : O.C(F)}, +hs: M.bnd(~F, O.sub(~F, s, q), O.mul(F, FV.fabs(~F, q), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), +hsm: O.le(~F, O.add(F, O.mul(F, gg, O.mul(F, FV.fabs(~F, q), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, gg, O.mul(F, FV.fabs(~F, q), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.one(F)), +hpe: M.vbnd.all(~F, M.vadd(~F, M.ofdv(~F, p), M.vneg(~F, M.vscale(~F, s, M.ofdv(~F, NU.drow(tr, c))))), ep), +hep: O.le(~F, O.zero(F), ep), +hgp: M.vbnd.all(~F, M.ofdv(~F, p), gp), +lp: {M.len(~F, M.ofdv(~F, p)) == Nat.add(n, n) : Nat}, +hgg: O.le(~F, O.zero(F), gg), +hgp0: O.le(~F, O.zero(F), gp), +hu: O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F)), +hnt: {GJ.nrows(~F, M.ofdm(~F, tr)) == n : Nat}, +hh: O.C(F), +hH: NP.InvB(~F, rmat(~F, n, M.ofdm(~F, tr)), n, hh), +hB: O.le(~F, O.add(F, O.mul(F, hh, bco(~F, n, gg, gp, ep, w)), O.mul(F, hh, bco(~F, n, gg, gp, ep, w))), O.one(F)), +gg2: O.C(F), +dd2: O.C(F), +ph2: O.C(F), +h2: rinv(~F, n, jm, M.ofdm(~F, NU.dclear(tr, w, p, c, 0n)), 0n, 1n+c, gg2, dd2, ph2), +hn2: {GJ.nrows(~F, M.ofdm(~F, NU.dclear(tr, w, p, c, 0n))) == n : Nat}) -> NP.InvB(~F, rmat(~F, n, M.ofdm(~F, NU.dclear(tr, w, p, c, 0n))), n, O.mul(F, O.add(F, hh, hh), aco(~F, gg))):
  NP.invb_of_low(~F, ~rmat(~F, n, M.ofdm(~F, NU.dclear(tr, w, p, c, 0n))), ~n, ~O.mul(F, O.add(F, hh, hh), aco(~F, gg)), ~(u => lu => low_vec(~F, n, jm, w, tr, c, gg, dd, ph, p, s, q, gp, ep, h, hc, hq, hs, hsm, hpe, hep, hgp, lp, hgg, hgp0, hu, hnt, hh, hH, hB, u, lu)),
    FO.mul_nonneg(~F, O.add(F, hh, hh), aco(~F, gg), FO.nonneg_add(~F, hh, hh, NP.invb_nn(~F, rmat(~F, n, M.ofdm(~F, tr)), n, hh, hH), NP.invb_nn(~F, rmat(~F, n, M.ofdm(~F, tr)), n, hh, hH)), FO.nonneg_add(~F, O.add(F, O.one(F), gg), O.add(F, gg, gg), FO.nonneg_add(~F, O.one(F), gg, NP.one_nn(~F), hgg), FO.nonneg_add(~F, gg, gg, hgg, hgg))),
    Equal.trans(Nat, GJ.nrows(~F, rmat(~F, n, M.ofdm(~F, NU.dclear(tr, w, p, c, 0n)))), GJ.nrows(~F, M.ofdm(~F, NU.dclear(tr, w, p, c, 0n))), n, nrows_rmat(~F, n, M.ofdm(~F, NU.dclear(tr, w, p, c, 0n))), hn2),
    rw_all(~F, n, jm, M.ofdm(~F, NU.dclear(tr, w, p, c, 0n)), 1n+c, gg2, dd2, ph2, h2, hn2))

# row j of a, against u: at most |R_a u|
def zb(~F: O.OField, +n: Nat, +a: M.Mat(~F), +u: M.Vec(~F), +j: Nat) -> M.bnd(~F, zr(~F, n, DV.mrow(~F, a, j), u), NP.vn(~F, M.matvec(~F, rmat(~F, n, a), u))):
  %look_rmv(~F, n, a, u, j) : M.bnd(~F, _, NP.vn(~F, M.matvec(~F, rmat(~F, n, a), u)))
  look_bnd(~F, M.matvec(~F, rmat(~F, n, a), u), j, NP.vn(~F, M.matvec(~F, rmat(~F, n, a), u)), FV.vmax_all(~F, M.matvec(~F, rmat(~F, n, a), u)), FV.vmax_nn(~F, M.matvec(~F, rmat(~F, n, a), u)))

# every row of a is a row of a with rows c and r swapped
def swp_go(~F: O.OField, +n: Nat, +a: M.Mat(~F), +c: Nat, +r: Nat, +u: M.Vec(~F), +k: Nat, +hc: {KA.natle(1n+c, GJ.nrows(~F, a)) == True{} : Bool}, +hr: {KA.natle(1n+r, GJ.nrows(~F, a)) == True{} : Bool}, b1: Bool, +e1: {KA.nateq(k, c) == b1 : Bool}, b2: Bool, +e2: {KA.nateq(k, r) == b2 : Bool}) -> M.bnd(~F, zr(~F, n, DV.mrow(~F, a, k), u), NP.vn(~F, M.matvec(~F, rmat(~F, n, GJ.mswap(~F, a, c, r)), u))):
  match b1:
    case True{}:
      %Equal.sym(Nat, k, c, GJ.nateq_ok(k, c, e1)) : M.bnd(~F, zr(~F, n, DV.mrow(~F, a, _), u), NP.vn(~F, M.matvec(~F, rmat(~F, n, GJ.mswap(~F, a, c, r)), u)))
      %Equal.sym(M.Vec(~F), DV.mrow(~F, a, c), DV.mrow(~F, GJ.mswap(~F, a, c, r), r), GJ.row_mset_eq(~F, GJ.mset(~F, a, c, DV.mrow(~F, a, r)), r, DV.mrow(~F, a, c), GJ.lt_nrows_mset(~F, a, c, DV.mrow(~F, a, r), r, hr))) : M.bnd(~F, zr(~F, n, _, u), NP.vn(~F, M.matvec(~F, rmat(~F, n, GJ.mswap(~F, a, c, r)), u)))
      zb(~F, n, GJ.mswap(~F, a, c, r), u, r)
    case False{}:
      match b2:
        case True{}:
          %Equal.sym(Nat, k, r, GJ.nateq_ok(k, r, e2)) : M.bnd(~F, zr(~F, n, DV.mrow(~F, a, _), u), NP.vn(~F, M.matvec(~F, rmat(~F, n, GJ.mswap(~F, a, c, r)), u)))
          %Equal.sym(M.Vec(~F), DV.mrow(~F, a, r), DV.mrow(~F, GJ.mswap(~F, a, c, r), c), Equal.trans(M.Vec(~F), DV.mrow(~F, a, r), DV.mrow(~F, GJ.mset(~F, a, c, DV.mrow(~F, a, r)), c), DV.mrow(~F, GJ.mswap(~F, a, c, r), c), GJ.row_mset_eq(~F, a, c, DV.mrow(~F, a, r), hc), GJ.row_mset_ne(~F, GJ.mset(~F, a, c, DV.mrow(~F, a, r)), r, c, DV.mrow(~F, a, c), (%GJ.nateq_ok(k, r, e2) : {KA.nateq(_, c) == False{} : Bool} e1)))) : M.bnd(~F, zr(~F, n, _, u), NP.vn(~F, M.matvec(~F, rmat(~F, n, GJ.mswap(~F, a, c, r)), u)))
          zb(~F, n, GJ.mswap(~F, a, c, r), u, c)
        case False{}:
          %Equal.sym(M.Vec(~F), DV.mrow(~F, a, k), DV.mrow(~F, GJ.mswap(~F, a, c, r), k), Equal.trans(M.Vec(~F), DV.mrow(~F, a, k), DV.mrow(~F, GJ.mset(~F, a, c, DV.mrow(~F, a, r)), k), DV.mrow(~F, GJ.mswap(~F, a, c, r), k), GJ.row_mset_ne(~F, a, c, k, DV.mrow(~F, a, r), Equal.trans(Bool, KA.nateq(c, k), KA.nateq(k, c), False{}, GJ.nateq_sym(c, k), e1)), GJ.row_mset_ne(~F, GJ.mset(~F, a, c, DV.mrow(~F, a, r)), r, k, DV.mrow(~F, a, c), Equal.trans(Bool, KA.nateq(r, k), KA.nateq(k, r), False{}, GJ.nateq_sym(r, k), e2)))) : M.bnd(~F, zr(~F, n, _, u), NP.vn(~F, M.matvec(~F, rmat(~F, n, GJ.mswap(~F, a, c, r)), u)))
          zb(~F, n, GJ.mswap(~F, a, c, r), u, k)

# |u| <= H |R u| <= H |R_swapped u|
def sw_low(~F: O.OField, +n: Nat, +a: M.Mat(~F), +c: Nat, +r: Nat, +hh: O.C(F), +hH: NP.InvB(~F, rmat(~F, n, a), n, hh), +hna: {GJ.nrows(~F, a) == n : Nat}, +hc: {KA.natle(1n+c, GJ.nrows(~F, a)) == True{} : Bool}, +hr: {KA.natle(1n+r, GJ.nrows(~F, a)) == True{} : Bool}, +u: M.Vec(~F), +lu: {M.len(~F, u) == n : Nat}) -> O.le(~F, NP.vn(~F, u), O.mul(F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, GJ.mswap(~F, a, c, r)), u)))):
  DM.le_trans(~F, NP.vn(~F, u), O.mul(F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, a), u))), O.mul(F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, GJ.mswap(~F, a, c, r)), u))),
    NP.lowb(~F, rmat(~F, n, a), n, hh, hH, Equal.trans(Nat, GJ.nrows(~F, rmat(~F, n, a)), GJ.nrows(~F, a), n, nrows_rmat(~F, n, a), hna), u, lu),
    FV.mul_le(~F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, a), u)), NP.vn(~F, M.matvec(~F, rmat(~F, n, GJ.mswap(~F, a, c, r)), u)), NP.invb_nn(~F, rmat(~F, n, a), n, hh, hH),
      FV.vmax_lub(~F, M.matvec(~F, rmat(~F, n, a), u), NP.vn(~F, M.matvec(~F, rmat(~F, n, GJ.mswap(~F, a, c, r)), u)), vall_lt(~F, ~M.matvec(~F, rmat(~F, n, a), u), ~NP.vn(~F, M.matvec(~F, rmat(~F, n, GJ.mswap(~F, a, c, r)), u)), ~(k => hk =>
        (%Equal.sym(O.C(F), O.lookup(~F, M.matvec(~F, rmat(~F, n, a), u), k), zr(~F, n, DV.mrow(~F, a, k), u), look_rmv(~F, n, a, u, k)) : M.bnd(~F, _, NP.vn(~F, M.matvec(~F, rmat(~F, n, GJ.mswap(~F, a, c, r)), u)))
          swp_go(~F, n, a, c, r, u, k, hc, hr, KA.nateq(k, c), {==}, KA.nateq(k, r), {==})))), FV.vmax_nn(~F, M.matvec(~F, rmat(~F, n, GJ.mswap(~F, a, c, r)), u)))))

# swapping two rows keeps an inverse of the right halves, same norm
def swap_invb(~F: O.OField, +n: Nat, +a: M.Mat(~F), +c: Nat, +r: Nat, +hh: O.C(F), +hH: NP.InvB(~F, rmat(~F, n, a), n, hh), +hna: {GJ.nrows(~F, a) == n : Nat}, +hc: {KA.natle(1n+c, GJ.nrows(~F, a)) == True{} : Bool}, +hr: {KA.natle(1n+r, GJ.nrows(~F, a)) == True{} : Bool}, hw: GJ.All(~(i => GJ.roww(~F, rmat(~F, n, GJ.mswap(~F, a, c, r)), n, i)), n)) -> NP.InvB(~F, rmat(~F, n, GJ.mswap(~F, a, c, r)), n, hh):
  NP.invb_of_low(~F, ~rmat(~F, n, GJ.mswap(~F, a, c, r)), ~n, ~hh, ~(u => lu => sw_low(~F, n, a, c, r, hh, hH, hna, hc, hr, u, lu)), NP.invb_nn(~F, rmat(~F, n, a), n, hh, hH),
    Equal.trans(Nat, GJ.nrows(~F, rmat(~F, n, GJ.mswap(~F, a, c, r))), GJ.nrows(~F, GJ.mswap(~F, a, c, r)), n, nrows_rmat(~F, n, GJ.mswap(~F, a, c, r)), Equal.trans(Nat, GJ.nrows(~F, GJ.mswap(~F, a, c, r)), GJ.nrows(~F, a), n, Equal.sym(Nat, GJ.nrows(~F, a), GJ.nrows(~F, GJ.mswap(~F, a, c, r)), GJ.nrows_mswap(~F, a, c, r)), hna)), hw)

# The pivot search
# ----------------
# dpivot scans rows k.. of column c and keeps the first strictly largest
# |entry|: it returns a row whose |entry| bounds every candidate, or None
# only when every candidate is 0. Tracked over the full list T, scanned
# up to index i, with the rest of the scan rdrop(i, T).

def rdrop(i: Nat, xs: List<&2, List<&2, S.D>>) -> List<&2, List<&2, S.D>>:
  match i xs:
    case 0n Nil{}:
      Nil{}
    case 0n Con{r, t}:
      Con{r, t}
    case 1n+j Nil{}:
      Nil{}
    case 1n+j Con{r, t}:
      rdrop(j, t)

def rdrop0(xs: List<&2, List<&2, S.D>>) -> {rdrop(0n, xs) == xs : List<&2, List<&2, S.D>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{r, t}:
      {==}

def dnilp(xs: List<&2, List<&2, S.D>>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{r, t}:
      Empty

def dnil_con(+h: List<&2, S.D>, +t: List<&2, List<&2, S.D>>, e: {Nil{} == Con{h, t} : List<&2, List<&2, S.D>>}) -> Empty:
  %e : dnilp(_)
  Unit{}

def dhd(xs: List<&2, List<&2, S.D>>) -> List<&2, S.D>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      r

def dtl(xs: List<&2, List<&2, S.D>>) -> List<&2, List<&2, S.D>>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      t

def rdrop_hd(i: Nat, xs: List<&2, List<&2, S.D>>, +h: List<&2, S.D>, +t: List<&2, List<&2, S.D>>, e: {rdrop(i, xs) == Con{h, t} : List<&2, List<&2, S.D>>}) -> {NU.drow(xs, i) == h : List<&2, S.D>}:
  match i xs:
    case 0n Nil{}:
      FO.absurd({NU.drow(Nil{}, 0n) == h : List<&2, S.D>}, dnil_con(h, t, e))
    case 0n Con{+r2, +t2}:
      Equal.cong(List<&2, List<&2, S.D>>, List<&2, S.D>, m => dhd(m), Con{r2, t2}, Con{h, t}, e)
    case 1n+j Nil{}:
      FO.absurd({NU.drow(Nil{}, 1n+j) == h : List<&2, S.D>}, dnil_con(h, t, e))
    case 1n+j Con{+r2, +t2}:
      rdrop_hd(j, t2, h, t, e)

def rdrop_tl(i: Nat, xs: List<&2, List<&2, S.D>>, +h: List<&2, S.D>, +t: List<&2, List<&2, S.D>>, e: {rdrop(i, xs) == Con{h, t} : List<&2, List<&2, S.D>>}) -> {rdrop(1n+i, xs) == t : List<&2, List<&2, S.D>>}:
  match i xs:
    case 0n Nil{}:
      FO.absurd({Nil{} == t : List<&2, List<&2, S.D>>}, dnil_con(h, t, e))
    case 0n Con{+r2, +t2}:
      Equal.trans(List<&2, List<&2, S.D>>, rdrop(0n, t2), t2, t, rdrop0(t2), Equal.cong(List<&2, List<&2, S.D>>, List<&2, List<&2, S.D>>, m => dtl(m), Con{r2, t2}, Con{h, t}, e))
    case 1n+j Nil{}:
      FO.absurd({Nil{} == t : List<&2, List<&2, S.D>>}, dnil_con(h, t, e))
    case 1n+j Con{+r2, +t2}:
      rdrop_tl(j, t2, h, t, e)

# the comparison's meaning in F
def cm_of(~F: O.OField, +a: S.D, +b: S.D, cm: Cmp, e: {KI.dcmp(a, b) == cm : Cmp}) -> N.cmeans(F, cm, M.ofd(~F, a), M.ofd(~F, b)):
  %e : N.cmeans(F, _, M.ofd(~F, a), M.ofd(~F, b))
  KI.dcmp_sound(~F, a, b)

def ndmax_lub.go(~F: O.OField, c: Cmp, +a: S.D, +b: S.D, +t: O.C(F), ha: O.le(~F, M.ofd(~F, a), t), hb: O.le(~F, M.ofd(~F, b), t)) -> O.le(~F, M.ofd(~F, NU.dmax.go(c, a, b)), t):
  match c:
    case LT{}:
      hb
    case EQ{}:
      ha
    case GT{}:
      ha

def ndmax_lub(~F: O.OField, +a: S.D, +b: S.D, +t: O.C(F), ha: O.le(~F, M.ofd(~F, a), t), hb: O.le(~F, M.ofd(~F, b), t)) -> O.le(~F, M.ofd(~F, NU.dmax(a, b)), t):
  ndmax_lub.go(~F, KI.dcmp(a, b), a, b, t, ha, hb)

def ndmax_l.go(~F: O.OField, c: Cmp, +a: S.D, +b: S.D, e: {KI.dcmp(a, b) == c : Cmp}) -> O.le(~F, M.ofd(~F, a), M.ofd(~F, NU.dmax.go(c, a, b))):
  match c:
    case LT{}:
      FO.lt_le(~F, M.ofd(~F, a), M.ofd(~F, b), cm_of(~F, a, b, LT{}, e))
    case EQ{}:
      FO.le_refl(~F, M.ofd(~F, a))
    case GT{}:
      FO.le_refl(~F, M.ofd(~F, a))

def ndmax_l(~F: O.OField, +a: S.D, +b: S.D) -> O.le(~F, M.ofd(~F, a), M.ofd(~F, NU.dmax(a, b))):
  ndmax_l.go(~F, KI.dcmp(a, b), a, b, {==})

def ndmax_r.go(~F: O.OField, c: Cmp, +a: S.D, +b: S.D, e: {KI.dcmp(a, b) == c : Cmp}) -> O.le(~F, M.ofd(~F, b), M.ofd(~F, NU.dmax.go(c, a, b))):
  match c:
    case LT{}:
      FO.le_refl(~F, M.ofd(~F, b))
    case EQ{}:
      Inr{Equal.sym(O.C(F), M.ofd(~F, a), M.ofd(~F, b), cm_of(~F, a, b, EQ{}, e))}
    case GT{}:
      FO.lt_le(~F, M.ofd(~F, b), M.ofd(~F, a), cm_of(~F, a, b, GT{}, e))

def ndmax_r(~F: O.OField, +a: S.D, +b: S.D) -> O.le(~F, M.ofd(~F, b), M.ofd(~F, NU.dmax(a, b))):
  ndmax_r.go(~F, KI.dcmp(a, b), a, b, {==})

# |x| in F for the solver's dabs
def dabs_bnd(~F: O.OField, +x: S.D) -> M.bnd(~F, M.ofd(~F, x), M.ofd(~F, NU.dabs(x))):
  KA.kabs_bnd(~KI.dnum(), ~F, ~KI.demb(~F), x)

def cnd(b: Bool, P: Data) -> Data:
  match b:
    case True{}:
      P
    case False{}:
      Unit

# candidate j (a row at or after k) is at most m in size
def cb(~F: O.OField, +t: List<&2, List<&2, S.D>>, +c: Nat, +k: Nat, +m: O.C(F), +j: Nat) -> Data:
  cnd(KA.natle(k, j), M.bnd(~F, M.ofd(~F, NU.dget(NU.drow(t, j), c)), m))

def cnd_mono(~F: O.OField, b: Bool, +v: O.C(F), +m: O.C(F), +m2: O.C(F), +hm: O.le(~F, m, m2), h: cnd(b, M.bnd(~F, v, m))) -> cnd(b, M.bnd(~F, v, m2)):
  match b:
    case True{}:
      FM.bnd_mono(~F, v, m, m2, h, FM.sub_nonneg(~F, m, m2, hm))
    case False{}:
      Unit{}

def cbs_mono(~F: O.OField, +t: List<&2, List<&2, S.D>>, +c: Nat, +k: Nat, +m: O.C(F), +m2: O.C(F), +hm: O.le(~F, m, m2), i: Nat, h: GJ.All(~(j => cb(~F, t, c, k, m, j)), i)) -> GJ.All(~(j => cb(~F, t, c, k, m2, j)), i):
  all_map(~(j => cb(~F, t, c, k, m, j)), ~(j => cb(~F, t, c, k, m2, j)), ~(j => q => cnd_mono(~F, KA.natle(k, j), M.ofd(~F, NU.dget(NU.drow(t, j), c)), m, m2, hm, q)), i, h)

# what the scan state promises: no pivot yet and bx <= 0, or a scanned
# candidate r whose size is at least bx
def acc(~F: O.OField, +t: List<&2, List<&2, S.D>>, +c: Nat, +k: Nat, +i: Nat, best: Maybe<&2, Nat>, +bx: S.D) -> Data:
  match best:
    case None{}:
      O.le(~F, M.ofd(~F, bx), O.zero(F))
    case Some{r}:
      M.Both({KA.natle(k, r) == True{} : Bool}, M.Both({KA.natle(1n+r, i) == True{} : Bool}, O.le(~F, M.ofd(~F, bx), M.ofd(~F, NU.dabs(NU.dget(NU.drow(t, r), c))))))

def acc_lo(~F: O.OField, +t: List<&2, List<&2, S.D>>, +c: Nat, +k: Nat, +i: Nat, best: Maybe<&2, Nat>, +bx: S.D, +bx2: S.D, h: acc(~F, t, c, k, i, best, bx), +hle: O.le(~F, M.ofd(~F, bx2), M.ofd(~F, bx))) -> acc(~F, t, c, k, 1n+i, best, bx2):
  match best:
    case None{}:
      DM.le_trans(~F, M.ofd(~F, bx2), M.ofd(~F, bx), O.zero(F), hle, h)
    case Some{+r}:
      (h1, hr) = h
      (h2, h3) = hr
      (h1, (GJ.le_succ(1n+r, i, h2), DM.le_trans(~F, M.ofd(~F, bx2), M.ofd(~F, bx), M.ofd(~F, NU.dabs(NU.dget(NU.drow(t, r), c))), hle, h3)))

# the scanned candidates, extended by row i = h
def pre_ext(~F: O.OField, +t: List<&2, List<&2, S.D>>, +c: Nat, +k: Nat, +i: Nat, +h: List<&2, S.D>, +bx: S.D, +e1: {KA.natle(k, i) == True{} : Bool}, +hh: {NU.drow(t, i) == h : List<&2, S.D>}, hp: GJ.All(~(j => cb(~F, t, c, k, M.ofd(~F, bx), j)), i)) -> GJ.All(~(j => cb(~F, t, c, k, M.ofd(~F, NU.dmax(bx, NU.dabs(NU.dget(h, c)))), j)), 1n+i):
  (cbs_mono(~F, t, c, k, M.ofd(~F, bx), M.ofd(~F, NU.dmax(bx, NU.dabs(NU.dget(h, c)))), ndmax_l(~F, bx, NU.dabs(NU.dget(h, c))), i, hp),
    (%Equal.sym(Bool, KA.natle(k, i), True{}, e1) : cnd(_, M.bnd(~F, M.ofd(~F, NU.dget(NU.drow(t, i), c)), M.ofd(~F, NU.dmax(bx, NU.dabs(NU.dget(h, c))))))
      (%Equal.sym(List<&2, S.D>, NU.drow(t, i), h, hh) : M.bnd(~F, M.ofd(~F, NU.dget(_, c)), M.ofd(~F, NU.dmax(bx, NU.dabs(NU.dget(h, c)))))
        FM.bnd_mono(~F, M.ofd(~F, NU.dget(h, c)), M.ofd(~F, NU.dabs(NU.dget(h, c))), M.ofd(~F, NU.dmax(bx, NU.dabs(NU.dget(h, c)))), dabs_bnd(~F, NU.dget(h, c)), FM.sub_nonneg(~F, M.ofd(~F, NU.dabs(NU.dget(h, c))), M.ofd(~F, NU.dmax(bx, NU.dabs(NU.dget(h, c)))), ndmax_r(~F, bx, NU.dabs(NU.dget(h, c))))))))

# one row of the scan: the scanned candidates
def dp_pre(~F: O.OField, +t: List<&2, List<&2, S.D>>, +c: Nat, +k: Nat, +i: Nat, +h: List<&2, S.D>, +bx: S.D, b: Bool, +e1: {KA.natle(k, i) == b : Bool}, +hh: {NU.drow(t, i) == h : List<&2, S.D>}, +hp: GJ.All(~(j => cb(~F, t, c, k, M.ofd(~F, bx), j)), i)) -> GJ.All(~(j => cb(~F, t, c, k, M.ofd(~F, NU.dpivot.bx(b, bx, NU.dabs(NU.dget(h, c)))), j)), 1n+i):
  match b:
    case False{}:
      (hp, (%Equal.sym(Bool, KA.natle(k, i), False{}, e1) : cnd(_, M.bnd(~F, M.ofd(~F, NU.dget(NU.drow(t, i), c)), M.ofd(~F, bx))) Unit{}))
    case True{}:
      pre_ext(~F, t, c, k, i, h, bx, e1, hh, hp)

# one row of the scan: the state's promise
def dp_acc(~F: O.OField, +t: List<&2, List<&2, S.D>>, +c: Nat, +k: Nat, +i: Nat, +h: List<&2, S.D>, best: Maybe<&2, Nat>, +bx: S.D, b: Bool, +e1: {KA.natle(k, i) == b : Bool}, cm: Cmp, +e2: {KI.dcmp(NU.dabs(NU.dget(h, c)), bx) == cm : Cmp}, +hh: {NU.drow(t, i) == h : List<&2, S.D>}, +ha: acc(~F, t, c, k, i, best, bx)) -> acc(~F, t, c, k, 1n+i, NU.dpivot.best(b, cm, i, best), NU.dpivot.bx(b, bx, NU.dabs(NU.dget(h, c)))):
  match b:
    case False{}:
      acc_lo(~F, t, c, k, i, best, bx, bx, ha, FO.le_refl(~F, M.ofd(~F, bx)))
    case True{}:
      match cm:
        case GT{}:
          (e1, (GJ.le_refl(1n+i), (%Equal.sym(List<&2, S.D>, NU.drow(t, i), h, hh) : O.le(~F, M.ofd(~F, NU.dmax(bx, NU.dabs(NU.dget(h, c)))), M.ofd(~F, NU.dabs(NU.dget(_, c))))
            ndmax_lub(~F, bx, NU.dabs(NU.dget(h, c)), M.ofd(~F, NU.dabs(NU.dget(h, c))), FO.lt_le(~F, M.ofd(~F, bx), M.ofd(~F, NU.dabs(NU.dget(h, c))), cm_of(~F, NU.dabs(NU.dget(h, c)), bx, GT{}, e2)), FO.le_refl(~F, M.ofd(~F, NU.dabs(NU.dget(h, c))))))))
        case EQ{}:
          acc_lo(~F, t, c, k, i, best, bx, NU.dmax(bx, NU.dabs(NU.dget(h, c))), ha, ndmax_lub(~F, bx, NU.dabs(NU.dget(h, c)), M.ofd(~F, bx), FO.le_refl(~F, M.ofd(~F, bx)), Inr{cm_of(~F, NU.dabs(NU.dget(h, c)), bx, EQ{}, e2)}))
        case LT{}:
          acc_lo(~F, t, c, k, i, best, bx, NU.dmax(bx, NU.dabs(NU.dget(h, c))), ha, ndmax_lub(~F, bx, NU.dabs(NU.dget(h, c)), M.ofd(~F, bx), FO.le_refl(~F, M.ofd(~F, bx)), FO.lt_le(~F, M.ofd(~F, NU.dabs(NU.dget(h, c))), M.ofd(~F, bx), cm_of(~F, NU.dabs(NU.dget(h, c)), bx, LT{}, e2))))

# the scan's result, for rows k.. of nn rows
def pfin(~F: O.OField, +t: List<&2, List<&2, S.D>>, +c: Nat, +k: Nat, +nn: Nat, res: Maybe<&2, Nat>) -> Data:
  match res:
    case None{}:
      GJ.All(~(j => cb(~F, t, c, k, O.zero(F), j)), nn)
    case Some{r}:
      M.Both({KA.natle(k, r) == True{} : Bool}, M.Both({KA.natle(1n+r, nn) == True{} : Bool}, GJ.All(~(j => cb(~F, t, c, k, M.ofd(~F, NU.dabs(NU.dget(NU.drow(t, r), c))), j)), nn)))

def pfin_end(~F: O.OField, +t: List<&2, List<&2, S.D>>, +c: Nat, +k: Nat, +i: Nat, best: Maybe<&2, Nat>, +bx: S.D, hp: GJ.All(~(j => cb(~F, t, c, k, M.ofd(~F, bx), j)), i), ha: acc(~F, t, c, k, i, best, bx)) -> pfin(~F, t, c, k, i, best):
  match best:
    case None{}:
      cbs_mono(~F, t, c, k, M.ofd(~F, bx), O.zero(F), ha, i, hp)
    case Some{+r}:
      (h1, hr) = ha
      (h2, h3) = hr
      (h1, (h2, cbs_mono(~F, t, c, k, M.ofd(~F, bx), M.ofd(~F, NU.dabs(NU.dget(NU.drow(t, r), c))), h3, i, hp)))

def dp_ok(~F: O.OField, rows: List<&2, List<&2, S.D>>, +t: List<&2, List<&2, S.D>>, +c: Nat, +k: Nat, +i: Nat, +best: Maybe<&2, Nat>, +bx: S.D, +hr: {rdrop(i, t) == rows : List<&2, List<&2, S.D>>}, +hn: {Nat.add(GJ.nrows(~F, M.ofdm(~F, rows)), i) == GJ.nrows(~F, M.ofdm(~F, t)) : Nat}, +hp: GJ.All(~(j => cb(~F, t, c, k, M.ofd(~F, bx), j)), i), +ha: acc(~F, t, c, k, i, best, bx)) -> pfin(~F, t, c, k, GJ.nrows(~F, M.ofdm(~F, t)), NU.dpivot(rows, c, k, i, best, bx)):
  match rows:
    case Nil{}:
      %hn : pfin(~F, t, c, k, _, best)
      pfin_end(~F, t, c, k, i, best, bx, hp, ha)
    case Con{+h, +rt}:
      dp_ok(~F, rt, t, c, k, 1n+i, NU.dpivot.best(KA.natle(k, i), KI.dcmp(NU.dabs(NU.dget(h, c)), bx), i, best), NU.dpivot.bx(KA.natle(k, i), bx, NU.dabs(NU.dget(h, c))), rdrop_tl(i, t, h, rt, hr),
        Equal.trans(Nat, Nat.add(GJ.nrows(~F, M.ofdm(~F, rt)), 1n+i), 1n+Nat.add(GJ.nrows(~F, M.ofdm(~F, rt)), i), GJ.nrows(~F, M.ofdm(~F, t)), Equal.sym(Nat, 1n+Nat.add(GJ.nrows(~F, M.ofdm(~F, rt)), i), Nat.add(GJ.nrows(~F, M.ofdm(~F, rt)), 1n+i), LN.add_succ(GJ.nrows(~F, M.ofdm(~F, rt)), i)), hn),
        dp_pre(~F, t, c, k, i, h, bx, KA.natle(k, i), {==}, rdrop_hd(i, t, h, rt, hr), hp),
        dp_acc(~F, t, c, k, i, h, best, bx, KA.natle(k, i), {==}, KI.dcmp(NU.dabs(NU.dget(h, c)), bx), {==}, rdrop_hd(i, t, h, rt, hr), ha))

# dpivot from the top, as dgj calls it
def pivot_ok(~F: O.OField, +t: List<&2, List<&2, S.D>>, +c: Nat) -> pfin(~F, t, c, c, GJ.nrows(~F, M.ofdm(~F, t)), NU.dpivot(t, c, c, 0n, None{}, NU.dzero())):
  dp_ok(~F, t, t, c, c, 0n, None{}, NU.dzero(), rdrop0(t), Equal.sym(Nat, GJ.nrows(~F, M.ofdm(~F, t)), Nat.add(GJ.nrows(~F, M.ofdm(~F, t)), 0n), LN.add_zero(GJ.nrows(~F, M.ofdm(~F, t)))), Unit{},
    (%DM.ofd_zero(~F) : O.le(~F, _, O.zero(F))
      FO.le_refl(~F, O.zero(F))))

# The pivot bound
# ---------------
# If every candidate in column c were small, the vector
# v = (-L_0c, ..., -L_(c-1)c, 1, 0, ...) would nearly be in the kernel of
# the rows' left parts L, since the finished columns are nearly unit; but
# R J v = L v - (L - R J) v and J, R have bounded inverses, so |v| >= 1
# forces some candidate to be large.

def vall_app(~F: O.OField, p: M.Vec(~F), +q: M.Vec(~F), +t: O.C(F), hp: M.vbnd.all(~F, p, t), +hq: M.vbnd.all(~F, q, t)) -> M.vbnd.all(~F, GJ.vapp(~F, p, q), t):
  match p:
    case Nil{}:
      hq
    case Con{a, xs}:
      (h1, h2) = hp
      (h1, vall_app(~F, xs, q, t, h2, hq))

def vall_take(~F: O.OField, k: Nat, v: M.Vec(~F), +t: O.C(F), h: M.vbnd.all(~F, v, t)) -> M.vbnd.all(~F, GJ.vtake(~F, k, v), t):
  match k v:
    case 0n v:
      Unit{}
    case 1n+j Nil{}:
      Unit{}
    case 1n+j Con{a, xs}:
      (h1, h2) = h
      (h1, vall_take(~F, j, xs, t, h2))

def lt_take(~F: O.OField, k: Nat, y: M.Vec(~F), i: Nat, h: {KA.natle(1n+i, M.len(~F, GJ.vtake(~F, k, y))) == True{} : Bool}) -> {KA.natle(1n+i, k) == True{} : Bool}:
  match k y i:
    case 0n y i:
      h
    case 1n+j Nil{} i:
      FO.absurd({KA.natle(1n+i, 1n+j) == True{} : Bool}, KA.ft(h))
    case 1n+j Con{a, t} 0n:
      {==}
    case 1n+j Con{a, t} 1n+i2:
      lt_take(~F, j, t, i2, h)

def dot_app_k(~F: O.OField, +r: M.Vec(~F), +p: M.Vec(~F), +q: M.Vec(~F), +k: Nat, hk: {M.len(~F, p) == k : Nat}) -> {O.add(F, M.dot(~F, GJ.vtake(~F, k, r), p), M.dot(~F, GJ.vdrop(~F, k, r), q)) == M.dot(~F, r, GJ.vapp(~F, p, q)) : O.C(F)}:
  %hk : {O.add(F, M.dot(~F, GJ.vtake(~F, _, r), p), M.dot(~F, GJ.vdrop(~F, _, r), q)) == M.dot(~F, r, GJ.vapp(~F, p, q)) : O.C(F)}
  GJ.dot_app(~F, r, p, q)

def look0_vhd(~F: O.OField, v: M.Vec(~F)) -> {O.lookup(~F, v, 0n) == GJ.vhd(~F, v) : O.C(F)}:
  match v:
    case Nil{}:
      {==}
    case Con{a, t}:
      {==}

def rinv_mall(~F: O.OField, +n: Nat, +jm: M.Mat(~F), s: M.Mat(~F), +i: Nat, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), h: rinv(~F, n, jm, s, i, c, gg, dd, ph)) -> mall(~F, s, gg):
  match s:
    case Nil{}:
      Unit{}
    case Con{x, t}:
      (h1, h2) = h
      (ri_e(~F, n, jm, x, i, c, gg, dd, ph, h1), rinv_mall(~F, n, jm, t, 1n+i, c, gg, dd, ph, h2))

# row k's invariant in an F matrix
def ri_atf(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +s: M.Mat(~F), +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +k: Nat, +h: rinv(~F, n, jm, s, 0n, c, gg, dd, ph), +hk: {KA.natle(1n+k, GJ.nrows(~F, s)) == True{} : Bool}) -> rowinv(~F, n, jm, DV.mrow(~F, s, k), k, c, gg, dd, ph):
  %Equal.sym(Nat, k, Nat.add(k, 0n), LN.add_zero(k)) : rowinv(~F, n, jm, DV.mrow(~F, s, k), _, c, gg, dd, ph)
  ri_at(~F, n, jm, s, 0n, c, gg, dd, ph, k, h, hk)

# column c above row c, and the near-kernel vector
def pcol(~F: O.OField, +s: M.Mat(~F), +c: Nat) -> M.Vec(~F):
  GJ.vtake(~F, c, GJ.mcol(~F, s, c))

def vk(~F: O.OField, +s: M.Mat(~F), +c: Nat, +rest: Nat) -> M.Vec(~F):
  GJ.vapp(~F, M.vneg(~F, pcol(~F, s, c)), Con{O.one(F), GJ.zeros(~F, rest)})

def len_pcol(~F: O.OField, +s: M.Mat(~F), +c: Nat, +hc: {KA.natle(c, GJ.nrows(~F, s)) == True{} : Bool}) -> {M.len(~F, pcol(~F, s, c)) == c : Nat}:
  Equal.sym(Nat, c, M.len(~F, pcol(~F, s, c)), GJ.len_vtake(~F, c, GJ.mcol(~F, s, c), (%GJ.len_mcol(~F, s, c) : {KA.natle(c, _) == True{} : Bool} hc)))

def len_pv(~F: O.OField, +s: M.Mat(~F), +c: Nat, +hc: {KA.natle(c, GJ.nrows(~F, s)) == True{} : Bool}) -> {M.len(~F, M.vneg(~F, pcol(~F, s, c))) == c : Nat}:
  Equal.trans(Nat, M.len(~F, M.vneg(~F, pcol(~F, s, c))), M.len(~F, pcol(~F, s, c)), c, Equal.sym(Nat, M.len(~F, pcol(~F, s, c)), M.len(~F, M.vneg(~F, pcol(~F, s, c))), GJ.len_vneg(~F, pcol(~F, s, c))), len_pcol(~F, s, c, hc))

def len_vk(~F: O.OField, +s: M.Mat(~F), +c: Nat, +rest: Nat, +hc: {KA.natle(c, GJ.nrows(~F, s)) == True{} : Bool}) -> {M.len(~F, vk(~F, s, c, rest)) == Nat.add(c, 1n+rest) : Nat}:
  %GJ.len_vapp(~F, M.vneg(~F, pcol(~F, s, c)), Con{O.one(F), GJ.zeros(~F, rest)}) : {_ == Nat.add(c, 1n+rest) : Nat}
  %Equal.sym(Nat, M.len(~F, M.vneg(~F, pcol(~F, s, c))), c, len_pv(~F, s, c, hc)) : {Nat.add(_, M.len(~F, Con{O.one(F), GJ.zeros(~F, rest)})) == Nat.add(c, 1n+rest) : Nat}
  %GJ.len_zeros(~F, rest) : {Nat.add(c, 1n+_) == Nat.add(c, 1n+rest) : Nat}
  {==}

def look_vk(~F: O.OField, +s: M.Mat(~F), +c: Nat, +rest: Nat, +hc: {KA.natle(c, GJ.nrows(~F, s)) == True{} : Bool}) -> {O.lookup(~F, vk(~F, s, c, rest), c) == O.one(F) : O.C(F)}:
  %len_pv(~F, s, c, hc) : {O.lookup(~F, vk(~F, s, c, rest), _) == O.one(F) : O.C(F)}
  Equal.sym(O.C(F), O.one(F), O.lookup(~F, vk(~F, s, c, rest), M.len(~F, M.vneg(~F, pcol(~F, s, c)))), GJ.look_app_len(~F, M.vneg(~F, pcol(~F, s, c)), Con{O.one(F), GJ.zeros(~F, rest)}))

# 1 <= |v| <= 1 + G
def one_le_vk(~F: O.OField, +s: M.Mat(~F), +c: Nat, +rest: Nat, +hc: {KA.natle(c, GJ.nrows(~F, s)) == True{} : Bool}) -> O.le(~F, O.one(F), NP.vn(~F, vk(~F, s, c, rest))):
  NP.bnd_lo(~F, O.one(F), NP.vn(~F, vk(~F, s, c, rest)), (%look_vk(~F, s, c, rest, hc) : M.bnd(~F, _, NP.vn(~F, vk(~F, s, c, rest)))
    look_bnd(~F, vk(~F, s, c, rest), c, NP.vn(~F, vk(~F, s, c, rest)), FV.vmax_all(~F, vk(~F, s, c, rest)), FV.vmax_nn(~F, vk(~F, s, c, rest)))))

def vk_le(~F: O.OField, +s: M.Mat(~F), +c: Nat, +rest: Nat, +gg: O.C(F), hs: mall(~F, s, gg), +hgg: O.le(~F, O.zero(F), gg)) -> O.le(~F, NP.vn(~F, vk(~F, s, c, rest)), O.add(F, O.one(F), gg)):
  FV.vmax_lub(~F, vk(~F, s, c, rest), O.add(F, O.one(F), gg), vall_app(~F, M.vneg(~F, pcol(~F, s, c)), Con{O.one(F), GJ.zeros(~F, rest)}, O.add(F, O.one(F), gg),
      FM.vall_mono(~F, M.vneg(~F, pcol(~F, s, c)), gg, O.add(F, O.one(F), gg), FM.vall_neg(~F, pcol(~F, s, c), gg, vall_take(~F, c, GJ.mcol(~F, s, c), gg, vall_mcol(~F, s, c, gg, hs, hgg))), FM.sub_nonneg(~F, gg, O.add(F, O.one(F), gg), le_addl(~F, O.one(F), gg, NP.one_nn(~F)))),
      (FM.bnd_mono(~F, O.one(F), O.one(F), O.add(F, O.one(F), gg), FV.bnd_self(~F, O.one(F), NP.one_nn(~F)), FM.sub_nonneg(~F, O.one(F), O.add(F, O.one(F), gg), le_addr(~F, O.one(F), gg, hgg))),
        FM.vall_mono(~F, GJ.zeros(~F, rest), O.zero(F), O.add(F, O.one(F), gg), NP.vall_zeros(~F, rest), FM.sub_nonneg(~F, O.zero(F), O.add(F, O.one(F), gg), FO.nonneg_add(~F, O.one(F), gg, NP.one_nn(~F), hgg))))),
    FO.nonneg_add(~F, O.one(F), gg, NP.one_nn(~F), hgg))

def le_add_r(a: Nat, +b: Nat) -> {KA.natle(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+j:
      le_add_r(j, b)

# x . v = -(x_<c . p) + x_c
def dot_x_vk(~F: O.OField, +x: M.Vec(~F), +s: M.Mat(~F), +c: Nat, +rest: Nat, +hc: {KA.natle(c, GJ.nrows(~F, s)) == True{} : Bool}) -> {M.dot(~F, x, vk(~F, s, c, rest)) == O.add(F, O.neg(F, M.dot(~F, GJ.vtake(~F, c, x), pcol(~F, s, c))), O.add(F, O.mul(F, O.lookup(~F, x, c), O.one(F)), O.zero(F))) : O.C(F)}:
  %dot_app_k(~F, x, M.vneg(~F, pcol(~F, s, c)), Con{O.one(F), GJ.zeros(~F, rest)}, c, len_pv(~F, s, c, hc)) : {_ == O.add(F, O.neg(F, M.dot(~F, GJ.vtake(~F, c, x), pcol(~F, s, c))), O.add(F, O.mul(F, O.lookup(~F, x, c), O.one(F)), O.zero(F))) : O.C(F)}
  %GJ.dot_vneg_r(~F, GJ.vtake(~F, c, x), pcol(~F, s, c)) : {O.add(F, _, M.dot(~F, GJ.vdrop(~F, c, x), Con{O.one(F), GJ.zeros(~F, rest)})) == O.add(F, O.neg(F, M.dot(~F, GJ.vtake(~F, c, x), pcol(~F, s, c))), O.add(F, O.mul(F, O.lookup(~F, x, c), O.one(F)), O.zero(F))) : O.C(F)}
  %GJ.dot_cons(~F, GJ.vdrop(~F, c, x), O.one(F), GJ.zeros(~F, rest)) : {O.add(F, O.neg(F, M.dot(~F, GJ.vtake(~F, c, x), pcol(~F, s, c))), _) == O.add(F, O.neg(F, M.dot(~F, GJ.vtake(~F, c, x), pcol(~F, s, c))), O.add(F, O.mul(F, O.lookup(~F, x, c), O.one(F)), O.zero(F))) : O.C(F)}
  %GJ.dot_zeros_r(~F, GJ.vtl(~F, GJ.vdrop(~F, c, x)), rest) : {O.add(F, O.neg(F, M.dot(~F, GJ.vtake(~F, c, x), pcol(~F, s, c))), O.add(F, O.mul(F, GJ.vhd(~F, GJ.vdrop(~F, c, x)), O.one(F)), _)) == O.add(F, O.neg(F, M.dot(~F, GJ.vtake(~F, c, x), pcol(~F, s, c))), O.add(F, O.mul(F, O.lookup(~F, x, c), O.one(F)), O.zero(F))) : O.C(F)}
  %look0_vhd(~F, GJ.vdrop(~F, c, x)) : {O.add(F, O.neg(F, M.dot(~F, GJ.vtake(~F, c, x), pcol(~F, s, c))), O.add(F, O.mul(F, _, O.one(F)), O.zero(F))) == O.add(F, O.neg(F, M.dot(~F, GJ.vtake(~F, c, x), pcol(~F, s, c))), O.add(F, O.mul(F, O.lookup(~F, x, c), O.one(F)), O.zero(F))) : O.C(F)}
  %GJ.look_drop(~F, c, x) : {O.add(F, O.neg(F, M.dot(~F, GJ.vtake(~F, c, x), pcol(~F, s, c))), O.add(F, O.mul(F, _, O.one(F)), O.zero(F))) == O.add(F, O.neg(F, M.dot(~F, GJ.vtake(~F, c, x), pcol(~F, s, c))), O.add(F, O.mul(F, O.lookup(~F, x, c), O.one(F)), O.zero(F))) : O.C(F)}
  {==}

# x_<c . p = (x_<c - e_i) . p + p_i
def dsplit(~F: O.OField, +x: M.Vec(~F), +c: Nat, +i: Nat, +p: M.Vec(~F), +hl: {KA.natle(M.len(~F, p), c) == True{} : Bool}) -> {M.dot(~F, GJ.vtake(~F, c, x), p) == O.add(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, x), M.vneg(~F, GJ.unit(~F, c, i))), p), O.lookup(~F, p, i)) : O.C(F)}:
  %FM.dot_vadd(~F, GJ.vtake(~F, c, x), M.vneg(~F, GJ.unit(~F, c, i)), p) : {M.dot(~F, GJ.vtake(~F, c, x), p) == O.add(F, _, O.lookup(~F, p, i)) : O.C(F)}
  %FM.dot_vneg(~F, GJ.unit(~F, c, i), p) : {M.dot(~F, GJ.vtake(~F, c, x), p) == O.add(F, O.add(F, M.dot(~F, GJ.vtake(~F, c, x), p), _), O.lookup(~F, p, i)) : O.C(F)}
  %GJ.dot_unit(~F, c, i, p, hl) : {M.dot(~F, GJ.vtake(~F, c, x), p) == O.add(F, O.add(F, M.dot(~F, GJ.vtake(~F, c, x), p), O.neg(F, _)), O.lookup(~F, p, i)) : O.C(F)}
  FR.fring_eq(~F, [M.dot(~F, GJ.vtake(~F, c, x), p), O.lookup(~F, p, i)], E.ZVar{0n}, E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZNeg{E.ZVar{1n}}}, E.ZVar{1n}}, {==})

# p_i: row i's entry c above the diagonal, 0 below
def pc_lo(~F: O.OField, +s: M.Mat(~F), +c: Nat, +i: Nat, +h: {KA.natle(1n+i, c) == True{} : Bool}) -> {O.lookup(~F, pcol(~F, s, c), i) == O.lookup(~F, DV.mrow(~F, s, i), c) : O.C(F)}:
  Equal.trans(O.C(F), O.lookup(~F, pcol(~F, s, c), i), O.lookup(~F, GJ.mcol(~F, s, c), i), O.lookup(~F, DV.mrow(~F, s, i), c), Equal.sym(O.C(F), O.lookup(~F, GJ.mcol(~F, s, c), i), O.lookup(~F, pcol(~F, s, c), i), GJ.look_take_lo(~F, c, GJ.mcol(~F, s, c), i, h)), Equal.sym(O.C(F), O.lookup(~F, DV.mrow(~F, s, i), c), O.lookup(~F, GJ.mcol(~F, s, c), i), GJ.look_mcol(~F, s, c, i)))

def pc_hi(~F: O.OField, +s: M.Mat(~F), +c: Nat, +i: Nat, +h: {KA.natle(c, i) == True{} : Bool}) -> {O.lookup(~F, pcol(~F, s, c), i) == O.zero(F) : O.C(F)}:
  Equal.sym(O.C(F), O.zero(F), O.lookup(~F, pcol(~F, s, c), i), GJ.look_take_hi(~F, c, GJ.mcol(~F, s, c), i, h))

# entry j of x_<c - e_i is x_j - [i = j]
def eq_dd(~F: O.OField, +x: M.Vec(~F), +c: Nat, +i: Nat, +j: Nat, +hj: {KA.natle(1n+j, c) == True{} : Bool}) -> {O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, KA.nateq(i, j))) == O.lookup(~F, M.vadd(~F, GJ.vtake(~F, c, x), M.vneg(~F, GJ.unit(~F, c, i))), j) : O.C(F)}:
  %GJ.look_vadd(~F, GJ.vtake(~F, c, x), M.vneg(~F, GJ.unit(~F, c, i)), j) : {O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, KA.nateq(i, j))) == _ : O.C(F)}
  %GJ.look_vneg(~F, GJ.unit(~F, c, i), j) : {O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, KA.nateq(i, j))) == O.add(F, O.lookup(~F, GJ.vtake(~F, c, x), j), _) : O.C(F)}
  %GJ.look_take_lo(~F, c, x, j, hj) : {O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, KA.nateq(i, j))) == O.add(F, _, O.neg(F, O.lookup(~F, GJ.unit(~F, c, i), j))) : O.C(F)}
  %GJ.look_unit(~F, c, i, j, hj) : {O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, KA.nateq(i, j))) == O.add(F, O.lookup(~F, x, j), O.neg(F, _)) : O.C(F)}
  %GJ.nateq_sym(j, i) : {O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, _)) == O.add(F, O.lookup(~F, x, j), O.neg(F, GJ.dl(~F, KA.nateq(j, i)))) : O.C(F)}
  FR.fring_eq(~F, [O.lookup(~F, x, j), GJ.dl(~F, KA.nateq(j, i))], E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZAdd{E.ZVar{0n}, E.ZNeg{E.ZVar{1n}}}, {==})

def vall_dd(~F: O.OField, +x: M.Vec(~F), +c: Nat, +i: Nat, +ph: O.C(F), +hf: fin(~F, x, i, c, ph), +hcx: {KA.natle(c, M.len(~F, x)) == True{} : Bool}) -> M.vbnd.all(~F, M.vadd(~F, GJ.vtake(~F, c, x), M.vneg(~F, GJ.unit(~F, c, i))), ph):
  vall_lt(~F, ~M.vadd(~F, GJ.vtake(~F, c, x), M.vneg(~F, GJ.unit(~F, c, i))), ~ph, ~(j => hj =>
    KB.bnd_val(~F, O.sub(~F, O.lookup(~F, x, j), GJ.dl(~F, KA.nateq(i, j))), O.lookup(~F, M.vadd(~F, GJ.vtake(~F, c, x), M.vneg(~F, GJ.unit(~F, c, i))), j), ph,
      eq_dd(~F, x, c, i, j, (%GJ.len_vadd(~F, GJ.vtake(~F, c, x), M.vneg(~F, GJ.unit(~F, c, i)), c, Equal.sym(Nat, c, M.len(~F, GJ.vtake(~F, c, x)), GJ.len_vtake(~F, c, x, hcx)), Equal.trans(Nat, M.len(~F, M.vneg(~F, GJ.unit(~F, c, i))), M.len(~F, GJ.unit(~F, c, i)), c, Equal.sym(Nat, M.len(~F, GJ.unit(~F, c, i)), M.len(~F, M.vneg(~F, GJ.unit(~F, c, i))), GJ.len_vneg(~F, GJ.unit(~F, c, i))), Equal.sym(Nat, c, M.len(~F, GJ.unit(~F, c, i)), GJ.len_unit(~F, c, i)))) : {KA.natle(1n+j, _) == True{} : Bool} hj)),
      GJ.all_at(~(q => M.bnd(~F, O.sub(~F, O.lookup(~F, x, q), GJ.dl(~F, KA.nateq(i, q))), ph)), c, hf, j, (%GJ.len_vadd(~F, GJ.vtake(~F, c, x), M.vneg(~F, GJ.unit(~F, c, i)), c, Equal.sym(Nat, c, M.len(~F, GJ.vtake(~F, c, x)), GJ.len_vtake(~F, c, x, hcx)), Equal.trans(Nat, M.len(~F, M.vneg(~F, GJ.unit(~F, c, i))), M.len(~F, GJ.unit(~F, c, i)), c, Equal.sym(Nat, M.len(~F, GJ.unit(~F, c, i)), M.len(~F, M.vneg(~F, GJ.unit(~F, c, i))), GJ.len_vneg(~F, GJ.unit(~F, c, i))), Equal.sym(Nat, c, M.len(~F, GJ.unit(~F, c, i)), GJ.len_unit(~F, c, i)))) : {KA.natle(1n+j, _) == True{} : Bool} hj)))))

# |(x_<c - e_i) . p| <= c phi G
def dd_bnd(~F: O.OField, +x: M.Vec(~F), +c: Nat, +i: Nat, +ph: O.C(F), +gg: O.C(F), +p: M.Vec(~F), +hf: fin(~F, x, i, c, ph), +hcx: {KA.natle(c, M.len(~F, x)) == True{} : Bool}, +hp: M.vbnd.all(~F, p, gg), +lp: {M.len(~F, p) == c : Nat}, +hgg: O.le(~F, O.zero(F), gg), +hph: O.le(~F, O.zero(F), ph)) -> M.bnd(~F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, x), M.vneg(~F, GJ.unit(~F, c, i))), p), O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg)):
  FM.bnd_mono(~F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, x), M.vneg(~F, GJ.unit(~F, c, i))), p), O.mul(F, NP.rowabs(~F, M.vadd(~F, GJ.vtake(~F, c, x), M.vneg(~F, GJ.unit(~F, c, i))), c), gg), O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg),
    (%lp : M.bnd(~F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, x), M.vneg(~F, GJ.unit(~F, c, i))), p), O.mul(F, NP.rowabs(~F, M.vadd(~F, GJ.vtake(~F, c, x), M.vneg(~F, GJ.unit(~F, c, i))), _), gg))
      NP.dot_le(~F, M.vadd(~F, GJ.vtake(~F, c, x), M.vneg(~F, GJ.unit(~F, c, i))), p, gg, hp, hgg)),
    FM.sub_nonneg(~F, O.mul(F, NP.rowabs(~F, M.vadd(~F, GJ.vtake(~F, c, x), M.vneg(~F, GJ.unit(~F, c, i))), c), gg), O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), FV.mul_le_r(~F, NP.rowabs(~F, M.vadd(~F, GJ.vtake(~F, c, x), M.vneg(~F, GJ.unit(~F, c, i))), c), O.mul(F, FR.ofn(~F, c), ph), gg, hgg, rowabs_le(~F, M.vadd(~F, GJ.vtake(~F, c, x), M.vneg(~F, GJ.unit(~F, c, i))), c, ph, vall_dd(~F, x, c, i, ph, hf, hcx), hph))))


def hcn(+c: Nat, +rest: Nat, +n: Nat, +hrest: {Nat.add(c, 1n+rest) == n : Nat}) -> {KA.natle(c, n) == True{} : Bool}:
  %hrest : {KA.natle(c, _) == True{} : Bool}
  le_add_r(c, 1n+rest)

def hcs(~F: O.OField, +s: M.Mat(~F), +c: Nat, +rest: Nat, +n: Nat, +hrest: {Nat.add(c, 1n+rest) == n : Nat}, +hns: {GJ.nrows(~F, s) == n : Nat}) -> {KA.natle(c, GJ.nrows(~F, s)) == True{} : Bool}:
  %Equal.sym(Nat, GJ.nrows(~F, s), n, hns) : {KA.natle(c, _) == True{} : Bool}
  hcn(c, rest, n, hrest)

def his(~F: O.OField, +s: M.Mat(~F), +n: Nat, +i: Nat, +hns: {GJ.nrows(~F, s) == n : Nat}, +hi: {KA.natle(1n+i, n) == True{} : Bool}) -> {KA.natle(1n+i, GJ.nrows(~F, s)) == True{} : Bool}:
  %Equal.sym(Nat, GJ.nrows(~F, s), n, hns) : {KA.natle(1n+i, _) == True{} : Bool}
  hi

def lpc_le(~F: O.OField, +s: M.Mat(~F), +c: Nat, +hc: {KA.natle(c, GJ.nrows(~F, s)) == True{} : Bool}) -> {KA.natle(M.len(~F, pcol(~F, s, c)), c) == True{} : Bool}:
  %Equal.sym(Nat, M.len(~F, pcol(~F, s, c)), c, len_pcol(~F, s, c, hc)) : {KA.natle(_, c) == True{} : Bool}
  GJ.le_refl(c)
# row i of the left parts against v: |x_i . v| <= c phi G + m
def xv_bnd.go(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +s: M.Mat(~F), +c: Nat, +rest: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +m: O.C(F), +h: rinv(~F, n, jm, s, 0n, c, gg, dd, ph), +hns: {GJ.nrows(~F, s) == n : Nat}, +hrest: {Nat.add(c, 1n+rest) == n : Nat}, +hm: GJ.All(~(j => cnd(KA.natle(c, j), M.bnd(~F, O.lookup(~F, DV.mrow(~F, s, j), c), m))), n), +hm0: O.le(~F, O.zero(F), m), +hgg: O.le(~F, O.zero(F), gg), +hdd: O.le(~F, O.zero(F), dd), +hph: O.le(~F, O.zero(F), ph), +i: Nat, +hi: {KA.natle(1n+i, n) == True{} : Bool}, b: Bool, +e: {KA.natle(1n+i, c) == b : Bool}) -> M.bnd(~F, M.dot(~F, DV.mrow(~F, s, i), vk(~F, s, c, rest)), O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m)):
  match b:
    case True{}:
      KB.bnd_val(~F, O.neg(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), M.vneg(~F, GJ.unit(~F, c, i))), pcol(~F, s, c))), M.dot(~F, DV.mrow(~F, s, i), vk(~F, s, c, rest)), O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m),
        (%Equal.sym(O.C(F), M.dot(~F, DV.mrow(~F, s, i), vk(~F, s, c, rest)), O.add(F, O.neg(F, M.dot(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), pcol(~F, s, c))), O.add(F, O.mul(F, O.lookup(~F, DV.mrow(~F, s, i), c), O.one(F)), O.zero(F))), dot_x_vk(~F, DV.mrow(~F, s, i), s, c, rest, hcs(~F, s, c, rest, n, hrest, hns))) : {O.neg(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), M.vneg(~F, GJ.unit(~F, c, i))), pcol(~F, s, c))) == _ : O.C(F)}
          (%Equal.sym(O.C(F), M.dot(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), pcol(~F, s, c)), O.add(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), M.vneg(~F, GJ.unit(~F, c, i))), pcol(~F, s, c)), O.lookup(~F, pcol(~F, s, c), i)), dsplit(~F, DV.mrow(~F, s, i), c, i, pcol(~F, s, c), lpc_le(~F, s, c, hcs(~F, s, c, rest, n, hrest, hns)))) : {O.neg(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), M.vneg(~F, GJ.unit(~F, c, i))), pcol(~F, s, c))) == O.add(F, O.neg(F, _), O.add(F, O.mul(F, O.lookup(~F, DV.mrow(~F, s, i), c), O.one(F)), O.zero(F))) : O.C(F)}
            (%Equal.sym(O.C(F), O.lookup(~F, pcol(~F, s, c), i), O.lookup(~F, DV.mrow(~F, s, i), c), pc_lo(~F, s, c, i, e)) : {O.neg(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), M.vneg(~F, GJ.unit(~F, c, i))), pcol(~F, s, c))) == O.add(F, O.neg(F, O.add(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), M.vneg(~F, GJ.unit(~F, c, i))), pcol(~F, s, c)), _)), O.add(F, O.mul(F, O.lookup(~F, DV.mrow(~F, s, i), c), O.one(F)), O.zero(F))) : O.C(F)}
              FR.fring_eq(~F, [M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), M.vneg(~F, GJ.unit(~F, c, i))), pcol(~F, s, c)), O.lookup(~F, DV.mrow(~F, s, i), c)], E.ZNeg{E.ZVar{0n}}, E.ZAdd{E.ZNeg{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZCst{S.Z0{}}}}, {==})))),
        FM.bnd_mono(~F, O.neg(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), M.vneg(~F, GJ.unit(~F, c, i))), pcol(~F, s, c))), O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m), FM.bnd_neg(~F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), M.vneg(~F, GJ.unit(~F, c, i))), pcol(~F, s, c)), O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg),
            dd_bnd(~F, DV.mrow(~F, s, i), c, i, ph, gg, pcol(~F, s, c), ri_f(~F, n, jm, DV.mrow(~F, s, i), i, c, gg, dd, ph, ri_atf(~F, n, jm, s, c, gg, dd, ph, i, h, his(~F, s, n, i, hns, hi))), (%Equal.sym(Nat, M.len(~F, DV.mrow(~F, s, i)), Nat.add(n, n), ri_len(~F, n, jm, DV.mrow(~F, s, i), i, c, gg, dd, ph, ri_atf(~F, n, jm, s, c, gg, dd, ph, i, h, his(~F, s, n, i, hns, hi)))) : {KA.natle(c, _) == True{} : Bool} GJ.le_trans(c, n, Nat.add(n, n), hcn(c, rest, n, hrest), le_add_r(n, n))), vall_take(~F, c, GJ.mcol(~F, s, c), gg, vall_mcol(~F, s, c, gg, rinv_mall(~F, n, jm, s, 0n, c, gg, dd, ph, h), hgg)), len_pcol(~F, s, c, hcs(~F, s, c, rest, n, hrest, hns)), hgg, hph)),
          FM.sub_nonneg(~F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m), le_addr(~F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m, hm0))))
    case False{}:
      KB.bnd_val(~F, O.add(F, O.neg(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), M.vneg(~F, GJ.unit(~F, c, i))), pcol(~F, s, c))), O.lookup(~F, DV.mrow(~F, s, i), c)), M.dot(~F, DV.mrow(~F, s, i), vk(~F, s, c, rest)), O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m),
        (%Equal.sym(O.C(F), M.dot(~F, DV.mrow(~F, s, i), vk(~F, s, c, rest)), O.add(F, O.neg(F, M.dot(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), pcol(~F, s, c))), O.add(F, O.mul(F, O.lookup(~F, DV.mrow(~F, s, i), c), O.one(F)), O.zero(F))), dot_x_vk(~F, DV.mrow(~F, s, i), s, c, rest, hcs(~F, s, c, rest, n, hrest, hns))) : {O.add(F, O.neg(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), M.vneg(~F, GJ.unit(~F, c, i))), pcol(~F, s, c))), O.lookup(~F, DV.mrow(~F, s, i), c)) == _ : O.C(F)}
          (%Equal.sym(O.C(F), M.dot(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), pcol(~F, s, c)), O.add(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), M.vneg(~F, GJ.unit(~F, c, i))), pcol(~F, s, c)), O.lookup(~F, pcol(~F, s, c), i)), dsplit(~F, DV.mrow(~F, s, i), c, i, pcol(~F, s, c), lpc_le(~F, s, c, hcs(~F, s, c, rest, n, hrest, hns)))) : {O.add(F, O.neg(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), M.vneg(~F, GJ.unit(~F, c, i))), pcol(~F, s, c))), O.lookup(~F, DV.mrow(~F, s, i), c)) == O.add(F, O.neg(F, _), O.add(F, O.mul(F, O.lookup(~F, DV.mrow(~F, s, i), c), O.one(F)), O.zero(F))) : O.C(F)}
            (%Equal.sym(O.C(F), O.lookup(~F, pcol(~F, s, c), i), O.zero(F), pc_hi(~F, s, c, i, GJ.not_lt(i, c, e))) : {O.add(F, O.neg(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), M.vneg(~F, GJ.unit(~F, c, i))), pcol(~F, s, c))), O.lookup(~F, DV.mrow(~F, s, i), c)) == O.add(F, O.neg(F, O.add(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), M.vneg(~F, GJ.unit(~F, c, i))), pcol(~F, s, c)), _)), O.add(F, O.mul(F, O.lookup(~F, DV.mrow(~F, s, i), c), O.one(F)), O.zero(F))) : O.C(F)}
              FR.fring_eq(~F, [M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), M.vneg(~F, GJ.unit(~F, c, i))), pcol(~F, s, c)), O.lookup(~F, DV.mrow(~F, s, i), c)], E.ZAdd{E.ZNeg{E.ZVar{0n}}, E.ZVar{1n}}, E.ZAdd{E.ZNeg{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Z0{}}}}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZCst{S.Z0{}}}}, {==})))),
        FM.bnd_add(~F, O.neg(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), M.vneg(~F, GJ.unit(~F, c, i))), pcol(~F, s, c))), O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), O.lookup(~F, DV.mrow(~F, s, i), c), m, FM.bnd_neg(~F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, c, DV.mrow(~F, s, i)), M.vneg(~F, GJ.unit(~F, c, i))), pcol(~F, s, c)), O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg),
            dd_bnd(~F, DV.mrow(~F, s, i), c, i, ph, gg, pcol(~F, s, c), ri_f(~F, n, jm, DV.mrow(~F, s, i), i, c, gg, dd, ph, ri_atf(~F, n, jm, s, c, gg, dd, ph, i, h, his(~F, s, n, i, hns, hi))), (%Equal.sym(Nat, M.len(~F, DV.mrow(~F, s, i)), Nat.add(n, n), ri_len(~F, n, jm, DV.mrow(~F, s, i), i, c, gg, dd, ph, ri_atf(~F, n, jm, s, c, gg, dd, ph, i, h, his(~F, s, n, i, hns, hi)))) : {KA.natle(c, _) == True{} : Bool} GJ.le_trans(c, n, Nat.add(n, n), hcn(c, rest, n, hrest), le_add_r(n, n))), vall_take(~F, c, GJ.mcol(~F, s, c), gg, vall_mcol(~F, s, c, gg, rinv_mall(~F, n, jm, s, 0n, c, gg, dd, ph, h), hgg)), len_pcol(~F, s, c, hcs(~F, s, c, rest, n, hrest, hns)), hgg, hph)),
          (%GJ.not_lt(i, c, e) : cnd(_, M.bnd(~F, O.lookup(~F, DV.mrow(~F, s, i), c), m))
            GJ.all_at(~(j => cnd(KA.natle(c, j), M.bnd(~F, O.lookup(~F, DV.mrow(~F, s, j), c), m))), n, hm, i, hi))))

# R_x . (J v) = x . v - (L - R J)_x . v
def zr_jv(~F: O.OField, +x: M.Vec(~F), +n: Nat, +jm: M.Mat(~F), +v: M.Vec(~F), +lv: {M.len(~F, v) == n : Nat}) -> {M.dot(~F, GJ.vdrop(~F, n, x), M.matvec(~F, jm, v)) == O.add(F, M.dot(~F, x, v), O.neg(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm))), v))) : O.C(F)}:
  %FM.dot_vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm)), v) : {M.dot(~F, GJ.vdrop(~F, n, x), M.matvec(~F, jm, v)) == O.add(F, M.dot(~F, x, v), O.neg(F, _)) : O.C(F)}
  %FM.dot_vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm), v) : {M.dot(~F, GJ.vdrop(~F, n, x), M.matvec(~F, jm, v)) == O.add(F, M.dot(~F, x, v), O.neg(F, O.add(F, M.dot(~F, GJ.vtake(~F, n, x), v), _))) : O.C(F)}
  %FM.vecmat_dot(~F, GJ.vdrop(~F, n, x), jm, v) : {M.dot(~F, GJ.vdrop(~F, n, x), M.matvec(~F, jm, v)) == O.add(F, M.dot(~F, x, v), O.neg(F, O.add(F, M.dot(~F, GJ.vtake(~F, n, x), v), O.neg(F, _)))) : O.C(F)}
  %lv : {M.dot(~F, GJ.vdrop(~F, n, x), M.matvec(~F, jm, v)) == O.add(F, M.dot(~F, x, v), O.neg(F, O.add(F, M.dot(~F, GJ.vtake(~F, _, x), v), O.neg(F, M.dot(~F, GJ.vdrop(~F, n, x), M.matvec(~F, jm, v)))))) : O.C(F)}
  %Equal.sym(O.C(F), M.dot(~F, GJ.vtake(~F, M.len(~F, v), x), v), M.dot(~F, x, v), GJ.dot_take(~F, x, v)) : {M.dot(~F, GJ.vdrop(~F, n, x), M.matvec(~F, jm, v)) == O.add(F, M.dot(~F, x, v), O.neg(F, O.add(F, _, O.neg(F, M.dot(~F, GJ.vdrop(~F, n, x), M.matvec(~F, jm, v)))))) : O.C(F)}
  FR.fring_eq(~F, [M.dot(~F, GJ.vdrop(~F, n, x), M.matvec(~F, jm, v)), M.dot(~F, x, v)], E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZNeg{E.ZAdd{E.ZVar{1n}, E.ZNeg{E.ZVar{0n}}}}}, {==})

def eq_dv(~F: O.OField, +x: M.Vec(~F), +n: Nat, +jm: M.Mat(~F), +k: Nat, +hk: {KA.natle(1n+k, n) == True{} : Bool}) -> {dk(~F, n, jm, x, k) == O.lookup(~F, GJ.vtake(~F, n, M.vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm)))), k) : O.C(F)}:
  %GJ.look_take_lo(~F, n, M.vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm))), k, hk) : {dk(~F, n, jm, x, k) == _ : O.C(F)}
  %GJ.look_vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm)), k) : {dk(~F, n, jm, x, k) == _ : O.C(F)}
  %GJ.look_vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm), k) : {dk(~F, n, jm, x, k) == O.add(F, O.lookup(~F, GJ.vtake(~F, n, x), k), _) : O.C(F)}
  %GJ.look_take_lo(~F, n, x, k, hk) : {dk(~F, n, jm, x, k) == O.add(F, _, O.neg(F, O.lookup(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm), k))) : O.C(F)}
  %Equal.sym(O.C(F), O.lookup(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm), k), M.dot(~F, GJ.vdrop(~F, n, x), GJ.mcol(~F, jm, k)), look_vecmat(~F, GJ.vdrop(~F, n, x), jm, k)) : {dk(~F, n, jm, x, k) == O.add(F, O.lookup(~F, x, k), O.neg(F, _)) : O.C(F)}
  FR.fring_eq(~F, [O.lookup(~F, x, k), M.dot(~F, GJ.vdrop(~F, n, x), GJ.mcol(~F, jm, k))], E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZAdd{E.ZVar{0n}, E.ZNeg{E.ZVar{1n}}}, {==})

# |(L - R J)_x . v| <= n Delta |v|
def dvec_bnd(~F: O.OField, +x: M.Vec(~F), +n: Nat, +jm: M.Mat(~F), +dd: O.C(F), +v: M.Vec(~F), +hd: dfb(~F, n, jm, x, dd), +lv: {M.len(~F, v) == n : Nat}, +hdd: O.le(~F, O.zero(F), dd)) -> M.bnd(~F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm))), v), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, v))):
  (%GJ.dot_take(~F, M.vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm))), v) : M.bnd(~F, _, O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, v)))
    (%Equal.sym(Nat, M.len(~F, v), n, lv) : M.bnd(~F, M.dot(~F, GJ.vtake(~F, _, M.vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm)))), v), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, v)))
      FM.bnd_mono(~F, M.dot(~F, GJ.vtake(~F, n, M.vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm)))), v), O.mul(F, NP.rowabs(~F, GJ.vtake(~F, n, M.vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm)))), M.len(~F, v)), NP.vn(~F, v)), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, v)),
        NP.dot_le(~F, GJ.vtake(~F, n, M.vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm)))), v, NP.vn(~F, v), FV.vmax_all(~F, v), FV.vmax_nn(~F, v)),
        FM.sub_nonneg(~F, O.mul(F, NP.rowabs(~F, GJ.vtake(~F, n, M.vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm)))), M.len(~F, v)), NP.vn(~F, v)), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, v)), FV.mul_le_r(~F, NP.rowabs(~F, GJ.vtake(~F, n, M.vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm)))), M.len(~F, v)), O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, v), FV.vmax_nn(~F, v),
          (%Equal.sym(Nat, M.len(~F, v), n, lv) : O.le(~F, NP.rowabs(~F, GJ.vtake(~F, n, M.vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm)))), _), O.mul(F, FR.ofn(~F, n), dd))
            rowabs_le(~F, GJ.vtake(~F, n, M.vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm)))), n, dd, vall_lt(~F, ~GJ.vtake(~F, n, M.vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm)))), ~dd, ~(k => hk =>
              KB.bnd_val(~F, dk(~F, n, jm, x, k), O.lookup(~F, GJ.vtake(~F, n, M.vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm)))), k), dd, eq_dv(~F, x, n, jm, k, lt_take(~F, n, M.vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm))), k, hk)), GJ.all_at(~(q => M.bnd(~F, dk(~F, n, jm, x, q), dd)), n, hd, k, lt_take(~F, n, M.vadd(~F, GJ.vtake(~F, n, x), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, x), jm))), k, hk))))), hdd)))))))

# row i of R against J v
def zrow_bnd(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +s: M.Mat(~F), +c: Nat, +rest: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +m: O.C(F), +h: rinv(~F, n, jm, s, 0n, c, gg, dd, ph), +hns: {GJ.nrows(~F, s) == n : Nat}, +hrest: {Nat.add(c, 1n+rest) == n : Nat}, +hm: GJ.All(~(j => cnd(KA.natle(c, j), M.bnd(~F, O.lookup(~F, DV.mrow(~F, s, j), c), m))), n), +hm0: O.le(~F, O.zero(F), m), +hgg: O.le(~F, O.zero(F), gg), +hdd: O.le(~F, O.zero(F), dd), +hph: O.le(~F, O.zero(F), ph), +i: Nat, +hi: {KA.natle(1n+i, n) == True{} : Bool}) -> M.bnd(~F, zr(~F, n, DV.mrow(~F, s, i), M.matvec(~F, jm, vk(~F, s, c, rest))), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, vk(~F, s, c, rest))))):
  KB.bnd_val(~F, O.add(F, M.dot(~F, DV.mrow(~F, s, i), vk(~F, s, c, rest)), O.neg(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, n, DV.mrow(~F, s, i)), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, DV.mrow(~F, s, i)), jm))), vk(~F, s, c, rest)))), zr(~F, n, DV.mrow(~F, s, i), M.matvec(~F, jm, vk(~F, s, c, rest))), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, vk(~F, s, c, rest)))),
    Equal.sym(O.C(F), zr(~F, n, DV.mrow(~F, s, i), M.matvec(~F, jm, vk(~F, s, c, rest))), O.add(F, M.dot(~F, DV.mrow(~F, s, i), vk(~F, s, c, rest)), O.neg(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, n, DV.mrow(~F, s, i)), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, DV.mrow(~F, s, i)), jm))), vk(~F, s, c, rest)))), zr_jv(~F, DV.mrow(~F, s, i), n, jm, vk(~F, s, c, rest), Equal.trans(Nat, M.len(~F, vk(~F, s, c, rest)), Nat.add(c, 1n+rest), n, len_vk(~F, s, c, rest, hcs(~F, s, c, rest, n, hrest, hns)), hrest))),
    FM.bnd_add(~F, M.dot(~F, DV.mrow(~F, s, i), vk(~F, s, c, rest)), O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m), O.neg(F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, n, DV.mrow(~F, s, i)), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, DV.mrow(~F, s, i)), jm))), vk(~F, s, c, rest))), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, vk(~F, s, c, rest))),
      xv_bnd.go(~F, n, jm, s, c, rest, gg, dd, ph, m, h, hns, hrest, hm, hm0, hgg, hdd, hph, i, hi, KA.natle(1n+i, c), {==}),
      FM.bnd_neg(~F, M.dot(~F, M.vadd(~F, GJ.vtake(~F, n, DV.mrow(~F, s, i)), M.vneg(~F, M.vecmat(~F, GJ.vdrop(~F, n, DV.mrow(~F, s, i)), jm))), vk(~F, s, c, rest)), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, vk(~F, s, c, rest))),
        dvec_bnd(~F, DV.mrow(~F, s, i), n, jm, dd, vk(~F, s, c, rest), ri_d(~F, n, jm, DV.mrow(~F, s, i), i, c, gg, dd, ph, ri_atf(~F, n, jm, s, c, gg, dd, ph, i, h, his(~F, s, n, i, hns, hi))), Equal.trans(Nat, M.len(~F, vk(~F, s, c, rest)), Nat.add(c, 1n+rest), n, len_vk(~F, s, c, rest, hcs(~F, s, c, rest, n, hrest, hns)), hrest), hdd))))

# an index below |R u| is below n
def hirm(~F: O.OField, +n: Nat, +s: M.Mat(~F), +u: M.Vec(~F), +i: Nat, +hns: {GJ.nrows(~F, s) == n : Nat}, +hi2: {KA.natle(1n+i, M.len(~F, M.matvec(~F, rmat(~F, n, s), u))) == True{} : Bool}) -> {KA.natle(1n+i, n) == True{} : Bool}:
  %hns : {KA.natle(1n+i, _) == True{} : Bool}
  %len_rmv(~F, n, s, u) : {KA.natle(1n+i, _) == True{} : Bool}
  hi2

# |R J v| <= c phi G + m + n Delta |v|
def rjv_le(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +s: M.Mat(~F), +c: Nat, +rest: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +m: O.C(F), +h: rinv(~F, n, jm, s, 0n, c, gg, dd, ph), +hns: {GJ.nrows(~F, s) == n : Nat}, +hrest: {Nat.add(c, 1n+rest) == n : Nat}, +hm: GJ.All(~(j => cnd(KA.natle(c, j), M.bnd(~F, O.lookup(~F, DV.mrow(~F, s, j), c), m))), n), +hm0: O.le(~F, O.zero(F), m), +hgg: O.le(~F, O.zero(F), gg), +hdd: O.le(~F, O.zero(F), dd), +hph: O.le(~F, O.zero(F), ph)) -> O.le(~F, NP.vn(~F, M.matvec(~F, rmat(~F, n, s), M.matvec(~F, jm, vk(~F, s, c, rest)))), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, vk(~F, s, c, rest))))):
  FV.vmax_lub(~F, M.matvec(~F, rmat(~F, n, s), M.matvec(~F, jm, vk(~F, s, c, rest))), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, vk(~F, s, c, rest)))), vall_lt(~F, ~M.matvec(~F, rmat(~F, n, s), M.matvec(~F, jm, vk(~F, s, c, rest))), ~O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, vk(~F, s, c, rest)))), ~(i => hi2 =>
      (%Equal.sym(O.C(F), O.lookup(~F, M.matvec(~F, rmat(~F, n, s), M.matvec(~F, jm, vk(~F, s, c, rest))), i), zr(~F, n, DV.mrow(~F, s, i), M.matvec(~F, jm, vk(~F, s, c, rest))), look_rmv(~F, n, s, M.matvec(~F, jm, vk(~F, s, c, rest)), i)) : M.bnd(~F, _, O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, vk(~F, s, c, rest)))))
        zrow_bnd(~F, n, jm, s, c, rest, gg, dd, ph, m, h, hns, hrest, hm, hm0, hgg, hdd, hph, i, hirm(~F, n, s, M.matvec(~F, jm, vk(~F, s, c, rest)), i, hns, hi2))))),
    FO.nonneg_add(~F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, vk(~F, s, c, rest))), FO.nonneg_add(~F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m, FO.mul_nonneg(~F, O.mul(F, FR.ofn(~F, c), ph), gg, FO.mul_nonneg(~F, FR.ofn(~F, c), ph, ofn_nn(~F, c), hph), hgg), hm0), FO.mul_nonneg(~F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, vk(~F, s, c, rest)), FO.mul_nonneg(~F, FR.ofn(~F, n), dd, ofn_nn(~F, n), hdd), FV.vmax_nn(~F, vk(~F, s, c, rest)))))


# the pivot bound: with |cand| <= m for every candidate,
# 1 <= beta H ((c phi G + m) + n Delta (1 + G))
def kern(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +s: M.Mat(~F), +c: Nat, +rest: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +m: O.C(F), +h: rinv(~F, n, jm, s, 0n, c, gg, dd, ph), +hns: {GJ.nrows(~F, s) == n : Nat}, +hrest: {Nat.add(c, 1n+rest) == n : Nat}, +hm: GJ.All(~(j => cnd(KA.natle(c, j), M.bnd(~F, O.lookup(~F, DV.mrow(~F, s, j), c), m))), n), +hm0: O.le(~F, O.zero(F), m), +hgg: O.le(~F, O.zero(F), gg), +hdd: O.le(~F, O.zero(F), dd), +hph: O.le(~F, O.zero(F), ph), +bb: O.C(F), +hh: O.C(F), +hJ: NP.InvB(~F, jm, n, bb), +hjn: {GJ.nrows(~F, jm) == n : Nat}, +hR: NP.InvB(~F, rmat(~F, n, s), n, hh)) -> O.le(~F, O.one(F), O.mul(F, O.mul(F, bb, hh), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), O.add(F, O.one(F), gg))))):
  +h1 = one_le_vk(~F, s, c, rest, hcs(~F, s, c, rest, n, hrest, hns))
  +h2 = NP.lowb(~F, jm, n, bb, hJ, hjn, vk(~F, s, c, rest), Equal.trans(Nat, M.len(~F, vk(~F, s, c, rest)), Nat.add(c, 1n+rest), n, len_vk(~F, s, c, rest, hcs(~F, s, c, rest, n, hrest, hns)), hrest))
  +h3 = NP.lowb(~F, rmat(~F, n, s), n, hh, hR, Equal.trans(Nat, GJ.nrows(~F, rmat(~F, n, s)), GJ.nrows(~F, s), n, nrows_rmat(~F, n, s), hns), M.matvec(~F, jm, vk(~F, s, c, rest)), Equal.trans(Nat, M.len(~F, M.matvec(~F, jm, vk(~F, s, c, rest))), GJ.nrows(~F, jm), n, Equal.sym(Nat, GJ.nrows(~F, jm), M.len(~F, M.matvec(~F, jm, vk(~F, s, c, rest))), GJ.len_matvec(~F, jm, vk(~F, s, c, rest))), hjn))
  +h4 = rjv_le(~F, n, jm, s, c, rest, gg, dd, ph, m, h, hns, hrest, hm, hm0, hgg, hdd, hph)
  +h5 = vk_le(~F, s, c, rest, gg, rinv_mall(~F, n, jm, s, 0n, c, gg, dd, ph, h), hgg)
  +hb0 = NP.invb_nn(~F, jm, n, bb, hJ)
  +hh0 = NP.invb_nn(~F, rmat(~F, n, s), n, hh, hR)
  +hnd = FO.mul_nonneg(~F, FR.ofn(~F, n), dd, ofn_nn(~F, n), hdd)
  +s1 = FM.sub_nonneg(~F, O.one(F), NP.vn(~F, vk(~F, s, c, rest)), h1)
  +s2 = FM.sub_nonneg(~F, NP.vn(~F, vk(~F, s, c, rest)), O.mul(F, bb, NP.vn(~F, M.matvec(~F, jm, vk(~F, s, c, rest)))), h2)
  +s3 = FM.sub_nonneg(~F, NP.vn(~F, M.matvec(~F, jm, vk(~F, s, c, rest))), O.mul(F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, s), M.matvec(~F, jm, vk(~F, s, c, rest))))), h3)
  +s4 = FM.sub_nonneg(~F, NP.vn(~F, M.matvec(~F, rmat(~F, n, s), M.matvec(~F, jm, vk(~F, s, c, rest)))), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, vk(~F, s, c, rest)))), h4)
  +s5 = FM.sub_nonneg(~F, NP.vn(~F, vk(~F, s, c, rest)), O.add(F, O.one(F), gg), h5)
  FV.le_of_sub(~F, O.one(F), O.mul(F, O.mul(F, bb, hh), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), O.add(F, O.one(F), gg)))), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.mul(F, bb, hh), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), O.add(F, O.one(F), gg)))), O.one(F)), O.add(F, O.add(F, O.add(F, O.add(F, O.sub(~F, NP.vn(~F, vk(~F, s, c, rest)), O.one(F)), O.sub(~F, O.mul(F, bb, NP.vn(~F, M.matvec(~F, jm, vk(~F, s, c, rest)))), NP.vn(~F, vk(~F, s, c, rest)))), O.mul(F, bb, O.sub(~F, O.mul(F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, s), M.matvec(~F, jm, vk(~F, s, c, rest))))), NP.vn(~F, M.matvec(~F, jm, vk(~F, s, c, rest)))))), O.mul(F, O.mul(F, bb, hh), O.sub(~F, O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, vk(~F, s, c, rest)))), NP.vn(~F, M.matvec(~F, rmat(~F, n, s), M.matvec(~F, jm, vk(~F, s, c, rest))))))), O.mul(F, O.mul(F, O.mul(F, bb, hh), O.mul(F, FR.ofn(~F, n), dd)), O.sub(~F, O.add(F, O.one(F), gg), NP.vn(~F, vk(~F, s, c, rest))))),
    FR.fring_eq(~F, [NP.vn(~F, vk(~F, s, c, rest)), NP.vn(~F, M.matvec(~F, jm, vk(~F, s, c, rest))), NP.vn(~F, M.matvec(~F, rmat(~F, n, s), M.matvec(~F, jm, vk(~F, s, c, rest)))), bb, hh, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m, O.mul(F, FR.ofn(~F, n), dd), gg], E.ZAdd{E.ZAdd{E.ZAdd{E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZMul{E.ZVar{3n}, E.ZVar{1n}}, E.ZVar{0n}}}, E.ZMul{E.ZVar{3n}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{2n}}, E.ZVar{1n}}}}, E.ZMul{E.ZMul{E.ZVar{3n}, E.ZVar{4n}}, E.ZSub{E.ZAdd{E.ZAdd{E.ZVar{5n}, E.ZVar{6n}}, E.ZMul{E.ZVar{7n}, E.ZVar{0n}}}, E.ZVar{2n}}}}, E.ZMul{E.ZMul{E.ZMul{E.ZVar{3n}, E.ZVar{4n}}, E.ZVar{7n}}, E.ZSub{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{8n}}, E.ZVar{0n}}}}, E.ZSub{E.ZMul{E.ZMul{E.ZVar{3n}, E.ZVar{4n}}, E.ZAdd{E.ZAdd{E.ZVar{5n}, E.ZVar{6n}}, E.ZMul{E.ZVar{7n}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{8n}}}}}, E.ZCst{S.Zpos{S.XH{}}}}, {==}),
    FO.nonneg_add(~F, O.add(F, O.add(F, O.add(F, O.sub(~F, NP.vn(~F, vk(~F, s, c, rest)), O.one(F)), O.sub(~F, O.mul(F, bb, NP.vn(~F, M.matvec(~F, jm, vk(~F, s, c, rest)))), NP.vn(~F, vk(~F, s, c, rest)))), O.mul(F, bb, O.sub(~F, O.mul(F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, s), M.matvec(~F, jm, vk(~F, s, c, rest))))), NP.vn(~F, M.matvec(~F, jm, vk(~F, s, c, rest)))))), O.mul(F, O.mul(F, bb, hh), O.sub(~F, O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, vk(~F, s, c, rest)))), NP.vn(~F, M.matvec(~F, rmat(~F, n, s), M.matvec(~F, jm, vk(~F, s, c, rest))))))), O.mul(F, O.mul(F, O.mul(F, bb, hh), O.mul(F, FR.ofn(~F, n), dd)), O.sub(~F, O.add(F, O.one(F), gg), NP.vn(~F, vk(~F, s, c, rest)))),
      FO.nonneg_add(~F, O.add(F, O.add(F, O.sub(~F, NP.vn(~F, vk(~F, s, c, rest)), O.one(F)), O.sub(~F, O.mul(F, bb, NP.vn(~F, M.matvec(~F, jm, vk(~F, s, c, rest)))), NP.vn(~F, vk(~F, s, c, rest)))), O.mul(F, bb, O.sub(~F, O.mul(F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, s), M.matvec(~F, jm, vk(~F, s, c, rest))))), NP.vn(~F, M.matvec(~F, jm, vk(~F, s, c, rest)))))), O.mul(F, O.mul(F, bb, hh), O.sub(~F, O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, vk(~F, s, c, rest)))), NP.vn(~F, M.matvec(~F, rmat(~F, n, s), M.matvec(~F, jm, vk(~F, s, c, rest)))))),
        FO.nonneg_add(~F, O.add(F, O.sub(~F, NP.vn(~F, vk(~F, s, c, rest)), O.one(F)), O.sub(~F, O.mul(F, bb, NP.vn(~F, M.matvec(~F, jm, vk(~F, s, c, rest)))), NP.vn(~F, vk(~F, s, c, rest)))), O.mul(F, bb, O.sub(~F, O.mul(F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, s), M.matvec(~F, jm, vk(~F, s, c, rest))))), NP.vn(~F, M.matvec(~F, jm, vk(~F, s, c, rest))))), FO.nonneg_add(~F, O.sub(~F, NP.vn(~F, vk(~F, s, c, rest)), O.one(F)), O.sub(~F, O.mul(F, bb, NP.vn(~F, M.matvec(~F, jm, vk(~F, s, c, rest)))), NP.vn(~F, vk(~F, s, c, rest))), s1, s2), FO.mul_nonneg(~F, bb, O.sub(~F, O.mul(F, hh, NP.vn(~F, M.matvec(~F, rmat(~F, n, s), M.matvec(~F, jm, vk(~F, s, c, rest))))), NP.vn(~F, M.matvec(~F, jm, vk(~F, s, c, rest)))), hb0, s3)),
        FO.mul_nonneg(~F, O.mul(F, bb, hh), O.sub(~F, O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), ph), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), dd), NP.vn(~F, vk(~F, s, c, rest)))), NP.vn(~F, M.matvec(~F, rmat(~F, n, s), M.matvec(~F, jm, vk(~F, s, c, rest))))), FO.mul_nonneg(~F, bb, hh, hb0, hh0), s4)),
      FO.mul_nonneg(~F, O.mul(F, O.mul(F, bb, hh), O.mul(F, FR.ofn(~F, n), dd)), O.sub(~F, O.add(F, O.one(F), gg), NP.vn(~F, vk(~F, s, c, rest))), FO.mul_nonneg(~F, O.mul(F, bb, hh), O.mul(F, FR.ofn(~F, n), dd), FO.mul_nonneg(~F, bb, hh, hb0, hh0), hnd), s5))))

# Constants of the elimination
# ----------------------------
# Column c's invariant uses entry bound G_c, inverse bound H_c, defect
# KD_c u and finished columns KP_c u, computed jointly with u = 2^-w
# taken out (u <= 1 absorbed); sigma = 4 beta H bounds the rounded
# reciprocal once the pivot is at least 1/(2 beta H).

def KS(~F: O.OField) -> Data:
  M.Both(O.C(F), M.Both(O.C(F), M.Both(O.C(F), O.C(F))))

def kg(~F: O.OField, st: KS(~F)) -> O.C(F):
  match st:
    case (a, r):
      a

def kh(~F: O.OField, st: KS(~F)) -> O.C(F):
  match st:
    case (a, r):
      match r:
        case (b, r2):
          b

def kd(~F: O.OField, st: KS(~F)) -> O.C(F):
  match st:
    case (a, r):
      match r:
        case (b, r2):
          match r2:
            case (d, p):
              d

def kp(~F: O.OField, st: KS(~F)) -> O.C(F):
  match st:
    case (a, r):
      match r:
        case (b, r2):
          match r2:
            case (d, p):
              p

def sgb(~F: O.OField, +bb: O.C(F), +hh: O.C(F)) -> O.C(F):
  O.add(F, O.mul(F, O.add(F, bb, bb), hh), O.mul(F, O.add(F, bb, bb), hh))

def gpc(~F: O.OField, +sg: O.C(F), +gg: O.C(F)) -> O.C(F):
  O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))

def ekc(~F: O.OField, +gg: O.C(F), +gp: O.C(F)) -> O.C(F):
  O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, gp), O.mul(F, gg, gp)), O.mul(F, gg, gp)))

def kdpc(~F: O.OField, +n: Nat, +g: O.C(F), +sg: O.C(F), +gg: O.C(F), +kd: O.C(F)) -> O.C(F):
  O.add(F, O.mul(F, sg, kd), O.mul(F, O.mul(F, sg, gg), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g))))

def kppc(~F: O.OField, +sg: O.C(F), +gg: O.C(F), +kp: O.C(F)) -> O.C(F):
  O.add(F, O.add(F, O.mul(F, sg, kp), O.one(F)), O.mul(F, sg, gg))

def kstep.go(~F: O.OField, +n: Nat, +g: O.C(F), +bb: O.C(F), +gg: O.C(F), +hh: O.C(F), +kd: O.C(F), +kp: O.C(F)) -> KS(~F):
  (gnew(~F, gg, gpc(~F, sgb(~F, bb, hh), gg), ekc(~F, gg, gpc(~F, sgb(~F, bb, hh), gg))), (O.mul(F, O.add(F, hh, hh), aco(~F, gg)), (dnew(~F, n, g, gg, kd, kdpc(~F, n, g, sgb(~F, bb, hh), gg, kd), ekc(~F, gg, gpc(~F, sgb(~F, bb, hh), gg))), pnew(~F, gg, kp, kppc(~F, sgb(~F, bb, hh), gg, kp), ekc(~F, gg, gpc(~F, sgb(~F, bb, hh), gg))))))

def kstep(~F: O.OField, +n: Nat, +g: O.C(F), +bb: O.C(F), +st: KS(~F)) -> KS(~F):
  kstep.go(~F, n, g, bb, kg(~F, st), kh(~F, st), kd(~F, st), kp(~F, st))

# the constants after c columns, from |J_ij| <= g and |J^-1| <= beta
def kst(~F: O.OField, +n: Nat, +g: O.C(F), +bb: O.C(F), c: Nat) -> KS(~F):
  match c:
    case 0n:
      (O.add(F, g, O.one(F)), (O.one(F), (O.zero(F), O.zero(F))))
    case 1n+j:
      kstep(~F, n, g, bb, kst(~F, n, g, bb, j))

def KNN(~F: O.OField, +st: KS(~F)) -> Data:
  M.Both(O.le(~F, O.zero(F), kg(~F, st)), M.Both(O.le(~F, O.zero(F), kh(~F, st)), M.Both(O.le(~F, O.zero(F), kd(~F, st)), O.le(~F, O.zero(F), kp(~F, st)))))


def knn_g(~F: O.OField, +st: KS(~F), h: KNN(~F, st)) -> O.le(~F, O.zero(F), kg(~F, st)):
  match h:
    case (a, r):
      a

def knn_h(~F: O.OField, +st: KS(~F), h: KNN(~F, st)) -> O.le(~F, O.zero(F), kh(~F, st)):
  match h:
    case (a, r):
      match r:
        case (b, r2):
          b

def knn_d(~F: O.OField, +st: KS(~F), h: KNN(~F, st)) -> O.le(~F, O.zero(F), kd(~F, st)):
  match h:
    case (a, r):
      match r:
        case (b, r2):
          match r2:
            case (d, q):
              d

def knn_p(~F: O.OField, +st: KS(~F), h: KNN(~F, st)) -> O.le(~F, O.zero(F), kp(~F, st)):
  match h:
    case (a, r):
      match r:
        case (b, r2):
          match r2:
            case (d, q):
              q

def knn_step(~F: O.OField, +n: Nat, +g: O.C(F), +bb: O.C(F), +st: KS(~F), +hg: O.le(~F, O.zero(F), g), +hb: O.le(~F, O.zero(F), bb), +h: KNN(~F, st)) -> KNN(~F, kstep(~F, n, g, bb, st)):
  +h1 = knn_g(~F, st, h)
  +h2 = knn_h(~F, st, h)
  +h3 = knn_d(~F, st, h)
  +h4 = knn_p(~F, st, h)
  (FO.nonneg_add(~F, O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), O.add(F, O.add(F, kg(~F, st), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))))), FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1)), FO.nonneg_add(~F, O.add(F, kg(~F, st), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))))), FO.nonneg_add(~F, kg(~F, st), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), h1, FO.mul_nonneg(~F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), h1, FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1)))), FO.nonneg_add(~F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), h1, FO.nonneg_add(~F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), FO.nonneg_add(~F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), FO.mul_nonneg(~F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), h1, FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1))), FO.mul_nonneg(~F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), h1, FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1)))), FO.mul_nonneg(~F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), h1, FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1))))))), (FO.mul_nonneg(~F, O.add(F, kh(~F, st), kh(~F, st)), O.add(F, O.add(F, O.one(F), kg(~F, st)), O.add(F, kg(~F, st), kg(~F, st))), FO.nonneg_add(~F, kh(~F, st), kh(~F, st), h2, h2), FO.nonneg_add(~F, O.add(F, O.one(F), kg(~F, st)), O.add(F, kg(~F, st), kg(~F, st)), FO.nonneg_add(~F, O.one(F), kg(~F, st), NP.one_nn(~F), h1), FO.nonneg_add(~F, kg(~F, st), kg(~F, st), h1, h1))), (FO.nonneg_add(~F, O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kd(~F, st)), O.mul(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))), O.add(F, O.add(F, kd(~F, st), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kd(~F, st)), O.mul(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))))), O.mul(F, O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))))), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))), FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kd(~F, st)), O.mul(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g))), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kd(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h3), FO.mul_nonneg(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1), FO.nonneg_add(~F, O.one(F), O.mul(F, FR.ofn(~F, n), g), NP.one_nn(~F), FO.mul_nonneg(~F, FR.ofn(~F, n), g, ofn_nn(~F, n), hg)))), FO.nonneg_add(~F, O.add(F, kd(~F, st), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kd(~F, st)), O.mul(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))))), O.mul(F, O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))))), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g))), FO.nonneg_add(~F, kd(~F, st), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kd(~F, st)), O.mul(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g))))), h3, FO.mul_nonneg(~F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kd(~F, st)), O.mul(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))), h1, FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kd(~F, st)), O.mul(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g))), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kd(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h3), FO.mul_nonneg(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1), FO.nonneg_add(~F, O.one(F), O.mul(F, FR.ofn(~F, n), g), NP.one_nn(~F), FO.mul_nonneg(~F, FR.ofn(~F, n), g, ofn_nn(~F, n), hg)))))), FO.mul_nonneg(~F, O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))))), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)), FO.nonneg_add(~F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), h1, FO.nonneg_add(~F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), FO.nonneg_add(~F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), FO.mul_nonneg(~F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), h1, FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1))), FO.mul_nonneg(~F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), h1, FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1)))), FO.mul_nonneg(~F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), h1, FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1))))), FO.nonneg_add(~F, O.one(F), O.mul(F, FR.ofn(~F, n), g), NP.one_nn(~F), FO.mul_nonneg(~F, FR.ofn(~F, n), g, ofn_nn(~F, n), hg))))), FO.nonneg_add(~F, O.add(F, O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kp(~F, st)), O.one(F)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), O.add(F, O.add(F, kp(~F, st), O.mul(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kp(~F, st)), O.one(F)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))))), FO.nonneg_add(~F, O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kp(~F, st)), O.one(F)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kp(~F, st)), O.one(F), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kp(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h4), NP.one_nn(~F)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1)), FO.nonneg_add(~F, O.add(F, kp(~F, st), O.mul(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kp(~F, st)), O.one(F)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))))), FO.nonneg_add(~F, kp(~F, st), O.mul(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kp(~F, st)), O.one(F)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), h4, FO.mul_nonneg(~F, kg(~F, st), O.add(F, O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kp(~F, st)), O.one(F)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), h1, FO.nonneg_add(~F, O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kp(~F, st)), O.one(F)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kp(~F, st)), O.one(F), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kp(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h4), NP.one_nn(~F)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1)))), FO.nonneg_add(~F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), h1, FO.nonneg_add(~F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), FO.nonneg_add(~F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), FO.mul_nonneg(~F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), h1, FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1))), FO.mul_nonneg(~F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), h1, FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1)))), FO.mul_nonneg(~F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), h1, FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), h2)), h1))))))))))

def kst_nn(~F: O.OField, +n: Nat, +g: O.C(F), +bb: O.C(F), +hg: O.le(~F, O.zero(F), g), +hb: O.le(~F, O.zero(F), bb), c: Nat) -> KNN(~F, kst(~F, n, g, bb, c)):
  match c:
    case 0n:
      (FO.nonneg_add(~F, g, O.one(F), hg, NP.one_nn(~F)), (NP.one_nn(~F), (FO.le_refl(~F, O.zero(F)), FO.le_refl(~F, O.zero(F)))))
    case 1n++j:
      knn_step(~F, n, g, bb, kst(~F, n, g, bb, j), hg, hb, kst_nn(~F, n, g, bb, hg, hb, j))


# one step's constants, with u <= 1, are at most the next column's
def gw(~F: O.OField, +sg: O.C(F), +gg: O.C(F), +w: Nat, +hs0: O.le(~F, O.zero(F), sg), +hg0: O.le(~F, O.zero(F), gg), +hu: O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F))) -> O.le(~F, gnew(~F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), gnew(~F, gg, gpc(~F, sg, gg), ekc(~F, gg, gpc(~F, sg, gg)))):
  FV.le_of_sub(~F, gnew(~F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), gnew(~F, gg, gpc(~F, sg, gg), ekc(~F, gg, gpc(~F, sg, gg))), FM.nn_eq(~F, O.sub(~F, gnew(~F, gg, gpc(~F, sg, gg), ekc(~F, gg, gpc(~F, sg, gg))), gnew(~F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.add(F, O.add(F, O.mul(F, O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.add(F, O.one(F), gg)), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))))), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, O.mul(F, O.add(F, O.add(F, gg, gg), gg), O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))),
    FR.fring_eq(~F, [sg, gg, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})], E.ZAdd{E.ZAdd{E.ZMul{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{2n}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{1n}}}, E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}}}, E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{2n}}}}, E.ZMul{E.ZMul{E.ZAdd{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{2n}}}}, E.ZVar{2n}}}, E.ZSub{E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, E.ZAdd{E.ZAdd{E.ZVar{1n}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}}, E.ZAdd{E.ZVar{1n}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}}}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}, E.ZAdd{E.ZAdd{E.ZVar{1n}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}}, E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}}}, E.ZVar{2n}}}}}, {==}),
    FO.nonneg_add(~F, O.add(F, O.mul(F, O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.add(F, O.one(F), gg)), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))))), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, O.mul(F, O.add(F, O.add(F, gg, gg), gg), O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FO.nonneg_add(~F, O.mul(F, O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.add(F, O.one(F), gg)), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))))), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), FO.mul_nonneg(~F, O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.add(F, O.one(F), gg), FO.mul_nonneg(~F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FO.mul_nonneg(~F, sg, gg, hs0, hg0), FM.sub_nonneg(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F), hu)), FO.nonneg_add(~F, O.one(F), gg, NP.one_nn(~F), hg0)), FO.mul_nonneg(~F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))))), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FO.nonneg_add(~F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))), hg0, FO.nonneg_add(~F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))), FO.nonneg_add(~F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))), FO.mul_nonneg(~F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)), hg0, FO.nonneg_add(~F, O.mul(F, sg, gg), O.mul(F, sg, gg), FO.mul_nonneg(~F, sg, gg, hs0, hg0), FO.mul_nonneg(~F, sg, gg, hs0, hg0))), FO.mul_nonneg(~F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)), hg0, FO.nonneg_add(~F, O.mul(F, sg, gg), O.mul(F, sg, gg), FO.mul_nonneg(~F, sg, gg, hs0, hg0), FO.mul_nonneg(~F, sg, gg, hs0, hg0)))), FO.mul_nonneg(~F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)), hg0, FO.nonneg_add(~F, O.mul(F, sg, gg), O.mul(F, sg, gg), FO.mul_nonneg(~F, sg, gg, hs0, hg0), FO.mul_nonneg(~F, sg, gg, hs0, hg0))))), FM.sub_nonneg(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F), hu))), FO.mul_nonneg(~F, O.mul(F, O.add(F, O.add(F, gg, gg), gg), O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), FO.mul_nonneg(~F, O.add(F, O.add(F, gg, gg), gg), O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), FO.nonneg_add(~F, O.add(F, gg, gg), gg, FO.nonneg_add(~F, gg, gg, hg0, hg0), hg0), FO.mul_nonneg(~F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FO.mul_nonneg(~F, sg, gg, hs0, hg0), FM.sub_nonneg(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F), hu))), u_nn(~F, w)))))

def dw(~F: O.OField, +n: Nat, +g: O.C(F), +sg: O.C(F), +gg: O.C(F), +kd: O.C(F), +w: Nat, +hs0: O.le(~F, O.zero(F), sg), +hg0: O.le(~F, O.zero(F), gg), +hg: O.le(~F, O.zero(F), g), +hu: O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F))) -> O.le(~F, dnew(~F, n, g, gg, O.mul(F, kd, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.mul(F, sg, O.mul(F, kd, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, dnew(~F, n, g, gg, kd, kdpc(~F, n, g, sg, gg, kd), ekc(~F, gg, gpc(~F, sg, gg))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))):
  FV.le_of_sub(~F, dnew(~F, n, g, gg, O.mul(F, kd, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.mul(F, sg, O.mul(F, kd, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, dnew(~F, n, g, gg, kd, kdpc(~F, n, g, sg, gg, kd), ekc(~F, gg, gpc(~F, sg, gg))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FM.nn_eq(~F, O.sub(~F, O.mul(F, dnew(~F, n, g, gg, kd, kdpc(~F, n, g, sg, gg, kd), ekc(~F, gg, gpc(~F, sg, gg))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), dnew(~F, n, g, gg, O.mul(F, kd, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.mul(F, sg, O.mul(F, kd, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, O.mul(F, O.mul(F, O.add(F, O.add(F, gg, gg), gg), O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g))),
    FR.fring_eq(~F, [sg, gg, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), kd, FR.ofn(~F, n), g], E.ZMul{E.ZMul{E.ZMul{E.ZAdd{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{2n}}}}, E.ZVar{2n}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZVar{4n}, E.ZVar{5n}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZVar{4n}, E.ZVar{5n}}}}}, E.ZAdd{E.ZAdd{E.ZVar{3n}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZVar{4n}, E.ZVar{5n}}}}}}}, E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZVar{4n}, E.ZVar{5n}}}}}}, E.ZVar{2n}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{3n}, E.ZVar{2n}}}, E.ZMul{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZVar{4n}, E.ZVar{5n}}}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{3n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{3n}, E.ZVar{2n}}}, E.ZMul{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZVar{4n}, E.ZVar{5n}}}}}}}, E.ZMul{E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}}}, E.ZVar{2n}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZVar{4n}, E.ZVar{5n}}}}}}}, {==}),
    FO.mul_nonneg(~F, O.mul(F, O.mul(F, O.add(F, O.add(F, gg, gg), gg), O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)), FO.mul_nonneg(~F, O.mul(F, O.add(F, O.add(F, gg, gg), gg), O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), FO.mul_nonneg(~F, O.add(F, O.add(F, gg, gg), gg), O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), FO.nonneg_add(~F, O.add(F, gg, gg), gg, FO.nonneg_add(~F, gg, gg, hg0, hg0), hg0), FO.mul_nonneg(~F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FO.mul_nonneg(~F, sg, gg, hs0, hg0), FM.sub_nonneg(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F), hu))), u_nn(~F, w)), FO.nonneg_add(~F, O.one(F), O.mul(F, FR.ofn(~F, n), g), NP.one_nn(~F), FO.mul_nonneg(~F, FR.ofn(~F, n), g, ofn_nn(~F, n), hg)))))

def pw(~F: O.OField, +sg: O.C(F), +gg: O.C(F), +kp: O.C(F), +w: Nat, +hs0: O.le(~F, O.zero(F), sg), +hg0: O.le(~F, O.zero(F), gg), +hu: O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F))) -> O.le(~F, pnew(~F, gg, O.mul(F, kp, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.add(F, O.mul(F, sg, O.mul(F, kp, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, pnew(~F, gg, kp, kppc(~F, sg, gg, kp), ekc(~F, gg, gpc(~F, sg, gg))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))):
  FV.le_of_sub(~F, pnew(~F, gg, O.mul(F, kp, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.add(F, O.mul(F, sg, O.mul(F, kp, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, pnew(~F, gg, kp, kppc(~F, sg, gg, kp), ekc(~F, gg, gpc(~F, sg, gg))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FM.nn_eq(~F, O.sub(~F, O.mul(F, pnew(~F, gg, kp, kppc(~F, sg, gg, kp), ekc(~F, gg, gpc(~F, sg, gg))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), pnew(~F, gg, O.mul(F, kp, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.add(F, O.mul(F, sg, O.mul(F, kp, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, O.mul(F, O.add(F, O.add(F, gg, gg), gg), O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})),
    FR.fring_eq(~F, [sg, gg, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), kp], E.ZMul{E.ZMul{E.ZAdd{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{2n}}}}, E.ZVar{2n}}, E.ZSub{E.ZMul{E.ZAdd{E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, E.ZAdd{E.ZAdd{E.ZVar{3n}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}}, E.ZAdd{E.ZVar{1n}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}}}}}, E.ZVar{2n}}, E.ZAdd{E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{3n}, E.ZVar{2n}}}, E.ZVar{2n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{3n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{3n}, E.ZVar{2n}}}, E.ZVar{2n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}}, E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}}}, E.ZVar{2n}}}}}, {==}),
    FO.mul_nonneg(~F, O.mul(F, O.add(F, O.add(F, gg, gg), gg), O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), FO.mul_nonneg(~F, O.add(F, O.add(F, gg, gg), gg), O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), FO.nonneg_add(~F, O.add(F, gg, gg), gg, FO.nonneg_add(~F, gg, gg, hg0, hg0), hg0), FO.mul_nonneg(~F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FO.mul_nonneg(~F, sg, gg, hs0, hg0), FM.sub_nonneg(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F), hu))), u_nn(~F, w))))

# Column step glue
# ----------------

def rinv_mono(~F: O.OField, +n: Nat, +jm: M.Mat(~F), s: M.Mat(~F), +i: Nat, +c: Nat, +g1: O.C(F), +d1: O.C(F), +p1: O.C(F), +g2: O.C(F), +d2: O.C(F), +p2: O.C(F), h: rinv(~F, n, jm, s, i, c, g1, d1, p1), +eg: O.le(~F, g1, g2), +ed: O.le(~F, d1, d2), +ep: O.le(~F, p1, p2)) -> rinv(~F, n, jm, s, i, c, g2, d2, p2):
  match s:
    case Nil{}:
      Unit{}
    case Con{x, t}:
      (h1, h2) = h
      (ri_mono(~F, n, jm, x, i, c, g1, d1, p1, g2, d2, p2, h1, eg, ed, ep), rinv_mono(~F, n, jm, t, 1n+i, c, g1, d1, p1, g2, d2, p2, h2, eg, ed, ep))

# after swapping rows c and r, row c is the old row r
def mrow_swap_c(~F: O.OField, +a: M.Mat(~F), +c: Nat, +r: Nat, +hc: {KA.natle(1n+c, GJ.nrows(~F, a)) == True{} : Bool}, b: Bool, +e: {KA.nateq(r, c) == b : Bool}) -> {DV.mrow(~F, GJ.mswap(~F, a, c, r), c) == DV.mrow(~F, a, r) : M.Vec(~F)}:
  match b:
    case True{}:
      %Equal.sym(Nat, r, c, GJ.nateq_ok(r, c, e)) : {DV.mrow(~F, GJ.mswap(~F, a, c, _), c) == DV.mrow(~F, a, _) : M.Vec(~F)}
      Equal.sym(M.Vec(~F), DV.mrow(~F, a, c), DV.mrow(~F, GJ.mswap(~F, a, c, c), c), GJ.row_mset_eq(~F, GJ.mset(~F, a, c, DV.mrow(~F, a, c)), c, DV.mrow(~F, a, c), GJ.lt_nrows_mset(~F, a, c, DV.mrow(~F, a, c), c, hc)))
    case False{}:
      Equal.sym(M.Vec(~F), DV.mrow(~F, a, r), DV.mrow(~F, GJ.mswap(~F, a, c, r), c), Equal.trans(M.Vec(~F), DV.mrow(~F, a, r), DV.mrow(~F, GJ.mset(~F, a, c, DV.mrow(~F, a, r)), c), DV.mrow(~F, GJ.mswap(~F, a, c, r), c), GJ.row_mset_eq(~F, a, c, DV.mrow(~F, a, r), hc), GJ.row_mset_ne(~F, GJ.mset(~F, a, c, DV.mrow(~F, a, r)), r, c, DV.mrow(~F, a, c), e)))

# the pivot in F: entry c of row c after the swap is entry c of row r
def piv_swap(~F: O.OField, +rows: List<&2, List<&2, S.D>>, +c: Nat, +r: Nat, +hc: {KA.natle(1n+c, GJ.nrows(~F, M.ofdm(~F, rows))) == True{} : Bool}) -> {M.ofd(~F, NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)) == M.ofd(~F, NU.dget(NU.drow(rows, r), c)) : O.C(F)}:
  %Equal.sym(O.C(F), M.ofd(~F, NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), O.lookup(~F, M.ofdv(~F, NU.drow(NU.dswap(rows, c, r), c)), c), dget_ofd(~F, NU.drow(NU.dswap(rows, c, r), c), c)) : {_ == M.ofd(~F, NU.dget(NU.drow(rows, r), c)) : O.C(F)}
  %Equal.sym(O.C(F), M.ofd(~F, NU.dget(NU.drow(rows, r), c)), O.lookup(~F, M.ofdv(~F, NU.drow(rows, r)), c), dget_ofd(~F, NU.drow(rows, r), c)) : {O.lookup(~F, M.ofdv(~F, NU.drow(NU.dswap(rows, c, r), c)), c) == _ : O.C(F)}
  %Equal.sym(M.Vec(~F), M.ofdv(~F, NU.drow(NU.dswap(rows, c, r), c)), DV.mrow(~F, M.ofdm(~F, NU.dswap(rows, c, r)), c), drow_ofd(~F, NU.dswap(rows, c, r), c)) : {O.lookup(~F, _, c) == O.lookup(~F, M.ofdv(~F, NU.drow(rows, r)), c) : O.C(F)}
  %Equal.sym(M.Vec(~F), M.ofdv(~F, NU.drow(rows, r)), DV.mrow(~F, M.ofdm(~F, rows), r), drow_ofd(~F, rows, r)) : {O.lookup(~F, DV.mrow(~F, M.ofdm(~F, NU.dswap(rows, c, r)), c), c) == O.lookup(~F, _, c) : O.C(F)}
  %Equal.sym(M.Mat(~F), M.ofdm(~F, NU.dswap(rows, c, r)), GJ.mswap(~F, M.ofdm(~F, rows), c, r), dswap_ofd(~F, rows, c, r)) : {O.lookup(~F, DV.mrow(~F, _, c), c) == O.lookup(~F, DV.mrow(~F, M.ofdm(~F, rows), r), c) : O.C(F)}
  Equal.cong(M.Vec(~F), O.C(F), x => O.lookup(~F, x, c), DV.mrow(~F, GJ.mswap(~F, M.ofdm(~F, rows), c, r), c), DV.mrow(~F, M.ofdm(~F, rows), r), mrow_swap_c(~F, M.ofdm(~F, rows), c, r, hc, KA.nateq(r, c), {==}))

def nrows_dswap(~F: O.OField, +rows: List<&2, List<&2, S.D>>, +c: Nat, +r: Nat) -> {GJ.nrows(~F, M.ofdm(~F, NU.dswap(rows, c, r))) == GJ.nrows(~F, M.ofdm(~F, rows)) : Nat}:
  %Equal.sym(M.Mat(~F), M.ofdm(~F, NU.dswap(rows, c, r)), GJ.mswap(~F, M.ofdm(~F, rows), c, r), dswap_ofd(~F, rows, c, r)) : {GJ.nrows(~F, _) == GJ.nrows(~F, M.ofdm(~F, rows)) : Nat}
  Equal.sym(Nat, GJ.nrows(~F, M.ofdm(~F, rows)), GJ.nrows(~F, GJ.mswap(~F, M.ofdm(~F, rows), c, r)), GJ.nrows_mswap(~F, M.ofdm(~F, rows), c, r))

def nrows_dclear(~F: O.OField, rows: List<&2, List<&2, S.D>>, +w: Nat, +p: List<&2, S.D>, +c: Nat, +i: Nat) -> {GJ.nrows(~F, M.ofdm(~F, NU.dclear(rows, w, p, c, i))) == GJ.nrows(~F, M.ofdm(~F, rows)) : Nat}:
  match rows:
    case Nil{}:
      {==}
    case Con{h, t}:
      %Equal.sym(Nat, GJ.nrows(~F, M.ofdm(~F, NU.dclear(t, w, p, c, 1n+i))), GJ.nrows(~F, M.ofdm(~F, t)), nrows_dclear(~F, t, w, p, c, 1n+i)) : {1n+_ == 1n+GJ.nrows(~F, M.ofdm(~F, t)) : Nat}
      {==}

# u (a + b) <= 1 with u, a, b >= 0: each part alone
def upart_l(~F: O.OField, +u: O.C(F), +a: O.C(F), +b: O.C(F), +h: O.le(~F, O.mul(F, u, O.add(F, a, b)), O.one(F)), +hu: O.le(~F, O.zero(F), u), +hb: O.le(~F, O.zero(F), b)) -> O.le(~F, O.mul(F, u, a), O.one(F)):
  DM.le_trans(~F, O.mul(F, u, a), O.mul(F, u, O.add(F, a, b)), O.one(F), FV.mul_le(~F, u, a, O.add(F, a, b), hu, le_addr(~F, a, b, hb)), h)

def upart_r(~F: O.OField, +u: O.C(F), +a: O.C(F), +b: O.C(F), +h: O.le(~F, O.mul(F, u, O.add(F, a, b)), O.one(F)), +hu: O.le(~F, O.zero(F), u), +ha: O.le(~F, O.zero(F), a)) -> O.le(~F, O.mul(F, u, b), O.one(F)):
  DM.le_trans(~F, O.mul(F, u, b), O.mul(F, u, O.add(F, a, b)), O.one(F), FV.mul_le(~F, u, b, O.add(F, a, b), hu, le_addl(~F, a, b, ha)), h)

def u_le1_of(~F: O.OField, +u: O.C(F), +h: O.le(~F, O.mul(F, u, O.one(F)), O.one(F))) -> O.le(~F, u, O.one(F)):
  %FR.fring_eq(~F, [u], E.ZMul{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{0n}, {==}) : O.le(~F, _, O.one(F))
  h

# The smallness each column needs, as u A_c <= 1

def ac1(~F: O.OField, +n: Nat, +bb: O.C(F), +c: Nat, +st: KS(~F)) -> O.C(F):
  O.mul(F, O.add(F, O.mul(F, bb, kh(~F, st)), O.mul(F, bb, kh(~F, st))), O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), kp(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, FR.ofn(~F, n), kd(~F, st)), O.add(F, O.one(F), kg(~F, st)))))

def ac2(~F: O.OField, +bb: O.C(F), +st: KS(~F)) -> O.C(F):
  O.add(F, O.mul(F, kg(~F, st), O.mul(F, O.add(F, bb, bb), kh(~F, st))), O.mul(F, kg(~F, st), O.mul(F, O.add(F, bb, bb), kh(~F, st))))

def ac3(~F: O.OField, +n: Nat, +bb: O.C(F), +st: KS(~F)) -> O.C(F):
  O.add(F, O.mul(F, kh(~F, st), O.add(F, O.mul(F, FR.ofn(~F, n), O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))))), O.mul(F, O.add(F, kg(~F, st), kg(~F, st)), O.mul(F, FR.ofn(~F, n), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))))), O.mul(F, kh(~F, st), O.add(F, O.mul(F, FR.ofn(~F, n), O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))))), O.mul(F, O.add(F, kg(~F, st), kg(~F, st)), O.mul(F, FR.ofn(~F, n), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))))))

def acoef(~F: O.OField, +n: Nat, +bb: O.C(F), +c: Nat, +st: KS(~F)) -> O.C(F):
  O.add(F, O.add(F, O.add(F, O.one(F), ac1(~F, n, bb, c, st)), ac2(~F, bb, st)), ac3(~F, n, bb, st))

def ac1_nn(~F: O.OField, +n: Nat, +bb: O.C(F), +c: Nat, +st: KS(~F), +hb: O.le(~F, O.zero(F), bb), +hk: KNN(~F, st)) -> O.le(~F, O.zero(F), ac1(~F, n, bb, c, st)):
  FO.mul_nonneg(~F, O.add(F, O.mul(F, bb, kh(~F, st)), O.mul(F, bb, kh(~F, st))), O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), kp(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, FR.ofn(~F, n), kd(~F, st)), O.add(F, O.one(F), kg(~F, st)))), FO.nonneg_add(~F, O.mul(F, bb, kh(~F, st)), O.mul(F, bb, kh(~F, st)), FO.mul_nonneg(~F, bb, kh(~F, st), hb, knn_h(~F, st, hk)), FO.mul_nonneg(~F, bb, kh(~F, st), hb, knn_h(~F, st, hk))), FO.nonneg_add(~F, O.mul(F, O.mul(F, FR.ofn(~F, c), kp(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, FR.ofn(~F, n), kd(~F, st)), O.add(F, O.one(F), kg(~F, st))), FO.mul_nonneg(~F, O.mul(F, FR.ofn(~F, c), kp(~F, st)), kg(~F, st), FO.mul_nonneg(~F, FR.ofn(~F, c), kp(~F, st), ofn_nn(~F, c), knn_p(~F, st, hk)), knn_g(~F, st, hk)), FO.mul_nonneg(~F, O.mul(F, FR.ofn(~F, n), kd(~F, st)), O.add(F, O.one(F), kg(~F, st)), FO.mul_nonneg(~F, FR.ofn(~F, n), kd(~F, st), ofn_nn(~F, n), knn_d(~F, st, hk)), FO.nonneg_add(~F, O.one(F), kg(~F, st), NP.one_nn(~F), knn_g(~F, st, hk)))))

def ac2_nn(~F: O.OField, +bb: O.C(F), +st: KS(~F), +hb: O.le(~F, O.zero(F), bb), +hk: KNN(~F, st)) -> O.le(~F, O.zero(F), ac2(~F, bb, st)):
  FO.nonneg_add(~F, O.mul(F, kg(~F, st), O.mul(F, O.add(F, bb, bb), kh(~F, st))), O.mul(F, kg(~F, st), O.mul(F, O.add(F, bb, bb), kh(~F, st))), FO.mul_nonneg(~F, kg(~F, st), O.mul(F, O.add(F, bb, bb), kh(~F, st)), knn_g(~F, st, hk), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk))), FO.mul_nonneg(~F, kg(~F, st), O.mul(F, O.add(F, bb, bb), kh(~F, st)), knn_g(~F, st, hk), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk))))

def ac3_nn(~F: O.OField, +n: Nat, +bb: O.C(F), +st: KS(~F), +hb: O.le(~F, O.zero(F), bb), +hk: KNN(~F, st)) -> O.le(~F, O.zero(F), ac3(~F, n, bb, st)):
  FO.nonneg_add(~F, O.mul(F, kh(~F, st), O.add(F, O.mul(F, FR.ofn(~F, n), O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))))), O.mul(F, O.add(F, kg(~F, st), kg(~F, st)), O.mul(F, FR.ofn(~F, n), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))))), O.mul(F, kh(~F, st), O.add(F, O.mul(F, FR.ofn(~F, n), O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))))), O.mul(F, O.add(F, kg(~F, st), kg(~F, st)), O.mul(F, FR.ofn(~F, n), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))))), FO.mul_nonneg(~F, kh(~F, st), O.add(F, O.mul(F, FR.ofn(~F, n), O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))))), O.mul(F, O.add(F, kg(~F, st), kg(~F, st)), O.mul(F, FR.ofn(~F, n), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), knn_h(~F, st, hk), FO.nonneg_add(~F, O.mul(F, FR.ofn(~F, n), O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))))), O.mul(F, O.add(F, kg(~F, st), kg(~F, st)), O.mul(F, FR.ofn(~F, n), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), FO.mul_nonneg(~F, FR.ofn(~F, n), O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))))), ofn_nn(~F, n), FO.nonneg_add(~F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), knn_g(~F, st, hk), FO.nonneg_add(~F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), FO.nonneg_add(~F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), FO.mul_nonneg(~F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), knn_g(~F, st, hk), FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk))), knn_g(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk))), knn_g(~F, st, hk)))), FO.mul_nonneg(~F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), knn_g(~F, st, hk), FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk))), knn_g(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk))), knn_g(~F, st, hk))))), FO.mul_nonneg(~F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), knn_g(~F, st, hk), FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk))), knn_g(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk))), knn_g(~F, st, hk))))))), FO.mul_nonneg(~F, O.add(F, kg(~F, st), kg(~F, st)), O.mul(F, FR.ofn(~F, n), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), FO.nonneg_add(~F, kg(~F, st), kg(~F, st), knn_g(~F, st, hk), knn_g(~F, st, hk)), FO.mul_nonneg(~F, FR.ofn(~F, n), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), ofn_nn(~F, n), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk))), knn_g(~F, st, hk)))))), FO.mul_nonneg(~F, kh(~F, st), O.add(F, O.mul(F, FR.ofn(~F, n), O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))))), O.mul(F, O.add(F, kg(~F, st), kg(~F, st)), O.mul(F, FR.ofn(~F, n), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), knn_h(~F, st, hk), FO.nonneg_add(~F, O.mul(F, FR.ofn(~F, n), O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))))), O.mul(F, O.add(F, kg(~F, st), kg(~F, st)), O.mul(F, FR.ofn(~F, n), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), FO.mul_nonneg(~F, FR.ofn(~F, n), O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))))), ofn_nn(~F, n), FO.nonneg_add(~F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), knn_g(~F, st, hk), FO.nonneg_add(~F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), FO.nonneg_add(~F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)))), FO.mul_nonneg(~F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), knn_g(~F, st, hk), FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk))), knn_g(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk))), knn_g(~F, st, hk)))), FO.mul_nonneg(~F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), knn_g(~F, st, hk), FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk))), knn_g(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk))), knn_g(~F, st, hk))))), FO.mul_nonneg(~F, kg(~F, st), O.add(F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), knn_g(~F, st, hk), FO.nonneg_add(~F, O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk))), knn_g(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk))), knn_g(~F, st, hk))))))), FO.mul_nonneg(~F, O.add(F, kg(~F, st), kg(~F, st)), O.mul(F, FR.ofn(~F, n), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st))), FO.nonneg_add(~F, kg(~F, st), kg(~F, st), knn_g(~F, st, hk), knn_g(~F, st, hk)), FO.mul_nonneg(~F, FR.ofn(~F, n), O.mul(F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st)), ofn_nn(~F, n), FO.mul_nonneg(~F, O.add(F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st))), kg(~F, st), FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), knn_h(~F, st, hk))), knn_g(~F, st, hk)))))))


# the pivot bound with the smallness: 1 <= 2 beta H m
def piv_two(~F: O.OField, +n: Nat, +c: Nat, +bb: O.C(F), +hh: O.C(F), +gg: O.C(F), +kd: O.C(F), +kp: O.C(F), +m: O.C(F), +u: O.C(F), +hk: O.le(~F, O.one(F), O.mul(F, O.mul(F, bb, hh), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), O.mul(F, kp, u)), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, kd, u)), O.add(F, O.one(F), gg))))), +ha: O.le(~F, O.mul(F, u, O.mul(F, O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), kp), gg), O.mul(F, O.mul(F, FR.ofn(~F, n), kd), O.add(F, O.one(F), gg))))), O.one(F))) -> O.le(~F, O.one(F), O.mul(F, O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), m)):
  FV.le_of_sub(~F, O.one(F), O.mul(F, O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), m), FM.nn_eq(~F, O.sub(~F, O.mul(F, O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), m), O.one(F)), O.add(F, O.add(F, O.sub(~F, O.mul(F, O.mul(F, bb, hh), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), O.mul(F, kp, u)), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, kd, u)), O.add(F, O.one(F), gg)))), O.one(F)), O.sub(~F, O.mul(F, O.mul(F, bb, hh), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), O.mul(F, kp, u)), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, kd, u)), O.add(F, O.one(F), gg)))), O.one(F))), O.sub(~F, O.one(F), O.mul(F, u, O.mul(F, O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), kp), gg), O.mul(F, O.mul(F, FR.ofn(~F, n), kd), O.add(F, O.one(F), gg))))))),
    FR.fring_eq(~F, [bb, hh, FR.ofn(~F, c), FR.ofn(~F, n), gg, kd, kp, m, u], E.ZAdd{E.ZAdd{E.ZSub{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZMul{E.ZVar{2n}, E.ZMul{E.ZVar{6n}, E.ZVar{8n}}}, E.ZVar{4n}}, E.ZVar{7n}}, E.ZMul{E.ZMul{E.ZVar{3n}, E.ZMul{E.ZVar{5n}, E.ZVar{8n}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{4n}}}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZMul{E.ZVar{2n}, E.ZMul{E.ZVar{6n}, E.ZVar{8n}}}, E.ZVar{4n}}, E.ZVar{7n}}, E.ZMul{E.ZMul{E.ZVar{3n}, E.ZMul{E.ZVar{5n}, E.ZVar{8n}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{4n}}}}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZVar{8n}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, E.ZAdd{E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{6n}}, E.ZVar{4n}}, E.ZMul{E.ZMul{E.ZVar{3n}, E.ZVar{5n}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{4n}}}}}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, E.ZVar{7n}}, E.ZCst{S.Zpos{S.XH{}}}}, {==}),
    FO.nonneg_add(~F, O.add(F, O.sub(~F, O.mul(F, O.mul(F, bb, hh), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), O.mul(F, kp, u)), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, kd, u)), O.add(F, O.one(F), gg)))), O.one(F)), O.sub(~F, O.mul(F, O.mul(F, bb, hh), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), O.mul(F, kp, u)), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, kd, u)), O.add(F, O.one(F), gg)))), O.one(F))), O.sub(~F, O.one(F), O.mul(F, u, O.mul(F, O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), kp), gg), O.mul(F, O.mul(F, FR.ofn(~F, n), kd), O.add(F, O.one(F), gg)))))),
      FO.nonneg_add(~F, O.sub(~F, O.mul(F, O.mul(F, bb, hh), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), O.mul(F, kp, u)), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, kd, u)), O.add(F, O.one(F), gg)))), O.one(F)), O.sub(~F, O.mul(F, O.mul(F, bb, hh), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), O.mul(F, kp, u)), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, kd, u)), O.add(F, O.one(F), gg)))), O.one(F)), FM.sub_nonneg(~F, O.one(F), O.mul(F, O.mul(F, bb, hh), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), O.mul(F, kp, u)), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, kd, u)), O.add(F, O.one(F), gg)))), hk), FM.sub_nonneg(~F, O.one(F), O.mul(F, O.mul(F, bb, hh), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), O.mul(F, kp, u)), gg), m), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, kd, u)), O.add(F, O.one(F), gg)))), hk)),
      FM.sub_nonneg(~F, O.mul(F, u, O.mul(F, O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, c), kp), gg), O.mul(F, O.mul(F, FR.ofn(~F, n), kd), O.add(F, O.one(F), gg))))), O.one(F), ha))))


# 1 <= B m, m <= |p| and q p = 1: |q| <= B
def qle(~F: O.OField, +q: O.C(F), +p: O.C(F), +m: O.C(F), +bv: O.C(F), +h1: O.le(~F, O.one(F), O.mul(F, bv, m)), +hmp: O.le(~F, m, FV.fabs(~F, p)), +hq: {O.mul(F, q, p) == O.one(F) : O.C(F)}, +hb0: O.le(~F, O.zero(F), bv)) -> O.le(~F, FV.fabs(~F, q), bv):
  FV.le_of_sub(~F, FV.fabs(~F, q), bv, FM.nn_eq(~F, O.sub(~F, bv, FV.fabs(~F, q)), O.mul(F, FV.fabs(~F, q), O.sub(~F, O.mul(F, bv, FV.fabs(~F, p)), O.one(F))), FO.eq_of_sub(~F, O.mul(F, FV.fabs(~F, q), O.sub(~F, O.mul(F, bv, FV.fabs(~F, p)), O.one(F))), O.sub(~F, bv, FV.fabs(~F, q)), FO.cert1(~F, O.sub(~F, O.mul(F, FV.fabs(~F, q), O.sub(~F, O.mul(F, bv, FV.fabs(~F, p)), O.one(F))), O.sub(~F, bv, FV.fabs(~F, q))), bv, O.sub(~F, O.mul(F, FV.fabs(~F, q), FV.fabs(~F, p)), O.one(F)), FR.fring_eq(~F, [FV.fabs(~F, q), FV.fabs(~F, p), bv], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{1n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZVar{2n}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), FO.sub_of_eq(~F, O.mul(F, FV.fabs(~F, q), FV.fabs(~F, p)), O.one(F), fabs_inv(~F, q, p, hq)))),
    FO.mul_nonneg(~F, FV.fabs(~F, q), O.sub(~F, O.mul(F, bv, FV.fabs(~F, p)), O.one(F)), FV.fabs_nn(~F, q), FM.sub_nonneg(~F, O.one(F), O.mul(F, bv, FV.fabs(~F, p)), DM.le_trans(~F, O.one(F), O.mul(F, bv, m), O.mul(F, bv, FV.fabs(~F, p)), h1, FV.mul_le(~F, bv, m, FV.fabs(~F, p), hb0, hmp))))))

# a zero pivot would make every candidate 0
def pnz(~F: O.OField, +x: S.D, +bv: O.C(F), +h1: O.le(~F, O.one(F), O.mul(F, bv, M.ofd(~F, NU.dabs(x)))), +hb0: O.le(~F, O.zero(F), bv), +e: {M.ofd(~F, x) == O.zero(F) : O.C(F)}) -> Empty:
  RL.le_lt_absurd(~F, O.one(F), O.zero(F), (%FR.fring_eq(~F, [bv], E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==}) : O.le(~F, O.one(F), _)
      DM.le_trans(~F, O.one(F), O.mul(F, bv, M.ofd(~F, NU.dabs(x))), O.mul(F, bv, O.zero(F)), h1, FV.mul_le(~F, bv, M.ofd(~F, NU.dabs(x)), O.zero(F), hb0,
        BP.kabs_le(~KI.dnum(), ~F, ~KI.demb(~F), x, O.zero(F), (%Equal.sym(O.C(F), M.ofd(~F, x), O.zero(F), e) : M.bnd(~F, _, O.zero(F))
          FM.bnd_zero(~F, O.zero(F), FO.le_refl(~F, O.zero(F)))))))),
    O.zero_lt_one(F))

# the scan's candidate bounds, read in F
def cbF(~F: O.OField, +rows: List<&2, List<&2, S.D>>, +c: Nat, +m: O.C(F), +n: Nat, h: GJ.All(~(j => cb(~F, rows, c, c, m, j)), GJ.nrows(~F, M.ofdm(~F, rows))), +hns: {GJ.nrows(~F, M.ofdm(~F, rows)) == n : Nat}) -> GJ.All(~(j => cnd(KA.natle(c, j), M.bnd(~F, O.lookup(~F, DV.mrow(~F, M.ofdm(~F, rows), j), c), m))), n):
  %hns : GJ.All(~(j => cnd(KA.natle(c, j), M.bnd(~F, O.lookup(~F, DV.mrow(~F, M.ofdm(~F, rows), j), c), m))), _)
  all_map(~(j => cb(~F, rows, c, c, m, j)), ~(j => cnd(KA.natle(c, j), M.bnd(~F, O.lookup(~F, DV.mrow(~F, M.ofdm(~F, rows), j), c), m))), ~(j => q =>
    (%drow_ofd(~F, rows, j) : cnd(KA.natle(c, j), M.bnd(~F, O.lookup(~F, _, c), m))
      (%dget_ofd(~F, NU.drow(rows, j), c) : cnd(KA.natle(c, j), M.bnd(~F, _, m))
        q))), GJ.nrows(~F, M.ofdm(~F, rows)), h)

def hc1(+c: Nat, +rest: Nat, +n: Nat, +hrest: {Nat.add(c, 1n+rest) == n : Nat}) -> {KA.natle(1n+c, n) == True{} : Bool}:
  %hrest : {KA.natle(1n+c, _) == True{} : Bool}
  %LN.add_succ(c, rest) : {KA.natle(1n+c, _) == True{} : Bool}
  le_add_r(c, rest)


# |s| <= |q| (1 + u) <= 4 beta H
def sg_le(~F: O.OField, +q: O.C(F), +u: O.C(F), +bb: O.C(F), +hh: O.C(F), +hq: O.le(~F, FV.fabs(~F, q), O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh))), +hu: O.le(~F, u, O.one(F))) -> O.le(~F, O.add(F, FV.fabs(~F, q), O.mul(F, FV.fabs(~F, q), u)), sgb(~F, bb, hh)):
  FV.le_of_sub(~F, O.add(F, FV.fabs(~F, q), O.mul(F, FV.fabs(~F, q), u)), sgb(~F, bb, hh), FM.nn_eq(~F, O.sub(~F, sgb(~F, bb, hh), O.add(F, FV.fabs(~F, q), O.mul(F, FV.fabs(~F, q), u))), O.add(F, O.add(F, O.sub(~F, O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), FV.fabs(~F, q)), O.sub(~F, O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), FV.fabs(~F, q))), O.mul(F, FV.fabs(~F, q), O.sub(~F, O.one(F), u))), FR.fring_eq(~F, [FV.fabs(~F, q), u, bb, hh], E.ZAdd{E.ZAdd{E.ZSub{E.ZAdd{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZMul{E.ZVar{2n}, E.ZVar{3n}}}, E.ZVar{0n}}, E.ZSub{E.ZAdd{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZMul{E.ZVar{2n}, E.ZVar{3n}}}, E.ZVar{0n}}}, E.ZMul{E.ZVar{0n}, E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{1n}}}}, E.ZSub{E.ZAdd{E.ZMul{E.ZAdd{E.ZVar{2n}, E.ZVar{2n}}, E.ZVar{3n}}, E.ZMul{E.ZAdd{E.ZVar{2n}, E.ZVar{2n}}, E.ZVar{3n}}}, E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}, {==}),
    FO.nonneg_add(~F, O.add(F, O.sub(~F, O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), FV.fabs(~F, q)), O.sub(~F, O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), FV.fabs(~F, q))), O.mul(F, FV.fabs(~F, q), O.sub(~F, O.one(F), u)), FO.nonneg_add(~F, O.sub(~F, O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), FV.fabs(~F, q)), O.sub(~F, O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), FV.fabs(~F, q)), FM.sub_nonneg(~F, FV.fabs(~F, q), O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), hq), FM.sub_nonneg(~F, FV.fabs(~F, q), O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), hq)), FO.mul_nonneg(~F, FV.fabs(~F, q), O.sub(~F, O.one(F), u), FV.fabs_nn(~F, q), FM.sub_nonneg(~F, u, O.one(F), hu)))))

# 2 G |q| u <= 1, for col_low
def hsm_of(~F: O.OField, +q: O.C(F), +u: O.C(F), +bb: O.C(F), +hh: O.C(F), +gg: O.C(F), +hq: O.le(~F, FV.fabs(~F, q), O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh))), +ha: O.le(~F, O.mul(F, u, O.add(F, O.mul(F, gg, O.mul(F, O.add(F, bb, bb), hh)), O.mul(F, gg, O.mul(F, O.add(F, bb, bb), hh)))), O.one(F)), +hu0: O.le(~F, O.zero(F), u), +hg0: O.le(~F, O.zero(F), gg)) -> O.le(~F, O.add(F, O.mul(F, gg, O.mul(F, FV.fabs(~F, q), u)), O.mul(F, gg, O.mul(F, FV.fabs(~F, q), u))), O.one(F)):
  FV.le_of_sub(~F, O.add(F, O.mul(F, gg, O.mul(F, FV.fabs(~F, q), u)), O.mul(F, gg, O.mul(F, FV.fabs(~F, q), u))), O.one(F), FM.nn_eq(~F, O.sub(~F, O.one(F), O.add(F, O.mul(F, gg, O.mul(F, FV.fabs(~F, q), u)), O.mul(F, gg, O.mul(F, FV.fabs(~F, q), u)))), O.add(F, O.sub(~F, O.one(F), O.mul(F, u, O.add(F, O.mul(F, gg, O.mul(F, O.add(F, bb, bb), hh)), O.mul(F, gg, O.mul(F, O.add(F, bb, bb), hh))))), O.mul(F, O.add(F, O.mul(F, gg, u), O.mul(F, gg, u)), O.sub(~F, O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), FV.fabs(~F, q)))), FR.fring_eq(~F, [FV.fabs(~F, q), u, bb, hh, gg], E.ZAdd{E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{4n}, E.ZMul{E.ZAdd{E.ZVar{2n}, E.ZVar{2n}}, E.ZVar{3n}}}, E.ZMul{E.ZVar{4n}, E.ZMul{E.ZAdd{E.ZVar{2n}, E.ZVar{2n}}, E.ZVar{3n}}}}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{4n}, E.ZVar{1n}}, E.ZMul{E.ZVar{4n}, E.ZVar{1n}}}, E.ZSub{E.ZAdd{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZMul{E.ZVar{2n}, E.ZVar{3n}}}, E.ZVar{0n}}}}, E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZMul{E.ZVar{4n}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, E.ZMul{E.ZVar{4n}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}}, {==}),
    FO.nonneg_add(~F, O.sub(~F, O.one(F), O.mul(F, u, O.add(F, O.mul(F, gg, O.mul(F, O.add(F, bb, bb), hh)), O.mul(F, gg, O.mul(F, O.add(F, bb, bb), hh))))), O.mul(F, O.add(F, O.mul(F, gg, u), O.mul(F, gg, u)), O.sub(~F, O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), FV.fabs(~F, q))), FM.sub_nonneg(~F, O.mul(F, u, O.add(F, O.mul(F, gg, O.mul(F, O.add(F, bb, bb), hh)), O.mul(F, gg, O.mul(F, O.add(F, bb, bb), hh)))), O.one(F), ha),
      FO.mul_nonneg(~F, O.add(F, O.mul(F, gg, u), O.mul(F, gg, u)), O.sub(~F, O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), FV.fabs(~F, q)), FO.nonneg_add(~F, O.mul(F, gg, u), O.mul(F, gg, u), FO.mul_nonneg(~F, gg, u, hg0, hu0), FO.mul_nonneg(~F, gg, u, hg0, hu0)), FM.sub_nonneg(~F, FV.fabs(~F, q), O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), hq)))))


# 2 H bco <= 1, for col_low
def hB_of(~F: O.OField, +n: Nat, +sg: O.C(F), +gg: O.C(F), +hh: O.C(F), +w: Nat, +ha: O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.add(F, O.mul(F, hh, O.add(F, O.mul(F, FR.ofn(~F, n), O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))))), O.mul(F, O.add(F, gg, gg), O.mul(F, FR.ofn(~F, n), O.mul(F, sg, gg))))), O.mul(F, hh, O.add(F, O.mul(F, FR.ofn(~F, n), O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))))), O.mul(F, O.add(F, gg, gg), O.mul(F, FR.ofn(~F, n), O.mul(F, sg, gg))))))), O.one(F)), +hs0: O.le(~F, O.zero(F), sg), +hg0: O.le(~F, O.zero(F), gg), +hh0: O.le(~F, O.zero(F), hh), +hu: O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F))) -> O.le(~F, O.add(F, O.mul(F, hh, bco(~F, n, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), w)), O.mul(F, hh, bco(~F, n, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), w))), O.one(F)):
  FV.le_of_sub(~F, O.add(F, O.mul(F, hh, bco(~F, n, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), w)), O.mul(F, hh, bco(~F, n, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), w))), O.one(F), FM.nn_eq(~F, O.sub(~F, O.one(F), O.add(F, O.mul(F, hh, bco(~F, n, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), w)), O.mul(F, hh, bco(~F, n, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.mul(F, sg, gg), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), w)))), O.add(F, O.sub(~F, O.one(F), O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.add(F, O.mul(F, hh, O.add(F, O.mul(F, FR.ofn(~F, n), O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))))), O.mul(F, O.add(F, gg, gg), O.mul(F, FR.ofn(~F, n), O.mul(F, sg, gg))))), O.mul(F, hh, O.add(F, O.mul(F, FR.ofn(~F, n), O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))))), O.mul(F, O.add(F, gg, gg), O.mul(F, FR.ofn(~F, n), O.mul(F, sg, gg)))))))), O.mul(F, O.add(F, hh, hh), O.mul(F, O.mul(F, FR.ofn(~F, n), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.add(F, O.add(F, gg, gg), gg), O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))))),
    FR.fring_eq(~F, [sg, gg, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), hh, FR.ofn(~F, n)], E.ZAdd{E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZVar{2n}, E.ZAdd{E.ZMul{E.ZVar{3n}, E.ZAdd{E.ZMul{E.ZVar{4n}, E.ZAdd{E.ZVar{1n}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}}}}, E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZMul{E.ZVar{4n}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}}}, E.ZMul{E.ZVar{3n}, E.ZAdd{E.ZMul{E.ZVar{4n}, E.ZAdd{E.ZVar{1n}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}}}}, E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZMul{E.ZVar{4n}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}}}}}}, E.ZMul{E.ZAdd{E.ZVar{3n}, E.ZVar{3n}}, E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{2n}}, E.ZMul{E.ZAdd{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{2n}}}}}}}, E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZMul{E.ZVar{3n}, E.ZAdd{E.ZMul{E.ZVar{4n}, E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}}}, E.ZVar{2n}}}, E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZMul{E.ZVar{4n}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}}}, E.ZMul{E.ZVar{3n}, E.ZAdd{E.ZMul{E.ZVar{4n}, E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}}}, E.ZVar{2n}}}, E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZVar{1n}}, E.ZMul{E.ZVar{4n}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}}}}}}, {==}),
    FO.nonneg_add(~F, O.sub(~F, O.one(F), O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.add(F, O.mul(F, hh, O.add(F, O.mul(F, FR.ofn(~F, n), O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))))), O.mul(F, O.add(F, gg, gg), O.mul(F, FR.ofn(~F, n), O.mul(F, sg, gg))))), O.mul(F, hh, O.add(F, O.mul(F, FR.ofn(~F, n), O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))))), O.mul(F, O.add(F, gg, gg), O.mul(F, FR.ofn(~F, n), O.mul(F, sg, gg)))))))), O.mul(F, O.add(F, hh, hh), O.mul(F, O.mul(F, FR.ofn(~F, n), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.add(F, O.add(F, gg, gg), gg), O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))),
      FM.sub_nonneg(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.add(F, O.mul(F, hh, O.add(F, O.mul(F, FR.ofn(~F, n), O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))))), O.mul(F, O.add(F, gg, gg), O.mul(F, FR.ofn(~F, n), O.mul(F, sg, gg))))), O.mul(F, hh, O.add(F, O.mul(F, FR.ofn(~F, n), O.add(F, gg, O.add(F, O.add(F, O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))), O.mul(F, gg, O.add(F, O.mul(F, sg, gg), O.mul(F, sg, gg)))))), O.mul(F, O.add(F, gg, gg), O.mul(F, FR.ofn(~F, n), O.mul(F, sg, gg))))))), O.one(F), ha),
      FO.mul_nonneg(~F, O.add(F, hh, hh), O.mul(F, O.mul(F, FR.ofn(~F, n), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.add(F, O.add(F, gg, gg), gg), O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), FO.nonneg_add(~F, hh, hh, hh0, hh0), FO.mul_nonneg(~F, O.mul(F, FR.ofn(~F, n), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.add(F, O.add(F, gg, gg), gg), O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), FO.mul_nonneg(~F, FR.ofn(~F, n), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), ofn_nn(~F, n), u_nn(~F, w)), FO.mul_nonneg(~F, O.add(F, O.add(F, gg, gg), gg), O.mul(F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), FO.nonneg_add(~F, O.add(F, gg, gg), gg, FO.nonneg_add(~F, gg, gg, hg0, hg0), hg0), FO.mul_nonneg(~F, O.mul(F, sg, gg), O.sub(~F, O.one(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FO.mul_nonneg(~F, sg, gg, hs0, hg0), FM.sub_nonneg(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F), hu))))))))

# the smallness, part by part
def sm_u(~F: O.OField, +n: Nat, +bb: O.C(F), +c: Nat, +st: KS(~F), +w: Nat, +hb: O.le(~F, O.zero(F), bb), +hk: KNN(~F, st), +hA: O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), acoef(~F, n, bb, c, st)), O.one(F))) -> O.le(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F)):
  u_le1_of(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), upart_l(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F), ac1(~F, n, bb, c, st), upart_l(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.add(F, O.one(F), ac1(~F, n, bb, c, st)), ac2(~F, bb, st), upart_l(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.add(F, O.add(F, O.one(F), ac1(~F, n, bb, c, st)), ac2(~F, bb, st)), ac3(~F, n, bb, st), hA, u_nn(~F, w), ac3_nn(~F, n, bb, st, hb, hk)), u_nn(~F, w), ac2_nn(~F, bb, st, hb, hk)), u_nn(~F, w), ac1_nn(~F, n, bb, c, st, hb, hk)))

def sm1(~F: O.OField, +n: Nat, +bb: O.C(F), +c: Nat, +st: KS(~F), +w: Nat, +hb: O.le(~F, O.zero(F), bb), +hk: KNN(~F, st), +hA: O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), acoef(~F, n, bb, c, st)), O.one(F))) -> O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), ac1(~F, n, bb, c, st)), O.one(F)):
  upart_r(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.one(F), ac1(~F, n, bb, c, st), upart_l(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.add(F, O.one(F), ac1(~F, n, bb, c, st)), ac2(~F, bb, st), upart_l(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.add(F, O.add(F, O.one(F), ac1(~F, n, bb, c, st)), ac2(~F, bb, st)), ac3(~F, n, bb, st), hA, u_nn(~F, w), ac3_nn(~F, n, bb, st, hb, hk)), u_nn(~F, w), ac2_nn(~F, bb, st, hb, hk)), u_nn(~F, w), NP.one_nn(~F))

def sm2(~F: O.OField, +n: Nat, +bb: O.C(F), +c: Nat, +st: KS(~F), +w: Nat, +hb: O.le(~F, O.zero(F), bb), +hk: KNN(~F, st), +hA: O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), acoef(~F, n, bb, c, st)), O.one(F))) -> O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), ac2(~F, bb, st)), O.one(F)):
  upart_r(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.add(F, O.one(F), ac1(~F, n, bb, c, st)), ac2(~F, bb, st), upart_l(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.add(F, O.add(F, O.one(F), ac1(~F, n, bb, c, st)), ac2(~F, bb, st)), ac3(~F, n, bb, st), hA, u_nn(~F, w), ac3_nn(~F, n, bb, st, hb, hk)), u_nn(~F, w), FO.nonneg_add(~F, O.one(F), ac1(~F, n, bb, c, st), NP.one_nn(~F), ac1_nn(~F, n, bb, c, st, hb, hk)))

def sm3(~F: O.OField, +n: Nat, +bb: O.C(F), +c: Nat, +st: KS(~F), +w: Nat, +hb: O.le(~F, O.zero(F), bb), +hk: KNN(~F, st), +hA: O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), acoef(~F, n, bb, c, st)), O.one(F))) -> O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), ac3(~F, n, bb, st)), O.one(F)):
  upart_r(~F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), O.add(F, O.add(F, O.one(F), ac1(~F, n, bb, c, st)), ac2(~F, bb, st)), ac3(~F, n, bb, st), hA, u_nn(~F, w), FO.nonneg_add(~F, O.add(F, O.one(F), ac1(~F, n, bb, c, st)), ac2(~F, bb, st), FO.nonneg_add(~F, O.one(F), ac1(~F, n, bb, c, st), NP.one_nn(~F), ac1_nn(~F, n, bb, c, st, hb, hk)), ac2_nn(~F, bb, st, hb, hk)))

def lt_n(~F: O.OField, +s: M.Mat(~F), +n: Nat, +r: Nat, +hns: {GJ.nrows(~F, s) == n : Nat}, +h: {KA.natle(1n+r, GJ.nrows(~F, s)) == True{} : Bool}) -> {KA.natle(1n+r, n) == True{} : Bool}:
  %hns : {KA.natle(1n+r, _) == True{} : Bool}
  h

# the pivot's size bounds the candidates' size
def hmp_of(~F: O.OField, +rows: List<&2, List<&2, S.D>>, +c: Nat, +r: Nat, +hc: {KA.natle(1n+c, GJ.nrows(~F, M.ofdm(~F, rows))) == True{} : Bool}) -> O.le(~F, M.ofd(~F, NU.dabs(NU.dget(NU.drow(rows, r), c))), FV.fabs(~F, M.ofd(~F, NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)))):
  %Equal.sym(O.C(F), M.ofd(~F, NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), M.ofd(~F, NU.dget(NU.drow(rows, r), c)), piv_swap(~F, rows, c, r, hc)) : O.le(~F, M.ofd(~F, NU.dabs(NU.dget(NU.drow(rows, r), c))), FV.fabs(~F, _))
  BP.kabs_le(~KI.dnum(), ~F, ~KI.demb(~F), NU.dget(NU.drow(rows, r), c), FV.fabs(~F, M.ofd(~F, NU.dget(NU.drow(rows, r), c))), FV.fabs_bnd(~F, M.ofd(~F, NU.dget(NU.drow(rows, r), c))))

def hzf(~F: O.OField, +rows: List<&2, List<&2, S.D>>, +c: Nat, +r: Nat, +bb: O.C(F), +hh: O.C(F), +hc: {KA.natle(1n+c, GJ.nrows(~F, M.ofdm(~F, rows))) == True{} : Bool}, +h1: O.le(~F, O.one(F), O.mul(F, O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), M.ofd(~F, NU.dabs(NU.dget(NU.drow(rows, r), c))))), +hb0: O.le(~F, O.zero(F), O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh))), e: {M.ofd(~F, NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)) == O.zero(F) : O.C(F)}) -> Empty:
  pnz(~F, NU.dget(NU.drow(rows, r), c), O.add(F, O.mul(F, bb, hh), O.mul(F, bb, hh)), h1, hb0, Equal.trans(O.C(F), M.ofd(~F, NU.dget(NU.drow(rows, r), c)), M.ofd(~F, NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), O.zero(F), Equal.sym(O.C(F), M.ofd(~F, NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), M.ofd(~F, NU.dget(NU.drow(rows, r), c)), piv_swap(~F, rows, c, r, hc)), e))

# the swapped rows keep an inverse of the right halves
def invs(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +rows: List<&2, List<&2, S.D>>, +c: Nat, +r: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +hh: O.C(F), +hR: NP.InvB(~F, rmat(~F, n, M.ofdm(~F, rows)), n, hh), +hns: {GJ.nrows(~F, M.ofdm(~F, rows)) == n : Nat}, +hc: {KA.natle(1n+c, GJ.nrows(~F, M.ofdm(~F, rows))) == True{} : Bool}, +hr: {KA.natle(1n+r, GJ.nrows(~F, M.ofdm(~F, rows))) == True{} : Bool}, +hsw: rinv(~F, n, jm, M.ofdm(~F, NU.dswap(rows, c, r)), 0n, c, gg, dd, ph), +hnt: {GJ.nrows(~F, M.ofdm(~F, NU.dswap(rows, c, r))) == n : Nat}) -> NP.InvB(~F, rmat(~F, n, M.ofdm(~F, NU.dswap(rows, c, r))), n, hh):
  %Equal.sym(M.Mat(~F), M.ofdm(~F, NU.dswap(rows, c, r)), GJ.mswap(~F, M.ofdm(~F, rows), c, r), dswap_ofd(~F, rows, c, r)) : NP.InvB(~F, rmat(~F, n, _), n, hh)
  swap_invb(~F, n, M.ofdm(~F, rows), c, r, hh, hR, hns, hc, hr,
    (%dswap_ofd(~F, rows, c, r) : GJ.All(~(i => GJ.roww(~F, rmat(~F, n, _), n, i)), n)
      rw_all(~F, n, jm, M.ofdm(~F, NU.dswap(rows, c, r)), c, gg, dd, ph, hsw, hnt)))

# 1 <= 2 beta H |pivot|
def piv_bh(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +w: Nat, +rows: List<&2, List<&2, S.D>>, +c: Nat, +rest: Nat, +r: Nat, +g: O.C(F), +bb: O.C(F), +st: KS(~F), +hns: {GJ.nrows(~F, M.ofdm(~F, rows)) == n : Nat}, +h: rinv(~F, n, jm, M.ofdm(~F, rows), 0n, c, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), +hR: NP.InvB(~F, rmat(~F, n, M.ofdm(~F, rows)), n, kh(~F, st)), +hrest: {Nat.add(c, 1n+rest) == n : Nat}, +hr1: {KA.natle(c, r) == True{} : Bool}, +hr2: {KA.natle(1n+r, GJ.nrows(~F, M.ofdm(~F, rows))) == True{} : Bool}, +hcand: GJ.All(~(j => cb(~F, rows, c, c, M.ofd(~F, NU.dabs(NU.dget(NU.drow(rows, r), c))), j)), GJ.nrows(~F, M.ofdm(~F, rows))), +hJ: NP.InvB(~F, jm, n, bb), +hjn: {GJ.nrows(~F, jm) == n : Nat}, +hj: mall(~F, jm, g), +hg: O.le(~F, O.zero(F), g), +hb: O.le(~F, O.zero(F), bb), +hk: KNN(~F, st), +hA: O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), acoef(~F, n, bb, c, st)), O.one(F))) -> O.le(~F, O.one(F), O.mul(F, O.add(F, O.mul(F, bb, kh(~F, st)), O.mul(F, bb, kh(~F, st))), M.ofd(~F, NU.dabs(NU.dget(NU.drow(rows, r), c))))):
  piv_two(~F, n, c, bb, kh(~F, st), kg(~F, st), kd(~F, st), kp(~F, st), M.ofd(~F, NU.dabs(NU.dget(NU.drow(rows, r), c))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}),
    kern(~F, n, jm, M.ofdm(~F, rows), c, rest, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), M.ofd(~F, NU.dabs(NU.dget(NU.drow(rows, r), c))), h, hns, hrest, cbF(~F, rows, c, M.ofd(~F, NU.dabs(NU.dget(NU.drow(rows, r), c))), n, hcand, hns), KA.kabs_nonneg(~KI.dnum(), ~F, ~KI.demb(~F), NU.dget(NU.drow(rows, r), c)), knn_g(~F, st, hk), FO.mul_nonneg(~F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), knn_d(~F, st, hk), u_nn(~F, w)), FO.mul_nonneg(~F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), knn_p(~F, st, hk), u_nn(~F, w)), bb, kh(~F, st), hJ, hjn, hR),
    sm1(~F, n, bb, c, st, w, hb, hk, hA))

# one column, under the column-c constants: the column-(c+1) constants
def col_full(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +w: Nat, +rows: List<&2, List<&2, S.D>>, +c: Nat, +rest: Nat, +r: Nat, +g: O.C(F), +bb: O.C(F), +st: KS(~F), +hns: {GJ.nrows(~F, M.ofdm(~F, rows)) == n : Nat}, +h: rinv(~F, n, jm, M.ofdm(~F, rows), 0n, c, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), +hR: NP.InvB(~F, rmat(~F, n, M.ofdm(~F, rows)), n, kh(~F, st)), +hrest: {Nat.add(c, 1n+rest) == n : Nat}, +hr1: {KA.natle(c, r) == True{} : Bool}, +hr2: {KA.natle(1n+r, GJ.nrows(~F, M.ofdm(~F, rows))) == True{} : Bool}, +hcand: GJ.All(~(j => cb(~F, rows, c, c, M.ofd(~F, NU.dabs(NU.dget(NU.drow(rows, r), c))), j)), GJ.nrows(~F, M.ofdm(~F, rows))), +hJ: NP.InvB(~F, jm, n, bb), +hjn: {GJ.nrows(~F, jm) == n : Nat}, +hj: mall(~F, jm, g), +hg: O.le(~F, O.zero(F), g), +hb: O.le(~F, O.zero(F), bb), +hk: KNN(~F, st), +hA: O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), acoef(~F, n, bb, c, st)), O.one(F))) -> M.Both(rinv(~F, n, jm, M.ofdm(~F, NU.delim(w, NU.dswap(rows, c, r), c)), 0n, 1n+c, kg(~F, kstep(~F, n, g, bb, st)), O.mul(F, kd(~F, kstep(~F, n, g, bb, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kstep(~F, n, g, bb, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), NP.InvB(~F, rmat(~F, n, M.ofdm(~F, NU.delim(w, NU.dswap(rows, c, r), c))), n, kh(~F, kstep(~F, n, g, bb, st)))):
  +hu = sm_u(~F, n, bb, c, st, w, hb, hk, hA)
  +hg0 = knn_g(~F, st, hk)
  +hh0 = knn_h(~F, st, hk)
  +hdd = FO.mul_nonneg(~F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), knn_d(~F, st, hk), u_nn(~F, w))
  +hph = FO.mul_nonneg(~F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), knn_p(~F, st, hk), u_nn(~F, w))
  +hb0 = FO.nonneg_add(~F, O.mul(F, bb, kh(~F, st)), O.mul(F, bb, kh(~F, st)), FO.mul_nonneg(~F, bb, kh(~F, st), hb, hh0), FO.mul_nonneg(~F, bb, kh(~F, st), hb, hh0))
  +hs0 = FO.nonneg_add(~F, O.mul(F, O.add(F, bb, bb), kh(~F, st)), O.mul(F, O.add(F, bb, bb), kh(~F, st)), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), hh0), FO.mul_nonneg(~F, O.add(F, bb, bb), kh(~F, st), FO.nonneg_add(~F, bb, bb, hb, hb), hh0))
  +h1 = piv_bh(~F, n, jm, w, rows, c, rest, r, g, bb, st, hns, h, hR, hrest, hr1, hr2, hcand, hJ, hjn, hj, hg, hb, hk, hA)
  +hql = qle(~F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)))), M.ofd(~F, NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), M.ofd(~F, NU.dabs(NU.dget(NU.drow(rows, r), c))), O.add(F, O.mul(F, bb, kh(~F, st)), O.mul(F, bb, kh(~F, st))), h1, hmp_of(~F, rows, c, r, his(~F, M.ofdm(~F, rows), n, c, hns, hc1(c, rest, n, hrest))), div_rel(~F, NU.dget(NU.drow(NU.dswap(rows, c, r), c), c), (e => hzf(~F, rows, c, r, bb, kh(~F, st), his(~F, M.ofdm(~F, rows), n, c, hns, hc1(c, rest, n, hrest)), h1, hb0, e))), hb0)
  +hsg = FM.bnd_mono(~F, M.ofd(~F, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c))), O.add(F, FV.fabs(~F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(NU.dget(NU.drow(NU.dswap(rows, c, r), c), c))))), O.mul(F, FV.fabs(~F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(NU.dget(NU.drow(NU.dswap(rows, c, r), c), c))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), sgb(~F, bb, kh(~F, st)), s_bnd(~F, w, NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), FM.sub_nonneg(~F, O.add(F, FV.fabs(~F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(NU.dget(NU.drow(NU.dswap(rows, c, r), c), c))))), O.mul(F, FV.fabs(~F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(NU.dget(NU.drow(NU.dswap(rows, c, r), c), c))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), sgb(~F, bb, kh(~F, st)), sg_le(~F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), bb, kh(~F, st), hql, hu)))
  +hep = FO.mul_nonneg(~F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), FO.mul_nonneg(~F, sgb(~F, bb, kh(~F, st)), kg(~F, st), hs0, hg0), u_nn(~F, w))
  +hpe = dscale_err(~F, w, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), NU.drow(NU.dswap(rows, c, r), c), sgb(~F, bb, kh(~F, st)), kg(~F, st), hsg, ri_e(~F, n, jm, M.ofdv(~F, NU.drow(NU.dswap(rows, c, r), c)), c, c, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), col_hx(~F, n, jm, rows, c, r, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), swap_ok(~F, n, jm, rows, c, r, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), h, hns, hc1(c, rest, n, hrest), hr1, lt_n(~F, M.ofdm(~F, rows), n, r, hns, hr2)), Equal.trans(Nat, GJ.nrows(~F, M.ofdm(~F, NU.dswap(rows, c, r))), GJ.nrows(~F, M.ofdm(~F, rows)), n, nrows_dswap(~F, rows, c, r), hns), hc1(c, rest, n, hrest))))
  +lp = Equal.trans(Nat, M.len(~F, M.ofdv(~F, NU.dscale(w, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), NU.drow(NU.dswap(rows, c, r), c)))), M.len(~F, M.ofdv(~F, NU.drow(NU.dswap(rows, c, r), c))), Nat.add(n, n), len_dscale(~F, w, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), NU.drow(NU.dswap(rows, c, r), c)), ri_len(~F, n, jm, M.ofdv(~F, NU.drow(NU.dswap(rows, c, r), c)), c, c, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), col_hx(~F, n, jm, rows, c, r, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), swap_ok(~F, n, jm, rows, c, r, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), h, hns, hc1(c, rest, n, hrest), hr1, lt_n(~F, M.ofdm(~F, rows), n, r, hns, hr2)), Equal.trans(Nat, GJ.nrows(~F, M.ofdm(~F, NU.dswap(rows, c, r))), GJ.nrows(~F, M.ofdm(~F, rows)), n, nrows_dswap(~F, rows, c, r), hns), hc1(c, rest, n, hrest))))
  +rcs = col_step(~F, n, jm, w, rows, c, r, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), g, sgb(~F, bb, kh(~F, st)), h, hns, Equal.trans(Nat, GJ.nrows(~F, M.ofdm(~F, NU.dswap(rows, c, r))), GJ.nrows(~F, M.ofdm(~F, rows)), n, nrows_dswap(~F, rows, c, r), hns), hc1(c, rest, n, hrest), hr1, lt_n(~F, M.ofdm(~F, rows), n, r, hns, hr2), (e => hzf(~F, rows, c, r, bb, kh(~F, st), his(~F, M.ofdm(~F, rows), n, c, hns, hc1(c, rest, n, hrest)), h1, hb0, e)), hsg, hg0, hdd, hph, hj, hg, hjn, hu)
  (rinv_mono(~F, n, jm, M.ofdm(~F, NU.delim(w, NU.dswap(rows, c, r), c)), 0n, 1n+c, gnew(~F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), dnew(~F, n, g, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))), O.mul(F, O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), pnew(~F, kg(~F, st), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), kg(~F, kstep(~F, n, g, bb, st)), O.mul(F, kd(~F, kstep(~F, n, g, bb, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kstep(~F, n, g, bb, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), rcs, gw(~F, sgb(~F, bb, kh(~F, st)), kg(~F, st), w, hs0, hg0, hu), dw(~F, n, g, sgb(~F, bb, kh(~F, st)), kg(~F, st), kd(~F, st), w, hs0, hg0, hg, hu), pw(~F, sgb(~F, bb, kh(~F, st)), kg(~F, st), kp(~F, st), w, hs0, hg0, hu)),
    col_low(~F, n, jm, w, NU.dswap(rows, c, r), c, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), NU.dscale(w, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), NU.drow(NU.dswap(rows, c, r), c)), M.ofd(~F, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c))), O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)))), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), swap_ok(~F, n, jm, rows, c, r, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), h, hns, hc1(c, rest, n, hrest), hr1, lt_n(~F, M.ofdm(~F, rows), n, r, hns, hr2)), his(~F, M.ofdm(~F, NU.dswap(rows, c, r)), n, c, Equal.trans(Nat, GJ.nrows(~F, M.ofdm(~F, NU.dswap(rows, c, r))), GJ.nrows(~F, M.ofdm(~F, rows)), n, nrows_dswap(~F, rows, c, r), hns), hc1(c, rest, n, hrest)), (%dget_ofd(~F, NU.drow(NU.dswap(rows, c, r), c), c) : {O.mul(F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)))), _) == O.one(F) : O.C(F)} div_rel(~F, NU.dget(NU.drow(NU.dswap(rows, c, r), c), c), (e => hzf(~F, rows, c, r, bb, kh(~F, st), his(~F, M.ofdm(~F, rows), n, c, hns, hc1(c, rest, n, hrest)), h1, hb0, e)))), s_err(~F, w, NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)),
      hsm_of(~F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), bb, kh(~F, st), kg(~F, st), hql, sm2(~F, n, bb, c, st, w, hb, hk, hA), u_nn(~F, w), hg0), hpe, hep,
      ri_e(~F, n, jm, M.ofdv(~F, NU.dscale(w, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), NU.drow(NU.dswap(rows, c, r), c))), c, 1n+c, O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))), O.add(F, O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))),
        prow(~F, n, jm, M.ofdv(~F, NU.drow(NU.dswap(rows, c, r), c)), c, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), col_hx(~F, n, jm, rows, c, r, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), swap_ok(~F, n, jm, rows, c, r, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), h, hns, hc1(c, rest, n, hrest), hr1, lt_n(~F, M.ofdm(~F, rows), n, r, hns, hr2)), Equal.trans(Nat, GJ.nrows(~F, M.ofdm(~F, NU.dswap(rows, c, r))), GJ.nrows(~F, M.ofdm(~F, rows)), n, nrows_dswap(~F, rows, c, r), hns), hc1(c, rest, n, hrest)), hg0, hph, M.ofd(~F, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c))), sgb(~F, bb, kh(~F, st)), O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), hsg, (%dget_ofd(~F, NU.drow(NU.dswap(rows, c, r), c), c) : {O.mul(F, O.ofq(~F, S.Q.div(S.D.toq(NU.done()), S.D.toq(NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)))), _) == O.one(F) : O.C(F)} div_rel(~F, NU.dget(NU.drow(NU.dswap(rows, c, r), c), c), (e => hzf(~F, rows, c, r, bb, kh(~F, st), his(~F, M.ofdm(~F, rows), n, c, hns, hc1(c, rest, n, hrest)), h1, hb0, e)))), s_err(~F, w, NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), u_nn(~F, w), M.ofdv(~F, NU.dscale(w, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), NU.drow(NU.dswap(rows, c, r), c))), lp, O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), hpe, hep, g, hj, hg, hjn)),
      lp, hg0, FO.nonneg_add(~F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FO.mul_nonneg(~F, sgb(~F, bb, kh(~F, st)), kg(~F, st), hs0, hg0), hep), hu, Equal.trans(Nat, GJ.nrows(~F, M.ofdm(~F, NU.dswap(rows, c, r))), GJ.nrows(~F, M.ofdm(~F, rows)), n, nrows_dswap(~F, rows, c, r), hns), kh(~F, st),
      invs(~F, n, jm, rows, c, r, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), kh(~F, st), hR, hns, his(~F, M.ofdm(~F, rows), n, c, hns, hc1(c, rest, n, hrest)), hr2, swap_ok(~F, n, jm, rows, c, r, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), h, hns, hc1(c, rest, n, hrest), hr1, lt_n(~F, M.ofdm(~F, rows), n, r, hns, hr2)), Equal.trans(Nat, GJ.nrows(~F, M.ofdm(~F, NU.dswap(rows, c, r))), GJ.nrows(~F, M.ofdm(~F, rows)), n, nrows_dswap(~F, rows, c, r), hns)),
      hB_of(~F, n, sgb(~F, bb, kh(~F, st)), kg(~F, st), kh(~F, st), w, sm3(~F, n, bb, c, st, w, hb, hk, hA), hs0, hg0, hh0, hu),
      gnew(~F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), dnew(~F, n, g, kg(~F, st), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), O.mul(F, kd(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), g)))), O.mul(F, O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), pnew(~F, kg(~F, st), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.add(F, O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), O.mul(F, kp(~F, st), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), O.mul(F, O.add(F, kg(~F, st), O.add(F, O.add(F, O.mul(F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))), O.mul(F, kg(~F, st), O.add(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), O.mul(F, O.mul(F, sgb(~F, bb, kh(~F, st)), kg(~F, st)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), rcs, Equal.trans(Nat, GJ.nrows(~F, M.ofdm(~F, NU.delim(w, NU.dswap(rows, c, r), c))), GJ.nrows(~F, M.ofdm(~F, NU.dswap(rows, c, r))), n, nrows_dclear(~F, NU.dswap(rows, c, r), w, NU.dscale(w, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), NU.drow(NU.dswap(rows, c, r), c)), c, 0n), Equal.trans(Nat, GJ.nrows(~F, M.ofdm(~F, NU.dswap(rows, c, r))), GJ.nrows(~F, M.ofdm(~F, rows)), n, nrows_dswap(~F, rows, c, r), hns))))


# The columns in turn
# -------------------

def bfst(-A: Data, -B: Data, h: M.Both(A, B)) -> A:
  match h:
    case (a, b):
      a

def bsnd(-A: Data, -B: Data, h: M.Both(A, B)) -> B:
  match h:
    case (a, b):
      b

# what the elimination ends with: n rows under the column-n constants
def dres(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +g: O.C(F), +bb: O.C(F), +w: Nat, res: Maybe<&2, List<&2, List<&2, S.D>>>) -> Type:
  match res:
    case None{}:
      Empty
    case Some{s}:
      M.Both({GJ.nrows(~F, M.ofdm(~F, s)) == n : Nat}, rinv(~F, n, jm, M.ofdm(~F, s), 0n, n, kg(~F, kst(~F, n, g, bb, n)), O.mul(F, kd(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))

# dgj with k columns left, from column c with its constants and the pivot
# search's result
def dgj_ok(~F: O.OField, k: Nat, +w: Nat, +c: Nat, piv: Maybe<&2, Nat>, +rows: List<&2, List<&2, S.D>>, +n: Nat, +jm: M.Mat(~F), +g: O.C(F), +bb: O.C(F), +hkc: {Nat.add(c, k) == n : Nat}, +hns: {GJ.nrows(~F, M.ofdm(~F, rows)) == n : Nat}, +hs: M.Both(rinv(~F, n, jm, M.ofdm(~F, rows), 0n, c, kg(~F, kst(~F, n, g, bb, c)), O.mul(F, kd(~F, kst(~F, n, g, bb, c)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kst(~F, n, g, bb, c)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), NP.InvB(~F, rmat(~F, n, M.ofdm(~F, rows)), n, kh(~F, kst(~F, n, g, bb, c)))), hp: pfin(~F, rows, c, c, GJ.nrows(~F, M.ofdm(~F, rows)), piv), +hJ: NP.InvB(~F, jm, n, bb), +hjn: {GJ.nrows(~F, jm) == n : Nat}, +hj: mall(~F, jm, g), +hg: O.le(~F, O.zero(F), g), +hb: O.le(~F, O.zero(F), bb), +hsm: GJ.All(~(q => O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), acoef(~F, n, bb, q, kst(~F, n, g, bb, q))), O.one(F))), n)) -> dres(~F, n, jm, g, bb, w, NU.dgj(k, w, c, piv, rows)):
  match k piv:
    case 0n piv:
      (hns, (%Equal.trans(Nat, c, Nat.add(c, 0n), n, LN.add_zero(c), hkc) : rinv(~F, n, jm, M.ofdm(~F, rows), 0n, _, kg(~F, kst(~F, n, g, bb, _)), O.mul(F, kd(~F, kst(~F, n, g, bb, _)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kst(~F, n, g, bb, _)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))
        bfst(rinv(~F, n, jm, M.ofdm(~F, rows), 0n, c, kg(~F, kst(~F, n, g, bb, c)), O.mul(F, kd(~F, kst(~F, n, g, bb, c)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kst(~F, n, g, bb, c)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), NP.InvB(~F, rmat(~F, n, M.ofdm(~F, rows)), n, kh(~F, kst(~F, n, g, bb, c))), hs)))
    case 1n++kk None{}:
      RL.le_lt_absurd(~F, O.one(F), O.zero(F),
        (%FR.fring_eq(~F, [bb, kh(~F, kst(~F, n, g, bb, c))], E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==}) : O.le(~F, O.one(F), _)
          piv_two(~F, n, c, bb, kh(~F, kst(~F, n, g, bb, c)), kg(~F, kst(~F, n, g, bb, c)), kd(~F, kst(~F, n, g, bb, c)), kp(~F, kst(~F, n, g, bb, c)), O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}),
            kern(~F, n, jm, M.ofdm(~F, rows), c, kk, kg(~F, kst(~F, n, g, bb, c)), O.mul(F, kd(~F, kst(~F, n, g, bb, c)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kst(~F, n, g, bb, c)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.zero(F), bfst(rinv(~F, n, jm, M.ofdm(~F, rows), 0n, c, kg(~F, kst(~F, n, g, bb, c)), O.mul(F, kd(~F, kst(~F, n, g, bb, c)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kst(~F, n, g, bb, c)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), NP.InvB(~F, rmat(~F, n, M.ofdm(~F, rows)), n, kh(~F, kst(~F, n, g, bb, c))), hs), hns, hkc, cbF(~F, rows, c, O.zero(F), n, hp, hns), FO.le_refl(~F, O.zero(F)), knn_g(~F, kst(~F, n, g, bb, c), kst_nn(~F, n, g, bb, hg, hb, c)), FO.mul_nonneg(~F, kd(~F, kst(~F, n, g, bb, c)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), knn_d(~F, kst(~F, n, g, bb, c), kst_nn(~F, n, g, bb, hg, hb, c)), u_nn(~F, w)), FO.mul_nonneg(~F, kp(~F, kst(~F, n, g, bb, c)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), knn_p(~F, kst(~F, n, g, bb, c), kst_nn(~F, n, g, bb, hg, hb, c)), u_nn(~F, w)), bb, kh(~F, kst(~F, n, g, bb, c)), hJ, hjn, bsnd(rinv(~F, n, jm, M.ofdm(~F, rows), 0n, c, kg(~F, kst(~F, n, g, bb, c)), O.mul(F, kd(~F, kst(~F, n, g, bb, c)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kst(~F, n, g, bb, c)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), NP.InvB(~F, rmat(~F, n, M.ofdm(~F, rows)), n, kh(~F, kst(~F, n, g, bb, c))), hs)),
            sm1(~F, n, bb, c, kst(~F, n, g, bb, c), w, hb, kst_nn(~F, n, g, bb, hg, hb, c), GJ.all_at(~(q => O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), acoef(~F, n, bb, q, kst(~F, n, g, bb, q))), O.one(F))), n, hsm, c, hc1(c, kk, n, hkc))))),
        O.zero_lt_one(F))
    case 1n++kk Some{+r}:
      (hr1, hq) = hp
      (hr2, hcand) = hq
      dgj_ok(~F, kk, w, 1n+c, NU.dpivot(NU.delim(w, NU.dswap(rows, c, r), c), 1n+c, 1n+c, 0n, None{}, NU.dzero()), NU.delim(w, NU.dswap(rows, c, r), c), n, jm, g, bb,
        Equal.trans(Nat, 1n+Nat.add(c, kk), Nat.add(c, 1n+kk), n, LN.add_succ(c, kk), hkc),
        Equal.trans(Nat, GJ.nrows(~F, M.ofdm(~F, NU.delim(w, NU.dswap(rows, c, r), c))), GJ.nrows(~F, M.ofdm(~F, NU.dswap(rows, c, r))), n, nrows_dclear(~F, NU.dswap(rows, c, r), w, NU.dscale(w, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(NU.dswap(rows, c, r), c), c)), NU.drow(NU.dswap(rows, c, r), c)), c, 0n), Equal.trans(Nat, GJ.nrows(~F, M.ofdm(~F, NU.dswap(rows, c, r))), GJ.nrows(~F, M.ofdm(~F, rows)), n, nrows_dswap(~F, rows, c, r), hns)),
        col_full(~F, n, jm, w, rows, c, kk, r, g, bb, kst(~F, n, g, bb, c), hns, bfst(rinv(~F, n, jm, M.ofdm(~F, rows), 0n, c, kg(~F, kst(~F, n, g, bb, c)), O.mul(F, kd(~F, kst(~F, n, g, bb, c)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kst(~F, n, g, bb, c)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), NP.InvB(~F, rmat(~F, n, M.ofdm(~F, rows)), n, kh(~F, kst(~F, n, g, bb, c))), hs), bsnd(rinv(~F, n, jm, M.ofdm(~F, rows), 0n, c, kg(~F, kst(~F, n, g, bb, c)), O.mul(F, kd(~F, kst(~F, n, g, bb, c)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kst(~F, n, g, bb, c)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), NP.InvB(~F, rmat(~F, n, M.ofdm(~F, rows)), n, kh(~F, kst(~F, n, g, bb, c))), hs), hkc, hr1, hr2, hcand, hJ, hjn, hj, hg, hb, kst_nn(~F, n, g, bb, hg, hb, c), GJ.all_at(~(q => O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), acoef(~F, n, bb, q, kst(~F, n, g, bb, q))), O.one(F))), n, hsm, c, hc1(c, kk, n, hkc))),
        pivot_ok(~F, NU.delim(w, NU.dswap(rows, c, r), c), 1n+c), hJ, hjn, hj, hg, hb, hsm)

# The start: rows [J | I]
# -----------------------

def ofdv_app(~F: O.OField, xs: List<&2, S.D>, +ys: List<&2, S.D>) -> {M.ofdv(~F, NU.dapp(xs, ys)) == GJ.vapp(~F, M.ofdv(~F, xs), M.ofdv(~F, ys)) : M.Vec(~F)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, t}:
      %Equal.sym(M.Vec(~F), M.ofdv(~F, NU.dapp(t, ys)), GJ.vapp(~F, M.ofdv(~F, t), M.ofdv(~F, ys)), ofdv_app(~F, t, ys)) : {Con{M.ofd(~F, h), _} == Con{M.ofd(~F, h), GJ.vapp(~F, M.ofdv(~F, t), M.ofdv(~F, ys))} : M.Vec(~F)}
      {==}

def ofdv_zeros(~F: O.OField, m: Nat) -> {M.ofdv(~F, NU.dzeros(m)) == GJ.zeros(~F, m) : M.Vec(~F)}:
  match m:
    case 0n:
      {==}
    case 1n++j:
      %DM.ofd_zero(~F) : {Con{_, M.ofdv(~F, NU.dzeros(j))} == Con{O.zero(F), GJ.zeros(~F, j)} : M.Vec(~F)}
      %Equal.sym(M.Vec(~F), M.ofdv(~F, NU.dzeros(j)), GJ.zeros(~F, j), ofdv_zeros(~F, j)) : {Con{O.zero(F), _} == Con{O.zero(F), GJ.zeros(~F, j)} : M.Vec(~F)}
      {==}

def ofdv_unit(~F: O.OField, n: Nat, k: Nat) -> {M.ofdv(~F, NU.dunit(n, k)) == GJ.unit(~F, n, k) : M.Vec(~F)}:
  match n k:
    case 0n k:
      {==}
    case 1n++m 0n:
      %DM.ofd_one(~F) : {Con{_, M.ofdv(~F, NU.dzeros(m))} == Con{O.one(F), GJ.zeros(~F, m)} : M.Vec(~F)}
      %Equal.sym(M.Vec(~F), M.ofdv(~F, NU.dzeros(m)), GJ.zeros(~F, m), ofdv_zeros(~F, m)) : {Con{O.one(F), _} == Con{O.one(F), GJ.zeros(~F, m)} : M.Vec(~F)}
      {==}
    case 1n++m 1n++j:
      %DM.ofd_zero(~F) : {Con{_, M.ofdv(~F, NU.dunit(m, j))} == Con{O.zero(F), GJ.unit(~F, m, j)} : M.Vec(~F)}
      %Equal.sym(M.Vec(~F), M.ofdv(~F, NU.dunit(m, j)), GJ.unit(~F, m, j), ofdv_unit(~F, m, j)) : {Con{O.zero(F), _} == Con{O.zero(F), GJ.unit(~F, m, j)} : M.Vec(~F)}
      {==}

# row i of the augmented rows is J_i followed by e_i
def aug_row(~F: O.OField, a: List<&2, List<&2, S.D>>, +n: Nat, +k: Nat, i: Nat, hi: {KA.natle(1n+i, GJ.nrows(~F, M.ofdm(~F, a))) == True{} : Bool}) -> {DV.mrow(~F, M.ofdm(~F, NU.daugment(a, n, k)), i) == GJ.vapp(~F, DV.mrow(~F, M.ofdm(~F, a), i), GJ.unit(~F, n, Nat.add(i, k))) : M.Vec(~F)}:
  match a i:
    case Nil{} 0n:
      FO.absurd({Nil{} == GJ.vapp(~F, Nil{}, GJ.unit(~F, n, k)) : M.Vec(~F)}, KA.ft(hi))
    case Nil{} 1n++j:
      FO.absurd({Nil{} == GJ.vapp(~F, Nil{}, GJ.unit(~F, n, 1n+Nat.add(j, k))) : M.Vec(~F)}, KA.ft(hi))
    case Con{+r, t} 0n:
      %ofdv_unit(~F, n, k) : {M.ofdv(~F, NU.dapp(r, NU.dunit(n, k))) == GJ.vapp(~F, M.ofdv(~F, r), _) : M.Vec(~F)}
      ofdv_app(~F, r, NU.dunit(n, k))
    case Con{r, t} 1n++j:
      %Equal.sym(Nat, 1n+Nat.add(j, k), Nat.add(j, 1n+k), LN.add_succ(j, k)) : {DV.mrow(~F, M.ofdm(~F, NU.daugment(t, n, 1n+k)), j) == GJ.vapp(~F, DV.mrow(~F, M.ofdm(~F, t), j), GJ.unit(~F, n, _)) : M.Vec(~F)}
      aug_row(~F, t, n, 1n+k, j, hi)

def look_app_lo(~F: O.OField, p: M.Vec(~F), +q: M.Vec(~F), k: Nat, h: {KA.natle(1n+k, M.len(~F, p)) == True{} : Bool}) -> {O.lookup(~F, p, k) == O.lookup(~F, GJ.vapp(~F, p, q), k) : O.C(F)}:
  match p k:
    case Nil{} k:
      FO.absurd({O.lookup(~F, Nil{}, k) == O.lookup(~F, q, k) : O.C(F)}, KA.ft(h))
    case Con{a, t} 0n:
      {==}
    case Con{a, t} 1n+j:
      look_app_lo(~F, t, q, j, h)

def drop_app(~F: O.OField, p: M.Vec(~F), +q: M.Vec(~F)) -> {GJ.vdrop(~F, M.len(~F, p), GJ.vapp(~F, p, q)) == q : M.Vec(~F)}:
  match p:
    case Nil{}:
      match q:
        case Nil{}:
          {==}
        case Con{x, xs}:
          {==}
    case Con{a, t}:
      drop_app(~F, t, q)

def vall_unit(~F: O.OField, n: Nat, i: Nat) -> M.vbnd.all(~F, GJ.unit(~F, n, i), O.one(F)):
  match n i:
    case 0n i:
      Unit{}
    case 1n++k 0n:
      (FV.bnd_self(~F, O.one(F), NP.one_nn(~F)), FM.vall_mono(~F, GJ.zeros(~F, k), O.zero(F), O.one(F), NP.vall_zeros(~F, k), FM.sub_nonneg(~F, O.zero(F), O.one(F), NP.one_nn(~F))))
    case 1n++k 1n+j:
      (FM.bnd_zero(~F, O.one(F), NP.one_nn(~F)), vall_unit(~F, k, j))

def mall_row(~F: O.OField, a: M.Mat(~F), +g: O.C(F), i: Nat, h: mall(~F, a, g)) -> M.vbnd.all(~F, DV.mrow(~F, a, i), g):
  match a i:
    case Nil{} i:
      Unit{}
    case Con{r, t} 0n:
      (h1, h2) = h
      h1
    case Con{r, t} 1n+j:
      (h1, h2) = h
      mall_row(~F, t, g, j, h2)

# the start row J_i e_i: entries <= g + 1, no defect
def dk0(~F: O.OField, +n: Nat, +a: List<&2, List<&2, S.D>>, +i: Nat, +k: Nat, +hw: GJ.roww(~F, M.ofdm(~F, a), n, i), +hjn: {GJ.nrows(~F, M.ofdm(~F, a)) == n : Nat}, +hk: {KA.natle(1n+k, n) == True{} : Bool}) -> {O.zero(F) == dk(~F, n, M.ofdm(~F, a), GJ.vapp(~F, DV.mrow(~F, M.ofdm(~F, a), i), GJ.unit(~F, n, i)), k) : O.C(F)}:
  %look_app_lo(~F, DV.mrow(~F, M.ofdm(~F, a), i), GJ.unit(~F, n, i), k, (%Equal.sym(Nat, M.len(~F, DV.mrow(~F, M.ofdm(~F, a), i)), n, hw) : {KA.natle(1n+k, _) == True{} : Bool}
      hk)) : {O.zero(F) == O.sub(~F, _, M.dot(~F, GJ.vdrop(~F, n, GJ.vapp(~F, DV.mrow(~F, M.ofdm(~F, a), i), GJ.unit(~F, n, i))), GJ.mcol(~F, M.ofdm(~F, a), k))) : O.C(F)}
  %hw : {O.zero(F) == O.sub(~F, O.lookup(~F, DV.mrow(~F, M.ofdm(~F, a), i), k), M.dot(~F, GJ.vdrop(~F, _, GJ.vapp(~F, DV.mrow(~F, M.ofdm(~F, a), i), GJ.unit(~F, n, i))), GJ.mcol(~F, M.ofdm(~F, a), k))) : O.C(F)}
  %Equal.sym(M.Vec(~F), GJ.vdrop(~F, M.len(~F, DV.mrow(~F, M.ofdm(~F, a), i)), GJ.vapp(~F, DV.mrow(~F, M.ofdm(~F, a), i), GJ.unit(~F, n, i))), GJ.unit(~F, n, i), drop_app(~F, DV.mrow(~F, M.ofdm(~F, a), i), GJ.unit(~F, n, i))) : {O.zero(F) == O.sub(~F, O.lookup(~F, DV.mrow(~F, M.ofdm(~F, a), i), k), M.dot(~F, _, GJ.mcol(~F, M.ofdm(~F, a), k))) : O.C(F)}
  %GJ.dot_unit(~F, n, i, GJ.mcol(~F, M.ofdm(~F, a), k), (%GJ.len_mcol(~F, M.ofdm(~F, a), k) : {KA.natle(_, n) == True{} : Bool}
      (%hjn : {KA.natle(GJ.nrows(~F, M.ofdm(~F, a)), _) == True{} : Bool}
        GJ.le_refl(GJ.nrows(~F, M.ofdm(~F, a)))))) : {O.zero(F) == O.sub(~F, O.lookup(~F, DV.mrow(~F, M.ofdm(~F, a), i), k), _) : O.C(F)}
  %GJ.look_mcol(~F, M.ofdm(~F, a), k, i) : {O.zero(F) == O.sub(~F, O.lookup(~F, DV.mrow(~F, M.ofdm(~F, a), i), k), _) : O.C(F)}
  FR.fring_eq(~F, [O.lookup(~F, DV.mrow(~F, M.ofdm(~F, a), i), k)], E.ZCst{S.Z0{}}, E.ZSub{E.ZVar{0n}, E.ZVar{0n}}, {==})

def len_xi(~F: O.OField, +n: Nat, +a: List<&2, List<&2, S.D>>, +i: Nat, +hw: GJ.roww(~F, M.ofdm(~F, a), n, i)) -> {M.len(~F, GJ.vapp(~F, DV.mrow(~F, M.ofdm(~F, a), i), GJ.unit(~F, n, i))) == Nat.add(n, n) : Nat}:
  %GJ.len_vapp(~F, DV.mrow(~F, M.ofdm(~F, a), i), GJ.unit(~F, n, i)) : {_ == Nat.add(n, n) : Nat}
  %Equal.sym(Nat, M.len(~F, DV.mrow(~F, M.ofdm(~F, a), i)), n, hw) : {Nat.add(_, M.len(~F, GJ.unit(~F, n, i))) == Nat.add(n, n) : Nat}
  %GJ.len_unit(~F, n, i) : {Nat.add(n, _) == Nat.add(n, n) : Nat}
  {==}

# the start row J_i e_i, under the column-0 constants (any row index:
# no finished columns yet)
def row0(~F: O.OField, +n: Nat, +a: List<&2, List<&2, S.D>>, +g: O.C(F), +w: Nat, +i: Nat, +i2: Nat, +hw: GJ.roww(~F, M.ofdm(~F, a), n, i), +hjn: {GJ.nrows(~F, M.ofdm(~F, a)) == n : Nat}, +hj: mall(~F, M.ofdm(~F, a), g), +hg: O.le(~F, O.zero(F), g)) -> rowinv(~F, n, M.ofdm(~F, a), GJ.vapp(~F, DV.mrow(~F, M.ofdm(~F, a), i), GJ.unit(~F, n, i)), i2, 0n, O.add(F, g, O.one(F)), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))):
  ri_mk(~F, n, M.ofdm(~F, a), GJ.vapp(~F, DV.mrow(~F, M.ofdm(~F, a), i), GJ.unit(~F, n, i)), i2, 0n, O.add(F, g, O.one(F)), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), len_xi(~F, n, a, i, hw),
    vall_app(~F, DV.mrow(~F, M.ofdm(~F, a), i), GJ.unit(~F, n, i), O.add(F, g, O.one(F)), FM.vall_mono(~F, DV.mrow(~F, M.ofdm(~F, a), i), g, O.add(F, g, O.one(F)), mall_row(~F, M.ofdm(~F, a), g, i, hj), FM.sub_nonneg(~F, g, O.add(F, g, O.one(F)), le_addr(~F, g, O.one(F), NP.one_nn(~F)))), FM.vall_mono(~F, GJ.unit(~F, n, i), O.one(F), O.add(F, g, O.one(F)), vall_unit(~F, n, i), FM.sub_nonneg(~F, O.one(F), O.add(F, g, O.one(F)), le_addl(~F, g, O.one(F), hg)))),
    GJ.all_mk(~n, ~(k => M.bnd(~F, dk(~F, n, M.ofdm(~F, a), GJ.vapp(~F, DV.mrow(~F, M.ofdm(~F, a), i), GJ.unit(~F, n, i)), k), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), ~(k => hk => KB.bnd_val(~F, O.zero(F), dk(~F, n, M.ofdm(~F, a), GJ.vapp(~F, DV.mrow(~F, M.ofdm(~F, a), i), GJ.unit(~F, n, i)), k), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), dk0(~F, n, a, i, k, hw, hjn, hk), FM.bnd_zero(~F, O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), FO.mul_nonneg(~F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), FO.le_refl(~F, O.zero(F)), u_nn(~F, w))))), n, GJ.le_refl(n)),
    Unit{})

# rinv from every row's invariant
def rinv_of(~F: O.OField, +n: Nat, +jm: M.Mat(~F), s: M.Mat(~F), +i0: Nat, +c: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +h: GJ.All(~(k => rowinv(~F, n, jm, DV.mrow(~F, s, k), Nat.add(k, i0), c, gg, dd, ph)), GJ.nrows(~F, s))) -> rinv(~F, n, jm, s, i0, c, gg, dd, ph):
  match s:
    case Nil{}:
      Unit{}
    case Con{+x, +t}:
      (GJ.all_at(~(k => rowinv(~F, n, jm, DV.mrow(~F, Con{x, t}, k), Nat.add(k, i0), c, gg, dd, ph)), 1n+GJ.nrows(~F, t), h, 0n, {==}),
        rinv_of(~F, n, jm, t, 1n+i0, c, gg, dd, ph, all_map(~(k => rowinv(~F, n, jm, DV.mrow(~F, Con{x, t}, 1n+k), Nat.add(1n+k, i0), c, gg, dd, ph)), ~(k => rowinv(~F, n, jm, DV.mrow(~F, t, k), Nat.add(k, 1n+i0), c, gg, dd, ph)), ~(k => q =>
          (%LN.add_succ(k, i0) : rowinv(~F, n, jm, DV.mrow(~F, t, k), _, c, gg, dd, ph)
            q)), GJ.nrows(~F, t), all_shift(~(k => rowinv(~F, n, jm, DV.mrow(~F, Con{x, t}, k), Nat.add(k, i0), c, gg, dd, ph)), GJ.nrows(~F, t), h))))

def nrows_aug(~F: O.OField, a: List<&2, List<&2, S.D>>, +n: Nat, +k: Nat) -> {GJ.nrows(~F, M.ofdm(~F, NU.daugment(a, n, k))) == GJ.nrows(~F, M.ofdm(~F, a)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{r, t}:
      %Equal.sym(Nat, GJ.nrows(~F, M.ofdm(~F, NU.daugment(t, n, 1n+k))), GJ.nrows(~F, M.ofdm(~F, t)), nrows_aug(~F, t, n, 1n+k)) : {1n+_ == 1n+GJ.nrows(~F, M.ofdm(~F, t)) : Nat}
      {==}

def hk_aug(~F: O.OField, +n: Nat, +a: List<&2, List<&2, S.D>>, +k: Nat, +hjn: {GJ.nrows(~F, M.ofdm(~F, a)) == n : Nat}, +hk: {KA.natle(1n+k, GJ.nrows(~F, M.ofdm(~F, NU.daugment(a, n, 0n)))) == True{} : Bool}) -> {KA.natle(1n+k, GJ.nrows(~F, M.ofdm(~F, a))) == True{} : Bool}:
  %nrows_aug(~F, a, n, 0n) : {KA.natle(1n+k, _) == True{} : Bool}
  hk

def hk_n(~F: O.OField, +n: Nat, +a: List<&2, List<&2, S.D>>, +k: Nat, +hjn: {GJ.nrows(~F, M.ofdm(~F, a)) == n : Nat}, +hk: {KA.natle(1n+k, GJ.nrows(~F, M.ofdm(~F, a))) == True{} : Bool}) -> {KA.natle(1n+k, n) == True{} : Bool}:
  %hjn : {KA.natle(1n+k, _) == True{} : Bool}
  hk

def row0_at(~F: O.OField, +n: Nat, +a: List<&2, List<&2, S.D>>, +g: O.C(F), +w: Nat, +k: Nat, +hk: {KA.natle(1n+k, GJ.nrows(~F, M.ofdm(~F, NU.daugment(a, n, 0n)))) == True{} : Bool}, +hw: GJ.All(~(i => GJ.roww(~F, M.ofdm(~F, a), n, i)), n), +hjn: {GJ.nrows(~F, M.ofdm(~F, a)) == n : Nat}, +hj: mall(~F, M.ofdm(~F, a), g), +hg: O.le(~F, O.zero(F), g)) -> rowinv(~F, n, M.ofdm(~F, a), DV.mrow(~F, M.ofdm(~F, NU.daugment(a, n, 0n)), k), Nat.add(k, 0n), 0n, O.add(F, g, O.one(F)), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))):
  %Equal.sym(M.Vec(~F), DV.mrow(~F, M.ofdm(~F, NU.daugment(a, n, 0n)), k), GJ.vapp(~F, DV.mrow(~F, M.ofdm(~F, a), k), GJ.unit(~F, n, Nat.add(k, 0n))), aug_row(~F, a, n, 0n, k, hk_aug(~F, n, a, k, hjn, hk))) : rowinv(~F, n, M.ofdm(~F, a), _, Nat.add(k, 0n), 0n, O.add(F, g, O.one(F)), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))
  %LN.add_zero(k) : rowinv(~F, n, M.ofdm(~F, a), GJ.vapp(~F, DV.mrow(~F, M.ofdm(~F, a), k), GJ.unit(~F, n, _)), Nat.add(k, 0n), 0n, O.add(F, g, O.one(F)), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))
  row0(~F, n, a, g, w, k, Nat.add(k, 0n), GJ.all_at(~(i => GJ.roww(~F, M.ofdm(~F, a), n, i)), n, hw, k, hk_n(~F, n, a, k, hjn, hk_aug(~F, n, a, k, hjn, hk))), hjn, hj, hg)

# the start's invariant
def rinv0(~F: O.OField, +n: Nat, +a: List<&2, List<&2, S.D>>, +g: O.C(F), +w: Nat, +hw: GJ.All(~(i => GJ.roww(~F, M.ofdm(~F, a), n, i)), n), +hjn: {GJ.nrows(~F, M.ofdm(~F, a)) == n : Nat}, +hj: mall(~F, M.ofdm(~F, a), g), +hg: O.le(~F, O.zero(F), g)) -> rinv(~F, n, M.ofdm(~F, a), M.ofdm(~F, NU.daugment(a, n, 0n)), 0n, 0n, O.add(F, g, O.one(F)), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))):
  rinv_of(~F, n, M.ofdm(~F, a), M.ofdm(~F, NU.daugment(a, n, 0n)), 0n, 0n, O.add(F, g, O.one(F)), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), GJ.all_mk(~GJ.nrows(~F, M.ofdm(~F, NU.daugment(a, n, 0n))), ~(k => rowinv(~F, n, M.ofdm(~F, a), DV.mrow(~F, M.ofdm(~F, NU.daugment(a, n, 0n)), k), Nat.add(k, 0n), 0n, O.add(F, g, O.one(F)), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))), ~(k => hk => row0_at(~F, n, a, g, w, k, hk, hw, hjn, hj, hg)), GJ.nrows(~F, M.ofdm(~F, NU.daugment(a, n, 0n))), GJ.le_refl(GJ.nrows(~F, M.ofdm(~F, NU.daugment(a, n, 0n))))))

def hns0(~F: O.OField, +n: Nat, +a: List<&2, List<&2, S.D>>, +hjn: {GJ.nrows(~F, M.ofdm(~F, a)) == n : Nat}) -> {GJ.nrows(~F, M.ofdm(~F, NU.daugment(a, n, 0n))) == n : Nat}:
  Equal.trans(Nat, GJ.nrows(~F, M.ofdm(~F, NU.daugment(a, n, 0n))), GJ.nrows(~F, M.ofdm(~F, a)), n, nrows_aug(~F, a, n, 0n), hjn)

# the start's right halves are I: entry k of I u is u_k
def e1_0(~F: O.OField, +n: Nat, +a: List<&2, List<&2, S.D>>, +u: M.Vec(~F), +k: Nat, +lu: {M.len(~F, u) == n : Nat}, +hk: {KA.natle(1n+k, n) == True{} : Bool}, +hw: GJ.All(~(i => GJ.roww(~F, M.ofdm(~F, a), n, i)), n), +hjn: {GJ.nrows(~F, M.ofdm(~F, a)) == n : Nat}) -> {zr(~F, n, DV.mrow(~F, M.ofdm(~F, NU.daugment(a, n, 0n)), k), u) == O.lookup(~F, u, k) : O.C(F)}:
  %Equal.sym(M.Vec(~F), DV.mrow(~F, M.ofdm(~F, NU.daugment(a, n, 0n)), k), GJ.vapp(~F, DV.mrow(~F, M.ofdm(~F, a), k), GJ.unit(~F, n, Nat.add(k, 0n))), aug_row(~F, a, n, 0n, k, (%Equal.sym(Nat, GJ.nrows(~F, M.ofdm(~F, a)), n, hjn) : {KA.natle(1n+k, _) == True{} : Bool}
      hk))) : {M.dot(~F, GJ.vdrop(~F, n, _), u) == O.lookup(~F, u, k) : O.C(F)}
  %LN.add_zero(k) : {M.dot(~F, GJ.vdrop(~F, n, GJ.vapp(~F, DV.mrow(~F, M.ofdm(~F, a), k), GJ.unit(~F, n, _))), u) == O.lookup(~F, u, k) : O.C(F)}
  %GJ.all_at(~(i => GJ.roww(~F, M.ofdm(~F, a), n, i)), n, hw, k, hk) : {M.dot(~F, GJ.vdrop(~F, _, GJ.vapp(~F, DV.mrow(~F, M.ofdm(~F, a), k), GJ.unit(~F, n, k))), u) == O.lookup(~F, u, k) : O.C(F)}
  %Equal.sym(M.Vec(~F), GJ.vdrop(~F, M.len(~F, DV.mrow(~F, M.ofdm(~F, a), k)), GJ.vapp(~F, DV.mrow(~F, M.ofdm(~F, a), k), GJ.unit(~F, n, k))), GJ.unit(~F, n, k), drop_app(~F, DV.mrow(~F, M.ofdm(~F, a), k), GJ.unit(~F, n, k))) : {M.dot(~F, _, u) == O.lookup(~F, u, k) : O.C(F)}
  Equal.sym(O.C(F), O.lookup(~F, u, k), M.dot(~F, GJ.unit(~F, n, k), u), GJ.dot_unit(~F, n, k, u, (%Equal.sym(Nat, M.len(~F, u), n, lu) : {KA.natle(_, n) == True{} : Bool}
    GJ.le_refl(n))))

def low0(~F: O.OField, +n: Nat, +a: List<&2, List<&2, S.D>>, +hw: GJ.All(~(i => GJ.roww(~F, M.ofdm(~F, a), n, i)), n), +hjn: {GJ.nrows(~F, M.ofdm(~F, a)) == n : Nat}, +u: M.Vec(~F), +lu: {M.len(~F, u) == n : Nat}) -> O.le(~F, NP.vn(~F, u), O.mul(F, O.one(F), NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, NU.daugment(a, n, 0n))), u)))):
  %Equal.sym(O.C(F), O.mul(F, O.one(F), NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, NU.daugment(a, n, 0n))), u))), NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, NU.daugment(a, n, 0n))), u)), FR.fring_eq(~F, [NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, NU.daugment(a, n, 0n))), u))], E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, E.ZVar{0n}, {==})) : O.le(~F, NP.vn(~F, u), _)
  FV.vmax_lub(~F, u, NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, NU.daugment(a, n, 0n))), u)), vall_lt(~F, ~u, ~NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, NU.daugment(a, n, 0n))), u)), ~(k => hk =>
      (%Equal.trans(O.C(F), O.lookup(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, NU.daugment(a, n, 0n))), u), k), zr(~F, n, DV.mrow(~F, M.ofdm(~F, NU.daugment(a, n, 0n)), k), u), O.lookup(~F, u, k), look_rmv(~F, n, M.ofdm(~F, NU.daugment(a, n, 0n)), u, k), e1_0(~F, n, a, u, k, lu, (%lu : {KA.natle(1n+k, _) == True{} : Bool} hk), hw, hjn)) : M.bnd(~F, _, NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, NU.daugment(a, n, 0n))), u)))
        look_bnd(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, NU.daugment(a, n, 0n))), u), k, NP.vn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, NU.daugment(a, n, 0n))), u)), FV.vmax_all(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, NU.daugment(a, n, 0n))), u)), FV.vmax_nn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, NU.daugment(a, n, 0n))), u)))))), FV.vmax_nn(~F, M.matvec(~F, rmat(~F, n, M.ofdm(~F, NU.daugment(a, n, 0n))), u)))

# the start's right halves have an inverse of norm at most 1
def invb0(~F: O.OField, +n: Nat, +a: List<&2, List<&2, S.D>>, +g: O.C(F), +w: Nat, +hw: GJ.All(~(i => GJ.roww(~F, M.ofdm(~F, a), n, i)), n), +hjn: {GJ.nrows(~F, M.ofdm(~F, a)) == n : Nat}, +hj: mall(~F, M.ofdm(~F, a), g), +hg: O.le(~F, O.zero(F), g)) -> NP.InvB(~F, rmat(~F, n, M.ofdm(~F, NU.daugment(a, n, 0n))), n, O.one(F)):
  NP.invb_of_low(~F, ~rmat(~F, n, M.ofdm(~F, NU.daugment(a, n, 0n))), ~n, ~O.one(F), ~(u => lu => low0(~F, n, a, hw, hjn, u, lu)), NP.one_nn(~F), Equal.trans(Nat, GJ.nrows(~F, rmat(~F, n, M.ofdm(~F, NU.daugment(a, n, 0n)))), GJ.nrows(~F, M.ofdm(~F, NU.daugment(a, n, 0n))), n, nrows_rmat(~F, n, M.ofdm(~F, NU.daugment(a, n, 0n))), hns0(~F, n, a, hjn)), rw_all(~F, n, M.ofdm(~F, a), M.ofdm(~F, NU.daugment(a, n, 0n)), 0n, O.add(F, g, O.one(F)), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, O.zero(F), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), rinv0(~F, n, a, g, w, hw, hjn, hj, hg), hns0(~F, n, a, hjn)))

# The end: A = the right halves, and I - A J is small
# ---------------------------------------------------

def ddrop_ofd(~F: O.OField, k: Nat, r: List<&2, S.D>) -> {M.ofdv(~F, NU.ddrop(k, r)) == GJ.vdrop(~F, k, M.ofdv(~F, r)) : M.Vec(~F)}:
  match k r:
    case 0n Nil{}:
      {==}
    case 0n Con{x, t}:
      {==}
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{x, t}:
      ddrop_ofd(~F, j, t)

def drights_ofd(~F: O.OField, +n: Nat, s: List<&2, List<&2, S.D>>) -> {M.ofdm(~F, NU.drights(n, s)) == rmat(~F, n, M.ofdm(~F, s)) : M.Mat(~F)}:
  match s:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      %Equal.sym(M.Vec(~F), M.ofdv(~F, NU.ddrop(n, r)), GJ.vdrop(~F, n, M.ofdv(~F, r)), ddrop_ofd(~F, n, r)) : {Con{_, M.ofdm(~F, NU.drights(n, t))} == Con{GJ.vdrop(~F, n, M.ofdv(~F, r)), rmat(~F, n, M.ofdm(~F, t))} : M.Mat(~F)}
      %Equal.sym(M.Mat(~F), M.ofdm(~F, NU.drights(n, t)), rmat(~F, n, M.ofdm(~F, t)), drights_ofd(~F, n, t)) : {Con{GJ.vdrop(~F, n, M.ofdv(~F, r)), _} == Con{GJ.vdrop(~F, n, M.ofdv(~F, r)), rmat(~F, n, M.ofdm(~F, t))} : M.Mat(~F)}
      {==}

# every entry of I - A J is at most e: |[i = k] - A_i . J_col k| <= e
def agood(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +A: M.Mat(~F), +e: O.C(F)) -> Data:
  GJ.All(~(i => GJ.All(~(k => M.bnd(~F, O.sub(~F, GJ.dl(~F, KA.nateq(i, k)), M.dot(~F, DV.mrow(~F, A, i), GJ.mcol(~F, jm, k))), e)), n)), n)


def ag_ent(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +x: M.Vec(~F), +i: Nat, +k: Nat, +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +h: rowinv(~F, n, jm, x, i, n, gg, dd, ph), +hk: {KA.natle(1n+k, n) == True{} : Bool}) -> M.bnd(~F, O.sub(~F, GJ.dl(~F, KA.nateq(i, k)), M.dot(~F, GJ.vdrop(~F, n, x), GJ.mcol(~F, jm, k))), O.add(F, dd, ph)):
  KB.bnd_val(~F, O.add(F, dk(~F, n, jm, x, k), O.neg(F, O.sub(~F, O.lookup(~F, x, k), GJ.dl(~F, KA.nateq(i, k))))), O.sub(~F, GJ.dl(~F, KA.nateq(i, k)), M.dot(~F, GJ.vdrop(~F, n, x), GJ.mcol(~F, jm, k))), O.add(F, dd, ph), FR.fring_eq(~F, [O.lookup(~F, x, k), GJ.dl(~F, KA.nateq(i, k)), M.dot(~F, GJ.vdrop(~F, n, x), GJ.mcol(~F, jm, k))], E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, E.ZNeg{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}}}, E.ZSub{E.ZVar{1n}, E.ZVar{2n}}, {==}),
    FM.bnd_add(~F, dk(~F, n, jm, x, k), dd, O.neg(F, O.sub(~F, O.lookup(~F, x, k), GJ.dl(~F, KA.nateq(i, k)))), ph,
      GJ.all_at(~(q => M.bnd(~F, dk(~F, n, jm, x, q), dd)), n, ri_d(~F, n, jm, x, i, n, gg, dd, ph, h), k, hk),
      FM.bnd_neg(~F, O.sub(~F, O.lookup(~F, x, k), GJ.dl(~F, KA.nateq(i, k))), ph, GJ.all_at(~(q => M.bnd(~F, O.sub(~F, O.lookup(~F, x, q), GJ.dl(~F, KA.nateq(i, q))), ph)), n, ri_f(~F, n, jm, x, i, n, gg, dd, ph, h), k, hk))))

def agood_of(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +s: M.Mat(~F), +gg: O.C(F), +dd: O.C(F), +ph: O.C(F), +h: rinv(~F, n, jm, s, 0n, n, gg, dd, ph), +hns: {GJ.nrows(~F, s) == n : Nat}) -> agood(~F, n, jm, rmat(~F, n, s), O.add(F, dd, ph)):
  GJ.all_mk(~n, ~(i => GJ.All(~(k => M.bnd(~F, O.sub(~F, GJ.dl(~F, KA.nateq(i, k)), M.dot(~F, DV.mrow(~F, rmat(~F, n, s), i), GJ.mcol(~F, jm, k))), O.add(F, dd, ph))), n)), ~(i => hi =>
    GJ.all_mk(~n, ~(k => M.bnd(~F, O.sub(~F, GJ.dl(~F, KA.nateq(i, k)), M.dot(~F, DV.mrow(~F, rmat(~F, n, s), i), GJ.mcol(~F, jm, k))), O.add(F, dd, ph))), ~(k => hk =>
      (%Equal.sym(M.Vec(~F), DV.mrow(~F, rmat(~F, n, s), i), GJ.vdrop(~F, n, DV.mrow(~F, s, i)), mrow_rmat(~F, n, s, i)) : M.bnd(~F, O.sub(~F, GJ.dl(~F, KA.nateq(i, k)), M.dot(~F, _, GJ.mcol(~F, jm, k))), O.add(F, dd, ph))
        ag_ent(~F, n, jm, DV.mrow(~F, s, i), i, k, gg, dd, ph, ri_atf(~F, n, jm, s, n, gg, dd, ph, i, h, his(~F, s, n, i, hns, hi)), hk))), n, GJ.le_refl(n))), n, GJ.le_refl(n))

# what dinverse returns: an n-row A with every entry of I - A J at most e
def dinv_res(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +e: O.C(F), res: Maybe<&2, List<&2, List<&2, S.D>>>) -> Type:
  match res:
    case None{}:
      Empty
    case Some{A}:
      M.Both({GJ.nrows(~F, M.ofdm(~F, A)) == n : Nat}, agood(~F, n, jm, M.ofdm(~F, A), e))

def dinv_some(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +g: O.C(F), +bb: O.C(F), +w: Nat, +s: List<&2, List<&2, S.D>>, +h: M.Both({GJ.nrows(~F, M.ofdm(~F, s)) == n : Nat}, rinv(~F, n, jm, M.ofdm(~F, s), 0n, n, kg(~F, kst(~F, n, g, bb, n)), O.mul(F, kd(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))) -> M.Both({GJ.nrows(~F, M.ofdm(~F, NU.drights(n, s))) == n : Nat}, agood(~F, n, jm, M.ofdm(~F, NU.drights(n, s)), O.add(F, O.mul(F, kd(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))))):
  %Equal.sym(M.Mat(~F), M.ofdm(~F, NU.drights(n, s)), rmat(~F, n, M.ofdm(~F, s)), drights_ofd(~F, n, s)) : M.Both({GJ.nrows(~F, _) == n : Nat}, agood(~F, n, jm, _, O.add(F, O.mul(F, kd(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))))
  (Equal.trans(Nat, GJ.nrows(~F, rmat(~F, n, M.ofdm(~F, s))), GJ.nrows(~F, M.ofdm(~F, s)), n, nrows_rmat(~F, n, M.ofdm(~F, s)), bfst({GJ.nrows(~F, M.ofdm(~F, s)) == n : Nat}, rinv(~F, n, jm, M.ofdm(~F, s), 0n, n, kg(~F, kst(~F, n, g, bb, n)), O.mul(F, kd(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), h)), agood_of(~F, n, jm, M.ofdm(~F, s), kg(~F, kst(~F, n, g, bb, n)), O.mul(F, kd(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), bsnd({GJ.nrows(~F, M.ofdm(~F, s)) == n : Nat}, rinv(~F, n, jm, M.ofdm(~F, s), 0n, n, kg(~F, kst(~F, n, g, bb, n)), O.mul(F, kd(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), h), bfst({GJ.nrows(~F, M.ofdm(~F, s)) == n : Nat}, rinv(~F, n, jm, M.ofdm(~F, s), 0n, n, kg(~F, kst(~F, n, g, bb, n)), O.mul(F, kd(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), h)))

def dinv_fin(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +g: O.C(F), +bb: O.C(F), +w: Nat, res: Maybe<&2, List<&2, List<&2, S.D>>>, h: dres(~F, n, jm, g, bb, w, res)) -> dinv_res(~F, n, jm, O.add(F, O.mul(F, kd(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), NU.dinv.of(n, res)):
  match res:
    case None{}:
      h
    case Some{+s}:
      dinv_some(~F, n, jm, g, bb, w, s, h)

# C4: the solver's rounded Gauss-Jordan, as it runs. For a dyadic n x n
# matrix a, read as J in F, with |J_ij| <= g and an inverse of norm at
# most beta, once u = 2^-w meets every column's smallness, dinverse
# returns A with every entry of I - A J at most (KD_n + KP_n) u.
def dinverse_ok(~F: O.OField, +n: Nat, +w: Nat, +a: List<&2, List<&2, S.D>>, +g: O.C(F), +bb: O.C(F), +hw: GJ.All(~(i => GJ.roww(~F, M.ofdm(~F, a), n, i)), n), +hjn: {GJ.nrows(~F, M.ofdm(~F, a)) == n : Nat}, +hJ: NP.InvB(~F, M.ofdm(~F, a), n, bb), +hj: mall(~F, M.ofdm(~F, a), g), +hg: O.le(~F, O.zero(F), g), +hb: O.le(~F, O.zero(F), bb), +hsm: GJ.All(~(q => O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), acoef(~F, n, bb, q, kst(~F, n, g, bb, q))), O.one(F))), n)) -> dinv_res(~F, n, M.ofdm(~F, a), O.add(F, O.mul(F, kd(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, kp(~F, kst(~F, n, g, bb, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}))), NU.dinverse(n, w, a)):
  dinv_fin(~F, n, M.ofdm(~F, a), g, bb, w, NU.dgj0(n, w, NU.daugment(a, n, 0n)),
    dgj_ok(~F, n, w, 0n, NU.dpivot(NU.daugment(a, n, 0n), 0n, 0n, 0n, None{}, NU.dzero()), NU.daugment(a, n, 0n), n, M.ofdm(~F, a), g, bb, {==}, hns0(~F, n, a, hjn), (rinv0(~F, n, a, g, w, hw, hjn, hj, hg), invb0(~F, n, a, g, w, hw, hjn, hj, hg)), pivot_ok(~F, NU.daugment(a, n, 0n), 0n), hJ, hjn, hj, hg, hb, hsm))
