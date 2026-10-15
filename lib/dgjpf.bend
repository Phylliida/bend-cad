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
