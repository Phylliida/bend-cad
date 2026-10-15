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
