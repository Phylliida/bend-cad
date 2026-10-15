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
