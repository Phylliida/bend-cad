# bend-cad: when refute finds no refutation, there is none (PLAN-sk13a S3).
# The simplex's Sat gives a linearized point: two functionals on
# polynomials, phi0 (the real part) and phi1 (the delta part), with
# weights 1 and 0 at the monomial 1, the dictionary's values at the y's,
# and the pivots' weights by back-substitution through the equations'
# rows (as in lib/indpf.bend). Both kill every equation; on every side
# (phi0, phi1) is lexicographically >= 0, and > 0 when the side is
# strict. A refutation l . es + m . ss = k read through both would make
# (k, 0) >= 0 lexicographically, and > 0 when k = 0 (a strict side
# weighted positively): never what Refutes0 asks. Proofs only.
#
# Generated from tools/drafts/satpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./nat.bend as LN
import ./zring.bend as R
import ./zlaws.bend as ZL
import ./zord.bend as ZO
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./qemb.bend as QE
import ./qfield.bend as QF
import ./qnorm.bend as QN
import ./natring.bend as NR
import ./redpoly.bend as RP
import ./identpf.bend as ID
import ./elim.bend as EL
import ./coefpf.bend as CF
import ./elimpf.bend as EP
import ./drvpf.bend as DR
import ./indpf.bend as IP
import ./simplex.bend as SX
import ./simppf.bend as SP
import ./runpf.bend as RN
import ./termpf.bend as TP
import ./pigeon.bend as PH
import ./refute.bend as RF
import ./unsatpf.bend as UN
import ./refpf.bend as RP2
import ./listpf.bend as LI
import ./lexpf.bend as LX

def absurd(-A: Type, x: Empty) -> A:
  match x:

# The run's Sat
# -------------

# no slack is below its bound
def sok(+lp: SX.LP, +t: SX.Tab) -> Bool:
  UN.isnone(SX.leave(lp, t))

def scheck(+lp: SX.LP, r: SX.Run) -> Bool:
  match r:
    case SX.Go{t}:
      True{}
    case SX.Sat{+t}:
      sok(lp, t)
    case SX.Unsat{t, i}:
      True{}

def sc.e(+lp: SX.LP, +t: SX.Tab, +i: Nat, me: Maybe<&2, Nat>) -> {scheck(lp, SX.step.e(lp, t, i, me)) == True{} : Bool}:
  match me:
    case None{}:
      {==}
    case Some{e}:
      {==}

def sc.l(+lp: SX.LP, +t: SX.Tab, ml: Maybe<&2, Nat>, hml: {ml == SX.leave(lp, t) : Maybe<&2, Nat>}) -> {scheck(lp, SX.step.l(lp, t, ml)) == True{} : Bool}:
  match ml:
    case None{}:
      %hml : {UN.isnone(_) == True{} : Bool}
      {==}
    case Some{+i}:
      sc.e(lp, t, i, SX.enter.go(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n))

def sc.adv(+lp: SX.LP, r: SX.Run, h: {scheck(lp, r) == True{} : Bool}) -> {scheck(lp, SX.adv(lp, r)) == True{} : Bool}:
  match r:
    case SX.Go{+t}:
      sc.l(lp, t, SX.leave(lp, t), {==})
    case SX.Sat{t}:
      h
    case SX.Unsat{t, i}:
      {==}

def scheck_all(+lp: SX.LP, n: Nat) -> {scheck(lp, RN.st(lp, n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++k:
      %Equal.sym(SX.Run, RN.st(lp, 1n+k), SX.adv(lp, RN.st(lp, k)), RN.st_succ(lp, k)) : {scheck(lp, _) == True{} : Bool}
      sc.adv(lp, RN.st(lp, k), scheck_all(lp, k))


def s_st(+lp: SX.LP, +hwf: {SP.lpwf(lp) == True{} : Bool}, +t: SX.Tab, +h: {SX.solve(lp) == SX.Sat{t} : SX.Run}) -> {RN.st(lp, PH.pow2(SX.LP.nv(lp))) == SX.Sat{t} : SX.Run}:
  Equal.trans(SX.Run, RN.st(lp, PH.pow2(SX.LP.nv(lp))), SX.solve(lp), SX.Sat{t}, Equal.sym(SX.Run, SX.solve(lp), RN.st(lp, PH.pow2(SX.LP.nv(lp))), TP.solve_st(lp)), h)

def s_tab(+lp: SX.LP, +hwf: {SP.lpwf(lp) == True{} : Bool}, +t: SX.Tab, +h: {SX.solve(lp) == SX.Sat{t} : SX.Run}) -> {RN.tab(lp, PH.pow2(SX.LP.nv(lp))) == t : SX.Tab}:
  %Equal.sym(SX.Run, RN.st(lp, PH.pow2(SX.LP.nv(lp))), SX.Sat{t}, s_st(lp, hwf, t, h)) : {RN.rtab(_) == t : SX.Tab}
  {==}

def s_leave(+lp: SX.LP, +hwf: {SP.lpwf(lp) == True{} : Bool}, +t: SX.Tab, +h: {SX.solve(lp) == SX.Sat{t} : SX.Run}) -> {SX.leave(lp, t) == None{} : Maybe<&2, Nat>}:
  UN.isnone_none(SX.leave(lp, t), (%s_st(lp, hwf, t, h) : {scheck(lp, _) == True{} : Bool}
    scheck_all(lp, PH.pow2(SX.LP.nv(lp)))))

def s_first(+lp: SX.LP, +hwf: {SP.lpwf(lp) == True{} : Bool}, +t: SX.Tab, +h: {SX.solve(lp) == SX.Sat{t} : SX.Run}) -> {RN.firstfrom(RN.viols(SX.LP.qs(lp), SX.Tab.rows(t), SX.LP.v0(lp), SX.LP.v1(lp)), 0n) == None{} : Maybe<&2, Nat>}:
  %RN.leave_eq(SX.LP.qs(lp), SX.Tab.rows(t), SX.LP.v0(lp), SX.LP.v1(lp), 0n) : {_ == None{} : Maybe<&2, Nat>}
  s_leave(lp, hwf, t, h)

def s_hr(+lp: SX.LP, +hwf: {SP.lpwf(lp) == True{} : Bool}, +t: SX.Tab, +h: {SX.solve(lp) == SX.Sat{t} : SX.Run}) -> {KA.natle(SX.LP.m(lp), SP.nrows(SX.Tab.rows(t))) == True{} : Bool}:
  %s_tab(lp, hwf, t, h) : {KA.natle(SX.LP.m(lp), SP.nrows(SX.Tab.rows(_))) == True{} : Bool}
  RN.hr_at(lp, PH.pow2(SX.LP.nv(lp)))

# every slack is at or above its bound
def s_noviol(+lp: SX.LP, +hwf: {SP.lpwf(lp) == True{} : Bool}, +t: SX.Tab, +h: {SX.solve(lp) == SX.Sat{t} : SX.Run}, +k: Nat, hk: {SX.ltn(k, SX.LP.m(lp)) == True{} : Bool}) -> {SX.viol(SX.rowat(SX.Tab.rows(t), k), SX.LP.v0(lp), SX.LP.v1(lp), RN.qat(SX.LP.qs(lp), k)) == False{} : Bool}:
  %RN.bat_viols(SX.LP.qs(lp), SX.Tab.rows(t), SX.LP.v0(lp), SX.LP.v1(lp), k, hk, s_hr(lp, hwf, t, h)) : {_ == False{} : Bool}
  RN.first_none(RN.viols(SX.LP.qs(lp), SX.Tab.rows(t), SX.LP.v0(lp), SX.LP.v1(lp)), s_first(lp, hwf, t, h), k)

def s_i1(~F: O.OField, +lp: SX.LP, +hwf: {SP.lpwf(lp) == True{} : Bool}, +t: SX.Tab, +h: {SX.solve(lp) == SX.Sat{t} : SX.Run}) -> SP.I1(~F, lp, SX.Tab.rows(t)):
  %s_tab(lp, hwf, t, h) : SP.I1(~F, lp, SX.Tab.rows(_))
  RN.i1_at(~F, lp, PH.pow2(SX.LP.nv(lp)), hwf)

# The slacks' values
# ------------------

def Ineq.a(q: SX.Ineq) -> List<&2, S.Z>:
  match q:
    case SX.Ineq{a, b, s}:
      a

def invg_at(~F: O.OField, qs: List<&2, SX.Ineq>, +m: Nat, +x: M.Vec(~F), xr: M.Vec(~F), k: Nat, h: SP.invg(~F, qs, m, x, xr), hk: {SX.ltn(k, SX.qlen(qs)) == True{} : Bool})
  -> {SP.fat(~F, xr, k) == SP.zdot(~F, SX.cat(EL.zeros(m), Ineq.a(RN.qat(qs, k))), x) : O.C(F)}:
  match qs xr k:
    case Nil{} xr k:
      absurd({SP.fat(~F, xr, k) == SP.zdot(~F, SX.cat(EL.zeros(m), Ineq.a(RN.qat(Nil{}, k))), x) : O.C(F)}, KA.ft(SP.ltn0(k, hk)))
    case Con{SX.Ineq{a, b, s}, qt} Nil{} 0n:
      (h1, h2) = h
      h1
    case Con{SX.Ineq{a, b, s}, qt} Nil{} 1n+j:
      (h1, h2) = h
      invg_at(~F, qt, m, x, Nil{}, j, h2, hk)
    case Con{SX.Ineq{a, b, s}, qt} Con{y, xt} 0n:
      (h1, h2) = h
      h1
    case Con{SX.Ineq{a, b, s}, qt} Con{y, xt} 1n+j:
      (h1, h2) = h
      invg_at(~F, qt, m, x, xt, j, h2, hk)


# slack k reads a_k . y at the dictionary's point for w
def s_val(~F: O.OField, +lp: SX.LP, +hwf: {SP.lpwf(lp) == True{} : Bool}, +t: SX.Tab, +h: {SX.solve(lp) == SX.Sat{t} : SX.Run}, +w: M.Vec(~F), +k: Nat, hk: {SX.ltn(k, SX.LP.m(lp)) == True{} : Bool})
  -> {SP.rv(~F, SX.rowat(SX.Tab.rows(t), k), w) == SP.zdot(~F, Ineq.a(RN.qat(SX.LP.qs(lp), k)), SP.ydrop(~F, SX.LP.m(lp), SP.rmap(~F, SX.Tab.rows(t), w))) : O.C(F)}:
  Equal.trans(O.C(F), SP.rv(~F, SX.rowat(SX.Tab.rows(t), k), w), SP.fat(~F, SP.rmap(~F, SX.Tab.rows(t), w), k), SP.zdot(~F, Ineq.a(RN.qat(SX.LP.qs(lp), k)), SP.ydrop(~F, SX.LP.m(lp), SP.rmap(~F, SX.Tab.rows(t), w))),
    SP.fat_rmap(~F, SX.Tab.rows(t), w, k),
    Equal.trans(O.C(F), SP.fat(~F, SP.rmap(~F, SX.Tab.rows(t), w), k), SP.zdot(~F, SX.cat(EL.zeros(SX.LP.m(lp)), Ineq.a(RN.qat(SX.LP.qs(lp), k))), SP.rmap(~F, SX.Tab.rows(t), w)), SP.zdot(~F, Ineq.a(RN.qat(SX.LP.qs(lp), k)), SP.ydrop(~F, SX.LP.m(lp), SP.rmap(~F, SX.Tab.rows(t), w))),
      invg_at(~F, SX.LP.qs(lp), SX.LP.m(lp), SP.rmap(~F, SX.Tab.rows(t), w), SP.rmap(~F, SX.Tab.rows(t), w), k, s_i1(~F, lp, hwf, t, h)(w), hk),
      Equal.sym(O.C(F), SP.zdot(~F, Ineq.a(RN.qat(SX.LP.qs(lp), k)), SP.ydrop(~F, SX.LP.m(lp), SP.rmap(~F, SX.Tab.rows(t), w))), SP.zdot(~F, SX.cat(EL.zeros(SX.LP.m(lp)), Ineq.a(RN.qat(SX.LP.qs(lp), k))), SP.rmap(~F, SX.Tab.rows(t), w)),
        SP.zdot_cat_zeros(~F, SX.LP.m(lp), Ineq.a(RN.qat(SX.LP.qs(lp), k)), SP.rmap(~F, SX.Tab.rows(t), w)))))

# The functional, back-substituted from a base
# --------------------------------------------

# the rows' pivots, newest last, then the base monomials
def bms(rows: List<&2, EL.Row>, +ms0: List<&2, List<&2, Nat>>) -> List<&2, List<&2, Nat>>:
  match rows:
    case Nil{}:
      ms0
    case Con{row, t}:
      Con{EP.rowpv(row), bms(t, ms0)}

# each pivot's weight kills its row, the later rows' weights first
def bcs(~F: O.OField, rows: List<&2, EL.Row>, +ms0: List<&2, List<&2, Nat>>, +cs0: List<&2, O.C(F)>) -> List<&2, O.C(F)>:
  match rows:
    case Nil{}:
      cs0
    case Con{+row, +t}:
      Con{O.mul(F, O.neg(F, IP.phi(~F, bms(t, ms0), bcs(~F, t, ms0, cs0), EP.rowp(row))), O.inv(F, O.ofz(~F, EL.cz(EP.rowpv(row), EP.rowp(row))))), bcs(~F, t, ms0, cs0)}

def b_allz(~F: O.OField, rows: List<&2, EL.Row>, +ms0: List<&2, List<&2, Nat>>, +cs0: List<&2, O.C(F)>, +B: List<&2, E.QExpr>, +hok: {EP.allok(B, rows) == True{} : Bool}, +he: {EP.ech(rows) == True{} : Bool})
  -> IP.AllZ(~F, bms(rows, ms0), bcs(~F, rows, ms0, cs0), rows):
  match rows:
    case Nil{}:
      Unit{}
    case Con{EL.Row{+p, +cb, +bt, +pv}, +t}:
      (IP.head_zero(~F, bms(t, ms0), bcs(~F, t, ms0, cs0), pv, p, EP.rowok_nz(B, p, cb, bt, pv, KA.band_l(EP.rowok(B, EL.Row{p, cb, bt, pv}), EP.allok(B, t), hok))),
       IP.allz_ext(~F, t, pv, O.mul(F, O.neg(F, IP.phi(~F, bms(t, ms0), bcs(~F, t, ms0, cs0), p)), O.inv(F, O.ofz(~F, EL.cz(pv, p)))), bms(t, ms0), bcs(~F, t, ms0, cs0),
         b_allz(~F, t, ms0, cs0, B, KA.band_r(EP.rowok(B, EL.Row{p, cb, bt, pv}), EP.allok(B, t), hok), KA.band_r(EP.zat(pv, t), EP.ech(t), he)),
         KA.band_l(EP.zat(pv, t), EP.ech(t), he)))

# on a polynomial 0 at every pivot, only the base counts
def b_res(~F: O.OField, rows: List<&2, EL.Row>, +ms0: List<&2, List<&2, Nat>>, +cs0: List<&2, O.C(F)>, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +hz: {EP.zp(rows, EL.Res{p, cb, bt}) == True{} : Bool})
  -> {IP.phi(~F, bms(rows, ms0), bcs(~F, rows, ms0, cs0), p) == IP.phi(~F, ms0, cs0, p) : O.C(F)}:
  match rows:
    case Nil{}:
      {==}
    case Con{+row, +t}:
      %Equal.sym(S.Z, EL.cz(EP.rowpv(row), p), S.Z0{}, EP.zero_of(EL.cz(EP.rowpv(row), p), KA.band_l(EP.ZAt(EP.rowpv(row), EL.Res{p, cb, bt}), EP.zp(t, EL.Res{p, cb, bt}), hz)))
        : {O.add(F, O.mul(F, O.mul(F, O.neg(F, IP.phi(~F, bms(t, ms0), bcs(~F, t, ms0, cs0), EP.rowp(row))), O.inv(F, O.ofz(~F, EL.cz(EP.rowpv(row), EP.rowp(row))))), O.ofz(~F, _)), IP.phi(~F, bms(t, ms0), bcs(~F, t, ms0, cs0), p)) == IP.phi(~F, ms0, cs0, p) : O.C(F)}
      %FL.mul_zero(~F, O.mul(F, O.neg(F, IP.phi(~F, bms(t, ms0), bcs(~F, t, ms0, cs0), EP.rowp(row))), O.inv(F, O.ofz(~F, EL.cz(EP.rowpv(row), EP.rowp(row))))))
        : {O.add(F, _, IP.phi(~F, bms(t, ms0), bcs(~F, t, ms0, cs0), p)) == IP.phi(~F, ms0, cs0, p) : O.C(F)}
      %Equal.sym(O.C(F), IP.phi(~F, bms(t, ms0), bcs(~F, t, ms0, cs0), p), IP.phi(~F, ms0, cs0, p), b_res(~F, t, ms0, cs0, p, cb, bt, KA.band_r(EP.ZAt(EP.rowpv(row), EL.Res{p, cb, bt}), EP.zp(t, EL.Res{p, cb, bt}), hz)))
        : {O.add(F, O.zero(F), _) == IP.phi(~F, ms0, cs0, p) : O.C(F)}
      FL.zero_add(~F, IP.phi(~F, ms0, cs0, p))

def b_res.r(~F: O.OField, +rows: List<&2, EL.Row>, +ms0: List<&2, List<&2, Nat>>, +cs0: List<&2, O.C(F)>, r: EL.Res, hz: {EP.zp(rows, r) == True{} : Bool})
  -> {IP.phi(~F, bms(rows, ms0), bcs(~F, rows, ms0, cs0), RF.Res.p(r)) == IP.phi(~F, ms0, cs0, RF.Res.p(r)) : O.C(F)}:
  match r:
    case EL.Res{+p, +cb, +bt}:
      b_res(~F, rows, ms0, cs0, p, cb, bt, hz)

# on the y's, phi is a dot product
def phi_coefs(~F: O.OField, ys: List<&2, List<&2, Nat>>, Y: List<&2, O.C(F)>, +p: List<&2, R.ZTerm>) -> {IP.phi(~F, ys, Y, p) == SP.zdot(~F, RF.coefs(ys, p), Y) : O.C(F)}:
  match ys Y:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{c, ct}:
      {==}
    case Con{y, yt} Nil{}:
      {==}
    case Con{+y, +yt} Con{+c, +ct}:
      %Equal.sym(O.C(F), IP.phi(~F, yt, ct, p), SP.zdot(~F, RF.coefs(yt, p), ct), phi_coefs(~F, yt, ct, p)) : {O.add(F, O.mul(F, c, O.ofz(~F, EL.cz(y, p))), _) == O.add(F, O.mul(F, O.ofz(~F, EL.cz(y, p)), c), SP.zdot(~F, RF.coefs(yt, p), ct)) : O.C(F)}
      FR.fring_eq(~F, [c, O.ofz(~F, EL.cz(y, p)), SP.zdot(~F, RF.coefs(yt, p), ct)], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{0n}}, E.ZVar{2n}}, {==})

# The sides' residuals under the functional
# -----------------------------------------

def rel_proj(+m: List<&2, Nat>, r: EL.Res, +e: E.QExpr, +B: List<&2, E.QExpr>, h: EP.Rel(m, r, e, B))
  -> {EL.cz(m, RF.Res.p(r)) == S.Z.add(S.Z.mul(S.Zpos{RF.Res.bt(r)}, EL.cz(m, EP.NE(e))), EP.zdot(RF.Res.cb(r), EP.zv(m, B))) : S.Z}:
  match r:
    case EL.Res{p, cb, bt}:
      h

def phi_t(~F: O.OField, +c: O.C(F), +bt: S.Pos, +X: S.Z, +Y: S.Z, +Z: S.Z, hz: {Z == S.Z.add(S.Z.mul(S.Zpos{bt}, X), Y) : S.Z})
  -> {O.mul(F, c, O.ofz(~F, Z)) == O.add(F, O.mul(F, O.ofp(~F, bt), O.mul(F, c, O.ofz(~F, X))), O.mul(F, c, O.ofz(~F, Y))) : O.C(F)}:
  %Equal.sym(S.Z, Z, S.Z.add(S.Z.mul(S.Zpos{bt}, X), Y), hz) : {O.mul(F, c, O.ofz(~F, _)) == O.add(F, O.mul(F, O.ofp(~F, bt), O.mul(F, c, O.ofz(~F, X))), O.mul(F, c, O.ofz(~F, Y))) : O.C(F)}
  %FR.ofz_add(~F, S.Z.mul(S.Zpos{bt}, X), Y)
    : {O.mul(F, c, _) == O.add(F, O.mul(F, O.ofp(~F, bt), O.mul(F, c, O.ofz(~F, X))), O.mul(F, c, O.ofz(~F, Y))) : O.C(F)}
  %FR.ofz_mul(~F, S.Zpos{bt}, X)
    : {O.mul(F, c, O.add(F, _, O.ofz(~F, Y))) == O.add(F, O.mul(F, O.ofp(~F, bt), O.mul(F, c, O.ofz(~F, X))), O.mul(F, c, O.ofz(~F, Y))) : O.C(F)}
  FR.fring_eq(~F, [c, O.ofp(~F, bt), O.ofz(~F, X), O.ofz(~F, Y)], E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{3n}}}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}, {==})


def cz_rel(+m: List<&2, Nat>, +rows: List<&2, EL.Row>, +e: E.QExpr, +B: List<&2, E.QExpr>, +hok: {EP.allok(B, rows) == True{} : Bool})
  -> {EL.cz(m, RF.Res.p(EL.resid(rows, e))) == S.Z.add(S.Z.mul(S.Zpos{RF.Res.bt(EL.resid(rows, e))}, EL.cz(m, EP.NE(e))), EL.cz(m, EP.comb(RF.Res.cb(EL.resid(rows, e)), B))) : S.Z}:
  %EP.cz_comb(m, RF.Res.cb(EL.resid(rows, e)), B) : {EL.cz(m, RF.Res.p(EL.resid(rows, e))) == S.Z.add(S.Z.mul(S.Zpos{RF.Res.bt(EL.resid(rows, e))}, EL.cz(m, EP.NE(e))), _) : S.Z}
  rel_proj(m, EL.resid(rows, e), e, B, EP.resid_rel(m, rows, e, B, hok))

# the residual is bt e plus the basis' combination, under phi too
def phi_rel(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +rows: List<&2, EL.Row>, +e: E.QExpr, +B: List<&2, E.QExpr>, +hok: {EP.allok(B, rows) == True{} : Bool})
  -> {IP.phi(~F, ms, cs, RF.Res.p(EL.resid(rows, e))) == O.add(F, O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, e))), IP.phi(~F, ms, cs, EP.NE(e))), IP.phi(~F, ms, cs, EP.comb(RF.Res.cb(EL.resid(rows, e)), B))) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      FR.fring_eq(~F, [O.ofp(~F, RF.Res.bt(EL.resid(rows, e)))], E.ZCst{S.Z0{}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}}, {==})
    case Nil{} Con{c, ct}:
      FR.fring_eq(~F, [O.ofp(~F, RF.Res.bt(EL.resid(rows, e)))], E.ZCst{S.Z0{}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}}, {==})
    case Con{m, mt} Nil{}:
      FR.fring_eq(~F, [O.ofp(~F, RF.Res.bt(EL.resid(rows, e)))], E.ZCst{S.Z0{}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}}, {==})
    case Con{+m, +mt} Con{+c, +ct}:
      %Equal.sym(O.C(F), O.mul(F, c, O.ofz(~F, EL.cz(m, RF.Res.p(EL.resid(rows, e))))), O.add(F, O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, e))), O.mul(F, c, O.ofz(~F, EL.cz(m, EP.NE(e))))), O.mul(F, c, O.ofz(~F, EL.cz(m, EP.comb(RF.Res.cb(EL.resid(rows, e)), B))))),
          phi_t(~F, c, RF.Res.bt(EL.resid(rows, e)), EL.cz(m, EP.NE(e)), EL.cz(m, EP.comb(RF.Res.cb(EL.resid(rows, e)), B)), EL.cz(m, RF.Res.p(EL.resid(rows, e))), cz_rel(m, rows, e, B, hok)))
        : {O.add(F, _, IP.phi(~F, mt, ct, RF.Res.p(EL.resid(rows, e)))) == O.add(F, O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, e))), IP.phi(~F, Con{m, mt}, Con{c, ct}, EP.NE(e))), IP.phi(~F, Con{m, mt}, Con{c, ct}, EP.comb(RF.Res.cb(EL.resid(rows, e)), B))) : O.C(F)}
      %Equal.sym(O.C(F), IP.phi(~F, mt, ct, RF.Res.p(EL.resid(rows, e))), O.add(F, O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, e))), IP.phi(~F, mt, ct, EP.NE(e))), IP.phi(~F, mt, ct, EP.comb(RF.Res.cb(EL.resid(rows, e)), B))), phi_rel(~F, mt, ct, rows, e, B, hok))
        : {O.add(F, O.add(F, O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, e))), O.mul(F, c, O.ofz(~F, EL.cz(m, EP.NE(e))))), O.mul(F, c, O.ofz(~F, EL.cz(m, EP.comb(RF.Res.cb(EL.resid(rows, e)), B))))), _) == O.add(F, O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, e))), IP.phi(~F, Con{m, mt}, Con{c, ct}, EP.NE(e))), IP.phi(~F, Con{m, mt}, Con{c, ct}, EP.comb(RF.Res.cb(EL.resid(rows, e)), B))) : O.C(F)}
      FR.fring_eq(~F, [O.ofp(~F, RF.Res.bt(EL.resid(rows, e))), c, O.ofz(~F, EL.cz(m, EP.NE(e))), O.ofz(~F, EL.cz(m, EP.comb(RF.Res.cb(EL.resid(rows, e)), B))), IP.phi(~F, mt, ct, EP.NE(e)), IP.phi(~F, mt, ct, EP.comb(RF.Res.cb(EL.resid(rows, e)), B))], E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}, E.ZVar{5n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{4n}}}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZVar{5n}}}, {==})

def lenr_proj(r: EL.Res, +k: Nat, h: EP.LenR(r, k)) -> {EP.vlen(RF.Res.cb(r)) == k : Nat}:
  match r:
    case EL.Res{p, cb, bt}:
      h

# with the basis killed, phi(residual) = bt phi(e)
def side_phi(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, +rows: List<&2, EL.Row>, +e: E.QExpr, +B: List<&2, E.QExpr>,
  +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat}, hp: IP.PZB(~F, ms, cs, B, SV.neqs(B)))
  -> {IP.phi(~F, ms, cs, RF.Res.p(EL.resid(rows, e))) == O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, e))), IP.phi(~F, ms, cs, EP.NE(e))) : O.C(F)}:
  %Equal.sym(O.C(F), IP.phi(~F, ms, cs, RF.Res.p(EL.resid(rows, e))), O.add(F, O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, e))), IP.phi(~F, ms, cs, EP.NE(e))), IP.phi(~F, ms, cs, EP.comb(RF.Res.cb(EL.resid(rows, e)), B))), phi_rel(~F, ms, cs, rows, e, B, EP.rinv_allok(B, rows, 0n, hr))) : {_ == O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, e))), IP.phi(~F, ms, cs, EP.NE(e))) : O.C(F)}
  %IP.phi_comb(~F, ms, cs, RF.Res.cb(EL.resid(rows, e)), B)
    : {O.add(F, O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, e))), IP.phi(~F, ms, cs, EP.NE(e))), _) == O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, e))), IP.phi(~F, ms, cs, EP.NE(e))) : O.C(F)}
  %Equal.sym(O.C(F), IP.fphis(~F, ms, cs, RF.Res.cb(EL.resid(rows, e)), B), O.zero(F), IP.fphis_zero(~F, ms, cs, RF.Res.cb(EL.resid(rows, e)), B, SV.neqs(B), hp,
      (%Equal.sym(Nat, EP.vlen(RF.Res.cb(EL.resid(rows, e))), SV.neqs(B), Equal.trans(Nat, EP.vlen(RF.Res.cb(EL.resid(rows, e))), EL.rlen(rows), SV.neqs(B), lenr_proj(EL.resid(rows, e), EL.rlen(rows), EP.resid_len(rows, e, EP.rinv_cblt(B, rows, 0n, EL.rlen(rows), hr, KA.natle_refl(EL.rlen(rows))))), hl))
         : {KA.natle(_, SV.neqs(B)) == True{} : Bool}
       KA.natle_refl(SV.neqs(B)))))
    : {O.add(F, O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, e))), IP.phi(~F, ms, cs, EP.NE(e))), _) == O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, e))), IP.phi(~F, ms, cs, EP.NE(e))) : O.C(F)}
  Equal.sym(O.C(F), O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, e))), IP.phi(~F, ms, cs, EP.NE(e))), O.add(F, O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, e))), IP.phi(~F, ms, cs, EP.NE(e))), O.zero(F)), FL.add_zero(~F, O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, e))), IP.phi(~F, ms, cs, EP.NE(e)))))

# Every equation is killed
# ------------------------

def pzb_pre(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, B: List<&2, E.QExpr>, +X: List<&2, E.QExpr>, h: IP.PZB(~F, ms, cs, RP2.qcat(B, X), SV.neqs(RP2.qcat(B, X))))
  -> IP.PZB(~F, ms, cs, B, SV.neqs(B)):
  match B:
    case Nil{}:
      Unit{}
    case Con{+b, +bs}:
      (h1, h2) = h
      (h1, pzb_pre(~F, ms, cs, bs, X, h2))

def pzb_last(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, B: List<&2, E.QExpr>, +e: E.QExpr, h: IP.PZB(~F, ms, cs, EP.qsnoc(B, e), SV.neqs(EP.qsnoc(B, e))))
  -> {IP.phi(~F, ms, cs, EP.NE(e)) == O.zero(F) : O.C(F)}:
  match B:
    case Nil{}:
      (h1, h2) = h
      h1
    case Con{b, +bs}:
      (h1, h2) = h
      pzb_last(~F, ms, cs, bs, e, h2)

# psi kills each equation of es
def AllK(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, es: List<&2, E.QExpr>) -> Data:
  match es:
    case Nil{}:
      Unit
    case Con{e, t}:
      M.Both({IP.psi(~F, ms, cs, e) == O.zero(F) : O.C(F)}, AllK(~F, ms, cs, t))

def drop_qz.r(+B: List<&2, E.QExpr>, +e: E.QExpr, r: EL.Res, hrel: @m: List<&2, Nat> -> EP.Rel(m, r, e, B), hnil: {EP.isnil(EP.resp(r)) == True{} : Bool})
  -> {QN.qzero(E.QSub{e, SV.lin(DR.dropls(DR.rescb(r), DR.resbt(r), e, B), B)}) == True{} : Bool}:
  match r:
    case EL.Res{+p, +cb, +bt}:
      DR.qn_isnil(R.norm(QN.clr(E.QSub{e, SV.lin(DR.dropls(cb, bt, e, B), B)})),
        EP.red_zero(R.norm(QN.clr(E.QSub{e, SV.lin(DR.dropls(cb, bt, e, B), B)})), RP.norm_red(QN.clr(E.QSub{e, SV.lin(DR.dropls(cb, bt, e, B), B)})),
          m => DR.drop_fn(cb, bt, e, B, m2 => DR.nil_rel(m2, p, cb, bt, e, B, hrel, hnil), m)))

# a dropped equation is the basis' combination, as a computed identity
def drop_qz(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, +h: {EP.rinv(B, rows, 0n) == True{} : Bool}, hnil: {EP.isnil(EP.resp(EL.resid(rows, e))) == True{} : Bool})
  -> {QN.qzero(E.QSub{e, SV.lin(DR.dropls(DR.rescb(EL.resid(rows, e)), DR.resbt(EL.resid(rows, e)), e, B), B)}) == True{} : Bool}:
  drop_qz.r(B, e, EL.resid(rows, e), m => EP.resid_rel(m, rows, e, B, EP.rinv_allok(B, rows, 0n, h)), hnil)

def nil_true.p(p: List<&2, R.ZTerm>, h: {True{} == RF.isnilp(p) : Bool}) -> {EP.isnil(p) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{x, t}:
      absurd({EP.isnil(Con{x, t}) == True{} : Bool}, KA.tf(h))

def nil_true(r: EL.Res, h: {True{} == RF.isnilp(RF.Res.p(r)) : Bool}) -> {EP.isnil(EP.resp(r)) == True{} : Bool}:
  match r:
    case EL.Res{p, cb, bt}:
      nil_true.p(p, h)


def kill_head(~F: O.OField, b: Bool, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +e: E.QExpr, +t: List<&2, E.QExpr>,
  hb: {b == RF.isnilp(RF.Res.p(EL.resid(rows, e))) : Bool}, +hr: {EP.rinv(B, rows, 0n) == True{} : Bool},
  hp: IP.PZB(~F, ms, cs, RP2.qcat(RP2.bnext(b, B, e), RP2.kept(RF.Walk.keep(RF.walk(t, RF.walk.next(b, rows, EL.resid(rows, e)))), t)), SV.neqs(RP2.qcat(RP2.bnext(b, B, e), RP2.kept(RF.Walk.keep(RF.walk(t, RF.walk.next(b, rows, EL.resid(rows, e)))), t))))) -> {IP.psi(~F, ms, cs, e) == O.zero(F) : O.C(F)}:
  match b:
    case True{}:
      +hpb = pzb_pre(~F, ms, cs, B, RP2.kept(RF.Walk.keep(RF.walk(t, RF.walk.next(b, rows, EL.resid(rows, e)))), t), hp)
      Equal.trans(O.C(F), IP.psi(~F, ms, cs, e), IP.psum(~F, ms, cs, DR.dropls(DR.rescb(EL.resid(rows, e)), DR.resbt(EL.resid(rows, e)), e, B), B), O.zero(F),
        IP.psi_eq(~F, ms, cs, e, DR.dropls(DR.rescb(EL.resid(rows, e)), DR.resbt(EL.resid(rows, e)), e, B), B, drop_qz(B, rows, e, hr, nil_true(EL.resid(rows, e), hb))),
        Equal.trans(O.C(F), IP.psum(~F, ms, cs, DR.dropls(DR.rescb(EL.resid(rows, e)), DR.resbt(EL.resid(rows, e)), e, B), B), IP.fpsi(~F, ms, cs, DR.dropls(DR.rescb(EL.resid(rows, e)), DR.resbt(EL.resid(rows, e)), e, B), B), O.zero(F),
          IP.psum_fpsi(~F, ms, cs, DR.dropls(DR.rescb(EL.resid(rows, e)), DR.resbt(EL.resid(rows, e)), e, B), B),
          IP.fpsi_zero(~F, ms, cs, DR.dropls(DR.rescb(EL.resid(rows, e)), DR.resbt(EL.resid(rows, e)), e, B), B, hpb)))
    case False{}:
      IP.psi_zero(~F, ms, cs, e, pzb_last(~F, ms, cs, B, e, pzb_pre(~F, ms, cs, EP.qsnoc(B, e), RP2.kept(RF.Walk.keep(RF.walk(t, RF.walk.next(b, rows, EL.resid(rows, e)))), t), hp)))


def walk_kill(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, es: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>,
  +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat}, +hp: IP.PZB(~F, ms, cs, RP2.wB(es, rows, B), SV.neqs(RP2.wB(es, rows, B)))) -> AllK(~F, ms, cs, es):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      +st = RP2.step_inv(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, B, e, {==}, hr, hl)
      (kill_head(~F, RF.isnilp(RF.Res.p(EL.resid(rows, e))), ms, cs, rows, B, e, t, {==}, hr,
         (%RP2.wB_kept(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)), RP2.bnext(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e)) : IP.PZB(~F, ms, cs, _, SV.neqs(_))
           hp)),
       walk_kill(~F, ms, cs, t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)), RP2.bnext(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e),
         LX.both_l({EP.rinv(RP2.bnext(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e), RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)), 0n) == True{} : Bool}, {EL.rlen(RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e))) == SV.neqs(RP2.bnext(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e)) : Nat}, st),
         LX.both_r({EP.rinv(RP2.bnext(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e), RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)), 0n) == True{} : Bool}, {EL.rlen(RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e))) == SV.neqs(RP2.bnext(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e)) : Nat}, st), hp))


def w_rlen(+es: List<&2, E.QExpr>) -> {EL.rlen(RF.Walk.rows(RF.walk(es, Nil{}))) == SV.neqs(RP2.kept(RF.Walk.keep(RF.walk(es, Nil{})), es)) : Nat}:
  %RP2.wB_kept(es, Nil{}, Nil{}) : {EL.rlen(RF.Walk.rows(RF.walk(es, Nil{}))) == SV.neqs(_) : Nat}
  LX.both_r({EP.rinv(RP2.wB(es, Nil{}, Nil{}), RF.Walk.rows(RF.walk(es, Nil{})), 0n) == True{} : Bool}, {EL.rlen(RF.Walk.rows(RF.walk(es, Nil{}))) == SV.neqs(RP2.wB(es, Nil{}, Nil{})) : Nat}, RP2.walk_inv(es, Nil{}, Nil{}, {==}, {==}))


# the functional kills the basis
def pz_basis(~F: O.OField, +ms0: List<&2, List<&2, Nat>>, +cs0: List<&2, O.C(F)>, +es: List<&2, E.QExpr>) -> IP.PZB(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), ms0), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), ms0, cs0), RP2.kept(RF.Walk.keep(RF.walk(es, Nil{})), es), SV.neqs(RP2.kept(RF.Walk.keep(RF.walk(es, Nil{})), es))):
  %w_rlen(es) : IP.PZB(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), ms0), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), ms0, cs0), RP2.kept(RF.Walk.keep(RF.walk(es, Nil{})), es), _)
  IP.tri(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), ms0), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), ms0, cs0), RP2.kept(RF.Walk.keep(RF.walk(es, Nil{})), es), RF.Walk.rows(RF.walk(es, Nil{})), 0n, RP2.w_rinv(es), b_allz(~F, RF.Walk.rows(RF.walk(es, Nil{})), ms0, cs0, RP2.kept(RF.Walk.keep(RF.walk(es, Nil{})), es), RP2.w_allok(es), EP.rinv_ech(RP2.kept(RF.Walk.keep(RF.walk(es, Nil{})), es), RF.Walk.rows(RF.walk(es, Nil{})), 0n, RP2.w_rinv(es))), IP.pzb0(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), ms0), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), ms0, cs0), RP2.kept(RF.Walk.keep(RF.walk(es, Nil{})), es)),
    (%w_rlen(es) : {KA.natle(EL.rlen(RF.Walk.rows(RF.walk(es, Nil{}))), _) == True{} : Bool}
      KA.natle_refl(EL.rlen(RF.Walk.rows(RF.walk(es, Nil{}))))))

# and so every equation of es
def kill_all(~F: O.OField, +ms0: List<&2, List<&2, Nat>>, +cs0: List<&2, O.C(F)>, +es: List<&2, E.QExpr>) -> AllK(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), ms0), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), ms0, cs0), es):
  walk_kill(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), ms0), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), ms0, cs0), es, Nil{}, Nil{}, {==}, {==},
    (%Equal.sym(List<&2, E.QExpr>, RP2.wB(es, Nil{}, Nil{}), RP2.kept(RF.Walk.keep(RF.walk(es, Nil{})), es), RP2.wB_kept(es, Nil{}, Nil{})) : IP.PZB(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), ms0), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), ms0, cs0), _, SV.neqs(_))
      pz_basis(~F, ms0, cs0, es)))
