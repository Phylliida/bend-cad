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

# Signs
# -----

# a side's sign at the point: > 0 lexicographically if strict, >= 0 if not
def SideOK(~F: O.OField, +x0: O.C(F), +x1: O.C(F), s: SK.Side) -> Data:
  match s:
    case SK.Gt0{e}:
      LX.LPos(~F, x0, x1)
    case SK.Ge0{e}:
      LX.LNonneg(~F, x0, x1)

def le_mul_pos(~F: O.OField, +c: O.C(F), +x: O.C(F), hc: O.lt(F, O.zero(F), c), hx: O.le(~F, O.zero(F), x)) -> O.le(~F, O.zero(F), O.mul(F, c, x)):
  match hx:
    case Inl{a}:
      Inl{O.lt_mul(F)(c, x)(hc)(a)}
    case Inr{e}:
      Inr{Equal.sym(O.C(F), O.mul(F, c, x), O.zero(F), LX.mul_zero_r(~F, c, x, Equal.sym(O.C(F), O.zero(F), x, e)))}

def lnn_scale(~F: O.OField, +c: O.C(F), +x0: O.C(F), +x1: O.C(F), +hc: O.lt(F, O.zero(F), c), hx: LX.LNonneg(~F, x0, x1)) -> LX.LNonneg(~F, O.mul(F, c, x0), O.mul(F, c, x1)):
  match hx:
    case Inl{a}:
      Inl{O.lt_mul(F)(c, x0)(hc)(a)}
    case Inr{+p}:
      Inr{(LX.mul_zero_r(~F, c, x0, LX.both_l({x0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), x1), p)), le_mul_pos(~F, c, x1, hc, LX.both_r({x0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), x1), p)))}

def lpos_scale(~F: O.OField, +c: O.C(F), +x0: O.C(F), +x1: O.C(F), +hc: O.lt(F, O.zero(F), c), hx: LX.LPos(~F, x0, x1)) -> LX.LPos(~F, O.mul(F, c, x0), O.mul(F, c, x1)):
  match hx:
    case Inl{a}:
      Inl{O.lt_mul(F)(c, x0)(hc)(a)}
    case Inr{+p}:
      Inr{(LX.mul_zero_r(~F, c, x0, LX.both_l({x0 == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), x1), p)), O.lt_mul(F)(c, x1)(hc)(LX.both_r({x0 == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), x1), p)))}

def sideok_scale(~F: O.OField, +c: O.C(F), +x0: O.C(F), +x1: O.C(F), s: SK.Side, hc: O.lt(F, O.zero(F), c), h: SideOK(~F, x0, x1, s)) -> SideOK(~F, O.mul(F, c, x0), O.mul(F, c, x1), s):
  match s:
    case SK.Gt0{e}:
      lpos_scale(~F, c, x0, x1, hc, h)
    case SK.Ge0{e}:
      lnn_scale(~F, c, x0, x1, hc, h)

# x - 1 >= 0: x > 0
def pos_of_sub1(~F: O.OField, +x: O.C(F), h: O.le(~F, O.zero(F), O.sub(~F, x, O.one(F)))) -> O.lt(F, O.zero(F), x):
  match h:
    case Inl{a}:
      O.lt_trans(F)(O.zero(F), O.one(F), x)(O.zero_lt_one(F))(QE.lt_of_sub(~F, O.one(F), x, a))
    case Inr{e}:
      (%Equal.sym(O.C(F), x, O.one(F), FO.eq_of_sub(~F, x, O.one(F), Equal.sym(O.C(F), O.zero(F), O.sub(~F, x, O.one(F)), e))) : O.lt(F, O.zero(F), _)
        O.zero_lt_one(F))

# (x0, x1 - [s strict]) >= 0: the side's sign
def sidep(~F: O.OField, s: SK.Side, +x0: O.C(F), +x1: O.C(F), h: LX.LNonneg(~F, x0, O.sub(~F, x1, O.ofz(~F, SX.ind(RF.strict(s)))))) -> SideOK(~F, x0, x1, s):
  match s:
    case SK.Gt0{e}:
      match h:
        case Inl{a}:
          Inl{a}
        case Inr{+p}:
          Inr{(LX.both_l({x0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), O.sub(~F, x1, O.one(F))), p), pos_of_sub1(~F, x1, LX.both_r({x0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), O.sub(~F, x1, O.one(F))), p)))}
    case SK.Ge0{e}:
      (%FR.fring_eq(~F, [x1], E.ZSub{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZVar{0n}, {==}) : LX.LNonneg(~F, x0, _)
        h)

# The sides at the point
# ----------------------

def ineq_of(+ys: List<&2, List<&2, Nat>>, +rows: List<&2, EL.Row>, +s: SK.Side) -> SX.Ineq:
  SX.Ineq{RF.coefs(ys, RF.Res.p(EL.resid(rows, RF.sexpr(s)))), EL.cz(Nil{}, RF.Res.p(EL.resid(rows, RF.sexpr(s)))), RF.strict(s)}

def qat_ineqs(+ys: List<&2, List<&2, Nat>>, +rows: List<&2, EL.Row>, ss: List<&2, SK.Side>, k: Nat, hk: {SX.ltn(k, SV.slen(ss)) == True{} : Bool})
  -> {RN.qat(RF.ineqs(ys, RF.sres(rows, ss), ss), k) == ineq_of(ys, rows, SV.side_at(ss, k)) : SX.Ineq}:
  match ss k:
    case Nil{} k:
      absurd({RN.qat(Nil{}, k) == ineq_of(ys, rows, SV.side_at(Nil{}, k)) : SX.Ineq}, KA.ft(SP.ltn0(k, hk)))
    case Con{s, st} 0n:
      {==}
    case Con{s, st} 1n+j:
      qat_ineqs(ys, rows, st, j, hk)

def vlen_coefs(ys: List<&2, List<&2, Nat>>, +p: List<&2, R.ZTerm>) -> {SX.vlen(RF.coefs(ys, p)) == RF.mlen(ys) : Nat}:
  match ys:
    case Nil{}:
      {==}
    case Con{y, +t}:
      %vlen_coefs(t, p) : {1n+SX.vlen(RF.coefs(t, p)) == 1n+_ : Nat}
      {==}

# the LP's a_k has one entry per monomial left
def lpwf_ineqs(+ys: List<&2, List<&2, Nat>>, rs: List<&2, EL.Res>, ss: List<&2, SK.Side>) -> {SP.lpwf.go(RF.ineqs(ys, rs, ss), RF.mlen(ys)) == True{} : Bool}:
  match rs ss:
    case Nil{} ss:
      {==}
    case Con{r, rt} Nil{}:
      {==}
    case Con{+r, +rt} Con{s, +st}:
      KA.band_i(KA.natle(SX.vlen(RF.coefs(ys, RF.Res.p(r))), RF.mlen(ys)), SP.lpwf.go(RF.ineqs(ys, rt, st), RF.mlen(ys)),
        (%Equal.sym(Nat, SX.vlen(RF.coefs(ys, RF.Res.p(r))), RF.mlen(ys), vlen_coefs(ys, RF.Res.p(r))) : {KA.natle(_, RF.mlen(ys)) == True{} : Bool}
          KA.natle_refl(RF.mlen(ys))),
        lpwf_ineqs(ys, rt, st))


def lp_wf(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>) -> {SP.lpwf(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)) == True{} : Bool}:
  lpwf_ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)

def zp_side(+es: List<&2, E.QExpr>, +e: E.QExpr) -> {EP.zp(RF.Walk.rows(RF.walk(es, Nil{})), EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), e)) == True{} : Bool}:
  EP.reduce_zp(RF.Walk.rows(RF.walk(es, Nil{})), EL.start(e, EL.rlen(RF.Walk.rows(RF.walk(es, Nil{})))), RP2.kept(RF.Walk.keep(RF.walk(es, Nil{})), es), RP2.w_allok(es), EP.rinv_ech(RP2.kept(RF.Walk.keep(RF.walk(es, Nil{})), es), RF.Walk.rows(RF.walk(es, Nil{})), 0n, RP2.w_rinv(es)))

# the functional on side k's residual: w b_k + a_k . Y
def sk_phi(~F: O.OField, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +k: Nat, +w: O.C(F), +Y: M.Vec(~F))
  -> {IP.phi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{w, Y}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))) == O.add(F, O.mul(F, w, O.ofz(~F, EL.cz(Nil{}, RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))))), SP.zdot(~F, RF.coefs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), Y)) : O.C(F)}:
  %Equal.sym(O.C(F), IP.phi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{w, Y}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), IP.phi(~F, Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{w, Y}, RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), b_res.r(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{w, Y}, EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))), zp_side(es, RF.sexpr(SV.side_at(ss, k)))))
    : {_ == O.add(F, O.mul(F, w, O.ofz(~F, EL.cz(Nil{}, RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))))), SP.zdot(~F, RF.coefs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), Y)) : O.C(F)}
  %phi_coefs(~F, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), Y, RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))) : {O.add(F, O.mul(F, w, O.ofz(~F, EL.cz(Nil{}, RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))))), IP.phi(~F, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), Y, RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k)))))) == O.add(F, O.mul(F, w, O.ofz(~F, EL.cz(Nil{}, RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))))), _) : O.C(F)}
  {==}

def hk_m(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +k: Nat, hk: {SX.ltn(k, SV.slen(ss)) == True{} : Bool}) -> {SX.ltn(k, SX.LP.m(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss))) == True{} : Bool}:
  %Equal.sym(Nat, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SV.slen(ss), RP2.qlen_ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.Walk.rows(RF.walk(es, Nil{})), ss)) : {SX.ltn(k, _) == True{} : Bool}
  hk

def val0(~F: O.OField, +b: S.Z, +z: O.C(F)) -> {O.add(F, O.mul(F, O.one(F), O.ofz(~F, b)), z) == O.sub(~F, z, O.ofz(~F, S.Z.neg(b))) : O.C(F)}:
  %FR.ofz_neg(~F, b) : {O.add(F, O.mul(F, O.one(F), O.ofz(~F, b)), z) == O.sub(~F, z, _) : O.C(F)}
  FR.fring_eq(~F, [O.ofz(~F, b), z], E.ZAdd{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, E.ZVar{1n}}, E.ZSub{E.ZVar{1n}, E.ZNeg{E.ZVar{0n}}}, {==})

def val1(~F: O.OField, +b: S.Z, +z: O.C(F)) -> {O.add(F, O.mul(F, O.zero(F), O.ofz(~F, b)), z) == z : O.C(F)}:
  FR.fring_eq(~F, [O.ofz(~F, b), z], E.ZAdd{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZVar{1n}}, E.ZVar{1n}, {==})

def sv_coefs(~F: O.OField, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +t: SX.Tab, +h: {SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)) == SX.Sat{t} : SX.Run}, +k: Nat, +hk: {SX.ltn(k, SV.slen(ss)) == True{} : Bool}, +wv: M.Vec(~F))
  -> {SP.rv(~F, SX.rowat(SX.Tab.rows(t), k), wv) == SP.zdot(~F, RF.coefs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), wv))) : O.C(F)}:
  %qat_ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.Walk.rows(RF.walk(es, Nil{})), ss, k, hk) : {SP.rv(~F, SX.rowat(SX.Tab.rows(t), k), wv) == SP.zdot(~F, Ineq.a(_), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), wv))) : O.C(F)}
  s_val(~F, RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), lp_wf(es, ss), t, h, wv, k, hk_m(es, ss, k, hk))

# at the point, side k's residual is lexicographically at or above [strict]
def sk_lex(~F: O.OField, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +t: SX.Tab, +h: {SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)) == SX.Sat{t} : SX.Run}, +k: Nat, +hk: {SX.ltn(k, SV.slen(ss)) == True{} : Bool})
  -> LX.LNonneg(~F, IP.phi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), O.sub(~F, IP.phi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), O.ofz(~F, SX.ind(RF.strict(SV.side_at(ss, k)))))):
  %Equal.sym(O.C(F), IP.phi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(t), k), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))), O.ofz(~F, S.Z.neg(EL.cz(Nil{}, RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k)))))))),
      Equal.trans(O.C(F), IP.phi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), O.add(F, O.mul(F, O.one(F), O.ofz(~F, EL.cz(Nil{}, RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))))), SP.zdot(~F, RF.coefs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss))))))), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(t), k), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))), O.ofz(~F, S.Z.neg(EL.cz(Nil{}, RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k)))))))),
        sk_phi(~F, es, ss, k, O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))),
        (%Equal.sym(O.C(F), SP.rv(~F, SX.rowat(SX.Tab.rows(t), k), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))), SP.zdot(~F, RF.coefs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))), sv_coefs(~F, es, ss, t, h, k, hk, RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss))))) : {O.add(F, O.mul(F, O.one(F), O.ofz(~F, EL.cz(Nil{}, RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))))), SP.zdot(~F, RF.coefs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss))))))) == O.sub(~F, _, O.ofz(~F, S.Z.neg(EL.cz(Nil{}, RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k)))))))) : O.C(F)}
          val0(~F, EL.cz(Nil{}, RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), SP.zdot(~F, RF.coefs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss))))))))))
    : LX.LNonneg(~F, _, O.sub(~F, IP.phi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), O.ofz(~F, SX.ind(RF.strict(SV.side_at(ss, k))))))
  %Equal.sym(O.C(F), IP.phi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), SP.rv(~F, SX.rowat(SX.Tab.rows(t), k), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))),
      Equal.trans(O.C(F), IP.phi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), O.add(F, O.mul(F, O.zero(F), O.ofz(~F, EL.cz(Nil{}, RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))))), SP.zdot(~F, RF.coefs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss))))))), SP.rv(~F, SX.rowat(SX.Tab.rows(t), k), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))),
        sk_phi(~F, es, ss, k, O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))),
        (%Equal.sym(O.C(F), SP.rv(~F, SX.rowat(SX.Tab.rows(t), k), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))), SP.zdot(~F, RF.coefs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))), sv_coefs(~F, es, ss, t, h, k, hk, RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss))))) : {O.add(F, O.mul(F, O.zero(F), O.ofz(~F, EL.cz(Nil{}, RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))))), SP.zdot(~F, RF.coefs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss))))))) == _ : O.C(F)}
          val1(~F, EL.cz(Nil{}, RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), SP.zdot(~F, RF.coefs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss))))))))))
    : LX.LNonneg(~F, O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(t), k), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))), O.ofz(~F, S.Z.neg(EL.cz(Nil{}, RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k)))))))), O.sub(~F, _, O.ofz(~F, SX.ind(RF.strict(SV.side_at(ss, k))))))
  (%qat_ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.Walk.rows(RF.walk(es, Nil{})), ss, k, hk) : LX.LNonneg(~F, O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(t), k), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))), O.ofz(~F, S.Z.neg(RN.Ineq.b(_)))), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(t), k), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))), O.ofz(~F, SX.ind(RN.Ineq.s(_)))))
    RN.noviol_f(~F, SX.rowat(SX.Tab.rows(t), k), SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), RN.qat(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), k), s_noviol(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), lp_wf(es, ss), t, h, k, hk_m(es, ss, k, hk))))


# psi on a side is a positive multiple of phi on its residual
def psi_val(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, +rows: List<&2, EL.Row>, +s: SK.Side, +B: List<&2, E.QExpr>,
  +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat}, hp: IP.PZB(~F, ms, cs, B, SV.neqs(B)))
  -> {IP.psi(~F, ms, cs, SV.sexpr(s)) == O.mul(F, O.mul(F, O.inv(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, RF.sexpr(s))))), O.inv(F, O.ofp(~F, QN.den(SV.sexpr(s))))), IP.phi(~F, ms, cs, RF.Res.p(EL.resid(rows, RF.sexpr(s))))) : O.C(F)}:
  %Equal.sym(O.C(F), IP.psi(~F, ms, cs, SV.sexpr(s)), O.mul(F, IP.phi(~F, ms, cs, EP.NE(SV.sexpr(s))), O.inv(F, O.ofp(~F, QN.den(SV.sexpr(s))))), IP.psi_phi(~F, ms, cs, SV.sexpr(s)))
    : {_ == O.mul(F, O.mul(F, O.inv(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, RF.sexpr(s))))), O.inv(F, O.ofp(~F, QN.den(SV.sexpr(s))))), IP.phi(~F, ms, cs, RF.Res.p(EL.resid(rows, RF.sexpr(s))))) : O.C(F)}
  %Equal.sym(O.C(F), IP.phi(~F, ms, cs, RF.Res.p(EL.resid(rows, RF.sexpr(s)))), O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, RF.sexpr(s)))), IP.phi(~F, ms, cs, EP.NE(RF.sexpr(s)))), side_phi(~F, ms, cs, rows, RF.sexpr(s), B, hr, hl, hp))
    : {O.mul(F, IP.phi(~F, ms, cs, EP.NE(SV.sexpr(s))), O.inv(F, O.ofp(~F, QN.den(SV.sexpr(s))))) == O.mul(F, O.mul(F, O.inv(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, RF.sexpr(s))))), O.inv(F, O.ofp(~F, QN.den(SV.sexpr(s))))), _) : O.C(F)}
  %Equal.sym(E.QExpr, RF.sexpr(s), SV.sexpr(s), RP2.sexpr_eq(s))
    : {O.mul(F, IP.phi(~F, ms, cs, EP.NE(SV.sexpr(s))), O.inv(F, O.ofp(~F, QN.den(SV.sexpr(s))))) == O.mul(F, O.mul(F, O.inv(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, RF.sexpr(s))))), O.inv(F, O.ofp(~F, QN.den(SV.sexpr(s))))), O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, RF.sexpr(s)))), IP.phi(~F, ms, cs, EP.NE(_)))) : O.C(F)}
  FO.eq_of_sub(~F, O.mul(F, IP.phi(~F, ms, cs, EP.NE(SV.sexpr(s))), O.inv(F, O.ofp(~F, QN.den(SV.sexpr(s))))), O.mul(F, O.mul(F, O.inv(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, RF.sexpr(s))))), O.inv(F, O.ofp(~F, QN.den(SV.sexpr(s))))), O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, RF.sexpr(s)))), IP.phi(~F, ms, cs, EP.NE(SV.sexpr(s))))), FO.cert1(~F, O.sub(~F, O.mul(F, IP.phi(~F, ms, cs, EP.NE(SV.sexpr(s))), O.inv(F, O.ofp(~F, QN.den(SV.sexpr(s))))), O.mul(F, O.mul(F, O.inv(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, RF.sexpr(s))))), O.inv(F, O.ofp(~F, QN.den(SV.sexpr(s))))), O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, RF.sexpr(s)))), IP.phi(~F, ms, cs, EP.NE(SV.sexpr(s)))))), O.neg(F, O.mul(F, IP.phi(~F, ms, cs, EP.NE(SV.sexpr(s))), O.inv(F, O.ofp(~F, QN.den(SV.sexpr(s)))))), O.sub(~F, O.mul(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, RF.sexpr(s)))), O.inv(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, RF.sexpr(s)))))), O.one(F)), FR.fring_eq(~F, [IP.phi(~F, ms, cs, EP.NE(SV.sexpr(s))), O.inv(F, O.ofp(~F, QN.den(SV.sexpr(s)))), O.ofp(~F, RF.Res.bt(EL.resid(rows, RF.sexpr(s)))), O.inv(F, O.ofp(~F, RF.Res.bt(EL.resid(rows, RF.sexpr(s)))))], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{3n}, E.ZVar{1n}}, E.ZMul{E.ZVar{2n}, E.ZVar{0n}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), QE.ofp_rel(~F, RF.Res.bt(EL.resid(rows, RF.sexpr(s))))))


# side k at the point
def side_k(~F: O.OField, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +t: SX.Tab, +h: {SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)) == SX.Sat{t} : SX.Run}, +k: Nat, +hk: {SX.ltn(k, SV.slen(ss)) == True{} : Bool})
  -> SideOK(~F, IP.psi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), SV.sexpr(SV.side_at(ss, k))), IP.psi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), SV.sexpr(SV.side_at(ss, k))), SV.side_at(ss, k)):
  %Equal.sym(O.C(F), IP.psi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), SV.sexpr(SV.side_at(ss, k))), O.mul(F, O.mul(F, O.inv(F, O.ofp(~F, RF.Res.bt(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k)))))), O.inv(F, O.ofp(~F, QN.den(SV.sexpr(SV.side_at(ss, k)))))), IP.phi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k)))))),
      psi_val(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), RF.Walk.rows(RF.walk(es, Nil{})), SV.side_at(ss, k), RP2.kept(RF.Walk.keep(RF.walk(es, Nil{})), es), RP2.w_rinv(es), w_rlen(es), pz_basis(~F, Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}, es)))
    : SideOK(~F, _, IP.psi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), SV.sexpr(SV.side_at(ss, k))), SV.side_at(ss, k))
  %Equal.sym(O.C(F), IP.psi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), SV.sexpr(SV.side_at(ss, k))), O.mul(F, O.mul(F, O.inv(F, O.ofp(~F, RF.Res.bt(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k)))))), O.inv(F, O.ofp(~F, QN.den(SV.sexpr(SV.side_at(ss, k)))))), IP.phi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k)))))),
      psi_val(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), RF.Walk.rows(RF.walk(es, Nil{})), SV.side_at(ss, k), RP2.kept(RF.Walk.keep(RF.walk(es, Nil{})), es), RP2.w_rinv(es), w_rlen(es), pz_basis(~F, Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}, es)))
    : SideOK(~F, O.mul(F, O.mul(F, O.inv(F, O.ofp(~F, RF.Res.bt(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k)))))), O.inv(F, O.ofp(~F, QN.den(SV.sexpr(SV.side_at(ss, k)))))), IP.phi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k)))))), _, SV.side_at(ss, k))
  sideok_scale(~F, O.mul(F, O.inv(F, O.ofp(~F, RF.Res.bt(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k)))))), O.inv(F, O.ofp(~F, QN.den(SV.sexpr(SV.side_at(ss, k)))))), IP.phi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), IP.phi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), SV.side_at(ss, k),
    O.lt_mul(F)(O.inv(F, O.ofp(~F, RF.Res.bt(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k)))))), O.inv(F, O.ofp(~F, QN.den(SV.sexpr(SV.side_at(ss, k))))))(RN.inv_pos(~F, RF.Res.bt(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))))(RN.inv_pos(~F, QN.den(SV.sexpr(SV.side_at(ss, k))))),
    sidep(~F, SV.side_at(ss, k), IP.phi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), IP.phi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), RF.Res.p(EL.resid(RF.Walk.rows(RF.walk(es, Nil{})), RF.sexpr(SV.side_at(ss, k))))), sk_lex(~F, es, ss, t, h, k, hk)))

# every side at the point
def AllS(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +c0: List<&2, O.C(F)>, +c1: List<&2, O.C(F)>, ss: List<&2, SK.Side>) -> Data:
  match ss:
    case Nil{}:
      Unit
    case Con{+s, t}:
      M.Both(SideOK(~F, IP.psi(~F, ms, c0, SV.sexpr(s)), IP.psi(~F, ms, c1, SV.sexpr(s)), s), AllS(~F, ms, c0, c1, t))

def sdrop(k: Nat, ss: List<&2, SK.Side>) -> List<&2, SK.Side>:
  match k ss:
    case 0n ss:
      ss
    case 1n+j Nil{}:
      Nil{}
    case 1n+j Con{s, t}:
      sdrop(j, t)

def shd(ss: List<&2, SK.Side>) -> SK.Side:
  match ss:
    case Nil{}:
      SK.Gt0{E.QCst{SV.qzero()}}
    case Con{s, t}:
      s

def stl(ss: List<&2, SK.Side>) -> List<&2, SK.Side>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{s, t}:
      t

def isnils(ss: List<&2, SK.Side>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{s, t}:
      False{}

def con_nil(+s: SK.Side, +t: List<&2, SK.Side>, h: {Con{s, t} == Nil{} : List<&2, SK.Side>}) -> Empty:
  KA.ft((%Equal.sym(List<&2, SK.Side>, Con{s, t}, Nil{}, h) : {isnils(_) == True{} : Bool}
    {==}))

def sdrop_con(k: Nat, ss: List<&2, SK.Side>, +s: SK.Side, +t: List<&2, SK.Side>, +h: {Con{s, t} == sdrop(k, ss) : List<&2, SK.Side>})
  -> M.Both({SV.side_at(ss, k) == s : SK.Side}, {t == sdrop(1n+k, ss) : List<&2, SK.Side>}):
  match k ss:
    case 0n Nil{}:
      absurd(M.Both({SV.side_at(Nil{}, 0n) == s : SK.Side}, {t == Nil{} : List<&2, SK.Side>}), con_nil(s, t, h))
    case 0n Con{+s2, +t2}:
      ((%h : {shd(_) == s : SK.Side}
         {==}),
       (%Equal.sym(List<&2, SK.Side>, Con{s, t}, Con{s2, t2}, h) : {stl(_) == t2 : List<&2, SK.Side>}
         {==}))
    case 1n+j Nil{}:
      absurd(M.Both({SV.side_at(Nil{}, 1n+j) == s : SK.Side}, {t == Nil{} : List<&2, SK.Side>}), con_nil(s, t, h))
    case 1n+j Con{s2, t2}:
      sdrop_con(j, t2, s, t, h)

def sdrop_lt(k: Nat, ss: List<&2, SK.Side>, +s: SK.Side, +t: List<&2, SK.Side>, h: {Con{s, t} == sdrop(k, ss) : List<&2, SK.Side>}) -> {SX.ltn(k, SV.slen(ss)) == True{} : Bool}:
  match k ss:
    case 0n Nil{}:
      absurd({SX.ltn(0n, 0n) == True{} : Bool}, con_nil(s, t, h))
    case 0n Con{s2, t2}:
      {==}
    case 1n+j Nil{}:
      absurd({SX.ltn(1n+j, 0n) == True{} : Bool}, con_nil(s, t, h))
    case 1n+j Con{s2, t2}:
      sdrop_lt(j, t2, s, t, h)

def allside(~F: O.OField, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +t: SX.Tab, +h: {SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)) == SX.Sat{t} : SX.Run}, sv: List<&2, SK.Side>, +k: Nat, +heq: {sv == sdrop(k, ss) : List<&2, SK.Side>}) -> AllS(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), sv):
  match sv:
    case Nil{}:
      Unit{}
    case Con{+s, +st}:
      +p = sdrop_con(k, ss, s, st, heq)
      ((%LX.both_l({SV.side_at(ss, k) == s : SK.Side}, {st == sdrop(1n+k, ss) : List<&2, SK.Side>}, p) : SideOK(~F, IP.psi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), SV.sexpr(_)), IP.psi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), SV.sexpr(_)), _)
         side_k(~F, es, ss, t, h, k, sdrop_lt(k, ss, s, st, heq))),
       allside(~F, es, ss, t, h, st, 1n+k, LX.both_r({SV.side_at(ss, k) == s : SK.Side}, {st == sdrop(1n+k, ss) : List<&2, SK.Side>}, p)))

# The constant 1
# --------------

def notnil(m: List<&2, Nat>) -> Bool:
  match m:
    case Nil{}:
      False{}
    case Con{v, vs}:
      True{}

def allcon(ms: List<&2, List<&2, Nat>>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case Con{m, t}:
      KA.band(notnil(m), allcon(t))

def pvcon(rows: List<&2, EL.Row>) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case Con{r, t}:
      KA.band(notnil(EP.rowpv(r)), pvcon(t))

def nn_cst(m: List<&2, Nat>, h: {RF.iscst(m) == False{} : Bool}) -> {notnil(m) == True{} : Bool}:
  match m:
    case Nil{}:
      absurd({notnil(Nil{}) == True{} : Bool}, KA.tf(h))
    case Con{v, vs}:
      {==}

def nn_row(r: EL.Row, h: {RF.iscst(RF.Row.pv(r)) == False{} : Bool}) -> {notnil(EP.rowpv(r)) == True{} : Bool}:
  match r:
    case EL.Row{p, cb, bt, pv}:
      nn_cst(pv, h)

# with no constant row, no pivot is 1
def crow_none(rows: List<&2, EL.Row>, +j: Nat, +h: {RF.crow(rows, j) == None{} : Maybe<&2, Nat>}) -> {pvcon(rows) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      KA.band_i(notnil(EP.rowpv(r)), pvcon(t),
        nn_row(r, UN.pick_none_l(RF.iscst(RF.Row.pv(r)), j, RF.crow(t, 1n+j), h)),
        crow_none(t, 1n+j, UN.pick_none_r(RF.iscst(RF.Row.pv(r)), j, RF.crow(t, 1n+j), h)))

def allcon_ins.d(o: Cmp, +m: List<&2, Nat>, +h0: List<&2, Nat>, +t: List<&2, List<&2, Nat>>, +hm: {notnil(m) == True{} : Bool}, +h: {allcon(Con{h0, t}) == True{} : Bool},
  ih: {allcon(RF.ins(m, t)) == True{} : Bool}) -> {allcon(RF.ins.dec(o, m, h0, t, RF.ins(m, t))) == True{} : Bool}:
  match o:
    case LT{}:
      KA.band_i(notnil(m), allcon(Con{h0, t}), hm, h)
    case EQ{}:
      h
    case GT{}:
      KA.band_i(notnil(h0), allcon(RF.ins(m, t)), KA.band_l(notnil(h0), allcon(t), h), ih)

def allcon_ins(+m: List<&2, Nat>, ys: List<&2, List<&2, Nat>>, +hm: {notnil(m) == True{} : Bool}, h: {allcon(ys) == True{} : Bool}) -> {allcon(RF.ins(m, ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      KA.band_i(notnil(m), True{}, hm, {==})
    case Con{+h0, +t}:
      +h2 = h
      allcon_ins.d(NR.mcmp(m, h0), m, h0, t, hm, h2, allcon_ins(m, t, hm, KA.band_r(notnil(h0), allcon(t), h2)))

def allcon_insnc(m: List<&2, Nat>, +ys: List<&2, List<&2, Nat>>, h: {allcon(ys) == True{} : Bool}) -> {allcon(RF.insnc(m, ys)) == True{} : Bool}:
  match m:
    case Nil{}:
      h
    case Con{+a, +b}:
      allcon_ins(Con{a, b}, ys, {==}, h)

def allcon_tmons(p: List<&2, R.ZTerm>, +ys: List<&2, List<&2, Nat>>, h: {allcon(ys) == True{} : Bool}) -> {allcon(RF.tmons(p, ys)) == True{} : Bool}:
  match p:
    case Nil{}:
      h
    case Con{R.ZTerm{c, +mm}, t}:
      allcon_tmons(t, RF.insnc(mm, ys), allcon_insnc(mm, ys, h))

def allcon_ymons(rs: List<&2, EL.Res>, +ys: List<&2, List<&2, Nat>>, h: {allcon(ys) == True{} : Bool}) -> {allcon(RF.ymons(rs, ys)) == True{} : Bool}:
  match rs:
    case Nil{}:
      h
    case Con{+r, t}:
      allcon_ymons(t, RF.tmons(RF.Res.p(r), ys), allcon_tmons(RF.Res.p(r), ys, h))

def cst_con(~F: O.OField, +c: O.C(F), m: List<&2, Nat>, +k: S.Q, +x: O.C(F), hm: {notnil(m) == True{} : Bool}) -> {O.add(F, O.mul(F, c, O.ofq(~F, CF.coef(E.QCst{k}, m))), x) == x : O.C(F)}:
  match m:
    case Nil{}:
      absurd({O.add(F, O.mul(F, c, O.ofq(~F, CF.coef(E.QCst{k}, Nil{}))), x) == x : O.C(F)}, KA.ft(hm))
    case Con{+v, +vs}:
      %Equal.sym(O.C(F), O.ofq(~F, CF.coef(E.QCst{k}, Con{v, vs})), O.zero(F),
          Equal.trans(O.C(F), O.ofq(~F, CF.coef(E.QCst{k}, Con{v, vs})), O.ofq(~F, SV.qzero()), O.zero(F), QE.ofq_eq(~F, CF.coef(E.QCst{k}, Con{v, vs}), SV.qzero(), CF.coef_cst_other(k, v, vs)), QE.ofq_zero(~F)))
        : {O.add(F, O.mul(F, c, _), x) == x : O.C(F)}
      FR.fring_eq(~F, [c, x], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZVar{1n}}, E.ZVar{1n}, {==})

# psi of a constant: only the monomial 1 counts
def psi_cst0(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +k: S.Q, h: {allcon(ms) == True{} : Bool}) -> {IP.psi(~F, ms, cs, E.QCst{k}) == O.zero(F) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{c, ct}:
      {==}
    case Con{m, mt} Nil{}:
      {==}
    case Con{+m, +mt} Con{+c, +ct}:
      +h2 = h
      %Equal.sym(O.C(F), IP.psi(~F, mt, ct, E.QCst{k}), O.zero(F), psi_cst0(~F, mt, ct, k, KA.band_r(notnil(m), allcon(mt), h2)))
        : {O.add(F, O.mul(F, c, O.ofq(~F, CF.coef(E.QCst{k}, m))), _) == O.zero(F) : O.C(F)}
      cst_con(~F, c, m, k, O.zero(F), KA.band_l(notnil(m), allcon(mt), h2))

def psi_cst_b(~F: O.OField, rows: List<&2, EL.Row>, +ms0: List<&2, List<&2, Nat>>, +cs0: List<&2, O.C(F)>, +k: S.Q, h: {pvcon(rows) == True{} : Bool})
  -> {IP.psi(~F, bms(rows, ms0), bcs(~F, rows, ms0, cs0), E.QCst{k}) == IP.psi(~F, ms0, cs0, E.QCst{k}) : O.C(F)}:
  match rows:
    case Nil{}:
      {==}
    case Con{+row, +t}:
      +h2 = h
      %Equal.sym(O.C(F), IP.psi(~F, bms(t, ms0), bcs(~F, t, ms0, cs0), E.QCst{k}), IP.psi(~F, ms0, cs0, E.QCst{k}), psi_cst_b(~F, t, ms0, cs0, k, KA.band_r(notnil(EP.rowpv(row)), pvcon(t), h2)))
        : {O.add(F, O.mul(F, O.mul(F, O.neg(F, IP.phi(~F, bms(t, ms0), bcs(~F, t, ms0, cs0), EP.rowp(row))), O.inv(F, O.ofz(~F, EL.cz(EP.rowpv(row), EP.rowp(row))))), O.ofq(~F, CF.coef(E.QCst{k}, EP.rowpv(row)))), _) == IP.psi(~F, ms0, cs0, E.QCst{k}) : O.C(F)}
      cst_con(~F, O.mul(F, O.neg(F, IP.phi(~F, bms(t, ms0), bcs(~F, t, ms0, cs0), EP.rowp(row))), O.inv(F, O.ofz(~F, EL.cz(EP.rowpv(row), EP.rowp(row))))), EP.rowpv(row), k, IP.psi(~F, ms0, cs0, E.QCst{k}),
        KA.band_l(notnil(EP.rowpv(row)), pvcon(t), h2))

# at the point: psi(k) is w k, w the weight at 1
def psi_cst(~F: O.OField, +rows: List<&2, EL.Row>, +ys: List<&2, List<&2, Nat>>, +w: O.C(F), +Y: List<&2, O.C(F)>, +k: S.Q, hr: {pvcon(rows) == True{} : Bool}, hy: {allcon(ys) == True{} : Bool})
  -> {IP.psi(~F, bms(rows, Con{Nil{}, ys}), bcs(~F, rows, Con{Nil{}, ys}, Con{w, Y}), E.QCst{k}) == O.mul(F, w, O.ofq(~F, k)) : O.C(F)}:
  %Equal.sym(O.C(F), IP.psi(~F, bms(rows, Con{Nil{}, ys}), bcs(~F, rows, Con{Nil{}, ys}, Con{w, Y}), E.QCst{k}), IP.psi(~F, Con{Nil{}, ys}, Con{w, Y}, E.QCst{k}), psi_cst_b(~F, rows, Con{Nil{}, ys}, Con{w, Y}, k, hr)) : {_ == O.mul(F, w, O.ofq(~F, k)) : O.C(F)}
  %Equal.sym(O.C(F), IP.psi(~F, ys, Y, E.QCst{k}), O.zero(F), psi_cst0(~F, ys, Y, k, hy)) : {O.add(F, O.mul(F, w, O.ofq(~F, CF.coef(E.QCst{k}, Nil{}))), _) == O.mul(F, w, O.ofq(~F, k)) : O.C(F)}
  %CF.coef_cst_one(k) : {O.add(F, O.mul(F, w, O.ofq(~F, _)), O.zero(F)) == O.mul(F, w, O.ofq(~F, k)) : O.C(F)}
  Equal.sym(O.C(F), O.mul(F, w, O.ofq(~F, k)), O.add(F, O.mul(F, w, O.ofq(~F, k)), O.zero(F)), FL.add_zero(~F, O.mul(F, w, O.ofq(~F, k))))

# psi through an identity
# -----------------------

def psi_qz(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +e1: E.QExpr, +e2: E.QExpr, +hz: {QN.qzero(E.QSub{e1, e2}) == True{} : Bool})
  -> {IP.psi(~F, ms, cs, e1) == IP.psi(~F, ms, cs, e2) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{c, ct}:
      {==}
    case Con{m, mt} Nil{}:
      {==}
    case Con{+m, +mt} Con{+c, +ct}:
      %QE.ofq_eq(~F, CF.coef(e1, m), CF.coef(e2, m), IP.coefeq(e1, e2, hz, m)) : {O.add(F, O.mul(F, c, O.ofq(~F, CF.coef(e1, m))), IP.psi(~F, mt, ct, e1)) == O.add(F, O.mul(F, c, _), IP.psi(~F, mt, ct, e2)) : O.C(F)}
      %psi_qz(~F, mt, ct, e1, e2, hz) : {O.add(F, O.mul(F, c, O.ofq(~F, CF.coef(e1, m))), IP.psi(~F, mt, ct, e1)) == O.add(F, O.mul(F, c, O.ofq(~F, CF.coef(e1, m))), _) : O.C(F)}
      {==}

def psi_add(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +a: E.QExpr, +b: E.QExpr)
  -> {IP.psi(~F, ms, cs, E.QAdd{a, b}) == O.add(F, IP.psi(~F, ms, cs, a), IP.psi(~F, ms, cs, b)) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      Equal.sym(O.C(F), O.add(F, O.zero(F), O.zero(F)), O.zero(F), IP.zz(~F))
    case Nil{} Con{c, ct}:
      Equal.sym(O.C(F), O.add(F, O.zero(F), O.zero(F)), O.zero(F), IP.zz(~F))
    case Con{m, mt} Nil{}:
      Equal.sym(O.C(F), O.add(F, O.zero(F), O.zero(F)), O.zero(F), IP.zz(~F))
    case Con{+m, +mt} Con{+c, +ct}:
      %CF.coef_add(a, b, m) : {O.add(F, O.mul(F, c, O.ofq(~F, _)), IP.psi(~F, mt, ct, E.QAdd{a, b})) == O.add(F, IP.psi(~F, Con{m, mt}, Con{c, ct}, a), IP.psi(~F, Con{m, mt}, Con{c, ct}, b)) : O.C(F)}
      %Equal.sym(O.C(F), O.ofq(~F, S.Q.add(CF.coef(a, m), CF.coef(b, m))), O.add(F, O.ofq(~F, CF.coef(a, m)), O.ofq(~F, CF.coef(b, m))), QE.ofq_add(~F, CF.coef(a, m), CF.coef(b, m)))
        : {O.add(F, O.mul(F, c, _), IP.psi(~F, mt, ct, E.QAdd{a, b})) == O.add(F, IP.psi(~F, Con{m, mt}, Con{c, ct}, a), IP.psi(~F, Con{m, mt}, Con{c, ct}, b)) : O.C(F)}
      %Equal.sym(O.C(F), IP.psi(~F, mt, ct, E.QAdd{a, b}), O.add(F, IP.psi(~F, mt, ct, a), IP.psi(~F, mt, ct, b)), psi_add(~F, mt, ct, a, b))
        : {O.add(F, O.mul(F, c, O.add(F, O.ofq(~F, CF.coef(a, m)), O.ofq(~F, CF.coef(b, m)))), _) == O.add(F, IP.psi(~F, Con{m, mt}, Con{c, ct}, a), IP.psi(~F, Con{m, mt}, Con{c, ct}, b)) : O.C(F)}
      FR.fring_eq(~F, [c, O.ofq(~F, CF.coef(a, m)), O.ofq(~F, CF.coef(b, m)), IP.psi(~F, mt, ct, a), IP.psi(~F, mt, ct, b)], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}, E.ZAdd{E.ZVar{3n}, E.ZVar{4n}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{3n}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{4n}}}, {==})

def psi_lin(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +ls: List<&2, S.Q>, +es: List<&2, E.QExpr>)
  -> {IP.psi(~F, ms, cs, SV.lin(ls, es)) == IP.psum(~F, ms, cs, ls, es) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{c, ct}:
      {==}
    case Con{m, mt} Nil{}:
      {==}
    case Con{+m, +mt} Con{+c, +ct}:
      %CF.coef_lin(ls, es, m) : {O.add(F, O.mul(F, c, O.ofq(~F, _)), IP.psi(~F, mt, ct, SV.lin(ls, es))) == IP.psum(~F, Con{m, mt}, Con{c, ct}, ls, es) : O.C(F)}
      %Equal.sym(O.C(F), IP.psi(~F, mt, ct, SV.lin(ls, es)), IP.psum(~F, mt, ct, ls, es), psi_lin(~F, mt, ct, ls, es))
        : {O.add(F, O.mul(F, c, O.ofq(~F, CF.qlin(ls, es, m))), _) == IP.psum(~F, Con{m, mt}, Con{c, ct}, ls, es) : O.C(F)}
      {==}

def fpsi_allk(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, ls: List<&2, S.Q>, es: List<&2, E.QExpr>, h: AllK(~F, ms, cs, es)) -> {IP.fpsi(~F, ms, cs, ls, es) == O.zero(F) : O.C(F)}:
  match ls es:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{e, et}:
      {==}
    case Con{l, lt} Nil{}:
      {==}
    case Con{+l, +lt} Con{+e, +et}:
      (h1, h2) = h
      %Equal.sym(O.C(F), IP.psi(~F, ms, cs, e), O.zero(F), h1) : {O.add(F, O.mul(F, O.ofq(~F, l), _), IP.fpsi(~F, ms, cs, lt, et)) == O.zero(F) : O.C(F)}
      %Equal.sym(O.C(F), IP.fpsi(~F, ms, cs, lt, et), O.zero(F), fpsi_allk(~F, ms, cs, lt, et, h2)) : {O.add(F, O.mul(F, O.ofq(~F, l), O.zero(F)), _) == O.zero(F) : O.C(F)}
      FR.fring_eq(~F, [O.ofq(~F, l)], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})

# the sides' combination
def psumS(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +mm: List<&2, S.Q>, +ss: List<&2, SK.Side>) -> O.C(F):
  match ms cs:
    case Nil{} Nil{}:
      O.zero(F)
    case Nil{} Con{c, ct}:
      O.zero(F)
    case Con{m, mt} Nil{}:
      O.zero(F)
    case Con{m, mt} Con{c, ct}:
      O.add(F, O.mul(F, c, O.ofq(~F, RP2.qslin(mm, ss, m))), psumS(~F, mt, ct, mm, ss))

def psi_slin(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +mm: List<&2, S.Q>, +ss: List<&2, SK.Side>)
  -> {IP.psi(~F, ms, cs, SV.slin(mm, ss)) == psumS(~F, ms, cs, mm, ss) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{c, ct}:
      {==}
    case Con{m, mt} Nil{}:
      {==}
    case Con{+m, +mt} Con{+c, +ct}:
      %RP2.coef_slin(mm, ss, m) : {O.add(F, O.mul(F, c, O.ofq(~F, _)), IP.psi(~F, mt, ct, SV.slin(mm, ss))) == psumS(~F, Con{m, mt}, Con{c, ct}, mm, ss) : O.C(F)}
      %Equal.sym(O.C(F), IP.psi(~F, mt, ct, SV.slin(mm, ss)), psumS(~F, mt, ct, mm, ss), psi_slin(~F, mt, ct, mm, ss))
        : {O.add(F, O.mul(F, c, O.ofq(~F, RP2.qslin(mm, ss, m))), _) == psumS(~F, Con{m, mt}, Con{c, ct}, mm, ss) : O.C(F)}
      {==}

def fpsiS(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, mm: List<&2, S.Q>, ss: List<&2, SK.Side>) -> O.C(F):
  match mm ss:
    case Nil{} ss:
      O.zero(F)
    case Con{l, lt} Nil{}:
      O.zero(F)
    case Con{l, lt} Con{s, st}:
      O.add(F, O.mul(F, O.ofq(~F, l), IP.psi(~F, ms, cs, SV.sexpr(s))), fpsiS(~F, ms, cs, lt, st))

def psumS_n(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +ss: List<&2, SK.Side>) -> {psumS(~F, ms, cs, Nil{}, ss) == O.zero(F) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{c, ct}:
      {==}
    case Con{m, mt} Nil{}:
      {==}
    case Con{+m, +mt} Con{+c, +ct}:
      %Equal.sym(O.C(F), psumS(~F, mt, ct, Nil{}, ss), O.zero(F), psumS_n(~F, mt, ct, ss)) : {O.add(F, O.mul(F, c, O.ofq(~F, S.Q{S.Z0{}, S.XH{}})), _) == O.zero(F) : O.C(F)}
      FR.fring_eq(~F, [c, O.inv(F, O.one(F))], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{1n}}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})

def psumS_cn(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +l: S.Q, +lt: List<&2, S.Q>) -> {psumS(~F, ms, cs, Con{l, lt}, Nil{}) == O.zero(F) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{c, ct}:
      {==}
    case Con{m, mt} Nil{}:
      {==}
    case Con{+m, +mt} Con{+c, +ct}:
      %Equal.sym(O.C(F), psumS(~F, mt, ct, Con{l, lt}, Nil{}), O.zero(F), psumS_cn(~F, mt, ct, l, lt)) : {O.add(F, O.mul(F, c, O.ofq(~F, S.Q{S.Z0{}, S.XH{}})), _) == O.zero(F) : O.C(F)}
      FR.fring_eq(~F, [c, O.inv(F, O.one(F))], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{1n}}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})

def psiS_split(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +l: S.Q, +s: SK.Side, +lt: List<&2, S.Q>, +st: List<&2, SK.Side>)
  -> {O.add(F, O.mul(F, O.ofq(~F, l), IP.psi(~F, ms, cs, SV.sexpr(s))), psumS(~F, ms, cs, lt, st)) == psumS(~F, ms, cs, Con{l, lt}, Con{s, st}) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      FR.fring_eq(~F, [O.ofq(~F, l)], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})
    case Nil{} Con{c, ct}:
      FR.fring_eq(~F, [O.ofq(~F, l)], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})
    case Con{m, mt} Nil{}:
      FR.fring_eq(~F, [O.ofq(~F, l)], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})
    case Con{+m, +mt} Con{+c, +ct}:
      %Equal.sym(O.C(F), O.ofq(~F, S.Q.add(S.Q.mul(l, CF.coef(SV.sexpr(s), m)), RP2.qslin(lt, st, m))), O.add(F, O.ofq(~F, S.Q.mul(l, CF.coef(SV.sexpr(s), m))), O.ofq(~F, RP2.qslin(lt, st, m))),
          QE.ofq_add(~F, S.Q.mul(l, CF.coef(SV.sexpr(s), m)), RP2.qslin(lt, st, m)))
        : {O.add(F, O.mul(F, O.ofq(~F, l), IP.psi(~F, Con{m, mt}, Con{c, ct}, SV.sexpr(s))), psumS(~F, Con{m, mt}, Con{c, ct}, lt, st)) == O.add(F, O.mul(F, c, _), psumS(~F, mt, ct, Con{l, lt}, Con{s, st})) : O.C(F)}
      %Equal.sym(O.C(F), O.ofq(~F, S.Q.mul(l, CF.coef(SV.sexpr(s), m))), O.mul(F, O.ofq(~F, l), O.ofq(~F, CF.coef(SV.sexpr(s), m))), QE.ofq_mul(~F, l, CF.coef(SV.sexpr(s), m)))
        : {O.add(F, O.mul(F, O.ofq(~F, l), IP.psi(~F, Con{m, mt}, Con{c, ct}, SV.sexpr(s))), psumS(~F, Con{m, mt}, Con{c, ct}, lt, st)) == O.add(F, O.mul(F, c, O.add(F, _, O.ofq(~F, RP2.qslin(lt, st, m)))), psumS(~F, mt, ct, Con{l, lt}, Con{s, st})) : O.C(F)}
      %psiS_split(~F, mt, ct, l, s, lt, st)
        : {O.add(F, O.mul(F, O.ofq(~F, l), IP.psi(~F, Con{m, mt}, Con{c, ct}, SV.sexpr(s))), psumS(~F, Con{m, mt}, Con{c, ct}, lt, st)) == O.add(F, O.mul(F, c, O.add(F, O.mul(F, O.ofq(~F, l), O.ofq(~F, CF.coef(SV.sexpr(s), m))), O.ofq(~F, RP2.qslin(lt, st, m)))), _) : O.C(F)}
      FR.fring_eq(~F, [c, O.ofq(~F, l), O.ofq(~F, CF.coef(SV.sexpr(s), m)), O.ofq(~F, RP2.qslin(lt, st, m)), IP.psi(~F, mt, ct, SV.sexpr(s)), psumS(~F, mt, ct, lt, st)], E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{4n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZVar{5n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{3n}}}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{4n}}, E.ZVar{5n}}}, {==})

def psumS_fpsiS(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, mm: List<&2, S.Q>, ss: List<&2, SK.Side>) -> {psumS(~F, ms, cs, mm, ss) == fpsiS(~F, ms, cs, mm, ss) : O.C(F)}:
  match mm ss:
    case Nil{} +ss:
      psumS_n(~F, ms, cs, ss)
    case Con{+l, +lt} Nil{}:
      psumS_cn(~F, ms, cs, l, lt)
    case Con{+l, +lt} Con{+s, +st}:
      %psiS_split(~F, ms, cs, l, s, lt, st) : {_ == fpsiS(~F, ms, cs, Con{l, lt}, Con{s, st}) : O.C(F)}
      %Equal.sym(O.C(F), psumS(~F, ms, cs, lt, st), fpsiS(~F, ms, cs, lt, st), psumS_fpsiS(~F, ms, cs, lt, st))
        : {O.add(F, O.mul(F, O.ofq(~F, l), IP.psi(~F, ms, cs, SV.sexpr(s))), _) == fpsiS(~F, ms, cs, Con{l, lt}, Con{s, st}) : O.C(F)}
      {==}

# psi of a refutation's left side: the sides' part only
def ref_val(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +ls: List<&2, S.Q>, +mm: List<&2, S.Q>, +k: S.Q,
  +hz: {QN.qzero(E.QSub{E.QAdd{SV.lin(ls, es), SV.slin(mm, ss)}, E.QCst{k}}) == True{} : Bool}, hk: AllK(~F, ms, cs, es))
  -> {fpsiS(~F, ms, cs, mm, ss) == IP.psi(~F, ms, cs, E.QCst{k}) : O.C(F)}:
  Equal.trans(O.C(F), fpsiS(~F, ms, cs, mm, ss), IP.psi(~F, ms, cs, E.QAdd{SV.lin(ls, es), SV.slin(mm, ss)}), IP.psi(~F, ms, cs, E.QCst{k}),
    (%Equal.sym(O.C(F), IP.psi(~F, ms, cs, E.QAdd{SV.lin(ls, es), SV.slin(mm, ss)}), O.add(F, IP.psi(~F, ms, cs, SV.lin(ls, es)), IP.psi(~F, ms, cs, SV.slin(mm, ss))), psi_add(~F, ms, cs, SV.lin(ls, es), SV.slin(mm, ss))) : {fpsiS(~F, ms, cs, mm, ss) == _ : O.C(F)}
     %Equal.sym(O.C(F), IP.psi(~F, ms, cs, SV.lin(ls, es)), IP.psum(~F, ms, cs, ls, es), psi_lin(~F, ms, cs, ls, es)) : {fpsiS(~F, ms, cs, mm, ss) == O.add(F, _, IP.psi(~F, ms, cs, SV.slin(mm, ss))) : O.C(F)}
     %Equal.sym(O.C(F), IP.psum(~F, ms, cs, ls, es), IP.fpsi(~F, ms, cs, ls, es), IP.psum_fpsi(~F, ms, cs, ls, es)) : {fpsiS(~F, ms, cs, mm, ss) == O.add(F, _, IP.psi(~F, ms, cs, SV.slin(mm, ss))) : O.C(F)}
     %Equal.sym(O.C(F), IP.fpsi(~F, ms, cs, ls, es), O.zero(F), fpsi_allk(~F, ms, cs, ls, es, hk)) : {fpsiS(~F, ms, cs, mm, ss) == O.add(F, _, IP.psi(~F, ms, cs, SV.slin(mm, ss))) : O.C(F)}
     %Equal.sym(O.C(F), IP.psi(~F, ms, cs, SV.slin(mm, ss)), psumS(~F, ms, cs, mm, ss), psi_slin(~F, ms, cs, mm, ss)) : {fpsiS(~F, ms, cs, mm, ss) == O.add(F, O.zero(F), _) : O.C(F)}
     %Equal.sym(O.C(F), psumS(~F, ms, cs, mm, ss), fpsiS(~F, ms, cs, mm, ss), psumS_fpsiS(~F, ms, cs, mm, ss)) : {fpsiS(~F, ms, cs, mm, ss) == O.add(F, O.zero(F), _) : O.C(F)}
     Equal.sym(O.C(F), O.add(F, O.zero(F), fpsiS(~F, ms, cs, mm, ss)), fpsiS(~F, ms, cs, mm, ss), FL.zero_add(~F, fpsiS(~F, ms, cs, mm, ss)))),
    psi_qz(~F, ms, cs, E.QAdd{SV.lin(ls, es), SV.slin(mm, ss)}, E.QCst{k}, hz))

# Lexicographic sums of nonnegative multiples
# -------------------------------------------

def ge0_of_eq(~F: O.OField, +x: O.C(F), e: {x == O.zero(F) : O.C(F)}) -> O.le(~F, O.zero(F), x):
  Inr{Equal.sym(O.C(F), x, O.zero(F), e)}

def pos_add(~F: O.OField, +x: O.C(F), +y: O.C(F), hx: O.lt(F, O.zero(F), x), hy: O.le(~F, O.zero(F), y)) -> O.lt(F, O.zero(F), O.add(F, x, y)):
  match hy:
    case Inl{l}:
      O.lt_trans(F)(O.zero(F), O.add(F, O.zero(F), y), O.add(F, x, y))((%Equal.sym(O.C(F), O.add(F, O.zero(F), y), y, FL.zero_add(~F, y)) : O.lt(F, O.zero(F), _)
        l))(O.lt_add(F)(O.zero(F), x, y)(hx))
    case Inr{e}:
      %e : O.lt(F, O.zero(F), O.add(F, x, _))
      %FL.add_zero(~F, x) : O.lt(F, O.zero(F), _)
      hx

def pos_add_r(~F: O.OField, +x: O.C(F), +y: O.C(F), hx: O.le(~F, O.zero(F), x), hy: O.lt(F, O.zero(F), y)) -> O.lt(F, O.zero(F), O.add(F, x, y)):
  %O.add_comm(F)(y, x) : O.lt(F, O.zero(F), _)
  pos_add(~F, y, x, hy, hx)

def nn_add(~F: O.OField, +x: O.C(F), +y: O.C(F), hx: O.le(~F, O.zero(F), x), hy: O.le(~F, O.zero(F), y)) -> O.le(~F, O.zero(F), O.add(F, x, y)):
  match hx:
    case Inl{l}:
      Inl{pos_add(~F, x, y, l, hy)}
    case Inr{e}:
      %e : O.le(~F, O.zero(F), O.add(F, _, y))
      %Equal.sym(O.C(F), O.add(F, O.zero(F), y), y, FL.zero_add(~F, y)) : O.le(~F, O.zero(F), _)
      hy

def lnn_add(~F: O.OField, +x0: O.C(F), +x1: O.C(F), +y0: O.C(F), +y1: O.C(F), hx: LX.LNonneg(~F, x0, x1), hy: LX.LNonneg(~F, y0, y1)) -> LX.LNonneg(~F, O.add(F, x0, y0), O.add(F, x1, y1)):
  match hx hy:
    case Inl{+u} Inl{+v}:
      Inl{pos_add(~F, x0, y0, u, FO.lt_le(~F, O.zero(F), y0, v))}
    case Inl{+u} Inr{+v}:
      Inl{pos_add(~F, x0, y0, u, ge0_of_eq(~F, y0, LX.both_l({y0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), y1), v)))}
    case Inr{+u} Inl{+v}:
      Inl{pos_add_r(~F, x0, y0, ge0_of_eq(~F, x0, LX.both_l({x0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), x1), u)), v)}
    case Inr{+u} Inr{+v}:
      Inr{(LX.zero_eq(~F, x0, y0, LX.both_l({x0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), x1), u), LX.both_l({y0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), y1), v)),
           nn_add(~F, x1, y1, LX.both_r({x0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), x1), u), LX.both_r({y0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), y1), v)))}

def lpos_add_l(~F: O.OField, +x0: O.C(F), +x1: O.C(F), +y0: O.C(F), +y1: O.C(F), hx: LX.LPos(~F, x0, x1), hy: LX.LNonneg(~F, y0, y1)) -> LX.LPos(~F, O.add(F, x0, y0), O.add(F, x1, y1)):
  match hx hy:
    case Inl{+u} Inl{+v}:
      Inl{pos_add(~F, x0, y0, u, FO.lt_le(~F, O.zero(F), y0, v))}
    case Inl{+u} Inr{+v}:
      Inl{pos_add(~F, x0, y0, u, ge0_of_eq(~F, y0, LX.both_l({y0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), y1), v)))}
    case Inr{+u} Inl{+v}:
      Inl{pos_add_r(~F, x0, y0, ge0_of_eq(~F, x0, LX.both_l({x0 == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), x1), u)), v)}
    case Inr{+u} Inr{+v}:
      Inr{(LX.zero_eq(~F, x0, y0, LX.both_l({x0 == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), x1), u), LX.both_l({y0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), y1), v)),
           pos_add(~F, x1, y1, LX.both_r({x0 == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), x1), u), LX.both_r({y0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), y1), v)))}

def lpos_add_r(~F: O.OField, +x0: O.C(F), +x1: O.C(F), +y0: O.C(F), +y1: O.C(F), hx: LX.LNonneg(~F, x0, x1), hy: LX.LPos(~F, y0, y1)) -> LX.LPos(~F, O.add(F, x0, y0), O.add(F, x1, y1)):
  match hx hy:
    case Inl{+u} Inl{+v}:
      Inl{pos_add(~F, x0, y0, u, FO.lt_le(~F, O.zero(F), y0, v))}
    case Inl{+u} Inr{+v}:
      Inl{pos_add(~F, x0, y0, u, ge0_of_eq(~F, y0, LX.both_l({y0 == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), y1), v)))}
    case Inr{+u} Inl{+v}:
      Inl{pos_add_r(~F, x0, y0, ge0_of_eq(~F, x0, LX.both_l({x0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), x1), u)), v)}
    case Inr{+u} Inr{+v}:
      Inr{(LX.zero_eq(~F, x0, y0, LX.both_l({x0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), x1), u), LX.both_l({y0 == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), y1), v)),
           pos_add_r(~F, x1, y1, LX.both_r({x0 == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), x1), u), LX.both_r({y0 == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), y1), v)))}

def lnn_scale0(~F: O.OField, +c: O.C(F), +x0: O.C(F), +x1: O.C(F), hc: O.le(~F, O.zero(F), c), hx: LX.LNonneg(~F, x0, x1)) -> LX.LNonneg(~F, O.mul(F, c, x0), O.mul(F, c, x1)):
  match hc:
    case Inl{l}:
      lnn_scale(~F, c, x0, x1, l, hx)
    case Inr{e}:
      %e : LX.LNonneg(~F, O.mul(F, _, x0), O.mul(F, _, x1))
      Inr{(FL.zero_mul(~F, x0), Inr{Equal.sym(O.C(F), O.mul(F, O.zero(F), x1), O.zero(F), FL.zero_mul(~F, x1))})}

def lpos_weak(~F: O.OField, +x0: O.C(F), +x1: O.C(F), h: LX.LPos(~F, x0, x1)) -> LX.LNonneg(~F, x0, x1):
  match h:
    case Inl{a}:
      Inl{a}
    case Inr{+p}:
      Inr{(LX.both_l({x0 == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), x1), p), FO.lt_le(~F, O.zero(F), x1, LX.both_r({x0 == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), x1), p)))}

def sideok_nn(~F: O.OField, +x0: O.C(F), +x1: O.C(F), s: SK.Side, h: SideOK(~F, x0, x1, s)) -> LX.LNonneg(~F, x0, x1):
  match s:
    case SK.Gt0{e}:
      lpos_weak(~F, x0, x1, h)
    case SK.Ge0{e}:
      h

# The multipliers in the field
# ----------------------------

def ofq_num0(~F: O.OField, k: S.Q, h: {S.Q.num(k) == S.Z0{} : S.Z}) -> {O.ofq(~F, k) == O.zero(F) : O.C(F)}:
  match k:
    case S.Q{n, +d}:
      %Equal.sym(S.Z, n, S.Z0{}, h) : {O.mul(F, O.ofz(~F, _), O.inv(F, O.ofp(~F, d))) == O.zero(F) : O.C(F)}
      FL.zero_mul(~F, O.inv(F, O.ofp(~F, d)))

def num_one(+a: S.Z, h: {S.Z.mul(a, S.Zpos{S.XH{}}) == S.Z0{} : S.Z}) -> {a == S.Z0{} : S.Z}:
  Equal.trans(S.Z, a, S.Z.mul(a, S.Zpos{S.XH{}}), S.Z0{}, ZL.mul_one(a), h)

def q_nn.go(~F: O.OField, o: Cmp, +m: S.Q, ho: {S.Z.cmp(S.Z.mul(S.Q.num(m), S.Zpos{S.XH{}}), S.Z0{}) == o : Cmp}, h: {SV.bnot(SV.islt(o)) == True{} : Bool}) -> O.le(~F, O.zero(F), O.ofq(~F, m)):
  match o:
    case LT{}:
      absurd(O.le(~F, O.zero(F), O.ofq(~F, m)), KA.ft(h))
    case EQ{}:
      ge0_of_eq(~F, O.ofq(~F, m), ofq_num0(~F, m, num_one(S.Q.num(m), ZO.sub_eq(S.Z.mul(S.Q.num(m), S.Zpos{S.XH{}}), S.Z0{}, ZO.eq_zero(S.Z.mul(S.Q.num(m), S.Zpos{S.XH{}}), S.Z0{}, ho)))))
    case GT{}:
      Inl{O.lt_mul(F)(O.ofz(~F, S.Q.num(m)), O.inv(F, O.ofp(~F, S.Q.den(m))))((%Equal.sym(S.Z, S.Q.num(m), S.Z.mul(S.Q.num(m), S.Zpos{S.XH{}}), ZL.mul_one(S.Q.num(m))) : O.lt(F, O.zero(F), O.ofz(~F, _))
          LX.zgt_f(~F, S.Z.mul(S.Q.num(m), S.Zpos{S.XH{}}), S.Z0{}, ho)))(RN.inv_pos(~F, S.Q.den(m)))}

# m >= 0: ofq(m) >= 0
def q_nn(~F: O.OField, +m: S.Q, h: {SV.bnot(SV.islt(S.Q.cmp(m, SV.qzero()))) == True{} : Bool}) -> O.le(~F, O.zero(F), O.ofq(~F, m)):
  q_nn.go(~F, S.Q.cmp(m, SV.qzero()), m, {==}, h)

def sv_lt(o: Cmp, h: {SV.islt(o) == True{} : Bool}) -> {o == LT{} : Cmp}:
  match o:
    case LT{}:
      {==}
    case EQ{}:
      absurd({EQ{} == LT{} : Cmp}, KA.ft(h))
    case GT{}:
      absurd({GT{} == LT{} : Cmp}, KA.ft(h))

# m > 0: ofq(m) > 0
def q_pos(~F: O.OField, +m: S.Q, h: {SV.islt(S.Q.cmp(SV.qzero(), m)) == True{} : Bool}) -> O.lt(F, O.zero(F), O.ofq(~F, m)):
  (%QE.ofq_zero(~F) : O.lt(F, _, O.ofq(~F, m))
    QE.ofq_lt(~F, SV.qzero(), m, sv_lt(S.Q.cmp(SV.qzero(), m), h)))


# m >= 0 on every side: the sum is lexicographically >= 0
def lnn_sum(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +c0: List<&2, O.C(F)>, +c1: List<&2, O.C(F)>, mm: List<&2, S.Q>, ss: List<&2, SK.Side>, hs: AllS(~F, ms, c0, c1, ss), hn: {SV.nonneg(mm) == True{} : Bool})
  -> LX.LNonneg(~F, fpsiS(~F, ms, c0, mm, ss), fpsiS(~F, ms, c1, mm, ss)):
  match mm ss:
    case Nil{} ss:
      Inr{({==}, Inr{{==}})}
    case Con{l, lt} Nil{}:
      Inr{({==}, Inr{{==}})}
    case Con{+l, +lt} Con{+s, +st}:
      (hs1, hs2) = hs
      +hn2 = hn
      lnn_add(~F, O.mul(F, O.ofq(~F, l), IP.psi(~F, ms, c0, SV.sexpr(s))), O.mul(F, O.ofq(~F, l), IP.psi(~F, ms, c1, SV.sexpr(s))), fpsiS(~F, ms, c0, lt, st), fpsiS(~F, ms, c1, lt, st),
        lnn_scale0(~F, O.ofq(~F, l), IP.psi(~F, ms, c0, SV.sexpr(s)), IP.psi(~F, ms, c1, SV.sexpr(s)), q_nn(~F, l, LI.band_l(SV.bnot(SV.islt(S.Q.cmp(l, SV.qzero()))), SV.nonneg(lt), hn2)), sideok_nn(~F, IP.psi(~F, ms, c0, SV.sexpr(s)), IP.psi(~F, ms, c1, SV.sexpr(s)), s, hs1)),
        lnn_sum(~F, ms, c0, c1, lt, st, hs2, LI.band_r(SV.bnot(SV.islt(S.Q.cmp(l, SV.qzero()))), SV.nonneg(lt), hn2)))


def lps.g(~F: O.OField, b: Bool, +ms: List<&2, List<&2, Nat>>, +c0: List<&2, O.C(F)>, +c1: List<&2, O.C(F)>, +l: S.Q, +lt: List<&2, S.Q>, +e: E.QExpr, +st: List<&2, SK.Side>,
  hb: {b == SV.islt(S.Q.cmp(SV.qzero(), l)) : Bool}, hs1: LX.LPos(~F, IP.psi(~F, ms, c0, e), IP.psi(~F, ms, c1, e)), +hs2: AllS(~F, ms, c0, c1, st), +hn: {SV.nonneg(Con{l, lt}) == True{} : Bool},
  hp: {SV.bor(b, SV.strict_pos(lt, st)) == True{} : Bool}, ih: {SV.strict_pos(lt, st) == True{} : Bool} -> LX.LPos(~F, fpsiS(~F, ms, c0, lt, st), fpsiS(~F, ms, c1, lt, st)))
  -> LX.LPos(~F, fpsiS(~F, ms, c0, Con{l, lt}, Con{SK.Gt0{e}, st}), fpsiS(~F, ms, c1, Con{l, lt}, Con{SK.Gt0{e}, st})):
  match b:
    case True{}:
      lpos_add_l(~F, O.mul(F, O.ofq(~F, l), IP.psi(~F, ms, c0, e)), O.mul(F, O.ofq(~F, l), IP.psi(~F, ms, c1, e)), fpsiS(~F, ms, c0, lt, st), fpsiS(~F, ms, c1, lt, st),
        lpos_scale(~F, O.ofq(~F, l), IP.psi(~F, ms, c0, e), IP.psi(~F, ms, c1, e), q_pos(~F, l, Equal.sym(Bool, True{}, SV.islt(S.Q.cmp(SV.qzero(), l)), hb)), hs1),
        lnn_sum(~F, ms, c0, c1, lt, st, hs2, LI.band_r(SV.bnot(SV.islt(S.Q.cmp(l, SV.qzero()))), SV.nonneg(lt), hn)))
    case False{}:
      lpos_add_r(~F, O.mul(F, O.ofq(~F, l), IP.psi(~F, ms, c0, e)), O.mul(F, O.ofq(~F, l), IP.psi(~F, ms, c1, e)), fpsiS(~F, ms, c0, lt, st), fpsiS(~F, ms, c1, lt, st),
        lnn_scale0(~F, O.ofq(~F, l), IP.psi(~F, ms, c0, e), IP.psi(~F, ms, c1, e), q_nn(~F, l, LI.band_l(SV.bnot(SV.islt(S.Q.cmp(l, SV.qzero()))), SV.nonneg(lt), hn)), lpos_weak(~F, IP.psi(~F, ms, c0, e), IP.psi(~F, ms, c1, e), hs1)),
        ih(hp))

def lps.c(~F: O.OField, s: SK.Side, +ms: List<&2, List<&2, Nat>>, +c0: List<&2, O.C(F)>, +c1: List<&2, O.C(F)>, +l: S.Q, +lt: List<&2, S.Q>, +st: List<&2, SK.Side>,
  hs1: SideOK(~F, IP.psi(~F, ms, c0, SV.sexpr(s)), IP.psi(~F, ms, c1, SV.sexpr(s)), s), +hs2: AllS(~F, ms, c0, c1, st), +hn: {SV.nonneg(Con{l, lt}) == True{} : Bool}, hp: {SV.strict_pos(Con{l, lt}, Con{s, st}) == True{} : Bool}, ih: {SV.strict_pos(lt, st) == True{} : Bool} -> LX.LPos(~F, fpsiS(~F, ms, c0, lt, st), fpsiS(~F, ms, c1, lt, st)))
  -> LX.LPos(~F, fpsiS(~F, ms, c0, Con{l, lt}, Con{s, st}), fpsiS(~F, ms, c1, Con{l, lt}, Con{s, st})):
  match s:
    case SK.Gt0{+e}:
      lps.g(~F, SV.islt(S.Q.cmp(SV.qzero(), l)), ms, c0, c1, l, lt, e, st, {==}, hs1, hs2, hn, hp, ih)
    case SK.Ge0{+e}:
      lpos_add_r(~F, O.mul(F, O.ofq(~F, l), IP.psi(~F, ms, c0, e)), O.mul(F, O.ofq(~F, l), IP.psi(~F, ms, c1, e)), fpsiS(~F, ms, c0, lt, st), fpsiS(~F, ms, c1, lt, st),
        lnn_scale0(~F, O.ofq(~F, l), IP.psi(~F, ms, c0, e), IP.psi(~F, ms, c1, e), q_nn(~F, l, LI.band_l(SV.bnot(SV.islt(S.Q.cmp(l, SV.qzero()))), SV.nonneg(lt), hn)), hs1),
        ih(hp))

# and > 0 when a strict side is weighted positively
def lpos_sum(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +c0: List<&2, O.C(F)>, +c1: List<&2, O.C(F)>, mm: List<&2, S.Q>, ss: List<&2, SK.Side>, hs: AllS(~F, ms, c0, c1, ss), +hn: {SV.nonneg(mm) == True{} : Bool},
  hp: {SV.strict_pos(mm, ss) == True{} : Bool}) -> LX.LPos(~F, fpsiS(~F, ms, c0, mm, ss), fpsiS(~F, ms, c1, mm, ss)):
  match mm ss:
    case Nil{} ss:
      absurd(LX.LPos(~F, O.zero(F), O.zero(F)), KA.ft(hp))
    case Con{l, lt} Nil{}:
      absurd(LX.LPos(~F, O.zero(F), O.zero(F)), KA.ft(hp))
    case Con{+l, +lt} Con{+s, +st}:
      (hs1, hs2) = hs
      +hs3 = hs2
      lps.c(~F, s, ms, c0, c1, l, lt, st, hs1, hs3, hn, hp, a => lpos_sum(~F, ms, c0, c1, lt, st, hs3, LI.band_r(SV.bnot(SV.islt(S.Q.cmp(l, SV.qzero()))), SV.nonneg(lt), hn), a))

# No refutation survives the point
# --------------------------------

def iszz_eq(z: S.Z, h: {SV.iszz(z) == True{} : Bool}) -> {z == S.Z0{} : S.Z}:
  match z:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      absurd({S.Zpos{p} == S.Z0{} : S.Z}, KA.ft(h))
    case S.Zneg{p}:
      absurd({S.Zneg{p} == S.Z0{} : S.Z}, KA.ft(h))

def pc.lt(~F: O.OField, +x: O.C(F), hl: O.lt(F, x, O.zero(F)), h: LX.LNonneg(~F, x, O.zero(F))) -> Empty:
  match h:
    case Inl{a}:
      LX.lt_irr0(~F, x, a, hl)
    case Inr{+p}:
      O.lt_irrefl(F)(O.zero(F))((%LX.both_l({x == O.zero(F) : O.C(F)}, O.le(~F, O.zero(F), O.zero(F)), p) : O.lt(F, _, O.zero(F))
        hl))

def pc.pos(~F: O.OField, +x: O.C(F), ez: {x == O.zero(F) : O.C(F)}, h: LX.LPos(~F, x, O.zero(F))) -> Empty:
  match h:
    case Inl{a}:
      O.lt_irrefl(F)(O.zero(F))((%ez : O.lt(F, O.zero(F), _)
        a))
    case Inr{+p}:
      O.lt_irrefl(F)(O.zero(F))(LX.both_r({x == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), O.zero(F)), p))


def pc.go(~F: O.OField, b: Bool, +ms: List<&2, List<&2, Nat>>, +c0: List<&2, O.C(F)>, +c1: List<&2, O.C(F)>, +ss: List<&2, SK.Side>, +mm: List<&2, S.Q>, +k: S.Q,
  hb: {b == SV.islt(S.Q.cmp(k, SV.qzero())) : Bool}, hbor: {SV.bor(b, SV.band(SV.iszz(S.Q.num(k)), SV.strict_pos(mm, ss))) == True{} : Bool}, +hs: AllS(~F, ms, c0, c1, ss), +hnn: {SV.nonneg(mm) == True{} : Bool},
  +v0: {fpsiS(~F, ms, c0, mm, ss) == O.ofq(~F, k) : O.C(F)}, +v1: {fpsiS(~F, ms, c1, mm, ss) == O.zero(F) : O.C(F)}) -> Empty:
  match b:
    case True{}:
      pc.lt(~F, O.ofq(~F, k), (%QE.ofq_zero(~F) : O.lt(F, O.ofq(~F, k), _)
          QE.ofq_lt(~F, k, SV.qzero(), sv_lt(S.Q.cmp(k, SV.qzero()), Equal.sym(Bool, True{}, SV.islt(S.Q.cmp(k, SV.qzero())), hb)))),
        (%v0 : LX.LNonneg(~F, _, O.zero(F))
         %v1 : LX.LNonneg(~F, fpsiS(~F, ms, c0, mm, ss), _)
         lnn_sum(~F, ms, c0, c1, mm, ss, hs, hnn)))
    case False{}:
      +hsp = hbor
      pc.pos(~F, O.ofq(~F, k), ofq_num0(~F, k, iszz_eq(S.Q.num(k), LI.band_l(SV.iszz(S.Q.num(k)), SV.strict_pos(mm, ss), hsp))),
        (%v0 : LX.LPos(~F, _, O.zero(F))
         %v1 : LX.LPos(~F, fpsiS(~F, ms, c0, mm, ss), _)
         lpos_sum(~F, ms, c0, c1, mm, ss, hs, hnn, LI.band_r(SV.iszz(S.Q.num(k)), SV.strict_pos(mm, ss), hsp))))

# a point killing every equation and holding every side refutes every
# refutation: read through both functionals, it would be (k, 0)
# lexicographically >= 0, and > 0 with a strict side weighted positively
def pt_contra(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +c0: List<&2, O.C(F)>, +c1: List<&2, O.C(F)>, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +ls: List<&2, S.Q>, +mm: List<&2, S.Q>, +k: S.Q,
  hk0: AllK(~F, ms, c0, es), hk1: AllK(~F, ms, c1, es), +hs: AllS(~F, ms, c0, c1, ss),
  hc0: {IP.psi(~F, ms, c0, E.QCst{k}) == O.ofq(~F, k) : O.C(F)}, hc1: {IP.psi(~F, ms, c1, E.QCst{k}) == O.zero(F) : O.C(F)}, hr: SV.Refutes0(es, ss, ls, mm, k)) -> Empty:
  (hro, hid) = hr
  +hz = ID.qzero_ident(E.QAdd{SV.lin(ls, es), SV.slin(mm, ss)}, E.QCst{k}, hid)
  +h3 = LI.band_r(SV.eq(SV.qlen(mm), SV.slen(ss)), SV.band(SV.nonneg(mm), SV.bor(SV.islt(S.Q.cmp(k, SV.qzero())), SV.band(SV.iszz(S.Q.num(k)), SV.strict_pos(mm, ss)))), LI.band_r(SV.eq(SV.qlen(ls), SV.neqs(es)), SV.band(SV.eq(SV.qlen(mm), SV.slen(ss)), SV.band(SV.nonneg(mm), SV.bor(SV.islt(S.Q.cmp(k, SV.qzero())), SV.band(SV.iszz(S.Q.num(k)), SV.strict_pos(mm, ss))))), hro))
  pc.go(~F, SV.islt(S.Q.cmp(k, SV.qzero())), ms, c0, c1, ss, mm, k, {==}, LI.band_r(SV.nonneg(mm), SV.bor(SV.islt(S.Q.cmp(k, SV.qzero())), SV.band(SV.iszz(S.Q.num(k)), SV.strict_pos(mm, ss))), h3), hs, LI.band_l(SV.nonneg(mm), SV.bor(SV.islt(S.Q.cmp(k, SV.qzero())), SV.band(SV.iszz(S.Q.num(k)), SV.strict_pos(mm, ss))), h3),
    Equal.trans(O.C(F), fpsiS(~F, ms, c0, mm, ss), IP.psi(~F, ms, c0, E.QCst{k}), O.ofq(~F, k), ref_val(~F, ms, c0, es, ss, ls, mm, k, hz, hk0), hc0),
    Equal.trans(O.C(F), fpsiS(~F, ms, c1, mm, ss), IP.psi(~F, ms, c1, E.QCst{k}), O.zero(F), ref_val(~F, ms, c1, es, ss, ls, mm, k, hz, hk1), hc1))

# The theorem
# -----------

# es and ss have no degree-0 refutation
def NoRef(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>) -> Type:
  @ls: List<&2, S.Q> -> @ms: List<&2, S.Q> -> @k: S.Q -> SV.Refutes0(es, ss, ls, ms, k) -> Empty

def sat_contra(~F: O.OField, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +t: SX.Tab, +h: {SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)) == SX.Sat{t} : SX.Run}, +hc: {RF.crow(RF.Walk.rows(RF.walk(es, Nil{})), 0n) == None{} : Maybe<&2, Nat>}, +ls: List<&2, S.Q>, +mm: List<&2, S.Q>, +k: S.Q, hr: SV.Refutes0(es, ss, ls, mm, k)) -> Empty:
  pt_contra(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), es, ss, ls, mm, k, kill_all(~F, Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}, es), kill_all(~F, Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}, es), allside(~F, es, ss, t, h, ss, 0n, {==}),
    Equal.trans(O.C(F), IP.psi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), E.QCst{k}), O.mul(F, O.one(F), O.ofq(~F, k)), O.ofq(~F, k),
      psi_cst(~F, RF.Walk.rows(RF.walk(es, Nil{})), RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss))))), k, crow_none(RF.Walk.rows(RF.walk(es, Nil{})), 0n, hc), allcon_ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}, {==})),
      FR.fring_eq(~F, [O.ofq(~F, k)], E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, E.ZVar{0n}, {==})),
    Equal.trans(O.C(F), IP.psi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), E.QCst{k}), O.mul(F, O.zero(F), O.ofq(~F, k)), O.zero(F),
      psi_cst(~F, RF.Walk.rows(RF.walk(es, Nil{})), RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss))))), k, crow_none(RF.Walk.rows(RF.walk(es, Nil{})), 0n, hc), allcon_ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}, {==})),
      FL.zero_mul(~F, O.ofq(~F, k))),
    hr)

# the simplex's Sat, with no constant row: no refutation
def sat_noref(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +t: SX.Tab, +h: {SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)) == SX.Sat{t} : SX.Run}, +hc: {RF.crow(RF.Walk.rows(RF.walk(es, Nil{})), 0n) == None{} : Maybe<&2, Nat>}) -> NoRef(es, ss):
  ls => mm => k => hr => sat_contra(~QF.qfield(), es, ss, t, h, hc, ls, mm, k, hr)

# refute decides degree-0 refutability: a certificate is a refutation, and
# none means there is none
def RefOk(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, mc: Maybe<&2, RF.Cert>) -> Type:
  match mc:
    case None{}:
      NoRef(es, ss)
    case Some{RF.Cert{ls, ms, k}}:
      SV.Refutes0(es, ss, ls, ms, k)

def ok.r(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, r: SX.Run, hr: {r == SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)) : SX.Run}, +hc: {RF.crow(RF.Walk.rows(RF.walk(es, Nil{})), 0n) == None{} : Maybe<&2, Nat>})
  -> RefOk(es, ss, RF.cert.run(RF.Walk.keep(RF.walk(es, Nil{})), es, ss, RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), r)):
  match r:
    case SX.Go{+t}:
      absurd(RefOk(es, ss, None{}), KA.tf((%Equal.sym(SX.Run, SX.Go{t}, SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), hr) : {RN.isgo(_) == False{} : Bool}
        TP.solve_ends(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), lp_wf(es, ss)))))
    case SX.Sat{+t}:
      sat_noref(es, ss, t, Equal.sym(SX.Run, SX.Sat{t}, SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), hr), hc)
    case SX.Unsat{+t, +i}:
      RP2.sound.r(es, ss, SX.Unsat{t, i}, hr)

def ok.c(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, mj: Maybe<&2, Nat>, hmj: {mj == RF.crow(RF.Walk.rows(RF.walk(es, Nil{})), 0n) : Maybe<&2, Nat>}) -> RefOk(es, ss, RF.cert(es, ss, RF.decide.c(RF.walk(es, Nil{}), mj, ss))):
  match mj:
    case Some{+j}:
      RP2.sound.c(es, ss, Some{j}, hmj)
    case None{}:
      ok.r(es, ss, SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), {==}, Equal.sym(Maybe<&2, Nat>, None{}, RF.crow(RF.Walk.rows(RF.walk(es, Nil{})), 0n), hmj))

def refute_ok(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>) -> RefOk(es, ss, RF.refute(es, ss)):
  ok.c(es, ss, RF.crow(RF.Walk.rows(RF.walk(es, Nil{})), 0n), {==})

# The point itself
# ----------------

# two functionals killing every equation of es, every side of ss at its
# sign, with weights 1 and 0 at the monomial 1
def PtOk(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +c0: List<&2, O.C(F)>, +c1: List<&2, O.C(F)>, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>) -> Type:
  AllK(~F, ms, c0, es) & (AllK(~F, ms, c1, es) & (AllS(~F, ms, c0, c1, ss) & ((@k: S.Q -> {IP.psi(~F, ms, c0, E.QCst{k}) == O.ofq(~F, k) : O.C(F)}) & (@k: S.Q -> {IP.psi(~F, ms, c1, E.QCst{k}) == O.zero(F) : O.C(F)}))))

def Point(~F: O.OField, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>) -> Type:
  &ms: List<&2, List<&2, Nat>> -> &c0: List<&2, O.C(F)> -> &c1: List<&2, O.C(F)> -> PtOk(~F, ms, c0, c1, es, ss)

def pt_noref.go(~F: O.OField, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, p: Point(~F, es, ss), +ls: List<&2, S.Q>, +mm: List<&2, S.Q>, +k: S.Q, hr: SV.Refutes0(es, ss, ls, mm, k)) -> Empty:
  (+ms, p1) = p
  (+c0, p2) = p1
  (+c1, p3) = p2
  (hk0, q1) = p3
  (hk1, q2) = q1
  (hs, q3) = q2
  (h0, h1) = q3
  pt_contra(~F, ms, c0, c1, es, ss, ls, mm, k, hk0, hk1, hs, h0(k), h1(k), hr)

# a point: no refutation
def pt_noref(~F: O.OField, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, p: Point(~F, es, ss)) -> NoRef(es, ss):
  ls => mm => k => hr => pt_noref.go(~F, es, ss, p, ls, mm, k, hr)

def pt_c0(~F: O.OField, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +t: SX.Tab, +h: {SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)) == SX.Sat{t} : SX.Run}, +hc: {RF.crow(RF.Walk.rows(RF.walk(es, Nil{})), 0n) == None{} : Maybe<&2, Nat>}, +k: S.Q) -> {IP.psi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), E.QCst{k}) == O.ofq(~F, k) : O.C(F)}:
  Equal.trans(O.C(F), IP.psi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), E.QCst{k}), O.mul(F, O.one(F), O.ofq(~F, k)), O.ofq(~F, k),
    psi_cst(~F, RF.Walk.rows(RF.walk(es, Nil{})), RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss))))), k, crow_none(RF.Walk.rows(RF.walk(es, Nil{})), 0n, hc), allcon_ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}, {==})), FR.fring_eq(~F, [O.ofq(~F, k)], E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, E.ZVar{0n}, {==}))

def pt_c1(~F: O.OField, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +t: SX.Tab, +h: {SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)) == SX.Sat{t} : SX.Run}, +hc: {RF.crow(RF.Walk.rows(RF.walk(es, Nil{})), 0n) == None{} : Maybe<&2, Nat>}, +k: S.Q) -> {IP.psi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), E.QCst{k}) == O.zero(F) : O.C(F)}:
  Equal.trans(O.C(F), IP.psi(~F, bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), E.QCst{k}), O.mul(F, O.zero(F), O.ofq(~F, k)), O.zero(F),
    psi_cst(~F, RF.Walk.rows(RF.walk(es, Nil{})), RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss))))), k, crow_none(RF.Walk.rows(RF.walk(es, Nil{})), 0n, hc), allcon_ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}, {==})), FL.zero_mul(~F, O.ofq(~F, k)))

def sat_point(~F: O.OField, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +t: SX.Tab, +h: {SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)) == SX.Sat{t} : SX.Run}, +hc: {RF.crow(RF.Walk.rows(RF.walk(es, Nil{})), 0n) == None{} : Maybe<&2, Nat>}) -> Point(~F, es, ss):
  (bms(RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}), (bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), (bcs(~F, RF.Walk.rows(RF.walk(es, Nil{})), Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}), (kill_all(~F, Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.one(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v0(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}, es), (kill_all(~F, Con{Nil{}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})}, Con{O.zero(F), SP.ydrop(~F, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SP.rmap(~F, SX.Tab.rows(t), RN.zv(~F, SX.LP.v1(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))))}, es), (allside(~F, es, ss, t, h, ss, 0n, {==}),
    (k => pt_c0(~F, es, ss, t, h, hc, k), k => pt_c1(~F, es, ss, t, h, hc, k))))))))

# when refute finds nothing, a point
def RefPt(~F: O.OField, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, mc: Maybe<&2, RF.Cert>) -> Type:
  match mc:
    case None{}:
      Point(~F, es, ss)
    case Some{c}:
      Unit

def pt.r(~F: O.OField, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, r: SX.Run, hr: {r == SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)) : SX.Run}, +hc: {RF.crow(RF.Walk.rows(RF.walk(es, Nil{})), 0n) == None{} : Maybe<&2, Nat>})
  -> RefPt(~F, es, ss, RF.cert.run(RF.Walk.keep(RF.walk(es, Nil{})), es, ss, RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), r)):
  match r:
    case SX.Go{+t}:
      absurd(RefPt(~F, es, ss, None{}), KA.tf((%Equal.sym(SX.Run, SX.Go{t}, SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), hr) : {RN.isgo(_) == False{} : Bool}
        TP.solve_ends(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), lp_wf(es, ss)))))
    case SX.Sat{+t}:
      sat_point(~F, es, ss, t, Equal.sym(SX.Run, SX.Sat{t}, SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), hr), hc)
    case SX.Unsat{t, i}:
      Unit{}

def pt.c(~F: O.OField, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, mj: Maybe<&2, Nat>, hmj: {mj == RF.crow(RF.Walk.rows(RF.walk(es, Nil{})), 0n) : Maybe<&2, Nat>}) -> RefPt(~F, es, ss, RF.cert(es, ss, RF.decide.c(RF.walk(es, Nil{}), mj, ss))):
  match mj:
    case Some{j}:
      Unit{}
    case None{}:
      pt.r(~F, es, ss, SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), {==}, Equal.sym(Maybe<&2, Nat>, None{}, RF.crow(RF.Walk.rows(RF.walk(es, Nil{})), 0n), hmj))

def refute_pt(~F: O.OField, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>) -> RefPt(~F, es, ss, RF.refute(es, ss)):
  pt.c(~F, es, ss, RF.crow(RF.Walk.rows(RF.walk(es, Nil{})), 0n), {==})

# refute found nothing: a point
def pt_of_none(~F: O.OField, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, h: {RF.refute(es, ss) == None{} : Maybe<&2, RF.Cert>}) -> Point(~F, es, ss):
  %h : RefPt(~F, es, ss, _)
  refute_pt(~F, es, ss)
