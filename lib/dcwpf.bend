# bend-cad: one constraint's equations through the elimination and the
# closure, for the pass with the direction layer (PLAN-sk13b B4.4).
# Proofs only.
#
# lib/dpass.bend's cwalk2 walks c's equations as lib/pass.bend's cwalk
# does, with one more way to drop: an equation with a nonzero residual is
# dropped when the closure of the facts it may read holds it (or
# explodes), with that derivation's nd, and joins the basis otherwise.
# The proof follows lib/cwpf.bend (whose invariant CWInv it reuses):
# - the closure's decision is exact (dd_ok): a derivation it returns is
#   valid and proves the equation, and when it returns none there is none
#   (lib/dcholdpf, lib/dcexplpf, lib/dcdecpf), from any outcome with
#   Ex (lib/dcexpf.bend); the walk's calls start from the state kept
#   across calls, W, valid for facts that the kept constraints' facts
#   extend (WInv), and a warm call gives Ex (lib/dwarmpf.bend wcall_ex);
# - the facts the walk reads at k are the spec's dfacts with the final
#   drops (fk_eq: the drops agree before k, and ofacts reads them only
#   there), so the decision is DirDerivable or NotDirDerivable;
# - each recorded drop's nd suffices (DropsNd), carried along the walk as
#   "the drops so far suffice, then so do the final ones".
# Result (cw2_final): DropsOk and DropsNd of the extended Honest for the
# walk's drops, and the invariant at its end.
#
# Generated from tools/drafts/dcwpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ../spec/_draft13b.bend as DH
import ../spec/dir.bend as DR
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as LI
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./drvpf.bend as DV
import ./indpf.bend as IN
import ./conflict.bend as CO
import ./pass.bend as PA
import ./kbpf.bend as KB
import ./ownpf.bend as OW
import ./solvedpf.bend as SP
import ./seppf.bend as SEP
import ./cwpf.bend as CW
import ./prepf.bend as PR
import ./wfdec.bend as WF
import ./covpf.bend as CV
import ./dclose.bend as DC
import ./dcroundpf.bend as DRP
import ./dctermpf.bend as TRM
import ./dcreprpf.bend as RR
import ./dcholdpf.bend as HLD
import ./dcexplpf.bend as EXP
import ./dcdecpf.bend as DEC
import ./dcexpf.bend as CX
import ./dmemopf.bend as MP
import ./dwarmpf.bend as DW
import ./dpassmpf.bend as DPM
import ./drefpf.bend as DRF
import ./dconflict.bend as DCF
import ./dbridgepf.bend as BRG
import ./dpass.bend as DPS


def absurd(-A: Type, x: Empty) -> A:
  match x:

# The closure's decision, exact
# -----------------------------

# what a decision means: a derivation that is valid and proves e, or that
# none exists
def DDec(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +e: E.QExpr, +m: Maybe<&2, DR.DStat>, mm: Maybe<&2, DR.Der>) -> Type:
  match mm:
    case None{}:
      @dv: DR.Der -> DR.Valid(es, fs, ctx, dv) -> SV.Proves(es, m, e, DR.concl(es, fs, dv)) -> Empty
    case Some{+d}:
      DR.Valid(es, fs, ctx, d) & SV.Proves(es, m, e, DR.concl(es, fs, d))

def dd.h(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +e: E.QExpr, +m: Maybe<&2, DR.DStat>, +eb: {DC.holds(es, fs, t, s, e, m) == b : Bool}, +H: RR.Hyp(es, fs, ctx, t, s),
  +hbm: {DC.fb.ds(m, t) == True{} : Bool}) -> DDec(es, fs, ctx, e, m, DPS.ddec.h(b, es, fs, t, s, e, m)):
  match b:
    case True{}:
      HLD.hold_ok(es, fs, ctx, t, s, H, e, m, eb, hbm)
    case False{}:
      dv => hv => hp => DEC.dec_none(es, fs, ctx, t, s, H, e, m, eb, dv, hv, hp)

# the decision from any outcome with Ex (lib/dcexpf.bend) is exact
def dd_ok(o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +e: E.QExpr, +m: Maybe<&2, DR.DStat>, hx: CX.Ex(es, fs, ctx, t, o),
  +hbm: {DC.fb.ds(m, t) == True{} : Bool}) -> DDec(es, fs, ctx, e, m, DPS.ddec.o(o, es, fs, t, e, m)):
  match o:
    case DC.OStep{+s}:
      absurd(DDec(es, fs, ctx, e, m, None{}), hx)
    case DC.OFix{+s}:
      dd.h(DC.holds(es, fs, t, s, e, m), es, fs, ctx, t, s, e, m, {==}, hx, hbm)
    case DC.OOne{+d}:
      EXP.expl_ok(DC.OOne{d}, es, fs, ctx, t, m, e, hx, {==})
    case DC.OVoid{+g, +dr, +di}:
      EXP.expl_ok(DC.OVoid{g, dr, di}, es, fs, ctx, t, m, e, hx, {==})

# The facts' bound
# ----------------

def fb_cat(xs: List<&2, DR.Fact>, +ys: List<&2, DR.Fact>, +t: Nat, +hx: {DC.fb(xs, t) == True{} : Bool}, +hy: {DC.fb(ys, t) == True{} : Bool}) -> {DC.fb(SV.fcat(xs, ys), t) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case Con{DR.Fact{+e, +nd, +ds}, +tl}:
      +h1 = LI.band_r(SEP.vbelow(e, t), SV.band(DC.fb.ds(ds, t), DC.fb(tl, t)), hx)
      LI.band_i(SEP.vbelow(e, t), SV.band(DC.fb.ds(ds, t), DC.fb(SV.fcat(tl, ys), t)), LI.band_l(SEP.vbelow(e, t), SV.band(DC.fb.ds(ds, t), DC.fb(tl, t)), hx),
        LI.band_i(DC.fb.ds(ds, t), DC.fb(SV.fcat(tl, ys), t), LI.band_l(DC.fb.ds(ds, t), DC.fb(tl, t), h1), fb_cat(tl, ys, t, LI.band_r(DC.fb.ds(ds, t), DC.fb(tl, t), h1), hy)))

def fb_ofgo(xs: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +c: Nat, +d: List<&2, Nat>, +i: Nat, +k: Nat, +n: Nat, +hw: {CV.ewithin(xs, n) == True{} : Bool}, +hz: {DC.zb(SV.ents(sk), 1n+n) == True{} : Bool})
  -> {DC.fb(SV.ofacts.go(xs, own, sk, c, d, i, k), 1n+n) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      BRG.fb_pick(SV.band(SV.lt(k, i), SV.band(SV.eq(SV.nth(own, k), c), SV.bnot(SV.mem(k, d)))), e, Nil{}, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.ofacts.go(t, own, sk, c, d, i, 1n+k), 1n+n,
        BRG.vb_of(e, n, CV.and_l(BX.QExpr.within(e, n), CV.ewithin(t, n), hw)), BRG.fbds_of(SV.kind_at(sk, c), SV.ents(sk), 1n+n, hz),
        fb_ofgo(t, own, sk, c, d, i, 1n+k, n, CV.and_r(BX.QExpr.within(e, n), CV.ewithin(t, n), hw), hz))

# the facts c's i-th equation may read are below the closure's bound
def fb_df(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +i: Nat, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> {DC.fb(SV.dfacts(sk, cls, R, c, d, i), DCF.tv(sk)) == True{} : Bool}:
  fb_cat(SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n), SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, d, i, 0n), DCF.tv(sk),
    BRG.fb_go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n, PA.nvars(sk), BRG.ew_of(sk, PA.nvars(sk), hcov, hwf), BRG.zb_tv(sk, hcov)),
    fb_ofgo(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, d, i, 0n, PA.nvars(sk), BRG.ew_of(sk, PA.nvars(sk), hcov, hwf), BRG.zb_tv(sk, hcov)))

# The facts the walk reads
# ------------------------


# drops at i or later do not change c's own facts before i
def of_cat(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +c: Nat, +X: List<&2, Nat>, +d: List<&2, Nat>, +i: Nat, +j: Nat, +hg: {OW.geall(X, i) == True{} : Bool})
  -> {SV.ofacts.go(es, own, sk, c, SV.cat(X, d), i, j) == SV.ofacts.go(es, own, sk, c, d, i, j) : List<&2, DR.Fact>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, t}:
      %Equal.sym(List<&2, DR.Fact>, SV.ofacts.go(t, own, sk, c, SV.cat(X, d), i, 1n+j), SV.ofacts.go(t, own, sk, c, d, i, 1n+j), of_cat(t, own, sk, c, X, d, i, 1n+j, hg)) : {SV.facts.pick(SV.band(SV.lt(j, i), SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, SV.cat(X, d))))), DR.Fact{e, Nil{}, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))}, _) == SV.facts.pick(SV.band(SV.lt(j, i), SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, d)))), DR.Fact{e, Nil{}, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))}, SV.ofacts.go(t, own, sk, c, d, i, 1n+j)) : List<&2, DR.Fact>}
      %SP.band_ag(SV.lt(j, i), SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, d))), SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, SV.cat(X, d)))), hl => Equal.sym(Bool, SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, SV.cat(X, d)))), SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, d))), SP.or_cat.h(SV.nth(own, j), c, X, d, i, j, hg, hl))) : {SV.facts.pick(_, DR.Fact{e, Nil{}, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))}, SV.ofacts.go(t, own, sk, c, d, i, 1n+j)) == SV.facts.pick(SV.band(SV.lt(j, i), SV.band(SV.eq(SV.nth(own, j), c), SV.bnot(SV.mem(j, d)))), DR.Fact{e, Nil{}, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))}, SV.ofacts.go(t, own, sk, c, d, i, 1n+j)) : List<&2, DR.Fact>}
      {==}

def of_x(+sk: SK.Sketch, +c: Nat, +k: Nat, +dF: List<&2, Nat>, +d: List<&2, Nat>, xr: CW.XRel(dF, d, k)) -> {SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, d, k, 0n) == SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, dF, k, 0n) : List<&2, DR.Fact>}:
  (+X, xq) = xr
  (hX, hg) = xq
  (%Equal.sym(List<&2, Nat>, dF, SV.cat(X, d), hX) : {SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, d, k, 0n) == SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, _, k, 0n) : List<&2, DR.Fact>}
    Equal.sym(List<&2, DR.Fact>, SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, SV.cat(X, d), k, 0n), SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, d, k, 0n), of_cat(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, X, d, k, 0n, hg)))

# the walk's facts at k are the spec's, with the final drops dF
def fk_eq(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +c: Nat, +F0: List<&2, DR.Fact>, +ds: List<&2, SV.Drop>, +k: Nat, +dF: List<&2, Nat>,
  +hF0: {F0 == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n) : List<&2, DR.Fact>}, +xr: CW.XRel(dF, SV.drops(ds), k)) -> {DPS.fk(sk, c, F0, ds, k) == SV.dfacts(sk, cls, R, c, dF, k) : List<&2, DR.Fact>}:
  %hF0 : {SV.fcat(F0, SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, SV.drops(ds), k, 0n)) == SV.fcat(_, SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, dF, k, 0n)) : List<&2, DR.Fact>}
  %of_x(sk, c, k, dF, SV.drops(ds), xr) : {SV.fcat(F0, SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, SV.drops(ds), k, 0n)) == SV.fcat(F0, _) : List<&2, DR.Fact>}
  {==}

# The decision at equation k, as the spec reads it
# ------------------------------------------------

def ddk(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +c: Nat, +dF: List<&2, Nat>, +k: Nat, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, SV.kept_before(sk, R, c)), SV.ctx(sk, R, c), DCF.tv(sk), W), +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> DDec(SV.ents(sk), SV.dfacts(sk, cls, R, c, dF, k), SV.ctx(sk, R, c), SV.eqat(SK.Sketch.eqs(sk), k), DPS.cstat(sk, c), DPS.ddec(sk, SV.dfacts(sk, cls, R, c, dF, k), SV.ctx(sk, R, c), SV.eqat(SK.Sketch.eqs(sk), k), DPS.cstat(sk, c), W)):
  dd_ok(DC.FO.o(DC.wcall(SV.ents(sk), SV.dfacts(sk, cls, R, c, dF, k), DCF.tv(sk), W)), SV.ents(sk), SV.dfacts(sk, cls, R, c, dF, k), SV.ctx(sk, R, c), DCF.tv(sk), SV.eqat(SK.Sketch.eqs(sk), k), DPS.cstat(sk, c),
    DW.wcall_ex(SV.ents(sk), SV.rfacts(sk, SV.kept_before(sk, R, c)), SV.dfacts(sk, cls, R, c, dF, k), SV.ctx(sk, R, c), DCF.tv(sk), W, hw, MP.pre_cat(SV.rfacts(sk, SV.kept_before(sk, R, c)), SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n), SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, dF, k, 0n), DPM.facts_pre(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, Nil{}, False{}, cls, True{}, 0n)),
      BRG.zb_tv(sk, hcov), fb_df(sk, cls, R, c, dF, k, hcov, hwf)), BRG.fbds_of(SV.kind_at(sk, c), SV.ents(sk), DCF.tv(sk), BRG.zb_tv(sk, hcov)))


def ddtr(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +hF0: {F0 == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n) : List<&2, DR.Fact>}, +hcx: {cx == SV.ctx(sk, R, c) : List<&2, E.QExpr>}, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, SV.kept_before(sk, R, c)), cx, DCF.tv(sk), W), +ds: List<&2, SV.Drop>, +k: Nat, +e: E.QExpr, +dF: List<&2, Nat>, +he: {SV.eqat(SK.Sketch.eqs(sk), k) == e : E.QExpr}, +xr: CW.XRel(dF, SV.drops(ds), k), +mm: Maybe<&2, DR.Der>, h: {DPS.ddec(sk, DPS.fk(sk, c, F0, ds, k), cx, e, DPS.cstat(sk, c), W) == mm : Maybe<&2, DR.Der>}) -> {DPS.ddec(sk, SV.dfacts(sk, cls, R, c, dF, k), SV.ctx(sk, R, c), SV.eqat(SK.Sketch.eqs(sk), k), DPS.cstat(sk, c), W) == mm : Maybe<&2, DR.Der>}:
  (%Equal.sym(E.QExpr, SV.eqat(SK.Sketch.eqs(sk), k), e, he) : {DPS.ddec(sk, SV.dfacts(sk, cls, R, c, dF, k), SV.ctx(sk, R, c), _, DPS.cstat(sk, c), W) == mm : Maybe<&2, DR.Der>}
    (%hcx : {DPS.ddec(sk, SV.dfacts(sk, cls, R, c, dF, k), _, e, DPS.cstat(sk, c), W) == mm : Maybe<&2, DR.Der>}
      (%fk_eq(sk, cls, R, c, F0, ds, k, dF, hF0, xr) : {DPS.ddec(sk, _, cx, e, DPS.cstat(sk, c), W) == mm : Maybe<&2, DR.Der>}
        h)))

# the walk's decision at k means what the spec asks
def ddat(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +hF0: {F0 == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n) : List<&2, DR.Fact>}, +hcx: {cx == SV.ctx(sk, R, c) : List<&2, E.QExpr>}, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, SV.kept_before(sk, R, c)), cx, DCF.tv(sk), W), +ds: List<&2, SV.Drop>, +k: Nat, +e: E.QExpr, +dF: List<&2, Nat>, +he: {SV.eqat(SK.Sketch.eqs(sk), k) == e : E.QExpr}, +xr: CW.XRel(dF, SV.drops(ds), k), +mm: Maybe<&2, DR.Der>, h: {DPS.ddec(sk, DPS.fk(sk, c, F0, ds, k), cx, e, DPS.cstat(sk, c), W) == mm : Maybe<&2, DR.Der>}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> DDec(SV.ents(sk), SV.dfacts(sk, cls, R, c, dF, k), SV.ctx(sk, R, c), SV.eqat(SK.Sketch.eqs(sk), k), DPS.cstat(sk, c), mm):
  (%ddtr(sk, cls, R, c, F0, cx, hF0, hcx, W, hw, ds, k, e, dF, he, xr, mm, h) : DDec(SV.ents(sk), SV.dfacts(sk, cls, R, c, dF, k), SV.ctx(sk, R, c), SV.eqat(SK.Sketch.eqs(sk), k), DPS.cstat(sk, c), _)
    ddk(sk, cls, R, c, dF, k, W, (%hcx : DW.WInv(SV.ents(sk), SV.rfacts(sk, SV.kept_before(sk, R, c)), _, DCF.tv(sk), W)
      hw), hcov, hwf))

def dnone_k(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +hF0: {F0 == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n) : List<&2, DR.Fact>}, +hcx: {cx == SV.ctx(sk, R, c) : List<&2, E.QExpr>}, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, SV.kept_before(sk, R, c)), cx, DCF.tv(sk), W), +ds: List<&2, SV.Drop>, +k: Nat, +e: E.QExpr, +dF: List<&2, Nat>, +he: {SV.eqat(SK.Sketch.eqs(sk), k) == e : E.QExpr}, +xr: CW.XRel(dF, SV.drops(ds), k), hdd: {DPS.ddec(sk, DPS.fk(sk, c, F0, ds, k), cx, e, DPS.cstat(sk, c), W) == None{} : Maybe<&2, DR.Der>}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> SV.NotDirDerivable(sk, cls, R, c, dF, k):
  ddat(sk, cls, R, c, F0, cx, hF0, hcx, W, hw, ds, k, e, dF, he, xr, None{}, hdd, hcov, hwf)

def dsk.go(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +hF0: {F0 == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n) : List<&2, DR.Fact>}, +hcx: {cx == SV.ctx(sk, R, c) : List<&2, E.QExpr>}, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, SV.kept_before(sk, R, c)), cx, DCF.tv(sk), W), +ds: List<&2, SV.Drop>, +k: Nat, +e: E.QExpr, +dF: List<&2, Nat>, +he: {SV.eqat(SK.Sketch.eqs(sk), k) == e : E.QExpr}, +xr: CW.XRel(dF, SV.drops(ds), k), +der: DR.Der, h: DR.Valid(SV.ents(sk), SV.dfacts(sk, cls, R, c, dF, k), SV.ctx(sk, R, c), der) & SV.Proves(SV.ents(sk), DPS.cstat(sk, c), SV.eqat(SK.Sketch.eqs(sk), k), DR.concl(SV.ents(sk), SV.dfacts(sk, cls, R, c, dF, k), der))) -> SV.DirDerivable(sk, cls, R, c, dF, k, DR.nd(SV.ents(sk), DPS.fk(sk, c, F0, ds, k), der)):
  (hv, hp) = h
  (der, (hv, (hp, (%Equal.sym(List<&2, DR.Fact>, DPS.fk(sk, c, F0, ds, k), SV.dfacts(sk, cls, R, c, dF, k), fk_eq(sk, cls, R, c, F0, ds, k, dF, hF0, xr)) : {SV.sub(DR.nd(SV.ents(sk), SV.dfacts(sk, cls, R, c, dF, k), der), DR.nd(SV.ents(sk), _, der)) == True{} : Bool}
    PR.sub_refl(DR.nd(SV.ents(sk), SV.dfacts(sk, cls, R, c, dF, k), der))))))

# a direction drop at k: DirDerivable with the nd it records
def dsome_k(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +hF0: {F0 == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n) : List<&2, DR.Fact>}, +hcx: {cx == SV.ctx(sk, R, c) : List<&2, E.QExpr>}, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, SV.kept_before(sk, R, c)), cx, DCF.tv(sk), W), +ds: List<&2, SV.Drop>, +k: Nat, +e: E.QExpr, +dF: List<&2, Nat>, +he: {SV.eqat(SK.Sketch.eqs(sk), k) == e : E.QExpr}, +xr: CW.XRel(dF, SV.drops(ds), k), +der: DR.Der, +hds: {DPS.ddec(sk, DPS.fk(sk, c, F0, ds, k), cx, e, DPS.cstat(sk, c), W) == Some{der} : Maybe<&2, DR.Der>}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> SV.DirDerivable(sk, cls, R, c, dF, k, DR.nd(SV.ents(sk), DPS.fk(sk, c, F0, ds, k), der)):
  dsk.go(sk, cls, R, c, F0, cx, hF0, hcx, W, hw, ds, k, e, dF, he, xr, der, ddat(sk, cls, R, c, F0, cx, hF0, hcx, W, hw, ds, k, e, dF, he, xr, Some{der}, hds, hcov, hwf))

# Degree 0 at k, with the final drops
# -----------------------------------


def der0(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, +e: E.QExpr, +dF: List<&2, Nat>,
  +he: {SV.eqat(SK.Sketch.eqs(sk), k) == e : E.QExpr}, +hnil: {EP.isnil(EP.resp(EL.resid(rows, e))) == True{} : Bool}, +hb: {CW.cwb(sk, c, k, rows, B, ds, us) == True{} : Bool}, +hB: {B == SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, SV.drops(ds), k)) : List<&2, E.QExpr>}, +xr2: CW.XRel(dF, SV.drops(ds), k))
  -> SV.Derivable(sk, R, D, c, dF, k):
  (DV.dropls(DV.rescb(EL.resid(rows, e)), DV.resbt(EL.resid(rows, e)), e, B), (%Equal.sym(E.QExpr, SV.eqat(SK.Sketch.eqs(sk), k), e, he) : SV.Ident(_, SV.lin(DV.dropls(DV.rescb(EL.resid(rows, e)), DV.resbt(EL.resid(rows, e)), e, B), SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, dF, k))))
    (%Equal.sym(List<&2, E.QExpr>, SV.own_rest(sk, c, dF, k), SV.own_rest(sk, c, SV.drops(ds), k), CW.or_x(sk, c, k, dF, SV.drops(ds), xr2)) : SV.Ident(e, SV.lin(DV.dropls(DV.rescb(EL.resid(rows, e)), DV.resbt(EL.resid(rows, e)), e, B), SK.cat(SV.presolved(sk, R, D, c), _)))
      (%hB : SV.Ident(e, SV.lin(DV.dropls(DV.rescb(EL.resid(rows, e)), DV.resbt(EL.resid(rows, e)), e, B), _))
        DV.derivable(B, rows, e, CW.cwb_rinv(sk, c, k, rows, B, ds, us, hb), hnil)))))

def nder0(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, +e: E.QExpr, +dF: List<&2, Nat>,
  +he: {SV.eqat(SK.Sketch.eqs(sk), k) == e : E.QExpr}, +hne: {EP.isnil(EP.resp(EL.resid(rows, e))) == False{} : Bool}, +hb: {CW.cwb(sk, c, k, rows, B, ds, us) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat}, +hB: {B == SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, SV.drops(ds), k)) : List<&2, E.QExpr>}, +xr1: CW.XRel(dF, SV.drops(ds), k))
  -> SV.NotDerivable(sk, R, D, c, dF, k):
  (%Equal.sym(E.QExpr, SV.eqat(SK.Sketch.eqs(sk), k), e, he) : (@ls: List<&2, S.Q> -> SV.Ident(_, SV.lin(ls, SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, dF, k)))) -> Empty)
    (%Equal.sym(List<&2, E.QExpr>, SV.own_rest(sk, c, dF, k), SV.own_rest(sk, c, SV.drops(ds), k), CW.or_x(sk, c, k, dF, SV.drops(ds), xr1)) : (@ls: List<&2, S.Q> -> SV.Ident(e, SV.lin(ls, SK.cat(SV.presolved(sk, R, D, c), _))) -> Empty)
      (%hB : (@ls: List<&2, S.Q> -> SV.Ident(e, SV.lin(ls, _)) -> Empty)
        IN.indep(B, rows, e, CW.cwb_rinv(sk, c, k, rows, B, ds, us, hb), hl, hne))))

# The invariant after a direction drop
# ------------------------------------

def inv_dropx(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, +nd: List<&2, Nat>, +q: SV.Comb,
  hi: CW.CWInv(sk, R, D, c, bp0, k, PA.CW{rows, B, bp, ds, us}), +heq: {SV.eq(SV.nth(SV.owners(sk), k), c) == True{} : Bool}, +hk: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool})
  -> CW.CWInv(sk, R, D, c, bp0, 1n+k, PA.CW{rows, B, bp, Con{SV.Drop{k, nd, q}, ds}, us}):
  (+hb, q1) = hi
  (hl, q2) = q1
  (hB, q3) = q2
  (hp, hbp) = q3
  +hdb = CW.cwb_dbelow(sk, c, k, rows, B, ds, us, hb)
  (CW.cwb_mk(sk, c, 1n+k, rows, B, Con{SV.Drop{k, nd, q}, ds}, us, CW.cwb_rinv(sk, c, k, rows, B, ds, us, hb),
      LI.band_i(SV.lt(k, 1n+k), SV.below(SV.drops(ds), 1n+k), KB.lt_succ(k), KB.below_up(SV.drops(ds), k, hdb)),
      LI.band_i(SV.bnot(SV.mem(k, SV.drops(ds))), SV.distinct(SV.drops(ds)), KB.bnot_f(SV.mem(k, SV.drops(ds)), KB.below_notmem(SV.drops(ds), k, hdb)), CW.cwb_ddist(sk, c, k, rows, B, ds, us, hb)),
      LI.band_i(SV.eq(SV.nth(SV.owners(sk), k), c), KB.allo(SV.owners(sk), SV.drops(ds), c), heq, CW.cwb_down(sk, c, k, rows, B, ds, us, hb)),
      CW.nonein_cons(us, k, SV.drops(ds), CW.cwb_udisj(sk, c, k, rows, B, ds, us, hb), CW.cwb_ubelow(sk, c, k, rows, B, ds, us, hb)), CW.cwb_udist(sk, c, k, rows, B, ds, us, hb), KB.below_up(us, k, CW.cwb_ubelow(sk, c, k, rows, B, ds, us, hb)), CW.cwb_uown(sk, c, k, rows, B, ds, us, hb)),
    (hl, (Equal.trans(List<&2, E.QExpr>, B, SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, SV.drops(ds), k)), SK.cat(SV.presolved(sk, R, D, c), SV.own_rest(sk, c, Con{k, SV.drops(ds)}, 1n+k)), hB, Equal.cong(List<&2, E.QExpr>, List<&2, E.QExpr>, y => SK.cat(SV.presolved(sk, R, D, c), y), SV.own_rest(sk, c, SV.drops(ds), k), SV.own_rest(sk, c, Con{k, SV.drops(ds)}, 1n+k), Equal.sym(List<&2, E.QExpr>, SV.own_rest(sk, c, Con{k, SV.drops(ds)}, 1n+k), SV.own_rest(sk, c, SV.drops(ds), k), CW.or_drop(sk, c, SV.drops(ds), k, heq, hk)))),
    (hp, hbp))))

# The walk's result from k
# ------------------------

# the drops so far suffice, then so do the final ones
def NDT(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +dF: List<&2, Nat>, +ds: List<&2, SV.Drop>, +dsF: List<&2, SV.Drop>) -> Type:
  DH.drops_nd(sk, cls, R, D, c, dF, ds) -> DH.drops_nd(sk, cls, R, D, c, dF, dsF)

def CWRes2(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, own_k: List<&2, Nat>, +st: PA.CW, +fin: PA.CW) -> Type:
  CW.XRel(SV.drops(CW.cw.ds(fin)), SV.drops(CW.cw.ds(st)), k) & (DH.drops_ok.go(sk, cls, R, D, c, SV.drops(CW.cw.ds(fin)), own_k, k) & (CW.CWInv(sk, R, D, c, bp0, SV.neqs(SK.Sketch.eqs(sk)), fin) & NDT(sk, cls, R, D, c, SV.drops(CW.cw.ds(fin)), CW.cw.ds(st), CW.cw.ds(fin))))

def res2_skip(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +o: Nat, +ot: List<&2, Nat>, st: PA.CW, +fin: PA.CW, +heo: {SV.eq(o, c) == False{} : Bool}, hi: CW.CWInv(sk, R, D, c, bp0, k, st), r: CWRes2(sk, cls, R, D, c, bp0, 1n+k, ot, st, fin))
  -> CWRes2(sk, cls, R, D, c, bp0, k, Con{o, ot}, st, fin):
  match st:
    case PA.CW{+rows, +B, +bp, +ds, +us}:
      (+hb, hq1) = hi
      (+xr, q) = r
      (dr, q2) = q
      (fr, nt) = q2
      (CW.xr_up(k, SV.drops(CW.cw.ds(fin)), SV.drops(ds), xr), (((%Equal.sym(Bool, SV.eq(o, c), False{}, heo) : DH.drops_ok.at(sk, cls, R, D, c, SV.drops(CW.cw.ds(fin)), _, k)
          CW.mem_x_f(k, SV.drops(CW.cw.ds(fin)), SV.drops(ds), xr, CW.cwb_dbelow(sk, c, k, rows, B, ds, us, hb))), dr), (fr, nt)))

def res2_drop(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +k: Nat, +o: Nat, +ot: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, +e: E.QExpr, +fin: PA.CW, +heo: {SV.eq(o, c) == True{} : Bool},
  +he: {SV.eqat(SK.Sketch.eqs(sk), k) == e : E.QExpr}, +hnil: {EP.isnil(EP.resp(EL.resid(rows, e))) == True{} : Bool}, hi: CW.CWInv(sk, R, D, c, bp0, k, PA.CW{rows, B, bp, ds, us}),
  r: CWRes2(sk, cls, R, D, c, bp0, 1n+k, ot, PA.CW{rows, B, bp, Con{PA.drop_of(k, EL.resid(rows, e), e, B, bp), ds}, us}, fin)) -> CWRes2(sk, cls, R, D, c, bp0, k, Con{o, ot}, PA.CW{rows, B, bp, ds, us}, fin):
  (+hb, q1) = hi
  (hl, q2) = q1
  (+hB, q3) = q2
  (+xr, q) = r
  (dr, q4) = q
  (fr, nt) = q4
  +xr2 = CW.xr_drop(k, SV.drops(CW.cw.ds(fin)), SV.drops(ds), xr)
  (xr2, (((%Equal.sym(Bool, SV.eq(o, c), True{}, heo) : DH.drops_ok.at(sk, cls, R, D, c, SV.drops(CW.cw.ds(fin)), _, k)
      (%Equal.sym(Bool, SV.mem(k, SV.drops(CW.cw.ds(fin))), True{}, CW.mem_x_t(k, SV.drops(CW.cw.ds(fin)), SV.drops(ds), xr)) : DH.drops_ok.mem(sk, cls, R, D, c, SV.drops(CW.cw.ds(fin)), _, k)
        Inl{der0(sk, R, D, c, k, rows, B, ds, us, e, SV.drops(CW.cw.ds(fin)), he, hnil, hb, hB, xr2)})), dr),
    (fr, h => nt((Inl{der0(sk, R, D, c, k, rows, B, ds, us, e, SV.drops(CW.cw.ds(fin)), he, hnil, hb, hB, xr2)}, h)))))


def res2_keep(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +hF0: {F0 == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n) : List<&2, DR.Fact>}, +hcx: {cx == SV.ctx(sk, R, c) : List<&2, E.QExpr>}, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, SV.kept_before(sk, R, c)), cx, DCF.tv(sk), W), +k: Nat, +o: Nat, +ot: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, +e: E.QExpr, +fin: PA.CW, +heo: {SV.eq(o, c) == True{} : Bool},
  +he: {SV.eqat(SK.Sketch.eqs(sk), k) == e : E.QExpr}, +hne: {EP.isnil(EP.resp(EL.resid(rows, e))) == False{} : Bool}, +hdd: {DPS.ddec(sk, DPS.fk(sk, c, F0, ds, k), cx, e, DPS.cstat(sk, c), W) == None{} : Maybe<&2, DR.Der>}, hi: CW.CWInv(sk, R, D, c, bp0, k, PA.CW{rows, B, bp, ds, us}), +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool},
  r: CWRes2(sk, cls, R, D, c, bp0, 1n+k, ot, PA.CW{EL.rsnoc(rows, EL.row_of(EL.resid(rows, e))), EP.qsnoc(B, e), CO.lsnoc(bp, k), ds, CO.lsnoc(us, k)}, fin)) -> CWRes2(sk, cls, R, D, c, bp0, k, Con{o, ot}, PA.CW{rows, B, bp, ds, us}, fin):
  (+hb, q1) = hi
  (+hl, q2) = q1
  (+hB, q3) = q2
  (+xr, q) = r
  (dr, q4) = q
  (fr, nt) = q4
  +xr1 = CW.xr_up(k, SV.drops(CW.cw.ds(fin)), SV.drops(ds), xr)
  (xr1, (((%Equal.sym(Bool, SV.eq(o, c), True{}, heo) : DH.drops_ok.at(sk, cls, R, D, c, SV.drops(CW.cw.ds(fin)), _, k)
      (%Equal.sym(Bool, SV.mem(k, SV.drops(CW.cw.ds(fin))), False{}, CW.mem_x_f(k, SV.drops(CW.cw.ds(fin)), SV.drops(ds), xr, CW.cwb_dbelow(sk, c, k, rows, B, ds, us, hb))) : DH.drops_ok.mem(sk, cls, R, D, c, SV.drops(CW.cw.ds(fin)), _, k)
        (nder0(sk, R, D, c, k, rows, B, ds, us, e, SV.drops(CW.cw.ds(fin)), he, hne, hb, hl, hB, xr1), dnone_k(sk, cls, R, c, F0, cx, hF0, hcx, W, hw, ds, k, e, SV.drops(CW.cw.ds(fin)), he, xr1, hdd, hcov, hwf)))), dr), (fr, nt)))

def res2_ddrop(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +hF0: {F0 == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n) : List<&2, DR.Fact>}, +hcx: {cx == SV.ctx(sk, R, c) : List<&2, E.QExpr>}, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, SV.kept_before(sk, R, c)), cx, DCF.tv(sk), W), +k: Nat, +o: Nat, +ot: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, +e: E.QExpr, +der: DR.Der, +fin: PA.CW, +heo: {SV.eq(o, c) == True{} : Bool},
  +he: {SV.eqat(SK.Sketch.eqs(sk), k) == e : E.QExpr}, +hds: {DPS.ddec(sk, DPS.fk(sk, c, F0, ds, k), cx, e, DPS.cstat(sk, c), W) == Some{der} : Maybe<&2, DR.Der>}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool},
  r: CWRes2(sk, cls, R, D, c, bp0, 1n+k, ot, PA.CW{rows, B, bp, Con{SV.Drop{k, DR.nd(SV.ents(sk), DPS.fk(sk, c, F0, ds, k), der), DPS.dcert(SV.ents(sk), DPS.fk(sk, c, F0, ds, k), der, DR.nd(SV.ents(sk), DPS.fk(sk, c, F0, ds, k), der))}, ds}, us}, fin)) -> CWRes2(sk, cls, R, D, c, bp0, k, Con{o, ot}, PA.CW{rows, B, bp, ds, us}, fin):
  (+xr, q) = r
  (dr, q4) = q
  (fr, nt) = q4
  +xr2 = CW.xr_drop(k, SV.drops(CW.cw.ds(fin)), SV.drops(ds), xr)
  (xr2, (((%Equal.sym(Bool, SV.eq(o, c), True{}, heo) : DH.drops_ok.at(sk, cls, R, D, c, SV.drops(CW.cw.ds(fin)), _, k)
      (%Equal.sym(Bool, SV.mem(k, SV.drops(CW.cw.ds(fin))), True{}, CW.mem_x_t(k, SV.drops(CW.cw.ds(fin)), SV.drops(ds), xr)) : DH.drops_ok.mem(sk, cls, R, D, c, SV.drops(CW.cw.ds(fin)), _, k)
        Inr{(DR.nd(SV.ents(sk), DPS.fk(sk, c, F0, ds, k), der), dsome_k(sk, cls, R, c, F0, cx, hF0, hcx, W, hw, ds, k, e, SV.drops(CW.cw.ds(fin)), he, xr2, der, hds, hcov, hwf))})), dr),
    (fr, h => nt((Inr{dsome_k(sk, cls, R, c, F0, cx, hF0, hcx, W, hw, ds, k, e, SV.drops(CW.cw.ds(fin)), he, xr2, der, hds, hcov, hwf)}, h)))))

# The walk
# --------


def cw2_ok.d(mm: Maybe<&2, DR.Der>, +sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +hF0: {F0 == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n) : List<&2, DR.Fact>}, +hcx: {cx == SV.ctx(sk, R, c) : List<&2, E.QExpr>}, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, SV.kept_before(sk, R, c)), cx, DCF.tv(sk), W), +e: E.QExpr, +t: List<&2, E.QExpr>, +o: Nat, +ot: List<&2, Nat>, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +em: {DPS.ddec(sk, DPS.fk(sk, c, F0, ds, k), cx, e, DPS.cstat(sk, c), W) == mm : Maybe<&2, DR.Der>}, +eb: {EP.isnil(EP.resp(EL.resid(rows, e))) == False{} : Bool}, +heq: {SV.eq(SV.nth(SV.owners(sk), k), c) == True{} : Bool}, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == Con{e, t} : List<&2, E.QExpr>}, +ho: {OW.ndrop(k, SV.owners(sk)) == Con{o, ot} : List<&2, Nat>}, +hlt: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +hi: CW.CWInv(sk, R, D, c, bp0, k, PA.CW{rows, B, bp, ds, us}), +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}, ih: @st2: PA.CW -> CW.CWInv(sk, R, D, c, bp0, 1n+k, st2) -> CWRes2(sk, cls, R, D, c, bp0, 1n+k, ot, st2, DPS.cwalk2(t, SV.owners(sk), c, 1n+k, st2, sk, F0, cx, W)))
  -> CWRes2(sk, cls, R, D, c, bp0, k, Con{o, ot}, PA.CW{rows, B, bp, ds, us}, DPS.cwalk2(t, SV.owners(sk), c, 1n+k, DPS.cw2.dir(mm, k, e, EL.resid(rows, e), rows, B, bp, ds, us, SV.ents(sk), DPS.fk(sk, c, F0, ds, k)), sk, F0, cx, W)):
  match mm:
    case None{}:
      res2_keep(sk, cls, R, D, c, bp0, F0, cx, hF0, hcx, W, hw, k, o, ot, rows, B, bp, ds, us, e, DPS.cwalk2(t, SV.owners(sk), c, 1n+k, PA.CW{EL.rsnoc(rows, EL.row_of(EL.resid(rows, e))), EP.qsnoc(B, e), CO.lsnoc(bp, k), ds, CO.lsnoc(us, k)}, sk, F0, cx, W), Equal.trans(Bool, SV.eq(o, c), SV.eq(SV.nth(SV.owners(sk), k), c), True{}, Equal.cong(Nat, Bool, x => SV.eq(x, c), o, SV.nth(SV.owners(sk), k), Equal.sym(Nat, SV.nth(SV.owners(sk), k), o, OW.nth_of(SV.owners(sk), k, o, ot, ho))), heq), OW.eqat_of(SK.Sketch.eqs(sk), k, e, t, hq), eb, em, hi, hcov, hwf,
        ih(PA.CW{EL.rsnoc(rows, EL.row_of(EL.resid(rows, e))), EP.qsnoc(B, e), CO.lsnoc(bp, k), ds, CO.lsnoc(us, k)}, CW.inv_keep(sk, R, D, c, bp0, k, rows, B, bp, ds, us, e, hi, heq, hlt, eb, OW.eqat_of(SK.Sketch.eqs(sk), k, e, t, hq))))
    case Some{+der}:
      res2_ddrop(sk, cls, R, D, c, bp0, F0, cx, hF0, hcx, W, hw, k, o, ot, rows, B, bp, ds, us, e, der, DPS.cwalk2(t, SV.owners(sk), c, 1n+k, PA.CW{rows, B, bp, Con{SV.Drop{k, DR.nd(SV.ents(sk), DPS.fk(sk, c, F0, ds, k), der), DPS.dcert(SV.ents(sk), DPS.fk(sk, c, F0, ds, k), der, DR.nd(SV.ents(sk), DPS.fk(sk, c, F0, ds, k), der))}, ds}, us}, sk, F0, cx, W), Equal.trans(Bool, SV.eq(o, c), SV.eq(SV.nth(SV.owners(sk), k), c), True{}, Equal.cong(Nat, Bool, x => SV.eq(x, c), o, SV.nth(SV.owners(sk), k), Equal.sym(Nat, SV.nth(SV.owners(sk), k), o, OW.nth_of(SV.owners(sk), k, o, ot, ho))), heq), OW.eqat_of(SK.Sketch.eqs(sk), k, e, t, hq), em, hcov, hwf,
        ih(PA.CW{rows, B, bp, Con{SV.Drop{k, DR.nd(SV.ents(sk), DPS.fk(sk, c, F0, ds, k), der), DPS.dcert(SV.ents(sk), DPS.fk(sk, c, F0, ds, k), der, DR.nd(SV.ents(sk), DPS.fk(sk, c, F0, ds, k), der))}, ds}, us}, inv_dropx(sk, R, D, c, bp0, k, rows, B, bp, ds, us, DR.nd(SV.ents(sk), DPS.fk(sk, c, F0, ds, k), der), DPS.dcert(SV.ents(sk), DPS.fk(sk, c, F0, ds, k), der, DR.nd(SV.ents(sk), DPS.fk(sk, c, F0, ds, k), der)), hi, heq, hlt)))

def cw2_ok.k(b: Bool, +sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +hF0: {F0 == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n) : List<&2, DR.Fact>}, +hcx: {cx == SV.ctx(sk, R, c) : List<&2, E.QExpr>}, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, SV.kept_before(sk, R, c)), cx, DCF.tv(sk), W), +e: E.QExpr, +t: List<&2, E.QExpr>, +o: Nat, +ot: List<&2, Nat>, +k: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +eb: {EP.isnil(EP.resp(EL.resid(rows, e))) == b : Bool}, +heq: {SV.eq(SV.nth(SV.owners(sk), k), c) == True{} : Bool}, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == Con{e, t} : List<&2, E.QExpr>}, +ho: {OW.ndrop(k, SV.owners(sk)) == Con{o, ot} : List<&2, Nat>}, +hlt: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +hi: CW.CWInv(sk, R, D, c, bp0, k, PA.CW{rows, B, bp, ds, us}), +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}, ih: @st2: PA.CW -> CW.CWInv(sk, R, D, c, bp0, 1n+k, st2) -> CWRes2(sk, cls, R, D, c, bp0, 1n+k, ot, st2, DPS.cwalk2(t, SV.owners(sk), c, 1n+k, st2, sk, F0, cx, W)))
  -> CWRes2(sk, cls, R, D, c, bp0, k, Con{o, ot}, PA.CW{rows, B, bp, ds, us}, DPS.cwalk2(t, SV.owners(sk), c, 1n+k, DPS.cw2.pick(EP.isnil(EP.resp(EL.resid(rows, e))), k, e, EL.resid(rows, e), rows, B, bp, ds, us, sk, c, F0, cx, W), sk, F0, cx, W)):
  match b:
    case True{}:
      %Equal.sym(Bool, EP.isnil(EP.resp(EL.resid(rows, e))), True{}, eb) : CWRes2(sk, cls, R, D, c, bp0, k, Con{o, ot}, PA.CW{rows, B, bp, ds, us}, DPS.cwalk2(t, SV.owners(sk), c, 1n+k, DPS.cw2.pick(_, k, e, EL.resid(rows, e), rows, B, bp, ds, us, sk, c, F0, cx, W), sk, F0, cx, W))
      res2_drop(sk, cls, R, D, c, bp0, k, o, ot, rows, B, bp, ds, us, e, DPS.cwalk2(t, SV.owners(sk), c, 1n+k, PA.CW{rows, B, bp, Con{PA.drop_of(k, EL.resid(rows, e), e, B, bp), ds}, us}, sk, F0, cx, W), Equal.trans(Bool, SV.eq(o, c), SV.eq(SV.nth(SV.owners(sk), k), c), True{}, Equal.cong(Nat, Bool, x => SV.eq(x, c), o, SV.nth(SV.owners(sk), k), Equal.sym(Nat, SV.nth(SV.owners(sk), k), o, OW.nth_of(SV.owners(sk), k, o, ot, ho))), heq), OW.eqat_of(SK.Sketch.eqs(sk), k, e, t, hq), eb, hi,
        ih(PA.CW{rows, B, bp, Con{PA.drop_of(k, EL.resid(rows, e), e, B, bp), ds}, us}, CW.inv_drop(sk, R, D, c, bp0, k, rows, B, bp, ds, us, e, hi, heq, hlt)))
    case False{}:
      %Equal.sym(Bool, EP.isnil(EP.resp(EL.resid(rows, e))), False{}, eb) : CWRes2(sk, cls, R, D, c, bp0, k, Con{o, ot}, PA.CW{rows, B, bp, ds, us}, DPS.cwalk2(t, SV.owners(sk), c, 1n+k, DPS.cw2.pick(_, k, e, EL.resid(rows, e), rows, B, bp, ds, us, sk, c, F0, cx, W), sk, F0, cx, W))
      cw2_ok.d(DPS.ddec(sk, DPS.fk(sk, c, F0, ds, k), cx, e, DPS.cstat(sk, c), W), sk, cls, R, D, c, bp0, F0, cx, hF0, hcx, W, hw, e, t, o, ot, k, rows, B, bp, ds, us, {==}, eb, heq, hq, ho, hlt, hi, hcov, hwf, ih)

def cw2_ok.s(st: PA.CW, +sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +hF0: {F0 == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n) : List<&2, DR.Fact>}, +hcx: {cx == SV.ctx(sk, R, c) : List<&2, E.QExpr>}, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, SV.kept_before(sk, R, c)), cx, DCF.tv(sk), W), +e: E.QExpr, +t: List<&2, E.QExpr>, +o: Nat, +ot: List<&2, Nat>, +k: Nat, +heq: {SV.eq(SV.nth(SV.owners(sk), k), c) == True{} : Bool}, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == Con{e, t} : List<&2, E.QExpr>}, +ho: {OW.ndrop(k, SV.owners(sk)) == Con{o, ot} : List<&2, Nat>}, +hlt: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, hi: CW.CWInv(sk, R, D, c, bp0, k, st), +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}, ih: @st2: PA.CW -> CW.CWInv(sk, R, D, c, bp0, 1n+k, st2) -> CWRes2(sk, cls, R, D, c, bp0, 1n+k, ot, st2, DPS.cwalk2(t, SV.owners(sk), c, 1n+k, st2, sk, F0, cx, W)))
  -> CWRes2(sk, cls, R, D, c, bp0, k, Con{o, ot}, st, DPS.cwalk2(t, SV.owners(sk), c, 1n+k, DPS.cw2.res(k, e, st, sk, c, F0, cx, W), sk, F0, cx, W)):
  match st:
    case PA.CW{+rows, +B, +bp, +ds, +us}:
      cw2_ok.k(EP.isnil(EP.resp(EL.resid(rows, e))), sk, cls, R, D, c, bp0, F0, cx, hF0, hcx, W, hw, e, t, o, ot, k, rows, B, bp, ds, us, {==}, heq, hq, ho, hlt, hi, hcov, hwf, ih)

def cw2_ok.o(b: Bool, +sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +hF0: {F0 == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n) : List<&2, DR.Fact>}, +hcx: {cx == SV.ctx(sk, R, c) : List<&2, E.QExpr>}, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, SV.kept_before(sk, R, c)), cx, DCF.tv(sk), W), +e: E.QExpr, +t: List<&2, E.QExpr>, +o: Nat, +ot: List<&2, Nat>, +k: Nat, +st: PA.CW, +eb: {SV.eq(SV.nth(SV.owners(sk), k), c) == b : Bool}, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == Con{e, t} : List<&2, E.QExpr>}, +ho: {OW.ndrop(k, SV.owners(sk)) == Con{o, ot} : List<&2, Nat>},
  +hlt: {SV.lt(k, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +hi: CW.CWInv(sk, R, D, c, bp0, k, st), +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}, ih: @st2: PA.CW -> CW.CWInv(sk, R, D, c, bp0, 1n+k, st2) -> CWRes2(sk, cls, R, D, c, bp0, 1n+k, ot, st2, DPS.cwalk2(t, SV.owners(sk), c, 1n+k, st2, sk, F0, cx, W))) -> CWRes2(sk, cls, R, D, c, bp0, k, Con{o, ot}, st, DPS.cwalk2(Con{e, t}, SV.owners(sk), c, k, st, sk, F0, cx, W)):
  match b:
    case True{}:
      %Equal.sym(Bool, SV.eq(SV.nth(SV.owners(sk), k), c), True{}, eb) : CWRes2(sk, cls, R, D, c, bp0, k, Con{o, ot}, st, DPS.cwalk2(t, SV.owners(sk), c, 1n+k, DPS.cw2.at(_, k, e, st, sk, c, F0, cx, W), sk, F0, cx, W))
      cw2_ok.s(st, sk, cls, R, D, c, bp0, F0, cx, hF0, hcx, W, hw, e, t, o, ot, k, eb, hq, ho, hlt, hi, hcov, hwf, ih)
    case False{}:
      %Equal.sym(Bool, SV.eq(SV.nth(SV.owners(sk), k), c), False{}, eb) : CWRes2(sk, cls, R, D, c, bp0, k, Con{o, ot}, st, DPS.cwalk2(t, SV.owners(sk), c, 1n+k, DPS.cw2.at(_, k, e, st, sk, c, F0, cx, W), sk, F0, cx, W))
      res2_skip(sk, cls, R, D, c, bp0, k, o, ot, st, DPS.cwalk2(t, SV.owners(sk), c, 1n+k, st, sk, F0, cx, W), (%OW.nth_of(SV.owners(sk), k, o, ot, ho) : {SV.eq(_, c) == False{} : Bool}
        eb), hi, ih(st, CW.inv_skip(sk, R, D, c, bp0, k, st, hi, eb, hlt)))

# the walk from position k
def cw2_ok(es: List<&2, E.QExpr>, own_k: List<&2, Nat>, +sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +bp0: List<&2, Nat>, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +hF0: {F0 == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n) : List<&2, DR.Fact>}, +hcx: {cx == SV.ctx(sk, R, c) : List<&2, E.QExpr>}, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, SV.kept_before(sk, R, c)), cx, DCF.tv(sk), W), +k: Nat, +st: PA.CW, +hq: {OW.qdrop(k, SK.Sketch.eqs(sk)) == es : List<&2, E.QExpr>}, +ho: {OW.ndrop(k, SV.owners(sk)) == own_k : List<&2, Nat>}, +hl: {SV.len(own_k) == SV.neqs(es) : Nat},
  +hk: {Nat.add(k, SV.neqs(es)) == SV.neqs(SK.Sketch.eqs(sk)) : Nat}, +hi: CW.CWInv(sk, R, D, c, bp0, k, st), +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> CWRes2(sk, cls, R, D, c, bp0, k, own_k, st, DPS.cwalk2(es, SV.owners(sk), c, k, st, sk, F0, cx, W)):
  match es own_k:
    case Nil{} Nil{}:
      ((Nil{}, ({==}, {==})), (Unit{}, ((%Equal.trans(Nat, k, Nat.add(k, 0n), SV.neqs(SK.Sketch.eqs(sk)), LN.add_zero(k), hk) : CW.CWInv(sk, R, D, c, bp0, _, st)
        hi), h => h)))
    case Nil{} Con{+o, +ot}:
      absurd(CWRes2(sk, cls, R, D, c, bp0, k, Con{o, ot}, st, st), CW.len_nc(o, ot, hl))
    case Con{+e, +t} Nil{}:
      absurd(CWRes2(sk, cls, R, D, c, bp0, k, Nil{}, st, DPS.cwalk2(Con{e, t}, SV.owners(sk), c, k, st, sk, F0, cx, W)), CW.len_cn(e, t, hl))
    case Con{+e, +t} Con{+o, +ot}:
      cw2_ok.o(SV.eq(SV.nth(SV.owners(sk), k), c), sk, cls, R, D, c, bp0, F0, cx, hF0, hcx, W, hw, e, t, o, ot, k, st, {==}, hq, ho, SP.lt_qdrop(SK.Sketch.eqs(sk), k, e, t, hq), hi, hcov, hwf,
        st2 => h2 => cw2_ok(t, ot, sk, cls, R, D, c, bp0, F0, cx, hF0, hcx, W, hw, 1n+k, st2, OW.qdrop_step(k, SK.Sketch.eqs(sk), e, t, hq), OW.ndrop_step(k, SV.owners(sk), o, ot, ho), LN.succ_inj(SV.len(ot), SV.neqs(t), hl),
          Equal.trans(Nat, 1n+Nat.add(k, SV.neqs(t)), Nat.add(k, 1n+SV.neqs(t)), SV.neqs(SK.Sketch.eqs(sk)), LN.add_succ(k, SV.neqs(t)), hk), h2, hcov, hwf))

# The walk's end
# --------------


def cw2_final.r2(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +hF0: {F0 == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n) : List<&2, DR.Fact>}, +hcx: {cx == SV.ctx(sk, R, c) : List<&2, E.QExpr>}, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, SV.kept_before(sk, R, c)), cx, DCF.tv(sk), W), +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, dr: DH.drops_ok.go(sk, cls, R, D, c, SV.drops(CW.cw.ds(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W))), SV.owners(sk), 0n), +fr: CW.CWInv(sk, R, D, c, bp, SV.neqs(SK.Sketch.eqs(sk)), DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W)), nt: NDT(sk, cls, R, D, c, SV.drops(CW.cw.ds(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W))), Nil{}, CW.cw.ds(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W)))) -> DH.DropsOk(sk, cls, R, D, c, SV.drops(CW.cw.ds(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W)))) & (DH.DropsNd(sk, cls, R, D, c, CW.cw.ds(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W))) & CW.CWInv(sk, R, D, c, bp, SV.neqs(SK.Sketch.eqs(sk)), DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W))):
  +hb = CW.inv_b(sk, R, D, c, bp, SV.neqs(SK.Sketch.eqs(sk)), DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W), fr)
  ((LI.band_i(SV.distinct(SV.drops(CW.cw.ds(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W)))), SV.below(SV.drops(CW.cw.ds(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W))), SV.neqs(SK.Sketch.eqs(sk))), CW.cwb_ddist(sk, c, SV.neqs(SK.Sketch.eqs(sk)), CW.cw.rows(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W)), CW.cw.B(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W)), CW.cw.ds(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W)), CW.cw.us(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W)), hb),
      CW.cwb_dbelow(sk, c, SV.neqs(SK.Sketch.eqs(sk)), CW.cw.rows(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W)), CW.cw.B(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W)), CW.cw.ds(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W)), CW.cw.us(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W)), hb)), dr),
   (nt(Unit{}), fr))

def cw2_final.r(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +hF0: {F0 == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n) : List<&2, DR.Fact>}, +hcx: {cx == SV.ctx(sk, R, c) : List<&2, E.QExpr>}, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, SV.kept_before(sk, R, c)), cx, DCF.tv(sk), W), +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, r: CWRes2(sk, cls, R, D, c, bp, 0n, SV.owners(sk), PA.CW{rows, B, bp, Nil{}, Nil{}}, DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W))) -> DH.DropsOk(sk, cls, R, D, c, SV.drops(CW.cw.ds(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W)))) & (DH.DropsNd(sk, cls, R, D, c, CW.cw.ds(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W))) & CW.CWInv(sk, R, D, c, bp, SV.neqs(SK.Sketch.eqs(sk)), DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W))):
  (xr, q) = r
  (dr, q2) = q
  (fr, nt) = q2
  cw2_final.r2(sk, cls, R, D, c, F0, cx, hF0, hcx, W, hw, rows, B, bp, dr, fr, nt)

# the walk's end: the extended DropsOk and DropsNd for its drops, and the
# invariant at the end
def cw2_final(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +hF0: {F0 == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, R, c), sk, cls, True{}, 0n) : List<&2, DR.Fact>}, +hcx: {cx == SV.ctx(sk, R, c) : List<&2, E.QExpr>}, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, SV.kept_before(sk, R, c)), cx, DCF.tv(sk), W), +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hB: {B == SV.presolved(sk, R, D, c) : List<&2, E.QExpr>}, hp: {B == SV.picked(SK.Sketch.eqs(sk), bp) : List<&2, E.QExpr>}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> DH.DropsOk(sk, cls, R, D, c, SV.drops(CW.cw.ds(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W)))) & (DH.DropsNd(sk, cls, R, D, c, CW.cw.ds(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W))) & CW.CWInv(sk, R, D, c, bp, SV.neqs(SK.Sketch.eqs(sk)), DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W))):
  cw2_final.r(sk, cls, R, D, c, F0, cx, hF0, hcx, W, hw, rows, B, bp, cw2_ok(SK.Sketch.eqs(sk), SV.owners(sk), sk, cls, R, D, c, bp, F0, cx, hF0, hcx, W, hw, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, {==}, {==}, OW.len_owners(sk), {==}, CW.cw_start(sk, R, D, c, rows, B, bp, hr, hl, hB, hp), hcov, hwf))
