# sk-13b (PLAN-sk13b.md v2): the direction layer's spec (spec/dir.bend,
# its facts in spec/solve.bend, the extended Honest in spec/_draft13b.bend)
# and its proofs, kept checking until the switch, when this file is
# retired.
# - Its functions run on sketch 8's shape (seg 10 = P0 -> P1, seg 11 =
#   P1 -> P2; #0 Parallel, #1 Perpendicular), each checked by {==}.
# - lib/dirpf.bend (B1), imported so the gate checks it: the calculus is
#   sound in every ordered field (DP.sound), and direction statements are
#   right for their kinds (DP.dstat_ok).
# - lib/kspacepf.bend (B2): K's membership decided exactly (KP.ks_der_ok,
#   KP.ks_out), its invariant kept (KP.ks_add_inv).
# - lib/seppf.bend (B3): a tagged identity a + t b = c + t d, none of them
#   mentioning t, separates into a = c and b = d (SP.sep).
# - lib/hspacepf.bend (B3): a hull's membership decided exactly
#   (HP.hs_der_ok, HP.hs_out), its invariant kept (HP.hs_add_inv).
# - lib/spanpf.bend (B3): spans, decided exactly both ways (SN.in_of_zero,
#   SN.zero_of_in), grown by appending, closed under combination.
# - lib/pairpf.bend (B3): the pair test, sound (PP.ptest_ok) and complete
#   (PP.ptest_some_b, PP.ptest_some_a): the label and frame tests' core.
# - lib/labpf.bend (B3): a product of rotations is the rotation by the
#   product (LP.gmul_comp), and the hull label test is sound (LP.hs_lab_ok)
#   and complete (LP.hs_lab_some), and so is the frame test against K
#   (LP.ks_lab_ok, LP.ks_lab_some).
# - lib/indsetpf.bend (B3): forms inserted in turn, each with a nonzero
#   residual, combine into the span only with every coefficient 0
#   (IP.indset_ok): the complex-line check's core.
# - The closure (lib/dclose.bend, B3) and its soundness so far: the open
#   test (lib/dcopenpf.bend), VD, a reusable Data form of validity
#   (lib/dcvd.bend), reusable span invariants (lib/dcinvpf.bend), forms
#   below t (lib/dcbelowpf.bend), root generators and rebuilt hulls
#   (lib/dcgenpf.bend), member derivations (lib/dcderpf.bend), merges
#   (lib/dcmergepf.bend), new K facts (lib/dcclxpf.bend), nonzero
#   labels (lib/labnzpf.bend), collapsed sets (lib/dcreppf.bend,
#   lib/dctiedpf.bend), new links (lib/dclinkpf.bend), and the whole run
#   (lib/dcroundpf.bend: DRP.dclose_ok, every result keeps the invariant).
# - The closure theorem (lib/dcclosepf.bend, B3): at the closure's
#   fixpoint every valid derivation's conclusion is represented
#   (CCF.dclose_closed), with its rules in lib/dcreprpf.bend,
#   lib/dcturnpf.bend, lib/dcpushpf.bend, lib/dcturncpf.bend,
#   lib/dclopf.bend and lib/dcftiepf.bend. Its negative answers decide
#   NotDirDerivable (lib/dcdecpf.bend, DEC.not_dir): a fixpoint whose sets
#   hold neither the equation nor its direction statement (DC.holds).
#   Its positive answers are derivations (lib/dcholdpf.bend, HLD.hold_ok:
#   DC.hold.der is valid and proves the equation), and an explosion
#   derives every equation (lib/dcexplpf.bend, EXP.expl_ok).
# - The closure stops (lib/dctermpf.bend, TRM.dclose_term): with
#   DC.dfuel's fuel it ends at a fixpoint or an explosion, since every
#   other round takes a measure down: K's pivots among the bases'
#   monomials (lib/dcbasepf.bend, lib/dckslpf.bend, lib/dcgspanpf.bend,
#   lib/dcclprogpf.bend), the roots and the link slots (lib/dcslotpf.bend).
# - The refutation decision (lib/dref.bend, lib/drefpf.bend): whatever
#   it returns is a refutation (DRF.dref_sound), and at a fixpoint it
#   returns none only when there is none (DRF.dref_complete).
# - Moving a derivation to more facts (lib/dmappf.bend, B4.1): with more
#   constraints, c has every direction refutation it has with fewer
#   (DMP.nodir_mono), so no refutation with more means none with fewer.
# - The refutation decision at the sketch's level (lib/dbridgepf.bend,
#   B4.2): LRefOk over c with cs's facts, sides and kinds is RefOk, both
#   ways (BRG.lref_of, BRG.nodir_of), and the closure's bound tv holds for
#   a covered, well-formed sketch (BRG.zb_tv, BRG.fb_rf).
# - Refutations of both kinds and the generalized deletion filter
#   (lib/dconflict.bend, lib/dconflictpf.bend, B4.3): the filter's support
#   with its nd is the extended ConflictOk (DCP.conflict2_ok).
# - The walk with direction drops (lib/dpass.bend cwalk2, lib/dcwpf.bend,
#   B4.4): its drops are the extended DropsOk, each recording its reason,
#   which is its witness (DropsNd), and sk-13a's walk invariant holds at
#   its end (DCW.cw2_final). Its closure calls start from a state kept across
#   calls (B4.8), valid for facts the kept constraints' facts extend
#   (DWM.WInv).
# - The pass with the direction layer is honest (lib/dpass.bend classes2,
#   lib/dpasspf.bend, B4.5): the extended Honest of spec/_draft13b.bend
#   holds of its classes (DPP.pass2_honest).
# - The closure made fast (B4.8 B): lib/dclose.bend's dclose decides on
#   lean residuals (lib/lres.bend, the full ones' polynomials by
#   lib/lrespf.bend), stops each check at its first item and keeps K
#   squared's lean rows across rounds, and returns exactly what the run as
#   designed (DC.dclose_ref) returns (lib/dfastpf.bend, DFP.dclose_eq).
# - The restated laws' content, over any honest classification, as
#   statements only: each stmt_ def is filled from a False == True
#   hypothesis, so nothing about the laws is proven here. Their
#   solver-level texts are tools/drafts/roadmap13b.draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/_draft13b.bend as DH
import ../spec/dir.bend as DR
import ../lib/dirpf.bend as DP
import ../lib/kspace.bend as KS
import ../lib/kspacepf.bend as KP
import ../lib/seppf.bend as SP
import ../lib/hspace.bend as HS
import ../lib/hspacepf.bend as HP
import ../lib/spanpf.bend as SN
import ../lib/pair.bend as PT
import ../lib/pairpf.bend as PP
import ../lib/lab.bend as LB
import ../lib/labpf.bend as LP
import ../lib/indset.bend as IS
import ../lib/indsetpf.bend as IP
import ../lib/dclose.bend as DC
import ../lib/dcopenpf.bend as OPF
import ../lib/dcvd.bend as VDF
import ../lib/dcinvpf.bend as IVF
import ../lib/dcgenpf.bend as GNF
import ../lib/dcmergepf.bend as MGF
import ../lib/dcclxpf.bend as CXF
import ../lib/labnzpf.bend as NZF
import ../lib/dcroundpf.bend as DRP
import ../lib/elim.bend as EL
import ../lib/elimpf.bend as EP
import ../spec/solve.bend as SS
import ../lib/labalgpf.bend as LAF
import ../lib/dcsetpf.bend as STF
import ../lib/dcnodepf.bend as NDF
import ../lib/lspanpf.bend as LSF
import ../lib/dcfixpf.bend as FXF
import ../lib/dclinepf.bend as CLF
import ../lib/dcreadpf.bend as RDF
import ../lib/dcshapepf.bend as SHF
import ../lib/dcreppf.bend as REPF
import ../lib/dcreprpf.bend as RRF
import ../lib/dcclosepf.bend as CCF
import ../lib/dcdecpf.bend as DEC
import ../lib/dcholdpf.bend as HLD
import ../lib/dcexplpf.bend as EXP
import ../lib/dctermpf.bend as TRM
import ../lib/dref.bend as DFX
import ../lib/drefpf.bend as DRF
import ../lib/dmappf.bend as DMP
import ../lib/dconflict.bend as DCF
import ../lib/dbridgepf.bend as BRG
import ../lib/dconflictpf.bend as DCP
import ../lib/dpass.bend as DPS
import ../lib/cwpf.bend as CWP
import ../lib/dcwpf.bend as DCW
import ../lib/dpasspf.bend as DPP
import ../lib/passpf.bend as PPF
import ../lib/solve.bend as SOL
import ../lib/wfdec.bend as WFD
import ../lib/pass.bend as PAS
import ../lib/dfastpf.bend as DFP
import ../lib/dwarmpf.bend as DWM

# The functions on an example
# ---------------------------

def es() -> List<&2, SK.Ent>:
  [SK.Ent{0n, False{}, SK.GPoint{0n, 1n}}, SK.Ent{1n, False{}, SK.GPoint{2n, 3n}}, SK.Ent{2n, False{}, SK.GPoint{4n, 5n}}, SK.Ent{10n, False{}, SK.GSeg{0n, 1n}}, SK.Ent{11n, False{}, SK.GSeg{1n, 2n}}]

def sk() -> SK.Sketch:
  SK.Sketch{[SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}], es(), [SK.Rec{0n, False{}, SK.Parallel{10n, 11n}}, SK.Rec{1n, False{}, SK.Perpendicular{10n, 11n}}]}

# the refutation's facts: #1 with support #0
def fs() -> List<&2, DR.Fact>:
  SS.rfacts(sk(), [1n, 0n])

def dre() -> DR.Der:
  DR.DLine{DR.DPPrem{0n}, DR.DPPrem{1n}, True{}}

def dim() -> DR.Der:
  DR.DLine{DR.DPPrem{0n}, DR.DPPrem{1n}, False{}}

# the facts are #0's and #1's equations, in sketch order, nd none, with
# their direction statements
def t_facts() -> {fs() == [DR.Fact{SK.VE.cross(DR.zseg(es(), 10n), DR.zseg(es(), 11n)), Nil{}, Some{DR.DStat{10n, DR.zseg(es(), 11n), DR.qo()}}}, DR.Fact{SK.VE.dot(DR.zseg(es(), 10n), DR.zseg(es(), 11n)), Nil{}, Some{DR.DStat{10n, DR.imul(DR.zseg(es(), 11n)), DR.qo()}}}] : List<&2, DR.Fact>}:
  {==}

# complex line at seg 10 gives K(Re z_11) and K(Im z_11), needing seg 10
def t_concl() -> {DR.concl(es(), fs(), dre()) == DR.JK{SK.VE.x(DR.zseg(es(), 11n))} : DR.Jd}:
  {==}

def t_concl_im() -> {DR.concl(es(), fs(), dim()) == DR.JK{SK.VE.y(DR.zseg(es(), 11n))} : DR.Jd}:
  {==}

def t_nd() -> {DR.nd(es(), fs(), dre()) == [10n] : List<&2, Nat>}:
  {==}

# the derived collapse of seg 11 needs seg 11 and seg 10 (10 twice: one
# from each part)
def t_refnd() -> {DR.ref.nd(es(), fs(), DR.RColl{dre(), dim(), 11n}) == [11n, 10n, 10n] : List<&2, Nat>}:
  {==}

# the context of #1: both equations
def t_ctx() -> {SS.ctx(sk(), Nil{}, 1n) == [SK.VE.cross(DR.zseg(es(), 10n), DR.zseg(es(), 11n)), SK.VE.dot(DR.zseg(es(), 10n), DR.zseg(es(), 11n))] : List<&2, E.QExpr>}:
  {==}

# an Angle with constant rotation is a statement; one with a variable is
# not
def t_angle_var() -> {DR.dstat(es(), SK.Angle{10n, False{}, 11n, False{}, E.QVar{0n}, E.QCst{DR.qz()}}) == None{} : Maybe<&2, DR.DStat>}:
  {==}

def t_onl() -> {DR.dstat(es(), SK.OnLine{2n, 10n}) == Some{DR.DStat{10n, SK.VE.sub(SK.Pt.ve(SK.Pt{4n, 5n}), SK.Pt.ve(SK.Pt{0n, 1n})), DR.qo()}} : Maybe<&2, DR.DStat>}:
  {==}

# the nd lists the laws read
def cmb() -> SS.Why:
  SS.WLin{Nil{}}

def cls() -> List<&2, SS.Class>:
  [SS.Kept{[SS.Drop{3n, [10n, 11n], cmb()}]}, SS.Conflict{[0n], [10n, 11n]}, SS.Amber{[SS.Drop{5n, [12n], cmb()}], Nil{}}]

def t_live() -> {SS.live_nd(cls()) == [10n, 11n, 12n] : List<&2, Nat>}:
  {==}

def t_amber() -> {SS.amber_nd(cls()) == [12n] : List<&2, Nat>}:
  {==}

def t_cnd() -> {SS.conflict_nd(cls(), 1n) == [10n, 11n] : List<&2, Nat>}:
  {==}

def t_dnd() -> {SS.dnd_at(cls(), 5n) == [12n] : List<&2, Nat>}:
  {==}

def t_ndh() -> {DR.ndh(es(), [10n]) == E.QMul{DR.norm2(es(), 10n), E.QCst{DR.qo()}} : E.QExpr}:
  {==}

# The restated laws, as statements only
# -------------------------------------

def stmt_pick(b: Bool, P: Type) -> Type:
  match b:
    case False{}:
      Unit
    case True{}:
      P

def stmt_absurd(P: Type, e: {False{} == True{} : Bool}) -> P:
  %e : stmt_pick(_, P)
  Unit{}

# solve_drop: wherever the solved equations hold and drop j's nd segments
# have nonzero length, equation j holds
def stmt_drop(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), +n: Nat, cov: {BX.Sketch.within(sk, n) == True{} : Bool}, +cls: List<&2, SS.Class>, h: DH.Honest(sk, cls), +x: M.Vec(~F), hz: SK.Zeros(~F, x, SS.solved(sk, SS.reds(cls), SS.dropped(cls))), +j: Nat, hj: {SS.mem(j, SS.dropped(cls)) == True{} : Bool}, hl: DR.Longs(~F, x, SS.ents(sk), SS.dnd_at(cls, j)), bot: {False{} == True{} : Bool}) -> SK.Zeros(~F, x, [SS.eqat(SK.Sketch.eqs(sk), j)]):
  stmt_absurd(SK.Zeros(~F, x, [SS.eqat(SK.Sketch.eqs(sk), j)]), bot)

# solve_amber: deleting every amber constraint changes no solution at
# which the amber drops' nd segments have nonzero length
def stmt_amber(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), +n: Nat, cov: {BX.Sketch.within(sk, n) == True{} : Bool}, +cls: List<&2, SS.Class>, h: DH.Honest(sk, cls), +x: M.Vec(~F), m: SK.Sketch.means(~F, x, SS.mark(SS.cat(SS.reds(cls), SS.ambers(cls)), sk)), hl: DR.Longs(~F, x, SS.ents(sk), SS.amber_nd(cls)), bot: {False{} == True{} : Bool}) -> SK.Sketch.means(~F, x, SS.mark(SS.reds(cls), sk)):
  stmt_absurd(SK.Sketch.means(~F, x, SS.mark(SS.reds(cls), sk)), bot)

# solve_conflict: a conflicting constraint and its support cannot all hold
# where its nd segments have nonzero length
def stmt_conflict(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), +n: Nat, cov: {BX.Sketch.within(sk, n) == True{} : Bool}, +cls: List<&2, SS.Class>, h: DH.Honest(sk, cls), +c: Nat, hc: {SS.is_conflict(SS.class_at(cls, c)) == True{} : Bool}, +x: M.Vec(~F), m: SK.Sketch.means(~F, x, SS.only(Con{c, SS.support(cls, c)}, sk)), hl: DR.Longs(~F, x, SS.ents(sk), SS.conflict_nd(cls, c)), bot: {False{} == True{} : Bool}) -> Empty:
  stmt_absurd(Empty, bot)

# honest_unique, unchanged in statement, over the extended Honest
def stmt_honest_unique(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +c1: List<&2, SS.Class>, h1: DH.Honest(sk, c1), +c2: List<&2, SS.Class>, h2: DH.Honest(sk, c2), +c: Nat, +j: Nat, bot: {False{} == True{} : Bool}) -> M.Both({SS.kind(SS.class_at(c1, c)) == SS.kind(SS.class_at(c2, c)) : Nat}, {SS.mem(j, SS.dropped(c1)) == SS.mem(j, SS.dropped(c2)) : Bool}):
  stmt_absurd(M.Both({SS.kind(SS.class_at(c1, c)) == SS.kind(SS.class_at(c2, c)) : Nat}, {SS.mem(j, SS.dropped(c1)) == SS.mem(j, SS.dropped(c2)) : Bool}), bot)

# solve_complete's and solve_refused's new hypothesis: at x, every
# segment in the nd of a drop of a Kept or Amber constraint has positive
# squared length (a Strict side, as the verdict checks it over the box)
def stmt_strict_nd(~F: O.OField, +sk: SK.Sketch, +cls: List<&2, SS.Class>, +x: M.Vec(~F), +pins: List<&2, Nat>, hn: SS.Strict(~F, x, DR.ndsides(SS.ents(sk), SS.live_nd(cls)), pins), bot: {False{} == True{} : Bool}) -> Unit:
  Unit{}

# B1's two results, as their types (the gate checks lib/dirpf.bend through
# this import)
def b1_sound(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +hf: DP.AllFacts(~F, env, es, fs), d: DR.Der, hv: DR.Valid(es, fs, ctx, d), +hl: DR.Longs(~F, env, es, DR.nd(es, fs, d))) -> DP.Holds(~F, env, es, DR.concl(es, fs, d)):
  DP.sound(~F, env, es, fs, ctx, hf, d, hv, hl)

def b1_stat(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, k: SK.Constraint, h: SK.Zeros(~F, env, SK.Constraint.eqs(es, k))) -> DP.StatHolds(~F, env, es, DR.dstat(es, k)):
  DP.dstat_ok(~F, env, es, k, h)

# B2's results, as their types
def b2_in(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, k: KS.KS, +e: E.QExpr, h: KP.KInv(es, fs, ctx, k), hz: {KS.ks.inb(k, e) == True{} : Bool})
  -> (DR.Valid(es, fs, ctx, KS.ks.der(es, fs, k, e)) & DR.IsK(DR.concl(es, fs, KS.ks.der(es, fs, k, e)))) & DR.Same(DR.Jd.e(DR.concl(es, fs, KS.ks.der(es, fs, k, e))), e):
  KP.ks_der_ok(es, fs, ctx, k, e, h, hz)

def b2_add(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, k: KS.KS, +d: DR.Der, h: KP.KInv(es, fs, ctx, k), hd: DR.Valid(es, fs, ctx, d) & DR.IsK(DR.concl(es, fs, d))) -> KP.KInv(es, fs, ctx, KS.ks.add(es, fs, k, d)):
  KP.ks_add_inv(es, fs, ctx, k, d, h, hd)

# B3's separation lemma, as its type
def b3_sep(+a: E.QExpr, +b: E.QExpr, +c: E.QExpr, +d: E.QExpr, +t: Nat,
  +ha: {SP.vbelow(a, t) == True{} : Bool}, +hb: {SP.vbelow(b, t) == True{} : Bool}, +hc: {SP.vbelow(c, t) == True{} : Bool}, +hd: {SP.vbelow(d, t) == True{} : Bool},
  h: SS.Ident(SP.tag(a, b, t), SP.tag(c, d, t))) -> SS.Ident(a, c) & SS.Ident(b, d):
  SP.sep(a, b, c, d, t, ha, hb, hc, hd, h)

# B3's hull membership, as its type
def b3_hull(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, h: HS.HS, +y: SK.VE, hi: HP.HInv(es, fs, ctx, r, t, h), hz: {HS.hs.inb(h, y, t) == True{} : Bool}, +hy: HP.VBelow(y, t), +hr: HP.VBelow(DR.zdir(es, r), t))
  -> ((DR.Valid(es, fs, ctx, HS.hs.der(es, fs, t, r, h, y)) & DR.IsP(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, y)))) & {DR.Jd.a(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, y))) == r : DR.Node}) & DR.SameV(DR.Jd.x(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, y))), y):
  HP.hs_der_ok(es, fs, ctx, r, t, h, y, hi, hz, hy, hr)

# B3's spans, as their types
def b3_span(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, +h: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SS.neqs(B) : Nat}, +hi: SN.InSpan(e, B)) -> {EP.isnil(EP.resp(EL.resid(rows, e))) == True{} : Bool}:
  SN.zero_of_in(B, rows, e, h, hl, hi)

# B3's pair test, as its types
def b3_pair_ok(+rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr, +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SS.neqs(B) : Nat}, +p0: PT.Pr,
  hp: {PT.ptest(rows, B, u, v) == Some{p0} : Maybe<&2, PT.Pr>}) -> SN.InSpan(PT.pcomb(p0, u, v), B):
  PP.ptest_ok(rows, B, u, v, hr, hl, p0, hp)

def b3_pair_some(+rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr, +a: S.Q, +bb: S.Q, +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SS.neqs(B) : Nat},
  hb: S.Q.eq(bb, S.Q{S.Z0{}, S.XH{}}) -> Empty, +hi: SN.InSpan(PT.pcomb(PT.Pr{a, bb}, u, v), B)) -> {PP.is_some(PT.ptest(rows, B, u, v)) == True{} : Bool}:
  PP.ptest_some_b(rows, B, u, v, a, bb, hr, hl, hb, hi)

def b3_comp(g: DR.Lab, h: DR.Lab, +x: SK.VE) -> DR.SameV(DR.gmul(g, DR.gmul(h, x)), DR.gmul(LB.lmul(g, h), x)):
  LP.gmul_comp(g, h, x)

def b3_lab_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, h: HS.HS, +z: SK.VE, +w: DR.Lab,
  hi: HP.HInv(es, fs, ctx, r, t, h), hw: {LB.hs.lab(es, fs, t, h, z) == Some{w} : Maybe<&2, DR.Lab>}) -> {HS.hs.inb(h, DR.gmul(w, z), t) == True{} : Bool}:
  LP.hs_lab_ok(es, fs, ctx, r, t, h, z, w, hi, hw)

def b3_lab_some(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, h: HS.HS, +z: SK.VE, hi: HP.HInv(es, fs, ctx, r, t, h),
  +a: S.Q, +bb: S.Q, hab: S.Q.eq(a, S.Q{S.Z0{}, S.XH{}}) -> S.Q.eq(bb, S.Q{S.Z0{}, S.XH{}}) -> Empty,
  +hin: SN.InSpan(HS.enc(DR.gmul(DR.Lab{a, bb}, z), t), HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t))) -> {LP.lis_some(LB.hs.lab(es, fs, t, h, z)) == True{} : Bool}:
  LP.hs_lab_some(es, fs, ctx, r, t, h, z, hi, a, bb, hab, hin)

def b3_klab_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, k: KS.KS, +z: SK.VE, +w: DR.Lab,
  hi: KP.KInv(es, fs, ctx, k), hw: {LB.ks.lab(es, fs, k, z) == Some{w} : Maybe<&2, DR.Lab>}) -> {KS.ks.inb(k, SK.VE.y(DR.gmul(w, z))) == True{} : Bool}:
  LP.ks_lab_ok(es, fs, ctx, k, z, w, hi, hw)

def b3_klab_some(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, k: KS.KS, +z: SK.VE, hi: KP.KInv(es, fs, ctx, k),
  +a: S.Q, +bb: S.Q, hab: S.Q.eq(a, S.Q{S.Z0{}, S.XH{}}) -> S.Q.eq(bb, S.Q{S.Z0{}, S.XH{}}) -> Empty,
  +hin: SN.InSpan(SK.VE.y(DR.gmul(DR.Lab{a, bb}, z)), KS.kexprs(es, fs, KS.ks.ds(k)))) -> {LP.lis_some(LB.ks.lab(es, fs, k, z)) == True{} : Bool}:
  LP.ks_lab_some(es, fs, ctx, k, z, hi, a, bb, hab, hin)

def b3_indset(vs: List<&2, E.QExpr>, +B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SS.neqs(B) : Nat},
  +hi: {IS.indset(vs, rows) == True{} : Bool}, ls: List<&2, S.Q>, +hin: SN.InSpan(SS.lin(ls, vs), B)) -> {IS.allz(ls, vs) == True{} : Bool}:
  IP.indset_ok(vs, B, rows, hr, hl, hi, ls, hin)

def b3_open(+es: List<&2, SK.Ent>, +ctx: List<&2, E.QExpr>, n: DR.Node, h: {DC.isopen(es, OPF.cspan(ctx), n) == True{} : Bool}) -> DR.Open(es, ctx, n):
  OPF.open_of(es, ctx, n, h)

def b3_valid(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, d: DR.Der, h: VDF.VD(es, fs, ctx, d)) -> DR.Valid(es, fs, ctx, d):
  VDF.valid_of(es, fs, ctx, d, h)

def b3_rhull(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +r: DR.Node,
  hk: IVF.KInvD(es, fs, ctx, t, DC.Sk.k(s)), hms: GNF.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GNF.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> IVF.HInvD(es, fs, ctx, r, t, DC.rhull(es, fs, t, s, r)):
  GNF.rhull_inv(es, fs, ctx, t, s, r, hk, hms, hls, hz, hb)

def b3_merges(rs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, hro: MGF.AllOpenD(es, ctx, rs),
  +hk: IVF.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GNF.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GNF.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> MGF.OptMs(es, fs, ctx, t, DC.mgs(rs, es, fs, t, s)):
  MGF.mgs_ok(rs, es, fs, ctx, t, s, hro, hk, hms, hls, hz, hb)

def b3_lines(rs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, hro: MGF.AllOpenD(es, ctx, rs),
  +hk: IVF.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GNF.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GNF.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> CXF.OptK(es, fs, ctx, t, DC.clxs(rs, es, fs, t, s)):
  CXF.clxs_ok(rs, es, fs, ctx, t, s, hro, hk, hms, hls, hz, hb)

def b3_nz(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +z: SK.VE, +w: DR.Lab, hw: {LB.hs.lab(es, fs, t, h, z) == Some{w} : Maybe<&2, DR.Lab>}) -> NZF.Nz(w):
  NZF.hs_lab_nz(es, fs, t, h, z, w, hw)

def b3_close(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, fuel: Nat, +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> DRP.OutInv(es, fs, ctx, t, DC.dclose(es, fs, ctx, t, fuel)):
  DRP.dclose_ok(es, fs, ctx, t, fuel, hz, hb)

def b3_conj(w: DR.Lab, +y: SK.VE) -> VDF.SameVD(DR.gmul(DR.Lab.conj(w), DR.gmul(w, y)), DR.vlin(DC.lnorm(w), y, DR.qz(), y)):
  LAF.conj_w(w, y)

def b3_k2(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +r: DR.Node, +y: SK.VE,
  +hk: IVF.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GNF.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GNF.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: REPF.MsNz(DC.Sk.ms(s)), +hlsn: REPF.LsNz(DC.Sk.ls(s)),
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool},
  hre: {KS.ks.inb(DC.Sk.k(s), SK.VE.x(y)) == True{} : Bool}, him: {KS.ks.inb(DC.Sk.k(s), SK.VE.y(y)) == True{} : Bool})
  -> STF.InSt(es, fs, DC.Sk.k(s), NDF.rset(es, fs, t, s, r), y):
  NDF.k2_in(es, fs, t, DC.Sk.k(s), NDF.rset(es, fs, t, s, r), y, NDF.sok_root(es, fs, ctx, t, s, r, hk, hms, hls, hmsn, hlsn, hz, hb), STF.kri(es, fs, ctx, t, DC.Sk.k(s), hk), hre, him)

def b3_qspan(ws: List<&2, DR.Lab>, +w: DR.Lab, hq: {DC.qspan(ws, w) == True{} : Bool}, hp: {LSF.pairok(ws) == True{} : Bool}, nz: LSF.LNzs(ws)) -> LSF.LSp(LSF.lat0(ws), LSF.lat1(ws), w):
  LSF.qspan_ok(ws, w, hq, hp, nz)

def b3_fix(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, fuel: Nat, +s: DC.Sk, eo: {DC.dclose(es, fs, ctx, t, fuel) == DC.OFix{s} : DC.Out},
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}) -> FXF.FixOut(es, fs, ctx, t, DC.segids(es), DC.OFix{s}):
  FXF.fix_at(es, fs, ctx, t, fuel, s, eo, hz, hb)

def b3_cline(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +r: DR.Node,
  +hk: IVF.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GNF.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GNF.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: REPF.MsNz(DC.Sk.ms(s)), +hlsn: REPF.LsNz(DC.Sk.ls(s)),
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}, +hclx: {DC.clx(es, fs, t, s, r) == None{} : Maybe<&2, DR.Der>},
  +y: SK.VE, h1: STF.HIn(es, fs, r, DC.rhull(es, fs, t, s, r), y), +h2: STF.HIn(es, fs, r, DC.rhull(es, fs, t, s, r), DR.imul(y))) -> CLF.K2(es, fs, DC.Sk.k(s), y):
  CLF.cline(es, fs, ctx, t, s, r, hk, hms, hls, hmsn, hlsn, hz, hb, hclx, y, h1, h2)

def b3_mgF(sc: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, DC.Mem>, +e: {DC.mgF(sc, es, fs, k, ms) == None{} : Maybe<&2, List<&2, DC.Mem>>},
  +m: DC.Mem, n: Nat, +en: {SHF.mat(sc, n) == Some{m} : Maybe<&2, DC.Mem>}, +hne: {DC.node_eq(DC.Mem.r(m), DR.NFrame{}) == False{} : Bool})
  -> {LB.ks.lab(es, fs, k, DR.zdir(es, DC.Mem.a(m))) == None{} : Maybe<&2, DR.Lab>}:
  RDF.mgF_none(sc, es, fs, k, ms, e, m, n, en, hne)

def b3_closed(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, fuel: Nat, +s: DC.Sk, eo: {DC.dclose(es, fs, ctx, t, fuel) == DC.OFix{s} : DC.Out},
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}, d: DR.Der, hv: DR.Valid(es, fs, ctx, d)) -> RRF.Repr(es, fs, t, s, DR.concl(es, fs, d)):
  CCF.dclose_closed(es, fs, ctx, t, fuel, s, eo, hz, hb, d, hv)

def b3_not_dir(+sk: SK.Sketch, +cls: List<&2, SS.Class>, +red: List<&2, Nat>, +c: Nat, +dd: List<&2, Nat>, +i: Nat, +t: Nat, fuel: Nat, +s: DC.Sk,
  +eo: {DC.dclose(SS.ents(sk), SS.dfacts(sk, cls, red, c, dd, i), SS.ctx(sk, red, c), t, fuel) == DC.OFix{s} : DC.Out}, +hz: {DC.zb(SS.ents(sk), t) == True{} : Bool},
  +hb: {DC.fb(SS.dfacts(sk, cls, red, c, dd, i), t) == True{} : Bool},
  +hh: {DC.holds(SS.ents(sk), SS.dfacts(sk, cls, red, c, dd, i), t, s, SS.eqat(SK.Sketch.eqs(sk), i), SS.dstat_of(SS.ents(sk), SS.kind_at(sk, c))) == False{} : Bool})
  -> SS.NotDirDerivable(sk, cls, red, c, dd, i):
  DEC.not_dir(sk, cls, red, c, dd, i, t, fuel, s, eo, hz, hb, hh)

def b3_hold(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RRF.Hyp(es, fs, ctx, t, s), +e: E.QExpr, +m: Maybe<&2, DR.DStat>,
  hh: {DC.holds(es, fs, t, s, e, m) == True{} : Bool}, hb: {DC.fb.ds(m, t) == True{} : Bool})
  -> DR.Valid(es, fs, ctx, DC.hold.der(es, fs, t, s, e, m)) & SS.Proves(es, m, e, DR.concl(es, fs, DC.hold.der(es, fs, t, s, e, m))):
  HLD.hold_ok(es, fs, ctx, t, s, H, e, m, hh, hb)

def b3_expl(o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +m: Maybe<&2, DR.DStat>, +e: E.QExpr, ho: DRP.OutInv(es, fs, ctx, t, o),
  hx: {DC.is_expl(o) == True{} : Bool}) -> DR.Valid(es, fs, ctx, DC.expl.der(o, es, e)) & SS.Proves(es, m, e, DR.concl(es, fs, DC.expl.der(o, es, e))):
  EXP.expl_ok(o, es, fs, ctx, t, m, e, ho, hx)

def b3_term(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, eo: {DC.dclose(es, fs, ctx, t, DC.dfuel(es, fs)) == DC.OStep{s} : DC.Out},
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}) -> Empty:
  TRM.dclose_nostep(es, fs, ctx, t, s, eo, hz, hb)

def b3_dref_sound(o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ss: List<&2, SK.Side>, +as: List<&2, DFX.Ang>, h: DRP.OutInv(es, fs, ctx, t, o))
  -> DRF.OptR(es, fs, ctx, ss, as, DFX.dref(o, es, fs, ss, as)):
  DRF.dref_sound(o, es, fs, ctx, t, ss, as, h)

def b3_dref_complete(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +fuel: Nat, +s: DC.Sk, +ss: List<&2, SK.Side>, +as: List<&2, DFX.Ang>,
  +eo: {DC.dclose(es, fs, ctx, t, fuel) == DC.OFix{s} : DC.Out}, +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool},
  hn: {DFX.dref(DC.OFix{s}, es, fs, ss, as) == None{} : Maybe<&2, DR.DRef>}) -> DRF.NoLRef(es, fs, ctx, ss, as):
  DRF.dref_complete(es, fs, ctx, t, s, ss, as, DRF.hyp_of(es, fs, ctx, t, fuel, s, eo, hz, hb), hn)

# B4.1's monotonicity, as its type
def b4_nodir_mono(+sk: SK.Sketch, +c: Nat, +cs1: List<&2, Nat>, +cs2: List<&2, Nat>, +cx: List<&2, E.QExpr>, +hsub: {SS.sub(cs1, cs2) == True{} : Bool}, h: SS.NoDirRef(sk, c, cs2, cx)) -> SS.NoDirRef(sk, c, cs1, cx):
  DMP.nodir_mono(sk, c, cs1, cs2, cx, hsub, h)

# B4.2's bridge and coverage, as their types
def b4_lref_of(r: DR.DRef, +sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>, +cx: List<&2, E.QExpr>,
  h: DRF.LRefOk(SS.ents(sk), SS.rfacts(sk, Con{c, cs}), cx, SK.cats(SS.csides(sk, Con{c, cs}), SS.esides(sk)), DCF.angl(sk, Con{c, cs}), r)) -> SS.RefOk(sk, c, cs, cx, r):
  BRG.lref_of(r, sk, c, cs, cx, h)

def b4_nodir_of(+sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>, +cx: List<&2, E.QExpr>,
  h: DRF.NoLRef(SS.ents(sk), SS.rfacts(sk, Con{c, cs}), cx, SK.cats(SS.csides(sk, Con{c, cs}), SS.esides(sk)), DCF.angl(sk, Con{c, cs}))) -> SS.NoDirRef(sk, c, cs, cx):
  BRG.nodir_of(sk, c, cs, cx, h)

def b4_fb(+sk: SK.Sketch, +cs: List<&2, Nat>, +hcov: {BX.Sketch.within(sk, PAS.nvars(sk)) == True{} : Bool}, +hwf: {WFD.wf_dec(sk) == True{} : Bool})
  -> M.Both({DC.zb(SS.ents(sk), DCF.tv(sk)) == True{} : Bool}, {DC.fb(SS.rfacts(sk, cs), DCF.tv(sk)) == True{} : Bool}):
  (BRG.zb_tv(sk, hcov), BRG.fb_rf(sk, cs, hcov, hwf))

# B4.3's conflict, as its type
def b4_conflict(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat, +cand: List<&2, Nat>,
  +hc: {SS.band(SS.distinct(cand), SS.band(SS.below(cand, c), SS.band(SS.all_driving(sk, cand), SS.none_in(cand, red)))) == True{} : Bool},
  hr: {DCF.refutable2(sk, c, cand, SS.ctx(sk, red, c)) == True{} : Bool}, +hcov: {BX.Sketch.within(sk, PAS.nvars(sk)) == True{} : Bool}, +hwf: {WFD.wf_dec(sk) == True{} : Bool})
  -> DH.ConflictOk(sk, red, c, DCF.support2(sk, c, SS.ctx(sk, red, c), cand), DCF.cnd(sk, c, DCF.support2(sk, c, SS.ctx(sk, red, c), cand), SS.ctx(sk, red, c))):
  DCP.conflict2_ok(sk, red, c, cand, hc, hr, hcov, hwf)

# B4.4's walk, as its type
def b4_walk(+sk: SK.Sketch, +cls: List<&2, SS.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>,
  +hF0: {F0 == SS.facts.go(SK.Sketch.eqs(sk), SS.owners(sk), SS.kept_before(sk, R, c), sk, cls, True{}, 0n) : List<&2, DR.Fact>}, +hcx: {cx == SS.ctx(sk, R, c) : List<&2, E.QExpr>},
  +W: DC.WK, +hw: DWM.WInv(SS.ents(sk), SS.rfacts(sk, SS.kept_before(sk, R, c)), cx, DCF.tv(sk), W), +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, hl: {EL.rlen(rows) == SS.neqs(B) : Nat},
  hB: {B == SS.presolved(sk, R, D, c) : List<&2, E.QExpr>}, hp: {B == SS.picked(SK.Sketch.eqs(sk), bp) : List<&2, E.QExpr>},
  +hb0: {SS.below(bp, SS.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +ha0: {PPF.allpre(bp, SS.owners(sk), R, D, c) == True{} : Bool},
  +hcov: {BX.Sketch.within(sk, PAS.nvars(sk)) == True{} : Bool}, +hwf: {WFD.wf_dec(sk) == True{} : Bool})
  -> DH.DropsOk(sk, cls, R, D, c, SS.drops(CWP.cw.ds(DPS.cwalk2(SK.Sketch.eqs(sk), SS.owners(sk), c, 0n, PAS.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W)))) & (DH.DropsNd(sk, cls, R, D, c, CWP.cw.ds(DPS.cwalk2(SK.Sketch.eqs(sk), SS.owners(sk), c, 0n, PAS.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W))) & CWP.CWInv(sk, R, D, c, bp, SS.neqs(SK.Sketch.eqs(sk)), DPS.cwalk2(SK.Sketch.eqs(sk), SS.owners(sk), c, 0n, PAS.CW{rows, B, bp, Nil{}, Nil{}}, sk, F0, cx, W))):
  DCW.cw2_final(sk, cls, R, D, c, F0, cx, hF0, hcx, W, hw, rows, B, bp, hr, hl, hB, hp, hb0, ha0, hcov, hwf)

# B4.5: the pass with the direction layer is honest
def b4_honest(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SOL.nvars(sk)) == True{} : Bool}) -> DH.Honest(sk, DPS.classes2(sk)):
  DPP.pass2_honest(sk, w, cov)

# B4.8: the fast closure is the closure as designed
def b4_fast(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, fuel: Nat) -> {DC.dclose(es, fs, ctx, t, fuel) == DC.dclose_ref(es, fs, ctx, t, fuel) : DC.Out}:
  DFP.dclose_eq(es, fs, ctx, t, fuel)
