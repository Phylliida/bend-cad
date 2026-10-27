# sk-13b B0 (PLAN-sk13b.md v2): the draft spec (spec/dir.bend,
# spec/_draft13b.bend) kept checking until it replaces spec/solve.bend at
# the switch (B4), when this file is retired.
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
#   (lib/dcmergepf.bend), new K facts (lib/dcclxpf.bend), and nonzero
#   labels (lib/labnzpf.bend).
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
import ../spec/_draft13b.bend as SV
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
import ../lib/elim.bend as EL
import ../lib/elimpf.bend as EP
import ../spec/solve.bend as SS

# The functions on an example
# ---------------------------

def es() -> List<&2, SK.Ent>:
  [SK.Ent{0n, False{}, SK.GPoint{0n, 1n}}, SK.Ent{1n, False{}, SK.GPoint{2n, 3n}}, SK.Ent{2n, False{}, SK.GPoint{4n, 5n}}, SK.Ent{10n, False{}, SK.GSeg{0n, 1n}}, SK.Ent{11n, False{}, SK.GSeg{1n, 2n}}]

def sk() -> SK.Sketch:
  SK.Sketch{[SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}], es(), [SK.Rec{0n, False{}, SK.Parallel{10n, 11n}}, SK.Rec{1n, False{}, SK.Perpendicular{10n, 11n}}]}

# the refutation's facts: #1 with support #0
def fs() -> List<&2, DR.Fact>:
  SV.rfacts(sk(), [1n, 0n])

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
def t_ctx() -> {SV.ctx(sk(), Nil{}, 1n) == [SK.VE.cross(DR.zseg(es(), 10n), DR.zseg(es(), 11n)), SK.VE.dot(DR.zseg(es(), 10n), DR.zseg(es(), 11n))] : List<&2, E.QExpr>}:
  {==}

# an Angle with constant rotation is a statement; one with a variable is
# not
def t_angle_var() -> {DR.dstat(es(), SK.Angle{10n, False{}, 11n, False{}, E.QVar{0n}, E.QCst{DR.qz()}}) == None{} : Maybe<&2, DR.DStat>}:
  {==}

def t_onl() -> {DR.dstat(es(), SK.OnLine{2n, 10n}) == Some{DR.DStat{10n, SK.VE.sub(SK.Pt.ve(SK.Pt{4n, 5n}), SK.Pt.ve(SK.Pt{0n, 1n})), DR.qo()}} : Maybe<&2, DR.DStat>}:
  {==}

# the nd lists the laws read
def cmb() -> SV.Comb:
  SV.Comb{E.QCst{DR.qo()}, Nil{}}

def cls() -> List<&2, SV.Class>:
  [SV.Kept{[SV.Drop{3n, [10n, 11n], cmb()}]}, SV.Conflict{[0n], [10n, 11n]}, SV.Amber{[SV.Drop{5n, [12n], cmb()}], Nil{}}]

def t_live() -> {SV.live_nd(cls()) == [10n, 11n, 12n] : List<&2, Nat>}:
  {==}

def t_amber() -> {SV.amber_nd(cls()) == [12n] : List<&2, Nat>}:
  {==}

def t_cnd() -> {SV.conflict_nd(cls(), 1n) == [10n, 11n] : List<&2, Nat>}:
  {==}

def t_dnd() -> {SV.dnd_at(cls(), 5n) == [12n] : List<&2, Nat>}:
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
def stmt_drop(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), +n: Nat, cov: {BX.Sketch.within(sk, n) == True{} : Bool}, +cls: List<&2, SV.Class>, h: SV.Honest(sk, cls), +x: M.Vec(~F), hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +j: Nat, hj: {SV.mem(j, SV.dropped(cls)) == True{} : Bool}, hl: DR.Longs(~F, x, SV.ents(sk), SV.dnd_at(cls, j)), bot: {False{} == True{} : Bool}) -> SK.Zeros(~F, x, [SV.eqat(SK.Sketch.eqs(sk), j)]):
  stmt_absurd(SK.Zeros(~F, x, [SV.eqat(SK.Sketch.eqs(sk), j)]), bot)

# solve_amber: deleting every amber constraint changes no solution at
# which the amber drops' nd segments have nonzero length
def stmt_amber(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), +n: Nat, cov: {BX.Sketch.within(sk, n) == True{} : Bool}, +cls: List<&2, SV.Class>, h: SV.Honest(sk, cls), +x: M.Vec(~F), m: SK.Sketch.means(~F, x, SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk)), hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(cls)), bot: {False{} == True{} : Bool}) -> SK.Sketch.means(~F, x, SV.mark(SV.reds(cls), sk)):
  stmt_absurd(SK.Sketch.means(~F, x, SV.mark(SV.reds(cls), sk)), bot)

# solve_conflict: a conflicting constraint and its support cannot all hold
# where its nd segments have nonzero length
def stmt_conflict(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), +n: Nat, cov: {BX.Sketch.within(sk, n) == True{} : Bool}, +cls: List<&2, SV.Class>, h: SV.Honest(sk, cls), +c: Nat, hc: {SV.is_conflict(SV.class_at(cls, c)) == True{} : Bool}, +x: M.Vec(~F), m: SK.Sketch.means(~F, x, SV.only(Con{c, SV.support(cls, c)}, sk)), hl: DR.Longs(~F, x, SV.ents(sk), SV.conflict_nd(cls, c)), bot: {False{} == True{} : Bool}) -> Empty:
  stmt_absurd(Empty, bot)

# honest_unique, unchanged in statement, over the extended Honest
def stmt_honest_unique(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +c1: List<&2, SV.Class>, h1: SV.Honest(sk, c1), +c2: List<&2, SV.Class>, h2: SV.Honest(sk, c2), +c: Nat, +j: Nat, bot: {False{} == True{} : Bool}) -> M.Both({SV.kind(SV.class_at(c1, c)) == SV.kind(SV.class_at(c2, c)) : Nat}, {SV.mem(j, SV.dropped(c1)) == SV.mem(j, SV.dropped(c2)) : Bool}):
  stmt_absurd(M.Both({SV.kind(SV.class_at(c1, c)) == SV.kind(SV.class_at(c2, c)) : Nat}, {SV.mem(j, SV.dropped(c1)) == SV.mem(j, SV.dropped(c2)) : Bool}), bot)

# solve_complete's and solve_refused's new hypothesis: at x, every
# segment in the nd of a drop of a Kept or Amber constraint has positive
# squared length (a Strict side, as the verdict checks it over the box)
def stmt_strict_nd(~F: O.OField, +sk: SK.Sketch, +cls: List<&2, SV.Class>, +x: M.Vec(~F), +pins: List<&2, Nat>, hn: SV.Strict(~F, x, DR.ndsides(SV.ents(sk), SV.live_nd(cls)), pins), bot: {False{} == True{} : Bool}) -> Unit:
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
