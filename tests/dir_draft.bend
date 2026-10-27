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
