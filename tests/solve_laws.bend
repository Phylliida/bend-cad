# The solver's proven laws (ROADMAP.bend) with their proofs
# (lib/solvepf.bend: the verdict laws; lib/regpf.bend: solve_regular;
# lib/blamepf.bend: solve_blame; lib/conflawpf.bend: solve_conflict;
# lib/totalpf.bend: solve_total, solve_honest; lib/completepf.bend:
# solve_complete; lib/refusedpf.bend: solve_refused), restated so the
# gate checks the proofs and tools/lawsync.py checks the statements match
# ROADMAP's.

import Base
import ../spec/num.bend as S
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/real.bend as CR
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ../lib/kinst.bend as KI
import ../lib/solve.bend as SO
import ../lib/solvepf.bend as SP
import ../lib/wfdec.bend as WF
import ../lib/totalpf.bend as TP
import ../spec/deriv.bend as DV
import ../lib/completepf.bend as CPF
import ../lib/regpf.bend as RGP
import ../lib/blamepf.bend as BLM
import ../lib/refusedpf.bend as RFD
import ../lib/conflawpf.bend as CFL

def solve_exists(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}) -> (&x: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x) & SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk)))):
  SP.solve_exists(~F, ~R, ~H, sk, g0, l, ok)

def solve_unique(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}, +x1: M.Vec(~F), h1: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x1), m1: SK.Sketch.means(~F, x1, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk)), +x2: M.Vec(~F), h2: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x2), m2: SK.Sketch.means(~F, x2, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk))) -> {x1 == x2 : M.Vec(~F)}:
  SP.solve_unique(~F, ~H, sk, g0, l, ok, x1, h1, m1, x2, h2, m2)

def solve_pins(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}) -> {SV.held(SO.Out.pins(SO.solve_l(sk, g0, l)), g0, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l))) == True{} : Bool}:
  SP.solve_pins(sk, g0, l, ok)

def solve_regular(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}, +x: M.Vec(~F), h: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x), m: SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk))) -> DV.Regular(~F, x, SV.solved(sk, SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), SV.dropped(SO.Out.cls(SO.solve_l(sk, g0, l)))), SV.free(SO.nvars(sk), 0n, SO.Out.pins(SO.solve_l(sk, g0, l)))):
  RGP.solve_regular(~F, ~H, sk, g0, l, ok, x, h, m)

def solve_blame(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}, +c: Nat) -> (&x: M.Vec(~F) -> SK.Sketch.means(~F, x, SV.only(SV.support(SO.Out.cls(SO.solve_l(sk, g0, l)), c), sk))):
  BLM.solve_blame(~F, ~R, ~H, sk, g0, l, ok, c)

def solve_conflict(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat, +c: Nat, hc: {SV.is_conflict(SV.class_at(SO.Out.cls(SO.solve_l(sk, g0, l)), c)) == True{} : Bool}, +x: M.Vec(~F), m: SK.Sketch.means(~F, x, SV.only(Con{c, SV.support(SO.Out.cls(SO.solve_l(sk, g0, l)), c)}, sk))) -> Empty:
  CFL.solve_conflict(~F, sk, w, cov, g0, l, c, hc, x, m)

def solve_total(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat) -> ({SO.Out.cls(SO.solve_l(sk, g0, l)) == SO.cls_of(sk) : List<&2, SV.Class>} & ({SO.Out.pins(SO.solve_l(sk, g0, l)) == SO.pins_of(sk) : List<&2, Nat>} & ({WF.wf_dec(SV.mark(SV.reds(SO.cls_of(sk)), sk)) == True{} : Bool} & ({SV.distinct(SO.pins_of(sk)) == True{} : Bool} & ({SV.below(SO.pins_of(sk), SO.nvars(sk)) == True{} : Bool} & (&m: List<&2, Nat> -> SV.Perfect(SV.solved(sk, SV.reds(SO.cls_of(sk)), SV.dropped(SO.cls_of(sk))), SV.free(SO.nvars(sk), 0n, SO.pins_of(sk)), m))))))):
  TP.solve_total(sk, w, cov, g0, l)

def solve_honest(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat) -> SV.Honest(sk, SO.Out.cls(SO.solve_l(sk, g0, l))):
  TP.solve_honest(sk, w, cov, g0, l)

def solve_complete(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +dy: {SV.dyadic(SV.mark(SV.reds(SO.cls_of(sk)), sk)) == True{} : Bool}, +g0: List<&2, S.D>, +x: M.Vec(~F), +hl: {M.len(~F, x) == SO.nvars(sk) : Nat}, +hp: SV.PinnedAt(~KI.dnum(), ~F, ~H, x, SO.pins_of(sk), g0), hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(SO.cls_of(sk)), SV.dropped(SO.cls_of(sk)))), hs: SV.Strict(~F, x, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(SO.cls_of(sk)), SV.ambers(SO.cls_of(sk))), sk)), SO.pins_of(sk)), hr: DV.Regular(~F, x, SV.solved(sk, SV.reds(SO.cls_of(sk)), SV.dropped(SO.cls_of(sk))), SV.free(SO.nvars(sk), 0n, SO.pins_of(sk)))) -> &d: O.C(F) -> (O.lt(F, O.zero(F), d) & (&l: Nat -> (@g: List<&2, S.D> -> SV.Near(~KI.dnum(), ~F, ~H, SO.nvars(sk), 0n, g, x, d, SO.pins_of(sk), g0) -> ({SO.Out.ok(SO.solve_l(sk, g, l)) == True{} : Bool} & BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g, l)), SO.Out.gr(SO.solve_l(sk, g, l)), x))))):
  CPF.solve_complete(~F, ~R, ~H, sk, w, cov, dy, g0, x, hl, hp, hz, hs, hr)

def solve_refused(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +dy: {SV.dyadic(SV.mark(SV.reds(SO.cls_of(sk)), sk)) == True{} : Bool}, +g0: List<&2, S.D>, hn: @l: Nat -> {SO.Out.ok(SO.solve_l(sk, g0, l)) == False{} : Bool}, +x: M.Vec(~F), +hx: {x == N.ofkv(~KI.dnum(), ~F, ~H, g0) : M.Vec(~F)}, +hl: {M.len(~F, x) == SO.nvars(sk) : Nat}, hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(SO.cls_of(sk)), SV.dropped(SO.cls_of(sk)))), hs: SV.Strict(~F, x, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(SO.cls_of(sk)), SV.ambers(SO.cls_of(sk))), sk)), SO.pins_of(sk)), hr: DV.Regular(~F, x, SV.solved(sk, SV.reds(SO.cls_of(sk)), SV.dropped(SO.cls_of(sk))), SV.free(SO.nvars(sk), 0n, SO.pins_of(sk)))) -> Empty:
  RFD.solve_refused(~F, ~R, ~H, sk, w, cov, dy, g0, hn, x, hx, hl, hz, hs, hr)
