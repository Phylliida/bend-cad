# The draft solver's laws (PLAN-sk13b B5): lib/dsolve.bend, the solver over
# the pass with the direction layer, beside lib/solve.bend until the
# switch. sk-13a's verdict laws with their statements unchanged (solve_l
# read as the draft solver's), and the extended Honest's laws at the
# solver level (tools/drafts/roadmap13b.draft's texts), proven in
# lib/dsolvepf.bend; restated here so the gate checks them.

import Base
import ../spec/num.bend as S
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/real.bend as CR
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/deriv.bend as DV
import ../spec/solve.bend as SV
import ../spec/_draft13b.bend as DH
import ../spec/dir.bend as DR
import ../lib/kinst.bend as KI
import ../lib/solve.bend as SO
import ../lib/dsolve.bend as DSO
import ../lib/dsolvepf.bend as DSP

def b5_exists(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(DSO.solve_l2(sk, g0, l)) == True{} : Bool}) -> (&x: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(DSO.solve_l2(sk, g0, l)), SO.Out.gr(DSO.solve_l2(sk, g0, l)), x) & SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(DSO.solve_l2(sk, g0, l))), sk)))):
  DSP.solve_exists2(~F, ~R, ~H, sk, g0, l, ok)

def b5_unique(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(DSO.solve_l2(sk, g0, l)) == True{} : Bool}, +x1: M.Vec(~F), h1: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(DSO.solve_l2(sk, g0, l)), SO.Out.gr(DSO.solve_l2(sk, g0, l)), x1), m1: SK.Sketch.means(~F, x1, SV.mark(SV.reds(SO.Out.cls(DSO.solve_l2(sk, g0, l))), sk)), +x2: M.Vec(~F), h2: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(DSO.solve_l2(sk, g0, l)), SO.Out.gr(DSO.solve_l2(sk, g0, l)), x2), m2: SK.Sketch.means(~F, x2, SV.mark(SV.reds(SO.Out.cls(DSO.solve_l2(sk, g0, l))), sk))) -> {x1 == x2 : M.Vec(~F)}:
  DSP.solve_unique2(~F, ~H, sk, g0, l, ok, x1, h1, m1, x2, h2, m2)

def b5_pins(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(DSO.solve_l2(sk, g0, l)) == True{} : Bool}) -> {SV.held(SO.Out.pins(DSO.solve_l2(sk, g0, l)), g0, SO.Out.gc(DSO.solve_l2(sk, g0, l)), SO.Out.gr(DSO.solve_l2(sk, g0, l))) == True{} : Bool}:
  DSP.solve_pins2(sk, g0, l, ok)

def b5_regular(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(DSO.solve_l2(sk, g0, l)) == True{} : Bool}, +x: M.Vec(~F), h: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(DSO.solve_l2(sk, g0, l)), SO.Out.gr(DSO.solve_l2(sk, g0, l)), x), m: SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(DSO.solve_l2(sk, g0, l))), sk))) -> DV.Regular(~F, x, SV.solved(sk, SV.reds(SO.Out.cls(DSO.solve_l2(sk, g0, l))), SV.dropped(SO.Out.cls(DSO.solve_l2(sk, g0, l)))), SV.free(SO.nvars(sk), 0n, SO.Out.pins(DSO.solve_l2(sk, g0, l)))):
  DSP.solve_regular2(~F, ~H, sk, g0, l, ok, x, h, m)

def b5_blame(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(DSO.solve_l2(sk, g0, l)) == True{} : Bool}, +c: Nat) -> (&x: M.Vec(~F) -> SK.Sketch.means(~F, x, SV.only(SV.support(SO.Out.cls(DSO.solve_l2(sk, g0, l)), c), sk))):
  DSP.solve_blame2(~F, ~R, ~H, sk, g0, l, ok, c)

def b5_honest(+sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat) -> DH.Honest(sk, SO.Out.cls(DSO.solve_l2(sk, g0, l))):
  DSP.solve_honest2(sk, w, cov, g0, l)

def b5_drop(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat, +x: M.Vec(~F), hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(SO.Out.cls(DSO.solve_l2(sk, g0, l))), SV.dropped(SO.Out.cls(DSO.solve_l2(sk, g0, l))))), +j: Nat, hj: {SV.mem(j, SV.dropped(SO.Out.cls(DSO.solve_l2(sk, g0, l)))) == True{} : Bool}, hl: DR.Longs(~F, x, SV.ents(sk), SV.dnd_at(SO.Out.cls(DSO.solve_l2(sk, g0, l)), j))) -> SK.Zeros(~F, x, [SV.eqat(SK.Sketch.eqs(sk), j)]):
  DSP.solve_drop2(~F, sk, w, cov, g0, l, x, hz, j, hj, hl)

def b5_amber(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat, +x: M.Vec(~F), m: SK.Sketch.means(~F, x, SV.mark(SV.cat(SV.reds(SO.Out.cls(DSO.solve_l2(sk, g0, l))), SV.ambers(SO.Out.cls(DSO.solve_l2(sk, g0, l)))), sk)), hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(SO.Out.cls(DSO.solve_l2(sk, g0, l))))) -> SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(DSO.solve_l2(sk, g0, l))), sk)):
  DSP.solve_amber2(~F, sk, w, cov, g0, l, x, m, hl)

def b5_conflict(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat, +c: Nat, hc: {SV.is_conflict(SV.class_at(SO.Out.cls(DSO.solve_l2(sk, g0, l)), c)) == True{} : Bool}, +x: M.Vec(~F), m: SK.Sketch.means(~F, x, SV.only(Con{c, SV.support(SO.Out.cls(DSO.solve_l2(sk, g0, l)), c)}, sk)), hl: DR.Longs(~F, x, SV.ents(sk), SV.conflict_nd(SO.Out.cls(DSO.solve_l2(sk, g0, l)), c))) -> Empty:
  DSP.solve_conflict2(~F, sk, w, cov, g0, l, c, hc, x, m, hl)
