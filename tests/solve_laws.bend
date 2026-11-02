# The solver's proven laws (ROADMAP.bend) with their proofs
# (lib/dsolvepf.bend: the verdict laws, solve_blame, solve_honest,
# solve_drop, solve_amber and solve_conflict; lib/dtotalpf.bend:
# solve_total; lib/duniqpf.bend: honest_unique), restated so the gate
# checks the proofs and tools/lawsync.py checks the statements match
# ROADMAP's. solve_complete and solve_refused are in
# tests/complete_laws.bend, fast_solve in tests/fast_laws.bend.

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
import ../spec/dir.bend as DR
import ../lib/kinst.bend as KI
import ../lib/solve.bend as SO
import ../lib/dsolvepf.bend as DSP
import ../lib/dtotalpf.bend as DTP
import ../lib/duniqpf.bend as DUQ
import ../lib/wfdec.bend as WF

def solve_exists(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}) -> (&x: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x) & SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk)))):
  DSP.solve_exists2(~F, ~R, ~H, sk, g0, l, ok)

def solve_unique(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}, +x1: M.Vec(~F), h1: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x1), m1: SK.Sketch.means(~F, x1, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk)), +x2: M.Vec(~F), h2: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x2), m2: SK.Sketch.means(~F, x2, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk))) -> {x1 == x2 : M.Vec(~F)}:
  DSP.solve_unique2(~F, ~H, sk, g0, l, ok, x1, h1, m1, x2, h2, m2)

def solve_pins(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}) -> {SV.held(SO.Out.pins(SO.solve_l(sk, g0, l)), g0, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l))) == True{} : Bool}:
  DSP.solve_pins2(sk, g0, l, ok)

def solve_regular(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}, +x: M.Vec(~F), h: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x), m: SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk))) -> DV.Regular(~F, x, SV.solved(sk, SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), SV.dropped(SO.Out.cls(SO.solve_l(sk, g0, l)))), SV.free(SO.nvars(sk), 0n, SO.Out.pins(SO.solve_l(sk, g0, l)))):
  DSP.solve_regular2(~F, ~H, sk, g0, l, ok, x, h, m)

def solve_blame(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}, +c: Nat) -> (&x: M.Vec(~F) -> SK.Sketch.means(~F, x, SV.only(SV.support(SO.Out.cls(SO.solve_l(sk, g0, l)), c), sk))):
  DSP.solve_blame2(~F, ~R, ~H, sk, g0, l, ok, c)

def solve_honest(+sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat) -> SV.Honest(sk, SO.Out.cls(SO.solve_l(sk, g0, l))):
  DSP.solve_honest2(sk, w, cov, g0, l)

def solve_drop(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat, +x: M.Vec(~F), hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), SV.dropped(SO.Out.cls(SO.solve_l(sk, g0, l))))), +j: Nat, hj: {SV.mem(j, SV.dropped(SO.Out.cls(SO.solve_l(sk, g0, l)))) == True{} : Bool}, hl: DR.Longs(~F, x, SV.ents(sk), SV.dnd_at(SO.Out.cls(SO.solve_l(sk, g0, l)), j))) -> SK.Zeros(~F, x, [SV.eqat(SK.Sketch.eqs(sk), j)]):
  DSP.solve_drop2(~F, sk, w, cov, g0, l, x, hz, j, hj, hl)

def solve_amber(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat, +x: M.Vec(~F), m: SK.Sketch.means(~F, x, SV.mark(SV.cat(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), SV.ambers(SO.Out.cls(SO.solve_l(sk, g0, l)))), sk)), hl: DR.Longs(~F, x, SV.ents(sk), SV.amber_nd(SO.Out.cls(SO.solve_l(sk, g0, l))))) -> SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk)):
  DSP.solve_amber2(~F, sk, w, cov, g0, l, x, m, hl)

def solve_conflict(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat, +c: Nat, hc: {SV.is_conflict(SV.class_at(SO.Out.cls(SO.solve_l(sk, g0, l)), c)) == True{} : Bool}, +x: M.Vec(~F), m: SK.Sketch.means(~F, x, SV.only(Con{c, SV.support(SO.Out.cls(SO.solve_l(sk, g0, l)), c)}, sk)), hl: DR.Longs(~F, x, SV.ents(sk), SV.conflict_nd(SO.Out.cls(SO.solve_l(sk, g0, l)), c))) -> Empty:
  DSP.solve_conflict2(~F, sk, w, cov, g0, l, c, hc, x, m, hl)

def solve_total(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat) -> ({SO.Out.cls(SO.solve_l(sk, g0, l)) == SO.cls_of(sk) : List<&2, SV.Class>} & ({SO.Out.pins(SO.solve_l(sk, g0, l)) == SO.pins_of(sk) : List<&2, Nat>} & ({WF.wf_dec(SV.mark(SV.reds(SO.cls_of(sk)), sk)) == True{} : Bool} & ({SV.distinct(SO.pins_of(sk)) == True{} : Bool} & ({SV.below(SO.pins_of(sk), SO.nvars(sk)) == True{} : Bool} & (&m: List<&2, Nat> -> SV.Perfect(SV.solved(sk, SV.reds(SO.cls_of(sk)), SV.dropped(SO.cls_of(sk))), SV.free(SO.nvars(sk), 0n, SO.pins_of(sk)), m))))))):
  DTP.solve_total2(sk, w, cov, g0, l)

def honest_unique(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +c1: List<&2, SV.Class>, h1: SV.Honest(sk, c1), +c2: List<&2, SV.Class>, h2: SV.Honest(sk, c2), +c: Nat, +j: Nat) -> M.Both({SV.kind(SV.class_at(c1, c)) == SV.kind(SV.class_at(c2, c)) : Nat}, {SV.mem(j, SV.dropped(c1)) == SV.mem(j, SV.dropped(c2)) : Bool}):
  DUQ.honest_unique2(sk, c1, h1, c2, h2, c, j)
