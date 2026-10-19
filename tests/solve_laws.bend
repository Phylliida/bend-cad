# The solver's proven laws (ROADMAP.bend) with their proofs
# (lib/solvepf.bend), restated so the gate checks the proofs and
# tools/lawsync.py checks the statements match ROADMAP's; and sk-09's
# totality and completeness in their interim forms over the classes
# (lib/totalpf.bend: total_now; lib/completepf.bend: complete_now), which
# ROADMAP's solve_total and solve_complete (sk-13a v2, open) replace.

import Base
import ../spec/num.bend as S
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/real.bend as CR
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ../lib/why.bend as WY
import ../lib/kinst.bend as KI
import ../lib/solve.bend as SO
import ../lib/solvepf.bend as SP
import ../lib/wfdec.bend as WF
import ../lib/totalpf.bend as TP
import ../spec/deriv.bend as DV
import ../lib/completepf.bend as CPF

def solve_exists(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}) -> (&x: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x) & SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk)))):
  SP.solve_exists(~F, ~R, ~H, sk, g0, l, ok)

def solve_unique(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}, +x1: M.Vec(~F), h1: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x1), m1: SK.Sketch.means(~F, x1, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk)), +x2: M.Vec(~F), h2: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x2), m2: SK.Sketch.means(~F, x2, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk))) -> {x1 == x2 : M.Vec(~F)}:
  SP.solve_unique(~F, ~H, sk, g0, l, ok, x1, h1, m1, x2, h2, m2)

def solve_pins(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}) -> {SV.held(SO.Out.pins(SO.solve_l(sk, g0, l)), g0, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l))) == True{} : Bool}:
  SP.solve_pins(sk, g0, l, ok)

def total_now(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat) -> M.Both({SO.Out.cls(SO.solve_l(sk, g0, l)) == SO.cls_of(sk) : List<&2, SV.Class>}, M.Both({SO.Out.pins(SO.solve_l(sk, g0, l)) == SO.pins_of(sk) : List<&2, Nat>}, M.Both({WY.explained(sk, SO.red_of(sk), SO.why_of(sk)) == True{} : Bool}, M.Both({WF.wf_dec(SV.mark(SV.reds(SO.cls_of(sk)), sk)) == True{} : Bool}, M.Both({SV.distinct(SO.pins_of(sk)) == True{} : Bool}, M.Both({SV.below(SO.pins_of(sk), SO.nvars(sk)) == True{} : Bool}, {Nat.add(SV.neqs(SK.Sketch.eqs(SV.mark(SV.reds(SO.cls_of(sk)), sk))), SV.len(SO.pins_of(sk))) == SO.nvars(sk) : Nat})))))):
  TP.total_now(sk, w, cov, g0, l)

def complete_now(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +dy: {SV.dyadic(sk) == True{} : Bool}, +g0: List<&2, S.D>, +x: M.Vec(~F), +hl: {M.len(~F, x) == SO.nvars(sk) : Nat}, +hp: SV.PinnedAt(~KI.dnum(), ~F, ~H, x, SO.pins_of(sk), g0), hz: SK.Zeros(~F, x, SK.Sketch.eqs(SV.mark(SV.reds(SO.cls_of(sk)), sk))), hs: SV.Strict(~F, x, SK.Sketch.sides(SV.mark(SV.reds(SO.cls_of(sk)), sk)), Nil{}), hr: DV.Regular(~F, x, SK.Sketch.eqs(SV.mark(SV.reds(SO.cls_of(sk)), sk)), SV.free(SO.nvars(sk), 0n, SO.pins_of(sk)))) -> &d: O.C(F) -> (O.lt(F, O.zero(F), d) & (&l: Nat -> (@g: List<&2, S.D> -> SV.Near(~KI.dnum(), ~F, ~H, SO.nvars(sk), 0n, g, x, d, SO.pins_of(sk), g0) -> ({SO.Out.ok(SO.solve_l(sk, g, l)) == True{} : Bool} & BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g, l)), SO.Out.gr(SO.solve_l(sk, g, l)), x))))):
  CPF.complete_now(~F, ~R, ~H, sk, w, cov, dy, g0, x, hl, hp, hz, hs, hr)
