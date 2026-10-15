# The solver's laws (ROADMAP.bend, drafts for review) with their proofs
# (lib/solvepf.bend; solve_total: lib/totalpf.bend), restated so the gate checks the proofs and
# tools/lawsync.py checks the statements match ROADMAP's.

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

def solve_exists(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +ok: {SO.Out.ok(SO.solve(sk, g0)) == True{} : Bool}) -> &x: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve(sk, g0)), SO.Out.gr(SO.solve(sk, g0)), x) & SK.Sketch.means(~F, x, SV.mark(SO.Out.red(SO.solve(sk, g0)), sk))):
  SP.solve_exists(~F, ~R, ~H, sk, g0, ok)

def solve_unique(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +ok: {SO.Out.ok(SO.solve(sk, g0)) == True{} : Bool}, +x1: M.Vec(~F), h1: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve(sk, g0)), SO.Out.gr(SO.solve(sk, g0)), x1), m1: SK.Sketch.means(~F, x1, SV.mark(SO.Out.red(SO.solve(sk, g0)), sk)), +x2: M.Vec(~F), h2: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve(sk, g0)), SO.Out.gr(SO.solve(sk, g0)), x2), m2: SK.Sketch.means(~F, x2, SV.mark(SO.Out.red(SO.solve(sk, g0)), sk))) -> {x1 == x2 : M.Vec(~F)}:
  SP.solve_unique(~F, ~H, sk, g0, ok, x1, h1, m1, x2, h2, m2)

def solve_red(+sk: SK.Sketch, +g0: List<&2, S.D>, +ok: {SO.Out.ok(SO.solve(sk, g0)) == True{} : Bool}) -> {SV.explained(sk, SO.Out.red(SO.solve(sk, g0)), SO.Out.why(SO.solve(sk, g0))) == True{} : Bool}:
  SP.solve_red(sk, g0, ok)

def solve_pins(+sk: SK.Sketch, +g0: List<&2, S.D>, +ok: {SO.Out.ok(SO.solve(sk, g0)) == True{} : Bool}) -> {SV.held(SO.Out.pins(SO.solve(sk, g0)), g0, SO.Out.gc(SO.solve(sk, g0)), SO.Out.gr(SO.solve(sk, g0))) == True{} : Bool}:
  SP.solve_pins(sk, g0, ok)

def solve_total(+sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat) -> M.Both({SO.Out.red(SO.solve_l(sk, g0, l)) == SO.red_of(sk) : List<&2, Nat>}, M.Both({SO.Out.why(SO.solve_l(sk, g0, l)) == SO.why_of(sk) : List<&2, SV.Why>}, M.Both({SO.Out.pins(SO.solve_l(sk, g0, l)) == SO.pins_of(sk) : List<&2, Nat>}, M.Both({SV.explained(sk, SO.red_of(sk), SO.why_of(sk)) == True{} : Bool}, M.Both({WF.wf_dec(SV.mark(SO.red_of(sk), sk)) == True{} : Bool}, M.Both({SV.distinct(SO.pins_of(sk)) == True{} : Bool}, M.Both({SV.below(SO.pins_of(sk), SO.nvars(sk)) == True{} : Bool}, {Nat.add(SV.neqs(SK.Sketch.eqs(SV.mark(SO.red_of(sk), sk))), SV.len(SO.pins_of(sk))) == SO.nvars(sk) : Nat}))))))):
  TP.solve_total(sk, w, cov, g0, l)
