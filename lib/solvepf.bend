# bend-cad: the solver's laws (ROADMAP: solve_exists, solve_unique,
# solve_red, solve_pins), proven from the verdict seal recomputes (lib/solve.bend) and
# the sk-06 sketch laws (lib/planpf.bend). Nothing about the search is
# used: whatever it found, a True verdict carries every hypothesis.

import Base
import ../spec/num.bend as S
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/real.bend as CR
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./kinst.bend as KI
import ./plan.bend as PL
import ./planpf.bend as PP
import ./wfdec.bend as WF
import ./solve.bend as SO

# The verdict's parts
# -------------------
# final(sk, g0, x) = P && A && B && C && D && E

def pP(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out) -> Bool:
  SV.held(SO.Out.pins(x), g0, SO.Out.gc(x), SO.Out.gr(x))

def pA(+sk: SK.Sketch, +x: SO.Out) -> Bool:
  SV.explained(sk, SO.Out.red(x), SO.Out.why(x))

def pB(+sk: SK.Sketch, +x: SO.Out) -> Bool:
  WF.wf_dec(SV.mark(SO.Out.red(x), sk))

def pC(+sk: SK.Sketch, +x: SO.Out) -> Bool:
  BX.Sketch.within(SV.mark(SO.Out.red(x), sk), List.length(&2, N.NC(KI.dnum()), SO.Out.gc(x)))

def pD(+sk: SK.Sketch, +x: SO.Out) -> Bool:
  PL.check(~KI.dnum(), SK.Sketch.eqs(SV.mark(SO.Out.red(x), sk)), SO.Out.gc(x), SO.Out.gr(x), SO.Out.plan(x))

def pE(+sk: SK.Sketch, +x: SO.Out) -> Bool:
  PL.check_sides(~KI.dnum(), SK.Sketch.sides(SV.mark(SO.Out.red(x), sk)), SO.Out.gc(x), SO.Out.gr(x))

def r0(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {KA.band(pA(sk, x), KA.band(pB(sk, x), KA.band(pC(sk, x), KA.band(pD(sk, x), pE(sk, x))))) == True{} : Bool}:
  KA.band_r(pP(sk, g0, x), KA.band(pA(sk, x), KA.band(pB(sk, x), KA.band(pC(sk, x), KA.band(pD(sk, x), pE(sk, x))))), h)

def r1(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {KA.band(pB(sk, x), KA.band(pC(sk, x), KA.band(pD(sk, x), pE(sk, x)))) == True{} : Bool}:
  KA.band_r(pA(sk, x), KA.band(pB(sk, x), KA.band(pC(sk, x), KA.band(pD(sk, x), pE(sk, x)))), r0(sk, g0, x, h))

def r2(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {KA.band(pC(sk, x), KA.band(pD(sk, x), pE(sk, x))) == True{} : Bool}:
  KA.band_r(pB(sk, x), KA.band(pC(sk, x), KA.band(pD(sk, x), pE(sk, x))), r1(sk, g0, x, h))

def r3(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {KA.band(pD(sk, x), pE(sk, x)) == True{} : Bool}:
  KA.band_r(pC(sk, x), KA.band(pD(sk, x), pE(sk, x)), r2(sk, g0, x, h))

def hP(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {pP(sk, g0, x) == True{} : Bool}:
  KA.band_l(pP(sk, g0, x), KA.band(pA(sk, x), KA.band(pB(sk, x), KA.band(pC(sk, x), KA.band(pD(sk, x), pE(sk, x))))), h)

def hA(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {pA(sk, x) == True{} : Bool}:
  KA.band_l(pA(sk, x), KA.band(pB(sk, x), KA.band(pC(sk, x), KA.band(pD(sk, x), pE(sk, x)))), r0(sk, g0, x, h))

def hB(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {pB(sk, x) == True{} : Bool}:
  KA.band_l(pB(sk, x), KA.band(pC(sk, x), KA.band(pD(sk, x), pE(sk, x))), r1(sk, g0, x, h))

def hC(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {pC(sk, x) == True{} : Bool}:
  KA.band_l(pC(sk, x), KA.band(pD(sk, x), pE(sk, x)), r2(sk, g0, x, h))

def hD(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {pD(sk, x) == True{} : Bool}:
  KA.band_l(pD(sk, x), pE(sk, x), r3(sk, g0, x, h))

def hE(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {pE(sk, x) == True{} : Bool}:
  KA.band_r(pD(sk, x), pE(sk, x), r3(sk, g0, x, h))

# For any answer with a True verdict
# ----------------------------------

def exists_of(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> &y: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y) & SK.Sketch.means(~F, y, SV.mark(SO.Out.red(x), sk))):
  PP.sketch_exists(~KI.dnum(), ~F, ~R, ~H, SV.mark(SO.Out.red(x), sk), WF.wf_ok(SV.mark(SO.Out.red(x), sk), hB(sk, g0, x, h)), SO.Out.gc(x), SO.Out.gr(x), hC(sk, g0, x, h), SO.Out.plan(x), hD(sk, g0, x, h), hE(sk, g0, x, h))

def unique_of(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}, +y1: M.Vec(~F), h1: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y1), m1: SK.Sketch.means(~F, y1, SV.mark(SO.Out.red(x), sk)), +y2: M.Vec(~F), h2: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y2), m2: SK.Sketch.means(~F, y2, SV.mark(SO.Out.red(x), sk))) -> {y1 == y2 : M.Vec(~F)}:
  PP.sketch_unique(~KI.dnum(), ~F, ~H, SV.mark(SO.Out.red(x), sk), SO.Out.gc(x), SO.Out.gr(x), hC(sk, g0, x, h), SO.Out.plan(x), hD(sk, g0, x, h), y1, h1, m1, y2, h2, m2)

def pins_of(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {SV.held(SO.Out.pins(x), g0, SO.Out.gc(x), SO.Out.gr(x)) == True{} : Bool}:
  hP(sk, g0, x, h)

def red_of(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {SV.explained(sk, SO.Out.red(x), SO.Out.why(x)) == True{} : Bool}:
  hA(sk, g0, x, h)

# The laws
# --------

def solve_exists(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +ok: {SO.Out.ok(SO.solve(sk, g0)) == True{} : Bool}) -> &x: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve(sk, g0)), SO.Out.gr(SO.solve(sk, g0)), x) & SK.Sketch.means(~F, x, SV.mark(SO.Out.red(SO.solve(sk, g0)), sk))):
  exists_of(~F, ~R, ~H, sk, g0, SO.search_b(sk, g0, SO.budget()), ok)

def solve_unique(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +ok: {SO.Out.ok(SO.solve(sk, g0)) == True{} : Bool}, +x1: M.Vec(~F), h1: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve(sk, g0)), SO.Out.gr(SO.solve(sk, g0)), x1), m1: SK.Sketch.means(~F, x1, SV.mark(SO.Out.red(SO.solve(sk, g0)), sk)), +x2: M.Vec(~F), h2: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve(sk, g0)), SO.Out.gr(SO.solve(sk, g0)), x2), m2: SK.Sketch.means(~F, x2, SV.mark(SO.Out.red(SO.solve(sk, g0)), sk))) -> {x1 == x2 : M.Vec(~F)}:
  unique_of(~F, ~H, sk, g0, SO.search_b(sk, g0, SO.budget()), ok, x1, h1, m1, x2, h2, m2)

def solve_red(+sk: SK.Sketch, +g0: List<&2, S.D>, +ok: {SO.Out.ok(SO.solve(sk, g0)) == True{} : Bool}) -> {SV.explained(sk, SO.Out.red(SO.solve(sk, g0)), SO.Out.why(SO.solve(sk, g0))) == True{} : Bool}:
  red_of(sk, g0, SO.search_b(sk, g0, SO.budget()), ok)

def solve_pins(+sk: SK.Sketch, +g0: List<&2, S.D>, +ok: {SO.Out.ok(SO.solve(sk, g0)) == True{} : Bool}) -> {SV.held(SO.Out.pins(SO.solve(sk, g0)), g0, SO.Out.gc(SO.solve(sk, g0)), SO.Out.gr(SO.solve(sk, g0))) == True{} : Bool}:
  pins_of(sk, g0, SO.search_b(sk, g0, SO.budget()), ok)
