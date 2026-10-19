# bend-cad: the solver's totality, in its sk-09 form (total_now), proven.
# Proofs only. ROADMAP's solve_total (sk-13a v2) adds the matching
# (Perfect, by dependence) and stays open until PLAN-sk13a.md S4.
#
# For a well-formed sketch whose variables cover it, whatever the drawing
# and the level, the structure stage never fails: the classes and pins
# solve reports are those of the sketch alone; every red constraint's
# sk-09 witness is explained (lib/redpf.bend, lib/why.bend); the sketch
# less the red constraints passes the well-formedness check
# (lib/wfcpf.bend); the pins are distinct variables; and with them the
# kept system is square (lib/maxpf.bend: the variable side's matching is
# maximum). The classes' red positions are the red stage's
# (lib/clspf.bend).

import Base
import ../spec/num.bend as S
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ./why.bend as WY
import ./wfdec.bend as WF
import ./solve.bend as SO
import ./listpf.bend as L
import ./redpf.bend as RP
import ./wfcpf.bend as WC
import ./covpf.bend as CV
import ./maxpf.bend as MX
import ./clspf.bend as CL

# the sk-09 facts, moved from the red stage's list to the classes
def rw_wf(+sk: SK.Sketch, h: {WF.wf_dec(SV.mark(SO.red_of(sk), sk)) == True{} : Bool}) -> {WF.wf_dec(SV.mark(SV.reds(SO.cls_of(sk)), sk)) == True{} : Bool}:
  %Equal.sym(SK.Sketch, SV.mark(SV.reds(SO.cls_of(sk)), sk), SV.mark(SO.red_of(sk), sk), CL.mark_cls_of(sk)) : {WF.wf_dec(_) == True{} : Bool}
  h

def rw_sq(+sk: SK.Sketch, h: {Nat.add(SV.neqs(SK.Sketch.eqs(SV.mark(SO.red_of(sk), sk))), SV.len(SO.pins_of(sk))) == SO.nvars(sk) : Nat}) -> {Nat.add(SV.neqs(SK.Sketch.eqs(SV.mark(SV.reds(SO.cls_of(sk)), sk))), SV.len(SO.pins_of(sk))) == SO.nvars(sk) : Nat}:
  %Equal.sym(SK.Sketch, SV.mark(SV.reds(SO.cls_of(sk)), sk), SV.mark(SO.red_of(sk), sk), CL.mark_cls_of(sk)) : {Nat.add(SV.neqs(SK.Sketch.eqs(_)), SV.len(SO.pins_of(sk))) == SO.nvars(sk) : Nat}
  h

def total_now(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat) -> M.Both({SO.Out.cls(SO.solve_l(sk, g0, l)) == SO.cls_of(sk) : List<&2, SV.Class>}, M.Both({SO.Out.pins(SO.solve_l(sk, g0, l)) == SO.pins_of(sk) : List<&2, Nat>}, M.Both({WY.explained(sk, SO.red_of(sk), SO.why_of(sk)) == True{} : Bool}, M.Both({WF.wf_dec(SV.mark(SV.reds(SO.cls_of(sk)), sk)) == True{} : Bool}, M.Both({SV.distinct(SO.pins_of(sk)) == True{} : Bool}, M.Both({SV.below(SO.pins_of(sk), SO.nvars(sk)) == True{} : Bool}, {Nat.add(SV.neqs(SK.Sketch.eqs(SV.mark(SV.reds(SO.cls_of(sk)), sk))), SV.len(SO.pins_of(sk))) == SO.nvars(sk) : Nat})))))):
  +hwf = WC.wf_dec_ok(sk, w)
  +ha = CV.cov(sk, SO.nvars(sk), cov, hwf)
  +hp = MX.pins_sq(sk, ha)
  +nv = SO.nvars(sk)
  +pins = SO.pins_of(sk)
  +kn = SV.neqs(SO.kept(sk))
  +hp2 = L.band_r(SV.distinct(pins), SV.band(SV.below(pins, nv), SV.eq(Nat.add(kn, SV.len(pins)), nv)), hp)
  ({==}, ({==}, (RP.explained_of(sk, SO.red_of(sk), SO.why_of(sk), RP.red_good(sk, nv, ha)), (rw_wf(sk, WC.wf_mark(SO.red_of(sk), sk, hwf)), (L.band_l(SV.distinct(pins), SV.band(SV.below(pins, nv), SV.eq(Nat.add(kn, SV.len(pins)), nv)), hp), (L.band_l(SV.below(pins, nv), SV.eq(Nat.add(kn, SV.len(pins)), nv), hp2), rw_sq(sk, L.eq_ok(Nat.add(kn, SV.len(pins)), nv, L.band_r(SV.below(pins, nv), SV.eq(Nat.add(kn, SV.len(pins)), nv), hp2)))))))))
