# bend-cad: the solver's totality and honesty (ROADMAP: solve_total,
# solve_honest), proven. Proofs only.
#
# For a well-formed sketch whose variables cover it, whatever the drawing
# and the level:
# - the classes and pins solve reports are those of the sketch alone (the
#   answer is built through projections, lib/solve.bend: found);
# - they are the single pass's classes, and those are honest
#   (lib/passpf.bend: pass_honest);
# - the sketch less the red constraints passes the well-formedness check
#   (lib/wfcpf.bend: any red list);
# - the pins are distinct variables, and the system solved has a perfect
#   matching onto the free variables, by dependence (lib/perfpf.bend:
#   total_pass).

import Base
import ../spec/num.bend as S
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ./wfdec.bend as WF
import ./struct.bend as ST
import ./solve.bend as SO
import ./pass.bend as PA
import ./wfcpf.bend as WC
import ./covpf.bend as CV
import ./gmpf.bend as GM
import ./passpf.bend as PP
import ./perfpf.bend as PF

def tp.go(+sk: SK.Sketch, +hwf: {WF.wf_dec(sk) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat,
  t: SK.Both({SV.distinct(SO.pins_of(sk)) == True{} : Bool}, {SV.below(SO.pins_of(sk), SO.nvars(sk)) == True{} : Bool}) & (&m: List<&2, Nat> -> SV.Perfect(SV.solved(sk, SV.reds(SO.cls_of(sk)), SV.dropped(SO.cls_of(sk))), SV.free(SO.nvars(sk), 0n, SO.pins_of(sk)), m)))
  -> ({SO.Out.cls(SO.solve_l(sk, g0, l)) == SO.cls_of(sk) : List<&2, SV.Class>} & ({SO.Out.pins(SO.solve_l(sk, g0, l)) == SO.pins_of(sk) : List<&2, Nat>} & ({WF.wf_dec(SV.mark(SV.reds(SO.cls_of(sk)), sk)) == True{} : Bool} & ({SV.distinct(SO.pins_of(sk)) == True{} : Bool} & ({SV.below(SO.pins_of(sk), SO.nvars(sk)) == True{} : Bool} & (&m: List<&2, Nat> -> SV.Perfect(SV.solved(sk, SV.reds(SO.cls_of(sk)), SV.dropped(SO.cls_of(sk))), SV.free(SO.nvars(sk), 0n, SO.pins_of(sk)), m))))))):
  (hdb, pm) = t
  (hd, hb) = hdb
  ({==}, ({==}, (WC.wf_mark(SV.reds(SO.cls_of(sk)), sk, hwf), (hd, (hb, pm)))))

# law 9: the structure stage never fails
def solve_total(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat) -> ({SO.Out.cls(SO.solve_l(sk, g0, l)) == SO.cls_of(sk) : List<&2, SV.Class>} & ({SO.Out.pins(SO.solve_l(sk, g0, l)) == SO.pins_of(sk) : List<&2, Nat>} & ({WF.wf_dec(SV.mark(SV.reds(SO.cls_of(sk)), sk)) == True{} : Bool} & ({SV.distinct(SO.pins_of(sk)) == True{} : Bool} & ({SV.below(SO.pins_of(sk), SO.nvars(sk)) == True{} : Bool} & (&m: List<&2, Nat> -> SV.Perfect(SV.solved(sk, SV.reds(SO.cls_of(sk)), SV.dropped(SO.cls_of(sk))), SV.free(SO.nvars(sk), 0n, SO.pins_of(sk)), m))))))):
  +hwf = WC.wf_dec_ok(sk, w)
  tp.go(sk, hwf, g0, l, PF.total_pass.a(sk, GM.adjb_dadjs(SK.Sketch.eqs(sk), SO.nvars(sk), CV.cov(sk, SO.nvars(sk), cov, hwf))))

# law 4: the classification is honest, at every level, ok or not
def solve_honest(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat) -> SV.Honest(sk, SO.Out.cls(SO.solve_l(sk, g0, l))):
  PP.pass_honest(sk, w, cov)
