# bend-cad: the single pass (PLAN-sk13a S4), restated here so the gate
# checks lib/passpf.bend and what it rests on (lib/kbpf.bend,
# lib/prepf.bend, lib/ownpf.bend, lib/solvedpf.bend, lib/cwpf.bend,
# lib/gmpf.bend, lib/clslpf.bend, lib/perfpf.bend) until the solver
# reports the pass's classes and pins (PLAN-sk13a S5). For every
# well-formed sketch whose variables cover it:
# - the pass's classes are honest (spec/solve.bend: Honest), each
#   constraint's class the honest one given the classes before it;
# - its pins are distinct variables, and the system solved has a perfect
#   matching onto the free variables, by dependence.

import Base
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ../lib/solve.bend as SO
import ../lib/pass.bend as PA
import ../lib/passpf.bend as PP
import ../lib/perfpf.bend as PF

def pass_honest(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}) -> SV.Honest(sk, PA.classes(sk)):
  PP.pass_honest(sk, w, cov)

# the pins are distinct variables, and the system solved has a perfect
# matching onto the free variables, by dependence (law 9's new part)
def total_pass(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool})
  -> SK.Both({SV.distinct(PA.pins(sk)) == True{} : Bool}, {SV.below(PA.pins(sk), PA.nvars(sk)) == True{} : Bool}) & (&m: List<&2, Nat> -> SV.Perfect(SV.solved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk))), SV.free(PA.nvars(sk), 0n, PA.pins(sk)), m)):
  PF.total_pass(sk, w, cov)
