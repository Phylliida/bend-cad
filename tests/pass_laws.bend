# bend-cad: the single pass (PLAN-sk13a S4), restated here so the gate
# checks lib/passpf.bend and what it rests on (lib/kbpf.bend,
# lib/prepf.bend, lib/ownpf.bend, lib/solvedpf.bend, lib/cwpf.bend,
# lib/gmpf.bend, lib/clslpf.bend) until the solver reports the pass's
# classes (PLAN-sk13a S5):
# - for every well-formed sketch whose variables cover it, the pass's
#   classes are honest (spec/solve.bend: Honest), each constraint's class
#   the honest one given the classes before it.

import Base
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ../lib/solve.bend as SO
import ../lib/pass.bend as PA
import ../lib/passpf.bend as PP

def pass_honest(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}) -> SV.Honest(sk, PA.classes(sk)):
  PP.pass_honest(sk, w, cov)
