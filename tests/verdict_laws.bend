# bend-cad: what the verdict's exact checks say (lib/verdict.bend,
# PLAN-sk13a S5), restated here so the gate checks lib/vrdpf.bend and
# lib/vsdpf.bend until the verdict uses them. In every ordered field, at
# a point x where the system solved holds:
# - when every class's dropped equations have combinations that pass,
#   every equation of the sketch less its red constraints holds;
# - wherever that system holds, the system solved does;
# - when moreover the amber refutations pass and the side conditions of
#   the sketch less its red and amber constraints hold, every side
#   condition of the sketch less its red constraints holds.

import Base
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../lib/verdict.bend as VD
import ../lib/vrdpf.bend as VR
import ../lib/vsdpf.bend as VS

def zeros_of_drops(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))), +hd: {VD.dck(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(cls), SV.dropped(cls), cls) == True{} : Bool})
  -> SK.Zeros(~F, x, SK.Sketch.eqs(SV.mark(SV.reds(cls), sk))):
  VR.zeros_mark(~F, x, sk, cls, hz, hd)

def zeros_of_kept(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, hk: SK.Zeros(~F, x, SK.Sketch.eqs(SV.mark(R, sk)))) -> SK.Zeros(~F, x, SV.solved(sk, R, D)):
  VR.zeros_solved(~F, x, sk, R, D, hk)

def sides_of_ambers(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, +cls: List<&2, SV.Class>, +hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(cls), SV.dropped(cls))),
  +hd: {VD.dck(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(cls), SV.dropped(cls), cls) == True{} : Bool}, +ha: {VD.ack(sk, SV.reds(cls), cls, 0n) == True{} : Bool},
  +hsc: SK.Sides(~F, x, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk)))) -> SK.Sides(~F, x, SK.Sketch.sides(SV.mark(SV.reds(cls), sk))):
  VS.sides_mark(~F, x, sk, cls, hz, hd, ha, hsc)
