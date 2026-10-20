# bend-cad: the structure the plan follows over the system solved
# (lib/pass.bend: skel; lib/skdpf.bend), restated so the gate checks it
# until the completeness proof uses it (PLAN-sk13a S5). For every sketch
# whose equations use only its variables:
# - the system solved is the full system at the pass's positions, so
#   reading it through positions in them is reading the full system;
# - the plan's pins are the pass's pins;
# - at a regular point of the system solved, in the free variables the
#   pass leaves, every block has an invertible Jacobian.

import Base
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/deriv.bend as DV
import ../lib/listpf.bend as L
import ../lib/struct.bend as ST
import ../lib/plan.bend as PL
import ../lib/dfspf.bend as D
import ../lib/pass.bend as PA
import ../lib/structpf.bend as STP
import ../lib/binvpf.bend as BI
import ../lib/solve.bend as SO
import ../lib/skdpf.bend as SD

def solved_read(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +vp: List<&2, Nat>, ys: List<&2, Nat>, hs: {L.subl(ys, PA.solved_pos(sk)) == True{} : Bool})
  -> {PL.reorder(vp, SV.solved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk))), ST.positions(ys, PA.solved_pos(sk))) == PL.reorder(vp, SK.Sketch.eqs(sk), ys) : List<&2, E.QExpr>}:
  SD.kept_reorder_d(sk, ha, vp, ys, hs)

def plan_pins(+sk: SK.Sketch) -> {SO.skel.pins(PA.skel(sk)) == PA.pins(sk) : List<&2, Nat>}:
  SD.pins_skel(sk)

def solved_blocks(~F: O.OField, +sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +x: M.Vec(~F), hr: DV.Regular(~F, x, SV.solved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk))), SV.free(PA.nvars(sk), 0n, PA.pins(sk))))
  -> BI.BInv(~F, x, SK.Sketch.eqs(sk), STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))))):
  SD.block_invs_d(~F, sk, ha, x, hr)
