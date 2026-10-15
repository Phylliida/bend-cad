# bend-cad: the solver's structure under solve_complete (DESIGN §10.4, C2),
# restated here so the gate checks lib/tarjanpf.bend and
# lib/structpf.bend until the completeness proof imports them.
# - Tarjan's components (lib/struct.bend: comps) partition the equations
#   they start from: put together they are distinct and hold exactly those
#   equations, when every equation one of them needs is among them (good
#   below nq, at most nq of them).
# - The solver's structure of a sketch's kept equations (variables
#   covered): the blocks hold exactly the kept equations, each valid with
#   its equations' mates as unknowns; the pins and then the blocks'
#   unknowns list every variable once; and the plan checker's walk over
#   the blocks finds its structural conjuncts (structpf: skok, swalk).

import Base
import ../spec/solve.bend as SV
import ../lib/karith.bend as KA
import ../lib/struct.bend as ST
import ../lib/listpf.bend as L
import ../spec/sketch.bend as SK
import ../lib/solve.bend as SO
import ../lib/dfspf.bend as D
import ../lib/maxpf.bend as MX
import ../lib/tarjanpf.bend as TJ
import ../lib/structpf.bend as SP

def tarjan_partitions(+adj: List<&2, List<&2, Nat>>, +em: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +nq: Nat, +hs: {L.subl(ST.somes(em), good) == True{} : Bool}, +hb: {SV.below(good, nq) == True{} : Bool}, hl: {KA.natle(SV.len(good), nq) == True{} : Bool}) -> {SV.band(SV.distinct(ST.cats(ST.comps(adj, em, good, nq))), SV.band(L.subl(good, ST.cats(ST.comps(adj, em, good, nq))), L.subl(ST.cats(ST.comps(adj, em, good, nq)), good))) == True{} : Bool}:
  TJ.comps_part(adj, em, good, nq, hs, hb, hl)

def solver_structure(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), SO.nvars(sk)) == True{} : Bool}) -> {SP.skok(SK.Sketch.eqs(sk), SO.nvars(sk), SO.good_of(sk), ST.KD.vm(MX.kvs(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk))), ST.KD.red(MX.kvs(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk))), SP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk), ST.KD.vm(MX.kvs(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk))), ST.KD.red(MX.kvs(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk))))) == True{} : Bool}:
  SP.struct_ok(sk, ha)
