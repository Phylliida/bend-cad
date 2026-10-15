# bend-cad: the solver's structure under solve_complete (DESIGN §10.4, C2),
# restated here so the gate checks lib/tarjanpf.bend until the
# completeness proof imports it.
# - Tarjan's components (lib/struct.bend: comps) partition the equations
#   they start from: put together they are distinct and hold exactly those
#   equations, when every equation one of them needs is among them (good
#   below nq, at most nq of them).

import Base
import ../spec/solve.bend as SV
import ../lib/karith.bend as KA
import ../lib/struct.bend as ST
import ../lib/listpf.bend as L
import ../lib/tarjanpf.bend as TJ

def tarjan_partitions(+adj: List<&2, List<&2, Nat>>, +em: List<&2, Maybe<&2, Nat>>, +good: List<&2, Nat>, +nq: Nat, +hs: {L.subl(ST.somes(em), good) == True{} : Bool}, +hb: {SV.below(good, nq) == True{} : Bool}, hl: {KA.natle(SV.len(good), nq) == True{} : Bool}) -> {SV.band(SV.distinct(ST.cats(ST.comps(adj, em, good, nq))), SV.band(L.subl(good, ST.cats(ST.comps(adj, em, good, nq))), L.subl(ST.cats(ST.comps(adj, em, good, nq)), good))) == True{} : Bool}:
  TJ.comps_part(adj, em, good, nq, hs, hb, hl)
