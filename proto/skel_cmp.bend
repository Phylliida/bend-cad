# Prints, for a few sketches, the solver's structure of the kept system
# (lib/solve.bend: skel_of, worked out in the sketch's numbering past dead
# equations, then renumbered) and lib/struct.bend's structure of the kept
# system itself: the two must agree (tools/regress.sh compares them).
# Native: bin/bend proto/skel_cmp.bend -o <out> && <out> --threads 1

import Base
import ../spec/sketch.bend as SK
import ../lib/struct.bend as ST
import ../lib/solve.bend as SO
import ./struct_run.bend as SR
import ./solve_run.bend as RU

def both(name: String, +sk: SK.Sketch) -> String:
  "== " ++ name ++ "\n" ++ SR.show(SO.skel_of(sk)) ++ "-- kept\n" ++ SR.show(ST.structure(SO.kept(sk), SO.nvars(sk)))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(both("circle", SR.circle()))
    IO.print(both("over", SR.over()))
    IO.print(both("free", RU.free()))
    IO.print(both("far", RU.far()))
    IO.print(both("mid", RU.mid()))
    IO.print(both("tiny", RU.tiny()))
    IO.print(both("chain12", SR.chain(12n)))
