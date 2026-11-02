# fast_solve for the draft solver (PLAN-sk13b B5.5): the draft word solver
# (lib/dwfast.bend) at word dyadics in base 2^12 returns exactly the draft
# solver's answer (lib/dsolve.bend), proven generically in
# lib/dwfastpf.bend and checked here at the CLI's base, as
# tests/fast_laws.bend does for sk-13a's solver. Its own gate root: the
# generic proof is checked again at these closed numbers.

import Base
import ../spec/num.bend as S
import ../spec/sketch.bend as SK
import ../lib/solve.bend as SO
import ../lib/fast.bend as FS
import ../lib/dsolve.bend as DSO
import ../lib/dwfast.bend as DWF
import ../lib/dwfastpf.bend as DWP
import ../lib/wnumpf.bend as WP

def b5_fast(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat) -> {DWF.wsolve_l2(sk, g0, l) == DSO.solve_l2(sk, g0, l) : SO.Out}:
  DWP.solve_l2_eq(~FS.wk(), ~FS.wo(), ~WP.wlaws(4095n, 11n, {==}), sk, g0, l)
