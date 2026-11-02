# The word solver's law (ROADMAP.bend: fast_solve) with its proof: the
# generic theorem (lib/dwfastpf.bend: solve_l2_eq, for every computing numbers
# K with the proposer's operations and laws) at the CLI's instance, word
# dyadics in base 2^12 (lib/fast.bend: wk, wo), whose laws hold for every
# base 2^(1 + lp) given 2^(1 + lp) = bp + 1 (lib/wnumpf.bend: wlaws), here
# 2^12 = 4095 + 1, which the checker evaluates. Its own gate root: checking
# the generic proof again at these closed numbers takes about 47 s.

import Base
import ../spec/num.bend as S
import ../spec/sketch.bend as SK
import ../lib/solve.bend as SO
import ../lib/fast.bend as FS
import ../lib/dwfastpf.bend as DWP
import ../lib/wnumpf.bend as WP

def fast_solve(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat) -> {FS.wsolve_l(sk, g0, l) == SO.solve_l(sk, g0, l) : SO.Out}:
  DWP.solve_l2_eq(~FS.wk(), ~FS.wo(), ~WP.wlaws(4095n, 11n, {==}), sk, g0, l)
