# bend-cad: plans and the plan checker (DESIGN §8.2, §8.4). Untrusted: only
# the plan_* and box_sides laws say what a passing check means.
#
# A plan orders a system's variables into blocks. Each block names its
# unknowns (vars), its parameters (pars: variables fixed before it, pinned
# or unknowns of earlier blocks), the system's equations it solves (by
# index), and a certificate for those equations renumbered locally
# (unknowns 0..n-1, then the parameters).

import Base
import ../spec/ring.bend as E
import ../spec/knum.bend as N
import ../spec/cert.bend as C
import ../spec/sketch.bend as SK

type PBlock<-K: N.Num> is Data:
  PBlock{vars: List<&2, Nat>, pars: List<&2, Nat>, eqs: List<&2, Nat>, cert: C.Cert<K>}

type Plan<-K: N.Num> is Data:
  Plan{pins: List<&2, Nat>, blocks: List<&2, PBlock<K>>}

# stub: rejects every plan (the real checker replaces it)
def check(~K: N.Num, eqs: List<&2, E.QExpr>, gc: N.KVec(~K), gr: N.KVec(~K), p: Plan<K>) -> Bool:
  False{}

# stub: certifies no side condition
def check_sides(~K: N.Num, sides: List<&2, SK.Side>, gc: N.KVec(~K), gr: N.KVec(~K)) -> Bool:
  False{}
