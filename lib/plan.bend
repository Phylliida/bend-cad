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
import ./karith.bend as KA
import ./kball.bend as KB
import ./cert.bend as CK

type PBlock<-K: N.Num> is Data:
  PBlock{vars: List<&2, Nat>, pars: List<&2, Nat>, eqs: List<&2, Nat>, cert: C.Cert<K>}

type Plan<-K: N.Num> is Data:
  Plan{pins: List<&2, Nat>, blocks: List<&2, PBlock<K>>}

# stub: rejects every plan (the real checker replaces it)
def check(~K: N.Num, eqs: List<&2, E.QExpr>, gc: N.KVec(~K), gr: N.KVec(~K), p: Plan<K>) -> Bool:
  False{}

# Side conditions over the box
# -----------------------------

# the ball of e over the box lies above 0 (or not below it)
def side_ok(~K: N.Num, +box: List<&2, KB.KB<K>>, s: SK.Side) -> Bool:
  match s:
    case SK.Gt0{+e}:
      KA.band(KB.held(~K, e), KA.klt(~K, N.nzero(K), KA.ksub(~K, KB.KB.c(K, KB.kball(~K, box, e)), KB.KB.r(K, KB.kball(~K, box, e)))))
    case SK.Ge0{+e}:
      KA.band(KB.held(~K, e), KA.kle(~K, N.nzero(K), KA.ksub(~K, KB.KB.c(K, KB.kball(~K, box, e)), KB.KB.r(K, KB.kball(~K, box, e)))))

def sides_ok(~K: N.Num, +box: List<&2, KB.KB<K>>, ss: List<&2, SK.Side>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{s, t}:
      KA.band(side_ok(~K, box, s), sides_ok(~K, box, t))

# every side condition holds over the box (radii not negative)
def check_sides(~K: N.Num, +sides: List<&2, SK.Side>, +gc: N.KVec(~K), +gr: N.KVec(~K)) -> Bool:
  KA.band(KA.kvle(~K, Nil{}, gr), sides_ok(~K, CK.zipb(~K, gc, gr), sides))
