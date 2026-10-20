# bend-cad: degree-0 refutations (PLAN-sk13a S3), restated here so the gate
# checks lib/termpf.bend, lib/unsatpf.bend, lib/refpf.bend, lib/satpf.bend
# and lib/conflictpf.bend until the solver's single pass (S4) imports them:
# - the simplex finishes on every well-formed problem;
# - refute decides refutability: its certificate is a Motzkin refutation
#   (the spec's Refutes0), and no certificate means none exists;
# - the deletion filter's support is a conflict's (the spec's ConflictOk).
# With x > 0 and -x > 0 there is one; with x > 0 alone there is none.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../lib/simplex.bend as SX
import ../lib/simppf.bend as SP
import ../lib/runpf.bend as RN
import ../lib/termpf.bend as TP
import ../lib/refute.bend as RF
import ../lib/satpf.bend as ST
import ../lib/conflict.bend as CO
import ../lib/conflictpf.bend as CP

def solve_ends(+lp: SX.LP, hwf: {SP.lpwf(lp) == True{} : Bool}) -> {RN.isgo(SX.solve(lp)) == False{} : Bool}:
  TP.solve_ends(lp, hwf)

def refute_ok(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>) -> ST.RefOk(es, ss, RF.refute(es, ss)):
  ST.refute_ok(es, ss)

# Demo
# ----

def issome(m: Maybe<&2, RF.Cert>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{c}:
      True{}

def x() -> E.QExpr:
  E.QVar{0n}

def demo_refuted() -> {issome(RF.refute(Nil{}, [SK.Gt0{x()}, SK.Gt0{E.QNeg{x()}}])) == True{} : Bool}:
  {==}

def demo_feasible() -> {issome(RF.refute(Nil{}, [SK.Gt0{x()}])) == False{} : Bool}:
  {==}

# a conflict's support: the deletion filter over candidates that are
# distinct, before c, driving and not red, with which c refutes
def conflict_ok(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat, +cand: List<&2, Nat>,
  +hc: {SV.band(SV.distinct(cand), SV.band(SV.below(cand, c), SV.band(SV.all_driving(sk, cand), SV.none_in(cand, red)))) == True{} : Bool},
  hr: {CO.refutable(sk, c, cand) == True{} : Bool}) -> SV.ConflictOk(sk, red, c, CO.support(sk, c, cand)):
  CP.conflict_ok(sk, red, c, cand, hc, hr)
