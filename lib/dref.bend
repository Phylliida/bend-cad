# bend-cad: the direction layer's refutation decision (PLAN-sk13b B3,
# "The refutation decision"). At the closure's result for the facts fs,
# with the side conditions ss and the Angles among the constraints refuted:
# - 1 in K: Motzkin's refutation by that fact alone (-1 times it is -1);
# - an open segment's direction in K squared: a derived collapse;
# - at a fixpoint: sk-13a's refute over K's generators and the sides,
#   else an Angle whose first or second segment has its direction in K
#   squared, else none.
# A refutation is found iff one exists (lib/drefpf.bend).
#
# Untrusted in the sense of the rest of lib/: its properties are proven,
# nothing about it is assumed.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./kspace.bend as KS
import ./refute.bend as RF
import ./dclose.bend as DC

# an Angle among the constraints refuted: its position and kind
type Ang is Data:
  Ang{p: Nat, k: SK.Constraint}

def qm1() -> S.Q:
  S.Q{S.Zneg{S.XH{}}, S.XH{}}

# 0 for each side
def zq(ss: List<&2, SK.Side>) -> List<&2, S.Q>:
  match ss:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{DR.qz(), zq(t)}

def ang.pick(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +s: Nat, +p: Nat, +fst: Bool, rest: Maybe<&2, DR.DRef>) -> Maybe<&2, DR.DRef>:
  match b:
    case True{}:
      Some{DR.RAngle{KS.ks.der(es, fs, k, SK.VE.x(DR.zseg(es, s))), KS.ks.der(es, fs, k, SK.VE.y(DR.zseg(es, s))), p, fst}}
    case False{}:
      rest

def ang.seg(m: Maybe<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +p: Nat, +fst: Bool, rest: Maybe<&2, DR.DRef>) -> Maybe<&2, DR.DRef>:
  match m:
    case None{}:
      rest
    case Some{+s}:
      ang.pick(DC.fullc(es, k, s), es, fs, k, s, p, fst, rest)

# the first Angle with a segment whose direction is in K squared
def angs(as: List<&2, Ang>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS) -> Maybe<&2, DR.DRef>:
  match as:
    case Nil{}:
      None{}
    case Con{Ang{+p, +kc}, t}:
      ang.seg(DR.angle_seg(kc, True{}), es, fs, k, p, True{}, ang.seg(DR.angle_seg(kc, False{}), es, fs, k, p, False{}, angs(t, es, fs, k)))

def dref.fix(m: Maybe<&2, RF.Cert>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +as: List<&2, Ang>) -> Maybe<&2, DR.DRef>:
  match m:
    case Some{RF.Cert{+ls, +ms, +kk}}:
      Some{DR.RMotz{KS.ks.ds(k), ls, ms, kk}}
    case None{}:
      angs(as, es, fs, k)

# a refutation at the closure's result o, if there is one
def dref(o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ss: List<&2, SK.Side>, +as: List<&2, Ang>) -> Maybe<&2, DR.DRef>:
  match o:
    case DC.OStep{s}:
      None{}
    case DC.OFix{+s}:
      dref.fix(RF.refute(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), ss), es, fs, DC.Sk.k(s), as)
    case DC.OOne{+d}:
      Some{DR.RMotz{Con{d, Nil{}}, Con{qm1(), Nil{}}, zq(ss), qm1()}}
    case DC.OVoid{+g, +dr, +di}:
      Some{DR.RColl{dr, di, g}}
