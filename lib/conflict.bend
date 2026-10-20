# bend-cad: a conflict's support (PLAN-sk13a S3), by Chinneck's deletion
# filter. Constraint c with candidate premises cand has a degree-0
# refutation; each candidate in turn is dropped if c with the ones kept so
# far and the ones not yet tested still has one. What is left still
# refutes with c, and without any one of its members it does not
# (lib/conflictpf.bend). A support stands for all equations of its
# members (dropped ones included), their side conditions and c's, and the
# entities' sides.
#
# Untrusted in the sense of the rest of lib/: its properties are proven,
# nothing about it is assumed.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./refute.bend as RF

def lcat(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, lcat(t, ys)}

def lsnoc(xs: List<&2, Nat>, +y: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Con{y, Nil{}}
    case Con{h, t}:
      Con{h, lsnoc(t, y)}

# the premises c with the constraints cs stands for
def supp.es(+sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>) -> List<&2, E.QExpr>:
  SV.eqs_of(sk, Con{c, cs})

def supp.ss(+sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>) -> List<&2, SK.Side>:
  SK.cats(SV.csides(sk, Con{c, cs}), SV.esides(sk))

def issome(m: Maybe<&2, RF.Cert>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{c}:
      True{}

def refutable(+sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>) -> Bool:
  issome(RF.refute(supp.es(sk, c, cs), supp.ss(sk, c, cs)))

def kpick(b: Bool, +keep: List<&2, Nat>, +x: Nat) -> List<&2, Nat>:
  match b:
    case True{}:
      keep
    case False{}:
      lsnoc(keep, x)

def fcons(b: Bool, +x: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      r
    case False{}:
      Con{x, r}

# the candidates rest, tested in order, keep the ones already kept
def filt(rest: List<&2, Nat>, +sk: SK.Sketch, +c: Nat, +keep: List<&2, Nat>) -> List<&2, Nat>:
  match rest:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      +b = refutable(sk, c, lcat(keep, t))
      fcons(b, x, filt(t, sk, c, kpick(b, keep, x)))

def support(+sk: SK.Sketch, +c: Nat, cand: List<&2, Nat>) -> List<&2, Nat>:
  filt(cand, sk, c, Nil{})
