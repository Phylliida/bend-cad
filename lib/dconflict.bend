# bend-cad: refutations of both kinds, and a conflict's support
# (PLAN-sk13b B4.3). Constraint c with the constraints cs refutes when it
# does at degree 0 (lib/conflict.bend) or by directions: the closure of
# their facts in c's context cx (lib/dclose.bend) with the refutation
# decision (lib/dref.bend). The support is Chinneck's deletion filter
# again, with that test: each candidate in turn is dropped if c with the
# ones kept so far and the ones not yet tested still refutes. The
# conflict's nd is none when c with the support refutes at degree 0, else
# its direction refutation's nd without the Angles' segments, each segment
# once (lib/dconflictpf.bend).
#
# Untrusted in the sense of the rest of lib/: its properties are proven,
# nothing about it is assumed.

import Base
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/dir.bend as DR
import ./conflict.bend as CO
import ./pass.bend as PA
import ./dclose.bend as DC
import ./dref.bend as DF

# the constraints cs, each with its kind, for the refutation decision's
# Angle check (it reads only the Angles)
def angl.p(m: Maybe<&2, SK.Constraint>, +p: Nat, rest: List<&2, DF.Ang>) -> List<&2, DF.Ang>:
  match m:
    case Some{k}:
      Con{DF.Ang{p, k}, rest}
    case None{}:
      rest

def angl(+sk: SK.Sketch, cs: List<&2, Nat>) -> List<&2, DF.Ang>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{+p, t}:
      angl.p(SV.kind_at(sk, p), p, angl(sk, t))

# past every variable of the sketch (the closure's tag variable)
def tv(+sk: SK.Sketch) -> Nat:
  1n+PA.nvars(sk)

# the closure of the facts fs, in the context cx, with enough fuel
def dcl(+sk: SK.Sketch, +fs: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>) -> DC.Out:
  DC.dclose(SV.ents(sk), fs, cx, tv(sk), DC.dfuel(SV.ents(sk), fs))

# a direction refutation of c with the constraints cs, in the context cx
def dirref(+sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>, +cx: List<&2, E.QExpr>) -> Maybe<&2, DR.DRef>:
  DF.dref(dcl(sk, SV.rfacts(sk, Con{c, cs}), cx), SV.ents(sk), SV.rfacts(sk, Con{c, cs}), CO.supp.ss(sk, c, cs), angl(sk, Con{c, cs}))

def issome(m: Maybe<&2, DR.DRef>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{r}:
      True{}

def ref2.b(b: Bool, +sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>, +cx: List<&2, E.QExpr>) -> Bool:
  match b:
    case True{}:
      True{}
    case False{}:
      issome(dirref(sk, c, cs, cx))

# c with the constraints cs refutes: at degree 0, else by directions
def refutable2(+sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>, +cx: List<&2, E.QExpr>) -> Bool:
  ref2.b(CO.refutable(sk, c, cs), sk, c, cs, cx)

# the candidates rest, tested in order, keep the ones already kept
def filt2(rest: List<&2, Nat>, +sk: SK.Sketch, +c: Nat, +cx: List<&2, E.QExpr>, +keep: List<&2, Nat>) -> List<&2, Nat>:
  match rest:
    case Nil{}:
      Nil{}
    case Con{+x, +t}:
      +b = refutable2(sk, c, CO.lcat(keep, t), cx)
      CO.fcons(b, x, filt2(t, sk, c, cx, CO.kpick(b, keep, x)))

def support2(+sk: SK.Sketch, +c: Nat, +cx: List<&2, E.QExpr>, cand: List<&2, Nat>) -> List<&2, Nat>:
  filt2(cand, sk, c, cx, Nil{})

# The conflict's nd
# -----------------

def ndpick(b: Bool, +x: Nat, +acc: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      acc
    case False{}:
      CO.lsnoc(acc, x)

# xs without the entries of ys, each entry once, after acc
def ndclean(xs: List<&2, Nat>, +ys: List<&2, Nat>, +acc: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      acc
    case Con{+x, t}:
      ndclean(t, ys, ndpick(SV.bor(SV.mem(x, ys), SV.mem(x, acc)), x, acc))

def cnd.m(m: Maybe<&2, DR.DRef>, +sk: SK.Sketch, +c: Nat, +s: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case Some{r}:
      ndclean(DR.ref.nd(SV.ents(sk), SV.rfacts(sk, Con{c, s}), r), SV.angle_args(sk, Con{c, s}), Nil{})
    case None{}:
      Nil{}

def cnd.b(b: Bool, +sk: SK.Sketch, +c: Nat, +s: List<&2, Nat>, +cx: List<&2, E.QExpr>) -> List<&2, Nat>:
  match b:
    case True{}:
      Nil{}
    case False{}:
      cnd.m(dirref(sk, c, s, cx), sk, c, s)

# none at degree 0; else the direction refutation's, without the Angles'
# segments (their meanings make them nonzero), each segment once
def cnd(+sk: SK.Sketch, +c: Nat, +s: List<&2, Nat>, +cx: List<&2, E.QExpr>) -> List<&2, Nat>:
  cnd.b(CO.refutable(sk, c, s), sk, c, s, cx)
