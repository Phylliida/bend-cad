# bend-cad spec, sk-13b B8b: every witness the answer names is irreducible.
# (DRAFT, PLAN-sk13b B8b C0: replaces Honest in spec/solve.bend at C5.)
#
# spec/solve.bend's Honest lets the solver pick some witnesses, and asks
# only that each be valid:
# - a direction drop's nd is exactly what its derivation needs, but
#   another derivation may need fewer segments;
# - a direction conflict's nd is exactly what its refutation needs, but
#   another refutation (of the same constraints) may need fewer;
# - an Over set has more equations than variables, but may hold
#   equations it does not need.
# A segment named but not needed reads as a way out ("unless L12 has
# length 0") when nothing depends on it, and the verdict checks it nonzero
# for nothing. Honest here adds, for each witness, that it is
# irreducible: without any one of its members, no witness of the same
# kind exists.
# - Irreducible is not fewest: when two different sets each suffice, the
#   answer names one, and the other may be smaller (the fewest is a
#   sparsest-combination problem).
# - Within the calculus: a segment of nd is one no derivation (refutation)
#   of spec/dir.bend can do without. A drop's facts carry the earlier
#   drops' nd, but the facts those drops were derived from are facts here
#   too, so a derivation may derive an earlier drop's equation another
#   way. A segment may still be nonzero for a reason the calculus does not
#   read (an Angle's or a LineDistance's side; a conflict leaves out the
#   segments of its Angles, a drop does not).
# - The types and the rest of Honest are spec/solve.bend's, so Honest
#   here implies that Honest (and every law proven from it), and the
#   classes it allows are a subset of those.

import Base
import ./ring.bend as E
import ./sketch.bend as SK
import ./dir.bend as DR
import ./solve.bend as SV

# Drops: each segment of a derivation's nd is needed
# ---------------------------------------------------

# c's i-th equation has no direction-layer derivation (from the facts it
# may read, in c's context) whose nd lies within A
def NotDirDerivableIn(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +i: Nat, +A: List<&2, Nat>) -> Type:
  @dv: DR.Der -> DR.Valid(SV.ents(sk), SV.dfacts(sk, cls, red, c, d, i), SV.ctx(sk, red, c), dv) -> SV.Proves(SV.ents(sk), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c)), SV.eqat(SK.Sketch.eqs(sk), i), DR.concl(SV.ents(sk), SV.dfacts(sk, cls, red, c, d, i), dv)) -> {SV.sub(DR.nd(SV.ents(sk), SV.dfacts(sk, cls, red, c, d, i), dv), A) == True{} : Bool} -> Empty

# nd is irreducible for c's i-th equation: without any one of its
# segments, no derivation. A constant combination of the solved equations
# is a derivation with no nd, so a direction drop with nd has none.
def NdIrred(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +i: Nat, +nd: List<&2, Nat>) -> Type:
  @m: Nat -> {SV.mem(m, nd) == True{} : Bool} -> NotDirDerivableIn(sk, cls, red, c, d, i, SV.unmark(m, nd))

def Tight.why(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +j: Nat, +nd: List<&2, Nat>, w: SV.Why) -> Type:
  match w:
    case SV.WLin{ms}:
      Unit
    case SV.WDer{dv}:
      NdIrred(sk, cls, red, c, d, j, nd)

# each direction drop of dd (c's drops, d their positions) has an
# irreducible nd (a constant combination's is none)
def Tight.drops(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, dd: List<&2, SV.Drop>) -> Type:
  match dd:
    case Nil{}:
      Unit
    case Con{SV.Drop{+j, +nd, w}, t}:
      Tight.why(sk, cls, red, c, d, j, nd, w) & Tight.drops(sk, cls, red, c, d, t)

# Conflicts: each segment of a refutation's nd is needed
# -------------------------------------------------------

# c with the constraints cs has no direction refutation (in the context
# cx) whose nd lies within A
def NoDirRefIn(+sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>, +cx: List<&2, E.QExpr>, +A: List<&2, Nat>) -> Type:
  @r: DR.DRef -> SV.RefOk(sk, c, cs, cx, r) -> {SV.sub(DR.ref.nd(SV.ents(sk), SV.rfacts(sk, Con{c, cs}), r), A) == True{} : Bool} -> Empty

# a conflict's nd (with its support s) is irreducible: without any one of
# its segments, and with the segments of Angles among c and s (which their
# meanings make nonzero), no direction refutation. A degree-0 refutation
# is a direction one with no nd, so a conflict with nd has none; and nd
# has no segment of an Angle among them (the refutation that gives nd
# would do without it).
def RefIrred(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat, +s: List<&2, Nat>, +nd: List<&2, Nat>) -> Type:
  @m: Nat -> {SV.mem(m, nd) == True{} : Bool} -> NoDirRefIn(sk, c, s, SV.ctx(sk, red, c), SV.cat(SV.unmark(m, nd), SV.angle_args(sk, Con{c, s})))

# Over sets: each equation is needed
# ----------------------------------

# without any one equation of s, the rest of es at s are matchable (each
# its own variable it depends on): s is an inclusion-minimal
# over-determined set. With Overdet's w, shorter than s and holding every
# variable s depends on, w is then exactly those variables, each once.
def OverIrred(+es: List<&2, E.QExpr>, +s: List<&2, Nat>) -> Type:
  @e: Nat -> {SV.mem(e, s) == True{} : Bool} -> SV.Matchable(SV.picked(es, SV.unmark(e, s)))

# Honest, irreducibly
# -------------------

# the witnesses of a driving constraint's class are irreducible
def Tight.driving(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +c: Nat, k: SV.Class) -> Type:
  match k:
    case SV.Kept{+dd}:
      Tight.drops(sk, cls, red, c, SV.drops(dd), dd)
    case SV.Amber{+dd, rs}:
      Tight.drops(sk, cls, red, c, SV.drops(dd), dd)
    case SV.Over{j, +s, w}:
      OverIrred(SK.Sketch.eqs(sk), s)
    case SV.Conflict{+s, +nd}:
      RefIrred(sk, red, c, s, nd)

# a driven constraint names no witness
def Tight.pick(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +red: List<&2, Nat>, +c: Nat, b: Bool, +k: SV.Class) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Tight.driving(sk, cls, red, c, k)

def Tight.at(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +c: Nat) -> Type:
  Tight.pick(sk, cls, SV.reds(cls), c, SV.driven(sk, c), SV.class_at(cls, c))

def Tight.go(+sk: SK.Sketch, +cls: List<&2, SV.Class>, n: Nat, +c: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+m:
      Tight.at(sk, cls, c) & Tight.go(sk, cls, m, 1n+c)

# every constraint's witnesses are irreducible
def Tight(+sk: SK.Sketch, +cls: List<&2, SV.Class>) -> Type:
  Tight.go(sk, cls, SV.ncons(sk), 0n)

# an honest classification whose witnesses are irreducible
def Honest(+sk: SK.Sketch, +cls: List<&2, SV.Class>) -> Type:
  SV.Honest(sk, cls) & Tight(sk, cls)
