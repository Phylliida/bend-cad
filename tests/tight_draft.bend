# sk-13b B8b C0 (PLAN-sk13b.md): the draft spec/_draft13c.bend, kept
# checking until it replaces Honest in spec/solve.bend (C5), when this
# file is retired. Nothing is proven against the draft yet.
# - Its Honest implies spec/solve.bend's (weaken), so every law proven
#   from that one holds for it.
# - On an example (tests/dir_laws.bend's two segments, with five
#   constraints and a class of each shape; not an honest classification),
#   Tight unfolds to one statement per witness and Unit elsewhere: given
#   those statements, t_tight builds Tight from them. The sets the
#   statements read are checked by {==}.

import Base
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ../spec/solve.bend as SV
import ../spec/_draft13c.bend as T

# the draft's Honest is spec/solve.bend's with more clauses
def weaken(+sk: SK.Sketch, +cls: List<&2, SV.Class>, h: T.Honest(sk, cls)) -> SV.Honest(sk, cls):
  match h:
    case (a, b):
      a

# The example
# -----------

def es() -> List<&2, SK.Ent>:
  [SK.Ent{0n, False{}, SK.GPoint{0n, 1n}}, SK.Ent{1n, False{}, SK.GPoint{2n, 3n}}, SK.Ent{2n, False{}, SK.GPoint{4n, 5n}}, SK.Ent{10n, False{}, SK.GSeg{0n, 1n}}, SK.Ent{11n, False{}, SK.GSeg{1n, 2n}}]

# #0 Parallel, #1 Perpendicular, #2 Horizontal, #3 Vertical, each one
# equation (0 to 3), and #4 a driven Coincident (none)
def sk() -> SK.Sketch:
  SK.Sketch{[SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}, SK.Coord{}], es(), [SK.Rec{0n, False{}, SK.Parallel{10n, 11n}}, SK.Rec{1n, False{}, SK.Perpendicular{10n, 11n}}, SK.Rec{2n, False{}, SK.Horizontal{0n, 1n}}, SK.Rec{3n, False{}, SK.Vertical{1n, 2n}}, SK.Rec{4n, True{}, SK.Coincident{0n, 2n}}]}

def dre() -> DR.Der:
  DR.DLine{DR.DPPrem{0n}, DR.DPPrem{1n}, True{}}

# a direction drop, a conflict, an Over, an amber with a constant
# combination, and the driven constraint kept
def cls() -> List<&2, SV.Class>:
  [SV.Kept{[SV.Drop{0n, [10n], SV.WDer{dre()}}]}, SV.Conflict{[0n], [10n, 11n]}, SV.Over{2n, [1n, 2n], [1n, 3n]}, SV.Amber{[SV.Drop{3n, Nil{}, SV.WLin{Nil{}}}], Nil{}}, SV.Kept{Nil{}}]

# Tight on it: the direction drop's nd (#0, its drops [0], red #1 and #2),
# the conflict's nd, the Over set; nothing for the constant combination
# or the driven constraint
def t_tight(h0: T.NdIrred(sk(), cls(), [1n, 2n], 0n, [0n], 0n, [10n]), h1: T.RefIrred(sk(), [1n, 2n], 1n, [0n], [10n, 11n]), h2: T.OverIrred(SK.Sketch.eqs(sk()), [1n, 2n])) -> T.Tight(sk(), cls()):
  ((h0, Unit{}), (h1, (h2, ((Unit{}, Unit{}), (Unit{}, Unit{})))))

# the drop without seg 10: no segment
def t_nd() -> {SV.unmark(10n, [10n]) == Nil{} : List<&2, Nat>}:
  {==}

# the conflict without seg 11: seg 10 (no Angle among #1 and #0)
def t_ref() -> {SV.cat(SV.unmark(11n, [10n, 11n]), SV.angle_args(sk(), [1n, 0n])) == [10n] : List<&2, Nat>}:
  {==}

# the Over set without equation 1: equation 2, #2's
def t_over() -> {SV.picked(SK.Sketch.eqs(sk()), SV.unmark(1n, [1n, 2n])) == SK.Constraint.eqs(es(), SK.Horizontal{0n, 1n}) : List<&2, E.QExpr>}:
  {==}
