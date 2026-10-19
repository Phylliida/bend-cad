# bend-cad: the sk-09 red stage's witnesses (lib/solve.bend: red_of,
# why_of), with what they mean. These were spec/solve.bend's until
# sk-13a's classes took their place (S0b, 2026-10-19); now they are only
# facts about the old stage, used by its proofs (lib/redpf.bend,
# lib/totalpf.bend) until the sk-13a stage replaces it (PLAN-sk13a.md S4).
# Untrusted: no law mentions them. Structure here is syntactic (inside reads
# the expression tree); the spec's Overdet reads dependence (Q30).

import Base
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV

def all_inside(+es: List<&2, E.QExpr>, s: List<&2, Nat>, +w: List<&2, Nat>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case Con{j, t}:
      SV.band(SV.inside(SV.eqat(es, j), w), all_inside(es, t, w))

# s names distinct equations of es, every variable they use is in w, and w
# is shorter than s
def overdet(+es: List<&2, E.QExpr>, +s: List<&2, Nat>, +w: List<&2, Nat>) -> Bool:
  SV.band(SV.distinct(s), SV.band(SV.below(s, SV.neqs(es)), SV.band(SV.lt(SV.len(w), SV.len(s)), all_inside(es, s, w))))


# every equation of s is owned by c or by a constraint not in red
def clean(+own: List<&2, Nat>, +red: List<&2, Nat>, +c: Nat, s: List<&2, Nat>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case Con{+k, t}:
      SV.band(SV.bor(SV.eq(SV.nth(own, k), c), SV.bnot(SV.mem(SV.nth(own, k), red))), clean(own, red, c, t))

# why the constraint at a position is red: equation j, which it owns,
# lies in the over-determined set s (whose variables are among w)
type Why is Data:
  Why{j: Nat, s: List<&2, Nat>, w: List<&2, Nat>}

# each red constraint (rs, in order) is explained by the matching Why,
# red being the whole list
def explained.go(+sk: SK.Sketch, +red: List<&2, Nat>, rs: List<&2, Nat>, why: List<&2, Why>) -> Bool:
  match rs why:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, yt}:
      False{}
    case Con{c, rt} Nil{}:
      False{}
    case Con{+c, rt} Con{Why{+j, +s, +w}, yt}:
      SV.band(SV.eq(SV.nth(SV.owners(sk), j), c), SV.band(SV.mem(j, s), SV.band(overdet(SK.Sketch.eqs(sk), s, w), SV.band(clean(SV.owners(sk), red, c, s), explained.go(sk, red, rt, yt)))))

def explained(+sk: SK.Sketch, +red: List<&2, Nat>, why: List<&2, Why>) -> Bool:
  explained.go(sk, red, red, why)
