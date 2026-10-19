# Demo: every §5.1 equation form evaluated on a small sketch with a known
# rational solution. A 4 × 3 rectangle ABDC with A fixed at the origin, the
# midpoint M of AB (B lies on the line A → M), a fixed point P and its mirror
# Q in AC, a circle about A through E = (3, 4), D at distance 3 left of the
# line A → B, the angle from AB to AE, a segment Z collapsed onto A, and
# zero distances (A to itself, A to C horizontally, B to the line AB).
# The checker computes everything below ({==}).

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as K

# n / d for small n, d
def q(n: Nat, d: Nat) -> S.Q:
  S.Q{S.Z.of_diff(n, 0n), S.Pos.of_succ(Nat.sub(d, 1n))}

def qneg(n: Nat) -> S.Q:
  S.Q{S.Z.of_diff(0n, n), S.XH{}}

def c(n: Nat) -> E.QExpr:
  E.QCst{q(n, 1n)}

def pt(id: Nat, x: Nat, y: Nat) -> K.Ent:
  K.Ent{id, False{}, K.GPoint{x, y}}

def sg(id: Nat, p: Nat, q: Nat) -> K.Ent:
  K.Ent{id, False{}, K.GSeg{p, q}}

# Variables: 0 Ax = Cx, 1 Ay = By = My, 2 Bx = Dx, 3 Cy = Dy, 4 Mx, 5 Px,
# 6 Py = Qy, 7 Qx, 8 Ex, 9 Ey, 10 the radius, 11 the aux length of AB.
# The merged points share variables here, which a sketch may still do: the
# merges' equations then read x - x = 0 and hold.
# Points 0 A, 1 B, 2 C, 3 D, 4 M, 5 P, 6 Q, 7 E; segments 10 AB, 11 CD,
# 12 AC, 13 AE, 14 AM, 15 Z = AA; circle 20 about A.
def ents() -> List<&2, K.Ent>:
  [pt(0n, 0n, 1n), pt(1n, 2n, 1n), pt(2n, 0n, 3n), pt(3n, 2n, 3n),
   pt(4n, 4n, 1n), pt(5n, 5n, 6n), pt(6n, 7n, 6n), pt(7n, 8n, 9n),
   sg(10n, 0n, 1n), sg(11n, 2n, 3n), sg(12n, 0n, 2n), sg(13n, 0n, 7n),
   sg(14n, 0n, 4n), sg(15n, 0n, 0n),
   K.Ent{20n, False{}, K.GCirc{0n, 10n}}]

def cons() -> List<&2, K.Constraint>:
  [K.Fix{0n, q(0n, 1n)}, K.Fix{1n, q(0n, 1n)},
   K.Horizontal{0n, 1n}, K.Vertical{0n, 2n}, K.Vertical{1n, 3n},
   K.Horizontal{2n, 3n}, K.Horizontal{0n, 4n}, K.Horizontal{5n, 6n},
   K.HDistance{0n, 1n, c(4n)}, K.VDistance{0n, 2n, c(3n)},
   K.Perpendicular{10n, 12n}, K.Parallel{10n, 11n}, K.EqualLength{10n, 11n},
   K.Midpoint{4n, 10n}, K.OnLine{4n, 10n}, K.OnLine{1n, 14n},
   K.Fix{5n, q(1n, 1n)}, K.Fix{6n, q(1n, 1n)}, K.Symmetric{5n, 6n, 12n},
   K.Radius{20n, c(5n)}, K.Diameter{20n, c(10n)}, K.OnCircle{7n, 20n},
   K.Distance{0n, 7n, c(5n)},
   K.LineDistance{3n, 10n, False{}, c(3n), 11n},
   K.Angle{10n, False{}, 13n, False{}, E.QCst{q(3n, 5n)}, E.QCst{q(4n, 5n)}},
   K.Parallel{10n, 15n}, K.Perpendicular{15n, 12n}, K.OnLine{5n, 15n},
   K.Distance{0n, 0n, c(0n)}, K.HDistance{0n, 2n, c(0n)},
   K.LineDistance{1n, 10n, False{}, c(0n), 11n}]

def good() -> List<&2, S.Q>:
  [q(0n, 1n), q(0n, 1n), q(4n, 1n), q(3n, 1n), q(2n, 1n), q(1n, 1n),
   q(1n, 1n), qneg(1n), q(3n, 1n), q(4n, 1n), q(5n, 1n), q(4n, 1n)]

# E moved to (4, 3): still on the circle, but the angle is now wrong
def bad() -> List<&2, S.Q>:
  [q(0n, 1n), q(0n, 1n), q(4n, 1n), q(3n, 1n), q(2n, 1n), q(1n, 1n),
   q(1n, 1n), qneg(1n), q(4n, 1n), q(3n, 1n), q(5n, 1n), q(4n, 1n)]

# A decision procedure for the demo (untrusted): every equation is 0 and
# every side condition positive, over the rationals.
def same(o: Cmp, want: Cmp) -> Bool:
  match o want:
    case LT{} LT{}:
      True{}
    case EQ{} EQ{}:
      True{}
    case GT{} GT{}:
      True{}
    case _ _:
      False{}

def all(+env: List<&2, S.Q>, +want: Cmp, xs: List<&2, E.QExpr>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(same(S.Q.cmp(E.qeval(env, h), S.Q{S.Z0{}, S.XH{}}), want), all(env, want, t))

def sides(+env: List<&2, S.Q>, xs: List<&2, K.Side>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{K.Gt0{e}, t}:
      Bool.and(same(S.Q.cmp(E.qeval(env, e), S.Q{S.Z0{}, S.XH{}}), GT{}), sides(env, t))
    case Con{K.Ge0{+e}, t}:
      Bool.and(Bool.or(same(S.Q.cmp(E.qeval(env, e), S.Q{S.Z0{}, S.XH{}}), GT{}), same(S.Q.cmp(E.qeval(env, e), S.Q{S.Z0{}, S.XH{}}), EQ{})), sides(env, t))

def ok(+env: List<&2, S.Q>, ks: List<&2, K.Constraint>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case Con{+k, t}:
      Bool.and(Bool.and(all(env, EQ{}, K.Constraint.eqs(ents(), k)), sides(env, K.Constraint.sides(ents(), k))), ok(env, t))

def good_ok() -> {ok(good(), cons()) == True{} : Bool}:
  {==}

def bad_fails() -> {ok(bad(), cons()) == False{} : Bool}:
  {==}

# D is left of A → B, so it is not at distance 3 on the left of B → A
def wrong_side() -> {ok(good(), [K.LineDistance{3n, 10n, True{}, c(3n), 11n}]) == False{} : Bool}:
  {==}

# |AE| = 5, but a distance is never negative
def negative() -> {ok(good(), [K.Distance{0n, 7n, E.QCst{qneg(5n)}}]) == False{} : Bool}:
  {==}

# B is 4 right of A, not A 4 right of B
def reversed() -> {ok(good(), [K.HDistance{1n, 0n, c(4n)}]) == False{} : Bool}:
  {==}

# References resolve to the entities they name
def refs_ok() -> K.Constraint.wf_refs(ents(), K.Symmetric{5n, 6n, 12n}):
  ({==}, ({==}, {==}))

# Merges are equations (D3 as revised): they ask nothing beyond their
# references, and one between points that differ fails (P is at height 1,
# E at height 4)
def merge_ok() -> K.Constraint.wf(ents(), K.Horizontal{0n, 1n}):
  Unit{}

def merge_fails() -> {ok(good(), [K.Horizontal{5n, 7n}]) == False{} : Bool}:
  {==}

# a segment id is not a point
def wrong_kind() -> {K.is_pt(K.find(10n, ents())) == False{} : Bool}:
  {==}

# a dangling id names nothing
def dangling() -> {K.is_seg(K.find(99n, ents())) == False{} : Bool}:
  {==}
