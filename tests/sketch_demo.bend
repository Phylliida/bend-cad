# Demo: every §5.1 equation form evaluated on a small sketch with a known
# rational solution. A 4 × 3 rectangle ABDC with A fixed at the origin, the
# midpoint M of AB (B lies on the line A → M), a fixed point P and its mirror
# Q in AC, a circle about A through E = (3, 4), D at distance 3 left of the
# line A → B, and the angle from AB to AE. The checker computes everything
# below ({==}).

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/geom.bend as G
import ../spec/sketch.bend as K

# n / d for small n, d
def q(n: Nat, d: Nat) -> S.Q:
  S.Q{S.Z.of_diff(n, 0n), S.Pos.of_succ(Nat.sub(d, 1n))}

def qneg(n: Nat) -> S.Q:
  S.Q{S.Z.of_diff(0n, n), S.XH{}}

def c(n: Nat) -> E.QExpr:
  E.QCst{q(n, 1n)}

# variables: 0 Ax = Cx, 1 Ay = By = My, 2 Bx = Dx, 3 Cy = Dy, 4 Mx, 5 Px,
# 6 Py = Qy, 7 Qx, 8 Ex, 9 Ey, 10 the radius, 11 the aux length of AB
def A() -> K.Pt:
  K.Pt{0n, 1n}

def B() -> K.Pt:
  K.Pt{2n, 1n}

def C() -> K.Pt:
  K.Pt{0n, 3n}

def D() -> K.Pt:
  K.Pt{2n, 3n}

def M() -> K.Pt:
  K.Pt{4n, 1n}

def P() -> K.Pt:
  K.Pt{5n, 6n}

def Qp() -> K.Pt:
  K.Pt{7n, 6n}

def Ep() -> K.Pt:
  K.Pt{8n, 9n}

def AB() -> K.Seg:
  K.Seg{A(), B()}

def CD() -> K.Seg:
  K.Seg{C(), D()}

def AC() -> K.Seg:
  K.Seg{A(), C()}

def AE() -> K.Seg:
  K.Seg{A(), Ep()}

def circ() -> K.Circ:
  K.Circ{A(), 10n}

def cons() -> List<&2, K.Constraint>:
  [K.Fix{0n, q(0n, 1n)}, K.Fix{1n, q(0n, 1n)},
   K.Horizontal{A(), B()}, K.Vertical{A(), C()}, K.Vertical{B(), D()},
   K.Horizontal{C(), D()}, K.Horizontal{A(), M()}, K.Horizontal{P(), Qp()},
   K.HDistance{A(), B(), c(4n)}, K.VDistance{A(), C(), c(3n)},
   K.Perpendicular{AB(), AC()}, K.Parallel{AB(), CD()}, K.EqualLength{AB(), CD()},
   K.Midpoint{M(), A(), B()}, K.OnSegment{M(), AB()}, K.OnLine{B(), K.Seg{A(), M()}},
   K.Fix{5n, q(1n, 1n)}, K.Fix{6n, q(1n, 1n)}, K.Symmetric{P(), Qp(), AC()},
   K.Radius{circ(), c(5n)}, K.Diameter{circ(), c(10n)}, K.OnCircle{Ep(), circ()},
   K.Distance{A(), Ep(), c(5n)},
   K.LineDistance{D(), AB(), c(3n), 11n},
   K.Angle{AB(), AE(), E.QCst{q(3n, 5n)}, E.QCst{q(4n, 5n)}}]

def good() -> List<&2, S.Q>:
  [q(0n, 1n), q(0n, 1n), q(4n, 1n), q(3n, 1n), q(2n, 1n), q(1n, 1n),
   q(1n, 1n), qneg(1n), q(3n, 1n), q(4n, 1n), q(5n, 1n), q(4n, 1n)]

# E moved to (4, 3): still on the circle, but the angle is now wrong
def bad() -> List<&2, S.Q>:
  [q(0n, 1n), q(0n, 1n), q(4n, 1n), q(3n, 1n), q(2n, 1n), q(1n, 1n),
   q(1n, 1n), qneg(1n), q(4n, 1n), q(3n, 1n), q(5n, 1n), q(4n, 1n)]

# A decision procedure for the demo (untrusted): every equation is 0 and
# every side condition positive.
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

def all(+env: List<&2, S.Q>, +want: Cmp, es: List<&2, E.QExpr>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{h, t}:
      Bool.and(same(S.Q.cmp(E.qeval(env, h), G.Q.zero()), want), all(env, want, t))

def ok(+env: List<&2, S.Q>, ks: List<&2, K.Constraint>) -> Bool:
  match ks:
    case Nil{}:
      True{}
    case Con{+k, t}:
      Bool.and(Bool.and(all(env, EQ{}, K.Constraint.eqs(k)), all(env, GT{}, K.Constraint.sides(k))), ok(env, t))

def good_ok() -> {ok(good(), cons()) == True{} : Bool}:
  {==}

def bad_fails() -> {ok(bad(), cons()) == False{} : Bool}:
  {==}

# D is left of A → B, so it is not at distance 3 on the left of B → A
def wrong_side() -> {ok(good(), [K.LineDistance{D(), K.Seg{B(), A()}, c(3n), 11n}]) == False{} : Bool}:
  {==}

# B is on the line through A and M, past M, so not on the segment AM
def past_end() -> {ok(good(), [K.OnSegment{B(), K.Seg{A(), M()}}]) == False{} : Bool}:
  {==}

# Meanings at the solution, with their witnesses
# ----------------------------------------------

# a rewrite motive refuting Z0 == nonzero
def nz(z: S.Z) -> Type:
  match z:
    case S.Z0{}:
      Unit
    case S.Zpos{p}:
      Empty
    case S.Zneg{p}:
      Empty

# and nonzero == Z0
def zn(z: S.Z) -> Type:
  match z:
    case S.Z0{}:
      Empty
    case S.Zpos{p}:
      Unit
    case S.Zneg{p}:
      Unit

def env() -> List<&2, S.Q>:
  good()

def at(p: K.Pt) -> G.V2:
  K.Pt.at(env(), p)

# A ≠ B: their x coordinates are 0 and 4
def ab_ne(h: G.V2.eq(at(A()), at(B()))) -> Empty:
  (hx, hy) = h
  %hx : nz(_)
  Unit{}

# M is strictly inside AB, at t = 1/2
def m_onseg() -> K.Constraint.means(env(), K.OnSegment{M(), AB()}):
  (h => ab_ne(h), (q(1n, 2n), ({==}, ({==}, ({==}, {==})))))

# Q mirrors P in AC: the midpoint (0, 1) is on AC at t = 1/3
def ac_ne(h: G.V2.eq(at(A()), at(C()))) -> Empty:
  (hx, hy) = h
  %hy : nz(_)
  Unit{}

def q_mirror() -> K.Constraint.means(env(), K.Symmetric{P(), Qp(), AC()}):
  ((h => ac_ne(h), (q(1n, 3n), ({==}, {==}))), {==})

# D is 3 left of A → B (length 4): the foot of its perpendicular is (4, 0)
def d_linedist() -> K.Constraint.means(env(), K.LineDistance{D(), AB(), c(3n), 11n}):
  (({==}, {==}), ({==}, (G.V2{q(4n, 1n), q(0n, 1n)}, ((h => ab_ne(h), (q(1n, 1n), ({==}, {==}))), ({==}, ({==}, {==}))))))

# AE is AB turned by (3/5, 4/5), scaled by 5/4
def u_ne(h: G.V2.eq(G.V2.sub(at(B()), at(A())), G.V2.zero())) -> Empty:
  (hx, hy) = h
  %hx : zn(_)
  Unit{}

def cs_ne(h: G.V2.eq(G.V2{q(3n, 5n), q(4n, 5n)}, G.V2.zero())) -> Empty:
  (hx, hy) = h
  %hx : zn(_)
  Unit{}

def e_angle() -> K.Constraint.means(env(), K.Angle{AB(), AE(), E.QCst{q(3n, 5n)}, E.QCst{q(4n, 5n)}}):
  (h => u_ne(h), (h => cs_ne(h), (q(5n, 4n), ({==}, ({==}, {==})))))
