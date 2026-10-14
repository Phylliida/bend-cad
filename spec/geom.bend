# bend-cad spec: plane geometry over the rationals, the vocabulary in which
# every constraint's meaning is stated (spec/sketch.bend, Constraint.means).
# Trusted. The definitions are the textbook ones, written without the
# equation forms' tricks: a point on a line is a + t(b - a) for some t,
# parallel vectors are multiples of each other, a mirror image has its
# midpoint on the mirror and its offset perpendicular to it.
#
# Equality is S.Q.eq (unreduced rationals) and order is S.Q.lt; the y axis
# points up, so positive orientation is counterclockwise. The exact solution
# of a sketch is real, not rational: see DESIGN §5.5 for how the meanings,
# stated here over Q, reach it.

import Base
import ./num.bend as S

# Rational constants
# ------------------

def Q.zero() -> S.Q:
  S.Q{S.Z0{}, S.XH{}}

def Q.one() -> S.Q:
  S.Q{S.Zpos{S.XH{}}, S.XH{}}

def Q.half() -> S.Q:
  S.Q{S.Zpos{S.XH{}}, S.XO{S.XH{}}}

# Vectors and points
# ------------------

type V2 is Data:
  V2{x: S.Q, y: S.Q}

def V2.x(v: V2) -> S.Q:
  match v:
    case V2{x, y}:
      x

def V2.y(v: V2) -> S.Q:
  match v:
    case V2{x, y}:
      y

def V2.zero() -> V2:
  V2{Q.zero(), Q.zero()}

# a = b
def V2.eq(+a: V2, +b: V2) -> Type:
  S.Q.eq(V2.x(a), V2.x(b)) & S.Q.eq(V2.y(a), V2.y(b))

# a ≠ b
def V2.ne(+a: V2, +b: V2) -> Type:
  V2.eq(a, b) -> Empty

def V2.add(+a: V2, +b: V2) -> V2:
  V2{S.Q.add(V2.x(a), V2.x(b)), S.Q.add(V2.y(a), V2.y(b))}

def V2.sub(+a: V2, +b: V2) -> V2:
  V2{S.Q.sub(V2.x(a), V2.x(b)), S.Q.sub(V2.y(a), V2.y(b))}

# t a
def V2.scale(+t: S.Q, +a: V2) -> V2:
  V2{S.Q.mul(t, V2.x(a)), S.Q.mul(t, V2.y(a))}

def V2.dot(+a: V2, +b: V2) -> S.Q:
  S.Q.add(S.Q.mul(V2.x(a), V2.x(b)), S.Q.mul(V2.y(a), V2.y(b)))

# the z part of the 3D cross product
def V2.cross(+a: V2, +b: V2) -> S.Q:
  S.Q.sub(S.Q.mul(V2.x(a), V2.y(b)), S.Q.mul(V2.y(a), V2.x(b)))

# |a|²
def V2.norm2(+a: V2) -> S.Q:
  V2.dot(a, a)

# a turned a quarter turn counterclockwise
def V2.perp(+a: V2) -> V2:
  V2{S.Q.neg(V2.y(a)), V2.x(a)}

# a turned by the rotation-and-scaling with matrix [[c, -s], [s, c]]
def V2.rot(+c: S.Q, +s: S.Q, +a: V2) -> V2:
  V2{S.Q.sub(S.Q.mul(c, V2.x(a)), S.Q.mul(s, V2.y(a))), S.Q.add(S.Q.mul(s, V2.x(a)), S.Q.mul(c, V2.y(a)))}

# the point a + t(b - a)
def V2.lerp(+a: V2, +b: V2, +t: S.Q) -> V2:
  V2.add(a, V2.scale(t, V2.sub(b, a)))

# the point midway between a and b
def V2.mid(+a: V2, +b: V2) -> V2:
  V2.scale(Q.half(), V2.add(a, b))

# twice the signed area of the triangle a, b, c: positive when c is left of
# the directed line a → b
def V2.orient(+a: V2, +b: V2, +c: V2) -> S.Q:
  V2.cross(V2.sub(b, a), V2.sub(c, a))

# Relations
# ---------

# the distance from p to q is d
def dist(+p: V2, +q: V2, +d: S.Q) -> Type:
  S.Q.lt(Q.zero(), d) & S.Q.eq(V2.norm2(V2.sub(q, p)), S.Q.mul(d, d))

# q is d to the right of p
def hdist(+p: V2, +q: V2, +d: S.Q) -> Type:
  S.Q.lt(Q.zero(), d) & S.Q.eq(S.Q.sub(V2.x(q), V2.x(p)), d)

# q is d above p
def vdist(+p: V2, +q: V2, +d: S.Q) -> Type:
  S.Q.lt(Q.zero(), d) & S.Q.eq(S.Q.sub(V2.y(q), V2.y(p)), d)

# segments a0 a1 and b0 b1 are proper and equally long
def equal_length(+a0: V2, +a1: V2, +b0: V2, +b1: V2) -> Type:
  V2.ne(a0, a1) & (V2.ne(b0, b1) & S.Q.eq(V2.norm2(V2.sub(a1, a0)), V2.norm2(V2.sub(b1, b0))))

# u and v are nonzero and v is a multiple of u
def parallel(+u: V2, +v: V2) -> Type:
  V2.ne(u, V2.zero()) & (V2.ne(v, V2.zero()) & Exists(S.Q, l => V2.eq(v, V2.scale(l, u))))

# v is parallel to u turned a quarter turn
def perpendicular(+u: V2, +v: V2) -> Type:
  parallel(V2.perp(u), v)

# p lies on the line through a and b
def on_line(+p: V2, +a: V2, +b: V2) -> Type:
  V2.ne(a, b) & Exists(S.Q, t => V2.eq(p, V2.lerp(a, b, t)))

# p lies strictly between a and b
def on_segment(+p: V2, +a: V2, +b: V2) -> Type:
  V2.ne(a, b) & Exists(S.Q, t => S.Q.lt(Q.zero(), t) & (S.Q.lt(t, Q.one()) & V2.eq(p, V2.lerp(a, b, t))))

# p is at distance d from the line through a and b, on its left: the foot f
# of the perpendicular from p is at distance d from p
def line_dist(+p: V2, +a: V2, +b: V2, +d: S.Q) -> Type:
  S.Q.lt(Q.zero(), V2.orient(a, b, p)) & Exists(V2, f => on_line(f, a, b) & (S.Q.eq(V2.dot(V2.sub(p, f), V2.sub(b, a)), Q.zero()) & dist(f, p, d)))

# q is the mirror image of p in the line through a and b: their midpoint is
# on the line and q - p is perpendicular to it (q = p when p is on the line)
def mirror(+p: V2, +q: V2, +a: V2, +b: V2) -> Type:
  on_line(V2.mid(p, q), a, b) & S.Q.eq(V2.dot(V2.sub(q, p), V2.sub(b, a)), Q.zero())

# v points along u turned by the rotation (c, s): with (c, s) = (cos θ,
# sin θ), θ is the counterclockwise angle from u to v
def angle(+u: V2, +v: V2, +c: S.Q, +s: S.Q) -> Type:
  V2.ne(u, V2.zero()) & (V2.ne(V2{c, s}, V2.zero()) & Exists(S.Q, l => S.Q.lt(Q.zero(), l) & V2.eq(v, V2.scale(l, V2.rot(c, s, u)))))
