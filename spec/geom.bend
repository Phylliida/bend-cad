# bend-cad spec: plane geometry over an ordered field F, the vocabulary in
# which every constraint's meaning is stated (spec/sketch.bend,
# Constraint.means). Trusted. The definitions are the textbook ones, written
# without the equation forms' tricks: parallel directions are multiples of
# each other, a point on a segment is a + t(b - a) with 0 < t < 1, a mirror
# image has its midpoint on the mirror and its offset perpendicular to it.
#
# Geometry may degenerate: a segment can collapse to a point. A relation
# that needs a direction then holds vacuously (a zero vector is parallel to
# every vector), exactly as its equation does. The y axis points up, so
# positive orientation is counterclockwise.

import Base
import ./num.bend as S
import ./field.bend as O

type V2<-A: Data> is Data:
  V2{x: A, y: A}

# a vector, or a point, with coordinates in F
def Vec(~F: O.OField) -> Data:
  V2<O.C(F)>

def x(~F: O.OField, v: Vec(~F)) -> O.C(F):
  match v:
    case V2{x, y}:
      x

def y(~F: O.OField, v: Vec(~F)) -> O.C(F):
  match v:
    case V2{x, y}:
      y

def vzero(~F: O.OField) -> Vec(~F):
  V2{O.zero(F), O.zero(F)}

# a ≠ b
def ne(~F: O.OField, +a: Vec(~F), +b: Vec(~F)) -> Type:
  {a == b : Vec(~F)} -> Empty

def add(~F: O.OField, +a: Vec(~F), +b: Vec(~F)) -> Vec(~F):
  V2{O.add(F, x(~F, a), x(~F, b)), O.add(F, y(~F, a), y(~F, b))}

def sub(~F: O.OField, +a: Vec(~F), +b: Vec(~F)) -> Vec(~F):
  V2{O.sub(~F, x(~F, a), x(~F, b)), O.sub(~F, y(~F, a), y(~F, b))}

# t a
def scale(~F: O.OField, +t: O.C(F), +a: Vec(~F)) -> Vec(~F):
  V2{O.mul(F, t, x(~F, a)), O.mul(F, t, y(~F, a))}

def dot(~F: O.OField, +a: Vec(~F), +b: Vec(~F)) -> O.C(F):
  O.add(F, O.mul(F, x(~F, a), x(~F, b)), O.mul(F, y(~F, a), y(~F, b)))

# the z part of the 3D cross product
def cross(~F: O.OField, +a: Vec(~F), +b: Vec(~F)) -> O.C(F):
  O.sub(~F, O.mul(F, x(~F, a), y(~F, b)), O.mul(F, y(~F, a), x(~F, b)))

# |a|²
def norm2(~F: O.OField, +a: Vec(~F)) -> O.C(F):
  dot(~F, a, a)

# a turned a quarter turn counterclockwise
def perp(~F: O.OField, +a: Vec(~F)) -> Vec(~F):
  V2{O.neg(F, y(~F, a)), x(~F, a)}

# a turned by the rotation-and-scaling with matrix [[c, -s], [s, c]]
def rot(~F: O.OField, +c: O.C(F), +s: O.C(F), +a: Vec(~F)) -> Vec(~F):
  V2{O.sub(~F, O.mul(F, c, x(~F, a)), O.mul(F, s, y(~F, a))), O.add(F, O.mul(F, s, x(~F, a)), O.mul(F, c, y(~F, a)))}

# the point a + t(b - a)
def lerp(~F: O.OField, +a: Vec(~F), +b: Vec(~F), +t: O.C(F)) -> Vec(~F):
  add(~F, a, scale(~F, t, sub(~F, b, a)))

# the point midway between a and b
def mid(~F: O.OField, +a: Vec(~F), +b: Vec(~F)) -> Vec(~F):
  scale(~F, O.half(~F), add(~F, a, b))

# twice the signed area of the triangle a, b, c: positive when c is left of
# the directed line a → b
def orient(~F: O.OField, +a: Vec(~F), +b: Vec(~F), +c: Vec(~F)) -> O.C(F):
  cross(~F, sub(~F, b, a), sub(~F, c, a))

# Relations
# ---------

# the distance from p to q is d
def dist(~F: O.OField, +p: Vec(~F), +q: Vec(~F), +d: O.C(F)) -> Type:
  O.lt(F, O.zero(F), d) & {norm2(~F, sub(~F, q, p)) == O.mul(F, d, d) : O.C(F)}

# q is d to the right of p
def hdist(~F: O.OField, +p: Vec(~F), +q: Vec(~F), +d: O.C(F)) -> Type:
  O.lt(F, O.zero(F), d) & {O.sub(~F, x(~F, q), x(~F, p)) == d : O.C(F)}

# q is d above p
def vdist(~F: O.OField, +p: Vec(~F), +q: Vec(~F), +d: O.C(F)) -> Type:
  O.lt(F, O.zero(F), d) & {O.sub(~F, y(~F, q), y(~F, p)) == d : O.C(F)}

# segments a0 a1 and b0 b1 are equally long
def equal_length(~F: O.OField, +a0: Vec(~F), +a1: Vec(~F), +b0: Vec(~F), +b1: Vec(~F)) -> Type:
  {norm2(~F, sub(~F, a1, a0)) == norm2(~F, sub(~F, b1, b0)) : O.C(F)}

# one of u, v is a multiple of the other
def parallel(~F: O.OField, +u: Vec(~F), +v: Vec(~F)) -> Type:
  Or(Exists(O.C(F), l => {v == scale(~F, l, u) : Vec(~F)}), Exists(O.C(F), l => {u == scale(~F, l, v) : Vec(~F)}))

# v is parallel to u turned a quarter turn
def perpendicular(~F: O.OField, +u: Vec(~F), +v: Vec(~F)) -> Type:
  parallel(~F, perp(~F, u), v)

# p lies on the line through a and b (any p does when a = b)
def on_line(~F: O.OField, +p: Vec(~F), +a: Vec(~F), +b: Vec(~F)) -> Type:
  parallel(~F, sub(~F, b, a), sub(~F, p, a))

# p lies strictly between a and b
def on_segment(~F: O.OField, +p: Vec(~F), +a: Vec(~F), +b: Vec(~F)) -> Type:
  ne(~F, a, b) & Exists(O.C(F), t => O.lt(F, O.zero(F), t) & (O.lt(F, t, O.one(F)) & {p == lerp(~F, a, b, t) : Vec(~F)}))

# p is at distance d from the line through a and b, on its left: the foot f
# of the perpendicular from p is at distance d from p
def line_dist(~F: O.OField, +p: Vec(~F), +a: Vec(~F), +b: Vec(~F), +d: O.C(F)) -> Type:
  O.lt(F, O.zero(F), orient(~F, a, b, p)) & Exists(Vec(~F), f => on_line(~F, f, a, b) & ({dot(~F, sub(~F, p, f), sub(~F, b, a)) == O.zero(F) : O.C(F)} & dist(~F, f, p, d)))

# q is the mirror image of p in the line through a and b: their midpoint is
# on the line and q - p is perpendicular to it (any p, q when a = b)
def mirror(~F: O.OField, +p: Vec(~F), +q: Vec(~F), +a: Vec(~F), +b: Vec(~F)) -> Type:
  on_line(~F, mid(~F, p, q), a, b) & {dot(~F, sub(~F, q, p), sub(~F, b, a)) == O.zero(F) : O.C(F)}

# v points along u turned by the rotation (c, s): with (c, s) = (cos θ,
# sin θ), θ is the counterclockwise angle from u to v
def angle(~F: O.OField, +u: Vec(~F), +v: Vec(~F), +c: O.C(F), +s: O.C(F)) -> Type:
  ne(~F, u, vzero(~F)) & (ne(~F, V2{c, s}, vzero(~F)) & Exists(O.C(F), l => O.lt(F, O.zero(F), l) & {v == scale(~F, l, rot(~F, c, s, u)) : Vec(~F)}))

# p is on the circle about c of radius r
def on_circle(~F: O.OField, +p: Vec(~F), +c: Vec(~F), +r: O.C(F)) -> Type:
  {norm2(~F, sub(~F, p, c)) == O.mul(F, r, r) : O.C(F)}
