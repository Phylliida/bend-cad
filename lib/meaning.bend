# The meaning lemmas, in every ordered field: for each constraint kind, its
# exact equations and side conditions hold exactly when its meaning does
# (ROADMAP.bend: means_sound, means_complete). Each kind is proven by value
# (lib/mforms.bend states it with references resolved), matching on the
# points so that both sides compute to the same coordinates; polynomial
# reasoning goes through certificates (lib/ford.bend) checked by the
# normalizer (lib/fring.bend).

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/geom.bend as G
import ../spec/sketch.bend as K
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./mforms.bend as MF

# Vectors
# -------

def pv(~F: O.OField, +env: List<&2, O.C(F)>, x: Nat, y: Nat) -> G.Vec(~F):
  G.V2{O.lookup(~F, env, x), O.lookup(~F, env, y)}

# componentwise equality
def v2_eq(~F: O.OField, +a: O.C(F), +b: O.C(F), +c: O.C(F), +d: O.C(F), e1: {a == c : O.C(F)}, e2: {b == d : O.C(F)}) -> {G.V2{a, b} == G.V2{c, d} : G.Vec(~F)}:
  %e1 : {G.V2{a, b} == G.V2{_, d} : G.Vec(~F)}
  %e2 : {G.V2{a, b} == G.V2{a, _} : G.Vec(~F)}
  {==}

def x_eq(~F: O.OField, +a: O.C(F), +b: O.C(F), +c: O.C(F), +d: O.C(F), e: {G.V2{a, b} == G.V2{c, d} : G.Vec(~F)}) -> {a == c : O.C(F)}:
  Equal.cong(G.Vec(~F), O.C(F), v => G.x(~F, v), G.V2{a, b}, G.V2{c, d}, e)

def y_eq(~F: O.OField, +a: O.C(F), +b: O.C(F), +c: O.C(F), +d: O.C(F), e: {G.V2{a, b} == G.V2{c, d} : G.Vec(~F)}) -> {b == d : O.C(F)}:
  Equal.cong(G.Vec(~F), O.C(F), v => G.y(~F, v), G.V2{a, b}, G.V2{c, d}, e)

# |u|² as a term
def n2(~F: O.OField, +x: O.C(F), +y: O.C(F)) -> O.C(F):
  O.add(F, O.mul(F, x, x), O.mul(F, y, y))

# 0 ≤ x x + y y
def n2_nonneg(~F: O.OField, +x: O.C(F), +y: O.C(F)) -> O.le(~F, O.zero(F), n2(~F, x, y)):
  FO.nonneg_add(~F, O.mul(F, x, x), O.mul(F, y, y), FO.sq_nonneg(~F, x), FO.sq_nonneg(~F, y))

# x x + y y = 0 gives y = 0 (with sumsq_zero for x)
def n2_zero_y(~F: O.OField, +x: O.C(F), +y: O.C(F), h: {n2(~F, x, y) == O.zero(F) : O.C(F)}) -> {y == O.zero(F) : O.C(F)}:
  FO.sumsq_zero(~F, y, x, Equal.trans(O.C(F), O.add(F, O.mul(F, y, y), O.mul(F, x, x)), n2(~F, x, y), O.zero(F), FL.add_comm(~F, O.mul(F, y, y), O.mul(F, x, x)), h))

# Parallel directions
# -------------------

# cross(u, v) = 0: one of u, v is a multiple of the other
def par_sound.pos(~F: O.OField, +ux: O.C(F), +uy: O.C(F), +vx: O.C(F), +vy: O.C(F), +h: {O.sub(~F, O.mul(F, ux, vy), O.mul(F, uy, vx)) == O.zero(F) : O.C(F)}, +g: O.lt(F, O.zero(F), n2(~F, ux, uy))) -> {G.V2{vx, vy} == G.V2{O.mul(F, O.mul(F, O.add(F, O.mul(F, ux, vx), O.mul(F, uy, vy)), O.inv(F, n2(~F, ux, uy))), ux), O.mul(F, O.mul(F, O.add(F, O.mul(F, ux, vx), O.mul(F, uy, vy)), O.inv(F, n2(~F, ux, uy))), uy)} : G.Vec(~F)}:
  v2_eq(~F, vx, vy, O.mul(F, O.mul(F, O.add(F, O.mul(F, ux, vx), O.mul(F, uy, vy)), O.inv(F, n2(~F, ux, uy))), ux), O.mul(F, O.mul(F, O.add(F, O.mul(F, ux, vx), O.mul(F, uy, vy)), O.inv(F, n2(~F, ux, uy))), uy),
    FO.eq_of_sub(~F, vx, O.mul(F, O.mul(F, O.add(F, O.mul(F, ux, vx), O.mul(F, uy, vy)), O.inv(F, n2(~F, ux, uy))), ux),
      FO.cert2(~F, O.sub(~F, vx, O.mul(F, O.mul(F, O.add(F, O.mul(F, ux, vx), O.mul(F, uy, vy)), O.inv(F, n2(~F, ux, uy))), ux)),
        O.neg(F, vx), O.sub(~F, O.mul(F, n2(~F, ux, uy), O.inv(F, n2(~F, ux, uy))), O.one(F)), O.neg(F, O.mul(F, O.inv(F, n2(~F, ux, uy)), uy)), O.sub(~F, O.mul(F, ux, vy), O.mul(F, uy, vx)),
        FR.fring_eq(~F, [ux, uy, vx, vy, O.inv(F, n2(~F, ux, uy))], E.ZSub{E.ZVar{2n}, E.ZMul{E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZVar{4n}}, E.ZVar{0n}}}, E.ZAdd{E.ZMul{E.ZNeg{E.ZVar{2n}}, E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{0n}}, E.ZMul{E.ZVar{1n}, E.ZVar{1n}}}, E.ZVar{4n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZVar{4n}, E.ZVar{1n}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}}, {==}),
        FO.inv_rel(~F, n2(~F, ux, uy), FO.ne_of_gt(~F, n2(~F, ux, uy), O.zero(F), g)), h)),
    FO.eq_of_sub(~F, vy, O.mul(F, O.mul(F, O.add(F, O.mul(F, ux, vx), O.mul(F, uy, vy)), O.inv(F, n2(~F, ux, uy))), uy),
      FO.cert2(~F, O.sub(~F, vy, O.mul(F, O.mul(F, O.add(F, O.mul(F, ux, vx), O.mul(F, uy, vy)), O.inv(F, n2(~F, ux, uy))), uy)),
        O.neg(F, vy), O.sub(~F, O.mul(F, n2(~F, ux, uy), O.inv(F, n2(~F, ux, uy))), O.one(F)), O.mul(F, O.inv(F, n2(~F, ux, uy)), ux), O.sub(~F, O.mul(F, ux, vy), O.mul(F, uy, vx)),
        FR.fring_eq(~F, [ux, uy, vx, vy, O.inv(F, n2(~F, ux, uy))], E.ZSub{E.ZVar{3n}, E.ZMul{E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZVar{4n}}, E.ZVar{1n}}}, E.ZAdd{E.ZMul{E.ZNeg{E.ZVar{3n}}, E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{0n}}, E.ZMul{E.ZVar{1n}, E.ZVar{1n}}}, E.ZVar{4n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{0n}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}}, {==}),
        FO.inv_rel(~F, n2(~F, ux, uy), FO.ne_of_gt(~F, n2(~F, ux, uy), O.zero(F), g)), h)))

# u = 0 = 0 v
def par_sound.zero(~F: O.OField, +ux: O.C(F), +uy: O.C(F), +vx: O.C(F), +vy: O.C(F), +e: {n2(~F, ux, uy) == O.zero(F) : O.C(F)}) -> {G.V2{ux, uy} == G.V2{O.mul(F, O.zero(F), vx), O.mul(F, O.zero(F), vy)} : G.Vec(~F)}:
  v2_eq(~F, ux, uy, O.mul(F, O.zero(F), vx), O.mul(F, O.zero(F), vy),
    Equal.trans(O.C(F), ux, O.zero(F), O.mul(F, O.zero(F), vx), FO.sumsq_zero(~F, ux, uy, e), Equal.sym(O.C(F), O.mul(F, O.zero(F), vx), O.zero(F), FL.zero_mul(~F, vx))),
    Equal.trans(O.C(F), uy, O.zero(F), O.mul(F, O.zero(F), vy), n2_zero_y(~F, ux, uy, e), Equal.sym(O.C(F), O.mul(F, O.zero(F), vy), O.zero(F), FL.zero_mul(~F, vy))))

def par_sound.go(~F: O.OField, +ux: O.C(F), +uy: O.C(F), +vx: O.C(F), +vy: O.C(F), +h: {O.sub(~F, O.mul(F, ux, vy), O.mul(F, uy, vx)) == O.zero(F) : O.C(F)}, t: Or(O.lt(F, n2(~F, ux, uy), O.zero(F)), Or({n2(~F, ux, uy) == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), n2(~F, ux, uy))))) -> G.parallel(~F, G.V2{ux, uy}, G.V2{vx, vy}):
  match t:
    case Inl{l}:
      FO.absurd(G.parallel(~F, G.V2{ux, uy}, G.V2{vx, vy}), O.lt_irrefl(F)(O.zero(F))(FO.le_lt_trans(~F, O.zero(F), n2(~F, ux, uy), O.zero(F), n2_nonneg(~F, ux, uy), l)))
    case Inr{Inl{e}}:
      Inr{(O.zero(F), par_sound.zero(~F, ux, uy, vx, vy, e))}
    case Inr{Inr{g}}:
      Inl{(O.mul(F, O.add(F, O.mul(F, ux, vx), O.mul(F, uy, vy)), O.inv(F, n2(~F, ux, uy))), par_sound.pos(~F, ux, uy, vx, vy, h, g))}

def par_sound(~F: O.OField, +ux: O.C(F), +uy: O.C(F), +vx: O.C(F), +vy: O.C(F), +h: {O.sub(~F, O.mul(F, ux, vy), O.mul(F, uy, vx)) == O.zero(F) : O.C(F)}) -> G.parallel(~F, G.V2{ux, uy}, G.V2{vx, vy}):
  par_sound.go(~F, ux, uy, vx, vy, h, O.lt_total(F)(n2(~F, ux, uy), O.zero(F)))

def par_complete(~F: O.OField, +ux: O.C(F), +uy: O.C(F), +vx: O.C(F), +vy: O.C(F), h: G.parallel(~F, G.V2{ux, uy}, G.V2{vx, vy})) -> {O.sub(~F, O.mul(F, ux, vy), O.mul(F, uy, vx)) == O.zero(F) : O.C(F)}:
  match h:
    case Inl{x}:
      (+l, e) = x
      %Equal.sym(G.Vec(~F), G.V2{vx, vy}, G.scale(~F, l, G.V2{ux, uy}), e) : {G.cross(~F, G.V2{ux, uy}, _) == O.zero(F) : O.C(F)}
      FR.fring_eq(~F, [ux, uy, l], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{2n}, E.ZVar{1n}}}, E.ZMul{E.ZVar{1n}, E.ZMul{E.ZVar{2n}, E.ZVar{0n}}}}, E.ZCst{S.Z0{}}, {==})
    case Inr{x}:
      (+l, e) = x
      %Equal.sym(G.Vec(~F), G.V2{ux, uy}, G.scale(~F, l, G.V2{vx, vy}), e) : {G.cross(~F, _, G.V2{vx, vy}) == O.zero(F) : O.C(F)}
      FR.fring_eq(~F, [vx, vy, l], E.ZSub{E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{0n}}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{1n}}, E.ZVar{0n}}}, E.ZCst{S.Z0{}}, {==})

# dot(u, v) = 0: v is parallel to u turned a quarter turn
def perp_sound(~F: O.OField, +ux: O.C(F), +uy: O.C(F), +vx: O.C(F), +vy: O.C(F), h: {O.add(F, O.mul(F, ux, vx), O.mul(F, uy, vy)) == O.zero(F) : O.C(F)}) -> G.parallel(~F, G.V2{O.neg(F, uy), ux}, G.V2{vx, vy}):
  par_sound(~F, O.neg(F, uy), ux, vx, vy,
    FO.cert1(~F, O.sub(~F, O.mul(F, O.neg(F, uy), vy), O.mul(F, ux, vx)), O.neg(F, O.one(F)), O.add(F, O.mul(F, ux, vx), O.mul(F, uy, vy)),
      FR.fring_eq(~F, [ux, uy, vx, vy], E.ZSub{E.ZMul{E.ZNeg{E.ZVar{1n}}, E.ZVar{3n}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, E.ZMul{E.ZNeg{E.ZCst{S.Zpos{S.XH{}}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}}, {==}), h))

def perp_complete(~F: O.OField, +ux: O.C(F), +uy: O.C(F), +vx: O.C(F), +vy: O.C(F), h: G.parallel(~F, G.V2{O.neg(F, uy), ux}, G.V2{vx, vy})) -> {O.add(F, O.mul(F, ux, vx), O.mul(F, uy, vy)) == O.zero(F) : O.C(F)}:
  FO.cert1(~F, O.add(F, O.mul(F, ux, vx), O.mul(F, uy, vy)), O.neg(F, O.one(F)), O.sub(~F, O.mul(F, O.neg(F, uy), vy), O.mul(F, ux, vx)),
    FR.fring_eq(~F, [ux, uy, vx, vy], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZMul{E.ZNeg{E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZMul{E.ZNeg{E.ZVar{1n}}, E.ZVar{3n}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}}, {==}),
    par_complete(~F, O.neg(F, uy), ux, vx, vy, h))

# a coordinate difference
def dx(~F: O.OField, +env: List<&2, O.C(F)>, a: Nat, b: Nat) -> O.C(F):
  O.sub(~F, O.lookup(~F, env, a), O.lookup(~F, env, b))

# Merges
# ------

def Coincident.sound(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Pt, +b: K.Pt, w: MF.W.Coincident(a, b), h: MF.H.Coincident(~F, env, a, b)) -> MF.M.Coincident(~F, env, a, b):
  %w : {K.at(~F, env, a) == K.at(~F, env, _) : G.Vec(~F)}
  {==}

def Coincident.complete(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Pt, +b: K.Pt, h: MF.M.Coincident(~F, env, a, b)) -> MF.H.Coincident(~F, env, a, b):
  (Unit{}, Unit{})

def Horizontal.sound(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Pt, +b: K.Pt, w: MF.W.Horizontal(a, b), h: MF.H.Horizontal(~F, env, a, b)) -> MF.M.Horizontal(~F, env, a, b):
  match a b:
    case K.Pt{ax, ay} K.Pt{bx, by}:
      %w : {O.lookup(~F, env, ay) == O.lookup(~F, env, _) : O.C(F)}
      {==}

def Horizontal.complete(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Pt, +b: K.Pt, h: MF.M.Horizontal(~F, env, a, b)) -> MF.H.Horizontal(~F, env, a, b):
  (Unit{}, Unit{})

def Vertical.sound(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Pt, +b: K.Pt, w: MF.W.Vertical(a, b), h: MF.H.Vertical(~F, env, a, b)) -> MF.M.Vertical(~F, env, a, b):
  match a b:
    case K.Pt{ax, ay} K.Pt{bx, by}:
      %w : {O.lookup(~F, env, ax) == O.lookup(~F, env, _) : O.C(F)}
      {==}

def Vertical.complete(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Pt, +b: K.Pt, h: MF.M.Vertical(~F, env, a, b)) -> MF.H.Vertical(~F, env, a, b):
  (Unit{}, Unit{})

def Concentric.sound(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Circ, +b: K.Circ, w: MF.W.Concentric(a, b), h: MF.H.Concentric(~F, env, a, b)) -> MF.M.Concentric(~F, env, a, b):
  %w : {K.at(~F, env, K.Circ.c(a)) == K.at(~F, env, _) : G.Vec(~F)}
  {==}

def Concentric.complete(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Circ, +b: K.Circ, h: MF.M.Concentric(~F, env, a, b)) -> MF.H.Concentric(~F, env, a, b):
  (Unit{}, Unit{})

def EqualRadius.sound(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Circ, +b: K.Circ, w: MF.W.EqualRadius(a, b), h: MF.H.EqualRadius(~F, env, a, b)) -> MF.M.EqualRadius(~F, env, a, b):
  %w : {O.lookup(~F, env, K.Circ.r(a)) == O.lookup(~F, env, _) : O.C(F)}
  {==}

def EqualRadius.complete(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Circ, +b: K.Circ, h: MF.M.EqualRadius(~F, env, a, b)) -> MF.H.EqualRadius(~F, env, a, b):
  (Unit{}, Unit{})

# Fix and dimensions
# ------------------

def Fix.sound(~F: O.OField, +env: List<&2, O.C(F)>, +v: Nat, +c: S.Q, w: MF.W.Fix(v, c), h: MF.H.Fix(~F, env, v, c)) -> MF.M.Fix(~F, env, v, c):
  ((hz, u1), u2) = h
  FO.eq_of_sub(~F, O.lookup(~F, env, v), O.ofq(~F, c), hz)

def Fix.complete(~F: O.OField, +env: List<&2, O.C(F)>, +v: Nat, +c: S.Q, h: MF.M.Fix(~F, env, v, c)) -> MF.H.Fix(~F, env, v, c):
  ((FO.sub_of_eq(~F, O.lookup(~F, env, v), O.ofq(~F, c), h), Unit{}), Unit{})

def Distance.sound(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +q: K.Pt, +d: E.QExpr, w: MF.W.Distance(p, q, d), h: MF.H.Distance(~F, env, p, q, d)) -> MF.M.Distance(~F, env, p, q, d):
  match p q:
    case K.Pt{px, py} K.Pt{qx, qy}:
      ((hz, u1), (hs, u2)) = h
      (hs, FO.eq_of_sub(~F, G.norm2(~F, G.sub(~F, pv(~F, env, qx, qy), pv(~F, env, px, py))), O.mul(F, O.eval(~F, env, d), O.eval(~F, env, d)), hz))

def Distance.complete(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +q: K.Pt, +d: E.QExpr, h: MF.M.Distance(~F, env, p, q, d)) -> MF.H.Distance(~F, env, p, q, d):
  match p q:
    case K.Pt{px, py} K.Pt{qx, qy}:
      (hs, he) = h
      ((FO.sub_of_eq(~F, G.norm2(~F, G.sub(~F, pv(~F, env, qx, qy), pv(~F, env, px, py))), O.mul(F, O.eval(~F, env, d), O.eval(~F, env, d)), he), Unit{}), (hs, Unit{}))

def HDistance.sound(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +q: K.Pt, +d: E.QExpr, w: MF.W.HDistance(p, q, d), h: MF.H.HDistance(~F, env, p, q, d)) -> MF.M.HDistance(~F, env, p, q, d):
  match p q:
    case K.Pt{px, py} K.Pt{qx, qy}:
      ((hz, u1), (hs, u2)) = h
      (hs, FO.eq_of_sub(~F, dx(~F, env, qx, px), O.eval(~F, env, d), hz))

def HDistance.complete(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +q: K.Pt, +d: E.QExpr, h: MF.M.HDistance(~F, env, p, q, d)) -> MF.H.HDistance(~F, env, p, q, d):
  match p q:
    case K.Pt{px, py} K.Pt{qx, qy}:
      (hs, he) = h
      ((FO.sub_of_eq(~F, dx(~F, env, qx, px), O.eval(~F, env, d), he), Unit{}), (hs, Unit{}))

def VDistance.sound(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +q: K.Pt, +d: E.QExpr, w: MF.W.VDistance(p, q, d), h: MF.H.VDistance(~F, env, p, q, d)) -> MF.M.VDistance(~F, env, p, q, d):
  match p q:
    case K.Pt{px, py} K.Pt{qx, qy}:
      ((hz, u1), (hs, u2)) = h
      (hs, FO.eq_of_sub(~F, dx(~F, env, qy, py), O.eval(~F, env, d), hz))

def VDistance.complete(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +q: K.Pt, +d: E.QExpr, h: MF.M.VDistance(~F, env, p, q, d)) -> MF.H.VDistance(~F, env, p, q, d):
  match p q:
    case K.Pt{px, py} K.Pt{qx, qy}:
      (hs, he) = h
      ((FO.sub_of_eq(~F, dx(~F, env, qy, py), O.eval(~F, env, d), he), Unit{}), (hs, Unit{}))

def Radius.sound(~F: O.OField, +env: List<&2, O.C(F)>, +c: K.Circ, +d: E.QExpr, w: MF.W.Radius(c, d), h: MF.H.Radius(~F, env, c, d)) -> MF.M.Radius(~F, env, c, d):
  ((hz, u1), u2) = h
  FO.eq_of_sub(~F, O.lookup(~F, env, K.Circ.r(c)), O.eval(~F, env, d), hz)

def Radius.complete(~F: O.OField, +env: List<&2, O.C(F)>, +c: K.Circ, +d: E.QExpr, h: MF.M.Radius(~F, env, c, d)) -> MF.H.Radius(~F, env, c, d):
  ((FO.sub_of_eq(~F, O.lookup(~F, env, K.Circ.r(c)), O.eval(~F, env, d), h), Unit{}), Unit{})

def Diameter.sound(~F: O.OField, +env: List<&2, O.C(F)>, +c: K.Circ, +d: E.QExpr, w: MF.W.Diameter(c, d), h: MF.H.Diameter(~F, env, c, d)) -> MF.M.Diameter(~F, env, c, d):
  ((hz, u1), u2) = h
  FO.eq_of_sub(~F, O.add(F, O.lookup(~F, env, K.Circ.r(c)), O.lookup(~F, env, K.Circ.r(c))), O.eval(~F, env, d), hz)

def Diameter.complete(~F: O.OField, +env: List<&2, O.C(F)>, +c: K.Circ, +d: E.QExpr, h: MF.M.Diameter(~F, env, c, d)) -> MF.H.Diameter(~F, env, c, d):
  ((FO.sub_of_eq(~F, O.add(F, O.lookup(~F, env, K.Circ.r(c)), O.lookup(~F, env, K.Circ.r(c))), O.eval(~F, env, d), h), Unit{}), Unit{})

# Relations
# ---------

def EqualLength.sound(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Seg, +b: K.Seg, w: MF.W.EqualLength(a, b), h: MF.H.EqualLength(~F, env, a, b)) -> MF.M.EqualLength(~F, env, a, b):
  match a b:
    case K.Seg{K.Pt{a0x, a0y}, K.Pt{a1x, a1y}} K.Seg{K.Pt{b0x, b0y}, K.Pt{b1x, b1y}}:
      ((hz, u1), u2) = h
      FO.eq_of_sub(~F, n2(~F, dx(~F, env, a1x, a0x), dx(~F, env, a1y, a0y)), n2(~F, dx(~F, env, b1x, b0x), dx(~F, env, b1y, b0y)), hz)

def EqualLength.complete(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Seg, +b: K.Seg, h: MF.M.EqualLength(~F, env, a, b)) -> MF.H.EqualLength(~F, env, a, b):
  match a b:
    case K.Seg{K.Pt{a0x, a0y}, K.Pt{a1x, a1y}} K.Seg{K.Pt{b0x, b0y}, K.Pt{b1x, b1y}}:
      ((FO.sub_of_eq(~F, n2(~F, dx(~F, env, a1x, a0x), dx(~F, env, a1y, a0y)), n2(~F, dx(~F, env, b1x, b0x), dx(~F, env, b1y, b0y)), h), Unit{}), Unit{})

def Perpendicular.sound(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Seg, +b: K.Seg, w: MF.W.Perpendicular(a, b), h: MF.H.Perpendicular(~F, env, a, b)) -> MF.M.Perpendicular(~F, env, a, b):
  match a b:
    case K.Seg{K.Pt{a0x, a0y}, K.Pt{a1x, a1y}} K.Seg{K.Pt{b0x, b0y}, K.Pt{b1x, b1y}}:
      ((hz, u1), u2) = h
      perp_sound(~F, dx(~F, env, a1x, a0x), dx(~F, env, a1y, a0y), dx(~F, env, b1x, b0x), dx(~F, env, b1y, b0y), hz)

def Perpendicular.complete(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Seg, +b: K.Seg, h: MF.M.Perpendicular(~F, env, a, b)) -> MF.H.Perpendicular(~F, env, a, b):
  match a b:
    case K.Seg{K.Pt{a0x, a0y}, K.Pt{a1x, a1y}} K.Seg{K.Pt{b0x, b0y}, K.Pt{b1x, b1y}}:
      ((perp_complete(~F, dx(~F, env, a1x, a0x), dx(~F, env, a1y, a0y), dx(~F, env, b1x, b0x), dx(~F, env, b1y, b0y), h), Unit{}), Unit{})

def Parallel.sound(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Seg, +b: K.Seg, w: MF.W.Parallel(a, b), h: MF.H.Parallel(~F, env, a, b)) -> MF.M.Parallel(~F, env, a, b):
  match a b:
    case K.Seg{K.Pt{a0x, a0y}, K.Pt{a1x, a1y}} K.Seg{K.Pt{b0x, b0y}, K.Pt{b1x, b1y}}:
      ((hz, u1), u2) = h
      par_sound(~F, dx(~F, env, a1x, a0x), dx(~F, env, a1y, a0y), dx(~F, env, b1x, b0x), dx(~F, env, b1y, b0y), hz)

def Parallel.complete(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Seg, +b: K.Seg, h: MF.M.Parallel(~F, env, a, b)) -> MF.H.Parallel(~F, env, a, b):
  match a b:
    case K.Seg{K.Pt{a0x, a0y}, K.Pt{a1x, a1y}} K.Seg{K.Pt{b0x, b0y}, K.Pt{b1x, b1y}}:
      ((par_complete(~F, dx(~F, env, a1x, a0x), dx(~F, env, a1y, a0y), dx(~F, env, b1x, b0x), dx(~F, env, b1y, b0y), h), Unit{}), Unit{})

def OnLine.sound(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +a: K.Seg, w: MF.W.OnLine(p, a), h: MF.H.OnLine(~F, env, p, a)) -> MF.M.OnLine(~F, env, p, a):
  match p a:
    case K.Pt{px, py} K.Seg{K.Pt{ax, ay}, K.Pt{bx, by}}:
      ((hz, u1), u2) = h
      par_sound(~F, dx(~F, env, bx, ax), dx(~F, env, by, ay), dx(~F, env, px, ax), dx(~F, env, py, ay), hz)

def OnLine.complete(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +a: K.Seg, h: MF.M.OnLine(~F, env, p, a)) -> MF.H.OnLine(~F, env, p, a):
  match p a:
    case K.Pt{px, py} K.Seg{K.Pt{ax, ay}, K.Pt{bx, by}}:
      ((par_complete(~F, dx(~F, env, bx, ax), dx(~F, env, by, ay), dx(~F, env, px, ax), dx(~F, env, py, ay), h), Unit{}), Unit{})

def OnCircle.sound(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +c: K.Circ, w: MF.W.OnCircle(p, c), h: MF.H.OnCircle(~F, env, p, c)) -> MF.M.OnCircle(~F, env, p, c):
  match p c:
    case K.Pt{px, py} K.Circ{K.Pt{cx, cy}, r}:
      ((hz, u1), u2) = h
      FO.eq_of_sub(~F, n2(~F, dx(~F, env, px, cx), dx(~F, env, py, cy)), O.mul(F, O.lookup(~F, env, r), O.lookup(~F, env, r)), hz)

def OnCircle.complete(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +c: K.Circ, h: MF.M.OnCircle(~F, env, p, c)) -> MF.H.OnCircle(~F, env, p, c):
  match p c:
    case K.Pt{px, py} K.Circ{K.Pt{cx, cy}, r}:
      ((FO.sub_of_eq(~F, n2(~F, dx(~F, env, px, cx), dx(~F, env, py, cy)), O.mul(F, O.lookup(~F, env, r), O.lookup(~F, env, r)), h), Unit{}), Unit{})

# Midpoint
# --------

def Midpoint.sound(~F: O.OField, +env: List<&2, O.C(F)>, +m: K.Pt, +a: K.Seg, w: MF.W.Midpoint(m, a), h: MF.H.Midpoint(~F, env, m, a)) -> MF.M.Midpoint(~F, env, m, a):
  match m a:
    case K.Pt{mx, my} K.Seg{K.Pt{ax, ay}, K.Pt{bx, by}}:
      ((hx, (hy, u1)), u2) = h
      v2_eq(~F, O.lookup(~F, env, mx), O.lookup(~F, env, my), O.mul(F, O.half(~F), O.add(F, O.lookup(~F, env, ax), O.lookup(~F, env, bx))), O.mul(F, O.half(~F), O.add(F, O.lookup(~F, env, ay), O.lookup(~F, env, by))),
        FO.eq_of_sub(~F, O.lookup(~F, env, mx), O.mul(F, O.half(~F), O.add(F, O.lookup(~F, env, ax), O.lookup(~F, env, bx))), FO.cert2(~F, O.sub(~F, O.lookup(~F, env, mx), O.mul(F, O.half(~F), O.add(F, O.lookup(~F, env, ax), O.lookup(~F, env, bx)))), O.half(~F), O.sub(~F, O.add(F, O.lookup(~F, env, mx), O.lookup(~F, env, mx)), O.add(F, O.lookup(~F, env, ax), O.lookup(~F, env, bx))), O.neg(F, O.lookup(~F, env, mx)), O.sub(~F, O.mul(F, O.add(F, O.one(F), O.one(F)), O.half(~F)), O.one(F)), FR.fring_eq(~F, [O.lookup(~F, env, mx), O.lookup(~F, env, ax), O.lookup(~F, env, bx), O.half(~F)], E.ZSub{E.ZVar{0n}, E.ZMul{E.ZVar{3n}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZAdd{E.ZMul{E.ZVar{3n}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZSub{E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{3n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), hx, FO.half_rel(~F))),
        FO.eq_of_sub(~F, O.lookup(~F, env, my), O.mul(F, O.half(~F), O.add(F, O.lookup(~F, env, ay), O.lookup(~F, env, by))), FO.cert2(~F, O.sub(~F, O.lookup(~F, env, my), O.mul(F, O.half(~F), O.add(F, O.lookup(~F, env, ay), O.lookup(~F, env, by)))), O.half(~F), O.sub(~F, O.add(F, O.lookup(~F, env, my), O.lookup(~F, env, my)), O.add(F, O.lookup(~F, env, ay), O.lookup(~F, env, by))), O.neg(F, O.lookup(~F, env, my)), O.sub(~F, O.mul(F, O.add(F, O.one(F), O.one(F)), O.half(~F)), O.one(F)), FR.fring_eq(~F, [O.lookup(~F, env, my), O.lookup(~F, env, ay), O.lookup(~F, env, by), O.half(~F)], E.ZSub{E.ZVar{0n}, E.ZMul{E.ZVar{3n}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZAdd{E.ZMul{E.ZVar{3n}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZSub{E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{3n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), hy, FO.half_rel(~F))))

def mid_complete(~F: O.OField, +mx: O.C(F), +my: O.C(F), +ax: O.C(F), +ay: O.C(F), +bx: O.C(F), +by: O.C(F), +h: {G.V2{mx, my} == G.mid(~F, G.V2{ax, ay}, G.V2{bx, by}) : G.Vec(~F)}) -> K.Both({O.sub(~F, O.add(F, mx, mx), O.add(F, ax, bx)) == O.zero(F) : O.C(F)}, K.Both({O.sub(~F, O.add(F, my, my), O.add(F, ay, by)) == O.zero(F) : O.C(F)}, Unit)) & Unit:
  ((FO.cert2(~F, O.sub(~F, O.add(F, mx, mx), O.add(F, ax, bx)), O.add(F, O.one(F), O.one(F)), O.sub(~F, mx, O.mul(F, O.half(~F), O.add(F, ax, bx))), O.add(F, ax, bx), O.sub(~F, O.mul(F, O.add(F, O.one(F), O.one(F)), O.half(~F)), O.one(F)), FR.fring_eq(~F, [mx, ax, bx, O.half(~F)], E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}, E.ZAdd{E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{0n}, E.ZMul{E.ZVar{3n}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}}}, E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}, E.ZSub{E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{3n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), FO.sub_of_eq(~F, mx, O.mul(F, O.half(~F), O.add(F, ax, bx)), x_eq(~F, mx, my, O.mul(F, O.half(~F), O.add(F, ax, bx)), O.mul(F, O.half(~F), O.add(F, ay, by)), h)), FO.half_rel(~F)),
    (FO.cert2(~F, O.sub(~F, O.add(F, my, my), O.add(F, ay, by)), O.add(F, O.one(F), O.one(F)), O.sub(~F, my, O.mul(F, O.half(~F), O.add(F, ay, by))), O.add(F, ay, by), O.sub(~F, O.mul(F, O.add(F, O.one(F), O.one(F)), O.half(~F)), O.one(F)), FR.fring_eq(~F, [my, ay, by, O.half(~F)], E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}, E.ZAdd{E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZVar{0n}, E.ZMul{E.ZVar{3n}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}}}, E.ZMul{E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}, E.ZSub{E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{3n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), FO.sub_of_eq(~F, my, O.mul(F, O.half(~F), O.add(F, ay, by)), y_eq(~F, mx, my, O.mul(F, O.half(~F), O.add(F, ax, bx)), O.mul(F, O.half(~F), O.add(F, ay, by)), h)), FO.half_rel(~F)), Unit{})), Unit{})

def Midpoint.complete(~F: O.OField, +env: List<&2, O.C(F)>, +m: K.Pt, +a: K.Seg, h: MF.M.Midpoint(~F, env, m, a)) -> MF.H.Midpoint(~F, env, m, a):
  match m a:
    case K.Pt{mx, my} K.Seg{K.Pt{ax, ay}, K.Pt{bx, by}}:
      mid_complete(~F, O.lookup(~F, env, mx), O.lookup(~F, env, my), O.lookup(~F, env, ax), O.lookup(~F, env, ay), O.lookup(~F, env, bx), O.lookup(~F, env, by), h)

# Mirror image
# ------------
# w = b - a, u = p - a, v = q - a, n = |w|²; E1, E2 are the mirror
# equations |w|² v - R̂ u = 0; z = mid(p, q) - a.


def sym_sound.go(~F: O.OField, +px: O.C(F), +py: O.C(F), +qx: O.C(F), +qy: O.C(F), +ax: O.C(F), +ay: O.C(F), +bx: O.C(F), +by: O.C(F), +h1: {O.sub(~F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, qx, ax)), O.add(F, O.mul(F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, px, ax)), O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay))), O.sub(~F, py, ay)))) == O.zero(F) : O.C(F)}, +h2: {O.sub(~F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, qy, ay)), O.add(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay))), O.sub(~F, px, ax)), O.mul(F, O.sub(~F, O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay)), O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax))), O.sub(~F, py, ay)))) == O.zero(F) : O.C(F)}, t: Or(O.lt(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), O.zero(F)), Or({n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)) == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))))) -> G.mirror(~F, G.V2{px, py}, G.V2{qx, qy}, G.V2{ax, ay}, G.V2{bx, by}):
  match t:
    case Inl{l}:
      FO.absurd(G.mirror(~F, G.V2{px, py}, G.V2{qx, qy}, G.V2{ax, ay}, G.V2{bx, by}), O.lt_irrefl(F)(O.zero(F))(FO.le_lt_trans(~F, O.zero(F), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), O.zero(F), n2_nonneg(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), l)))
    case Inr{Inl{+e}}:
      +ewx = FO.sumsq_zero(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay), e)
      +ewy = n2_zero_y(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay), e)
      (par_sound(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay), O.sub(~F, O.mul(F, O.half(~F), O.add(F, px, qx)), ax), O.sub(~F, O.mul(F, O.half(~F), O.add(F, py, qy)), ay), FO.cert2(~F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, O.mul(F, O.half(~F), O.add(F, py, qy)), ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, O.mul(F, O.half(~F), O.add(F, px, qx)), ax))), O.sub(~F, O.mul(F, O.half(~F), O.add(F, py, qy)), ay), O.sub(~F, bx, ax), O.neg(F, O.sub(~F, O.mul(F, O.half(~F), O.add(F, px, qx)), ax)), O.sub(~F, by, ay), FR.fring_eq(~F, [px, py, qx, qy, ax, ay, bx, by, O.half(~F), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))], E.ZSub{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZMul{E.ZVar{8n}, E.ZAdd{E.ZVar{1n}, E.ZVar{3n}}}, E.ZVar{5n}}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZSub{E.ZMul{E.ZVar{8n}, E.ZAdd{E.ZVar{0n}, E.ZVar{2n}}}, E.ZVar{4n}}}}, E.ZAdd{E.ZMul{E.ZSub{E.ZMul{E.ZVar{8n}, E.ZAdd{E.ZVar{1n}, E.ZVar{3n}}}, E.ZVar{5n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZMul{E.ZNeg{E.ZSub{E.ZMul{E.ZVar{8n}, E.ZAdd{E.ZVar{0n}, E.ZVar{2n}}}, E.ZVar{4n}}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, {==}), ewx, ewy)),
       FO.cert2(~F, O.add(F, O.mul(F, O.sub(~F, qx, px), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, qy, py), O.sub(~F, by, ay))), O.sub(~F, qx, px), O.sub(~F, bx, ax), O.sub(~F, qy, py), O.sub(~F, by, ay), FR.fring_eq(~F, [px, py, qx, qy, ax, ay, bx, by, O.half(~F), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))], E.ZAdd{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZAdd{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, {==}), ewx, ewy))
    case Inr{Inr{g}}:
      +hn = FO.inv_rel(~F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), FO.ne_of_gt(~F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), O.zero(F), g))
      (par_sound(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay), O.sub(~F, O.mul(F, O.half(~F), O.add(F, px, qx)), ax), O.sub(~F, O.mul(F, O.half(~F), O.add(F, py, qy)), ay),
         FO.cert4(~F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, O.mul(F, O.half(~F), O.add(F, py, qy)), ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, O.mul(F, O.half(~F), O.add(F, px, qx)), ax))), O.neg(F, O.mul(F, O.mul(F, O.half(~F), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, by, ay))), O.sub(~F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, qx, ax)), O.add(F, O.mul(F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, px, ax)), O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay))), O.sub(~F, py, ay)))), O.mul(F, O.mul(F, O.half(~F), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, bx, ax)), O.sub(~F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, qy, ay)), O.add(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay))), O.sub(~F, px, ax)), O.mul(F, O.sub(~F, O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay)), O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax))), O.sub(~F, py, ay)))), O.neg(F, O.mul(F, O.half(~F), O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.add(F, O.sub(~F, py, ay), O.sub(~F, qy, ay))), O.mul(F, O.sub(~F, by, ay), O.add(F, O.sub(~F, px, ax), O.sub(~F, qx, ax)))))), O.sub(~F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.one(F)), O.sub(~F, O.mul(F, O.sub(~F, bx, ax), ay), O.mul(F, O.sub(~F, by, ay), ax)), O.sub(~F, O.mul(F, O.add(F, O.one(F), O.one(F)), O.half(~F)), O.one(F)), FR.fring_eq(~F, [px, py, qx, qy, ax, ay, bx, by, O.half(~F), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))], E.ZSub{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZMul{E.ZVar{8n}, E.ZAdd{E.ZVar{1n}, E.ZVar{3n}}}, E.ZVar{5n}}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZSub{E.ZMul{E.ZVar{8n}, E.ZAdd{E.ZVar{0n}, E.ZVar{2n}}}, E.ZVar{4n}}}}, E.ZAdd{E.ZAdd{E.ZAdd{E.ZMul{E.ZNeg{E.ZMul{E.ZMul{E.ZVar{8n}, E.ZVar{9n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZSub{E.ZVar{2n}, E.ZVar{4n}}}, E.ZAdd{E.ZMul{E.ZSub{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZSub{E.ZVar{0n}, E.ZVar{4n}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}, E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZSub{E.ZVar{1n}, E.ZVar{5n}}}}}}, E.ZMul{E.ZMul{E.ZMul{E.ZVar{8n}, E.ZVar{9n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZSub{E.ZVar{3n}, E.ZVar{5n}}}, E.ZAdd{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}, E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZSub{E.ZVar{0n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}, E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}}, E.ZSub{E.ZVar{1n}, E.ZVar{5n}}}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZVar{8n}, E.ZSub{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZAdd{E.ZSub{E.ZVar{1n}, E.ZVar{5n}}, E.ZSub{E.ZVar{3n}, E.ZVar{5n}}}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZVar{4n}}, E.ZSub{E.ZVar{2n}, E.ZVar{4n}}}}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZVar{9n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZSub{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZVar{5n}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZVar{4n}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{8n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), h1, h2, hn, FO.half_rel(~F))),
       FO.cert3(~F, O.add(F, O.mul(F, O.sub(~F, qx, px), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, qy, py), O.sub(~F, by, ay))), O.mul(F, O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay))), O.sub(~F, bx, ax)), O.sub(~F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, qx, ax)), O.add(F, O.mul(F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, px, ax)), O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay))), O.sub(~F, py, ay)))), O.mul(F, O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay))), O.sub(~F, by, ay)), O.sub(~F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, qy, ay)), O.add(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay))), O.sub(~F, px, ax)), O.mul(F, O.sub(~F, O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay)), O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax))), O.sub(~F, py, ay)))), O.neg(F, O.add(F, O.mul(F, O.sub(~F, qx, px), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, qy, py), O.sub(~F, by, ay)))), O.sub(~F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.one(F)), FR.fring_eq(~F, [px, py, qx, qy, ax, ay, bx, by, O.half(~F), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))], E.ZAdd{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZMul{E.ZVar{9n}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZSub{E.ZVar{2n}, E.ZVar{4n}}}, E.ZAdd{E.ZMul{E.ZSub{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZSub{E.ZVar{0n}, E.ZVar{4n}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}, E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZSub{E.ZVar{1n}, E.ZVar{5n}}}}}}, E.ZMul{E.ZMul{E.ZVar{9n}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZSub{E.ZVar{3n}, E.ZVar{5n}}}, E.ZAdd{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}, E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZSub{E.ZVar{0n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}, E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}}, E.ZSub{E.ZVar{1n}, E.ZVar{5n}}}}}}}, E.ZMul{E.ZNeg{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZVar{9n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), h1, h2, hn))

def sym_sound(~F: O.OField, +px: O.C(F), +py: O.C(F), +qx: O.C(F), +qy: O.C(F), +ax: O.C(F), +ay: O.C(F), +bx: O.C(F), +by: O.C(F), +h1: {O.sub(~F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, qx, ax)), O.add(F, O.mul(F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, px, ax)), O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay))), O.sub(~F, py, ay)))) == O.zero(F) : O.C(F)}, +h2: {O.sub(~F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, qy, ay)), O.add(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay))), O.sub(~F, px, ax)), O.mul(F, O.sub(~F, O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay)), O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax))), O.sub(~F, py, ay)))) == O.zero(F) : O.C(F)}) -> G.mirror(~F, G.V2{px, py}, G.V2{qx, qy}, G.V2{ax, ay}, G.V2{bx, by}):
  sym_sound.go(~F, px, py, qx, qy, ax, ay, bx, by, h1, h2, O.lt_total(F)(n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), O.zero(F)))

def sym_complete(~F: O.OField, +px: O.C(F), +py: O.C(F), +qx: O.C(F), +qy: O.C(F), +ax: O.C(F), +ay: O.C(F), +bx: O.C(F), +by: O.C(F), h: G.mirror(~F, G.V2{px, py}, G.V2{qx, qy}, G.V2{ax, ay}, G.V2{bx, by})) -> K.Both({O.sub(~F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, qx, ax)), O.add(F, O.mul(F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, px, ax)), O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay))), O.sub(~F, py, ay)))) == O.zero(F) : O.C(F)}, K.Both({O.sub(~F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, qy, ay)), O.add(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay))), O.sub(~F, px, ax)), O.mul(F, O.sub(~F, O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay)), O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax))), O.sub(~F, py, ay)))) == O.zero(F) : O.C(F)}, Unit)) & Unit:
  (ol, +hd0) = h
  +c = par_complete(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay), O.sub(~F, O.mul(F, O.half(~F), O.add(F, px, qx)), ax), O.sub(~F, O.mul(F, O.half(~F), O.add(F, py, qy)), ay), ol)
  ((FO.cert3(~F, O.sub(~F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, qx, ax)), O.add(F, O.mul(F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, px, ax)), O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay))), O.sub(~F, py, ay)))), O.sub(~F, bx, ax), O.add(F, O.mul(F, O.sub(~F, qx, px), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, qy, py), O.sub(~F, by, ay))), O.neg(F, O.mul(F, O.ofz(~F, S.Zpos{S.XO{S.XH{}}}), O.sub(~F, by, ay))), O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, O.mul(F, O.half(~F), O.add(F, py, qy)), ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, O.mul(F, O.half(~F), O.add(F, px, qx)), ax))), O.mul(F, O.sub(~F, by, ay), O.add(F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.add(F, O.sub(~F, py, ay), O.sub(~F, qy, ay))), O.mul(F, O.sub(~F, by, ay), O.add(F, O.sub(~F, px, ax), O.sub(~F, qx, ax)))), O.mul(F, O.ofz(~F, S.Zpos{S.XO{S.XH{}}}), O.sub(~F, O.mul(F, O.sub(~F, bx, ax), ay), O.mul(F, O.sub(~F, by, ay), ax))))), O.sub(~F, O.mul(F, O.add(F, O.one(F), O.one(F)), O.half(~F)), O.one(F)), FR.fring_eq(~F, [px, py, qx, qy, ax, ay, bx, by, O.half(~F), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))], E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZSub{E.ZVar{2n}, E.ZVar{4n}}}, E.ZAdd{E.ZMul{E.ZSub{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZSub{E.ZVar{0n}, E.ZVar{4n}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}, E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZSub{E.ZVar{1n}, E.ZVar{5n}}}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZAdd{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZCst{S.Zpos{S.XO{S.XH{}}}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZSub{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZMul{E.ZVar{8n}, E.ZAdd{E.ZVar{1n}, E.ZVar{3n}}}, E.ZVar{5n}}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZSub{E.ZMul{E.ZVar{8n}, E.ZAdd{E.ZVar{0n}, E.ZVar{2n}}}, E.ZVar{4n}}}}}}, E.ZMul{E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZAdd{E.ZSub{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZAdd{E.ZSub{E.ZVar{1n}, E.ZVar{5n}}, E.ZSub{E.ZVar{3n}, E.ZVar{5n}}}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZVar{4n}}, E.ZSub{E.ZVar{2n}, E.ZVar{4n}}}}}, E.ZMul{E.ZCst{S.Zpos{S.XO{S.XH{}}}}, E.ZSub{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZVar{5n}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZVar{4n}}}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{8n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), hd0, c, FO.half_rel(~F)),
   (FO.cert3(~F, O.sub(~F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, qy, ay)), O.add(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), O.mul(F, O.sub(~F, bx, ax), O.sub(~F, by, ay))), O.sub(~F, px, ax)), O.mul(F, O.sub(~F, O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay)), O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax))), O.sub(~F, py, ay)))), O.sub(~F, by, ay), O.add(F, O.mul(F, O.sub(~F, qx, px), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, qy, py), O.sub(~F, by, ay))), O.mul(F, O.ofz(~F, S.Zpos{S.XO{S.XH{}}}), O.sub(~F, bx, ax)), O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, O.mul(F, O.half(~F), O.add(F, py, qy)), ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, O.mul(F, O.half(~F), O.add(F, px, qx)), ax))), O.neg(F, O.mul(F, O.sub(~F, bx, ax), O.add(F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.add(F, O.sub(~F, py, ay), O.sub(~F, qy, ay))), O.mul(F, O.sub(~F, by, ay), O.add(F, O.sub(~F, px, ax), O.sub(~F, qx, ax)))), O.mul(F, O.ofz(~F, S.Zpos{S.XO{S.XH{}}}), O.sub(~F, O.mul(F, O.sub(~F, bx, ax), ay), O.mul(F, O.sub(~F, by, ay), ax)))))), O.sub(~F, O.mul(F, O.add(F, O.one(F), O.one(F)), O.half(~F)), O.one(F)), FR.fring_eq(~F, [px, py, qx, qy, ax, ay, bx, by, O.half(~F), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))], E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZSub{E.ZVar{3n}, E.ZVar{5n}}}, E.ZAdd{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}, E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}, E.ZSub{E.ZVar{0n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}, E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}}, E.ZSub{E.ZVar{1n}, E.ZVar{5n}}}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZAdd{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{7n}, E.ZVar{5n}}}}}, E.ZMul{E.ZMul{E.ZCst{S.Zpos{S.XO{S.XH{}}}}, E.ZSub{E.ZVar{6n}, E.ZVar{4n}}}, E.ZSub{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZSub{E.ZMul{E.ZVar{8n}, E.ZAdd{E.ZVar{1n}, E.ZVar{3n}}}, E.ZVar{5n}}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZSub{E.ZMul{E.ZVar{8n}, E.ZAdd{E.ZVar{0n}, E.ZVar{2n}}}, E.ZVar{4n}}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZAdd{E.ZSub{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZAdd{E.ZSub{E.ZVar{1n}, E.ZVar{5n}}, E.ZSub{E.ZVar{3n}, E.ZVar{5n}}}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZVar{4n}}, E.ZSub{E.ZVar{2n}, E.ZVar{4n}}}}}, E.ZMul{E.ZCst{S.Zpos{S.XO{S.XH{}}}}, E.ZSub{E.ZMul{E.ZSub{E.ZVar{6n}, E.ZVar{4n}}, E.ZVar{5n}}, E.ZMul{E.ZSub{E.ZVar{7n}, E.ZVar{5n}}, E.ZVar{4n}}}}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{8n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), hd0, c, FO.half_rel(~F)), Unit{})), Unit{})

def Symmetric.sound(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +q: K.Pt, +a: K.Seg, w: MF.W.Symmetric(p, q, a), h: MF.H.Symmetric(~F, env, p, q, a)) -> MF.M.Symmetric(~F, env, p, q, a):
  match p q a:
    case K.Pt{px, py} K.Pt{qx, qy} K.Seg{K.Pt{ax, ay}, K.Pt{bx, by}}:
      ((h1, (h2, u1)), u2) = h
      sym_sound(~F, O.lookup(~F, env, px), O.lookup(~F, env, py), O.lookup(~F, env, qx), O.lookup(~F, env, qy), O.lookup(~F, env, ax), O.lookup(~F, env, ay), O.lookup(~F, env, bx), O.lookup(~F, env, by), h1, h2)

def Symmetric.complete(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +q: K.Pt, +a: K.Seg, h: MF.M.Symmetric(~F, env, p, q, a)) -> MF.H.Symmetric(~F, env, p, q, a):
  match p q a:
    case K.Pt{px, py} K.Pt{qx, qy} K.Seg{K.Pt{ax, ay}, K.Pt{bx, by}}:
      sym_complete(~F, O.lookup(~F, env, px), O.lookup(~F, env, py), O.lookup(~F, env, qx), O.lookup(~F, env, qy), O.lookup(~F, env, ax), O.lookup(~F, env, ay), O.lookup(~F, env, bx), O.lookup(~F, env, by), h)

# 0 < x x + y y unless (x, y) = 0
def sumsq_pos.go(~F: O.OField, +x: O.C(F), +y: O.C(F), h: {G.V2{x, y} == G.vzero(~F) : G.Vec(~F)} -> Empty, t: Or(O.lt(F, n2(~F, x, y), O.zero(F)), Or({n2(~F, x, y) == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), n2(~F, x, y))))) -> O.lt(F, O.zero(F), n2(~F, x, y)):
  match t:
    case Inl{l}:
      FO.absurd(O.lt(F, O.zero(F), n2(~F, x, y)), O.lt_irrefl(F)(O.zero(F))(FO.le_lt_trans(~F, O.zero(F), n2(~F, x, y), O.zero(F), n2_nonneg(~F, x, y), l)))
    case Inr{Inl{+e}}:
      FO.absurd(O.lt(F, O.zero(F), n2(~F, x, y)), h(v2_eq(~F, x, y, O.zero(F), O.zero(F), FO.sumsq_zero(~F, x, y, e), n2_zero_y(~F, x, y, e))))
    case Inr{Inr{g}}:
      g

def sumsq_pos(~F: O.OField, +x: O.C(F), +y: O.C(F), h: {G.V2{x, y} == G.vzero(~F) : G.Vec(~F)} -> Empty) -> O.lt(F, O.zero(F), n2(~F, x, y)):
  sumsq_pos.go(~F, x, y, h, O.lt_total(F)(n2(~F, x, y), O.zero(F)))

# Angle
# -----
# w = R u, the rotation (c, s) applied to u


# u = 0 would make dot(R u, v) = 0
def angle.u_ne.lt(~F: O.OField, +ux: O.C(F), +uy: O.C(F), +vx: O.C(F), +vy: O.C(F), +c: O.C(F), +s: O.C(F), hs: O.lt(F, O.zero(F), G.dot(~F, G.rot(~F, c, s, G.V2{ux, uy}), G.V2{vx, vy})), e: {G.V2{ux, uy} == G.vzero(~F) : G.Vec(~F)}) -> O.lt(F, O.zero(F), O.zero(F)):
  %FR.fring_eq(~F, [c, s, vx, vy], E.ZAdd{E.ZMul{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZMul{E.ZVar{1n}, E.ZCst{S.Z0{}}}}, E.ZVar{2n}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZCst{S.Z0{}}}, E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}}, E.ZVar{3n}}}, E.ZCst{S.Z0{}}, {==}) : O.lt(F, O.zero(F), _)
  %e : O.lt(F, O.zero(F), G.dot(~F, G.rot(~F, c, s, _), G.V2{vx, vy}))
  hs

# (c, s) = 0 would too
def angle.cs_ne.lt(~F: O.OField, +ux: O.C(F), +uy: O.C(F), +vx: O.C(F), +vy: O.C(F), +c: O.C(F), +s: O.C(F), hs: O.lt(F, O.zero(F), G.dot(~F, G.rot(~F, c, s, G.V2{ux, uy}), G.V2{vx, vy})), +e: {G.V2{c, s} == G.vzero(~F) : G.Vec(~F)}) -> O.lt(F, O.zero(F), O.zero(F)):
  %FR.fring_eq(~F, [ux, uy, vx, vy], E.ZAdd{E.ZMul{E.ZSub{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{1n}}}, E.ZVar{2n}}, E.ZMul{E.ZAdd{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{1n}}}, E.ZVar{3n}}}, E.ZCst{S.Z0{}}, {==}) : O.lt(F, O.zero(F), _)
  %x_eq(~F, c, s, O.zero(F), O.zero(F), e) : O.lt(F, O.zero(F), G.dot(~F, G.rot(~F, _, O.zero(F), G.V2{ux, uy}), G.V2{vx, vy}))
  %y_eq(~F, c, s, O.zero(F), O.zero(F), e) : O.lt(F, O.zero(F), G.dot(~F, G.rot(~F, c, _, G.V2{ux, uy}), G.V2{vx, vy}))
  hs

def angle.l.go(~F: O.OField, +ux: O.C(F), +uy: O.C(F), +vx: O.C(F), +vy: O.C(F), +c: O.C(F), +s: O.C(F), +hz: {O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), vy), O.mul(F, O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)), vx)) == O.zero(F) : O.C(F)}, +hs: O.lt(F, O.zero(F), O.add(F, O.mul(F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), vx), O.mul(F, O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)), vy))), t: Or(O.lt(F, n2(~F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), O.add(F, O.mul(F, s, ux), O.mul(F, c, uy))), O.zero(F)), Or({n2(~F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), O.add(F, O.mul(F, s, ux), O.mul(F, c, uy))) == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), n2(~F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), O.add(F, O.mul(F, s, ux), O.mul(F, c, uy))))))) -> Exists(O.C(F), l => O.lt(F, O.zero(F), l) & {G.V2{vx, vy} == G.scale(~F, l, G.rot(~F, c, s, G.V2{ux, uy})) : G.Vec(~F)}):
  match t:
    case Inl{l}:
      FO.absurd(Exists(O.C(F), l => O.lt(F, O.zero(F), l) & {G.V2{vx, vy} == G.scale(~F, l, G.rot(~F, c, s, G.V2{ux, uy})) : G.Vec(~F)}), O.lt_irrefl(F)(O.zero(F))(FO.le_lt_trans(~F, O.zero(F), n2(~F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), O.add(F, O.mul(F, s, ux), O.mul(F, c, uy))), O.zero(F), n2_nonneg(~F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), O.add(F, O.mul(F, s, ux), O.mul(F, c, uy))), l)))
    case Inr{Inl{+e}}:
      +ewx = FO.sumsq_zero(~F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)), e)
      +ewy = n2_zero_y(~F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)), e)
      FO.absurd(Exists(O.C(F), l => O.lt(F, O.zero(F), l) & {G.V2{vx, vy} == G.scale(~F, l, G.rot(~F, c, s, G.V2{ux, uy})) : G.Vec(~F)}), FO.ne_of_gt(~F, O.add(F, O.mul(F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), vx), O.mul(F, O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)), vy)), O.zero(F), hs)(FO.cert2(~F, O.add(F, O.mul(F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), vx), O.mul(F, O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)), vy)), vx, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), vy, O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)), FR.fring_eq(~F, [c, s, ux, uy, vx, vy], E.ZAdd{E.ZMul{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZVar{4n}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}, E.ZVar{5n}}}, E.ZAdd{E.ZMul{E.ZVar{4n}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}}, E.ZMul{E.ZVar{5n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}}}, {==}), ewx, ewy)))
    case Inr{Inr{+g}}:
      (O.mul(F, O.add(F, O.mul(F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), vx), O.mul(F, O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)), vy)), O.inv(F, n2(~F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), O.add(F, O.mul(F, s, ux), O.mul(F, c, uy))))),
       (O.lt_mul(F)(O.add(F, O.mul(F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), vx), O.mul(F, O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)), vy)), O.inv(F, n2(~F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)))))(hs)(FO.inv_pos(~F, n2(~F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), O.add(F, O.mul(F, s, ux), O.mul(F, c, uy))), g)),
        par_sound.pos(~F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)), vx, vy, hz, g)))

def angle_sound(~F: O.OField, +ux: O.C(F), +uy: O.C(F), +vx: O.C(F), +vy: O.C(F), +c: O.C(F), +s: O.C(F), +hz: {O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), vy), O.mul(F, O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)), vx)) == O.zero(F) : O.C(F)}, +hs: O.lt(F, O.zero(F), O.add(F, O.mul(F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), vx), O.mul(F, O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)), vy)))) -> G.angle(~F, G.V2{ux, uy}, G.V2{vx, vy}, c, s):
  (e => O.lt_irrefl(F)(O.zero(F))(angle.u_ne.lt(~F, ux, uy, vx, vy, c, s, hs, e)),
   (e => O.lt_irrefl(F)(O.zero(F))(angle.cs_ne.lt(~F, ux, uy, vx, vy, c, s, hs, e)),
    angle.l.go(~F, ux, uy, vx, vy, c, s, hz, hs, O.lt_total(F)(n2(~F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), O.add(F, O.mul(F, s, ux), O.mul(F, c, uy))), O.zero(F)))))

def angle_complete.cross(~F: O.OField, +ux: O.C(F), +uy: O.C(F), +vx: O.C(F), +vy: O.C(F), +c: O.C(F), +s: O.C(F), +l: O.C(F), e: {G.V2{vx, vy} == G.scale(~F, l, G.rot(~F, c, s, G.V2{ux, uy})) : G.Vec(~F)}) -> {O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), vy), O.mul(F, O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)), vx)) == O.zero(F) : O.C(F)}:
  %Equal.sym(G.Vec(~F), G.V2{vx, vy}, G.scale(~F, l, G.rot(~F, c, s, G.V2{ux, uy})), e) : {G.cross(~F, G.rot(~F, c, s, G.V2{ux, uy}), _) == O.zero(F) : O.C(F)}
  FR.fring_eq(~F, [c, s, ux, uy, l], E.ZSub{E.ZMul{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZMul{E.ZVar{4n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}, E.ZMul{E.ZVar{4n}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}}}}, E.ZCst{S.Z0{}}, {==})

def angle_complete.dot(~F: O.OField, +ux: O.C(F), +uy: O.C(F), +vx: O.C(F), +vy: O.C(F), +c: O.C(F), +s: O.C(F), +l: O.C(F), lpos: O.lt(F, O.zero(F), l), e: {G.V2{vx, vy} == G.scale(~F, l, G.rot(~F, c, s, G.V2{ux, uy})) : G.Vec(~F)}, nu: {G.V2{ux, uy} == G.vzero(~F) : G.Vec(~F)} -> Empty, ncs: {G.V2{c, s} == G.vzero(~F) : G.Vec(~F)} -> Empty) -> O.lt(F, O.zero(F), O.add(F, O.mul(F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), vx), O.mul(F, O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)), vy))):
  %Equal.sym(G.Vec(~F), G.V2{vx, vy}, G.scale(~F, l, G.rot(~F, c, s, G.V2{ux, uy})), e) : O.lt(F, O.zero(F), G.dot(~F, G.rot(~F, c, s, G.V2{ux, uy}), _))
  %FR.fring_eq(~F, [c, s, ux, uy, l], E.ZMul{E.ZVar{4n}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{0n}}, E.ZMul{E.ZVar{1n}, E.ZVar{1n}}}, E.ZAdd{E.ZMul{E.ZVar{2n}, E.ZVar{2n}}, E.ZMul{E.ZVar{3n}, E.ZVar{3n}}}}}, E.ZAdd{E.ZMul{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZMul{E.ZVar{4n}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}, E.ZMul{E.ZVar{4n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}}}}, {==}) : O.lt(F, O.zero(F), _)
  O.lt_mul(F)(l, O.mul(F, n2(~F, c, s), n2(~F, ux, uy)))(lpos)(O.lt_mul(F)(n2(~F, c, s), n2(~F, ux, uy))(sumsq_pos(~F, c, s, ncs))(sumsq_pos(~F, ux, uy, nu)))

def angle_complete.go(~F: O.OField, +ux: O.C(F), +uy: O.C(F), +vx: O.C(F), +vy: O.C(F), +c: O.C(F), +s: O.C(F), +l: O.C(F), +lpos: O.lt(F, O.zero(F), l), +e: {G.V2{vx, vy} == G.scale(~F, l, G.rot(~F, c, s, G.V2{ux, uy})) : G.Vec(~F)}, nu: {G.V2{ux, uy} == G.vzero(~F) : G.Vec(~F)} -> Empty, ncs: {G.V2{c, s} == G.vzero(~F) : G.Vec(~F)} -> Empty) -> K.Both({O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), vy), O.mul(F, O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)), vx)) == O.zero(F) : O.C(F)}, Unit) & K.Both(O.lt(F, O.zero(F), O.add(F, O.mul(F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), vx), O.mul(F, O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)), vy))), Unit):
  ((angle_complete.cross(~F, ux, uy, vx, vy, c, s, l, e), Unit{}), (angle_complete.dot(~F, ux, uy, vx, vy, c, s, l, lpos, e, nu, ncs), Unit{}))

def angle_complete(~F: O.OField, +ux: O.C(F), +uy: O.C(F), +vx: O.C(F), +vy: O.C(F), +c: O.C(F), +s: O.C(F), h: G.angle(~F, G.V2{ux, uy}, G.V2{vx, vy}, c, s)) -> K.Both({O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), vy), O.mul(F, O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)), vx)) == O.zero(F) : O.C(F)}, Unit) & K.Both(O.lt(F, O.zero(F), O.add(F, O.mul(F, O.sub(~F, O.mul(F, c, ux), O.mul(F, s, uy)), vx), O.mul(F, O.add(F, O.mul(F, s, ux), O.mul(F, c, uy)), vy))), Unit):
  (nu, x) = h
  (ncs, y) = x
  (l, z) = y
  (lpos, e) = z
  angle_complete.go(~F, ux, uy, vx, vy, c, s, l, lpos, e, nu, ncs)

def Angle.sound.r(~F: O.OField, +env: List<&2, O.C(F)>, +a0x: Nat, +a0y: Nat, +a1x: Nat, +a1y: Nat, +b0x: Nat, +b0y: Nat, +b1x: Nat, +b1y: Nat, +ra: Bool, +rb: Bool, +c: E.QExpr, +s: E.QExpr, h: MF.H.Angle(~F, env, K.Seg{K.Pt{a0x, a0y}, K.Pt{a1x, a1y}}, ra, K.Seg{K.Pt{b0x, b0y}, K.Pt{b1x, b1y}}, rb, c, s)) -> MF.M.Angle(~F, env, K.Seg{K.Pt{a0x, a0y}, K.Pt{a1x, a1y}}, ra, K.Seg{K.Pt{b0x, b0y}, K.Pt{b1x, b1y}}, rb, c, s):
  match ra rb:
    case False{} False{}:
      ((hz, u1), (hs, u2)) = h
      angle_sound(~F, dx(~F, env, a1x, a0x), dx(~F, env, a1y, a0y), dx(~F, env, b1x, b0x), dx(~F, env, b1y, b0y), O.eval(~F, env, c), O.eval(~F, env, s), hz, hs)
    case False{} True{}:
      ((hz, u1), (hs, u2)) = h
      angle_sound(~F, dx(~F, env, a1x, a0x), dx(~F, env, a1y, a0y), dx(~F, env, b0x, b1x), dx(~F, env, b0y, b1y), O.eval(~F, env, c), O.eval(~F, env, s), hz, hs)
    case True{} False{}:
      ((hz, u1), (hs, u2)) = h
      angle_sound(~F, dx(~F, env, a0x, a1x), dx(~F, env, a0y, a1y), dx(~F, env, b1x, b0x), dx(~F, env, b1y, b0y), O.eval(~F, env, c), O.eval(~F, env, s), hz, hs)
    case True{} True{}:
      ((hz, u1), (hs, u2)) = h
      angle_sound(~F, dx(~F, env, a0x, a1x), dx(~F, env, a0y, a1y), dx(~F, env, b0x, b1x), dx(~F, env, b0y, b1y), O.eval(~F, env, c), O.eval(~F, env, s), hz, hs)

def Angle.sound(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Seg, +ra: Bool, +b: K.Seg, +rb: Bool, +c: E.QExpr, +s: E.QExpr, w: MF.W.Angle(a, ra, b, rb, c, s), h: MF.H.Angle(~F, env, a, ra, b, rb, c, s)) -> MF.M.Angle(~F, env, a, ra, b, rb, c, s):
  match a b:
    case K.Seg{K.Pt{a0x, a0y}, K.Pt{a1x, a1y}} K.Seg{K.Pt{b0x, b0y}, K.Pt{b1x, b1y}}:
      Angle.sound.r(~F, env, a0x, a0y, a1x, a1y, b0x, b0y, b1x, b1y, ra, rb, c, s, h)

def Angle.complete.r(~F: O.OField, +env: List<&2, O.C(F)>, +a0x: Nat, +a0y: Nat, +a1x: Nat, +a1y: Nat, +b0x: Nat, +b0y: Nat, +b1x: Nat, +b1y: Nat, +ra: Bool, +rb: Bool, +c: E.QExpr, +s: E.QExpr, h: MF.M.Angle(~F, env, K.Seg{K.Pt{a0x, a0y}, K.Pt{a1x, a1y}}, ra, K.Seg{K.Pt{b0x, b0y}, K.Pt{b1x, b1y}}, rb, c, s)) -> MF.H.Angle(~F, env, K.Seg{K.Pt{a0x, a0y}, K.Pt{a1x, a1y}}, ra, K.Seg{K.Pt{b0x, b0y}, K.Pt{b1x, b1y}}, rb, c, s):
  match ra rb:
    case False{} False{}:
      angle_complete(~F, dx(~F, env, a1x, a0x), dx(~F, env, a1y, a0y), dx(~F, env, b1x, b0x), dx(~F, env, b1y, b0y), O.eval(~F, env, c), O.eval(~F, env, s), h)
    case False{} True{}:
      angle_complete(~F, dx(~F, env, a1x, a0x), dx(~F, env, a1y, a0y), dx(~F, env, b0x, b1x), dx(~F, env, b0y, b1y), O.eval(~F, env, c), O.eval(~F, env, s), h)
    case True{} False{}:
      angle_complete(~F, dx(~F, env, a0x, a1x), dx(~F, env, a0y, a1y), dx(~F, env, b1x, b0x), dx(~F, env, b1y, b0y), O.eval(~F, env, c), O.eval(~F, env, s), h)
    case True{} True{}:
      angle_complete(~F, dx(~F, env, a0x, a1x), dx(~F, env, a0y, a1y), dx(~F, env, b0x, b1x), dx(~F, env, b0y, b1y), O.eval(~F, env, c), O.eval(~F, env, s), h)

def Angle.complete(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Seg, +ra: Bool, +b: K.Seg, +rb: Bool, +c: E.QExpr, +s: E.QExpr, h: MF.M.Angle(~F, env, a, ra, b, rb, c, s)) -> MF.H.Angle(~F, env, a, ra, b, rb, c, s):
  match a b:
    case K.Seg{K.Pt{a0x, a0y}, K.Pt{a1x, a1y}} K.Seg{K.Pt{b0x, b0y}, K.Pt{b1x, b1y}}:
      Angle.complete.r(~F, env, a0x, a0y, a1x, a1y, b0x, b0y, b1x, b1y, ra, rb, c, s, h)

# Point-line distance
# -------------------
# Oriented line a → b, w = b - a, z = p - a, n = |w|², D = dot(z, w),
# Cr = cross(w, z); the foot of the perpendicular is f = a + t w, t = D / n.


# 0 ≤ orient(a, b, p) = d l
def ld.orient(~F: O.OField, +ax: O.C(F), +ay: O.C(F), +bx: O.C(F), +by: O.C(F), +px: O.C(F), +py: O.C(F), +d: O.C(F), +l: O.C(F), h1: {O.sub(~F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax))), O.mul(F, d, l)) == O.zero(F) : O.C(F)}, hlp: O.lt(F, O.zero(F), l), hd: O.le(~F, O.zero(F), d)) -> O.le(~F, O.zero(F), O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax)))):
  %Equal.sym(O.C(F), O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax))), O.mul(F, d, l), FO.eq_of_sub(~F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax))), O.mul(F, d, l), h1)) : O.le(~F, O.zero(F), _)
  FO.mul_nonneg(~F, d, l, hd, FO.lt_le(~F, O.zero(F), l, hlp))

# 0 < n = l l
def ld.npos(~F: O.OField, +ax: O.C(F), +ay: O.C(F), +bx: O.C(F), +by: O.C(F), +l: O.C(F), hl: {O.sub(~F, O.mul(F, l, l), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay))) == O.zero(F) : O.C(F)}, +hlp: O.lt(F, O.zero(F), l)) -> O.lt(F, O.zero(F), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay))):
  %FO.eq_of_sub(~F, O.mul(F, l, l), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), hl) : O.lt(F, O.zero(F), _)
  O.lt_mul(F)(l, l)(hlp)(hlp)

def ld_sound(~F: O.OField, +ax: O.C(F), +ay: O.C(F), +bx: O.C(F), +by: O.C(F), +px: O.C(F), +py: O.C(F), +d: O.C(F), +l: O.C(F), +h1: {O.sub(~F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax))), O.mul(F, d, l)) == O.zero(F) : O.C(F)}, +hl: {O.sub(~F, O.mul(F, l, l), O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay)))) == O.zero(F) : O.C(F)}, +hlp: O.lt(F, O.zero(F), l), +hd: O.le(~F, O.zero(F), d)) -> G.line_dist(~F, G.V2{px, py}, G.V2{ax, ay}, G.V2{bx, by}, d):
  +hn = FO.inv_rel(~F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), FO.ne_of_gt(~F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), O.zero(F), ld.npos(~F, ax, ay, bx, by, l, hl, hlp)))
  (ld.orient(~F, ax, ay, bx, by, px, py, d, l, h1, hlp, hd),
   (G.V2{O.add(F, ax, O.mul(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, bx, ax))), O.add(F, ay, O.mul(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, by, ay)))},
    (Inl{(O.mul(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), v2_eq(~F, O.sub(~F, O.add(F, ax, O.mul(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, bx, ax))), ax), O.sub(~F, O.add(F, ay, O.mul(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, by, ay))), ay), O.mul(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, bx, ax)), O.mul(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, by, ay)), FR.fring_eq(~F, [ax, ay, bx, by, px, py, d, l, O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))], E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}, E.ZVar{8n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}}, E.ZVar{0n}}, E.ZMul{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}, E.ZVar{8n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, {==}), FR.fring_eq(~F, [ax, ay, bx, by, px, py, d, l, O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))], E.ZSub{E.ZAdd{E.ZVar{1n}, E.ZMul{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}, E.ZVar{8n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}, E.ZVar{8n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}, {==})))},
     (FO.cert1(~F, O.add(F, O.mul(F, O.sub(~F, px, O.add(F, ax, O.mul(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, bx, ax)))), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, O.add(F, ay, O.mul(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, by, ay)))), O.sub(~F, by, ay))), O.neg(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay)))), O.sub(~F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.one(F)), FR.fring_eq(~F, [ax, ay, bx, by, px, py, d, l, O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))], E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}, E.ZVar{8n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZAdd{E.ZVar{1n}, E.ZMul{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}, E.ZVar{8n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}, E.ZMul{E.ZNeg{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}, E.ZVar{8n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), hn),
      (hd, FO.eq_of_sub(~F, O.add(F, O.mul(F, O.sub(~F, px, O.add(F, ax, O.mul(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, bx, ax)))), O.sub(~F, px, O.add(F, ax, O.mul(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, bx, ax))))), O.mul(F, O.sub(~F, py, O.add(F, ay, O.mul(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, by, ay)))), O.sub(~F, py, O.add(F, ay, O.mul(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, by, ay)))))), O.mul(F, d, d), FO.cert3(~F, O.sub(~F, O.add(F, O.mul(F, O.sub(~F, px, O.add(F, ax, O.mul(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, bx, ax)))), O.sub(~F, px, O.add(F, ax, O.mul(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, bx, ax))))), O.mul(F, O.sub(~F, py, O.add(F, ay, O.mul(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, by, ay)))), O.sub(~F, py, O.add(F, ay, O.mul(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, by, ay)))))), O.mul(F, d, d)), O.add(F, O.sub(~F, O.mul(F, d, d), O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, px, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, py, ay)))), O.mul(F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay))), O.add(F, O.mul(F, O.sub(~F, px, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, ay), O.sub(~F, by, ay)))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay))))), O.sub(~F, O.mul(F, O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.one(F)), O.mul(F, O.mul(F, d, d), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, O.mul(F, l, l), O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay)))), O.mul(F, O.add(F, O.mul(F, d, l), O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax)))), O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))), O.sub(~F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax))), O.mul(F, d, l)), FR.fring_eq(~F, [ax, ay, bx, by, px, py, d, l, O.inv(F, n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)))], E.ZSub{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}, E.ZVar{8n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}}}, E.ZSub{E.ZVar{4n}, E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}, E.ZVar{8n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZAdd{E.ZVar{1n}, E.ZMul{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}, E.ZVar{8n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}}, E.ZSub{E.ZVar{5n}, E.ZAdd{E.ZVar{1n}, E.ZMul{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}, E.ZVar{8n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}}}}, E.ZMul{E.ZVar{6n}, E.ZVar{6n}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZAdd{E.ZSub{E.ZMul{E.ZVar{6n}, E.ZVar{6n}}, E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZVar{0n}}, E.ZSub{E.ZVar{4n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZVar{1n}}, E.ZSub{E.ZVar{5n}, E.ZVar{1n}}}}}, E.ZMul{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}, E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}}, E.ZVar{8n}}}, E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}, E.ZVar{8n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZMul{E.ZMul{E.ZVar{6n}, E.ZVar{6n}}, E.ZVar{8n}}, E.ZSub{E.ZMul{E.ZVar{7n}, E.ZVar{7n}}, E.ZAdd{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}}}}, E.ZMul{E.ZMul{E.ZAdd{E.ZMul{E.ZVar{6n}, E.ZVar{7n}}, E.ZSub{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{5n}, E.ZVar{1n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{4n}, E.ZVar{0n}}}}}, E.ZVar{8n}}, E.ZSub{E.ZSub{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{5n}, E.ZVar{1n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{4n}, E.ZVar{0n}}}}, E.ZMul{E.ZVar{6n}, E.ZVar{7n}}}}}, {==}), hn, hl, h1)))))))

# the exact form from the meaning: cross² = (d l)², both sides ≥ 0
def ld_complete.fin(~F: O.OField, -e2t: O.C(F), +ax: O.C(F), +ay: O.C(F), +bx: O.C(F), +by: O.C(F), +px: O.C(F), +py: O.C(F), +d: O.C(F), +l: O.C(F), +fx: O.C(F), +fy: O.C(F), horient: O.le(~F, O.zero(F), O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax)))), fon: G.on_line(~F, G.V2{fx, fy}, G.V2{ax, ay}, G.V2{bx, by}), +fdot: {O.add(F, O.mul(F, O.sub(~F, px, fx), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, fy), O.sub(~F, by, ay))) == O.zero(F) : O.C(F)}, +hd: O.le(~F, O.zero(F), d), +fdd: {O.add(F, O.mul(F, O.sub(~F, px, fx), O.sub(~F, px, fx)), O.mul(F, O.sub(~F, py, fy), O.sub(~F, py, fy))) == O.mul(F, d, d) : O.C(F)}, +hl: {O.sub(~F, O.mul(F, l, l), O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay)))) == O.zero(F) : O.C(F)}, e2: {e2t == O.zero(F) : O.C(F)}, +hlp: O.lt(F, O.zero(F), l)) -> K.Both({O.sub(~F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax))), O.mul(F, d, l)) == O.zero(F) : O.C(F)}, K.Both({e2t == O.zero(F) : O.C(F)}, Unit)) & K.Both(O.lt(F, O.zero(F), l), K.Both(O.le(~F, O.zero(F), d), Unit)):
  +c0 = par_complete(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay), O.sub(~F, fx, ax), O.sub(~F, fy, ay), fon)
  +dd = FO.sub_of_eq(~F, O.add(F, O.mul(F, O.sub(~F, px, fx), O.sub(~F, px, fx)), O.mul(F, O.sub(~F, py, fy), O.sub(~F, py, fy))), O.mul(F, d, d), fdd)
  ((FO.sub_of_eq(~F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax))), O.mul(F, d, l), FO.sq_eq(~F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax))), O.mul(F, d, l), horient, FO.mul_nonneg(~F, d, l, hd, FO.lt_le(~F, O.zero(F), l, hlp)),
      FO.eq_of_sub(~F, O.mul(F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax))), O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax)))), O.mul(F, O.mul(F, d, l), O.mul(F, d, l)), FO.cert4(~F, O.sub(~F, O.mul(F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax))), O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax)))), O.mul(F, O.mul(F, d, l), O.mul(F, d, l))), O.neg(F, O.mul(F, d, d)), O.sub(~F, O.mul(F, l, l), O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay)))), O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay))), O.sub(~F, O.add(F, O.mul(F, O.sub(~F, px, fx), O.sub(~F, px, fx)), O.mul(F, O.sub(~F, py, fy), O.sub(~F, py, fy))), O.mul(F, d, d)), O.neg(F, O.add(F, O.mul(F, O.sub(~F, px, fx), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, fy), O.sub(~F, by, ay)))), O.add(F, O.mul(F, O.sub(~F, px, fx), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, py, fy), O.sub(~F, by, ay))), O.add(F, O.mul(F, O.ofz(~F, S.Zpos{S.XO{S.XH{}}}), O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, fy)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, fx)))), O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, fy, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, fx, ax)))), O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, fy, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, fx, ax))), FR.fring_eq(~F, [ax, ay, bx, by, px, py, d, l, fx, fy], E.ZSub{E.ZMul{E.ZSub{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{5n}, E.ZVar{1n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{4n}, E.ZVar{0n}}}}, E.ZSub{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{5n}, E.ZVar{1n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{4n}, E.ZVar{0n}}}}}, E.ZMul{E.ZMul{E.ZVar{6n}, E.ZVar{7n}}, E.ZMul{E.ZVar{6n}, E.ZVar{7n}}}}, E.ZAdd{E.ZAdd{E.ZAdd{E.ZMul{E.ZNeg{E.ZMul{E.ZVar{6n}, E.ZVar{6n}}}, E.ZSub{E.ZMul{E.ZVar{7n}, E.ZVar{7n}}, E.ZAdd{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}, E.ZSub{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZVar{8n}}, E.ZSub{E.ZVar{4n}, E.ZVar{8n}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZVar{9n}}, E.ZSub{E.ZVar{5n}, E.ZVar{9n}}}}, E.ZMul{E.ZVar{6n}, E.ZVar{6n}}}}}, E.ZMul{E.ZNeg{E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZVar{8n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZVar{9n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}}, E.ZAdd{E.ZMul{E.ZSub{E.ZVar{4n}, E.ZVar{8n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{5n}, E.ZVar{9n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZCst{S.Zpos{S.XO{S.XH{}}}}, E.ZSub{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{5n}, E.ZVar{9n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{4n}, E.ZVar{8n}}}}}, E.ZSub{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{9n}, E.ZVar{1n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{8n}, E.ZVar{0n}}}}}, E.ZSub{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{9n}, E.ZVar{1n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{8n}, E.ZVar{0n}}}}}}, {==}), hl, dd, fdot, c0)))),
    (e2, Unit{})),
   (hlp, (hd, Unit{})))

def ld_complete.f(~F: O.OField, -e2t: O.C(F), +ax: O.C(F), +ay: O.C(F), +bx: O.C(F), +by: O.C(F), +px: O.C(F), +py: O.C(F), +d: O.C(F), +l: O.C(F), horient: O.le(~F, O.zero(F), O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax)))), +f: G.Vec(~F), y: G.on_line(~F, f, G.V2{ax, ay}, G.V2{bx, by}) & ({G.dot(~F, G.sub(~F, G.V2{px, py}, f), G.sub(~F, G.V2{bx, by}, G.V2{ax, ay})) == O.zero(F) : O.C(F)} & G.dist(~F, f, G.V2{px, py}, d)), +hl: {O.sub(~F, O.mul(F, l, l), O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay)))) == O.zero(F) : O.C(F)}, e2: {e2t == O.zero(F) : O.C(F)}, +hlp: O.lt(F, O.zero(F), l)) -> K.Both({O.sub(~F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax))), O.mul(F, d, l)) == O.zero(F) : O.C(F)}, K.Both({e2t == O.zero(F) : O.C(F)}, Unit)) & K.Both(O.lt(F, O.zero(F), l), K.Both(O.le(~F, O.zero(F), d), Unit)):
  match f:
    case G.V2{fx, fy}:
      (fon, z) = y
      (fdot, fdist) = z
      (hd, fdd) = fdist
      ld_complete.fin(~F, e2t, ax, ay, bx, by, px, py, d, l, fx, fy, horient, fon, fdot, hd, fdd, hl, e2, hlp)

def ld_complete(~F: O.OField, -e2t: O.C(F), +ax: O.C(F), +ay: O.C(F), +bx: O.C(F), +by: O.C(F), +px: O.C(F), +py: O.C(F), +d: O.C(F), +l: O.C(F), h: G.line_dist(~F, G.V2{px, py}, G.V2{ax, ay}, G.V2{bx, by}, d), +hl: {O.sub(~F, O.mul(F, l, l), O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay)))) == O.zero(F) : O.C(F)}, e2: {e2t == O.zero(F) : O.C(F)}, +hlp: O.lt(F, O.zero(F), l)) -> K.Both({O.sub(~F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax))), O.mul(F, d, l)) == O.zero(F) : O.C(F)}, K.Both({e2t == O.zero(F) : O.C(F)}, Unit)) & K.Both(O.lt(F, O.zero(F), l), K.Both(O.le(~F, O.zero(F), d), Unit)):
  (horient, x) = h
  (f, y) = x
  ld_complete.f(~F, e2t, ax, ay, bx, by, px, py, d, l, horient, f, y, hl, e2, hlp)

# the same with the line taken from b to a

# |a - b|² = |b - a|²

def ld.flip(~F: O.OField, +ax: O.C(F), +ay: O.C(F), +bx: O.C(F), +by: O.C(F), +l: O.C(F), h2: {O.sub(~F, O.mul(F, l, l), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay))) == O.zero(F) : O.C(F)}) -> {O.sub(~F, O.mul(F, l, l), O.add(F, O.mul(F, O.sub(~F, ax, bx), O.sub(~F, ax, bx)), O.mul(F, O.sub(~F, ay, by), O.sub(~F, ay, by)))) == O.zero(F) : O.C(F)}:
  FO.cert1(~F, O.sub(~F, O.mul(F, l, l), O.add(F, O.mul(F, O.sub(~F, ax, bx), O.sub(~F, ax, bx)), O.mul(F, O.sub(~F, ay, by), O.sub(~F, ay, by)))), O.one(F), O.sub(~F, O.mul(F, l, l), O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay)))), FR.fring_eq(~F, [bx, by, ax, ay, l], E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{4n}}, E.ZAdd{E.ZMul{E.ZSub{E.ZVar{2n}, E.ZVar{0n}}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, E.ZMul{E.ZSub{E.ZVar{3n}, E.ZVar{1n}}, E.ZSub{E.ZVar{3n}, E.ZVar{1n}}}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{4n}}, E.ZAdd{E.ZMul{E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, E.ZSub{E.ZVar{0n}, E.ZVar{2n}}}, E.ZMul{E.ZSub{E.ZVar{1n}, E.ZVar{3n}}, E.ZSub{E.ZVar{1n}, E.ZVar{3n}}}}}}, {==}), h2)

def ld_full_f(~F: O.OField, +ax: O.C(F), +ay: O.C(F), +bx: O.C(F), +by: O.C(F), +px: O.C(F), +py: O.C(F), +d: O.C(F), +l: O.C(F), +h1: {O.sub(~F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax))), O.mul(F, d, l)) == O.zero(F) : O.C(F)}, +h2: {O.sub(~F, O.mul(F, l, l), O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay)))) == O.zero(F) : O.C(F)}, +hlp: O.lt(F, O.zero(F), l), +hd: O.le(~F, O.zero(F), d)) -> O.lt(F, O.zero(F), l) & (G.dist(~F, G.V2{ax, ay}, G.V2{bx, by}, l) & G.line_dist(~F, G.V2{px, py}, G.V2{ax, ay}, G.V2{bx, by}, d)):
  (hlp, ((FO.lt_le(~F, O.zero(F), l, hlp), Equal.sym(O.C(F), O.mul(F, l, l), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), FO.eq_of_sub(~F, O.mul(F, l, l), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), h2))),
    ld_sound(~F, ax, ay, bx, by, px, py, d, l, h1, h2, hlp, hd)))

def ld_full_t(~F: O.OField, +ax: O.C(F), +ay: O.C(F), +bx: O.C(F), +by: O.C(F), +px: O.C(F), +py: O.C(F), +d: O.C(F), +l: O.C(F), +h1: {O.sub(~F, O.sub(~F, O.mul(F, O.sub(~F, ax, bx), O.sub(~F, py, by)), O.mul(F, O.sub(~F, ay, by), O.sub(~F, px, bx))), O.mul(F, d, l)) == O.zero(F) : O.C(F)}, +h2: {O.sub(~F, O.mul(F, l, l), O.add(F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, bx, ax)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, by, ay)))) == O.zero(F) : O.C(F)}, +hlp: O.lt(F, O.zero(F), l), +hd: O.le(~F, O.zero(F), d)) -> O.lt(F, O.zero(F), l) & (G.dist(~F, G.V2{ax, ay}, G.V2{bx, by}, l) & G.line_dist(~F, G.V2{px, py}, G.V2{bx, by}, G.V2{ax, ay}, d)):
  (hlp, ((FO.lt_le(~F, O.zero(F), l, hlp), Equal.sym(O.C(F), O.mul(F, l, l), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), FO.eq_of_sub(~F, O.mul(F, l, l), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), h2))),
    ld_sound(~F, bx, by, ax, ay, px, py, d, l, h1, ld.flip(~F, ax, ay, bx, by, l, h2), hlp, hd)))

def LineDistance.sound.r(~F: O.OField, +env: List<&2, O.C(F)>, +px: Nat, +py: Nat, +ax: Nat, +ay: Nat, +bx: Nat, +by: Nat, +rev: Bool, +d: E.QExpr, +l: Nat, h: MF.H.LineDistance(~F, env, K.Pt{px, py}, K.Seg{K.Pt{ax, ay}, K.Pt{bx, by}}, rev, d, l)) -> MF.M.LineDistance(~F, env, K.Pt{px, py}, K.Seg{K.Pt{ax, ay}, K.Pt{bx, by}}, rev, d, l):
  match rev:
    case False{}:
      ((h1, (h2, u1)), (hlp, (hd, u2))) = h
      ld_full_f(~F, O.lookup(~F, env, ax), O.lookup(~F, env, ay), O.lookup(~F, env, bx), O.lookup(~F, env, by), O.lookup(~F, env, px), O.lookup(~F, env, py), O.eval(~F, env, d), O.lookup(~F, env, l), h1, h2, hlp, hd)
    case True{}:
      ((h1, (h2, u1)), (hlp, (hd, u2))) = h
      ld_full_t(~F, O.lookup(~F, env, ax), O.lookup(~F, env, ay), O.lookup(~F, env, bx), O.lookup(~F, env, by), O.lookup(~F, env, px), O.lookup(~F, env, py), O.eval(~F, env, d), O.lookup(~F, env, l), h1, h2, hlp, hd)

def LineDistance.sound(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +a: K.Seg, +rev: Bool, +d: E.QExpr, +l: Nat, w: MF.W.LineDistance(p, a, rev, d, l), h: MF.H.LineDistance(~F, env, p, a, rev, d, l)) -> MF.M.LineDistance(~F, env, p, a, rev, d, l):
  match p a:
    case K.Pt{px, py} K.Seg{K.Pt{ax, ay}, K.Pt{bx, by}}:
      LineDistance.sound.r(~F, env, px, py, ax, ay, bx, by, rev, d, l, h)

# |b - a|² = l l, from the meaning
def ld.e2(~F: O.OField, +ax: O.C(F), +ay: O.C(F), +bx: O.C(F), +by: O.C(F), +l: O.C(F), he: {n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)) == O.mul(F, l, l) : O.C(F)}) -> {O.sub(~F, O.mul(F, l, l), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay))) == O.zero(F) : O.C(F)}:
  FO.sub_of_eq(~F, O.mul(F, l, l), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), Equal.sym(O.C(F), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay)), O.mul(F, l, l), he))

def ld_cfull_f.go(~F: O.OField, +ax: O.C(F), +ay: O.C(F), +bx: O.C(F), +by: O.C(F), +px: O.C(F), +py: O.C(F), +d: O.C(F), +l: O.C(F), +hlp: O.lt(F, O.zero(F), l), +e2: {O.sub(~F, O.mul(F, l, l), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay))) == O.zero(F) : O.C(F)}, hline: G.line_dist(~F, G.V2{px, py}, G.V2{ax, ay}, G.V2{bx, by}, d)) -> K.Both({O.sub(~F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax))), O.mul(F, d, l)) == O.zero(F) : O.C(F)}, K.Both({O.sub(~F, O.mul(F, l, l), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay))) == O.zero(F) : O.C(F)}, Unit)) & K.Both(O.lt(F, O.zero(F), l), K.Both(O.le(~F, O.zero(F), d), Unit)):
  ld_complete(~F, O.sub(~F, O.mul(F, l, l), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay))), ax, ay, bx, by, px, py, d, l, hline, e2, e2, hlp)

def ld_cfull_t.go(~F: O.OField, +ax: O.C(F), +ay: O.C(F), +bx: O.C(F), +by: O.C(F), +px: O.C(F), +py: O.C(F), +d: O.C(F), +l: O.C(F), +hlp: O.lt(F, O.zero(F), l), +e2: {O.sub(~F, O.mul(F, l, l), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay))) == O.zero(F) : O.C(F)}, hline: G.line_dist(~F, G.V2{px, py}, G.V2{bx, by}, G.V2{ax, ay}, d)) -> K.Both({O.sub(~F, O.sub(~F, O.mul(F, O.sub(~F, ax, bx), O.sub(~F, py, by)), O.mul(F, O.sub(~F, ay, by), O.sub(~F, px, bx))), O.mul(F, d, l)) == O.zero(F) : O.C(F)}, K.Both({O.sub(~F, O.mul(F, l, l), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay))) == O.zero(F) : O.C(F)}, Unit)) & K.Both(O.lt(F, O.zero(F), l), K.Both(O.le(~F, O.zero(F), d), Unit)):
  ld_complete(~F, O.sub(~F, O.mul(F, l, l), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay))), bx, by, ax, ay, px, py, d, l, hline, ld.flip(~F, ax, ay, bx, by, l, e2), e2, hlp)

def ld_cfull_f(~F: O.OField, +ax: O.C(F), +ay: O.C(F), +bx: O.C(F), +by: O.C(F), +px: O.C(F), +py: O.C(F), +d: O.C(F), +l: O.C(F), h: O.lt(F, O.zero(F), l) & (G.dist(~F, G.V2{ax, ay}, G.V2{bx, by}, l) & G.line_dist(~F, G.V2{px, py}, G.V2{ax, ay}, G.V2{bx, by}, d))) -> K.Both({O.sub(~F, O.sub(~F, O.mul(F, O.sub(~F, bx, ax), O.sub(~F, py, ay)), O.mul(F, O.sub(~F, by, ay), O.sub(~F, px, ax))), O.mul(F, d, l)) == O.zero(F) : O.C(F)}, K.Both({O.sub(~F, O.mul(F, l, l), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay))) == O.zero(F) : O.C(F)}, Unit)) & K.Both(O.lt(F, O.zero(F), l), K.Both(O.le(~F, O.zero(F), d), Unit)):
  (hlp, x) = h
  (hdist, hline) = x
  (hll, he) = hdist
  ld_cfull_f.go(~F, ax, ay, bx, by, px, py, d, l, hlp, ld.e2(~F, ax, ay, bx, by, l, he), hline)

def ld_cfull_t(~F: O.OField, +ax: O.C(F), +ay: O.C(F), +bx: O.C(F), +by: O.C(F), +px: O.C(F), +py: O.C(F), +d: O.C(F), +l: O.C(F), h: O.lt(F, O.zero(F), l) & (G.dist(~F, G.V2{ax, ay}, G.V2{bx, by}, l) & G.line_dist(~F, G.V2{px, py}, G.V2{bx, by}, G.V2{ax, ay}, d))) -> K.Both({O.sub(~F, O.sub(~F, O.mul(F, O.sub(~F, ax, bx), O.sub(~F, py, by)), O.mul(F, O.sub(~F, ay, by), O.sub(~F, px, bx))), O.mul(F, d, l)) == O.zero(F) : O.C(F)}, K.Both({O.sub(~F, O.mul(F, l, l), n2(~F, O.sub(~F, bx, ax), O.sub(~F, by, ay))) == O.zero(F) : O.C(F)}, Unit)) & K.Both(O.lt(F, O.zero(F), l), K.Both(O.le(~F, O.zero(F), d), Unit)):
  (hlp, x) = h
  (hdist, hline) = x
  (hll, he) = hdist
  ld_cfull_t.go(~F, ax, ay, bx, by, px, py, d, l, hlp, ld.e2(~F, ax, ay, bx, by, l, he), hline)

def LineDistance.complete.r(~F: O.OField, +env: List<&2, O.C(F)>, +px: Nat, +py: Nat, +ax: Nat, +ay: Nat, +bx: Nat, +by: Nat, +rev: Bool, +d: E.QExpr, +l: Nat, h: MF.M.LineDistance(~F, env, K.Pt{px, py}, K.Seg{K.Pt{ax, ay}, K.Pt{bx, by}}, rev, d, l)) -> MF.H.LineDistance(~F, env, K.Pt{px, py}, K.Seg{K.Pt{ax, ay}, K.Pt{bx, by}}, rev, d, l):
  match rev:
    case False{}:
      ld_cfull_f(~F, O.lookup(~F, env, ax), O.lookup(~F, env, ay), O.lookup(~F, env, bx), O.lookup(~F, env, by), O.lookup(~F, env, px), O.lookup(~F, env, py), O.eval(~F, env, d), O.lookup(~F, env, l), h)
    case True{}:
      ld_cfull_t(~F, O.lookup(~F, env, ax), O.lookup(~F, env, ay), O.lookup(~F, env, bx), O.lookup(~F, env, by), O.lookup(~F, env, px), O.lookup(~F, env, py), O.eval(~F, env, d), O.lookup(~F, env, l), h)

def LineDistance.complete(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +a: K.Seg, +rev: Bool, +d: E.QExpr, +l: Nat, h: MF.M.LineDistance(~F, env, p, a, rev, d, l)) -> MF.H.LineDistance(~F, env, p, a, rev, d, l):
  match p a:
    case K.Pt{px, py} K.Seg{K.Pt{ax, ay}, K.Pt{bx, by}}:
      LineDistance.complete.r(~F, env, px, py, ax, ay, bx, by, rev, d, l, h)
# Every kind: the exact form implies the meaning
def means_sound(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, K.Ent>, +k: K.Constraint, w: K.Constraint.wf(es, k), h: K.Constraint.holds(~F, env, es, k)) -> K.Constraint.means(~F, env, es, k):
  match k:
    case K.Coincident{a, b}:
      Coincident.sound(~F, env, K.pt(es, a), K.pt(es, b), w, h)
    case K.Horizontal{a, b}:
      Horizontal.sound(~F, env, K.pt(es, a), K.pt(es, b), w, h)
    case K.Vertical{a, b}:
      Vertical.sound(~F, env, K.pt(es, a), K.pt(es, b), w, h)
    case K.Concentric{a, b}:
      Concentric.sound(~F, env, K.circ(es, a), K.circ(es, b), w, h)
    case K.EqualRadius{a, b}:
      EqualRadius.sound(~F, env, K.circ(es, a), K.circ(es, b), w, h)
    case K.Fix{v, c}:
      Fix.sound(~F, env, v, c, w, h)
    case K.Distance{p, q, d}:
      Distance.sound(~F, env, K.pt(es, p), K.pt(es, q), d, w, h)
    case K.HDistance{p, q, d}:
      HDistance.sound(~F, env, K.pt(es, p), K.pt(es, q), d, w, h)
    case K.VDistance{p, q, d}:
      VDistance.sound(~F, env, K.pt(es, p), K.pt(es, q), d, w, h)
    case K.Radius{c, d}:
      Radius.sound(~F, env, K.circ(es, c), d, w, h)
    case K.Diameter{c, d}:
      Diameter.sound(~F, env, K.circ(es, c), d, w, h)
    case K.LineDistance{p, a, rev, d, l}:
      LineDistance.sound(~F, env, K.pt(es, p), K.seg(es, a), rev, d, l, w, h)
    case K.Angle{a, ra, b, rb, c, s}:
      Angle.sound(~F, env, K.seg(es, a), ra, K.seg(es, b), rb, c, s, w, h)
    case K.EqualLength{a, b}:
      EqualLength.sound(~F, env, K.seg(es, a), K.seg(es, b), w, h)
    case K.Perpendicular{a, b}:
      Perpendicular.sound(~F, env, K.seg(es, a), K.seg(es, b), w, h)
    case K.Parallel{a, b}:
      Parallel.sound(~F, env, K.seg(es, a), K.seg(es, b), w, h)
    case K.OnLine{p, a}:
      OnLine.sound(~F, env, K.pt(es, p), K.seg(es, a), w, h)
    case K.OnCircle{p, c}:
      OnCircle.sound(~F, env, K.pt(es, p), K.circ(es, c), w, h)
    case K.Midpoint{m, a}:
      Midpoint.sound(~F, env, K.pt(es, m), K.seg(es, a), w, h)
    case K.Symmetric{p, q, a}:
      Symmetric.sound(~F, env, K.pt(es, p), K.pt(es, q), K.seg(es, a), w, h)

# Every kind: the meaning implies the exact form
def means_complete(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, K.Ent>, +k: K.Constraint, h: K.Constraint.means(~F, env, es, k)) -> K.Constraint.holds(~F, env, es, k):
  match k:
    case K.Coincident{a, b}:
      Coincident.complete(~F, env, K.pt(es, a), K.pt(es, b), h)
    case K.Horizontal{a, b}:
      Horizontal.complete(~F, env, K.pt(es, a), K.pt(es, b), h)
    case K.Vertical{a, b}:
      Vertical.complete(~F, env, K.pt(es, a), K.pt(es, b), h)
    case K.Concentric{a, b}:
      Concentric.complete(~F, env, K.circ(es, a), K.circ(es, b), h)
    case K.EqualRadius{a, b}:
      EqualRadius.complete(~F, env, K.circ(es, a), K.circ(es, b), h)
    case K.Fix{v, c}:
      Fix.complete(~F, env, v, c, h)
    case K.Distance{p, q, d}:
      Distance.complete(~F, env, K.pt(es, p), K.pt(es, q), d, h)
    case K.HDistance{p, q, d}:
      HDistance.complete(~F, env, K.pt(es, p), K.pt(es, q), d, h)
    case K.VDistance{p, q, d}:
      VDistance.complete(~F, env, K.pt(es, p), K.pt(es, q), d, h)
    case K.Radius{c, d}:
      Radius.complete(~F, env, K.circ(es, c), d, h)
    case K.Diameter{c, d}:
      Diameter.complete(~F, env, K.circ(es, c), d, h)
    case K.LineDistance{p, a, rev, d, l}:
      LineDistance.complete(~F, env, K.pt(es, p), K.seg(es, a), rev, d, l, h)
    case K.Angle{a, ra, b, rb, c, s}:
      Angle.complete(~F, env, K.seg(es, a), ra, K.seg(es, b), rb, c, s, h)
    case K.EqualLength{a, b}:
      EqualLength.complete(~F, env, K.seg(es, a), K.seg(es, b), h)
    case K.Perpendicular{a, b}:
      Perpendicular.complete(~F, env, K.seg(es, a), K.seg(es, b), h)
    case K.Parallel{a, b}:
      Parallel.complete(~F, env, K.seg(es, a), K.seg(es, b), h)
    case K.OnLine{p, a}:
      OnLine.complete(~F, env, K.pt(es, p), K.seg(es, a), h)
    case K.OnCircle{p, c}:
      OnCircle.complete(~F, env, K.pt(es, p), K.circ(es, c), h)
    case K.Midpoint{m, a}:
      Midpoint.complete(~F, env, K.pt(es, m), K.seg(es, a), h)
    case K.Symmetric{p, q, a}:
      Symmetric.complete(~F, env, K.pt(es, p), K.pt(es, q), K.seg(es, a), h)

# Entities
# --------

def ent_sound(~F: O.OField, +env: List<&2, O.C(F)>, e: K.Ent, h: K.Ent.holds(~F, env, e)) -> K.Ent.means(~F, env, e):
  match e:
    case K.Ent{id, cst, K.GPoint{x, y}}:
      Unit{}
    case K.Ent{id, cst, K.GSeg{p, q}}:
      Unit{}
    case K.Ent{id, cst, K.GCirc{c, r}}:
      (hr, u) = h
      hr
    case K.Ent{id, cst, K.GArc{s, f, b}}:
      (hb, u) = h
      hb

def ent_complete(~F: O.OField, +env: List<&2, O.C(F)>, e: K.Ent, h: K.Ent.means(~F, env, e)) -> K.Ent.holds(~F, env, e):
  match e:
    case K.Ent{id, cst, K.GPoint{x, y}}:
      Unit{}
    case K.Ent{id, cst, K.GSeg{p, q}}:
      Unit{}
    case K.Ent{id, cst, K.GCirc{c, r}}:
      (h, Unit{})
    case K.Ent{id, cst, K.GArc{s, f, b}}:
      (h, Unit{})

# Lists of equations and side conditions
# --------------------------------------

def zeros_l(~F: O.OField, +env: List<&2, O.C(F)>, xs: List<&2, E.QExpr>, +ys: List<&2, E.QExpr>, +h: K.Zeros(~F, env, K.cat(xs, ys))) -> K.Zeros(~F, env, xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{x, t}:
      (+hx, +rest) = h
      (hx, zeros_l(~F, env, t, ys, rest))

def zeros_r(~F: O.OField, +env: List<&2, O.C(F)>, xs: List<&2, E.QExpr>, +ys: List<&2, E.QExpr>, +h: K.Zeros(~F, env, K.cat(xs, ys))) -> K.Zeros(~F, env, ys):
  match xs:
    case Nil{}:
      h
    case Con{x, t}:
      (+hx, +rest) = h
      zeros_r(~F, env, t, ys, rest)

def zeros_cat(~F: O.OField, +env: List<&2, O.C(F)>, xs: List<&2, E.QExpr>, +ys: List<&2, E.QExpr>, +a: K.Zeros(~F, env, xs), +b: K.Zeros(~F, env, ys)) -> K.Zeros(~F, env, K.cat(xs, ys)):
  match xs:
    case Nil{}:
      b
    case Con{x, t}:
      (+ha, +ra) = a
      (ha, zeros_cat(~F, env, t, ys, ra, b))

def sides_l(~F: O.OField, +env: List<&2, O.C(F)>, xs: List<&2, K.Side>, +ys: List<&2, K.Side>, +h: K.Sides(~F, env, K.cats(xs, ys))) -> K.Sides(~F, env, xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{K.Gt0{e}, t}:
      (+hx, +rest) = h
      (hx, sides_l(~F, env, t, ys, rest))
    case Con{K.Ge0{e}, t}:
      (+hx, +rest) = h
      (hx, sides_l(~F, env, t, ys, rest))

def sides_r(~F: O.OField, +env: List<&2, O.C(F)>, xs: List<&2, K.Side>, +ys: List<&2, K.Side>, +h: K.Sides(~F, env, K.cats(xs, ys))) -> K.Sides(~F, env, ys):
  match xs:
    case Nil{}:
      h
    case Con{K.Gt0{e}, t}:
      (+hx, +rest) = h
      sides_r(~F, env, t, ys, rest)
    case Con{K.Ge0{e}, t}:
      (+hx, +rest) = h
      sides_r(~F, env, t, ys, rest)

def sides_cat(~F: O.OField, +env: List<&2, O.C(F)>, xs: List<&2, K.Side>, +ys: List<&2, K.Side>, +a: K.Sides(~F, env, xs), +b: K.Sides(~F, env, ys)) -> K.Sides(~F, env, K.cats(xs, ys)):
  match xs:
    case Nil{}:
      b
    case Con{K.Gt0{e}, t}:
      (+ha, +ra) = a
      (ha, sides_cat(~F, env, t, ys, ra, b))
    case Con{K.Ge0{e}, t}:
      (+ha, +ra) = a
      (ha, sides_cat(~F, env, t, ys, ra, b))

# Entities and constraints of a sketch
# ------------------------------------

def ents_sound(~F: O.OField, +env: List<&2, O.C(F)>, xs: List<&2, K.Ent>, +h: K.Sides(~F, env, K.Sketch.sides.ents(xs))) -> K.Sketch.means.ents(~F, env, xs):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      (ent_sound(~F, env, e, sides_l(~F, env, K.Ent.sides(e), K.Sketch.sides.ents(t), h)),
       ents_sound(~F, env, t, sides_r(~F, env, K.Ent.sides(e), K.Sketch.sides.ents(t), h)))

def ents_complete(~F: O.OField, +env: List<&2, O.C(F)>, xs: List<&2, K.Ent>, h: K.Sketch.means.ents(~F, env, xs)) -> K.Sides(~F, env, K.Sketch.sides.ents(xs)):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      (he, ht) = h
      sides_cat(~F, env, K.Ent.sides(e), K.Sketch.sides.ents(t), ent_complete(~F, env, e, he), ents_complete(~F, env, t, ht))

def cons_sound(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, K.Ent>, cs: List<&2, K.Rec>, w: K.Sketch.wf.cons(es, cs), +hz: K.Zeros(~F, env, K.Sketch.eqs.go(es, cs)), +hs: K.Sides(~F, env, K.Sketch.sides.cons(es, cs))) -> K.Sketch.means.cons(~F, env, es, cs):
  match cs:
    case Nil{}:
      Unit{}
    case Con{K.Rec{id, True{}, +k}, +t}:
      (wr, x) = w
      (wk, wt) = x
      cons_sound(~F, env, es, t, wt, hz, hs)
    case Con{K.Rec{id, False{}, +k}, +t}:
      (wr, x) = w
      (wk, wt) = x
      (means_sound(~F, env, es, k, wk, (zeros_l(~F, env, K.Constraint.eqs(es, k), K.Sketch.eqs.go(es, t), hz), sides_l(~F, env, K.Constraint.sides(es, k), K.Sketch.sides.cons(es, t), hs))),
       cons_sound(~F, env, es, t, wt, zeros_r(~F, env, K.Constraint.eqs(es, k), K.Sketch.eqs.go(es, t), hz), sides_r(~F, env, K.Constraint.sides(es, k), K.Sketch.sides.cons(es, t), hs)))

def cons_complete.k(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, K.Ent>, +k: K.Constraint, +t: List<&2, K.Rec>, hk: K.Constraint.holds(~F, env, es, k), rest: K.Both(K.Zeros(~F, env, K.Sketch.eqs.go(es, t)), K.Sides(~F, env, K.Sketch.sides.cons(es, t)))) -> K.Both(K.Zeros(~F, env, K.cat(K.Constraint.eqs(es, k), K.Sketch.eqs.go(es, t))), K.Sides(~F, env, K.cats(K.Constraint.sides(es, k), K.Sketch.sides.cons(es, t)))):
  (zk, sk) = hk
  (zt, st) = rest
  (zeros_cat(~F, env, K.Constraint.eqs(es, k), K.Sketch.eqs.go(es, t), zk, zt), sides_cat(~F, env, K.Constraint.sides(es, k), K.Sketch.sides.cons(es, t), sk, st))

def cons_complete(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, K.Ent>, cs: List<&2, K.Rec>, h: K.Sketch.means.cons(~F, env, es, cs)) -> K.Both(K.Zeros(~F, env, K.Sketch.eqs.go(es, cs)), K.Sides(~F, env, K.Sketch.sides.cons(es, cs))):
  match cs:
    case Nil{}:
      (Unit{}, Unit{})
    case Con{K.Rec{id, True{}, k}, t}:
      cons_complete(~F, env, es, t, h)
    case Con{K.Rec{id, False{}, +k}, +t}:
      (hk, ht) = h
      cons_complete.k(~F, env, es, k, t, means_complete(~F, env, es, k, hk), cons_complete(~F, env, es, t, ht))

# Whole sketches
# --------------

def sketch_sound.k(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, K.Ent>, +cs: List<&2, K.Rec>, wc: K.Sketch.wf.cons(es, cs), hz: K.Zeros(~F, env, K.Sketch.eqs.go(es, cs)), +hs: K.Sides(~F, env, K.cats(K.Sketch.sides.ents(es), K.Sketch.sides.cons(es, cs)))) -> K.Sketch.means.ents(~F, env, es) & K.Sketch.means.cons(~F, env, es, cs):
  (ents_sound(~F, env, es, sides_l(~F, env, K.Sketch.sides.ents(es), K.Sketch.sides.cons(es, cs), hs)),
   cons_sound(~F, env, es, cs, wc, hz, sides_r(~F, env, K.Sketch.sides.ents(es), K.Sketch.sides.cons(es, cs), hs)))

def sketch_sound(~F: O.OField, +env: List<&2, O.C(F)>, sk: K.Sketch, w: K.Sketch.wf(sk), h: K.Sketch.holds(~F, env, sk)) -> K.Sketch.means(~F, env, sk):
  match sk:
    case K.Sketch{vs, +es, +cs}:
      (we, wc) = w
      (hz, hs) = h
      sketch_sound.k(~F, env, es, cs, wc, hz, hs)

def sketch_complete.k(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, K.Ent>, +cs: List<&2, K.Rec>, se: K.Sides(~F, env, K.Sketch.sides.ents(es)), rest: K.Both(K.Zeros(~F, env, K.Sketch.eqs.go(es, cs)), K.Sides(~F, env, K.Sketch.sides.cons(es, cs)))) -> K.Zeros(~F, env, K.Sketch.eqs.go(es, cs)) & K.Sides(~F, env, K.cats(K.Sketch.sides.ents(es), K.Sketch.sides.cons(es, cs))):
  (z, s) = rest
  (z, sides_cat(~F, env, K.Sketch.sides.ents(es), K.Sketch.sides.cons(es, cs), se, s))

def sketch_complete(~F: O.OField, +env: List<&2, O.C(F)>, sk: K.Sketch, h: K.Sketch.means(~F, env, sk)) -> K.Sketch.holds(~F, env, sk):
  match sk:
    case K.Sketch{vs, +es, +cs}:
      (he, hc) = h
      sketch_complete.k(~F, env, es, cs, ents_complete(~F, env, es, he), cons_complete(~F, env, es, cs, hc))
