# bend-cad spec: the typed IR of a sketch, the exact equation form of every
# constraint kind, and what each kind means. Trusted (DESIGN §4, §5, D6):
# the forms are produced here, inside the checker, so an untrusted front end
# cannot change what a constraint means.
#
# A sketch's unknowns are variables, named by index into an environment of
# rationals (unused indices read as 0). Geometry refers to variables
# directly: a point is the pair of its coordinate variables, so merged
# points (D3) are points with the same indices. Each constraint has
#   eqs:   polynomials that must vanish (the exact equation form, §5),
#   sides: polynomials that must be positive (side conditions, §8.6),
#   wf:    for merge kinds, the index sharing that realizes it,
#   means: its geometric meaning (spec/geom.bend).
# The meaning lemmas (ROADMAP.bend, DESIGN §5.5) say that, for a well-formed
# constraint, eqs = 0 and sides > 0 hold exactly when the meaning holds.
#
# Scope: the core vocabulary of DESIGN §5.1. Tangency and joins (§5.2) and
# arcs (§5.3) get their forms in sk-10, curves (§5.4) in sk-15; their
# entities are declared below so the IR's shape is fixed now.

import Base
import ./num.bend as S
import ./ring.bend as E
import ./geom.bend as G

# Variables
# ---------
# The kind fixes a variable's display scale (§3) and its ink weight (§10);
# it does not change any meaning.

type VKind is Data:
  Coord{}
  Length{}
  Param{}
  Aux{}

# Geometry
# --------

# a point: the indices of its coordinate variables
type Pt is Data:
  Pt{x: Nat, y: Nat}

# a segment from p to q, also naming the line through them, directed p → q
type Seg is Data:
  Seg{p: Pt, q: Pt}

# a full circle: its center and the index of its radius variable
type Circ is Data:
  Circ{c: Pt, r: Nat}

# a bulge arc counterclockwise from s to e; b (an index) = tan(sweep / 4) > 0
type Arc is Data:
  Arc{s: Pt, e: Pt, b: Nat}

def Pt.x(p: Pt) -> Nat:
  match p:
    case Pt{x, y}:
      x

def Pt.y(p: Pt) -> Nat:
  match p:
    case Pt{x, y}:
      y

def Seg.p(s: Seg) -> Pt:
  match s:
    case Seg{p, q}:
      p

def Seg.q(s: Seg) -> Pt:
  match s:
    case Seg{p, q}:
      q

def Circ.c(c: Circ) -> Pt:
  match c:
    case Circ{c, r}:
      c

def Circ.r(c: Circ) -> Nat:
  match c:
    case Circ{c, r}:
      r

def Arc.s(a: Arc) -> Pt:
  match a:
    case Arc{s, e, b}:
      s

def Arc.e(a: Arc) -> Pt:
  match a:
    case Arc{s, e, b}:
      e

def Arc.b(a: Arc) -> Nat:
  match a:
    case Arc{s, e, b}:
      b

# Entities: what is drawn. Conic arcs, splines and offsets join in sk-15.
type Geo is Data:
  GPoint{p: Pt}
  GSeg{s: Seg}
  GCirc{c: Circ}
  GArc{a: Arc}

type Ent is Data:
  Ent{id: Nat, construction: Bool, g: Geo}

# Constraints
# -----------
# Dimension values d, and the rotation (c, s) of an angle, are rational
# expressions over the variables: rational constants, named variables, or
# variables pinned to exact constants elsewhere (§7). A segment argument is
# directed; the front end orients it to pick a side or an angle's quadrant.

type Constraint is Data:
  # merges (D3): realized by shared variable indices, no equations
  Coincident{a: Pt, b: Pt}
  Horizontal{a: Pt, b: Pt}
  Vertical{a: Pt, b: Pt}
  Concentric{a: Circ, b: Circ}
  EqualRadius{a: Circ, b: Circ}
  # variable v is the constant k (fix, block, pins)
  Fix{v: Nat, k: S.Q}
  # dimensions
  Distance{p: Pt, q: Pt, d: E.QExpr}
  HDistance{p: Pt, q: Pt, d: E.QExpr}
  VDistance{p: Pt, q: Pt, d: E.QExpr}
  Radius{c: Circ, d: E.QExpr}
  Diameter{c: Circ, d: E.QExpr}
  # l is the index of an aux length variable, the length of the line
  LineDistance{p: Pt, a: Seg, d: E.QExpr, l: Nat}
  Angle{a: Seg, b: Seg, c: E.QExpr, s: E.QExpr}
  # relations
  EqualLength{a: Seg, b: Seg}
  Perpendicular{a: Seg, b: Seg}
  Parallel{a: Seg, b: Seg}
  OnLine{p: Pt, a: Seg}
  OnSegment{p: Pt, a: Seg}
  OnCircle{p: Pt, c: Circ}
  Midpoint{m: Pt, p: Pt, q: Pt}
  Symmetric{p: Pt, q: Pt, a: Seg}

# a constraint as stored: persistent id; driven (reference) dimensions are
# measured, not imposed, and contribute no equations
type Rec is Data:
  Rec{id: Nat, driven: Bool, k: Constraint}

type Sketch is Data:
  Sketch{vars: List<&2, VKind>, ents: List<&2, Ent>, cons: List<&2, Rec>}

# Expressions
# -----------

def var(i: Nat) -> E.QExpr:
  E.QVar{i}

# a vector of two expressions
type VE is Data:
  VE{x: E.QExpr, y: E.QExpr}

def VE.x(v: VE) -> E.QExpr:
  match v:
    case VE{x, y}:
      x

def VE.y(v: VE) -> E.QExpr:
  match v:
    case VE{x, y}:
      y

def Pt.ve(p: Pt) -> VE:
  match p:
    case Pt{x, y}:
      VE{var(x), var(y)}

def VE.add(+a: VE, +b: VE) -> VE:
  VE{E.QAdd{VE.x(a), VE.x(b)}, E.QAdd{VE.y(a), VE.y(b)}}

def VE.sub(+a: VE, +b: VE) -> VE:
  VE{E.QSub{VE.x(a), VE.x(b)}, E.QSub{VE.y(a), VE.y(b)}}

def VE.dot(+a: VE, +b: VE) -> E.QExpr:
  E.QAdd{E.QMul{VE.x(a), VE.x(b)}, E.QMul{VE.y(a), VE.y(b)}}

def VE.cross(+a: VE, +b: VE) -> E.QExpr:
  E.QSub{E.QMul{VE.x(a), VE.y(b)}, E.QMul{VE.y(a), VE.x(b)}}

def VE.norm2(+a: VE) -> E.QExpr:
  VE.dot(a, a)

def VE.rot(+c: E.QExpr, +s: E.QExpr, +a: VE) -> VE:
  VE{E.QSub{E.QMul{c, VE.x(a)}, E.QMul{s, VE.y(a)}}, E.QAdd{E.QMul{s, VE.x(a)}, E.QMul{c, VE.y(a)}}}

# q - p for a segment from p to q
def Seg.dir(+a: Seg) -> VE:
  VE.sub(Pt.ve(Seg.q(a)), Pt.ve(Seg.p(a)))

# |w|² (q - a) - R̂ (p - a), the mirror equations (§5.1), w = b - a
def sym.eqs(+p: VE, +q: VE, +a: VE, +b: VE) -> List<&2, E.QExpr>:
  +w = VE.sub(b, a)
  +u = VE.sub(p, a)
  +v = VE.sub(q, a)
  +xx = {E.QMul{VE.x(w), VE.x(w)} : E.QExpr}
  +yy = {E.QMul{VE.y(w), VE.y(w)} : E.QExpr}
  +xy = {E.QMul{VE.x(w), VE.y(w)} : E.QExpr}
  +n = {E.QAdd{xx, yy} : E.QExpr}
  [E.QSub{E.QMul{n, VE.x(v)}, E.QAdd{E.QMul{E.QSub{xx, yy}, VE.x(u)}, E.QMul{E.QAdd{xy, xy}, VE.y(u)}}},
   E.QSub{E.QMul{n, VE.y(v)}, E.QAdd{E.QMul{E.QAdd{xy, xy}, VE.x(u)}, E.QMul{E.QSub{yy, xx}, VE.y(u)}}}]

# Exact equation forms (§5.1)
# ---------------------------

def Constraint.eqs(+k: Constraint) -> List<&2, E.QExpr>:
  match k:
    case Coincident{a, b}:
      []
    case Horizontal{a, b}:
      []
    case Vertical{a, b}:
      []
    case Concentric{a, b}:
      []
    case EqualRadius{a, b}:
      []
    case Fix{v, c}:
      [E.QSub{var(v), E.QCst{c}}]
    case Distance{p, q, d}:
      [E.QSub{VE.norm2(VE.sub(Pt.ve(q), Pt.ve(p))), E.QMul{d, d}}]
    case HDistance{p, q, d}:
      [E.QSub{E.QSub{var(Pt.x(q)), var(Pt.x(p))}, d}]
    case VDistance{p, q, d}:
      [E.QSub{E.QSub{var(Pt.y(q)), var(Pt.y(p))}, d}]
    case Radius{c, d}:
      [E.QSub{var(Circ.r(c)), d}]
    case Diameter{c, d}:
      [E.QSub{E.QAdd{var(Circ.r(c)), var(Circ.r(c))}, d}]
    case LineDistance{p, a, d, l}:
      [E.QSub{VE.cross(Seg.dir(a), VE.sub(Pt.ve(p), Pt.ve(Seg.p(a)))), E.QMul{d, var(l)}},
       E.QSub{E.QMul{var(l), var(l)}, VE.norm2(Seg.dir(a))}]
    case Angle{a, b, c, s}:
      [VE.cross(VE.rot(c, s, Seg.dir(a)), Seg.dir(b))]
    case EqualLength{a, b}:
      [E.QSub{VE.norm2(Seg.dir(a)), VE.norm2(Seg.dir(b))}]
    case Perpendicular{a, b}:
      [VE.dot(Seg.dir(a), Seg.dir(b))]
    case Parallel{a, b}:
      [VE.cross(Seg.dir(a), Seg.dir(b))]
    case OnLine{p, a}:
      [VE.cross(Seg.dir(a), VE.sub(Pt.ve(p), Pt.ve(Seg.p(a))))]
    case OnSegment{p, a}:
      [VE.cross(Seg.dir(a), VE.sub(Pt.ve(p), Pt.ve(Seg.p(a))))]
    case OnCircle{p, c}:
      [E.QSub{VE.norm2(VE.sub(Pt.ve(p), Pt.ve(Circ.c(c)))), E.QMul{var(Circ.r(c)), var(Circ.r(c))}}]
    case Midpoint{m, p, q}:
      [E.QSub{E.QAdd{var(Pt.x(m)), var(Pt.x(m))}, E.QAdd{var(Pt.x(p)), var(Pt.x(q))}},
       E.QSub{E.QAdd{var(Pt.y(m)), var(Pt.y(m))}, E.QAdd{var(Pt.y(p)), var(Pt.y(q))}}]
    case Symmetric{p, q, a}:
      sym.eqs(Pt.ve(p), Pt.ve(q), Pt.ve(Seg.p(a)), Pt.ve(Seg.q(a)))

# Side conditions: each must be positive. Nondegeneracy that another side
# condition already implies is not repeated (an angle's dot > 0 implies both
# directions are nonzero; a point strictly inside a segment implies the
# segment is proper).
def Constraint.sides(+k: Constraint) -> List<&2, E.QExpr>:
  match k:
    case Coincident{a, b}:
      []
    case Horizontal{a, b}:
      []
    case Vertical{a, b}:
      []
    case Concentric{a, b}:
      []
    case EqualRadius{a, b}:
      []
    case Fix{v, c}:
      []
    case Distance{p, q, d}:
      [d]
    case HDistance{p, q, d}:
      [d]
    case VDistance{p, q, d}:
      [d]
    case Radius{c, d}:
      [d]
    case Diameter{c, d}:
      [d]
    case LineDistance{p, a, d, l}:
      [var(l), d]
    case Angle{a, b, c, s}:
      [VE.dot(VE.rot(c, s, Seg.dir(a)), Seg.dir(b))]
    case EqualLength{a, b}:
      [VE.norm2(Seg.dir(a)), VE.norm2(Seg.dir(b))]
    case Perpendicular{a, b}:
      [VE.norm2(Seg.dir(a)), VE.norm2(Seg.dir(b))]
    case Parallel{a, b}:
      [VE.norm2(Seg.dir(a)), VE.norm2(Seg.dir(b))]
    case OnLine{p, a}:
      [VE.norm2(Seg.dir(a))]
    case OnSegment{p, a}:
      [VE.dot(VE.sub(Pt.ve(p), Pt.ve(Seg.p(a))), Seg.dir(a)),
       E.QSub{VE.norm2(Seg.dir(a)), VE.dot(VE.sub(Pt.ve(p), Pt.ve(Seg.p(a))), Seg.dir(a))}]
    case OnCircle{p, c}:
      [var(Circ.r(c))]
    case Midpoint{m, p, q}:
      []
    case Symmetric{p, q, a}:
      [VE.norm2(Seg.dir(a))]

# Merge kinds are realized by shared variable indices (D3)
def Constraint.wf(+k: Constraint) -> Type:
  match k:
    case Coincident{a, b}:
      {a == b : Pt}
    case Horizontal{a, b}:
      {Pt.y(a) == Pt.y(b) : Nat}
    case Vertical{a, b}:
      {Pt.x(a) == Pt.x(b) : Nat}
    case Concentric{a, b}:
      {Circ.c(a) == Circ.c(b) : Pt}
    case EqualRadius{a, b}:
      {Circ.r(a) == Circ.r(b) : Nat}
    case _:
      Unit

# Meanings
# --------

def Pt.at(+env: List<&2, S.Q>, p: Pt) -> G.V2:
  match p:
    case Pt{x, y}:
      G.V2{E.qlookup(env, x), E.qlookup(env, y)}

def Constraint.means(+env: List<&2, S.Q>, +k: Constraint) -> Type:
  match k:
    case Coincident{a, b}:
      G.V2.eq(Pt.at(env, a), Pt.at(env, b))
    case Horizontal{a, b}:
      S.Q.eq(E.qlookup(env, Pt.y(a)), E.qlookup(env, Pt.y(b)))
    case Vertical{a, b}:
      S.Q.eq(E.qlookup(env, Pt.x(a)), E.qlookup(env, Pt.x(b)))
    case Concentric{a, b}:
      G.V2.eq(Pt.at(env, Circ.c(a)), Pt.at(env, Circ.c(b)))
    case EqualRadius{a, b}:
      S.Q.eq(E.qlookup(env, Circ.r(a)), E.qlookup(env, Circ.r(b)))
    case Fix{v, c}:
      S.Q.eq(E.qlookup(env, v), c)
    case Distance{p, q, d}:
      G.dist(Pt.at(env, p), Pt.at(env, q), E.qeval(env, d))
    case HDistance{p, q, d}:
      G.hdist(Pt.at(env, p), Pt.at(env, q), E.qeval(env, d))
    case VDistance{p, q, d}:
      G.vdist(Pt.at(env, p), Pt.at(env, q), E.qeval(env, d))
    case Radius{c, d}:
      S.Q.lt(G.Q.zero(), E.qeval(env, d)) & S.Q.eq(E.qlookup(env, Circ.r(c)), E.qeval(env, d))
    case Diameter{c, d}:
      S.Q.lt(G.Q.zero(), E.qeval(env, d)) & S.Q.eq(S.Q.add(E.qlookup(env, Circ.r(c)), E.qlookup(env, Circ.r(c))), E.qeval(env, d))
    case LineDistance{p, a, d, l}:
      G.dist(Pt.at(env, Seg.p(a)), Pt.at(env, Seg.q(a)), E.qlookup(env, l)) & G.line_dist(Pt.at(env, p), Pt.at(env, Seg.p(a)), Pt.at(env, Seg.q(a)), E.qeval(env, d))
    case Angle{a, b, c, s}:
      G.angle(G.V2.sub(Pt.at(env, Seg.q(a)), Pt.at(env, Seg.p(a))), G.V2.sub(Pt.at(env, Seg.q(b)), Pt.at(env, Seg.p(b))), E.qeval(env, c), E.qeval(env, s))
    case EqualLength{a, b}:
      G.equal_length(Pt.at(env, Seg.p(a)), Pt.at(env, Seg.q(a)), Pt.at(env, Seg.p(b)), Pt.at(env, Seg.q(b)))
    case Perpendicular{a, b}:
      G.perpendicular(G.V2.sub(Pt.at(env, Seg.q(a)), Pt.at(env, Seg.p(a))), G.V2.sub(Pt.at(env, Seg.q(b)), Pt.at(env, Seg.p(b))))
    case Parallel{a, b}:
      G.parallel(G.V2.sub(Pt.at(env, Seg.q(a)), Pt.at(env, Seg.p(a))), G.V2.sub(Pt.at(env, Seg.q(b)), Pt.at(env, Seg.p(b))))
    case OnLine{p, a}:
      G.on_line(Pt.at(env, p), Pt.at(env, Seg.p(a)), Pt.at(env, Seg.q(a)))
    case OnSegment{p, a}:
      G.on_segment(Pt.at(env, p), Pt.at(env, Seg.p(a)), Pt.at(env, Seg.q(a)))
    case OnCircle{p, c}:
      G.dist(Pt.at(env, Circ.c(c)), Pt.at(env, p), E.qlookup(env, Circ.r(c)))
    case Midpoint{m, p, q}:
      G.V2.eq(Pt.at(env, m), G.V2.mid(Pt.at(env, p), Pt.at(env, q)))
    case Symmetric{p, q, a}:
      G.mirror(Pt.at(env, p), Pt.at(env, q), Pt.at(env, Seg.p(a)), Pt.at(env, Seg.q(a)))

# Entities: their side conditions keep every drawn curve proper
def Ent.sides(+e: Ent) -> List<&2, E.QExpr>:
  match e:
    case Ent{id, cst, GPoint{p}}:
      []
    case Ent{id, cst, GSeg{s}}:
      [VE.norm2(Seg.dir(s))]
    case Ent{id, cst, GCirc{c}}:
      [var(Circ.r(c))]
    case Ent{id, cst, GArc{a}}:
      [var(Arc.b(a)), VE.norm2(VE.sub(Pt.ve(Arc.e(a)), Pt.ve(Arc.s(a))))]

def Ent.means(+env: List<&2, S.Q>, +e: Ent) -> Type:
  match e:
    case Ent{id, cst, GPoint{p}}:
      Unit
    case Ent{id, cst, GSeg{s}}:
      G.V2.ne(Pt.at(env, Seg.p(s)), Pt.at(env, Seg.q(s)))
    case Ent{id, cst, GCirc{c}}:
      S.Q.lt(G.Q.zero(), E.qlookup(env, Circ.r(c)))
    case Ent{id, cst, GArc{a}}:
      S.Q.lt(G.Q.zero(), E.qlookup(env, Arc.b(a))) & G.V2.ne(Pt.at(env, Arc.s(a)), Pt.at(env, Arc.e(a)))

# Holding
# -------

# every expression in es is 0
def Zeros(+env: List<&2, S.Q>, es: List<&2, E.QExpr>) -> Type:
  match es:
    case Nil{}:
      Unit
    case Con{h, t}:
      S.Q.eq(E.qeval(env, h), G.Q.zero()) & Zeros(env, t)

# every expression in es is positive
def Poss(+env: List<&2, S.Q>, es: List<&2, E.QExpr>) -> Type:
  match es:
    case Nil{}:
      Unit
    case Con{h, t}:
      S.Q.lt(G.Q.zero(), E.qeval(env, h)) & Poss(env, t)

def Constraint.holds(+env: List<&2, S.Q>, +k: Constraint) -> Type:
  Zeros(env, Constraint.eqs(k)) & Poss(env, Constraint.sides(k))

def Ent.holds(+env: List<&2, S.Q>, +e: Ent) -> Type:
  Poss(env, Ent.sides(e))

# The sketch's exact system
# -------------------------

def cat(xs: List<&2, E.QExpr>, ys: List<&2, E.QExpr>) -> List<&2, E.QExpr>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, cat(t, ys)}

# F: the equations of every driving constraint
def Sketch.eqs.go(cs: List<&2, Rec>) -> List<&2, E.QExpr>:
  match cs:
    case Nil{}:
      []
    case Con{Rec{id, True{}, k}, t}:
      Sketch.eqs.go(t)
    case Con{Rec{id, False{}, k}, t}:
      cat(Constraint.eqs(k), Sketch.eqs.go(t))

def Sketch.sides.ents(es: List<&2, Ent>) -> List<&2, E.QExpr>:
  match es:
    case Nil{}:
      []
    case Con{e, t}:
      cat(Ent.sides(e), Sketch.sides.ents(t))

def Sketch.sides.cons(cs: List<&2, Rec>) -> List<&2, E.QExpr>:
  match cs:
    case Nil{}:
      []
    case Con{Rec{id, True{}, k}, t}:
      Sketch.sides.cons(t)
    case Con{Rec{id, False{}, k}, t}:
      cat(Constraint.sides(k), Sketch.sides.cons(t))

def Sketch.eqs(sk: Sketch) -> List<&2, E.QExpr>:
  match sk:
    case Sketch{vs, es, cs}:
      Sketch.eqs.go(cs)

# the side conditions: every entity's, then every driving constraint's
def Sketch.sides(sk: Sketch) -> List<&2, E.QExpr>:
  match sk:
    case Sketch{vs, es, +cs}:
      cat(Sketch.sides.ents(es), Sketch.sides.cons(cs))

def Sketch.wf.go(cs: List<&2, Rec>) -> Type:
  match cs:
    case Nil{}:
      Unit
    case Con{Rec{id, dr, k}, t}:
      Constraint.wf(k) & Sketch.wf.go(t)

def Sketch.wf(sk: Sketch) -> Type:
  match sk:
    case Sketch{vs, es, cs}:
      Sketch.wf.go(cs)

def Sketch.holds(+env: List<&2, S.Q>, +sk: Sketch) -> Type:
  Zeros(env, Sketch.eqs(sk)) & Poss(env, Sketch.sides(sk))

def Sketch.means.ents(+env: List<&2, S.Q>, es: List<&2, Ent>) -> Type:
  match es:
    case Nil{}:
      Unit
    case Con{e, t}:
      Ent.means(env, e) & Sketch.means.ents(env, t)

def Sketch.means.cons(+env: List<&2, S.Q>, cs: List<&2, Rec>) -> Type:
  match cs:
    case Nil{}:
      Unit
    case Con{Rec{id, True{}, k}, t}:
      Sketch.means.cons(env, t)
    case Con{Rec{id, False{}, k}, t}:
      Constraint.means(env, k) & Sketch.means.cons(env, t)

# every drawn curve is proper and every driving constraint means what it says
def Sketch.means(+env: List<&2, S.Q>, sk: Sketch) -> Type:
  match sk:
    case Sketch{vs, es, cs}:
      Sketch.means.ents(env, es) & Sketch.means.cons(env, cs)
