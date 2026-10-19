# bend-cad spec: the typed IR of a sketch, the exact equation form of every
# constraint kind, and what each kind means. Trusted (DESIGN §4, §5, D6):
# the forms are produced here, inside the checker, so an untrusted front end
# cannot change what a constraint means.
#
# A sketch's unknowns are variables, named by index into an environment
# (unused indices read as 0). Entities are the drawn geometry, with
# persistent IDs: a point names its two coordinate variables, a segment its
# two endpoint points, a circle its center point and radius variable.
# A merge (coincident, horizontal, vertical, concentric, equal radius) is
# an equation like any other constraint (D3 as revised 2026-10-19, as Fix
# was before it: sharing variables is the solver's optimization, not part
# of what a sketch means). Constraints reference existing
# entities by ID; the spec resolves each reference (wf_refs checks that it
# names an entity of the right kind). Each constraint has
#   eqs:   polynomials over the variables that must vanish (§5),
#   sides: polynomials that must be positive, or nonnegative (side
#          conditions, §8.6),
#   wf:    nothing beyond the references, for every kind so far,
#   means: its geometric meaning in any ordered field (spec/geom.bend).
# The meaning lemmas (ROADMAP.bend, DESIGN §5.5) say that, for a well-formed
# constraint, eqs = 0 and sides > 0 hold exactly when the meaning holds.
#
# Geometry may degenerate (a segment may collapse to a point, a distance
# may be 0); only dimensions (≥ 0) and the choices a user made (a side, a
# quadrant) are side conditions. Circles keep a positive radius and arcs a
# positive bulge.
#
# Scope: the core vocabulary of DESIGN §5.1. Tangency and joins (§5.2) and
# arcs (§5.3) get their forms in sk-10, curves (§5.4) in sk-15; arcs are
# declared below so the IR's shape is fixed now.

import Base
import ./num.bend as S
import ./ring.bend as E
import ./field.bend as O
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

# Entities
# --------
# Conic arcs, splines and offsets join in sk-15.

type Geo is Data:
  # x, y: coordinate variables
  GPoint{x: Nat, y: Nat}
  # p, q: endpoint point IDs; the segment is directed p → q
  GSeg{p: Nat, q: Nat}
  # c: center point ID; r: radius variable
  GCirc{c: Nat, r: Nat}
  # s, e: endpoint point IDs; b: bulge variable, tan(sweep / 4) > 0,
  # counterclockwise from s to e
  GArc{s: Nat, e: Nat, b: Nat}

type Ent is Data:
  Ent{id: Nat, construction: Bool, g: Geo}

# Constraints
# -----------
# Point, segment and circle arguments are entity IDs. Dimension values d,
# and the rotation (c, s) of an angle, are rational expressions over the
# variables: rational constants, named variables, or variables pinned to
# exact constants elsewhere (§7).

type Constraint is Data:
  # merges (D3): realized by shared variables, no equations
  Coincident{a: Nat, b: Nat}
  Horizontal{a: Nat, b: Nat}
  Vertical{a: Nat, b: Nat}
  Concentric{a: Nat, b: Nat}
  EqualRadius{a: Nat, b: Nat}
  # variable v is the constant k (fix, block, pins)
  Fix{v: Nat, k: S.Q}
  # dimensions (d ≥ 0); for HDistance, q is right of p, for VDistance above it
  Distance{p: Nat, q: Nat, d: E.QExpr}
  HDistance{p: Nat, q: Nat, d: E.QExpr}
  VDistance{p: Nat, q: Nat, d: E.QExpr}
  Radius{c: Nat, d: E.QExpr}
  Diameter{c: Nat, d: E.QExpr}
  # p is left of segment a's line or on it, the line taken in reverse when
  # rev; l is an aux length variable, the segment's length
  LineDistance{p: Nat, a: Nat, rev: Bool, d: E.QExpr, l: Nat}
  # from segment a (reversed when ra) to segment b (reversed when rb)
  Angle{a: Nat, ra: Bool, b: Nat, rb: Bool, c: E.QExpr, s: E.QExpr}
  # relations
  EqualLength{a: Nat, b: Nat}
  Perpendicular{a: Nat, b: Nat}
  Parallel{a: Nat, b: Nat}
  # p is on the line through segment a (anywhere on it)
  OnLine{p: Nat, a: Nat}
  OnCircle{p: Nat, c: Nat}
  # m is the midpoint of segment a
  Midpoint{m: Nat, a: Nat}
  # q is the mirror image of p in segment a's line
  Symmetric{p: Nat, q: Nat, a: Nat}

# a constraint as stored: persistent id; driven (reference) dimensions are
# measured, not imposed, and contribute no equations
type Rec is Data:
  Rec{id: Nat, driven: Bool, k: Constraint}

type Sketch is Data:
  Sketch{vars: List<&2, VKind>, ents: List<&2, Ent>, cons: List<&2, Rec>}

# Resolving references
# --------------------
# Resolved geometry names variables directly. A reference that does not
# name an entity of the right kind resolves to geometry at variable 0;
# wf_refs rules that out.

type Pt is Data:
  Pt{x: Nat, y: Nat}

type Seg is Data:
  Seg{p: Pt, q: Pt}

type Circ is Data:
  Circ{c: Pt, r: Nat}

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

def find.pick(b: Bool, g: Geo, rest: Maybe<&2, Geo>) -> Maybe<&2, Geo>:
  match b:
    case True{}:
      Some{g}
    case False{}:
      rest

# the entity with this id (the first, should ids repeat)
def find(+id: Nat, es: List<&2, Ent>) -> Maybe<&2, Geo>:
  match es:
    case Nil{}:
      None{}
    case Con{Ent{eid, cst, g}, t}:
      find.pick(Nat.is_eq(eid, id), g, find(id, t))

def pt.of(m: Maybe<&2, Geo>) -> Pt:
  match m:
    case Some{GPoint{x, y}}:
      Pt{x, y}
    case _:
      Pt{0n, 0n}

def pt(+es: List<&2, Ent>, id: Nat) -> Pt:
  pt.of(find(id, es))

def seg.of(+es: List<&2, Ent>, m: Maybe<&2, Geo>) -> Seg:
  match m:
    case Some{GSeg{p, q}}:
      Seg{pt(es, p), pt(es, q)}
    case _:
      Seg{Pt{0n, 0n}, Pt{0n, 0n}}

def seg(+es: List<&2, Ent>, id: Nat) -> Seg:
  seg.of(es, find(id, es))

# s, reversed when rev
def Seg.rev_if(+s: Seg, rev: Bool) -> Seg:
  match rev:
    case False{}:
      s
    case True{}:
      Seg{Seg.q(s), Seg.p(s)}

# segment id, reversed when rev
def dseg(+es: List<&2, Ent>, id: Nat, rev: Bool) -> Seg:
  Seg.rev_if(seg(es, id), rev)

def circ.of(+es: List<&2, Ent>, m: Maybe<&2, Geo>) -> Circ:
  match m:
    case Some{GCirc{c, r}}:
      Circ{pt(es, c), r}
    case _:
      Circ{Pt{0n, 0n}, 0n}

def circ(+es: List<&2, Ent>, id: Nat) -> Circ:
  circ.of(es, find(id, es))

def is_pt(m: Maybe<&2, Geo>) -> Bool:
  match m:
    case Some{GPoint{x, y}}:
      True{}
    case _:
      False{}

def is_seg(m: Maybe<&2, Geo>) -> Bool:
  match m:
    case Some{GSeg{p, q}}:
      True{}
    case _:
      False{}

def is_circ(m: Maybe<&2, Geo>) -> Bool:
  match m:
    case Some{GCirc{c, r}}:
      True{}
    case _:
      False{}

# id names a point (segment, circle) entity
def IsPt(+es: List<&2, Ent>, +id: Nat) -> Type:
  {is_pt(find(id, es)) == True{} : Bool}

def IsSeg(+es: List<&2, Ent>, +id: Nat) -> Type:
  {is_seg(find(id, es)) == True{} : Bool}

def IsCirc(+es: List<&2, Ent>, +id: Nat) -> Type:
  {is_circ(find(id, es)) == True{} : Bool}

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

# a side condition: e > 0, or e ≥ 0
type Side is Data:
  Gt0{e: E.QExpr}
  Ge0{e: E.QExpr}

# Exact equation forms (§5.1)
# ---------------------------

def Constraint.eqs(+es: List<&2, Ent>, +k: Constraint) -> List<&2, E.QExpr>:
  match k:
    case Coincident{a, b}:
      [E.QSub{var(Pt.x(pt(es, a))), var(Pt.x(pt(es, b)))}, E.QSub{var(Pt.y(pt(es, a))), var(Pt.y(pt(es, b)))}]
    case Horizontal{a, b}:
      [E.QSub{var(Pt.y(pt(es, a))), var(Pt.y(pt(es, b)))}]
    case Vertical{a, b}:
      [E.QSub{var(Pt.x(pt(es, a))), var(Pt.x(pt(es, b)))}]
    case Concentric{a, b}:
      [E.QSub{var(Pt.x(Circ.c(circ(es, a)))), var(Pt.x(Circ.c(circ(es, b))))}, E.QSub{var(Pt.y(Circ.c(circ(es, a)))), var(Pt.y(Circ.c(circ(es, b))))}]
    case EqualRadius{a, b}:
      [E.QSub{var(Circ.r(circ(es, a))), var(Circ.r(circ(es, b)))}]
    case Fix{v, c}:
      [E.QSub{var(v), E.QCst{c}}]
    case Distance{p, q, d}:
      [E.QSub{VE.norm2(VE.sub(Pt.ve(pt(es, q)), Pt.ve(pt(es, p)))), E.QMul{d, d}}]
    case HDistance{p, q, d}:
      [E.QSub{E.QSub{var(Pt.x(pt(es, q))), var(Pt.x(pt(es, p)))}, d}]
    case VDistance{p, q, d}:
      [E.QSub{E.QSub{var(Pt.y(pt(es, q))), var(Pt.y(pt(es, p)))}, d}]
    case Radius{c, d}:
      [E.QSub{var(Circ.r(circ(es, c))), d}]
    case Diameter{c, d}:
      [E.QSub{E.QAdd{var(Circ.r(circ(es, c))), var(Circ.r(circ(es, c)))}, d}]
    case LineDistance{p, a, rev, d, l}:
      [E.QSub{VE.cross(Seg.dir(dseg(es, a, rev)), VE.sub(Pt.ve(pt(es, p)), Pt.ve(Seg.p(dseg(es, a, rev))))), E.QMul{d, var(l)}},
       E.QSub{E.QMul{var(l), var(l)}, VE.norm2(Seg.dir(seg(es, a)))}]
    case Angle{a, ra, b, rb, c, s}:
      [VE.cross(VE.rot(c, s, Seg.dir(dseg(es, a, ra))), Seg.dir(dseg(es, b, rb)))]
    case EqualLength{a, b}:
      [E.QSub{VE.norm2(Seg.dir(seg(es, a))), VE.norm2(Seg.dir(seg(es, b)))}]
    case Perpendicular{a, b}:
      [VE.dot(Seg.dir(seg(es, a)), Seg.dir(seg(es, b)))]
    case Parallel{a, b}:
      [VE.cross(Seg.dir(seg(es, a)), Seg.dir(seg(es, b)))]
    case OnLine{p, a}:
      [VE.cross(Seg.dir(seg(es, a)), VE.sub(Pt.ve(pt(es, p)), Pt.ve(Seg.p(seg(es, a)))))]
    case OnCircle{p, c}:
      [E.QSub{VE.norm2(VE.sub(Pt.ve(pt(es, p)), Pt.ve(Circ.c(circ(es, c))))), E.QMul{var(Circ.r(circ(es, c))), var(Circ.r(circ(es, c)))}}]
    case Midpoint{m, a}:
      [E.QSub{E.QAdd{var(Pt.x(pt(es, m))), var(Pt.x(pt(es, m)))}, E.QAdd{var(Pt.x(Seg.p(seg(es, a)))), var(Pt.x(Seg.q(seg(es, a))))}},
       E.QSub{E.QAdd{var(Pt.y(pt(es, m))), var(Pt.y(pt(es, m)))}, E.QAdd{var(Pt.y(Seg.p(seg(es, a)))), var(Pt.y(Seg.q(seg(es, a))))}}]
    case Symmetric{p, q, a}:
      sym.eqs(Pt.ve(pt(es, p)), Pt.ve(pt(es, q)), Pt.ve(Seg.p(seg(es, a))), Pt.ve(Seg.q(seg(es, a))))

# Side conditions. Only dimensions and choices are here: geometry may
# degenerate. (An angle's dot > 0 also makes both directions and (c, s)
# nonzero. A radius needs none: its circle keeps r > 0.)
def Constraint.sides(+es: List<&2, Ent>, +k: Constraint) -> List<&2, Side>:
  match k:
    case Distance{p, q, d}:
      [Ge0{d}]
    case HDistance{p, q, d}:
      [Ge0{d}]
    case VDistance{p, q, d}:
      [Ge0{d}]
    case LineDistance{p, a, rev, d, l}:
      [Gt0{var(l)}, Ge0{d}]
    case Angle{a, ra, b, rb, c, s}:
      [Gt0{VE.dot(VE.rot(c, s, Seg.dir(dseg(es, a, ra))), Seg.dir(dseg(es, b, rb)))}]
    case _:
      []

# No kind asks more than its references (merges were realized by shared
# variables until D3 was revised, 2026-10-19; they are equations now)
def Constraint.wf(+es: List<&2, Ent>, +k: Constraint) -> Type:
  Unit

# every reference names an entity of the right kind
def Constraint.wf_refs(+es: List<&2, Ent>, +k: Constraint) -> Type:
  match k:
    case Coincident{a, b}:
      IsPt(es, a) & IsPt(es, b)
    case Horizontal{a, b}:
      IsPt(es, a) & IsPt(es, b)
    case Vertical{a, b}:
      IsPt(es, a) & IsPt(es, b)
    case Concentric{a, b}:
      IsCirc(es, a) & IsCirc(es, b)
    case EqualRadius{a, b}:
      IsCirc(es, a) & IsCirc(es, b)
    case Fix{v, c}:
      Unit
    case Distance{p, q, d}:
      IsPt(es, p) & IsPt(es, q)
    case HDistance{p, q, d}:
      IsPt(es, p) & IsPt(es, q)
    case VDistance{p, q, d}:
      IsPt(es, p) & IsPt(es, q)
    case Radius{c, d}:
      IsCirc(es, c)
    case Diameter{c, d}:
      IsCirc(es, c)
    case LineDistance{p, a, rev, d, l}:
      IsPt(es, p) & IsSeg(es, a)
    case Angle{a, ra, b, rb, c, s}:
      IsSeg(es, a) & IsSeg(es, b)
    case EqualLength{a, b}:
      IsSeg(es, a) & IsSeg(es, b)
    case Perpendicular{a, b}:
      IsSeg(es, a) & IsSeg(es, b)
    case Parallel{a, b}:
      IsSeg(es, a) & IsSeg(es, b)
    case OnLine{p, a}:
      IsPt(es, p) & IsSeg(es, a)
    case OnCircle{p, c}:
      IsPt(es, p) & IsCirc(es, c)
    case Midpoint{m, a}:
      IsPt(es, m) & IsSeg(es, a)
    case Symmetric{p, q, a}:
      IsPt(es, p) & (IsPt(es, q) & IsSeg(es, a))

# Meanings
# --------

# a resolved point's value under env
def at(~F: O.OField, +env: List<&2, O.C(F)>, p: Pt) -> G.Vec(~F):
  match p:
    case Pt{x, y}:
      G.V2{O.lookup(~F, env, x), O.lookup(~F, env, y)}

# a resolved segment's direction q - p under env
def dirv(~F: O.OField, +env: List<&2, O.C(F)>, +a: Seg) -> G.Vec(~F):
  G.sub(~F, at(~F, env, Seg.q(a)), at(~F, env, Seg.p(a)))

def Constraint.means(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, Ent>, +k: Constraint) -> Type:
  match k:
    case Coincident{a, b}:
      {at(~F, env, pt(es, a)) == at(~F, env, pt(es, b)) : G.Vec(~F)}
    case Horizontal{a, b}:
      {G.y(~F, at(~F, env, pt(es, a))) == G.y(~F, at(~F, env, pt(es, b))) : O.C(F)}
    case Vertical{a, b}:
      {G.x(~F, at(~F, env, pt(es, a))) == G.x(~F, at(~F, env, pt(es, b))) : O.C(F)}
    case Concentric{a, b}:
      {at(~F, env, Circ.c(circ(es, a))) == at(~F, env, Circ.c(circ(es, b))) : G.Vec(~F)}
    case EqualRadius{a, b}:
      {O.lookup(~F, env, Circ.r(circ(es, a))) == O.lookup(~F, env, Circ.r(circ(es, b))) : O.C(F)}
    case Fix{v, c}:
      {O.lookup(~F, env, v) == O.ofq(~F, c) : O.C(F)}
    case Distance{p, q, d}:
      G.dist(~F, at(~F, env, pt(es, p)), at(~F, env, pt(es, q)), O.eval(~F, env, d))
    case HDistance{p, q, d}:
      G.hdist(~F, at(~F, env, pt(es, p)), at(~F, env, pt(es, q)), O.eval(~F, env, d))
    case VDistance{p, q, d}:
      G.vdist(~F, at(~F, env, pt(es, p)), at(~F, env, pt(es, q)), O.eval(~F, env, d))
    case Radius{c, d}:
      {O.lookup(~F, env, Circ.r(circ(es, c))) == O.eval(~F, env, d) : O.C(F)}
    case Diameter{c, d}:
      {O.add(F, O.lookup(~F, env, Circ.r(circ(es, c))), O.lookup(~F, env, Circ.r(circ(es, c)))) == O.eval(~F, env, d) : O.C(F)}
    case LineDistance{p, a, rev, d, l}:
      O.lt(F, O.zero(F), O.lookup(~F, env, l)) & G.dist(~F, at(~F, env, Seg.p(seg(es, a))), at(~F, env, Seg.q(seg(es, a))), O.lookup(~F, env, l)) & G.line_dist(~F, at(~F, env, pt(es, p)), at(~F, env, Seg.p(dseg(es, a, rev))), at(~F, env, Seg.q(dseg(es, a, rev))), O.eval(~F, env, d))
    case Angle{a, ra, b, rb, c, s}:
      G.angle(~F, dirv(~F, env, dseg(es, a, ra)), dirv(~F, env, dseg(es, b, rb)), O.eval(~F, env, c), O.eval(~F, env, s))
    case EqualLength{a, b}:
      G.equal_length(~F, at(~F, env, Seg.p(seg(es, a))), at(~F, env, Seg.q(seg(es, a))), at(~F, env, Seg.p(seg(es, b))), at(~F, env, Seg.q(seg(es, b))))
    case Perpendicular{a, b}:
      G.perpendicular(~F, dirv(~F, env, seg(es, a)), dirv(~F, env, seg(es, b)))
    case Parallel{a, b}:
      G.parallel(~F, dirv(~F, env, seg(es, a)), dirv(~F, env, seg(es, b)))
    case OnLine{p, a}:
      G.on_line(~F, at(~F, env, pt(es, p)), at(~F, env, Seg.p(seg(es, a))), at(~F, env, Seg.q(seg(es, a))))
    case OnCircle{p, c}:
      G.on_circle(~F, at(~F, env, pt(es, p)), at(~F, env, Circ.c(circ(es, c))), O.lookup(~F, env, Circ.r(circ(es, c))))
    case Midpoint{m, a}:
      {at(~F, env, pt(es, m)) == G.mid(~F, at(~F, env, Seg.p(seg(es, a))), at(~F, env, Seg.q(seg(es, a)))) : G.Vec(~F)}
    case Symmetric{p, q, a}:
      G.mirror(~F, at(~F, env, pt(es, p)), at(~F, env, pt(es, q)), at(~F, env, Seg.p(seg(es, a))), at(~F, env, Seg.q(seg(es, a))))

# Entities
# --------
# Points and segments carry no conditions; circles keep a positive radius,
# arcs a positive bulge.

def Ent.sides(e: Ent) -> List<&2, Side>:
  match e:
    case Ent{id, cst, GCirc{c, r}}:
      [Gt0{var(r)}]
    case Ent{id, cst, GArc{s, f, b}}:
      [Gt0{var(b)}]
    case _:
      []

def Ent.means(~F: O.OField, +env: List<&2, O.C(F)>, e: Ent) -> Type:
  match e:
    case Ent{id, cst, GCirc{c, r}}:
      O.lt(F, O.zero(F), O.lookup(~F, env, r))
    case Ent{id, cst, GArc{s, f, b}}:
      O.lt(F, O.zero(F), O.lookup(~F, env, b))
    case _:
      Unit

# a segment's ends, a circle's center and an arc's ends are point entities
def Ent.wf_refs(+es: List<&2, Ent>, e: Ent) -> Type:
  match e:
    case Ent{id, cst, GSeg{p, q}}:
      IsPt(es, p) & IsPt(es, q)
    case Ent{id, cst, GCirc{c, r}}:
      IsPt(es, c)
    case Ent{id, cst, GArc{s, f, b}}:
      IsPt(es, s) & IsPt(es, f)
    case _:
      Unit

# Holding
# -------

# A and B (a pair of reusable facts)
def Both(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

# every expression in xs is 0 in F
def Zeros(~F: O.OField, +env: List<&2, O.C(F)>, xs: List<&2, E.QExpr>) -> Data:
  match xs:
    case Nil{}:
      Unit
    case Con{h, t}:
      Both({O.eval(~F, env, h) == O.zero(F) : O.C(F)}, Zeros(~F, env, t))

# every side condition in xs holds in F
def Sides(~F: O.OField, +env: List<&2, O.C(F)>, xs: List<&2, Side>) -> Data:
  match xs:
    case Nil{}:
      Unit
    case Con{Gt0{e}, t}:
      Both(O.lt(F, O.zero(F), O.eval(~F, env, e)), Sides(~F, env, t))
    case Con{Ge0{e}, t}:
      Both(O.le(~F, O.zero(F), O.eval(~F, env, e)), Sides(~F, env, t))

def Constraint.holds(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, Ent>, +k: Constraint) -> Type:
  Zeros(~F, env, Constraint.eqs(es, k)) & Sides(~F, env, Constraint.sides(es, k))

def Ent.holds(~F: O.OField, +env: List<&2, O.C(F)>, e: Ent) -> Type:
  Sides(~F, env, Ent.sides(e))

# The sketch's exact system
# -------------------------
# Sketch.eqs is F in DESIGN §8 and Sketch.sides its side conditions; the
# certificates evaluate them over the rationals (E.qeval).

def cat(xs: List<&2, E.QExpr>, ys: List<&2, E.QExpr>) -> List<&2, E.QExpr>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, cat(t, ys)}

def cats(xs: List<&2, Side>, ys: List<&2, Side>) -> List<&2, Side>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, cats(t, ys)}

# the equations of every driving constraint
def Sketch.eqs.go(+es: List<&2, Ent>, cs: List<&2, Rec>) -> List<&2, E.QExpr>:
  match cs:
    case Nil{}:
      []
    case Con{Rec{id, True{}, k}, t}:
      Sketch.eqs.go(es, t)
    case Con{Rec{id, False{}, k}, t}:
      cat(Constraint.eqs(es, k), Sketch.eqs.go(es, t))

def Sketch.sides.ents(es: List<&2, Ent>) -> List<&2, Side>:
  match es:
    case Nil{}:
      []
    case Con{e, t}:
      cats(Ent.sides(e), Sketch.sides.ents(t))

def Sketch.sides.cons(+es: List<&2, Ent>, cs: List<&2, Rec>) -> List<&2, Side>:
  match cs:
    case Nil{}:
      []
    case Con{Rec{id, True{}, k}, t}:
      Sketch.sides.cons(es, t)
    case Con{Rec{id, False{}, k}, t}:
      cats(Constraint.sides(es, k), Sketch.sides.cons(es, t))

def Sketch.eqs(sk: Sketch) -> List<&2, E.QExpr>:
  match sk:
    case Sketch{vs, es, cs}:
      Sketch.eqs.go(es, cs)

# the side conditions: every entity's, then every driving constraint's
def Sketch.sides(sk: Sketch) -> List<&2, Side>:
  match sk:
    case Sketch{vs, +es, cs}:
      cats(Sketch.sides.ents(es), Sketch.sides.cons(es, cs))

def Sketch.wf.ents(+es: List<&2, Ent>, xs: List<&2, Ent>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{e, t}:
      Ent.wf_refs(es, e) & Sketch.wf.ents(es, t)

def Sketch.wf.cons(+es: List<&2, Ent>, cs: List<&2, Rec>) -> Type:
  match cs:
    case Nil{}:
      Unit
    case Con{Rec{id, dr, +k}, t}:
      Constraint.wf_refs(es, k) & (Constraint.wf(es, k) & Sketch.wf.cons(es, t))

# every reference resolves and every merge is realized
def Sketch.wf(sk: Sketch) -> Type:
  match sk:
    case Sketch{vs, +es, cs}:
      Sketch.wf.ents(es, es) & Sketch.wf.cons(es, cs)

def Sketch.holds(~F: O.OField, +env: List<&2, O.C(F)>, +sk: Sketch) -> Type:
  Zeros(~F, env, Sketch.eqs(sk)) & Sides(~F, env, Sketch.sides(sk))

def Sketch.means.ents(~F: O.OField, +env: List<&2, O.C(F)>, es: List<&2, Ent>) -> Type:
  match es:
    case Nil{}:
      Unit
    case Con{e, t}:
      Ent.means(~F, env, e) & Sketch.means.ents(~F, env, t)

def Sketch.means.cons(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, Ent>, cs: List<&2, Rec>) -> Type:
  match cs:
    case Nil{}:
      Unit
    case Con{Rec{id, True{}, k}, t}:
      Sketch.means.cons(~F, env, es, t)
    case Con{Rec{id, False{}, k}, t}:
      Constraint.means(~F, env, es, k) & Sketch.means.cons(~F, env, es, t)

# every circle and arc is proper and every driving constraint means what it
# says
def Sketch.means(~F: O.OField, +env: List<&2, O.C(F)>, sk: Sketch) -> Type:
  match sk:
    case Sketch{vs, +es, cs}:
      Sketch.means.ents(~F, env, es) & Sketch.means.cons(~F, env, es, cs)
