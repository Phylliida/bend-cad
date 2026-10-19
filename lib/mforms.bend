# Generated from spec/sketch.bend by mforms.py: each constraint kind's
# holds (H), meaning (M) and merge condition (W), with its references
# already resolved (points, segments and circles as values).

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/geom.bend as G
import ../spec/sketch.bend as K

def H.Coincident(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Pt, +b: K.Pt) -> Type:
  K.Zeros(~F, env, [E.QSub{K.var(K.Pt.x(a)), K.var(K.Pt.x(b))}, E.QSub{K.var(K.Pt.y(a)), K.var(K.Pt.y(b))}]) & K.Sides(~F, env, [])

def M.Coincident(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Pt, +b: K.Pt) -> Type:
  {K.at(~F, env, a) == K.at(~F, env, b) : G.Vec(~F)}

def W.Coincident(+a: K.Pt, +b: K.Pt) -> Type:
  Unit

def H.Horizontal(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Pt, +b: K.Pt) -> Type:
  K.Zeros(~F, env, [E.QSub{K.var(K.Pt.y(a)), K.var(K.Pt.y(b))}]) & K.Sides(~F, env, [])

def M.Horizontal(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Pt, +b: K.Pt) -> Type:
  {G.y(~F, K.at(~F, env, a)) == G.y(~F, K.at(~F, env, b)) : O.C(F)}

def W.Horizontal(+a: K.Pt, +b: K.Pt) -> Type:
  Unit

def H.Vertical(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Pt, +b: K.Pt) -> Type:
  K.Zeros(~F, env, [E.QSub{K.var(K.Pt.x(a)), K.var(K.Pt.x(b))}]) & K.Sides(~F, env, [])

def M.Vertical(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Pt, +b: K.Pt) -> Type:
  {G.x(~F, K.at(~F, env, a)) == G.x(~F, K.at(~F, env, b)) : O.C(F)}

def W.Vertical(+a: K.Pt, +b: K.Pt) -> Type:
  Unit

def H.Concentric(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Circ, +b: K.Circ) -> Type:
  K.Zeros(~F, env, [E.QSub{K.var(K.Pt.x(K.Circ.c(a))), K.var(K.Pt.x(K.Circ.c(b)))}, E.QSub{K.var(K.Pt.y(K.Circ.c(a))), K.var(K.Pt.y(K.Circ.c(b)))}]) & K.Sides(~F, env, [])

def M.Concentric(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Circ, +b: K.Circ) -> Type:
  {K.at(~F, env, K.Circ.c(a)) == K.at(~F, env, K.Circ.c(b)) : G.Vec(~F)}

def W.Concentric(+a: K.Circ, +b: K.Circ) -> Type:
  Unit

def H.EqualRadius(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Circ, +b: K.Circ) -> Type:
  K.Zeros(~F, env, [E.QSub{K.var(K.Circ.r(a)), K.var(K.Circ.r(b))}]) & K.Sides(~F, env, [])

def M.EqualRadius(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Circ, +b: K.Circ) -> Type:
  {O.lookup(~F, env, K.Circ.r(a)) == O.lookup(~F, env, K.Circ.r(b)) : O.C(F)}

def W.EqualRadius(+a: K.Circ, +b: K.Circ) -> Type:
  Unit

def H.Fix(~F: O.OField, +env: List<&2, O.C(F)>, +v: Nat, +c: S.Q) -> Type:
  K.Zeros(~F, env, [E.QSub{K.var(v), E.QCst{c}}]) & K.Sides(~F, env, [])

def M.Fix(~F: O.OField, +env: List<&2, O.C(F)>, +v: Nat, +c: S.Q) -> Type:
  {O.lookup(~F, env, v) == O.ofq(~F, c) : O.C(F)}

def W.Fix(+v: Nat, +c: S.Q) -> Type:
  Unit

def H.Distance(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +q: K.Pt, +d: E.QExpr) -> Type:
  K.Zeros(~F, env, [E.QSub{K.VE.norm2(K.VE.sub(K.Pt.ve(q), K.Pt.ve(p))), E.QMul{d, d}}]) & K.Sides(~F, env, [K.Ge0{d}])

def M.Distance(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +q: K.Pt, +d: E.QExpr) -> Type:
  G.dist(~F, K.at(~F, env, p), K.at(~F, env, q), O.eval(~F, env, d))

def W.Distance(+p: K.Pt, +q: K.Pt, +d: E.QExpr) -> Type:
  Unit

def H.HDistance(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +q: K.Pt, +d: E.QExpr) -> Type:
  K.Zeros(~F, env, [E.QSub{E.QSub{K.var(K.Pt.x(q)), K.var(K.Pt.x(p))}, d}]) & K.Sides(~F, env, [K.Ge0{d}])

def M.HDistance(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +q: K.Pt, +d: E.QExpr) -> Type:
  G.hdist(~F, K.at(~F, env, p), K.at(~F, env, q), O.eval(~F, env, d))

def W.HDistance(+p: K.Pt, +q: K.Pt, +d: E.QExpr) -> Type:
  Unit

def H.VDistance(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +q: K.Pt, +d: E.QExpr) -> Type:
  K.Zeros(~F, env, [E.QSub{E.QSub{K.var(K.Pt.y(q)), K.var(K.Pt.y(p))}, d}]) & K.Sides(~F, env, [K.Ge0{d}])

def M.VDistance(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +q: K.Pt, +d: E.QExpr) -> Type:
  G.vdist(~F, K.at(~F, env, p), K.at(~F, env, q), O.eval(~F, env, d))

def W.VDistance(+p: K.Pt, +q: K.Pt, +d: E.QExpr) -> Type:
  Unit

def H.Radius(~F: O.OField, +env: List<&2, O.C(F)>, +c: K.Circ, +d: E.QExpr) -> Type:
  K.Zeros(~F, env, [E.QSub{K.var(K.Circ.r(c)), d}]) & K.Sides(~F, env, [])

def M.Radius(~F: O.OField, +env: List<&2, O.C(F)>, +c: K.Circ, +d: E.QExpr) -> Type:
  {O.lookup(~F, env, K.Circ.r(c)) == O.eval(~F, env, d) : O.C(F)}

def W.Radius(+c: K.Circ, +d: E.QExpr) -> Type:
  Unit

def H.Diameter(~F: O.OField, +env: List<&2, O.C(F)>, +c: K.Circ, +d: E.QExpr) -> Type:
  K.Zeros(~F, env, [E.QSub{E.QAdd{K.var(K.Circ.r(c)), K.var(K.Circ.r(c))}, d}]) & K.Sides(~F, env, [])

def M.Diameter(~F: O.OField, +env: List<&2, O.C(F)>, +c: K.Circ, +d: E.QExpr) -> Type:
  {O.add(F, O.lookup(~F, env, K.Circ.r(c)), O.lookup(~F, env, K.Circ.r(c))) == O.eval(~F, env, d) : O.C(F)}

def W.Diameter(+c: K.Circ, +d: E.QExpr) -> Type:
  Unit

def H.LineDistance(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +a: K.Seg, +rev: Bool, +d: E.QExpr, +l: Nat) -> Type:
  K.Zeros(~F, env, [E.QSub{K.VE.cross(K.Seg.dir(K.Seg.rev_if(a, rev)), K.VE.sub(K.Pt.ve(p), K.Pt.ve(K.Seg.p(K.Seg.rev_if(a, rev))))), E.QMul{d, K.var(l)}},
    E.QSub{E.QMul{K.var(l), K.var(l)}, K.VE.norm2(K.Seg.dir(a))}]) & K.Sides(~F, env, [K.Gt0{K.var(l)}, K.Ge0{d}])

def M.LineDistance(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +a: K.Seg, +rev: Bool, +d: E.QExpr, +l: Nat) -> Type:
  O.lt(F, O.zero(F), O.lookup(~F, env, l)) & G.dist(~F, K.at(~F, env, K.Seg.p(a)), K.at(~F, env, K.Seg.q(a)), O.lookup(~F, env, l)) & G.line_dist(~F, K.at(~F, env, p), K.at(~F, env, K.Seg.p(K.Seg.rev_if(a, rev))), K.at(~F, env, K.Seg.q(K.Seg.rev_if(a, rev))), O.eval(~F, env, d))

def W.LineDistance(+p: K.Pt, +a: K.Seg, +rev: Bool, +d: E.QExpr, +l: Nat) -> Type:
  Unit

def H.Angle(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Seg, +ra: Bool, +b: K.Seg, +rb: Bool, +c: E.QExpr, +s: E.QExpr) -> Type:
  K.Zeros(~F, env, [K.VE.cross(K.VE.rot(c, s, K.Seg.dir(K.Seg.rev_if(a, ra))), K.Seg.dir(K.Seg.rev_if(b, rb)))]) & K.Sides(~F, env, [K.Gt0{K.VE.dot(K.VE.rot(c, s, K.Seg.dir(K.Seg.rev_if(a, ra))), K.Seg.dir(K.Seg.rev_if(b, rb)))}])

def M.Angle(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Seg, +ra: Bool, +b: K.Seg, +rb: Bool, +c: E.QExpr, +s: E.QExpr) -> Type:
  G.angle(~F, K.dirv(~F, env, K.Seg.rev_if(a, ra)), K.dirv(~F, env, K.Seg.rev_if(b, rb)), O.eval(~F, env, c), O.eval(~F, env, s))

def W.Angle(+a: K.Seg, +ra: Bool, +b: K.Seg, +rb: Bool, +c: E.QExpr, +s: E.QExpr) -> Type:
  Unit

def H.EqualLength(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Seg, +b: K.Seg) -> Type:
  K.Zeros(~F, env, [E.QSub{K.VE.norm2(K.Seg.dir(a)), K.VE.norm2(K.Seg.dir(b))}]) & K.Sides(~F, env, [])

def M.EqualLength(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Seg, +b: K.Seg) -> Type:
  G.equal_length(~F, K.at(~F, env, K.Seg.p(a)), K.at(~F, env, K.Seg.q(a)), K.at(~F, env, K.Seg.p(b)), K.at(~F, env, K.Seg.q(b)))

def W.EqualLength(+a: K.Seg, +b: K.Seg) -> Type:
  Unit

def H.Perpendicular(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Seg, +b: K.Seg) -> Type:
  K.Zeros(~F, env, [K.VE.dot(K.Seg.dir(a), K.Seg.dir(b))]) & K.Sides(~F, env, [])

def M.Perpendicular(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Seg, +b: K.Seg) -> Type:
  G.perpendicular(~F, K.dirv(~F, env, a), K.dirv(~F, env, b))

def W.Perpendicular(+a: K.Seg, +b: K.Seg) -> Type:
  Unit

def H.Parallel(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Seg, +b: K.Seg) -> Type:
  K.Zeros(~F, env, [K.VE.cross(K.Seg.dir(a), K.Seg.dir(b))]) & K.Sides(~F, env, [])

def M.Parallel(~F: O.OField, +env: List<&2, O.C(F)>, +a: K.Seg, +b: K.Seg) -> Type:
  G.parallel(~F, K.dirv(~F, env, a), K.dirv(~F, env, b))

def W.Parallel(+a: K.Seg, +b: K.Seg) -> Type:
  Unit

def H.OnLine(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +a: K.Seg) -> Type:
  K.Zeros(~F, env, [K.VE.cross(K.Seg.dir(a), K.VE.sub(K.Pt.ve(p), K.Pt.ve(K.Seg.p(a))))]) & K.Sides(~F, env, [])

def M.OnLine(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +a: K.Seg) -> Type:
  G.on_line(~F, K.at(~F, env, p), K.at(~F, env, K.Seg.p(a)), K.at(~F, env, K.Seg.q(a)))

def W.OnLine(+p: K.Pt, +a: K.Seg) -> Type:
  Unit

def H.OnCircle(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +c: K.Circ) -> Type:
  K.Zeros(~F, env, [E.QSub{K.VE.norm2(K.VE.sub(K.Pt.ve(p), K.Pt.ve(K.Circ.c(c)))), E.QMul{K.var(K.Circ.r(c)), K.var(K.Circ.r(c))}}]) & K.Sides(~F, env, [])

def M.OnCircle(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +c: K.Circ) -> Type:
  G.on_circle(~F, K.at(~F, env, p), K.at(~F, env, K.Circ.c(c)), O.lookup(~F, env, K.Circ.r(c)))

def W.OnCircle(+p: K.Pt, +c: K.Circ) -> Type:
  Unit

def H.Midpoint(~F: O.OField, +env: List<&2, O.C(F)>, +m: K.Pt, +a: K.Seg) -> Type:
  K.Zeros(~F, env, [E.QSub{E.QAdd{K.var(K.Pt.x(m)), K.var(K.Pt.x(m))}, E.QAdd{K.var(K.Pt.x(K.Seg.p(a))), K.var(K.Pt.x(K.Seg.q(a)))}},
    E.QSub{E.QAdd{K.var(K.Pt.y(m)), K.var(K.Pt.y(m))}, E.QAdd{K.var(K.Pt.y(K.Seg.p(a))), K.var(K.Pt.y(K.Seg.q(a)))}}]) & K.Sides(~F, env, [])

def M.Midpoint(~F: O.OField, +env: List<&2, O.C(F)>, +m: K.Pt, +a: K.Seg) -> Type:
  {K.at(~F, env, m) == G.mid(~F, K.at(~F, env, K.Seg.p(a)), K.at(~F, env, K.Seg.q(a))) : G.Vec(~F)}

def W.Midpoint(+m: K.Pt, +a: K.Seg) -> Type:
  Unit

def H.Symmetric(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +q: K.Pt, +a: K.Seg) -> Type:
  K.Zeros(~F, env, K.sym.eqs(K.Pt.ve(p), K.Pt.ve(q), K.Pt.ve(K.Seg.p(a)), K.Pt.ve(K.Seg.q(a)))) & K.Sides(~F, env, [])

def M.Symmetric(~F: O.OField, +env: List<&2, O.C(F)>, +p: K.Pt, +q: K.Pt, +a: K.Seg) -> Type:
  G.mirror(~F, K.at(~F, env, p), K.at(~F, env, q), K.at(~F, env, K.Seg.p(a)), K.at(~F, env, K.Seg.q(a)))

def W.Symmetric(+p: K.Pt, +q: K.Pt, +a: K.Seg) -> Type:
  Unit
