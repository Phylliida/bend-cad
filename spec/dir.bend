# bend-cad spec: the direction layer's calculus (sk-13b, PLAN-sk13b.md v2).
# Trusted. What the solver may claim about directions, and with which
# nondegeneracy, as derivations it must exhibit; spec/solve.bend's Honest
# reads them.
#
# A segment s from p to q has the direction z_s = (x_q - x_p, y_q - y_p),
# read as the complex number (x_q - x_p) + i (y_q - y_p). The frame node
# has direction (1, 0). For pairs of expressions u, v (complex forms),
# cross(u, v) = Im(conj(u) v) (SK.VE.cross) and dot(u, v) = Re(conj(u) v).
#
# Two judgments, about the equations of some constraints (facts):
# - K(e): the polynomial e vanishes;
# - par(a, x): the form x is parallel to node a's direction, i.e.
#   cross(z_a, x) vanishes.
# Each holds wherever the facts hold and the segments of its nd have
# nonzero length (Q15: a collapsed segment satisfies every direction
# relation, so the nondegeneracy is stated, never assumed). The rules
# (PLAN-sk13b.md, "The calculus") are the constructors of Der; each is a
# polynomial identity with polynomial multipliers, proven once
# (PLAN-sk13b B1). A derivation is data; Valid says it follows the rules,
# and concl and nd read off what it proves and what it needs.
#
# The context (the span of the equations of the constraint judged and its
# premises) decides which segments are collapsed. A collapsed segment is
# never passed through, and complex line is never applied at one: what
# that would give fails at every solution, and would turn later
# constraints red for nothing.

import Base
import ./num.bend as S
import ./ring.bend as E
import ./field.bend as O
import ./geom.bend as G
import ./sketch.bend as SK

# Numbers and lists
# -----------------

def qz() -> S.Q:
  S.Q{S.Z0{}, S.XH{}}

def qo() -> S.Q:
  S.Q{S.Zpos{S.XH{}}, S.XH{}}

def cst(q: S.Q) -> E.QExpr:
  E.QCst{q}

def znz(z: S.Z) -> Bool:
  match z:
    case S.Z0{}:
      False{}
    case S.Zpos{p}:
      True{}
    case S.Zneg{p}:
      True{}

# q is not 0
def qnz(q: S.Q) -> Bool:
  znz(S.Q.num(q))

def ncat(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, ncat(t, ys)}

# e1 and e2 are the same polynomial (as spec/solve.bend's Ident)
def Same(+e1: E.QExpr, +e2: E.QExpr) -> Type:
  @x: List<&2, S.Q> -> S.Q.eq(E.qeval(x, e1), E.qeval(x, e2))

# both parts agree
def SameV(+u: SK.VE, +v: SK.VE) -> Type:
  Same(SK.VE.x(u), SK.VE.x(v)) & Same(SK.VE.y(u), SK.VE.y(v))

# l_1 e_1 + ... + l_n e_n (as spec/solve.bend's lin)
def dlin(ls: List<&2, S.Q>, es: List<&2, E.QExpr>) -> E.QExpr:
  match ls es:
    case Con{l, lt} Con{e, et}:
      E.QAdd{E.QMul{E.QCst{l}, e}, dlin(lt, et)}
    case Nil{} es:
      E.QCst{qz()}
    case Con{l, lt} Nil{}:
      E.QCst{qz()}

# e is a constant combination of es
def InSpan(+e: E.QExpr, +es: List<&2, E.QExpr>) -> Type:
  &ls: List<&2, S.Q> -> Same(e, dlin(ls, es))

# Complex forms
# -------------

# a constant label c + i s
type Lab is Data:
  Lab{c: S.Q, s: S.Q}

def Lab.conj(g: Lab) -> Lab:
  match g:
    case Lab{c, s}:
      Lab{c, S.Q.neg(s)}

# g x
def gmul(g: Lab, +x: SK.VE) -> SK.VE:
  match g:
    case Lab{c, s}:
      SK.VE.rot(cst(c), cst(s), x)

# i x
def imul(+x: SK.VE) -> SK.VE:
  SK.VE{E.QNeg{SK.VE.y(x)}, SK.VE.x(x)}

# m1 x1 + m2 x2
def vlin(+m1: S.Q, +x1: SK.VE, +m2: S.Q, +x2: SK.VE) -> SK.VE:
  SK.VE{E.QAdd{E.QMul{cst(m1), SK.VE.x(x1)}, E.QMul{cst(m2), SK.VE.x(x2)}}, E.QAdd{E.QMul{cst(m1), SK.VE.y(x1)}, E.QMul{cst(m2), SK.VE.y(x2)}}}

# Nodes
# -----

type Node is Data:
  # the x axis, direction (1, 0)
  NFrame{}
  # the segment entity s
  NSeg{s: Nat}

# segment s's direction
def zseg(+es: List<&2, SK.Ent>, s: Nat) -> SK.VE:
  SK.Seg.dir(SK.seg(es, s))

# a node's direction
def zdir(+es: List<&2, SK.Ent>, n: Node) -> SK.VE:
  match n:
    case NFrame{}:
      SK.VE{cst(qo()), cst(qz())}
    case NSeg{s}:
      zseg(es, s)

# the segments among a node (none for the frame)
def Node.segs(n: Node) -> List<&2, Nat>:
  match n:
    case NFrame{}:
      Nil{}
    case NSeg{s}:
      [s]

# Direction statements
# --------------------
# A constraint whose one equation is l cross(z_a, x), by its kind:
# Parallel (x = z_b), Perpendicular (x = i z_b, since dot(u, v) =
# cross(u, i v)), an Angle whose rotation (c, s) is constant (x =
# conj(c + i s) times b's direction as the Angle takes it, l = -1 when it
# takes a reversed), and OnLine (x = p - the start of a). Every other
# constraint is none.

type DStat is Data:
  DStat{a: Nat, x: SK.VE, l: S.Q}

def sgn(rev: Bool) -> S.Q:
  match rev:
    case False{}:
      qo()
    case True{}:
      S.Q.neg(qo())

def dstat.angle(+es: List<&2, SK.Ent>, +a: Nat, +ra: Bool, +b: Nat, +rb: Bool, c: E.QExpr, s: E.QExpr) -> Maybe<&2, DStat>:
  match c s:
    case E.QCst{+qc} E.QCst{+qs}:
      Some{DStat{a, gmul(Lab{qc, S.Q.neg(qs)}, SK.Seg.dir(SK.dseg(es, b, rb))), sgn(ra)}}
    case c s:
      None{}

def dstat(+es: List<&2, SK.Ent>, k: SK.Constraint) -> Maybe<&2, DStat>:
  match k:
    case SK.Parallel{a, b}:
      Some{DStat{a, zseg(es, b), qo()}}
    case SK.Perpendicular{a, b}:
      Some{DStat{a, imul(zseg(es, b)), qo()}}
    case SK.Angle{a, ra, b, rb, c, s}:
      dstat.angle(es, a, ra, b, rb, c, s)
    case SK.OnLine{p, +a}:
      Some{DStat{a, SK.VE.sub(SK.Pt.ve(SK.pt(es, p)), SK.Pt.ve(SK.Seg.p(SK.seg(es, a)))), qo()}}
    case _:
      None{}

# Facts
# -----
# An equation the derivations may use, with the segments its own truth
# needs nonzero (none for an equation the solver solves; a dropped one's
# drop nd) and its direction statement, if its constraint makes one.

type Fact is Data:
  Fact{e: E.QExpr, nd: List<&2, Nat>, ds: Maybe<&2, DStat>}

def fact_at(fs: List<&2, Fact>, i: Nat) -> Maybe<&2, Fact>:
  match fs i:
    case Nil{} i:
      None{}
    case Con{f, t} 0n:
      Some{f}
    case Con{f, t} 1n+j:
      fact_at(t, j)

# Collapse
# --------

# segment s is collapsed in the context ctx: both parts of its direction
# are constant combinations of ctx
def Collapsed(+es: List<&2, SK.Ent>, +ctx: List<&2, E.QExpr>, +s: Nat) -> Type:
  InSpan(SK.VE.x(zseg(es, s)), ctx) & InSpan(SK.VE.y(zseg(es, s)), ctx)

# a node that may be passed through: the frame, or a segment not collapsed
def Open(+es: List<&2, SK.Ent>, +ctx: List<&2, E.QExpr>, n: Node) -> Type:
  match n:
    case NFrame{}:
      Unit
    case NSeg{s}:
      Collapsed(es, ctx, s) -> Empty

# Judgments and derivations
# -------------------------

type Jd is Data:
  # e vanishes
  JK{e: E.QExpr}
  # x is parallel to a's direction
  JP{a: Node, x: SK.VE}

type Der is Data:
  # K(e) for the fact e at position i
  DPrem{i: Nat}
  # K(l1 e1 + l2 e2) from K(e1), K(e2)
  DKLin{l1: S.Q, d1: Der, l2: S.Q, d2: Der}
  # frame-back: K(Im x) from par(frame, x)
  DBack{d: Der}
  # complex line: K(Re x) (re) or K(Im x) from par(a, x) and par(a, i x),
  # a open
  DLine{d1: Der, d2: Der, re: Bool}
  # par(a, x) from the direction statement of the fact at position i
  DPPrem{i: Nat}
  # par(a, z_a)
  DSelf{a: Node}
  # par(a, m1 x1 + m2 x2) from par(a, x1), par(a, x2)
  DPLin{m1: S.Q, d1: Der, m2: S.Q, d2: Der}
  # par(a, x + l) from par(a, x), K(Re l), K(Im l)
  DKnown{d: Der, dr: Der, di: Der}
  # turn: par(b, g z_a) from par(a, conj(g) z_b)
  DTurn{d: Der, g: Lab, b: Nat}
  # through: par(a, conj(g) x) from par(a, conj(g) z_b) and par(b, x),
  # b open
  DThrough{d1: Der, d2: Der, g: Lab, b: Nat}
  # frame: par(frame, x) from K(Im x)
  DFrame{d: Der, x: SK.VE}
  # void: par(a, x), any x, from K(Re z_a), K(Im z_a)
  DVoid{dr: Der, di: Der, a: Node, x: SK.VE}

def zeroe() -> E.QExpr:
  E.QCst{qz()}

def zerov() -> SK.VE:
  SK.VE{zeroe(), zeroe()}

# what a K judgment says (0 for a parallel one)
def Jd.e(j: Jd) -> E.QExpr:
  match j:
    case JK{e}:
      e
    case JP{+a, +x}:
      zeroe()

def Jd.a(j: Jd) -> Node:
  match j:
    case JK{e}:
      NFrame{}
    case JP{+a, +x}:
      a

def Jd.x(j: Jd) -> SK.VE:
  match j:
    case JK{e}:
      zerov()
    case JP{+a, +x}:
      x

def fact.e(m: Maybe<&2, Fact>) -> E.QExpr:
  match m:
    case Some{Fact{e, nd, ds}}:
      e
    case None{}:
      zeroe()

def fact.nd(m: Maybe<&2, Fact>) -> List<&2, Nat>:
  match m:
    case Some{Fact{e, nd, ds}}:
      nd
    case None{}:
      Nil{}

def fact.pj(m: Maybe<&2, Fact>) -> Jd:
  match m:
    case Some{Fact{e, nd, Some{DStat{a, x, l}}}}:
      JP{NSeg{a}, x}
    case _:
      JK{zeroe()}

def dline.e(re: Bool, +x: SK.VE) -> E.QExpr:
  match re:
    case True{}:
      SK.VE.x(x)
    case False{}:
      SK.VE.y(x)

# what a derivation proves
def concl(+es: List<&2, SK.Ent>, +fs: List<&2, Fact>, d: Der) -> Jd:
  match d:
    case DPrem{+i}:
      JK{fact.e(fact_at(fs, i))}
    case DKLin{+l1, +d1, +l2, +d2}:
      JK{E.QAdd{E.QMul{cst(l1), Jd.e(concl(es, fs, d1))}, E.QMul{cst(l2), Jd.e(concl(es, fs, d2))}}}
    case DBack{+d}:
      JK{SK.VE.y(Jd.x(concl(es, fs, d)))}
    case DLine{+d1, +d2, +re}:
      JK{dline.e(re, Jd.x(concl(es, fs, d1)))}
    case DPPrem{+i}:
      fact.pj(fact_at(fs, i))
    case DSelf{+a}:
      JP{a, zdir(es, a)}
    case DPLin{+m1, +d1, +m2, +d2}:
      JP{Jd.a(concl(es, fs, d1)), vlin(m1, Jd.x(concl(es, fs, d1)), m2, Jd.x(concl(es, fs, d2)))}
    case DKnown{+d, +dr, +di}:
      JP{Jd.a(concl(es, fs, d)), SK.VE.add(Jd.x(concl(es, fs, d)), SK.VE{Jd.e(concl(es, fs, dr)), Jd.e(concl(es, fs, di))})}
    case DTurn{+d, +g, +b}:
      JP{NSeg{b}, gmul(g, zdir(es, Jd.a(concl(es, fs, d))))}
    case DThrough{+d1, +d2, +g, +b}:
      JP{Jd.a(concl(es, fs, d1)), gmul(Lab.conj(g), Jd.x(concl(es, fs, d2)))}
    case DFrame{+d, +x}:
      JP{NFrame{}, x}
    case DVoid{+dr, +di, +a, +x}:
      JP{a, x}

# the segments a derivation needs nonzero: its facts' own, every b passed
# through, every segment a complex line is applied at
def nd(+es: List<&2, SK.Ent>, +fs: List<&2, Fact>, d: Der) -> List<&2, Nat>:
  match d:
    case DPrem{+i}:
      fact.nd(fact_at(fs, i))
    case DKLin{+l1, +d1, +l2, +d2}:
      ncat(nd(es, fs, d1), nd(es, fs, d2))
    case DBack{+d}:
      nd(es, fs, d)
    case DLine{+d1, +d2, +re}:
      ncat(Node.segs(Jd.a(concl(es, fs, d1))), ncat(nd(es, fs, d1), nd(es, fs, d2)))
    case DPPrem{+i}:
      fact.nd(fact_at(fs, i))
    case DSelf{+a}:
      Nil{}
    case DPLin{+m1, +d1, +m2, +d2}:
      ncat(nd(es, fs, d1), nd(es, fs, d2))
    case DKnown{+d, +dr, +di}:
      ncat(nd(es, fs, d), ncat(nd(es, fs, dr), nd(es, fs, di)))
    case DTurn{+d, +g, +b}:
      nd(es, fs, d)
    case DThrough{+d1, +d2, +g, +b}:
      Con{b, ncat(nd(es, fs, d1), nd(es, fs, d2))}
    case DFrame{+d, +x}:
      nd(es, fs, d)
    case DVoid{+dr, +di, +a, +x}:
      ncat(nd(es, fs, dr), nd(es, fs, di))

# a K conclusion; a parallel one
def IsK(j: Jd) -> Type:
  match j:
    case JK{e}:
      Unit
    case JP{+a, +x}:
      Empty

def IsP(j: Jd) -> Type:
  match j:
    case JK{e}:
      Empty
    case JP{+a, +x}:
      Unit

# the fact at i exists (and, for DPPrem, makes a direction statement with
# a nonzero factor)
def HasFact(m: Maybe<&2, Fact>) -> Type:
  match m:
    case Some{f}:
      Unit
    case None{}:
      Empty

def HasStat(m: Maybe<&2, Fact>) -> Type:
  match m:
    case Some{Fact{e, nd, Some{DStat{a, x, l}}}}:
      {qnz(l) == True{} : Bool}
    case _:
      Empty

# d follows the rules, over the facts fs, with ctx the context
def Valid(+es: List<&2, SK.Ent>, +fs: List<&2, Fact>, +ctx: List<&2, E.QExpr>, d: Der) -> Type:
  match d:
    case DPrem{+i}:
      HasFact(fact_at(fs, i))
    case DKLin{+l1, +d1, +l2, +d2}:
      Valid(es, fs, ctx, d1) & (Valid(es, fs, ctx, d2) & (IsK(concl(es, fs, d1)) & IsK(concl(es, fs, d2))))
    case DBack{+d}:
      Valid(es, fs, ctx, d) & (IsP(concl(es, fs, d)) & {Jd.a(concl(es, fs, d)) == NFrame{} : Node})
    case DLine{+d1, +d2, +re}:
      Valid(es, fs, ctx, d1) & (Valid(es, fs, ctx, d2) & (IsP(concl(es, fs, d1)) & (IsP(concl(es, fs, d2)) & ({Jd.a(concl(es, fs, d1)) == Jd.a(concl(es, fs, d2)) : Node} & (Open(es, ctx, Jd.a(concl(es, fs, d1))) & SameV(Jd.x(concl(es, fs, d2)), imul(Jd.x(concl(es, fs, d1)))))))))
    case DPPrem{+i}:
      HasStat(fact_at(fs, i))
    case DSelf{+a}:
      Unit
    case DPLin{+m1, +d1, +m2, +d2}:
      Valid(es, fs, ctx, d1) & (Valid(es, fs, ctx, d2) & (IsP(concl(es, fs, d1)) & (IsP(concl(es, fs, d2)) & {Jd.a(concl(es, fs, d1)) == Jd.a(concl(es, fs, d2)) : Node})))
    case DKnown{+d, +dr, +di}:
      Valid(es, fs, ctx, d) & (Valid(es, fs, ctx, dr) & (Valid(es, fs, ctx, di) & (IsP(concl(es, fs, d)) & (IsK(concl(es, fs, dr)) & IsK(concl(es, fs, di))))))
    case DTurn{+d, +g, +b}:
      Valid(es, fs, ctx, d) & (IsP(concl(es, fs, d)) & SameV(Jd.x(concl(es, fs, d)), gmul(Lab.conj(g), zseg(es, b))))
    case DThrough{+d1, +d2, +g, +b}:
      Valid(es, fs, ctx, d1) & (Valid(es, fs, ctx, d2) & (IsP(concl(es, fs, d1)) & (IsP(concl(es, fs, d2)) & (SameV(Jd.x(concl(es, fs, d1)), gmul(Lab.conj(g), zseg(es, b))) & ({Jd.a(concl(es, fs, d2)) == NSeg{b} : Node} & Open(es, ctx, NSeg{b}))))))
    case DFrame{+d, +x}:
      Valid(es, fs, ctx, d) & (IsK(concl(es, fs, d)) & Same(Jd.e(concl(es, fs, d)), SK.VE.y(x)))
    case DVoid{+dr, +di, +a, +x}:
      Valid(es, fs, ctx, dr) & (Valid(es, fs, ctx, di) & (IsK(concl(es, fs, dr)) & (IsK(concl(es, fs, di)) & (Same(Jd.e(concl(es, fs, dr)), SK.VE.x(zdir(es, a))) & Same(Jd.e(concl(es, fs, di)), SK.VE.y(zdir(es, a)))))))

# Refutations
# -----------
# What makes a set of constraints, with the one judged, unable to hold
# where the refutation's nd is nonzero (degree-0 refutations of the
# equations alone stay spec/solve.bend's Refutes0):
# - a Motzkin refutation of K facts with the side conditions;
# - a derived collapse: both parts of an open segment's direction are K
#   facts;
# - an Angle on a segment whose collapse is K facts: its side dot > 0 is
#   then 0 (its meaning needs the direction nonzero).

type DRef is Data:
  # the K facts ds with multipliers ls, the sides with ms >= 0, = k
  RMotz{ds: List<&2, Der>, ls: List<&2, S.Q>, ms: List<&2, S.Q>, k: S.Q}
  # segment s, open, with K(Re z_s) and K(Im z_s)
  RColl{dr: Der, di: Der, s: Nat}
  # the Angle at constraint position p (one of those refuted), its first
  # segment (fst) or its second collapsed: K(Re z), K(Im z)
  RAngle{dr: Der, di: Der, p: Nat, fst: Bool}

def dconcls(+es: List<&2, SK.Ent>, +fs: List<&2, Fact>, ds: List<&2, Der>) -> List<&2, E.QExpr>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      Con{Jd.e(concl(es, fs, d)), dconcls(es, fs, t)}

def AllValidK(+es: List<&2, SK.Ent>, +fs: List<&2, Fact>, +ctx: List<&2, E.QExpr>, ds: List<&2, Der>) -> Type:
  match ds:
    case Nil{}:
      Unit
    case Con{+d, t}:
      Valid(es, fs, ctx, d) & (IsK(concl(es, fs, d)) & AllValidK(es, fs, ctx, t))

def nds(+es: List<&2, SK.Ent>, +fs: List<&2, Fact>, ds: List<&2, Der>) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, t}:
      ncat(nd(es, fs, d), nds(es, fs, t))

def ref.nd(+es: List<&2, SK.Ent>, +fs: List<&2, Fact>, r: DRef) -> List<&2, Nat>:
  match r:
    case RMotz{+ds, +ls, +ms, +k}:
      nds(es, fs, ds)
    case RColl{+dr, +di, +s}:
      Con{s, ncat(nd(es, fs, dr), nd(es, fs, di))}
    case RAngle{+dr, +di, +p, +fst}:
      ncat(nd(es, fs, dr), nd(es, fs, di))

# the Angle's segment that a refutation says collapsed, if the
# constraint is an Angle
def angle_seg(k: SK.Constraint, fst: Bool) -> Maybe<&2, Nat>:
  match k fst:
    case SK.Angle{a, ra, b, rb, c, s} True{}:
      Some{a}
    case SK.Angle{a, ra, b, rb, c, s} False{}:
      Some{b}
    case _ fst:
      None{}

def AngleColl(+es: List<&2, SK.Ent>, +fs: List<&2, Fact>, +dr: Der, +di: Der, m: Maybe<&2, Nat>) -> Type:
  match m:
    case Some{+a}:
      Same(Jd.e(concl(es, fs, dr)), SK.VE.x(zseg(es, a))) & Same(Jd.e(concl(es, fs, di)), SK.VE.y(zseg(es, a)))
    case None{}:
      Empty

# r refutes the facts fs (with ks the constraints the facts at each
# position come from, and ss the side conditions), in the context ctx.
# The Motzkin case is spec/solve.bend's Refutes0 condition, stated there
# (RefutesK), since it reads its sign checks.
def RefColl(+es: List<&2, SK.Ent>, +fs: List<&2, Fact>, +ctx: List<&2, E.QExpr>, +dr: Der, +di: Der, +s: Nat) -> Type:
  Valid(es, fs, ctx, dr) & (Valid(es, fs, ctx, di) & (IsK(concl(es, fs, dr)) & (IsK(concl(es, fs, di)) & (Same(Jd.e(concl(es, fs, dr)), SK.VE.x(zseg(es, s))) & (Same(Jd.e(concl(es, fs, di)), SK.VE.y(zseg(es, s))) & Open(es, ctx, NSeg{s}))))))

def RefAngle(+es: List<&2, SK.Ent>, +fs: List<&2, Fact>, +ctx: List<&2, E.QExpr>, +dr: Der, +di: Der, +k: SK.Constraint, +fst: Bool) -> Type:
  Valid(es, fs, ctx, dr) & (Valid(es, fs, ctx, di) & (IsK(concl(es, fs, dr)) & (IsK(concl(es, fs, di)) & AngleColl(es, fs, dr, di, angle_seg(k, fst)))))

# Nondegeneracy
# -------------

# segment s has nonzero length at env, stated as its squared length being
# positive (in an ordered field the same as its endpoints differing; it is
# also exactly the side condition Gt0{|z_s|^2} the verdict checks)
def Long(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, +s: Nat) -> Data:
  O.lt(F, O.zero(F), O.eval(~F, env, SK.VE.norm2(zseg(es, s))))

# every segment of nd has nonzero length
def Longs(~F: O.OField, +env: List<&2, O.C(F)>, +es: List<&2, SK.Ent>, nd: List<&2, Nat>) -> Data:
  match nd:
    case Nil{}:
      Unit
    case Con{+s, t}:
      SK.Both(Long(~F, env, es, s), Longs(~F, env, es, t))

# |s|^2, the factor of nd's segment s in a certificate
def norm2(+es: List<&2, SK.Ent>, +s: Nat) -> E.QExpr:
  SK.VE.norm2(zseg(es, s))

# the certificate's h: the product of nd's squared lengths (1 for none)
def ndh(+es: List<&2, SK.Ent>, nd: List<&2, Nat>) -> E.QExpr:
  match nd:
    case Nil{}:
      cst(qo())
    case Con{+s, t}:
      E.QMul{norm2(es, s), ndh(es, t)}

# the side conditions saying nd's segments are nonzero (the verdict
# checks them over the box)
def ndsides(+es: List<&2, SK.Ent>, nd: List<&2, Nat>) -> List<&2, SK.Side>:
  match nd:
    case Nil{}:
      Nil{}
    case Con{+s, t}:
      Con{SK.Gt0{norm2(es, s)}, ndsides(es, t)}
