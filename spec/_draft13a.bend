# bend-cad spec: what the solver's answers mean (DESIGN §10.2, §8.11).
# Trusted; DRAFT FOR REVIEW (sk-13a v4, SK13A-REVIEW.md) with the solve_*
# laws in ROADMAP.bend.
#
# The solver classifies each constraint (by its position in the sketch's
# list of constraints, counting driven ones too, so that a repeated id
# cannot drop a second constraint):
# - red: made driven (Rec's driven flag; a driven constraint contributes
#   no equations), with a reason: Over (one of its equations lies in a
#   structurally over-determined set of its own and earlier solved
#   equations) or Conflict (a degree-0 refutation with its support, kept
#   constraints before it);
# - amber: redundant: its equations follow from earlier solved ones and
#   its side conditions from the premises before it;
# - kept, with some equations perhaps dropped from the system solved.
# Every judgment is a derivation in the layer's proof system (degree 0:
# constant multipliers, Motzkin's form), with completeness conditions; the
# semantic laws (solve_drop, solve_amber, solve_conflict) follow. Honest
# (below) collects the conditions on a classification; honest_unique says
# the sketch determines the classification.
#
# The solver may also pin variables: hold free degrees of freedom at the
# drawing's values (radius 0). held says each pin is exactly at its drawn
# value with radius 0, so a pin never moves anything the user drew.

import Base
import ./num.bend as S
import ./ring.bend as E
import ./field.bend as O
import ./mat.bend as M
import ./knum.bend as N
import ./_draft_sketch13a.bend as SK
import ./box.bend as BX

# Lists of numbers
# ----------------

def band(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      False{}

def bor(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      True{}
    case False{}:
      b

def bnot(a: Bool) -> Bool:
  match a:
    case True{}:
      False{}
    case False{}:
      True{}

def eq(a: Nat, b: Nat) -> Bool:
  match a b:
    case 0n 0n:
      True{}
    case 0n 1n+j:
      False{}
    case 1n+i 0n:
      False{}
    case 1n+i 1n+j:
      eq(i, j)

def lt(a: Nat, b: Nat) -> Bool:
  match a b:
    case a 0n:
      False{}
    case 0n 1n+j:
      True{}
    case 1n+i 1n+j:
      lt(i, j)

def mem(+v: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      bor(eq(v, h), mem(v, t))

def len(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+len(t)

def nth(xs: List<&2, Nat>, k: Nat) -> Nat:
  match xs k:
    case Nil{} k:
      0n
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      nth(t, j)

# no entry twice
def distinct(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, +t}:
      band(bnot(mem(h, t)), distinct(t))

# every entry is below n
def below(xs: List<&2, Nat>, +n: Nat) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      band(lt(h, n), below(t, n))

# Over-determined sets of equations
# ---------------------------------

# every variable of e is in w
def inside(e: E.QExpr, +w: List<&2, Nat>) -> Bool:
  match e:
    case E.QVar{v}:
      mem(v, w)
    case E.QCst{q}:
      True{}
    case E.QAdd{a, b}:
      band(inside(a, w), inside(b, w))
    case E.QSub{a, b}:
      band(inside(a, w), inside(b, w))
    case E.QMul{a, b}:
      band(inside(a, w), inside(b, w))
    case E.QNeg{a}:
      inside(a, w)

def neqs(es: List<&2, E.QExpr>) -> Nat:
  match es:
    case Nil{}:
      0n
    case Con{e, t}:
      1n+neqs(t)

# equation j of es (0 = 0 past the end)
def eqat(es: List<&2, E.QExpr>, j: Nat) -> E.QExpr:
  match es j:
    case Nil{} j:
      E.QCst{S.Q{S.Z0{}, S.XH{}}}
    case Con{e, t} 0n:
      e
    case Con{e, t} 1n+i:
      eqat(t, i)

def all_inside(+es: List<&2, E.QExpr>, s: List<&2, Nat>, +w: List<&2, Nat>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case Con{j, t}:
      band(inside(eqat(es, j), w), all_inside(es, t, w))

# s names distinct equations of es, every variable they use is in w, and w
# is shorter than s
def overdet(+es: List<&2, E.QExpr>, +s: List<&2, Nat>, +w: List<&2, Nat>) -> Bool:
  band(distinct(s), band(below(s, neqs(es)), band(lt(len(w), len(s)), all_inside(es, s, w))))

# Which constraint each equation comes from
# -----------------------------------------
# Sketch.eqs lists every driving constraint's equations in order; owners
# lists, in the same order, the position of each one's constraint in the
# sketch's list of constraints.

def reps(n: Nat, +x: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{x, reps(m, x)}

def cat(xs: List<&2, Nat>, ys: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, cat(t, ys)}

def owners.go(+es: List<&2, SK.Ent>, cs: List<&2, SK.Rec>, +i: Nat) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{SK.Rec{id, True{}, k}, t}:
      owners.go(es, t, 1n+i)
    case Con{SK.Rec{id, False{}, k}, t}:
      cat(reps(neqs(SK.Constraint.eqs(es, k)), i), owners.go(es, t, 1n+i))

def owners(sk: SK.Sketch) -> List<&2, Nat>:
  match sk:
    case SK.Sketch{vs, +es, cs}:
      owners.go(es, cs, 0n)

# Red constraints
# ---------------

# the constraints at the positions in red become driven
def mark.cons(+red: List<&2, Nat>, cs: List<&2, SK.Rec>, +i: Nat) -> List<&2, SK.Rec>:
  match cs:
    case Nil{}:
      Nil{}
    case Con{SK.Rec{id, dr, k}, t}:
      Con{SK.Rec{id, bor(dr, mem(i, red)), k}, mark.cons(red, t, 1n+i)}

def mark(+red: List<&2, Nat>, sk: SK.Sketch) -> SK.Sketch:
  match sk:
    case SK.Sketch{vs, es, cs}:
      SK.Sketch{vs, es, mark.cons(red, cs, 0n)}

# Judgments as (in)feasibility (sk-13a, DESIGN §8.11, Q24)
# --------------------------------------------------------
# What the solver says about a constraint is a statement about solution
# sets, in every ordered field (the same, for these statements, as over the
# reals), never about its box:
# - amber (redundant): the constraints before it imply it, its side
#   conditions included, so deleting every amber constraint changes no
#   solution (solve_amber);
# - red, Conflict: it cannot hold together with its support, kept
#   constraints before it (solve_conflict);
# - red, Over: one of its equations lies in a structurally over-determined
#   set (more equations than variables). This claims the count only, not
#   infeasibility: incidence theorems (Pappus) are over-determined and
#   consistent; Phase 4 decides Over flags exactly.
# Inside its solve the solver may also drop an equation of a kept
# constraint that the equations it solves imply, everywhere (solve_drop).
# The constraint is not made driven: it still holds at the certified
# geometry (solve_exists), and its side conditions are checked as any
# other's. A constraint whose equations are all dropped need not be amber:
# a side condition may still do work (an angle's orientation).

# the equations of es at the positions in js, in the order of js
def picked(+es: List<&2, E.QExpr>, js: List<&2, Nat>) -> List<&2, E.QExpr>:
  match js:
    case Nil{}:
      Nil{}
    case Con{j, t}:
      Con{eqat(es, j), picked(es, t)}

def solved.pick(b: Bool, e: E.QExpr, rest: List<&2, E.QExpr>) -> List<&2, E.QExpr>:
  match b:
    case True{}:
      Con{e, rest}
    case False{}:
      rest

# es from position k: those whose constraint is not red and that are not
# dropped
def solved.go(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +k: Nat) -> List<&2, E.QExpr>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      solved.pick(band(bnot(mem(nth(own, k), red)), bnot(mem(k, ds))), e, solved.go(t, own, red, ds, 1n+k))

# the system the solver solves: the sketch's equations (Sketch.eqs) whose
# constraint is not red and that are not dropped (ds names them in the
# sketch's numbering), in order. With nothing dropped it is the system of
# mark(red, sk).
def solved(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>) -> List<&2, E.QExpr>:
  solved.go(SK.Sketch.eqs(sk), owners(sk), red, ds, 0n)

# The sketch with only the constraints at the positions in cs driving
def only.cons(+cs: List<&2, Nat>, rs: List<&2, SK.Rec>, +i: Nat) -> List<&2, SK.Rec>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{SK.Rec{id, dr, k}, t}:
      Con{SK.Rec{id, bor(dr, bnot(mem(i, cs))), k}, only.cons(cs, t, 1n+i)}

def only(+cs: List<&2, Nat>, sk: SK.Sketch) -> SK.Sketch:
  match sk:
    case SK.Sketch{vs, es, rs}:
      SK.Sketch{vs, es, only.cons(cs, rs, 0n)}

# Certificates for dropped equations
# ----------------------------------

# q times the sketch's equation i
type Mul is Data:
  Mul{i: Nat, q: E.QExpr}

# a certificate for an equation g: h g = q_1 g_i1 + ... + q_n g_in, an
# identity of polynomials (the g_i the sketch's equations). Data only: the
# verdict checks it, and that h is nonzero over the box (h = 1 in the first
# layer); solve_drop says what dropping means, so nothing here is trusted
# beyond its shape.
type Cert is Data:
  Cert{h: E.QExpr, qs: List<&2, Mul>}

# a dropped equation, by its position in Sketch.eqs, and its certificate
type Drop is Data:
  Drop{j: Nat, c: Cert}

# the dropped equations' positions
def drops(ds: List<&2, Drop>) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{Drop{j, c}, t}:
      Con{j, drops(t)}

# Red and amber constraints
# -------------------------

# every equation of s is c's own, or solved and earlier: its constraint is
# before c and not red, and it is not dropped
def clean(+own: List<&2, Nat>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, s: List<&2, Nat>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case Con{+k, t}:
      band(bor(eq(nth(own, k), c), band(lt(nth(own, k), c), band(bnot(mem(nth(own, k), red)), bnot(mem(k, ds))))), clean(own, red, ds, c, t))

# why the constraint at a position is red
type Why is Data:
  # its equation j lies in the over-determined set s (whose variables are
  # among w), made of its own and solved equations
  Over{j: Nat, s: List<&2, Nat>, w: List<&2, Nat>}
  # it cannot hold together with its support, the constraints at the
  # positions s: all kept, all before it, each driving an equation
  # (solve_conflict0 and solve_conflict); s is empty when it cannot hold
  # at all (a distance of -5)
  Conflict{s: List<&2, Nat>}

# no entry of xs is in ys
def none_in(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      band(bnot(mem(h, ys)), none_in(t, ys))

def clen(cs: List<&2, SK.Rec>) -> Nat:
  match cs:
    case Nil{}:
      0n
    case Con{c, t}:
      1n+clen(t)

# the number of constraints
def ncons(sk: SK.Sketch) -> Nat:
  match sk:
    case SK.Sketch{vs, es, cs}:
      clen(cs)

# a driven constraint has none
def ceqs.rec(+es: List<&2, SK.Ent>, r: SK.Rec) -> Nat:
  match r:
    case SK.Rec{id, True{}, k}:
      0n
    case SK.Rec{id, False{}, k}:
      neqs(SK.Constraint.eqs(es, k))

def ceqs.at(+es: List<&2, SK.Ent>, cs: List<&2, SK.Rec>, c: Nat) -> Nat:
  match cs c:
    case Nil{} c:
      0n
    case Con{r, t} 0n:
      ceqs.rec(es, r)
    case Con{r, t} 1n+m:
      ceqs.at(es, t, m)

# the number of equations the constraint at position c contributes (0 if
# it is driven)
def ceqs(sk: SK.Sketch, c: Nat) -> Nat:
  match sk:
    case SK.Sketch{vs, +es, cs}:
      ceqs.at(es, cs, c)

# each of cs drives an equation
def has_eqs(+sk: SK.Sketch, cs: List<&2, Nat>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{c, t}:
      band(lt(0n, ceqs(sk, c)), has_eqs(sk, t))

# the reason y explains the constraint at position c
def why_ok(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, y: Why) -> Bool:
  match y:
    case Over{+j, +s, +w}:
      band(eq(nth(owners(sk), j), c), band(mem(j, s), band(overdet(SK.Sketch.eqs(sk), s, w), clean(owners(sk), red, ds, c, s))))
    case Conflict{+s}:
      band(lt(0n, ceqs(sk, c)), band(distinct(s), band(below(s, c), band(has_eqs(sk, s), none_in(s, red)))))

# each red constraint (rs, in order) is explained by the matching Why,
# red being the whole list and ds the dropped equations
def explained.go(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, rs: List<&2, Nat>, why: List<&2, Why>) -> Bool:
  match rs why:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, yt}:
      False{}
    case Con{c, rt} Nil{}:
      False{}
    case Con{+c, rt} Con{y, yt}:
      band(why_ok(sk, red, ds, c, y), explained.go(sk, red, ds, rt, yt))

# every dropped equation is a kept constraint's
def owners_kept(+own: List<&2, Nat>, +red: List<&2, Nat>, ds: List<&2, Nat>) -> Bool:
  match ds:
    case Nil{}:
      True{}
    case Con{k, t}:
      band(bnot(mem(nth(own, k), red)), owners_kept(own, red, t))

# the dropped equations are distinct equations of kept constraints
def dropped_ok(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>) -> Bool:
  band(distinct(ds), band(below(ds, neqs(SK.Sketch.eqs(sk))), owners_kept(owners(sk), red, ds)))

# no constraint is red twice, the dropped equations are kept ones, and each
# red constraint is explained
def explained(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, why: List<&2, Why>) -> Bool:
  band(distinct(red), band(dropped_ok(sk, red, ds), explained.go(sk, red, ds, red, why)))

# every equation of c (from position k) is dropped
def alldrop.go(own: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +k: Nat) -> Bool:
  match own:
    case Nil{}:
      True{}
    case Con{o, t}:
      band(bor(bnot(eq(o, c)), mem(k, ds)), alldrop.go(t, ds, c, 1n+k))

def alldrop(+sk: SK.Sketch, +ds: List<&2, Nat>, cs: List<&2, Nat>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, t}:
      band(alldrop.go(owners(sk), ds, c, 0n), alldrop(sk, ds, t))

# the amber constraints are distinct, kept, each drives an equation (a
# driven constraint has none), and all their equations are dropped
def amber_ok(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +amber: List<&2, Nat>) -> Bool:
  band(distinct(amber), band(none_in(amber, red), band(has_eqs(sk, amber), alldrop(sk, ds, amber))))

def conflicts.of(c: Nat, y: Why, rest: List<&2, Nat>) -> List<&2, Nat>:
  match y:
    case Over{j, s, w}:
      rest
    case Conflict{s}:
      Con{c, rest}

# the red constraints whose reason is a conflict
def conflicts(red: List<&2, Nat>, why: List<&2, Why>) -> List<&2, Nat>:
  match red why:
    case Con{c, rt} Con{y, yt}:
      conflicts.of(c, y, conflicts(rt, yt))
    case Nil{} why:
      Nil{}
    case Con{c, rt} Nil{}:
      Nil{}

def support.pick(b: Bool, s: List<&2, Nat>, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      s
    case False{}:
      rest

def support.of(+c: Nat, +r: Nat, y: Why, rest: List<&2, Nat>) -> List<&2, Nat>:
  match y:
    case Over{j, s, w}:
      rest
    case Conflict{s}:
      support.pick(eq(r, c), s, rest)

def over_at.of(+c: Nat, +j: Nat, +r: Nat, y: Why) -> Bool:
  match y:
    case Over{jj, s, w}:
      band(eq(r, c), eq(jj, j))
    case Conflict{s}:
      False{}

# the red constraint c is red as Over, with its equation j
def over_at(+c: Nat, +j: Nat, red: List<&2, Nat>, why: List<&2, Why>) -> Bool:
  match red why:
    case Con{+r, rt} Con{y, yt}:
      bor(over_at.of(c, j, r, y), over_at(c, j, rt, yt))
    case Nil{} why:
      False{}
    case Con{r, rt} Nil{}:
      False{}

# the support of the red constraint c's conflict
def support(+c: Nat, red: List<&2, Nat>, why: List<&2, Why>) -> List<&2, Nat>:
  match red why:
    case Con{+r, rt} Con{y, yt}:
      support.of(c, r, y, support(c, rt, yt))
    case Nil{} why:
      Nil{}
    case Con{r, rt} Nil{}:
      Nil{}

def unmark.go(b: Bool, h: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      rest
    case False{}:
      Con{h, rest}

# xs without c
def unmark(+c: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      unmark.go(eq(h, c), h, unmark(c, t))

# Degree-0 derivations: the first layer's proof system
# ----------------------------------------------------
# The laws about dropped, amber and conflicting constraints state the
# derivation itself (a combination with constant coefficients), not only
# what it implies: an implication from premises that have no solution says
# nothing, but "this equation is 1 times that one" stays true however the
# rest of the sketch fails. The semantic laws (solve_drop, solve_amber,
# solve_conflict) follow from these.

def qlen(xs: List<&2, S.Q>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+qlen(t)

# l_1 e_1 + ... + l_n e_n
def lin(ls: List<&2, S.Q>, es: List<&2, E.QExpr>) -> E.QExpr:
  match ls es:
    case Con{l, lt} Con{e, et}:
      E.QAdd{E.QMul{E.QCst{l}, e}, lin(lt, et)}
    case Nil{} es:
      E.QCst{S.Q{S.Z0{}, S.XH{}}}
    case Con{l, lt} Nil{}:
      E.QCst{S.Q{S.Z0{}, S.XH{}}}

# every entry is 0 (its numerator is)
def AllZero(ls: List<&2, S.Q>) -> Data:
  match ls:
    case Nil{}:
      Unit
    case Con{l, t}:
      M.Both({S.Q.num(l) == S.Z0{} : S.Z}, AllZero(t))

def qzero() -> S.Q:
  S.Q{S.Z0{}, S.XH{}}

def islt(c: Cmp) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      False{}
    case GT{}:
      False{}

# e1 and e2 are the same polynomial: equal at every rational point (Q is
# infinite, so this is equality of polynomials, and then they agree in
# every ordered field)
def Ident(+e1: E.QExpr, +e2: E.QExpr) -> Type:
  @x: List<&2, S.Q> -> S.Q.eq(E.qeval(x, e1), E.qeval(x, e2))

# a side condition's expression
def sexpr(s: SK.Side) -> E.QExpr:
  match s:
    case SK.Gt0{e}:
      e
    case SK.Ge0{e}:
      e

def slen(ss: List<&2, SK.Side>) -> Nat:
  match ss:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+slen(t)

# m_1 s_1 + ... + m_n s_n, the s_k side conditions' expressions
def slin(ms: List<&2, S.Q>, ss: List<&2, SK.Side>) -> E.QExpr:
  match ms ss:
    case Con{m, mt} Con{h, st}:
      E.QAdd{E.QMul{E.QCst{m}, sexpr(h)}, slin(mt, st)}
    case Nil{} ss:
      E.QCst{qzero()}
    case Con{m, mt} Nil{}:
      E.QCst{qzero()}

# the side condition that holds exactly where s fails
def negate(s: SK.Side) -> SK.Side:
  match s:
    case SK.Gt0{e}:
      SK.Ge0{E.QNeg{e}}
    case SK.Ge0{e}:
      SK.Gt0{E.QNeg{e}}

# every entry is >= 0
def nonneg(ms: List<&2, S.Q>) -> Bool:
  match ms:
    case Nil{}:
      True{}
    case Con{+m, t}:
      band(bnot(islt(S.Q.cmp(m, qzero()))), nonneg(t))

# some strict side condition has a positive multiplier
def strict_pos(ms: List<&2, S.Q>, ss: List<&2, SK.Side>) -> Bool:
  match ms ss:
    case Con{+m, mt} Con{SK.Gt0{e}, st}:
      bor(islt(S.Q.cmp(qzero(), m)), strict_pos(mt, st))
    case Con{m, mt} Con{SK.Ge0{e}, st}:
      strict_pos(mt, st)
    case Nil{} ss:
      False{}
    case Con{m, mt} Nil{}:
      False{}

def iszz(z: S.Z) -> Bool:
  match z:
    case S.Z0{}:
      True{}
    case S.Zpos{p}:
      False{}
    case S.Zneg{p}:
      False{}

def refok(+ls: List<&2, S.Q>, +ms: List<&2, S.Q>, +k: S.Q, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>) -> Bool:
  band(eq(qlen(ls), neqs(es)), band(eq(qlen(ms), slen(ss)), band(nonneg(ms), bor(islt(S.Q.cmp(k, qzero())), band(iszz(S.Q.num(k)), strict_pos(ms, ss))))))

# a degree-0 refutation of the equations es and side conditions ss
# (Motzkin's form): constants l_i (one per equation), m_k >= 0 (one per
# side condition) and k with
#   l_1 e_1 + ... + m_1 s_1 + ... = k
# as polynomials, and k < 0, or k = 0 with m_k > 0 for some strict s_k.
# Wherever every e_i is 0 and every s_k holds, the left side is >= 0 (> 0
# in the second case), so no point, in any ordered field, satisfies them
# all
def Refutes0(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +ls: List<&2, S.Q>, +ms: List<&2, S.Q>, +k: S.Q) -> Type:
  {refok(ls, ms, k, es, ss) == True{} : Bool} & Ident(E.QAdd{lin(ls, es), slin(ms, ss)}, E.QCst{k})

# The pieces the derivations are about
# ------------------------------------

def eqs_of.go(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +cs: List<&2, Nat>, +k: Nat) -> List<&2, E.QExpr>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      solved.pick(mem(nth(own, k), cs), e, eqs_of.go(t, own, cs, 1n+k))

# the sketch's equations owned by the constraints at the positions cs, in
# order
def eqs_of(+sk: SK.Sketch, +cs: List<&2, Nat>) -> List<&2, E.QExpr>:
  eqs_of.go(SK.Sketch.eqs(sk), owners(sk), cs, 0n)

def csides.pick(b: Bool, xs: List<&2, SK.Side>, rest: List<&2, SK.Side>) -> List<&2, SK.Side>:
  match b:
    case True{}:
      SK.cats(xs, rest)
    case False{}:
      rest

def csides.go(+es: List<&2, SK.Ent>, rs: List<&2, SK.Rec>, +cs: List<&2, Nat>, +i: Nat) -> List<&2, SK.Side>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{SK.Rec{id, True{}, k}, t}:
      csides.go(es, t, cs, 1n+i)
    case Con{SK.Rec{id, False{}, +k}, t}:
      csides.pick(mem(i, cs), SK.Constraint.sides(es, k), csides.go(es, t, cs, 1n+i))

# the side conditions of the driving constraints at the positions cs, in
# order
def csides(sk: SK.Sketch, +cs: List<&2, Nat>) -> List<&2, SK.Side>:
  match sk:
    case SK.Sketch{vs, +es, rs}:
      csides.go(es, rs, cs, 0n)

# every entity's side conditions (a circle's r > 0, an arc's bulge > 0)
def esides(sk: SK.Sketch) -> List<&2, SK.Side>:
  match sk:
    case SK.Sketch{vs, es, rs}:
      SK.Sketch.sides.ents(es)

def below_solved.go(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +j: Nat, +k: Nat) -> List<&2, E.QExpr>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      solved.pick(band(lt(k, j), band(bnot(mem(nth(own, k), red)), bnot(mem(k, ds)))), e, below_solved.go(t, own, red, ds, j, 1n+k))

# the solved equations at positions before j (in Sketch.eqs)
def below_solved(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +j: Nat) -> List<&2, E.QExpr>:
  below_solved.go(SK.Sketch.eqs(sk), owners(sk), red, ds, j, 0n)

def kept.pick(b: Bool, i: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      Con{i, rest}
    case False{}:
      rest

def kept.go(rs: List<&2, SK.Rec>, +red: List<&2, Nat>, +c: Nat, +i: Nat) -> List<&2, Nat>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{SK.Rec{id, True{}, k}, t}:
      kept.go(t, red, c, 1n+i)
    case Con{SK.Rec{id, False{}, k}, t}:
      kept.pick(band(lt(i, c), bnot(mem(i, red))), i, kept.go(t, red, c, 1n+i))

# the kept (not red), driving constraints at positions before c
def kept_before(sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat) -> List<&2, Nat>:
  match sk:
    case SK.Sketch{vs, es, rs}:
      kept.go(rs, red, c, 0n)

# the side condition at position i of a list (0 > 0, which never holds,
# past its end)
def side_at(ss: List<&2, SK.Side>, i: Nat) -> SK.Side:
  match ss i:
    case Nil{} i:
      SK.Gt0{E.QCst{qzero()}}
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+m:
      side_at(t, m)

# A one-to-one matching (for solve_total)
# ---------------------------------------

# e mentions the variable v
def uses(+v: Nat, e: E.QExpr) -> Bool:
  match e:
    case E.QVar{i}:
      eq(i, v)
    case E.QCst{q}:
      False{}
    case E.QAdd{a, b}:
      bor(uses(v, a), uses(v, b))
    case E.QSub{a, b}:
      bor(uses(v, a), uses(v, b))
    case E.QMul{a, b}:
      bor(uses(v, a), uses(v, b))
    case E.QNeg{a}:
      uses(v, a)

# every entry of xs is in ys
def sub(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      band(mem(h, ys), sub(t, ys))

# equation i of es mentions entry i of m, one entry per equation
def uses_all(es: List<&2, E.QExpr>, m: List<&2, Nat>) -> Bool:
  match es m:
    case Nil{} Nil{}:
      True{}
    case Con{e, t} Con{+v, u}:
      band(uses(v, e), uses_all(t, u))
    case Nil{} Con{v, u}:
      False{}
    case Con{e, t} Nil{}:
      False{}

# m matches the equations es one to one with the variables vs: equation i
# with entry i of m, a variable it mentions, and every variable of vs is
# some equation's (so the system is square). `uses` is syntactic, so this
# is about structure only; regularity is solve_complete's and
# solve_regular's
def perfect(+es: List<&2, E.QExpr>, +vs: List<&2, Nat>, +m: List<&2, Nat>) -> Bool:
  band(eq(len(vs), len(m)), band(distinct(m), band(sub(m, vs), uses_all(es, m))))

# Honest classifications (sk-13a)
# --------------------------------
# What the derivation and completeness laws say about the solver's answer,
# as one predicate of any classification (red, why, dropped equations ds,
# amber), so that two honest classifications of a sketch can be compared:
# honest_unique says the sketch determines which constraints are red, which
# of those conflict, which equations are dropped and which constraints are
# amber; only the witnesses and supports shown may differ.

def own_below.go(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +c: Nat, +i: Nat, +k: Nat) -> List<&2, E.QExpr>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      solved.pick(band(lt(k, i), eq(nth(own, k), c)), e, own_below.go(t, own, c, i, 1n+k))

# c's own equations at positions before i
def own_below(+sk: SK.Sketch, +c: Nat, +i: Nat) -> List<&2, E.QExpr>:
  own_below.go(SK.Sketch.eqs(sk), owners(sk), c, i, 0n)

def over_s.of(+c: Nat, +r: Nat, y: Why, rest: List<&2, Nat>) -> List<&2, Nat>:
  match y:
    case Over{j, s, w}:
      support.pick(eq(r, c), s, rest)
    case Conflict{s}:
      rest

# the over-determined set of the red constraint c's Over
def over_s(+c: Nat, red: List<&2, Nat>, why: List<&2, Why>) -> List<&2, Nat>:
  match red why:
    case Con{+r, rt} Con{y, yt}:
      over_s.of(c, r, y, over_s(c, rt, yt))
    case Nil{} why:
      Nil{}
    case Con{r, rt} Nil{}:
      Nil{}

# the premises before c: the equations and side conditions of the kept
# constraints before it, and the entities' side conditions
def pre_eqs(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat) -> List<&2, E.QExpr>:
  eqs_of(sk, kept_before(sk, red, c))

def pre_sides(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat) -> List<&2, SK.Side>:
  SK.cats(csides(sk, kept_before(sk, red, c)), esides(sk))

# every dropped equation is a constant combination of the solved equations
# before it
def Drop0(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>) -> Type:
  @j: Nat -> {mem(j, ds) == True{} : Bool} -> &ls: List<&2, S.Q> -> Ident(eqat(SK.Sketch.eqs(sk), j), lin(ls, below_solved(sk, red, ds, j)))

# the premises before c, and the negation of c's i-th side condition
def neg_pre(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat, +i: Nat) -> List<&2, SK.Side>:
  SK.cats(pre_sides(sk, red, c), [negate(side_at(csides(sk, [c]), i))])

# every side condition of an amber constraint is implied by the premises
# before it: they and its negation have a degree-0 refutation
def Amber0(+sk: SK.Sketch, +red: List<&2, Nat>, +amber: List<&2, Nat>) -> Type:
  @c: Nat -> {mem(c, amber) == True{} : Bool} -> @i: Nat -> {lt(i, slen(csides(sk, [c]))) == True{} : Bool} -> &ls: List<&2, S.Q> -> &ms: List<&2, S.Q> -> &k: S.Q -> Refutes0(pre_eqs(sk, red, c), neg_pre(sk, red, c, i), ls, ms, k)

# every conflict has a degree-0 refutation with its support
def Conflict0(+sk: SK.Sketch, +red: List<&2, Nat>, +why: List<&2, Why>) -> Type:
  @c: Nat -> {mem(c, conflicts(red, why)) == True{} : Bool} -> &ls: List<&2, S.Q> -> &ms: List<&2, S.Q> -> &k: S.Q -> Refutes0(eqs_of(sk, Con{c, support(c, red, why)}), SK.cats(csides(sk, Con{c, support(c, red, why)}), esides(sk)), ls, ms, k)

# and none without any one member of its support (the support is
# irreducible)
def ConflictMin(+sk: SK.Sketch, +red: List<&2, Nat>, +why: List<&2, Why>) -> Type:
  @c: Nat -> {mem(c, conflicts(red, why)) == True{} : Bool} -> @m: Nat -> {mem(m, support(c, red, why)) == True{} : Bool} -> @ls: List<&2, S.Q> -> @ms: List<&2, S.Q> -> @k: S.Q -> Refutes0(eqs_of(sk, Con{c, unmark(m, support(c, red, why))}), SK.cats(csides(sk, Con{c, unmark(m, support(c, red, why))}), esides(sk)), ls, ms, k) -> Empty

# no constant combination of the solved equations, other than all zeros,
# is constant
def Deg0(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>) -> Type:
  @ls: List<&2, S.Q> -> {qlen(ls) == neqs(solved(sk, red, ds)) : Nat} -> @k: S.Q -> Ident(lin(ls, solved(sk, red, ds)), E.QCst{k}) -> AllZero(ls)

# the kept system (solved equations, every kept constraint's side
# conditions, the entities') has no degree-0 refutation
def Mz0(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>) -> Type:
  @ls: List<&2, S.Q> -> @ms: List<&2, S.Q> -> @k: S.Q -> Refutes0(solved(sk, red, ds), SK.cats(csides(sk, kept_before(sk, red, ncons(sk))), esides(sk)), ls, ms, k) -> Empty

# a red constraint is Over only when degree 0 finds nothing for it: none of
# its equations in the over-determined set is a constant combination, plus
# a constant, of the solved equations before it and its own earlier ones;
# and it has no degree-0 refutation with the premises before it
def Over0(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +why: List<&2, Why>) -> Type:
  @c: Nat -> @j: Nat -> {over_at(c, j, red, why) == True{} : Bool} -> ((@i: Nat -> {band(mem(i, over_s(c, red, why)), eq(nth(owners(sk), i), c)) == True{} : Bool} -> @ls: List<&2, S.Q> -> @k: S.Q -> Ident(eqat(SK.Sketch.eqs(sk), i), E.QAdd{lin(ls, SK.cat(below_solved(sk, red, ds, i), own_below(sk, c, i))), E.QCst{k}}) -> Empty) & (@ls: List<&2, S.Q> -> @ms: List<&2, S.Q> -> @k: S.Q -> Refutes0(SK.cat(pre_eqs(sk, red, c), eqs_of(sk, [c])), SK.cats(pre_sides(sk, red, c), csides(sk, [c])), ls, ms, k) -> Empty))

# redundancy is reported: a kept constraint that drives an equation, has
# all its equations dropped, and whose every side condition is implied by
# the premises before it, is amber
def AmberComplete(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +amber: List<&2, Nat>) -> Type:
  @c: Nat -> {mem(c, red) == False{} : Bool} -> {lt(0n, ceqs(sk, c)) == True{} : Bool} -> {alldrop(sk, ds, [c]) == True{} : Bool} -> (@i: Nat -> {lt(i, slen(csides(sk, [c]))) == True{} : Bool} -> &ls: List<&2, S.Q> -> &ms: List<&2, S.Q> -> &k: S.Q -> Refutes0(pre_eqs(sk, red, c), neg_pre(sk, red, c, i), ls, ms, k)) -> {mem(c, amber) == True{} : Bool}

# the solved system has a one-to-one matching of its equations with
# variables each mentions (no structurally over-determined part)
def Matchable(+es: List<&2, E.QExpr>) -> Type:
  &m: List<&2, Nat> -> {band(distinct(m), uses_all(es, m)) == True{} : Bool}

# an honest classification of the sketch: red with reasons, dropped
# equations ds, amber
def Honest(+sk: SK.Sketch, +red: List<&2, Nat>, +why: List<&2, Why>, +ds: List<&2, Nat>, +amber: List<&2, Nat>) -> Type:
  {band(explained(sk, red, ds, why), amber_ok(sk, red, ds, amber)) == True{} : Bool} & (Drop0(sk, red, ds) & (Amber0(sk, red, amber) & (Conflict0(sk, red, why) & (ConflictMin(sk, red, why) & (Deg0(sk, red, ds) & (Mz0(sk, red, ds) & (Over0(sk, red, ds, why) & (AmberComplete(sk, red, ds, amber) & Matchable(solved(sk, red, ds))))))))))

# Pins
# ----

def dzero() -> S.D:
  S.D{S.Z0{}, 0n}

def dnth(xs: List<&2, S.D>, k: Nat) -> S.D:
  match xs k:
    case Nil{} k:
      dzero()
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      dnth(t, j)

def iseq(c: Cmp) -> Bool:
  match c:
    case LT{}:
      False{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

# a = b as numbers
def deq(+a: S.D, +b: S.D) -> Bool:
  iseq(S.Q.cmp(S.D.toq(a), S.D.toq(b)))

# every pin has radius 0 in the box and its center is its drawn value
def held(pins: List<&2, Nat>, +g0: List<&2, S.D>, +gc: List<&2, S.D>, +gr: List<&2, S.D>) -> Bool:
  match pins:
    case Nil{}:
      True{}
    case Con{+v, t}:
      band(deq(dnth(gr, v), dzero()), band(deq(dnth(gc, v), dnth(g0, v)), held(t, g0, gc, gr)))

# For completeness (solve_complete)
# ---------------------------------

def free.go(b: Bool, k: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      rest
    case False{}:
      Con{k, rest}

# the variables 0 .. n - 1 that are not pins, in order (from k)
def free(n: Nat, +k: Nat, +pins: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      free.go(mem(k, pins), k, free(m, 1n+k, pins))

# a positive is a power of two
def pow2(p: S.Pos) -> Bool:
  match p:
    case S.XH{}:
      True{}
    case S.XO{q}:
      pow2(q)
    case S.XI{q}:
      False{}

# every constant of e is written over a power of two (so the dyadics, the
# solver's numbers, hold it exactly)
def dyconst(e: E.QExpr) -> Bool:
  match e:
    case E.QVar{v}:
      True{}
    case E.QCst{S.Q{n, d}}:
      pow2(d)
    case E.QAdd{a, b}:
      band(dyconst(a), dyconst(b))
    case E.QSub{a, b}:
      band(dyconst(a), dyconst(b))
    case E.QMul{a, b}:
      band(dyconst(a), dyconst(b))
    case E.QNeg{a}:
      dyconst(a)

def dyeqs(es: List<&2, E.QExpr>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, t}:
      band(dyconst(e), dyeqs(t))

def dysides(ss: List<&2, SK.Side>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{SK.Gt0{e}, t}:
      band(dyconst(e), dysides(t))
    case Con{SK.Ge0{e}, t}:
      band(dyconst(e), dysides(t))

# every constant of the sketch's equations and side conditions is dyadic
def dyadic(+sk: SK.Sketch) -> Bool:
  band(dyeqs(SK.Sketch.eqs(sk)), dysides(SK.Sketch.sides(sk)))

# x is the drawing g0 at every pin (g0 read in F through H)
def PinnedAt(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x: M.Vec(~F), pins: List<&2, Nat>, +g0: N.KVec(~K)) -> Data:
  match pins:
    case Nil{}:
      Unit
    case Con{+v, t}:
      M.Both({O.lookup(~F, x, v) == O.lookup(~F, N.ofkv(~K, ~F, ~H, g0), v) : O.C(F)}, PinnedAt(~K, ~F, ~H, x, t, g0))

# |a - b| < d
def Close(~F: O.OField, +a: O.C(F), +b: O.C(F), +d: O.C(F)) -> Data:
  M.Both(O.lt(F, O.sub(~F, a, b), d), O.lt(F, O.sub(~F, b, a), d))

def Near.go(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, pin: Bool, +g: N.KVec(~K), +x: M.Vec(~F), +d: O.C(F), +g0: N.KVec(~K), +v: Nat) -> Data:
  match pin:
    case True{}:
      {O.lookup(~F, N.ofkv(~K, ~F, ~H, g), v) == O.lookup(~F, N.ofkv(~K, ~F, ~H, g0), v) : O.C(F)}
    case False{}:
      Close(~F, O.lookup(~F, N.ofkv(~K, ~F, ~H, g), v), O.lookup(~F, x, v), d)

# the drawing g is within d of x at every variable 0 .. n - 1 (from v)
# that is not a pin, and agrees with the drawing g0 at the pins
def Near(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, n: Nat, +v: Nat, +g: N.KVec(~K), +x: M.Vec(~F), +d: O.C(F), +pins: List<&2, Nat>, +g0: N.KVec(~K)) -> Data:
  match n:
    case 0n:
      Unit
    case 1n+m:
      M.Both(Near.go(~K, ~F, ~H, mem(v, pins), g, x, d, g0, v), Near(~K, ~F, ~H, m, 1n+v, g, x, d, pins, g0))

# a side condition holds strictly at x: e > 0; an e >= 0 whose variables
# are all pins may also hold with equality (its ball has radius 0, so it
# is checked at its exact value; balls cannot certify an expression of a
# free variable at exactly 0)
def Strict.ge(~F: O.OField, b: Bool, +x: M.Vec(~F), +e: E.QExpr) -> Data:
  match b:
    case True{}:
      O.le(~F, O.zero(F), O.eval(~F, x, e))
    case False{}:
      O.lt(F, O.zero(F), O.eval(~F, x, e))

def Strict(~F: O.OField, +x: M.Vec(~F), ss: List<&2, SK.Side>, +pins: List<&2, Nat>) -> Data:
  match ss:
    case Nil{}:
      Unit
    case Con{SK.Gt0{+e}, t}:
      M.Both(O.lt(F, O.zero(F), O.eval(~F, x, e)), Strict(~F, x, t, pins))
    case Con{SK.Ge0{+e}, t}:
      M.Both(Strict.ge(~F, inside(e, pins), x, e), Strict(~F, x, t, pins))
