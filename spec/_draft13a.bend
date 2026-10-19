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
# The answer gives each constraint exactly one class (Kept, Amber, Over,
# Conflict). Every judgment is a derivation in the layer's proof system
# (degree 0: constant multipliers, Motzkin's form); Honest says each
# constraint's class is the honest one given the classes before it, so the
# sketch determines the classification (honest_unique). Structure is read
# from what an equation depends on (its derivative is not identically 0),
# not from how it is written. The semantic laws (solve_drop, solve_amber,
# solve_conflict) follow.
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
import ./sketch.bend as SK
import ./box.bend as BX
import ./deriv.bend as DV

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

# Variables of an expression
# --------------------------

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

# Classes
# -------
# The answer classifies every constraint, by position, with exactly one
# class, so a constraint cannot be red twice, red and amber, or red with
# dropped equations.

# a degree-0 refutation's multipliers (for the verdict to check an amber
# constraint's side conditions by their certificates)
type Ref is Data:
  Ref{ls: List<&2, S.Q>, ms: List<&2, S.Q>, k: S.Q}

type Class is Data:
  # kept; these of its equations are dropped from the system solved
  Kept{ds: List<&2, Drop>}
  # redundant: all its equations are dropped (these), and its side
  # conditions are implied by the premises before it (one refutation of
  # the premises and the side's negation each, rs)
  Amber{ds: List<&2, Drop>, rs: List<&2, Ref>}
  # red: its equation j lies in s, more equations than variables (all in
  # w), made of its own equations and earlier solved ones
  Over{j: Nat, s: List<&2, Nat>, w: List<&2, Nat>}
  # red: it cannot hold together with its support s, kept constraints
  # before it, irreducibly
  Conflict{s: List<&2, Nat>}

# the class of the constraint at position c (kept, nothing dropped, past
# the end)
def class_at(cls: List<&2, Class>, c: Nat) -> Class:
  match cls c:
    case Nil{} c:
      Kept{Nil{}}
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+m:
      class_at(t, m)

def clsn(cls: List<&2, Class>) -> Nat:
  match cls:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+clsn(t)

# 0 kept, 1 amber, 2 over, 3 conflict
def kind(k: Class) -> Nat:
  match k:
    case Kept{ds}:
      0n
    case Amber{ds, rs}:
      1n
    case Over{j, s, w}:
      2n
    case Conflict{s}:
      3n

def is_red(k: Class) -> Bool:
  match k:
    case Kept{ds}:
      False{}
    case Amber{ds, rs}:
      False{}
    case Over{j, s, w}:
      True{}
    case Conflict{s}:
      True{}

def is_amber(k: Class) -> Bool:
  match k:
    case Kept{ds}:
      False{}
    case Amber{ds, rs}:
      True{}
    case Over{j, s, w}:
      False{}
    case Conflict{s}:
      False{}

def is_conflict(k: Class) -> Bool:
  match k:
    case Kept{ds}:
      False{}
    case Amber{ds, rs}:
      False{}
    case Over{j, s, w}:
      False{}
    case Conflict{s}:
      True{}

def pos.pick(b: Bool, i: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      Con{i, rest}
    case False{}:
      rest

def reds.go(cls: List<&2, Class>, +i: Nat) -> List<&2, Nat>:
  match cls:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      pos.pick(is_red(h), i, reds.go(t, 1n+i))

# the red constraints' positions
def reds(cls: List<&2, Class>) -> List<&2, Nat>:
  reds.go(cls, 0n)

def ambers.go(cls: List<&2, Class>, +i: Nat) -> List<&2, Nat>:
  match cls:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      pos.pick(is_amber(h), i, ambers.go(t, 1n+i))

# the amber constraints' positions
def ambers(cls: List<&2, Class>) -> List<&2, Nat>:
  ambers.go(cls, 0n)

def conflicts.go(cls: List<&2, Class>, +i: Nat) -> List<&2, Nat>:
  match cls:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      pos.pick(is_conflict(h), i, conflicts.go(t, 1n+i))

# the conflicting constraints' positions
def conflicts(cls: List<&2, Class>) -> List<&2, Nat>:
  conflicts.go(cls, 0n)

def kdrops(k: Class) -> List<&2, Nat>:
  match k:
    case Kept{ds}:
      drops(ds)
    case Amber{ds, rs}:
      drops(ds)
    case Over{j, s, w}:
      Nil{}
    case Conflict{s}:
      Nil{}

# the dropped equations' positions (in Sketch.eqs)
def dropped(cls: List<&2, Class>) -> List<&2, Nat>:
  match cls:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      cat(kdrops(h), dropped(t))

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

def driven.rec(r: SK.Rec) -> Bool:
  match r:
    case SK.Rec{id, dr, k}:
      dr

def driven.at(cs: List<&2, SK.Rec>, c: Nat) -> Bool:
  match cs c:
    case Nil{} c:
      True{}
    case Con{r, t} 0n:
      driven.rec(r)
    case Con{r, t} 1n+m:
      driven.at(t, m)

# the constraint at position c is driven (or there is none)
def driven(sk: SK.Sketch, c: Nat) -> Bool:
  match sk:
    case SK.Sketch{vs, es, cs}:
      driven.at(cs, c)

# the constraint at position c exists and is driving
def driving(+sk: SK.Sketch, +c: Nat) -> Bool:
  band(lt(c, ncons(sk)), bnot(driven(sk, c)))

# each of cs is driving
def all_driving(+sk: SK.Sketch, cs: List<&2, Nat>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case Con{+c, t}:
      band(driving(sk, c), all_driving(sk, t))

# every equation of c (from position k) is in ds
def alldrop.go(own: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +k: Nat) -> Bool:
  match own:
    case Nil{}:
      True{}
    case Con{o, t}:
      band(bor(bnot(eq(o, c)), mem(k, ds)), alldrop.go(t, ds, c, 1n+k))

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

def support.of(k: Class) -> List<&2, Nat>:
  match k:
    case Kept{ds}:
      Nil{}
    case Amber{ds, rs}:
      Nil{}
    case Over{j, s, w}:
      Nil{}
    case Conflict{s}:
      s

# the support of the constraint at position c, if it conflicts
def support(+cls: List<&2, Class>, +c: Nat) -> List<&2, Nat>:
  support.of(class_at(cls, c))

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

# Dependence, and one-to-one matchings
# -------------------------------------

# e depends on the variable v: its derivative in v is not identically 0 (a
# variable that only cancels, as in x - x + y, does not count)
def Depends(+e: E.QExpr, +v: Nat) -> Type:
  Ident(DV.deriv(e, v), E.QCst{qzero()}) -> Empty

# every variable e depends on is in w
def DependsWithin(+e: E.QExpr, +w: List<&2, Nat>) -> Type:
  @v: Nat -> {mem(v, w) == False{} : Bool} -> Ident(DV.deriv(e, v), E.QCst{qzero()})

# equation i of es depends on entry i of m, one entry per equation
def DepAll(es: List<&2, E.QExpr>, m: List<&2, Nat>) -> Type:
  match es m:
    case Nil{} Nil{}:
      Unit
    case Con{+e, t} Con{+v, u}:
      Depends(e, v) & DepAll(t, u)
    case Nil{} Con{v, u}:
      Empty
    case Con{e, t} Nil{}:
      Empty

# every equation of es at the positions s depends only on variables in w
def AllWithin(+es: List<&2, E.QExpr>, s: List<&2, Nat>, +w: List<&2, Nat>) -> Type:
  match s:
    case Nil{}:
      Unit
    case Con{+k, t}:
      DependsWithin(eqat(es, k), w) & AllWithin(es, t, w)

# s names distinct equations of es that depend only on variables in w, and
# w is shorter than s: structurally over-determined (no matching can give
# each of them its own variable)
def Overdet(+es: List<&2, E.QExpr>, +s: List<&2, Nat>, +w: List<&2, Nat>) -> Type:
  {band(distinct(s), band(below(s, neqs(es)), lt(len(w), len(s)))) == True{} : Bool} & AllWithin(es, s, w)

# every entry of xs is in ys
def sub(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{h, t}:
      band(mem(h, ys), sub(t, ys))

# a one-to-one matching of es with variables each depends on
def Matchable(+es: List<&2, E.QExpr>) -> Type:
  &m: List<&2, Nat> -> ({distinct(m) == True{} : Bool} & DepAll(es, m))

# m matches the equations es one to one with the variables vs, each
# equation with a variable it depends on, every variable of vs used (for
# solve_total: the system solved is square in the free variables)
def Perfect(+es: List<&2, E.QExpr>, +vs: List<&2, Nat>, +m: List<&2, Nat>) -> Type:
  {band(eq(len(vs), len(m)), band(distinct(m), sub(m, vs))) == True{} : Bool} & DepAll(es, m)

# Honest classifications (sk-13a), constraint by constraint
# ---------------------------------------------------------
# What the answer must be, stated for each constraint c given the classes
# of the constraints before it, as exclusive cases, so the sketch decides
# every class (honest_unique, by induction along the order):
# - Conflict iff c with the premises before it has a degree-0 refutation
#   (then with an irreducible support among them);
# - otherwise each equation of c is dropped iff it is a constant
#   combination of the solved equations before c and c's own earlier
#   equations not dropped;
# - otherwise Over iff c's remaining equations with the solved ones before
#   it contain a structurally over-determined set (by what the equations
#   depend on);
# - otherwise kept, and amber iff all of its equations are dropped and
#   every side condition of it is implied.
# The global facts (the kept system has no refutation; the solved
# equations are independent modulo constants; they have a matching)
# follow as theorems.

def presolved.go(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +k: Nat) -> List<&2, E.QExpr>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      solved.pick(band(lt(nth(own, k), c), band(bnot(mem(nth(own, k), red)), bnot(mem(k, ds)))), e, presolved.go(t, own, red, ds, c, 1n+k))

# the solved equations of the constraints before c
def presolved(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat) -> List<&2, E.QExpr>:
  presolved.go(SK.Sketch.eqs(sk), owners(sk), red, ds, c, 0n)

def own_rest.go(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +i: Nat, +k: Nat) -> List<&2, E.QExpr>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      solved.pick(band(lt(k, i), band(eq(nth(own, k), c), bnot(mem(k, d)))), e, own_rest.go(t, own, c, d, i, 1n+k))

# c's own equations at positions before i that are not in d
def own_rest(+sk: SK.Sketch, +c: Nat, +d: List<&2, Nat>, +i: Nat) -> List<&2, E.QExpr>:
  own_rest.go(SK.Sketch.eqs(sk), owners(sk), c, d, i, 0n)

# the premises before c: the equations and side conditions of the kept
# constraints before it, and the entities' side conditions
def pre_eqs(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat) -> List<&2, E.QExpr>:
  eqs_of(sk, kept_before(sk, red, c))

def pre_sides(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat) -> List<&2, SK.Side>:
  SK.cats(csides(sk, kept_before(sk, red, c)), esides(sk))

# the premises before c, and the negation of c's i-th side condition
def neg_pre(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat, +i: Nat) -> List<&2, SK.Side>:
  SK.cats(pre_sides(sk, red, c), [negate(side_at(csides(sk, [c]), i))])

# c with the premises before it has no degree-0 refutation
def NoRefute(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat) -> Type:
  @ls: List<&2, S.Q> -> @ms: List<&2, S.Q> -> @k: S.Q -> Refutes0(SK.cat(pre_eqs(sk, red, c), eqs_of(sk, [c])), SK.cats(pre_sides(sk, red, c), csides(sk, [c])), ls, ms, k) -> Empty

# c's i-th side condition is implied by the premises before it (they and
# its negation have a degree-0 refutation), or it is not
def Implied(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat, +i: Nat) -> Type:
  &ls: List<&2, S.Q> -> &ms: List<&2, S.Q> -> &k: S.Q -> Refutes0(pre_eqs(sk, red, c), neg_pre(sk, red, c, i), ls, ms, k)

def NotImplied(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat, +i: Nat) -> Type:
  @ls: List<&2, S.Q> -> @ms: List<&2, S.Q> -> @k: S.Q -> Refutes0(pre_eqs(sk, red, c), neg_pre(sk, red, c, i), ls, ms, k) -> Empty

# the equations equation i of c may be combined from: the solved ones
# before c and c's own earlier ones not in d
def basis(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +i: Nat) -> List<&2, E.QExpr>:
  SK.cat(presolved(sk, red, ds, c), own_rest(sk, c, d, i))

def Derivable(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +i: Nat) -> Type:
  &ls: List<&2, S.Q> -> Ident(eqat(SK.Sketch.eqs(sk), i), lin(ls, basis(sk, red, ds, c, d, i)))

def NotDerivable(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, +i: Nat) -> Type:
  @ls: List<&2, S.Q> -> Ident(eqat(SK.Sketch.eqs(sk), i), lin(ls, basis(sk, red, ds, c, d, i))) -> Empty

def drops_ok.mem(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, m: Bool, +k: Nat) -> Type:
  match m:
    case True{}:
      Derivable(sk, red, ds, c, d, k)
    case False{}:
      NotDerivable(sk, red, ds, c, d, k)

def drops_ok.at(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, b: Bool, +k: Nat) -> Type:
  match b:
    case True{}:
      drops_ok.mem(sk, red, ds, c, d, mem(k, d), k)
    case False{}:
      {mem(k, d) == False{} : Bool}

def drops_ok.go(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, own: List<&2, Nat>, +k: Nat) -> Type:
  match own:
    case Nil{}:
      Unit
    case Con{o, t}:
      drops_ok.at(sk, red, ds, c, d, eq(o, c), k) & drops_ok.go(sk, red, ds, c, d, t, 1n+k)

# d is exactly c's derivable equations: each equation of c is in d iff it
# is a constant combination of the solved equations before c and c's own
# earlier equations not in d; nothing else is in d
def DropsOk(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>) -> Type:
  {band(distinct(d), below(d, neqs(SK.Sketch.eqs(sk)))) == True{} : Bool} & drops_ok.go(sk, red, ds, c, d, owners(sk), 0n)

# the equations of an Over set: c's own not in d, or solved and earlier
def clean(+own: List<&2, Nat>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +d: List<&2, Nat>, +c: Nat, s: List<&2, Nat>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case Con{+k, t}:
      band(bor(band(eq(nth(own, k), c), bnot(mem(k, d))), band(lt(nth(own, k), c), band(bnot(mem(nth(own, k), red)), bnot(mem(k, ds))))), clean(own, red, ds, d, c, t))

# every equation of c is in d
def is_amberable(+sk: SK.Sketch, +c: Nat, +d: List<&2, Nat>) -> Bool:
  alldrop.go(owners(sk), d, c, 0n)

# kept with the dropped equations d: no refutation, d exactly the
# derivable ones, no over-determined set, and not amber (if every
# equation is dropped, some side condition is not implied)
def KeptOk(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>) -> Type:
  NoRefute(sk, red, c) & (DropsOk(sk, red, ds, c, d) & (Matchable(SK.cat(presolved(sk, red, ds, c), own_rest(sk, c, d, neqs(SK.Sketch.eqs(sk))))) & ({is_amberable(sk, c, d) == True{} : Bool} -> &i: Nat -> ({lt(i, slen(csides(sk, [c]))) == True{} : Bool} & NotImplied(sk, red, c, i)))))

# amber with the dropped equations d: no refutation, d exactly the
# derivable ones, all of c's equations, every side implied
def AmberOk(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>) -> Type:
  NoRefute(sk, red, c) & (DropsOk(sk, red, ds, c, d) & ({is_amberable(sk, c, d) == True{} : Bool} & (@i: Nat -> {lt(i, slen(csides(sk, [c]))) == True{} : Bool} -> Implied(sk, red, c, i))))

# Over with equation j in the over-determined set s over w: no
# refutation, and with c's derivable equations d set aside, s is made of
# c's other equations and earlier solved ones
def OverOk(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, +j: Nat, +s: List<&2, Nat>, +w: List<&2, Nat>) -> Type:
  NoRefute(sk, red, c) & (&d: List<&2, Nat> -> (DropsOk(sk, red, ds, c, d) & {band(eq(nth(owners(sk), j), c), band(mem(j, s), clean(owners(sk), red, ds, d, c, s))) == True{} : Bool} & Overdet(SK.Sketch.eqs(sk), s, w)))

# Conflict with support s: kept, driving constraints before c; c and s
# have a degree-0 refutation; without any one member of s they have none
def ConflictOk(+sk: SK.Sketch, +red: List<&2, Nat>, +c: Nat, +s: List<&2, Nat>) -> Type:
  {band(distinct(s), band(below(s, c), band(all_driving(sk, s), none_in(s, red)))) == True{} : Bool} & ((&ls: List<&2, S.Q> -> &ms: List<&2, S.Q> -> &k: S.Q -> Refutes0(eqs_of(sk, Con{c, s}), SK.cats(csides(sk, Con{c, s}), esides(sk)), ls, ms, k)) & (@m: Nat -> {mem(m, s) == True{} : Bool} -> @ls: List<&2, S.Q> -> @ms: List<&2, S.Q> -> @k: S.Q -> Refutes0(eqs_of(sk, Con{c, unmark(m, s)}), SK.cats(csides(sk, Con{c, unmark(m, s)}), esides(sk)), ls, ms, k) -> Empty))

def Fate.driving(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, k: Class) -> Type:
  match k:
    case Kept{+dc}:
      KeptOk(sk, red, ds, c, drops(dc))
    case Amber{+dc, rs}:
      AmberOk(sk, red, ds, c, drops(dc))
    case Over{+j, +s, +w}:
      OverOk(sk, red, ds, c, j, s, w)
    case Conflict{+s}:
      ConflictOk(sk, red, c, s)

# a driven constraint means nothing: kept, nothing dropped
def Fate.driven(k: Class) -> Type:
  match k:
    case Kept{dc}:
      {drops(dc) == Nil{} : List<&2, Nat>}
    case Amber{dc, rs}:
      Empty
    case Over{j, s, w}:
      Empty
    case Conflict{s}:
      Empty

def Fate.pick(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, b: Bool, +k: Class) -> Type:
  match b:
    case True{}:
      Fate.driven(k)
    case False{}:
      Fate.driving(sk, red, ds, c, k)

# the constraint at position c has its honest class, given the others'
def Fate(+sk: SK.Sketch, +cls: List<&2, Class>, +c: Nat) -> Type:
  Fate.pick(sk, reds(cls), dropped(cls), c, driven(sk, c), class_at(cls, c))

def Honest.go(+sk: SK.Sketch, +cls: List<&2, Class>, n: Nat, +c: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+m:
      Fate(sk, cls, c) & Honest.go(sk, cls, m, 1n+c)

# an honest classification of the sketch: one class per constraint, each
# the honest one given the classes before it
def Honest(+sk: SK.Sketch, +cls: List<&2, Class>) -> Type:
  {clsn(cls) == ncons(sk) : Nat} & Honest.go(sk, cls, ncons(sk), 0n)

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
