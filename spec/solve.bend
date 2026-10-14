# bend-cad spec: what the solver's answers mean (DESIGN §10.2). Trusted;
# DRAFT FOR REVIEW with the solve_* laws in ROADMAP.bend.
#
# The solver may flag constraints red (named by their position in the
# sketch's list of constraints, counting driven ones too, so that a
# repeated id cannot drop a second constraint): it drops them from the
# exact system by making them driven (Rec's driven flag; a driven constraint
# contributes no equations, sk-03), and it certifies the rest. Each red
# constraint must be explained: it owns an equation j of the sketch's exact
# system (Sketch.eqs) that lies in a set S of the system's equations which
# use fewer variables than S has equations (all of them in W, and W is
# shorter than S). Such a set over-determines its variables: its
# Jacobian has rank at most |W| < |S| everywhere, so it can never be part
# of a certified (square, regular) system, and some equation of it has to
# go. This is a fact about the equations alone; it does not depend on how
# the solver matched or pinned anything. Moreover S may use, besides the
# red constraint's own equations, only equations of constraints that stay
# (are not red): so restoring any one red constraint alone over-determines
# what was kept, and no red flag is spare. (Without this, an
# over-determined set padded with unrelated equations would "explain"
# dropping anything; found by the independent audit, 2026-10-14.)
#
# The solver may also pin variables: hold free degrees of freedom at the
# drawing's values (radius 0). held says each pin is exactly at its drawn
# value with radius 0, so a pin never moves anything the user drew.

import Base
import ./num.bend as S
import ./ring.bend as E
import ./sketch.bend as SK

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

# every equation of s is owned by c or by a constraint not in red
def clean(+own: List<&2, Nat>, +red: List<&2, Nat>, +c: Nat, s: List<&2, Nat>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case Con{+k, t}:
      band(bor(eq(nth(own, k), c), bnot(mem(nth(own, k), red))), clean(own, red, c, t))

# why the constraint at a position is red: equation j, which it owns,
# lies in the over-determined set s (whose variables are among w)
type Why is Data:
  Why{j: Nat, s: List<&2, Nat>, w: List<&2, Nat>}

# each red constraint (rs, in order) is explained by the matching Why,
# red being the whole list
def explained.go(+sk: SK.Sketch, +red: List<&2, Nat>, rs: List<&2, Nat>, why: List<&2, Why>) -> Bool:
  match rs why:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, yt}:
      False{}
    case Con{c, rt} Nil{}:
      False{}
    case Con{+c, rt} Con{Why{+j, +s, +w}, yt}:
      band(eq(nth(owners(sk), j), c), band(mem(j, s), band(overdet(SK.Sketch.eqs(sk), s, w), band(clean(owners(sk), red, c, s), explained.go(sk, red, rt, yt)))))

def explained(+sk: SK.Sketch, +red: List<&2, Nat>, why: List<&2, Why>) -> Bool:
  explained.go(sk, red, red, why)

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
