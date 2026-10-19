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
import ./field.bend as O
import ./mat.bend as M
import ./knum.bend as N
import ./sketch.bend as SK
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

# Dropped equations (sk-13a, DESIGN §8.11, Q24)
# ---------------------------------------------
# The solver may drop an equation of a kept constraint from the system it
# solves, when the equations it does solve imply it. The constraint is not
# made driven: it stays in the sketch's meaning, so the certified geometry
# satisfies it (solve_exists), and its side conditions are checked like
# every other. solve_drop says the dropped equations follow from the
# solved ones in the box. A constraint all of whose equations are dropped
# is redundant (the page shows it amber); one with only some dropped just
# holds, and nothing in it can be removed.

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

# Certificates
# ------------

# q times the sketch's equation i
type Mul is Data:
  Mul{i: Nat, q: E.QExpr}

# a certificate for an equation g: h g = q_1 g_i1 + ... + q_n g_in + k, an
# identity of polynomials (the g_i the sketch's equations). Data only:
# the verdict checks a dropped equation's (k = 0, h nonzero over the box)
# and the laws solve_drop and solve_conflict say what passing buys, so
# nothing here is trusted beyond its shape.
type Cert is Data:
  Cert{h: E.QExpr, qs: List<&2, Mul>, k: S.Q}

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

# Red constraints
# ---------------

# every equation of s is c's own, or solved (its constraint not red, and
# it not dropped)
def clean(+own: List<&2, Nat>, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, s: List<&2, Nat>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case Con{+k, t}:
      band(bor(eq(nth(own, k), c), band(bnot(mem(nth(own, k), red)), bnot(mem(k, ds)))), clean(own, red, ds, c, t))

# why the constraint at a position is red
type Why is Data:
  # its equation j lies in the over-determined set s (whose variables are
  # among w), made of its own and solved equations
  Over{j: Nat, s: List<&2, Nat>, w: List<&2, Nat>}
  # its equation j cannot hold together with the solved equations: c is
  # a certificate with k nonzero (solve_conflict)
  Conflict{j: Nat, c: Cert}
  # its i-th side condition mentions no variable and fails (a distance of
  # -5)
  Side{i: Nat}

# e mentions no variable
def novar(e: E.QExpr) -> Bool:
  match e:
    case E.QVar{v}:
      False{}
    case E.QCst{q}:
      True{}
    case E.QAdd{a, b}:
      band(novar(a), novar(b))
    case E.QSub{a, b}:
      band(novar(a), novar(b))
    case E.QMul{a, b}:
      band(novar(a), novar(b))
    case E.QNeg{a}:
      novar(a)

def islt(c: Cmp) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      False{}
    case GT{}:
      False{}

def qzero() -> S.Q:
  S.Q{S.Z0{}, S.XH{}}

# a side condition that mentions no variable and is false (over the
# rationals, so in every ordered field)
def fails(s: SK.Side) -> Bool:
  match s:
    case SK.Gt0{+e}:
      band(novar(e), bnot(islt(S.Q.cmp(qzero(), E.qeval([], e)))))
    case SK.Ge0{+e}:
      band(novar(e), islt(S.Q.cmp(E.qeval([], e), qzero())))

# the i-th of ss fails
def fails_at(ss: List<&2, SK.Side>, i: Nat) -> Bool:
  match ss i:
    case Nil{} i:
      False{}
    case Con{s, t} 0n:
      fails(s)
    case Con{s, t} 1n+m:
      fails_at(t, m)

def sides.at(+es: List<&2, SK.Ent>, cs: List<&2, SK.Rec>, c: Nat) -> List<&2, SK.Side>:
  match cs c:
    case Nil{} c:
      Nil{}
    case Con{SK.Rec{id, dr, k}, t} 0n:
      SK.Constraint.sides(es, k)
    case Con{h, t} 1n+m:
      sides.at(es, t, m)

# the side conditions of the constraint at position c
def sides_of(sk: SK.Sketch, c: Nat) -> List<&2, SK.Side>:
  match sk:
    case SK.Sketch{vs, +es, cs}:
      sides.at(es, cs, c)

# the reason y explains the constraint at position c
def why_ok(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, +c: Nat, y: Why) -> Bool:
  match y:
    case Over{+j, +s, +w}:
      band(eq(nth(owners(sk), j), c), band(mem(j, s), band(overdet(SK.Sketch.eqs(sk), s, w), clean(owners(sk), red, ds, c, s))))
    case Conflict{j, cert}:
      eq(nth(owners(sk), j), c)
    case Side{i}:
      fails_at(sides_of(sk, c), i)

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

# no constraint is red twice, and each is explained
def explained(+sk: SK.Sketch, +red: List<&2, Nat>, +ds: List<&2, Nat>, why: List<&2, Why>) -> Bool:
  band(distinct(red), explained.go(sk, red, ds, red, why))

def conflicts.of(c: Nat, y: Why, rest: List<&2, Nat>) -> List<&2, Nat>:
  match y:
    case Over{j, s, w}:
      rest
    case Conflict{j, cert}:
      Con{c, rest}
    case Side{i}:
      Con{c, rest}

# the red constraints whose reason is a conflict (Conflict or Side)
def conflicts(red: List<&2, Nat>, why: List<&2, Why>) -> List<&2, Nat>:
  match red why:
    case Con{c, rt} Con{y, yt}:
      conflicts.of(c, y, conflicts(rt, yt))
    case Nil{} why:
      Nil{}
    case Con{c, rt} Nil{}:
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
# some equation's (so the system is square, and its Jacobian is not
# singular for want of structure)
def perfect(+es: List<&2, E.QExpr>, +vs: List<&2, Nat>, +m: List<&2, Nat>) -> Bool:
  band(eq(len(vs), len(m)), band(distinct(m), band(sub(m, vs), uses_all(es, m))))

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

# a side condition holds strictly at x: e > 0; a variable-free e >= 0 may
# also hold with equality (balls cannot certify a variable expression at
# exactly 0)
def Strict.ge(~F: O.OField, b: Bool, +x: M.Vec(~F), +e: E.QExpr) -> Data:
  match b:
    case True{}:
      O.le(~F, O.zero(F), O.eval(~F, x, e))
    case False{}:
      O.lt(F, O.zero(F), O.eval(~F, x, e))

def Strict(~F: O.OField, +x: M.Vec(~F), ss: List<&2, SK.Side>) -> Data:
  match ss:
    case Nil{}:
      Unit
    case Con{SK.Gt0{+e}, t}:
      M.Both(O.lt(F, O.zero(F), O.eval(~F, x, e)), Strict(~F, x, t))
    case Con{SK.Ge0{+e}, t}:
      M.Both(Strict.ge(~F, BX.QExpr.within(e, 0n), x, e), Strict(~F, x, t))
