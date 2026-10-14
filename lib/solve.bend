# bend-cad: the solver (DESIGN §10), verified. solve(sk, g0) takes a
# sketch and a drawing (a dyadic value per variable) and answers with a
# box, a plan, the variables it pinned (free degrees of freedom held at
# the drawing's values) and the constraints it flagged red with their
# reasons.
#
# search does the work (lib/struct.bend: red constraints and their
# witnesses, pins, blocks; lib/numer.bend: Newton, Y and radii at
# precisions 64 .. 512). seal then recomputes the verdict from the answer
# alone: every pin held at its drawn value with radius 0 and every red
# constraint explained (spec/solve.bend), the sketch with
# them made driven well formed (lib/wfdec.bend), covered by the box, its
# plan and its side conditions checked (lib/plan.bend). So the laws
# (solve_exists, solve_unique, solve_red, solve_pins) need nothing from
# search: they follow from the verdict and the sk-06 laws.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/real.bend as CR
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./kinst.bend as KI
import ./plan.bend as PL
import ./planpf.bend as PP
import ./struct.bend as ST
import ./numer.bend as NU
import ./wfdec.bend as WF

# The answer
# ----------

type Out is Data:
  Out{ok: Bool, red: List<&2, Nat>, why: List<&2, SV.Why>, pins: List<&2, Nat>, gc: List<&2, S.D>, gr: List<&2, S.D>, plan: PL.Plan<KI.dnum()>}

def Out.ok(x: Out) -> Bool:
  match x:
    case Out{ok, red, why, pins, gc, gr, plan}:
      ok

def Out.red(x: Out) -> List<&2, Nat>:
  match x:
    case Out{ok, red, why, pins, gc, gr, plan}:
      red

def Out.why(x: Out) -> List<&2, SV.Why>:
  match x:
    case Out{ok, red, why, pins, gc, gr, plan}:
      why

def Out.pins(x: Out) -> List<&2, Nat>:
  match x:
    case Out{ok, red, why, pins, gc, gr, plan}:
      pins

def Out.gc(x: Out) -> List<&2, S.D>:
  match x:
    case Out{ok, red, why, pins, gc, gr, plan}:
      gc

def Out.gr(x: Out) -> List<&2, S.D>:
  match x:
    case Out{ok, red, why, pins, gc, gr, plan}:
      gr

def Out.plan(x: Out) -> PL.Plan<KI.dnum()>:
  match x:
    case Out{ok, red, why, pins, gc, gr, plan}:
      plan

# The search
# ----------

def vlen(vs: List<&2, SK.VKind>) -> Nat:
  match vs:
    case Nil{}:
      0n
    case Con{v, t}:
      1n+vlen(t)

# the number of variables
def nvars(sk: SK.Sketch) -> Nat:
  match sk:
    case SK.Sketch{vs, es, cs}:
      vlen(vs)

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

# the equations (indices from k) owned by constraint c
def owned.go(b: Bool, +k: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      Con{k, rest}
    case False{}:
      rest

def owned(own: List<&2, Nat>, +c: Nat, +k: Nat) -> List<&2, Nat>:
  match own:
    case Nil{}:
      Nil{}
    case Con{o, t}:
      owned.go(SV.eq(o, c), k, owned(t, c, 1n+k))

# each constraint's equations, in order (constraints from c, n of them)
def groups(n: Nat, +own: List<&2, Nat>, +c: Nat) -> List<&2, List<&2, Nat>>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{owned(own, c, 0n), groups(m, own, 1n+c)}

# each red constraint, and why
def reds(+own: List<&2, Nat>, rs: List<&2, ST.Red>) -> List<&2, Nat>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{ST.Red{j, s, w}, t}:
      Con{SV.nth(own, j), reds(own, t)}

def whys(rs: List<&2, ST.Red>) -> List<&2, SV.Why>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{ST.Red{j, s, w}, t}:
      Con{SV.Why{j, s, w}, whys(t)}

# the first precision that gives a plan. Every failure moves on to the
# next precision, a block whose Newton did not settle included: at a low
# precision an ill-conditioned block can fail to settle or lose a pivot
# that a higher one keeps (solve_complete needs this)
def ploop(ps: List<&2, Nat>, cur: NU.PR, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel, +g0: List<&2, S.D>) -> NU.PR:
  match ps cur:
    case Nil{} cur:
      cur
    case Con{p, t} NU.POk{x}:
      NU.POk{x}
    case Con{+p, t} NU.PStop{}:
      ploop(t, NU.plan(es, nv, skel, g0, p), es, nv, skel, g0)
    case Con{+p, t} NU.PRetry{}:
      ploop(t, NU.plan(es, nv, skel, g0, p), es, nv, skel, g0)

# the first b precisions of 64, 96, 128, 192, 256, ... (doubling every
# two steps)
def precs(b: Nat, +p: Nat, +q: Nat) -> List<&2, Nat>:
  match b:
    case 0n:
      Nil{}
    case 1n+c:
      Con{p, precs(c, q, Nat.add(p, p))}

def precisions(b: Nat) -> List<&2, Nat>:
  precs(b, 64n, 96n)

# the default budget: 64 .. 512 bits
def budget() -> Nat:
  7n

def noplan() -> PL.Plan<KI.dnum()>:
  PL.Plan{Nil{}, Nil{}, 0n, Nil{}}

def pr.ok(m: NU.PR) -> Bool:
  match m:
    case NU.POk{x}:
      True{}
    case NU.PRetry{}:
      False{}
    case NU.PStop{}:
      False{}

def pr.gc(m: NU.PR) -> List<&2, S.D>:
  match m:
    case NU.POk{NU.NP{plan, gc, gr}}:
      gc
    case NU.PRetry{}:
      Nil{}
    case NU.PStop{}:
      Nil{}

def pr.gr(m: NU.PR) -> List<&2, S.D>:
  match m:
    case NU.POk{NU.NP{plan, gc, gr}}:
      gr
    case NU.PRetry{}:
      Nil{}
    case NU.PStop{}:
      Nil{}

def pr.plan(m: NU.PR) -> PL.Plan<KI.dnum()>:
  match m:
    case NU.POk{NU.NP{plan, gc, gr}}:
      plan
    case NU.PRetry{}:
      noplan()
    case NU.PStop{}:
      noplan()

# the answer is built through projections, so that its red constraints
# and pins are visibly red_of(sk) and pins_of(sk) whatever the numbers do
def found(+red: List<&2, Nat>, +why: List<&2, SV.Why>, +pins: List<&2, Nat>, +m: NU.PR) -> Out:
  Out{pr.ok(m), red, why, pins, pr.gc(m), pr.gr(m), pr.plan(m)}

def ntake(n: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match n xs:
    case 0n xs:
      Nil{}
    case 1n+m Nil{}:
      Nil{}
    case 1n+m Con{h, t}:
      Con{h, ntake(m, t)}

# the pins: the first np variables in block order
def skel.pins(s: ST.Skel) -> List<&2, Nat>:
  match s:
    case ST.Skel{vp, ep, np, bs, red}:
      ntake(np, vp)

# The structure depends on the sketch alone
# -----------------------------------------
# Red constraints first (constraints matched as units, in order: each red
# one's witness uses only kept constraints and itself), then the sketch
# less them: its pins and blocks.

def rs_of(+sk: SK.Sketch) -> List<&2, ST.Red>:
  ST.reds(SK.Sketch.eqs(sk), nvars(sk), groups(ncons(sk), SV.owners(sk), 0n))

def red_of(+sk: SK.Sketch) -> List<&2, Nat>:
  reds(SV.owners(sk), rs_of(sk))

def why_of(+sk: SK.Sketch) -> List<&2, SV.Why>:
  whys(rs_of(sk))

# the sketch's exact system less its red constraints
def kept(+sk: SK.Sketch) -> List<&2, E.QExpr>:
  SK.Sketch.eqs(SV.mark(red_of(sk), sk))

def skel_of(+sk: SK.Sketch) -> ST.Skel:
  ST.structure(kept(sk), nvars(sk))

def pins_of(+sk: SK.Sketch) -> List<&2, Nat>:
  skel.pins(skel_of(sk))

# The search, with a budget of b precisions
def search_b(+sk: SK.Sketch, +g0: List<&2, S.D>, +b: Nat) -> Out:
  found(red_of(sk), why_of(sk), pins_of(sk), ploop(precisions(b), NU.PRetry{}, kept(sk), nvars(sk), skel_of(sk), g0))

# For the UI: equation j is the k-th equation of its constraint (a red
# constraint shows all red; expanded, it names the equation of its Why)
def eqk.go(b: Bool, rest: Nat) -> Nat:
  match b:
    case True{}:
      1n+rest
    case False{}:
      rest

# how many of the first j equations share owner c
def eqk(own: List<&2, Nat>, +c: Nat, j: Nat) -> Nat:
  match own j:
    case Nil{} j:
      0n
    case Con{o, t} 0n:
      0n
    case Con{o, t} 1n+i:
      eqk.go(SV.eq(o, c), eqk(t, c, i))

def eqlabel(+sk: SK.Sketch, +j: Nat) -> Nat:
  eqk(SV.owners(sk), SV.nth(SV.owners(sk), j), j)

# The verdict
# -----------

# what the laws need, read off the answer alone
def final(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: Out) -> Bool:
  KA.band(SV.held(Out.pins(x), g0, Out.gc(x), Out.gr(x)),
  KA.band(SV.explained(sk, Out.red(x), Out.why(x)),
  KA.band(WF.wf_dec(SV.mark(Out.red(x), sk)),
  KA.band(BX.Sketch.within(SV.mark(Out.red(x), sk), List.length(&2, N.NC(KI.dnum()), Out.gc(x))),
  KA.band(PL.check(~KI.dnum(), SK.Sketch.eqs(SV.mark(Out.red(x), sk)), Out.gc(x), Out.gr(x), Out.plan(x)),
  PL.check_sides(~KI.dnum(), SK.Sketch.sides(SV.mark(Out.red(x), sk)), Out.gc(x), Out.gr(x)))))))

def seal(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: Out) -> Out:
  Out{final(sk, g0, x), Out.red(x), Out.why(x), Out.pins(x), Out.gc(x), Out.gr(x), Out.plan(x)}

# The solver, with a budget of b precisions, and with the default budget
def solve_b(+sk: SK.Sketch, +g0: List<&2, S.D>, +b: Nat) -> Out:
  seal(sk, g0, search_b(sk, g0, b))

def solve(+sk: SK.Sketch, +g0: List<&2, S.D>) -> Out:
  solve_b(sk, g0, budget())
