# bend-cad: the solver (DESIGN §10), verified. solve(sk, g0) takes a
# sketch and a drawing (a dyadic value per variable) and answers with a
# box, a plan, the variables it pinned (free degrees of freedom held at
# the drawing's values) and a class for each constraint (spec/solve.bend:
# Kept, Amber, Over, Conflict).
#
# search does the work (lib/struct.bend: red constraints and their
# witnesses, pins, blocks; lib/numer.bend: Newton, Y and radii at
# precisions 64 .. 512). seal then recomputes the verdict from the answer
# alone: every pin held at its drawn value with radius 0, the sketch with
# the red constraints made driven well formed (lib/wfdec.bend), covered by
# the box, its plan and its side conditions checked (lib/plan.bend). So
# the verdict laws (solve_exists, solve_unique, solve_pins) need nothing
# from search: they follow from the verdict and the sk-06 laws.
#
# Until sk-13a's stage lands (PLAN-sk13a.md S4) the classes come from
# sk-09's red stage: Over (with its syntactic witness, lib/why.bend) at
# each red constraint, Kept with nothing dropped elsewhere.

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
import ./why.bend as WY
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
  Out{ok: Bool, cls: List<&2, SV.Class>, pins: List<&2, Nat>, gc: List<&2, S.D>, gr: List<&2, S.D>, plan: PL.Plan<KI.dnum()>}

def Out.ok(x: Out) -> Bool:
  match x:
    case Out{ok, cls, pins, gc, gr, plan}:
      ok

def Out.cls(x: Out) -> List<&2, SV.Class>:
  match x:
    case Out{ok, cls, pins, gc, gr, plan}:
      cls

def Out.pins(x: Out) -> List<&2, Nat>:
  match x:
    case Out{ok, cls, pins, gc, gr, plan}:
      pins

def Out.gc(x: Out) -> List<&2, S.D>:
  match x:
    case Out{ok, cls, pins, gc, gr, plan}:
      gc

def Out.gr(x: Out) -> List<&2, S.D>:
  match x:
    case Out{ok, cls, pins, gc, gr, plan}:
      gr

def Out.plan(x: Out) -> PL.Plan<KI.dnum()>:
  match x:
    case Out{ok, cls, pins, gc, gr, plan}:
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

# Red constraints
# ---------------
# The constraints are walked in order, as Sketch.eqs and SV.owners walk
# them: constraint i (counting driven ones) owns the equations k .. k + n -
# 1 of the sketch's exact system. Its equations are matched as a unit
# (lib/struct.bend: grp); if one fails, the matching goes back to what it
# was and i is red, with that equation's witness. vm: the matching (each
# variable's equation); red, why: the red constraints so far and why,
# newest first.

type CS is Data:
  CS{vm: List<&2, Maybe<&2, Nat>>, red: List<&2, Nat>, why: List<&2, WY.Why>}

def CS.vm(st: CS) -> List<&2, Maybe<&2, Nat>>:
  match st:
    case CS{vm, red, why}:
      vm

def CS.red(st: CS) -> List<&2, Nat>:
  match st:
    case CS{vm, red, why}:
      red

def CS.why(st: CS) -> List<&2, WY.Why>:
  match st:
    case CS{vm, red, why}:
      why

def cfin(+i: Nat, g: ST.GS, st: CS) -> CS:
  match g st:
    case ST.GOk{vm2} CS{vm, red, why}:
      CS{vm2, red, why}
    case ST.GFail{ST.Red{j, s, w}} CS{vm, red, why}:
      CS{vm, Con{i, red}, Con{WY.Why{j, s, w}, why}}

# the constraints cs from position i, their equations from k
def kuhnc(cs: List<&2, SK.Rec>, +es: List<&2, SK.Ent>, +i: Nat, +k: Nat, +adj: List<&2, List<&2, Nat>>, +f: Nat, +st: CS) -> CS:
  match cs:
    case Nil{}:
      st
    case Con{SK.Rec{id, True{}, kd}, t}:
      kuhnc(t, es, 1n+i, k, adj, f, st)
    case Con{SK.Rec{id, False{}, +kd}, t}:
      +n = SV.neqs(SK.Constraint.eqs(es, kd))
      kuhnc(t, es, 1n+i, Nat.add(k, n), adj, f, cfin(i, ST.grp(n, k, adj, f, ST.GOk{CS.vm(st)}), st))

# the precisions of level l: of 64, 96, 128, 192, 256, ... (doubling
# every two steps), seven from the l-th. Level 0 is 64 .. 512 bits; a higher
# level starts higher and never tries the coarse ones (solve_complete
# needs that: a coarse precision can lose the drawing's detail and
# certify a neighbouring solution)
def precs(n: Nat, +p: Nat, +q: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+c:
      Con{p, precs(c, q, Nat.add(p, p))}

def precs.from(l: Nat, +w: Nat, +p: Nat, +q: Nat) -> List<&2, Nat>:
  match l:
    case 0n:
      precs(w, p, q)
    case 1n+m:
      precs.from(m, w, q, Nat.add(p, p))

# w precisions from the l-th
def precisions(+l: Nat, +w: Nat) -> List<&2, Nat>:
  precs.from(l, w, 64n, 96n)

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

# the answer is built through projections, so that its classes and pins
# are visibly cls_of(sk) and pins_of(sk) whatever the numbers do
def found(+cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +m: NU.PR) -> Out:
  Out{pr.ok(m), cls, pins, pr.gc(m), pr.gr(m), pr.plan(m)}

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

# The verdict
# -----------

# what the laws need, read off the answer alone
def final(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: Out) -> Bool:
  KA.band(SV.held(Out.pins(x), g0, Out.gc(x), Out.gr(x)),
  KA.band(WF.wf_dec(SV.mark(SV.reds(Out.cls(x)), sk)),
  KA.band(BX.Sketch.within(SV.mark(SV.reds(Out.cls(x)), sk), List.length(&2, N.NC(KI.dnum()), Out.gc(x))),
  KA.band(PL.check(~KI.dnum(), SK.Sketch.eqs(SV.mark(SV.reds(Out.cls(x)), sk)), Out.gc(x), Out.gr(x), Out.plan(x)),
  PL.check_sides(~KI.dnum(), SK.Sketch.sides(SV.mark(SV.reds(Out.cls(x)), sk)), Out.gc(x), Out.gr(x))))))

# The precision loop
# ------------------

# the answer at one precision passes the whole verdict (matching on the
# plan first keeps the verdict folded while the plan is unknown, as it is
# wherever a law mentions solve symbolically)
def accept(m: NU.PR, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>) -> Bool:
  match m:
    case NU.POk{+x}:
      final(sk, g0, found(cls, pins, NU.POk{x}))
    case NU.PRetry{}:
      False{}
    case NU.PStop{}:
      False{}

# the first precision whose answer passes the whole verdict (side
# conditions included: a box too wide for one is retried higher). Every
# failure moves on to the next precision, a block whose Newton did not
# settle included: at a low precision an ill-conditioned block can fail
# to settle or lose a pivot that a higher one keeps
def ploop(ps: List<&2, Nat>, ok: Bool, cur: NU.PR, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel) -> NU.PR:
  match ps ok:
    case Nil{} ok:
      cur
    case Con{p, t} True{}:
      cur
    case Con{+p, t} False{}:
      +nx = NU.plan(es, nv, skel, g0, p)
      ploop(t, accept(nx, sk, g0, cls, pins), nx, sk, g0, cls, pins, es, nv, skel)

# The structure depends on the sketch alone
# -----------------------------------------
# Red constraints first (constraints matched as units, in order: each red
# one's witness uses only kept constraints and itself), then the sketch
# less them: its pins and blocks.

def run(sk: SK.Sketch, +nv: Nat) -> CS:
  match sk:
    case SK.Sketch{vs, +es, +cs}:
      kuhnc(cs, es, 0n, 0n, ST.adj(SK.Sketch.eqs.go(es, cs)), 1n+nv, CS{ST.nones(nv), Nil{}, Nil{}})

def rs_of(+sk: SK.Sketch) -> CS:
  run(sk, nvars(sk))

def red_of(+sk: SK.Sketch) -> List<&2, Nat>:
  CS.red(rs_of(sk))

def why_of(+sk: SK.Sketch) -> List<&2, WY.Why>:
  CS.why(rs_of(sk))

# the sketch's exact system less its red constraints
def kept(+sk: SK.Sketch) -> List<&2, E.QExpr>:
  SK.Sketch.eqs(SV.mark(red_of(sk), sk))

# the kept equations in the sketch's numbering: those the red stage
# matched, in order
def good_of(+sk: SK.Sketch) -> List<&2, Nat>:
  ST.inter(ST.iota(ST.len.q(SK.Sketch.eqs(sk)), 0n), ST.somes(CS.vm(rs_of(sk))))

def skel.from(+sk: SK.Sketch, +good: List<&2, Nat>) -> ST.Skel:
  ST.renum(ST.skel.kept(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), nvars(sk), good), good)

# the structure of the kept system, worked out in the sketch's numbering
# (the red stage's matching is there) and renumbered
def skel_of(+sk: SK.Sketch) -> ST.Skel:
  skel.from(sk, good_of(sk))

# the pins: the earliest variables the kept system can leave over (with
# them it is square: the red stage's matching saturates its equations, and
# the variable side's greedy matching is then maximum)
def pins_of(+sk: SK.Sketch) -> List<&2, Nat>:
  skel.pins(skel_of(sk))

# The classes (until the sk-13a stage, PLAN-sk13a.md S4): Over with its
# witness at each red constraint, Kept with nothing dropped elsewhere

# the witness red's member c has (red and why are aligned)
def whyat.go(b: Bool, +y: WY.Why, rest: WY.Why) -> WY.Why:
  match b:
    case True{}:
      y
    case False{}:
      rest

def whyat(red: List<&2, Nat>, why: List<&2, WY.Why>, +c: Nat) -> WY.Why:
  match red why:
    case Nil{} why:
      WY.Why{0n, Nil{}, Nil{}}
    case Con{r, rt} Nil{}:
      WY.Why{0n, Nil{}, Nil{}}
    case Con{r, rt} Con{+y, yt}:
      whyat.go(SV.eq(r, c), y, whyat(rt, yt, c))

def over_of(y: WY.Why) -> SV.Class:
  match y:
    case WY.Why{j, s, w}:
      SV.Over{j, s, w}

def cls_at(b: Bool, +red: List<&2, Nat>, +why: List<&2, WY.Why>, +c: Nat) -> SV.Class:
  match b:
    case True{}:
      over_of(whyat(red, why, c))
    case False{}:
      SV.Kept{Nil{}}

# the classes of positions i .. i + n - 1
def cls.go(n: Nat, +red: List<&2, Nat>, +why: List<&2, WY.Why>, +i: Nat) -> List<&2, SV.Class>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{cls_at(SV.mem(i, red), red, why, i), cls.go(m, red, why, 1n+i)}

def cls_mk(+red: List<&2, Nat>, +why: List<&2, WY.Why>, +n: Nat) -> List<&2, SV.Class>:
  cls.go(n, red, why, 0n)

# the classes, from the sketch alone
def cls_of(+sk: SK.Sketch) -> List<&2, SV.Class>:
  cls_mk(red_of(sk), why_of(sk), SV.ncons(sk))

# the loop from its first precision's answer (starting it with a literal
# "not yet" would let the checker unfold the whole verdict symbolically
# wherever a law mentions solve, ~40 s per file)
def ploop.start(ps: List<&2, Nat>, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel) -> NU.PR:
  match ps:
    case Nil{}:
      NU.PRetry{}
    case Con{+p, t}:
      +nx = NU.plan(es, nv, skel, g0, p)
      ploop(t, accept(nx, sk, g0, cls, pins), nx, sk, g0, cls, pins, es, nv, skel)

# The search over w precisions from level l
def search_lw(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +w: Nat) -> Out:
  found(cls_of(sk), pins_of(sk), ploop.start(precisions(l, w), sk, g0, cls_of(sk), pins_of(sk), kept(sk), nvars(sk), skel_of(sk)))

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

def seal(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: Out) -> Out:
  Out{final(sk, g0, x), Out.cls(x), Out.pins(x), Out.gc(x), Out.gr(x), Out.plan(x)}

# The solver over w precisions from level l; at level l (seven precisions
# from the l-th: "try harder"); and at level 0 (64 .. 512 bits)
def solve_lw(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +w: Nat) -> Out:
  seal(sk, g0, search_lw(sk, g0, l, w))

def solve_l(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat) -> Out:
  solve_lw(sk, g0, l, 7n)

def solve(+sk: SK.Sketch, +g0: List<&2, S.D>) -> Out:
  solve_l(sk, g0, 0n)
