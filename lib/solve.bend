# bend-cad: the solver (DESIGN §10), verified. solve(sk, g0) takes a
# sketch and a drawing (a dyadic value per variable) and answers with a
# box, a plan, the variables it pinned (free degrees of freedom held at
# the drawing's values) and a class for each constraint (spec/solve.bend:
# Kept, Amber, Over, Conflict).
#
# The classes are the pass's (lib/dpass.bend: classes2, the single pass of
# PLAN-sk13a S4 with sk-13b's direction layer), and so is the structure:
# the system solved (the sketch's equations whose constraint is not red
# and that are not dropped), its pins and its blocks (lib/dpass.bend:
# pins2, skel2). The search does the numbers (lib/numer.bend: Newton, Y
# and radii at precisions 64 .. 512) over the system solved, and judges
# each answer by the verdict (final), which reads the answer alone: every
# segment in the nd of a drop of a Kept or Amber constraint long over the
# box (ndok), every pin held at its drawn value with radius 0, the sketch
# with the red constraints made driven well formed (lib/wfdec.bend),
# covered by the box, the plan checked over the system solved (its orders
# every variable once, the pins first, and as many equations as that
# system has), the side conditions of the constraints neither red nor
# amber checked over the box (lib/plan.bend), and the amber side
# conditions certified by their refutations (lib/verdict.bend). The
# answer's ok is the verdict the search reached on it, computed once
# (lib/dsolvepf.bend: verdict2 proves it is final of that answer). So the
# verdict laws (solve_exists, solve_unique, solve_pins, solve_regular) need
# nothing else from search: they follow from the verdict and the sk-06
# laws.

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
import ./pass.bend as PA
import ./dpass.bend as DPS
import ../spec/dir.bend as DR
import ./verdict.bend as VD
import ./cert.bend as CK

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

# the number of variables (the pass's count)
def nvars(+sk: SK.Sketch) -> Nat:
  PA.nvars(sk)

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

# an answer at one precision, for the verdict to judge (which never reads
# its ok). Answers are built through projections, so that their classes
# and pins are visibly cls_of(sk) and pins_of(sk) whatever the numbers do
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

# two lists of numbers are the same
def nl_eq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{b, t}:
      False{}
    case Con{a, s} Nil{}:
      False{}
    case Con{a, s} Con{b, t}:
      SV.band(SV.eq(a, b), nl_eq(s, t))

# the plan's orders: a box coordinate and a place in the variable order
# for each of the nv variables, every variable once, the np pins first,
# and a place in the equation order for each of the nq equations
def shape(+nv: Nat, +nq: Nat, +gc: List<&2, S.D>, +pins: List<&2, Nat>, p: PL.Plan<KI.dnum()>) -> Bool:
  match p:
    case PL.Plan{+vp, +ep, +np, bs}:
      KA.band(KA.nateq(KA.klen(~KI.dnum(), gc), nv),
      KA.band(KA.nateq(PL.nlen(vp), nv),
      KA.band(SV.distinct(vp),
      KA.band(KA.nateq(PL.nlen(ep), nq),
      nl_eq(ntake(np, vp), pins)))))

# the pins: the first np variables in block order
def skel.pins(s: ST.Skel) -> List<&2, Nat>:
  match s:
    case ST.Skel{vp, ep, np, bs, red}:
      ntake(np, vp)

# The verdict
# -----------

# sk-13a's checks, read off the answer alone (the exact checks last: they
# are the most work, and a box that fails is retried anyway)
def checks(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: Out) -> Bool:
  KA.band(SV.held(Out.pins(x), g0, Out.gc(x), Out.gr(x)),
  KA.band(WF.wf_dec(SV.mark(SV.reds(Out.cls(x)), sk)),
  KA.band(BX.Sketch.within(SV.mark(SV.reds(Out.cls(x)), sk), List.length(&2, N.NC(KI.dnum()), Out.gc(x))),
  KA.band(PL.check(~KI.dnum(), SV.solved(sk, SV.reds(Out.cls(x)), SV.dropped(Out.cls(x))), Out.gc(x), Out.gr(x), Out.plan(x)),
  KA.band(PL.check_sides(~KI.dnum(), SK.Sketch.sides(SV.mark(SV.cat(SV.reds(Out.cls(x)), SV.ambers(Out.cls(x))), sk)), Out.gc(x), Out.gr(x)),
  KA.band(shape(nvars(sk), CK.eqlen(SV.solved(sk, SV.reds(Out.cls(x)), SV.dropped(Out.cls(x)))), Out.gc(x), Out.pins(x), Out.plan(x)),
  VD.exact(sk, Out.cls(x))))))))

# the live drops' nd segments are long over the box (sk-13b), so that at
# every point of the box each dropped equation holds where the solved
# ones do
def ndok(+sk: SK.Sketch, +x: Out) -> Bool:
  PL.check_sides(~KI.dnum(), DR.ndsides(SV.ents(sk), SV.live_nd(Out.cls(x))), Out.gc(x), Out.gr(x))

# what the laws need: the nd sides first (a box too wide for them is
# retried anyway), then the checks
def final(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: Out) -> Bool:
  KA.band(ndok(sk, x), checks(sk, g0, x))

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

# the loop's answer and the verdict it reached on it
type Run is Data:
  Run{ok: Bool, m: NU.PR}

def run.ok(r: Run) -> Bool:
  match r:
    case Run{ok, m}:
      ok

def run.m(r: Run) -> NU.PR:
  match r:
    case Run{ok, m}:
      m

# the first precision whose answer passes the whole verdict (side
# conditions included: a box too wide for one is retried higher), with
# that verdict. Every failure moves on to the next precision, a block
# whose Newton did not settle included: at a low precision an
# ill-conditioned block can fail to settle or lose a pivot that a higher
# one keeps
def ploop(ps: List<&2, Nat>, ok: Bool, cur: NU.PR, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel) -> Run:
  match ps ok:
    case Nil{} ok:
      Run{ok, cur}
    case Con{p, t} True{}:
      Run{True{}, cur}
    case Con{+p, t} False{}:
      +nx = NU.plan(es, nv, skel, g0, p)
      ploop(t, accept(nx, sk, g0, cls, pins), nx, sk, g0, cls, pins, es, nv, skel)

# The structure depends on the sketch alone
# -----------------------------------------
# The pass (lib/dpass.bend) classifies the constraints and leaves the
# system solved, matched by dependence; its pins are the variables the
# variable side leaves over, and the blocks follow (lib/dpass.bend: skel2).

# the classes
def cls_of(+sk: SK.Sketch) -> List<&2, SV.Class>:
  DPS.classes2(sk)

# the system solved
def kept(+sk: SK.Sketch) -> List<&2, E.QExpr>:
  SV.solved(sk, SV.reds(cls_of(sk)), SV.dropped(cls_of(sk)))

# its positions in the sketch's numbering, in order
def good_of(+sk: SK.Sketch) -> List<&2, Nat>:
  DPS.solved_pos2(sk)

# the structure of the system solved, renumbered to positions in it
def skel_of(+sk: SK.Sketch) -> ST.Skel:
  DPS.skel2(sk)

# the pins: the earliest variables the system solved can leave over
def pins_of(+sk: SK.Sketch) -> List<&2, Nat>:
  DPS.pins2(sk)

# the loop from its first precision's answer (starting it with a literal
# "not yet" would let the checker unfold the whole verdict symbolically
# wherever a law mentions solve, ~40 s per file)
def ploop.start(ps: List<&2, Nat>, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel) -> Run:
  match ps:
    case Nil{}:
      Run{False{}, NU.PRetry{}}
    case Con{+p, t}:
      +nx = NU.plan(es, nv, skel, g0, p)
      ploop(t, accept(nx, sk, g0, cls, pins), nx, sk, g0, cls, pins, es, nv, skel)

# the loop's answer with its verdict, built through projections like found
def answer(+cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +r: Run) -> Out:
  Out{run.ok(r), cls, pins, pr.gc(run.m(r)), pr.gr(run.m(r)), pr.plan(run.m(r))}

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

# The solver over w precisions from level l; at level l (seven precisions
# from the l-th: "try harder"); and at level 0 (64 .. 512 bits)
def solve_lw(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +w: Nat) -> Out:
  answer(cls_of(sk), pins_of(sk), ploop.start(precisions(l, w), sk, g0, cls_of(sk), pins_of(sk), kept(sk), nvars(sk), skel_of(sk)))

def solve_l(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat) -> Out:
  solve_lw(sk, g0, l, 7n)

def solve(+sk: SK.Sketch, +g0: List<&2, S.D>) -> Out:
  solve_l(sk, g0, 0n)
