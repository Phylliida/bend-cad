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

# the first precision that gives a plan (a block that will not settle
# stops the search: more precision will not help it)
def ploop(ps: List<&2, Nat>, cur: NU.PR, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel, +g0: List<&2, S.D>) -> NU.PR:
  match ps cur:
    case Nil{} cur:
      cur
    case Con{p, t} NU.POk{x}:
      NU.POk{x}
    case Con{p, t} NU.PStop{}:
      NU.PStop{}
    case Con{+p, t} NU.PRetry{}:
      ploop(t, NU.plan(es, nv, skel, g0, p), es, nv, skel, g0)

def precisions() -> List<&2, Nat>:
  [64n, 96n, 128n, 192n, 256n, 384n, 512n]

def noplan() -> PL.Plan<KI.dnum()>:
  PL.Plan{Nil{}, Nil{}, 0n, Nil{}}

def found(+red: List<&2, Nat>, +why: List<&2, SV.Why>, +pins: List<&2, Nat>, m: NU.PR) -> Out:
  match m:
    case NU.PRetry{}:
      Out{False{}, red, why, pins, Nil{}, Nil{}, noplan()}
    case NU.PStop{}:
      Out{False{}, red, why, pins, Nil{}, Nil{}, noplan()}
    case NU.POk{NU.NP{plan, gc, gr}}:
      Out{True{}, red, why, pins, gc, gr, plan}

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

def search.sk(+red: List<&2, Nat>, +why: List<&2, SV.Why>, +es: List<&2, E.QExpr>, +nv: Nat, +g0: List<&2, S.D>, +skel: ST.Skel) -> Out:
  found(red, why, skel.pins(skel), ploop(precisions(), NU.PRetry{}, es, nv, skel, g0))

def search.es(+red: List<&2, Nat>, +why: List<&2, SV.Why>, +es: List<&2, E.QExpr>, +nv: Nat, +g0: List<&2, S.D>) -> Out:
  search.sk(red, why, es, nv, g0, ST.structure(es, nv))

def search.go(+sk: SK.Sketch, +g0: List<&2, S.D>, +nv: Nat, +rs: List<&2, ST.Red>) -> Out:
  search.es(reds(SV.owners(sk), rs), whys(rs), SK.Sketch.eqs(SV.mark(reds(SV.owners(sk), rs), sk)), nv, g0)

# red constraints first (constraints matched as units, in order: each
# red one's witness uses only kept constraints and itself), then the
# sketch less them
def search(+sk: SK.Sketch, +g0: List<&2, S.D>) -> Out:
  search.go(sk, g0, nvars(sk), ST.reds(SK.Sketch.eqs(sk), nvars(sk), groups(ncons(sk), SV.owners(sk), 0n)))

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

# The solver
def solve(+sk: SK.Sketch, +g0: List<&2, S.D>) -> Out:
  seal(sk, g0, search(sk, g0))
