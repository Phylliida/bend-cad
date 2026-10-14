# bend-cad: the solver (DESIGN §10), verified. solve(sk, g0) takes a
# sketch and a drawing (a dyadic value per variable) and answers with a
# box, a plan, and the constraints it flagged red with their reasons.
#
# search does the work (lib/struct.bend: red equations and their
# witnesses, pins, blocks; lib/numer.bend: Newton, Y and radii at
# precisions 64 .. 512). seal then recomputes the verdict from the answer
# alone: every red constraint explained (spec/solve.bend), the sketch with
# them made driven well formed (lib/wfdec.bend), covered by the box, its
# plan and its side conditions checked (lib/plan.bend). So the laws
# (solve_exists, solve_unique, solve_red) need nothing from search: they
# follow from the verdict and the sk-06 laws.

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
  Out{ok: Bool, red: List<&2, Nat>, why: List<&2, SV.Why>, gc: List<&2, S.D>, gr: List<&2, S.D>, plan: PL.Plan<KI.dnum()>}

def Out.ok(x: Out) -> Bool:
  match x:
    case Out{ok, red, why, gc, gr, plan}:
      ok

def Out.red(x: Out) -> List<&2, Nat>:
  match x:
    case Out{ok, red, why, gc, gr, plan}:
      red

def Out.why(x: Out) -> List<&2, SV.Why>:
  match x:
    case Out{ok, red, why, gc, gr, plan}:
      why

def Out.gc(x: Out) -> List<&2, S.D>:
  match x:
    case Out{ok, red, why, gc, gr, plan}:
      gc

def Out.gr(x: Out) -> List<&2, S.D>:
  match x:
    case Out{ok, red, why, gc, gr, plan}:
      gr

def Out.plan(x: Out) -> PL.Plan<KI.dnum()>:
  match x:
    case Out{ok, red, why, gc, gr, plan}:
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

def skel.red(s: ST.Skel) -> List<&2, ST.Red>:
  match s:
    case ST.Skel{vp, ep, np, bs, red}:
      red

# each red equation's constraint, and why
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

def found(+red: List<&2, Nat>, +why: List<&2, SV.Why>, m: NU.PR) -> Out:
  match m:
    case NU.PRetry{}:
      Out{False{}, red, why, Nil{}, Nil{}, noplan()}
    case NU.PStop{}:
      Out{False{}, red, why, Nil{}, Nil{}, noplan()}
    case NU.POk{NU.NP{plan, gc, gr}}:
      Out{True{}, red, why, gc, gr, plan}

def search.es(+red: List<&2, Nat>, +why: List<&2, SV.Why>, +es: List<&2, E.QExpr>, +nv: Nat, +g0: List<&2, S.D>) -> Out:
  found(red, why, ploop(precisions(), NU.PRetry{}, es, nv, ST.structure(es, nv), g0))

def search.go(+sk: SK.Sketch, +g0: List<&2, S.D>, +nv: Nat, +rs: List<&2, ST.Red>) -> Out:
  search.es(reds(SV.owners(sk), rs), whys(rs), SK.Sketch.eqs(SV.mark(reds(SV.owners(sk), rs), sk)), nv, g0)

def search(+sk: SK.Sketch, +g0: List<&2, S.D>) -> Out:
  search.go(sk, g0, nvars(sk), skel.red(ST.structure(SK.Sketch.eqs(sk), nvars(sk))))

# The verdict
# -----------

# what the laws need, read off the answer alone
def final(+sk: SK.Sketch, +x: Out) -> Bool:
  KA.band(SV.explained(sk, Out.red(x), Out.why(x)),
  KA.band(WF.wf_dec(SV.mark(Out.red(x), sk)),
  KA.band(BX.Sketch.within(SV.mark(Out.red(x), sk), List.length(&2, N.NC(KI.dnum()), Out.gc(x))),
  KA.band(PL.check(~KI.dnum(), SK.Sketch.eqs(SV.mark(Out.red(x), sk)), Out.gc(x), Out.gr(x), Out.plan(x)),
  PL.check_sides(~KI.dnum(), SK.Sketch.sides(SV.mark(Out.red(x), sk)), Out.gc(x), Out.gr(x))))))

def seal(+sk: SK.Sketch, +x: Out) -> Out:
  Out{final(sk, x), Out.red(x), Out.why(x), Out.gc(x), Out.gr(x), Out.plan(x)}

# The solver
def solve(+sk: SK.Sketch, +g0: List<&2, S.D>) -> Out:
  seal(sk, search(sk, g0))
