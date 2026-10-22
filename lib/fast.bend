# bend-cad: the fast solver (PLAN-sk13w W5, W6). lib/solve.bend's solver
# with its numbers in any K that the proposer's operations W extend
# (lib/pops.bend): the same precision loop, the proposer written over K
# (lib/gnumer.bend), and the same verdict, its plan and side checks run by
# the generic checker in K and its other parts read through tod. The
# answer is sent back to S.D once, at the end. With laws relating K to
# KI.dnum() (lib/pops.bend: PLaws) it returns exactly what SO.solve does
# (lib/fastpf.bend: fsolve_eq), so every law about the solver holds for
# it. The CLI runs it at word dyadics in base 2^14 (wsolve below).

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/knum.bend as N
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ./certdef.bend as C
import ./karith.bend as KA
import ./kinst.bend as KI
import ./plan.bend as PL
import ./struct.bend as ST
import ./wfdec.bend as WF
import ./verdict.bend as VD
import ./cert.bend as CK
import ./solve.bend as SO
import ./pass.bend as PA
import ./pops.bend as PO
import ./gnumer.bend as GN
import ./wnum.bend as WN

# Conversions with S.D
# --------------------

def ofdv(~K: N.Num, ~W: PO.POps<K>, xs: List<&2, S.D>) -> N.KVec(~K):
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{PO.ofd(K, W, x), ofdv(~K, ~W, t)}

def todv(~K: N.Num, ~W: PO.POps<K>, xs: N.KVec(~K)) -> List<&2, S.D>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{PO.tod(K, W, x), todv(~K, ~W, t)}

def todm(~K: N.Num, ~W: PO.POps<K>, a: N.KMat(~K)) -> List<&2, List<&2, S.D>>:
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{todv(~K, ~W, r), todm(~K, ~W, t)}

def todcert(~K: N.Num, ~W: PO.POps<K>, c: C.Cert<K>) -> C.Cert<KI.dnum()>:
  match c:
    case C.Cert{yc, yr, q, ym, pc, pr}:
      C.Cert{todv(~K, ~W, yc), todv(~K, ~W, yr), PO.tod(K, W, q), todm(~K, ~W, ym), todv(~K, ~W, pc), todv(~K, ~W, pr)}

def todpb(~K: N.Num, ~W: PO.POps<K>, b: PL.PBlock<K>) -> PL.PBlock<KI.dnum()>:
  match b:
    case PL.PBlock{n, pars, c}:
      PL.PBlock{n, pars, todcert(~K, ~W, c)}

def todpbs(~K: N.Num, ~W: PO.POps<K>, bs: List<&2, PL.PBlock<K>>) -> List<&2, PL.PBlock<KI.dnum()>>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      Con{todpb(~K, ~W, b), todpbs(~K, ~W, t)}

def todplan(~K: N.Num, ~W: PO.POps<K>, p: PL.Plan<K>) -> PL.Plan<KI.dnum()>:
  match p:
    case PL.Plan{vp, ep, np, bs}:
      PL.Plan{vp, ep, np, todpbs(~K, ~W, bs)}

# The answer in K
# ---------------

type FOut<-K: N.Num> is Data:
  FOut{ok: Bool, cls: List<&2, SV.Class>, pins: List<&2, Nat>, gc: List<&2, N.NC(K)>, gr: List<&2, N.NC(K)>, plan: PL.Plan<K>}

def FOut.ok(-K: N.Num, x: FOut<K>) -> Bool:
  match x:
    case FOut{ok, cls, pins, gc, gr, plan}:
      ok

def FOut.cls(-K: N.Num, x: FOut<K>) -> List<&2, SV.Class>:
  match x:
    case FOut{ok, cls, pins, gc, gr, plan}:
      cls

def FOut.pins(-K: N.Num, x: FOut<K>) -> List<&2, Nat>:
  match x:
    case FOut{ok, cls, pins, gc, gr, plan}:
      pins

def FOut.gc(-K: N.Num, x: FOut<K>) -> N.KVec(~K):
  match x:
    case FOut{ok, cls, pins, gc, gr, plan}:
      gc

def FOut.gr(-K: N.Num, x: FOut<K>) -> N.KVec(~K):
  match x:
    case FOut{ok, cls, pins, gc, gr, plan}:
      gr

def FOut.plan(-K: N.Num, x: FOut<K>) -> PL.Plan<K>:
  match x:
    case FOut{ok, cls, pins, gc, gr, plan}:
      plan

def noplan(~K: N.Num) -> PL.Plan<K>:
  PL.Plan{Nil{}, Nil{}, 0n, Nil{}}

def pr.ok(~K: N.Num, m: GN.GPR<K>) -> Bool:
  match m:
    case GN.GPOk{x}:
      True{}
    case GN.GPRetry{}:
      False{}
    case GN.GPStop{}:
      False{}

def pr.gc(~K: N.Num, m: GN.GPR<K>) -> N.KVec(~K):
  match m:
    case GN.GPOk{GN.GNP{plan, gc, gr}}:
      gc
    case GN.GPRetry{}:
      Nil{}
    case GN.GPStop{}:
      Nil{}

def pr.gr(~K: N.Num, m: GN.GPR<K>) -> N.KVec(~K):
  match m:
    case GN.GPOk{GN.GNP{plan, gc, gr}}:
      gr
    case GN.GPRetry{}:
      Nil{}
    case GN.GPStop{}:
      Nil{}

def pr.plan(~K: N.Num, m: GN.GPR<K>) -> PL.Plan<K>:
  match m:
    case GN.GPOk{GN.GNP{plan, gc, gr}}:
      plan
    case GN.GPRetry{}:
      noplan(~K)
    case GN.GPStop{}:
      noplan(~K)

# an answer at one precision, for the verdict to judge
def found(~K: N.Num, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +m: GN.GPR<K>) -> FOut<K>:
  FOut{pr.ok(~K, m), cls, pins, pr.gc(~K, m), pr.gr(~K, m), pr.plan(~K, m)}

# SO.shape over K
def shape(~K: N.Num, +nv: Nat, +nq: Nat, +gc: N.KVec(~K), +pins: List<&2, Nat>, p: PL.Plan<K>) -> Bool:
  match p:
    case PL.Plan{+vp, +ep, +np, bs}:
      KA.band(KA.nateq(KA.klen(~K, gc), nv),
      KA.band(KA.nateq(PL.nlen(vp), nv),
      KA.band(SV.distinct(vp),
      KA.band(KA.nateq(PL.nlen(ep), nq),
      SO.nl_eq(SO.ntake(np, vp), pins)))))

# The verdict
# -----------

# SO.final, its plan and sides checked in K
def final(~K: N.Num, ~W: PO.POps<K>, +sk: SK.Sketch, +g0: List<&2, S.D>, +x: FOut<K>) -> Bool:
  KA.band(SV.held(FOut.pins(K, x), g0, todv(~K, ~W, FOut.gc(K, x)), todv(~K, ~W, FOut.gr(K, x))),
  KA.band(WF.wf_dec(SV.mark(SV.reds(FOut.cls(K, x)), sk)),
  KA.band(BX.Sketch.within(SV.mark(SV.reds(FOut.cls(K, x)), sk), List.length(&2, N.NC(K), FOut.gc(K, x))),
  KA.band(PL.check(~K, SV.solved(sk, SV.reds(FOut.cls(K, x)), SV.dropped(FOut.cls(K, x))), FOut.gc(K, x), FOut.gr(K, x), FOut.plan(K, x)),
  KA.band(PL.check_sides(~K, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(FOut.cls(K, x)), SV.ambers(FOut.cls(K, x))), sk)), FOut.gc(K, x), FOut.gr(K, x)),
  KA.band(shape(~K, SO.nvars(sk), CK.eqlen(SV.solved(sk, SV.reds(FOut.cls(K, x)), SV.dropped(FOut.cls(K, x)))), FOut.gc(K, x), FOut.pins(K, x), FOut.plan(K, x)),
  VD.exact(sk, FOut.cls(K, x))))))))

# The precision loop
# ------------------

def accept(~K: N.Num, ~W: PO.POps<K>, m: GN.GPR<K>, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>) -> Bool:
  match m:
    case GN.GPOk{+x}:
      final(~K, ~W, sk, g0, found(~K, cls, pins, GN.GPOk{x}))
    case GN.GPRetry{}:
      False{}
    case GN.GPStop{}:
      False{}

type FRun<-K: N.Num> is Data:
  FRun{ok: Bool, m: GN.GPR<K>}

def run.ok(-K: N.Num, r: FRun<K>) -> Bool:
  match r:
    case FRun{ok, m}:
      ok

def run.m(-K: N.Num, r: FRun<K>) -> GN.GPR<K>:
  match r:
    case FRun{ok, m}:
      m

# SO.ploop: g0 is the drawing, g0w the same in K
def ploop(~K: N.Num, ~W: PO.POps<K>, ps: List<&2, Nat>, ok: Bool, cur: GN.GPR<K>, +sk: SK.Sketch, +g0: List<&2, S.D>, +g0w: N.KVec(~K), +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel) -> FRun<K>:
  match ps ok:
    case Nil{} ok:
      FRun{ok, cur}
    case Con{p, t} True{}:
      FRun{True{}, cur}
    case Con{+p, t} False{}:
      +nx = GN.plan(~K, ~W, es, nv, skel, g0w, p)
      ploop(~K, ~W, t, accept(~K, ~W, nx, sk, g0, cls, pins), nx, sk, g0, g0w, cls, pins, es, nv, skel)

def ploop.start(~K: N.Num, ~W: PO.POps<K>, ps: List<&2, Nat>, +sk: SK.Sketch, +g0: List<&2, S.D>, +g0w: N.KVec(~K), +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel) -> FRun<K>:
  match ps:
    case Nil{}:
      FRun{False{}, GN.GPRetry{}}
    case Con{+p, t}:
      +nx = GN.plan(~K, ~W, es, nv, skel, g0w, p)
      ploop(~K, ~W, t, accept(~K, ~W, nx, sk, g0, cls, pins), nx, sk, g0, g0w, cls, pins, es, nv, skel)

# the loop's answer with its verdict, sent back to S.D
def answer(~K: N.Num, ~W: PO.POps<K>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +r: FRun<K>) -> SO.Out:
  SO.Out{run.ok(K, r), cls, pins, todv(~K, ~W, pr.gc(~K, run.m(K, r))), todv(~K, ~W, pr.gr(~K, run.m(K, r))), todplan(~K, ~W, pr.plan(~K, run.m(K, r)))}

# The solver (SO.solve_lw, SO.solve_l, SO.solve)
# ----------------------------------------------
# SO.solve_lw names the pass's results (classes, solved positions, pins,
# structure) separately, and each runs the pass again; here each is
# computed once and passed on. The terms are SO.solve_lw's with the shared
# values substituted, so the two are equal by definition.

def solve_kv(~K: N.Num, ~W: PO.POps<K>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +w: Nat, +cls: List<&2, SV.Class>, +sp: List<&2, Nat>, +kv: ST.KD) -> SO.Out:
  answer(~K, ~W, cls, ST.KD.red(kv), ploop.start(~K, ~W, SO.precisions(l, w), sk, g0, ofdv(~K, ~W, g0), cls, ST.KD.red(kv), SV.solved(sk, SV.reds(cls), SV.dropped(cls)), PA.nvars(sk), ST.renum(ST.skel.kd(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), sp, kv), sp)))

def solve_st(~K: N.Num, ~W: PO.POps<K>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +w: Nat, +cls: List<&2, SV.Class>, +sp: List<&2, Nat>, +da: List<&2, List<&2, Nat>>) -> SO.Out:
  solve_kv(~K, ~W, sk, g0, l, w, cls, sp, PA.kvs(da, ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), sp))

def solve_da(~K: N.Num, ~W: PO.POps<K>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +w: Nat, +da: List<&2, List<&2, Nat>>) -> SO.Out:
  solve_st(~K, ~W, sk, g0, l, w, PA.pass(PA.recs(sk), SK.Sketch.eqs(sk), SV.owners(sk), sk, da, 1n+PA.nvars(sk), 0n, PA.start(PA.nvars(sk))), PA.PS.bp(PA.pass_st(PA.recs(sk), SK.Sketch.eqs(sk), SV.owners(sk), sk, da, 1n+PA.nvars(sk), 0n, PA.start(PA.nvars(sk)))), da)

def solve_lw(~K: N.Num, ~W: PO.POps<K>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +w: Nat) -> SO.Out:
  solve_da(~K, ~W, sk, g0, l, w, PA.dadjs(SK.Sketch.eqs(sk)))

def solve_l(~K: N.Num, ~W: PO.POps<K>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat) -> SO.Out:
  solve_lw(~K, ~W, sk, g0, l, 7n)

def solve(~K: N.Num, ~W: PO.POps<K>, +sk: SK.Sketch, +g0: List<&2, S.D>) -> SO.Out:
  solve_l(~K, ~W, sk, g0, 0n)

# Word dyadics in base 2^14
# -------------------------
# A template's arguments are closed terms, so the CLI's base is fixed here.
# It is 2^14 (lp = 13): the checker's numbers are unary, so a type naming
# a computed 2^(1 + lp) - 1 has it expanded and compared digit by digit,
# and the base must be a literal; 2^14 is the largest for which the
# checker can still evaluate the hypothesis 2^14 = 16383 + 1 that the
# theorem at this base needs (lib/fastpf.bend: wsolve_eq). A larger base
# saves little: sketch 6 (a 32x32 block) took 4% fewer instructions at
# 2^23.

def wk() -> N.Num:
  WN.wnum(16383n, 13n)

def wo() -> PO.POps<wk()>:
  WN.wops(16383n, 13n)

# the solver at word dyadics, base 2^14 (the CLI's)
def wsolve(+sk: SK.Sketch, +g0: List<&2, S.D>) -> SO.Out:
  solve(~wk(), ~wo(), sk, g0)
