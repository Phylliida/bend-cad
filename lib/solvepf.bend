# bend-cad: the solver's verdict laws (ROADMAP: solve_exists,
# solve_unique, solve_pins), proven from the verdict (lib/solve.bend:
# final), the sk-06 sketch laws (lib/planpf.bend) and what the exact checks
# say (lib/vrdpf.bend, lib/vsdpf.bend). The search judges each answer and
# keeps that verdict with it; a True ok is the verdict of the answer
# returned (verdict, below). Nothing else about the search is used:
# whatever it found, a True verdict carries every hypothesis. The plan gives a point of the box where the system solved
# holds (and only one); there the drop checks give every equation of the
# sketch less its red constraints, the box's side checks and the amber
# refutations every side condition, so it means that sketch. The plan's
# shape check (hS) is lib/regpf.bend's, for solve_regular.

# Generated from tools/drafts/solvepf.draft by tools/expand.py; edit the
# draft.

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
import ./listpf.bend as L
import ./plan.bend as PL
import ./planpf.bend as PP
import ./meaning.bend as MN
import ./wfdec.bend as WF
import ./verdict.bend as VD
import ./vrdpf.bend as VR
import ./vsdpf.bend as VS
import ./struct.bend as ST
import ./numer.bend as NU
import ./solve.bend as SO
import ./cert.bend as CK

# The verdict's parts
# -------------------
# final(sk, g0, x) = P && B && C && D && E && (S && X)


def pP(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out) -> Bool:
  SV.held(SO.Out.pins(x), g0, SO.Out.gc(x), SO.Out.gr(x))

def pB(+sk: SK.Sketch, +x: SO.Out) -> Bool:
  WF.wf_dec(SV.mark(SV.reds(SO.Out.cls(x)), sk))

def pC(+sk: SK.Sketch, +x: SO.Out) -> Bool:
  BX.Sketch.within(SV.mark(SV.reds(SO.Out.cls(x)), sk), List.length(&2, N.NC(KI.dnum()), SO.Out.gc(x)))

def pD(+sk: SK.Sketch, +x: SO.Out) -> Bool:
  PL.check(~KI.dnum(), SV.solved(sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x))), SO.Out.gc(x), SO.Out.gr(x), SO.Out.plan(x))

def pE(+sk: SK.Sketch, +x: SO.Out) -> Bool:
  PL.check_sides(~KI.dnum(), SK.Sketch.sides(SV.mark(SV.cat(SV.reds(SO.Out.cls(x)), SV.ambers(SO.Out.cls(x))), sk)), SO.Out.gc(x), SO.Out.gr(x))

def pS(+sk: SK.Sketch, +x: SO.Out) -> Bool:
  SO.shape(SO.nvars(sk), CK.eqlen(SV.solved(sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x)))), SO.Out.gc(x), SO.Out.pins(x), SO.Out.plan(x))

def pX(+sk: SK.Sketch, +x: SO.Out) -> Bool:
  VD.exact(sk, SO.Out.cls(x))


def r0(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {KA.band(pB(sk, x), KA.band(pC(sk, x), KA.band(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x)))))) == True{} : Bool}:
  KA.band_r(pP(sk, g0, x), KA.band(pB(sk, x), KA.band(pC(sk, x), KA.band(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x)))))), h)

def r1(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {KA.band(pC(sk, x), KA.band(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x))))) == True{} : Bool}:
  KA.band_r(pB(sk, x), KA.band(pC(sk, x), KA.band(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x))))), r0(sk, g0, x, h))

def r2(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {KA.band(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x)))) == True{} : Bool}:
  KA.band_r(pC(sk, x), KA.band(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x)))), r1(sk, g0, x, h))

def r3(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x))) == True{} : Bool}:
  KA.band_r(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x))), r2(sk, g0, x, h))

def hP(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {pP(sk, g0, x) == True{} : Bool}:
  KA.band_l(pP(sk, g0, x), KA.band(pB(sk, x), KA.band(pC(sk, x), KA.band(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x)))))), h)

def hB(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {pB(sk, x) == True{} : Bool}:
  KA.band_l(pB(sk, x), KA.band(pC(sk, x), KA.band(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x))))), r0(sk, g0, x, h))

def hC(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {pC(sk, x) == True{} : Bool}:
  KA.band_l(pC(sk, x), KA.band(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x)))), r1(sk, g0, x, h))

def hD(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {pD(sk, x) == True{} : Bool}:
  KA.band_l(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x))), r2(sk, g0, x, h))

def hE(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {pE(sk, x) == True{} : Bool}:
  KA.band_l(pE(sk, x), KA.band(pS(sk, x), pX(sk, x)), r3(sk, g0, x, h))

def hTX(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {KA.band(pS(sk, x), pX(sk, x)) == True{} : Bool}:
  KA.band_r(pE(sk, x), KA.band(pS(sk, x), pX(sk, x)), r3(sk, g0, x, h))

def hS(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {pS(sk, x) == True{} : Bool}:
  KA.band_l(pS(sk, x), pX(sk, x), hTX(sk, g0, x, h))

def hX(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {pX(sk, x) == True{} : Bool}:
  KA.band_r(pS(sk, x), pX(sk, x), hTX(sk, g0, x, h))


def hdck(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {VD.dck(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x)), SO.Out.cls(x)) == True{} : Bool}:
  L.band_l(VD.dck(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x)), SO.Out.cls(x)), VD.ack(sk, SV.reds(SO.Out.cls(x)), SO.Out.cls(x), 0n), hX(sk, g0, x, h))

def hack(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {VD.ack(sk, SV.reds(SO.Out.cls(x)), SO.Out.cls(x), 0n) == True{} : Bool}:
  L.band_r(VD.dck(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x)), SO.Out.cls(x)), VD.ack(sk, SV.reds(SO.Out.cls(x)), SO.Out.cls(x), 0n), hX(sk, g0, x, h))

# For any answer with a True verdict
# ----------------------------------

def ex.go(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}, s: Sigma<&2, &2, M.Vec(~F), y => M.Both(BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y), SK.Zeros(~F, y, SV.solved(sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x)))))>)
  -> &y: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y) & SK.Sketch.means(~F, y, SV.mark(SV.reds(SO.Out.cls(x)), sk))):
  (+y, hy) = s
  (+hin, +hz) = hy
  (y, (hin, MN.sketch_sound(~F, y, SV.mark(SV.reds(SO.Out.cls(x)), sk), WF.wf_ok(SV.mark(SV.reds(SO.Out.cls(x)), sk), hB(sk, g0, x, h)),
    (VR.zeros_mark(~F, y, sk, SO.Out.cls(x), hz, hdck(sk, g0, x, h)),
     VS.sides_mark(~F, y, sk, SO.Out.cls(x), hz, hdck(sk, g0, x, h), hack(sk, g0, x, h),
       PP.box_sides(~KI.dnum(), ~F, ~H, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(SO.Out.cls(x)), SV.ambers(SO.Out.cls(x))), sk)), SO.Out.gc(x), SO.Out.gr(x), hE(sk, g0, x, h), y, hin))))))

def exists_of(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> &y: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y) & SK.Sketch.means(~F, y, SV.mark(SV.reds(SO.Out.cls(x)), sk))):
  ex.go(~F, ~H, sk, g0, x, h, PP.plan_exists(~KI.dnum(), ~F, ~R, ~H, SV.solved(sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x))), SO.Out.gc(x), SO.Out.gr(x), SO.Out.plan(x), hD(sk, g0, x, h)))

def unique_of(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}, +y1: M.Vec(~F), h1: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y1), m1: SK.Sketch.means(~F, y1, SV.mark(SV.reds(SO.Out.cls(x)), sk)), +y2: M.Vec(~F), h2: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y2), m2: SK.Sketch.means(~F, y2, SV.mark(SV.reds(SO.Out.cls(x)), sk))) -> {y1 == y2 : M.Vec(~F)}:
  PP.plan_unique(~KI.dnum(), ~F, ~H, SV.solved(sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x))), SO.Out.gc(x), SO.Out.gr(x), SO.Out.plan(x), hD(sk, g0, x, h),
    y1, h1, VR.zeros_solved(~F, y1, sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x)), PP.zeros_of_holds(~F, y1, SV.mark(SV.reds(SO.Out.cls(x)), sk), MN.sketch_complete(~F, y1, SV.mark(SV.reds(SO.Out.cls(x)), sk), m1))),
    y2, h2, VR.zeros_solved(~F, y2, sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x)), PP.zeros_of_holds(~F, y2, SV.mark(SV.reds(SO.Out.cls(x)), sk), MN.sketch_complete(~F, y2, SV.mark(SV.reds(SO.Out.cls(x)), sk), m2))))

def pins_of(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.final(sk, g0, x) == True{} : Bool}) -> {SV.held(SO.Out.pins(x), g0, SO.Out.gc(x), SO.Out.gr(x)) == True{} : Bool}:
  hP(sk, g0, x, h)

# The verdict the search keeps
# ----------------------------
# The loop judges each answer (accept) and keeps that verdict with it,
# stopping at a True one: the bit it returns is the verdict of the answer
# it returns.


def loop_ok(ps: List<&2, Nat>, ok: Bool, +cur: NU.PR, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel, h: {ok == SO.accept(cur, sk, g0, cls, pins) : Bool}) -> {SO.run.ok(SO.ploop(ps, ok, cur, sk, g0, cls, pins, es, nv, skel)) == SO.accept(SO.run.m(SO.ploop(ps, ok, cur, sk, g0, cls, pins, es, nv, skel)), sk, g0, cls, pins) : Bool}:
  match ps ok:
    case Nil{} ok:
      h
    case Con{p, t} True{}:
      h
    case Con{+p, t} False{}:
      loop_ok(t, SO.accept(NU.plan(es, nv, skel, g0, p), sk, g0, cls, pins), NU.plan(es, nv, skel, g0, p), sk, g0, cls, pins, es, nv, skel, {==})

def start_ok(ps: List<&2, Nat>, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel) -> {SO.run.ok(SO.ploop.start(ps, sk, g0, cls, pins, es, nv, skel)) == SO.accept(SO.run.m(SO.ploop.start(ps, sk, g0, cls, pins, es, nv, skel)), sk, g0, cls, pins) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, t}:
      loop_ok(t, SO.accept(NU.plan(es, nv, skel, g0, p), sk, g0, cls, pins), NU.plan(es, nv, skel, g0, p), sk, g0, cls, pins, es, nv, skel, {==})

# a run whose bit is its answer's verdict and True: its answer passes
def run_final(r: SO.Run, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, hs: {SO.run.ok(r) == SO.accept(SO.run.m(r), sk, g0, cls, pins) : Bool}, ok: {SO.run.ok(r) == True{} : Bool}) -> {SO.final(sk, g0, SO.answer(cls, pins, r)) == True{} : Bool}:
  match r:
    case SO.Run{b, m}:
      match b:
        case True{}:
          match m:
            case NU.POk{+y}:
              Equal.sym(Bool, True{}, SO.accept(NU.POk{y}, sk, g0, cls, pins), hs)
            case NU.PRetry{}:
              L.absurd({SO.final(sk, g0, SO.answer(cls, pins, SO.Run{True{}, NU.PRetry{}})) == True{} : Bool}, KA.tf(hs))
            case NU.PStop{}:
              L.absurd({SO.final(sk, g0, SO.answer(cls, pins, SO.Run{True{}, NU.PStop{}})) == True{} : Bool}, KA.tf(hs))
        case False{}:
          L.absurd({SO.final(sk, g0, SO.answer(cls, pins, SO.Run{False{}, m})) == True{} : Bool}, KA.ft(ok))


# a True ok is a True verdict on the solver's answer
def verdict(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}) -> {SO.final(sk, g0, SO.solve_l(sk, g0, l)) == True{} : Bool}:
  run_final(SO.ploop.start(SO.precisions(l, 7n), sk, g0, SO.cls_of(sk), SO.pins_of(sk), SO.kept(sk), SO.nvars(sk), SO.skel_of(sk)), sk, g0, SO.cls_of(sk), SO.pins_of(sk), start_ok(SO.precisions(l, 7n), sk, g0, SO.cls_of(sk), SO.pins_of(sk), SO.kept(sk), SO.nvars(sk), SO.skel_of(sk)), ok)

# The laws
# --------

def solve_exists(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}) -> &x: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x) & SK.Sketch.means(~F, x, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk))):
  exists_of(~F, ~R, ~H, sk, g0, SO.solve_l(sk, g0, l), verdict(sk, g0, l, ok))

def solve_unique(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}, +x1: M.Vec(~F), h1: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x1), m1: SK.Sketch.means(~F, x1, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk)), +x2: M.Vec(~F), h2: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l)), x2), m2: SK.Sketch.means(~F, x2, SV.mark(SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), sk))) -> {x1 == x2 : M.Vec(~F)}:
  unique_of(~F, ~H, sk, g0, SO.solve_l(sk, g0, l), verdict(sk, g0, l, ok), x1, h1, m1, x2, h2, m2)

def solve_pins(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +ok: {SO.Out.ok(SO.solve_l(sk, g0, l)) == True{} : Bool}) -> {SV.held(SO.Out.pins(SO.solve_l(sk, g0, l)), g0, SO.Out.gc(SO.solve_l(sk, g0, l)), SO.Out.gr(SO.solve_l(sk, g0, l))) == True{} : Bool}:
  pins_of(sk, g0, SO.solve_l(sk, g0, l), verdict(sk, g0, l, ok))

