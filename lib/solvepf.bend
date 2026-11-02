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
#
# Since the sk-13b switch (2026-11-02), what this file proved about
# sk-13a's pass, Honest or solver is proven in lib/dsolvepf.bend; what
# is left here is what that proof reuses, and the description below is
# of the sk-13a proof.

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
import ./wfcpf.bend as WC
import ./covpf.bend as CV
import ./gmpf.bend as GM
import ./dfspf.bend as D
import ./pass.bend as PA
import ./dropok.bend as DK
import ./ckpf.bend as CKP

# The verdict's parts
# -------------------
# checks(sk, g0, x) = P && B && C && D && E && (S && X)


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


def r0(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}) -> {KA.band(pB(sk, x), KA.band(pC(sk, x), KA.band(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x)))))) == True{} : Bool}:
  KA.band_r(pP(sk, g0, x), KA.band(pB(sk, x), KA.band(pC(sk, x), KA.band(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x)))))), h)

def r1(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}) -> {KA.band(pC(sk, x), KA.band(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x))))) == True{} : Bool}:
  KA.band_r(pB(sk, x), KA.band(pC(sk, x), KA.band(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x))))), r0(sk, g0, x, h))

def r2(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}) -> {KA.band(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x)))) == True{} : Bool}:
  KA.band_r(pC(sk, x), KA.band(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x)))), r1(sk, g0, x, h))

def r3(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}) -> {KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x))) == True{} : Bool}:
  KA.band_r(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x))), r2(sk, g0, x, h))

def hP(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}) -> {pP(sk, g0, x) == True{} : Bool}:
  KA.band_l(pP(sk, g0, x), KA.band(pB(sk, x), KA.band(pC(sk, x), KA.band(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x)))))), h)

def hB(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}) -> {pB(sk, x) == True{} : Bool}:
  KA.band_l(pB(sk, x), KA.band(pC(sk, x), KA.band(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x))))), r0(sk, g0, x, h))

def hC(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}) -> {pC(sk, x) == True{} : Bool}:
  KA.band_l(pC(sk, x), KA.band(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x)))), r1(sk, g0, x, h))

def hD(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}) -> {pD(sk, x) == True{} : Bool}:
  KA.band_l(pD(sk, x), KA.band(pE(sk, x), KA.band(pS(sk, x), pX(sk, x))), r2(sk, g0, x, h))

def hE(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}) -> {pE(sk, x) == True{} : Bool}:
  KA.band_l(pE(sk, x), KA.band(pS(sk, x), pX(sk, x)), r3(sk, g0, x, h))

def hTX(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}) -> {KA.band(pS(sk, x), pX(sk, x)) == True{} : Bool}:
  KA.band_r(pE(sk, x), KA.band(pS(sk, x), pX(sk, x)), r3(sk, g0, x, h))

def hS(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}) -> {pS(sk, x) == True{} : Bool}:
  KA.band_l(pS(sk, x), pX(sk, x), hTX(sk, g0, x, h))

def hX(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}) -> {pX(sk, x) == True{} : Bool}:
  KA.band_r(pS(sk, x), pX(sk, x), hTX(sk, g0, x, h))


def hack(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}) -> {VD.ack(sk, SV.reds(SO.Out.cls(x)), SO.Out.cls(x), 0n) == True{} : Bool}:
  hX(sk, g0, x, h)

# What the verdict checked, without the driven flags
# --------------------------------------------------

def wf_unmark(+red: List<&2, Nat>, sk: SK.Sketch, h: {WF.wf_dec(SV.mark(red, sk)) == True{} : Bool}) -> {WF.wf_dec(sk) == True{} : Bool}:
  match sk:
    case SK.Sketch{vs, +es, +cs}:
      %WC.mark_cons(es, red, cs, 0n) : {KA.band(WF.ents(es, es), _) == True{} : Bool}
      h

def wu_cons(+red: List<&2, Nat>, cs: List<&2, SK.Rec>, +i: Nat, +n: Nat, +h: {BX.Sketch.within.cons(SV.mark.cons(red, cs, i), n) == True{} : Bool}) -> {BX.Sketch.within.cons(cs, n) == True{} : Bool}:
  match cs:
    case Nil{}:
      {==}
    case Con{SK.Rec{id, dr, +k}, +t}:
      CV.and_i(BX.Constraint.within(k, n), BX.Sketch.within.cons(t, n), CV.and_l(BX.Constraint.within(k, n), BX.Sketch.within.cons(SV.mark.cons(red, t, 1n+i), n), h), wu_cons(red, t, 1n+i, n, CV.and_r(BX.Constraint.within(k, n), BX.Sketch.within.cons(SV.mark.cons(red, t, 1n+i), n), h)))

def w_unmark(+red: List<&2, Nat>, sk: SK.Sketch, +n: Nat, +h: {BX.Sketch.within(SV.mark(red, sk), n) == True{} : Bool}) -> {BX.Sketch.within(sk, n) == True{} : Bool}:
  match sk:
    case SK.Sketch{vs, +es, +cs}:
      CV.and_i(BX.Sketch.within.ents(es, n), BX.Sketch.within.cons(cs, n), CV.and_l(BX.Sketch.within.ents(es, n), BX.Sketch.within.cons(SV.mark.cons(red, cs, 0n), n), h), wu_cons(red, cs, 0n, n, CV.and_r(BX.Sketch.within.ents(es, n), BX.Sketch.within.cons(SV.mark.cons(red, cs, 0n), n), h)))

def len_kl(xs: List<&2, S.D>) -> {List.length(&2, N.NC(KI.dnum()), xs) == KA.klen(~KI.dnum(), xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{a, t}:
      %Equal.sym(Nat, List.length(&2, N.NC(KI.dnum()), t), KA.klen(~KI.dnum(), t), len_kl(t)) : {1n+_ == 1n+KA.klen(~KI.dnum(), t) : Nat}
      {==}

# the shape check: a box coordinate per variable
def sh_klen(+nv: Nat, +nq: Nat, +gc: List<&2, S.D>, +pins: List<&2, Nat>, p: PL.Plan<KI.dnum()>, +h: {SO.shape(nv, nq, gc, pins, p) == True{} : Bool}) -> {KA.klen(~KI.dnum(), gc) == nv : Nat}:
  match p:
    case PL.Plan{+vp, +ep, +np, +bs}:
      KA.nateq_ok(KA.klen(~KI.dnum(), gc), nv, KA.band_l(KA.nateq(KA.klen(~KI.dnum(), gc), nv), KA.band(KA.nateq(PL.nlen(vp), nv), KA.band(SV.distinct(vp), KA.band(KA.nateq(PL.nlen(ep), nq), SO.nl_eq(SO.ntake(np, vp), pins)))), h))

def wfd_of(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}) -> {WF.wf_dec(sk) == True{} : Bool}:
  wf_unmark(SV.reds(SO.Out.cls(x)), sk, hB(sk, g0, x, h))

def wf_of(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}) -> SK.Sketch.wf(sk):
  WF.wf_ok(sk, wfd_of(sk, g0, x, h))

def cov_of(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}) -> {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}:
  %Equal.trans(Nat, List.length(&2, N.NC(KI.dnum()), SO.Out.gc(x)), KA.klen(~KI.dnum(), SO.Out.gc(x)), SO.nvars(sk), len_kl(SO.Out.gc(x)), sh_klen(SO.nvars(sk), CK.eqlen(SV.solved(sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x)))), SO.Out.gc(x), SO.Out.pins(x), SO.Out.plan(x), hS(sk, g0, x, h))) : {BX.Sketch.within(sk, _) == True{} : Bool}
  w_unmark(SV.reds(SO.Out.cls(x)), sk, List.length(&2, N.NC(KI.dnum()), SO.Out.gc(x)), hC(sk, g0, x, h))

# and so the pass's adjacency is within the variables
def adjb_of(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}) -> {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}:
  GM.adjb_dadjs(SK.Sketch.eqs(sk), SO.nvars(sk), CV.cov(sk, SO.nvars(sk), cov_of(sk, g0, x, h), wfd_of(sk, g0, x, h)))

# For any answer with a True verdict
# ----------------------------------

def ex.go(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}, +hd: {DK.dck(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x)), SO.Out.cls(x)) == True{} : Bool}, s: Sigma<&2, &2, M.Vec(~F), y => M.Both(BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y), SK.Zeros(~F, y, SV.solved(sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x)))))>)
  -> &y: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y) & SK.Sketch.means(~F, y, SV.mark(SV.reds(SO.Out.cls(x)), sk))):
  (+y, hy) = s
  (+hin, +hz) = hy
  (y, (hin, MN.sketch_sound(~F, y, SV.mark(SV.reds(SO.Out.cls(x)), sk), WF.wf_ok(SV.mark(SV.reds(SO.Out.cls(x)), sk), hB(sk, g0, x, h)),
    (VR.zeros_mark(~F, y, sk, SO.Out.cls(x), hz, hd),
     VS.sides_mark(~F, y, sk, SO.Out.cls(x), hz, hd, hack(sk, g0, x, h),
       PP.box_sides(~KI.dnum(), ~F, ~H, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(SO.Out.cls(x)), SV.ambers(SO.Out.cls(x))), sk)), SO.Out.gc(x), SO.Out.gr(x), hE(sk, g0, x, h), y, hin))))))

def exists_of(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}, +hd: {DK.dck(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x)), SO.Out.cls(x)) == True{} : Bool}) -> &y: M.Vec(~F) -> (BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y) & SK.Sketch.means(~F, y, SV.mark(SV.reds(SO.Out.cls(x)), sk))):
  ex.go(~F, ~H, sk, g0, x, h, hd, PP.plan_exists(~KI.dnum(), ~F, ~R, ~H, SV.solved(sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x))), SO.Out.gc(x), SO.Out.gr(x), SO.Out.plan(x), hD(sk, g0, x, h)))

def unique_of(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}, +y1: M.Vec(~F), h1: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y1), m1: SK.Sketch.means(~F, y1, SV.mark(SV.reds(SO.Out.cls(x)), sk)), +y2: M.Vec(~F), h2: BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(x), SO.Out.gr(x), y2), m2: SK.Sketch.means(~F, y2, SV.mark(SV.reds(SO.Out.cls(x)), sk))) -> {y1 == y2 : M.Vec(~F)}:
  PP.plan_unique(~KI.dnum(), ~F, ~H, SV.solved(sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x))), SO.Out.gc(x), SO.Out.gr(x), SO.Out.plan(x), hD(sk, g0, x, h),
    y1, h1, VR.zeros_solved(~F, y1, sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x)), PP.zeros_of_holds(~F, y1, SV.mark(SV.reds(SO.Out.cls(x)), sk), MN.sketch_complete(~F, y1, SV.mark(SV.reds(SO.Out.cls(x)), sk), m1))),
    y2, h2, VR.zeros_solved(~F, y2, sk, SV.reds(SO.Out.cls(x)), SV.dropped(SO.Out.cls(x)), PP.zeros_of_holds(~F, y2, SV.mark(SV.reds(SO.Out.cls(x)), sk), MN.sketch_complete(~F, y2, SV.mark(SV.reds(SO.Out.cls(x)), sk), m2))))

def pins_of(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out, +h: {SO.checks(sk, g0, x) == True{} : Bool}) -> {SV.held(SO.Out.pins(x), g0, SO.Out.gc(x), SO.Out.gr(x)) == True{} : Bool}:
  hP(sk, g0, x, h)

# The verdict the search keeps
# ----------------------------
# The loop judges each answer (accept) and keeps that verdict with it,
# stopping at a True one: the bit it returns is the verdict of the answer
# it returns.



# The laws
# --------
