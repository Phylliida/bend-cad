# bend-cad: what a refusal of the draft solver means (PLAN-sk13b B7,
# solve_refused over the new pass): if no level certifies the drawing g0,
# it is not a regular solution of the system solved at which the live
# drops' nd segments are nonzero (lib/dcompletepf.bend's solve_complete2
# would certify it). Proofs only; lib/refusedpf.bend's, over the draft
# solver.
#
# Generated from tools/drafts/drefusedpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/real.bend as CR
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ../spec/deriv.bend as DV
import ../spec/dir.bend as DR
import ./karith.bend as KA
import ./kinst.bend as KI
import ./solve.bend as SO
import ./dsolve.bend as DSO
import ./refusedpf.bend as RFD
import ./dcompletepf.bend as DCP


# a level that certifies g0 contradicts hn
def ref.fin(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, hn: {SO.Out.ok(DSO.solve_l2(sk, g0, l)) == False{} : Bool}, +x: M.Vec(~F), f: ({SO.Out.ok(DSO.solve_l2(sk, g0, l)) == True{} : Bool} & BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(DSO.solve_l2(sk, g0, l)), SO.Out.gr(DSO.solve_l2(sk, g0, l)), x))) -> Empty:
  match f:
    case (hok, hin):
      KA.tf(Equal.trans(Bool, True{}, SO.Out.ok(DSO.solve_l2(sk, g0, l)), False{}, Equal.sym(Bool, SO.Out.ok(DSO.solve_l2(sk, g0, l)), True{}, hok), hn))

def ref.l(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, hn: @l: Nat -> {SO.Out.ok(DSO.solve_l2(sk, g0, l)) == False{} : Bool}, +x: M.Vec(~F), +hx: {x == N.ofkv(~KI.dnum(), ~F, ~H, g0) : M.Vec(~F)}, +d: O.C(F), +hd: O.lt(F, O.zero(F), d), q: &l: Nat -> (@g: List<&2, S.D> -> SV.Near(~KI.dnum(), ~F, ~H, SO.nvars(sk), 0n, g, x, d, DSO.pins_of2(sk), g0) -> ({SO.Out.ok(DSO.solve_l2(sk, g, l)) == True{} : Bool} & BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(DSO.solve_l2(sk, g, l)), SO.Out.gr(DSO.solve_l2(sk, g, l)), x)))) -> Empty:
  match q:
    case (+l, f):
      ref.fin(~F, ~H, sk, g0, l, hn(l), x, f(g0, (%Equal.sym(M.Vec(~F), x, N.ofkv(~KI.dnum(), ~F, ~H, g0), hx) : SV.Near(~KI.dnum(), ~F, ~H, SO.nvars(sk), 0n, g0, _, d, DSO.pins_of2(sk), g0)
        RFD.near_self(~KI.dnum(), ~F, ~H, SO.nvars(sk), 0n, g0, d, hd, DSO.pins_of2(sk)))))

def ref.d(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, +g0: List<&2, S.D>, hn: @l: Nat -> {SO.Out.ok(DSO.solve_l2(sk, g0, l)) == False{} : Bool}, +x: M.Vec(~F), +hx: {x == N.ofkv(~KI.dnum(), ~F, ~H, g0) : M.Vec(~F)}, s: &d: O.C(F) -> (O.lt(F, O.zero(F), d) & (&l: Nat -> (@g: List<&2, S.D> -> SV.Near(~KI.dnum(), ~F, ~H, SO.nvars(sk), 0n, g, x, d, DSO.pins_of2(sk), g0) -> ({SO.Out.ok(DSO.solve_l2(sk, g, l)) == True{} : Bool} & BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(DSO.solve_l2(sk, g, l)), SO.Out.gr(DSO.solve_l2(sk, g, l)), x)))))) -> Empty:
  match s:
    case (+d, p):
      match p:
        case (+hd, q):
          ref.l(~F, ~H, sk, g0, hn, x, hx, d, hd, q)

# LAW 11 (ROADMAP solve_refused): if no level certifies the drawing g0,
# then g0 read in F is not a regular solution of the system solved in the
# solver's free variables (with the pins at their drawn values and the
# sides strict, as law 10 reads one)
def solve_refused2(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +dy: {SV.dyadic(SV.mark(SV.reds(DSO.cls_of2(sk)), sk)) == True{} : Bool}, +g0: List<&2, S.D>, hn0: @l: Nat -> {SO.Out.ok(DSO.solve_l2(sk, g0, l)) == False{} : Bool}, +x: M.Vec(~F), +hx: {x == N.ofkv(~KI.dnum(), ~F, ~H, g0) : M.Vec(~F)}, +hl: {M.len(~F, x) == SO.nvars(sk) : Nat}, hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(DSO.cls_of2(sk)), SV.dropped(DSO.cls_of2(sk)))), hs: SV.Strict(~F, x, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(DSO.cls_of2(sk)), SV.ambers(DSO.cls_of2(sk))), sk)), DSO.pins_of2(sk)), hn: SV.Strict(~F, x, DR.ndsides(SV.ents(sk), SV.live_nd(DSO.cls_of2(sk))), DSO.pins_of2(sk)), hr: DV.Regular(~F, x, SV.solved(sk, SV.reds(DSO.cls_of2(sk)), SV.dropped(DSO.cls_of2(sk))), SV.free(SO.nvars(sk), 0n, DSO.pins_of2(sk)))) -> Empty:
  ref.d(~F, ~H, sk, g0, hn0, x, hx, DCP.solve_complete2(~F, ~R, ~H, sk, w, cov, dy, g0, x, hl, (%Equal.sym(M.Vec(~F), x, N.ofkv(~KI.dnum(), ~F, ~H, g0), hx) : SV.PinnedAt(~KI.dnum(), ~F, ~H, _, DSO.pins_of2(sk), g0)
    RFD.pinned_self(~KI.dnum(), ~F, ~H, g0, DSO.pins_of2(sk))), hz, hs, hn, hr))
