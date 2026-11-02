# Completeness for the draft solver (PLAN-sk13b B7): solve_complete and
# solve_refused as tools/drafts/roadmap13b.draft states them (with the nd
# sides strict, hn), solve_l read as the draft solver's (lib/dsolve.bend),
# proven in lib/dcompletepf.bend and lib/drefusedpf.bend; restated here so
# the gate checks them. Its own gate root (the completeness proof is the
# longest to check).

import Base
import ../spec/num.bend as S
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/real.bend as CR
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/deriv.bend as DV
import ../spec/solve.bend as SV
import ../spec/dir.bend as DR
import ../lib/kinst.bend as KI
import ../lib/solve.bend as SO
import ../lib/dsolve.bend as DSO
import ../lib/dcompletepf.bend as DCP
import ../lib/drefusedpf.bend as DRP

def b7_complete(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, dy: {SV.dyadic(SV.mark(SV.reds(DSO.cls_of2(sk)), sk)) == True{} : Bool}, +g0: List<&2, S.D>, +x: M.Vec(~F), hl: {M.len(~F, x) == SO.nvars(sk) : Nat}, hp: SV.PinnedAt(~KI.dnum(), ~F, ~H, x, DSO.pins_of2(sk), g0), hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(DSO.cls_of2(sk)), SV.dropped(DSO.cls_of2(sk)))), hs: SV.Strict(~F, x, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(DSO.cls_of2(sk)), SV.ambers(DSO.cls_of2(sk))), sk)), DSO.pins_of2(sk)), hn: SV.Strict(~F, x, DR.ndsides(SV.ents(sk), SV.live_nd(DSO.cls_of2(sk))), DSO.pins_of2(sk)), hr: DV.Regular(~F, x, SV.solved(sk, SV.reds(DSO.cls_of2(sk)), SV.dropped(DSO.cls_of2(sk))), SV.free(SO.nvars(sk), 0n, DSO.pins_of2(sk)))) -> (&d: O.C(F) -> (O.lt(F, O.zero(F), d) & (&l: Nat -> (@g: List<&2, S.D> -> SV.Near(~KI.dnum(), ~F, ~H, SO.nvars(sk), 0n, g, x, d, DSO.pins_of2(sk), g0) -> ({SO.Out.ok(DSO.solve_l2(sk, g, l)) == True{} : Bool} & BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(DSO.solve_l2(sk, g, l)), SO.Out.gr(DSO.solve_l2(sk, g, l)), x)))))):
  DCP.solve_complete2(~F, ~R, ~H, sk, w, cov, dy, g0, x, hl, hp, hz, hs, hn, hr)

def b7_refused(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, dy: {SV.dyadic(SV.mark(SV.reds(DSO.cls_of2(sk)), sk)) == True{} : Bool}, +g0: List<&2, S.D>, hn0: @l: Nat -> {SO.Out.ok(DSO.solve_l2(sk, g0, l)) == False{} : Bool}, +x: M.Vec(~F), hx: {x == N.ofkv(~KI.dnum(), ~F, ~H, g0) : M.Vec(~F)}, hl: {M.len(~F, x) == SO.nvars(sk) : Nat}, hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(DSO.cls_of2(sk)), SV.dropped(DSO.cls_of2(sk)))), hs: SV.Strict(~F, x, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(DSO.cls_of2(sk)), SV.ambers(DSO.cls_of2(sk))), sk)), DSO.pins_of2(sk)), hn: SV.Strict(~F, x, DR.ndsides(SV.ents(sk), SV.live_nd(DSO.cls_of2(sk))), DSO.pins_of2(sk)), hr: DV.Regular(~F, x, SV.solved(sk, SV.reds(DSO.cls_of2(sk)), SV.dropped(DSO.cls_of2(sk))), SV.free(SO.nvars(sk), 0n, DSO.pins_of2(sk)))) -> Empty:
  DRP.solve_refused2(~F, ~R, ~H, sk, w, cov, dy, g0, hn0, x, hx, hl, hz, hs, hn, hr)
