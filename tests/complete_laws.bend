# Completeness (ROADMAP.bend: solve_complete and solve_refused) with its
# proofs (lib/dcompletepf.bend, lib/drefusedpf.bend), restated so the gate
# checks them and tools/lawsync.py checks the statements match ROADMAP's.
# Its own gate root (the completeness proof is the longest to check).

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
import ../lib/dcompletepf.bend as DCP
import ../lib/drefusedpf.bend as DRP

def solve_complete(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, dy: {SV.dyadic(SV.mark(SV.reds(SO.cls_of(sk)), sk)) == True{} : Bool}, +g0: List<&2, S.D>, +x: M.Vec(~F), hl: {M.len(~F, x) == SO.nvars(sk) : Nat}, hp: SV.PinnedAt(~KI.dnum(), ~F, ~H, x, SO.pins_of(sk), g0), hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(SO.cls_of(sk)), SV.dropped(SO.cls_of(sk)))), hs: SV.Strict(~F, x, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(SO.cls_of(sk)), SV.ambers(SO.cls_of(sk))), sk)), SO.pins_of(sk)), hn: SV.Strict(~F, x, DR.ndsides(SV.ents(sk), SV.live_nd(SO.cls_of(sk))), SO.pins_of(sk)), hr: DV.Regular(~F, x, SV.solved(sk, SV.reds(SO.cls_of(sk)), SV.dropped(SO.cls_of(sk))), SV.free(SO.nvars(sk), 0n, SO.pins_of(sk)))) -> (&d: O.C(F) -> (O.lt(F, O.zero(F), d) & (&l: Nat -> (@g: List<&2, S.D> -> SV.Near(~KI.dnum(), ~F, ~H, SO.nvars(sk), 0n, g, x, d, SO.pins_of(sk), g0) -> ({SO.Out.ok(SO.solve_l(sk, g, l)) == True{} : Bool} & BX.inbox(~KI.dnum(), ~F, ~H, SO.Out.gc(SO.solve_l(sk, g, l)), SO.Out.gr(SO.solve_l(sk, g, l)), x)))))):
  DCP.solve_complete2(~F, ~R, ~H, sk, w, cov, dy, g0, x, hl, hp, hz, hs, hn, hr)

def solve_refused(~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<KI.dnum(), F>, +sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, dy: {SV.dyadic(SV.mark(SV.reds(SO.cls_of(sk)), sk)) == True{} : Bool}, +g0: List<&2, S.D>, hn0: @l: Nat -> {SO.Out.ok(SO.solve_l(sk, g0, l)) == False{} : Bool}, +x: M.Vec(~F), hx: {x == N.ofkv(~KI.dnum(), ~F, ~H, g0) : M.Vec(~F)}, hl: {M.len(~F, x) == SO.nvars(sk) : Nat}, hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(SO.cls_of(sk)), SV.dropped(SO.cls_of(sk)))), hs: SV.Strict(~F, x, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(SO.cls_of(sk)), SV.ambers(SO.cls_of(sk))), sk)), SO.pins_of(sk)), hn: SV.Strict(~F, x, DR.ndsides(SV.ents(sk), SV.live_nd(SO.cls_of(sk))), SO.pins_of(sk)), hr: DV.Regular(~F, x, SV.solved(sk, SV.reds(SO.cls_of(sk)), SV.dropped(SO.cls_of(sk))), SV.free(SO.nvars(sk), 0n, SO.pins_of(sk)))) -> Empty:
  DRP.solve_refused2(~F, ~R, ~H, sk, w, cov, dy, g0, hn0, x, hx, hl, hz, hs, hn, hr)
