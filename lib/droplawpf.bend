# bend-cad: law 6, solve_drop (PLAN-sk13a S6): in every ordered field,
# wherever the solved equations hold, every dropped equation holds. Proofs
# only.
#
# The pass's own answer passes the verdict's exact checks (lib/ckpf.bend:
# ck_pass), among them the drop check: each dropped equation is a
# combination of earlier solved ones, so it is 0 wherever they are
# (lib/vrdpf.bend: dropped_zero).

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ./listpf.bend as L
import ./wfcpf.bend as WC
import ./covpf.bend as CV
import ./gmpf.bend as GM
import ./verdict.bend as VD
import ./ckpf.bend as CKP
import ./vrdpf.bend as VR
import ./solve.bend as SO

# every equation picked at a dropped position is 0
def zp.go(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +hz: SK.Zeros(~F, x, SV.solved.go(es, own, R, D, 0n)), +cls: List<&2, SV.Class>, +hd: {VD.dck(es, own, R, D, cls) == True{} : Bool}, js: List<&2, Nat>, +hs: {L.subl(js, SV.dropped(cls)) == True{} : Bool}) -> SK.Zeros(~F, x, SV.picked(es, js)):
  match js:
    case Nil{}:
      Unit{}
    case Con{+j, +t}:
      (VR.dropped_zero(~F, x, es, own, R, D, hz, cls, j, L.subl_hd(j, t, SV.dropped(cls), hs), hd), zp.go(~F, x, es, own, R, D, hz, cls, hd, t, L.subl_tl(j, t, SV.dropped(cls), hs)))

# LAW 6 (ROADMAP solve_drop): wherever the system solved holds, every
# dropped equation holds
def solve_drop(~F: O.OField, +sk: SK.Sketch, w: SK.Sketch.wf(sk), cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat, +x: M.Vec(~F), hz: SK.Zeros(~F, x, SV.solved(sk, SV.reds(SO.Out.cls(SO.solve_l(sk, g0, l))), SV.dropped(SO.Out.cls(SO.solve_l(sk, g0, l)))))) -> SK.Zeros(~F, x, SV.picked(SK.Sketch.eqs(sk), SV.dropped(SO.Out.cls(SO.solve_l(sk, g0, l))))):
  +cls = SO.Out.cls(SO.solve_l(sk, g0, l))
  +hwf = WC.wf_dec_ok(sk, w)
  +ha = CV.cov(sk, SO.nvars(sk), cov, hwf)
  +hex = CKP.ck_pass(sk, GM.adjb_dadjs(SK.Sketch.eqs(sk), SO.nvars(sk), ha))
  zp.go(~F, x, SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(cls), SV.dropped(cls), hz, cls, L.band_l(VD.dck(SK.Sketch.eqs(sk), SV.owners(sk), SV.reds(cls), SV.dropped(cls), cls), VD.ack(sk, SV.reds(cls), cls, 0n), hex), SV.dropped(cls), L.subl_refl(SV.dropped(cls)))
