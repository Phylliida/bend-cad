# bend-cad: the structure the plan follows over the new pass's system
# solved (PLAN-sk13b B7): lib/skdpf.bend over lib/dpass.bend's end state,
# for the solver's completeness. The same lemmas; the invariant at
# the new pass's end (lib/dpasspf.bend: final2_inv) also needs the sketch
# well formed and covered (the closure's bound), so each takes those too.
#
# Generated from tools/drafts/dskdpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/box.bend as BX
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/deriv.bend as DV
import ./listpf.bend as L
import ./struct.bend as ST
import ./plan.bend as PL
import ./dfspf.bend as D
import ./maxpf.bend as MX
import ./gmpf.bend as GM
import ./pass.bend as PA
import ./solvedpf.bend as SP
import ./passpf.bend as PP
import ./perfpf.bend as PF
import ./structpf.bend as STP
import ./keptpf.bend as KP
import ./gjpf.bend as GJ
import ./permpf.bend as PM
import ./binvpf.bend as BI
import ./solve.bend as SO
import ./wfdec.bend as WF
import ./dpass.bend as DPS
import ./dpasspf.bend as DPP
import ./dtotalpf.bend as DTP


def hA_of(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}) -> {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}:
  GM.adjb_dadjs(SK.Sketch.eqs(sk), PA.nvars(sk), ha)

# the blocks over the dependence matching are lib/structpf.bend's
def struct_d(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> {STP.skok(SK.Sketch.eqs(sk), PA.nvars(sk), DPS.solved_pos2(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))))) == True{} : Bool}:
  STP.skel_kd(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk)), SK.Sketch.eqs(sk), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk), DTP.vend_pass2(sk, hA_of(sk, ha), hcov, hwf), ha)

# The system solved, by position
# ------------------------------

def eqat_get(es: List<&2, E.QExpr>, j: Nat) -> {SV.eqat(es, j) == PL.eqget(es, j) : E.QExpr}:
  match es j:
    case Nil{} j:
      {==}
    case Con{e, t} 0n:
      {==}
    case Con{e, t} 1n+k:
      eqat_get(t, k)

def picked_pickk(+es: List<&2, E.QExpr>, xs: List<&2, Nat>) -> {SV.picked(es, xs) == KP.pickk(es, 0n, xs) : List<&2, E.QExpr>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+j, +t}:
      %Equal.sym(E.QExpr, SV.eqat(es, j), PL.eqget(es, j), eqat_get(es, j)) : {Con{_, SV.picked(es, t)} == KP.pickk(es, 0n, Con{j, t}) : List<&2, E.QExpr>}
      %Equal.sym(List<&2, E.QExpr>, SV.picked(es, t), KP.pickk(es, 0n, t), picked_pickk(es, t)) : {Con{PL.eqget(es, j), _} == KP.pickk(es, 0n, Con{j, t}) : List<&2, E.QExpr>}
      {==}

# the system solved is the full system at the pass's positions
def kept_good_d(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> {SV.solved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk))) == KP.pickk(SK.Sketch.eqs(sk), 0n, DPS.solved_pos2(sk)) : List<&2, E.QExpr>}:
  +hi = DPP.final2_inv(sk, hA_of(sk, ha), hcov, hwf)
  Equal.trans(List<&2, E.QExpr>, SV.solved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk))), SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk)), KP.pickk(SK.Sketch.eqs(sk), 0n, DPS.solved_pos2(sk)), SP.solved_end(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk))),
    Equal.trans(List<&2, E.QExpr>, SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk)), PP.ps.B(DPS.final2_st(sk)), KP.pickk(SK.Sketch.eqs(sk), 0n, DPS.solved_pos2(sk)), Equal.sym(List<&2, E.QExpr>, PP.ps.B(DPS.final2_st(sk)), SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk)), PP.pinv_B(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), DPS.final2_st(sk), hi)),
      Equal.trans(List<&2, E.QExpr>, PP.ps.B(DPS.final2_st(sk)), SV.picked(SK.Sketch.eqs(sk), PP.ps.bp(DPS.final2_st(sk))), KP.pickk(SK.Sketch.eqs(sk), 0n, DPS.solved_pos2(sk)), PP.pinv_p(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), DPS.final2_st(sk), hi),
        (%PF.bp_eq(DPS.final2_st(sk)) : {SV.picked(SK.Sketch.eqs(sk), _) == KP.pickk(SK.Sketch.eqs(sk), 0n, DPS.solved_pos2(sk)) : List<&2, E.QExpr>}
          picked_pickk(SK.Sketch.eqs(sk), DPS.solved_pos2(sk))))))

def kept_len_d(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> {SV.neqs(SV.solved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)))) == SV.len(DPS.solved_pos2(sk)) : Nat}:
  %Equal.sym(List<&2, E.QExpr>, SV.solved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk))), KP.pickk(SK.Sketch.eqs(sk), 0n, DPS.solved_pos2(sk)), kept_good_d(sk, ha, hcov, hwf)) : {SV.neqs(_) == SV.len(DPS.solved_pos2(sk)) : Nat}
  KP.pk_len(SK.Sketch.eqs(sk), 0n, DPS.solved_pos2(sk))

# reading the system solved through positions in good is reading the full
# system
def kept_reorder_d(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}, +vp: List<&2, Nat>, ys: List<&2, Nat>, hs: {L.subl(ys, DPS.solved_pos2(sk)) == True{} : Bool}) -> {PL.reorder(vp, SV.solved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk))), ST.positions(ys, DPS.solved_pos2(sk))) == PL.reorder(vp, SK.Sketch.eqs(sk), ys) : List<&2, E.QExpr>}:
  %Equal.sym(List<&2, E.QExpr>, SV.solved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk))), KP.pickk(SK.Sketch.eqs(sk), 0n, DPS.solved_pos2(sk)), kept_good_d(sk, ha, hcov, hwf)) : {PL.reorder(vp, _, ST.positions(ys, DPS.solved_pos2(sk))) == PL.reorder(vp, SK.Sketch.eqs(sk), ys) : List<&2, E.QExpr>}
  KP.re_pick(ys, vp, SK.Sketch.eqs(sk), DPS.solved_pos2(sk), hs)

# The pins
# --------

# the plan's pins are the pass's
def pins_skel(+sk: SK.Sketch) -> {SO.skel.pins(DPS.skel2(sk)) == DPS.pins2(sk) : List<&2, Nat>}:
  MX.ntake_app(ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.allvars(ST.blocks.of(ST.adj(SK.Sketch.eqs(sk)), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.comps(ST.adj(SK.Sketch.eqs(sk)), ST.invert(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), 0n, ST.nones(PA.nvars(sk))), DPS.solved_pos2(sk), ST.len.q(SK.Sketch.eqs(sk))))))

# The blocks' Jacobians
# ---------------------

# a regular point of the system solved, in the free variables the pass
# leaves: the Jacobian in block order is invertible
def regular_blocks_d(~F: O.OField, +sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}, +x: M.Vec(~F), hr: DV.Regular(~F, x, SV.solved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk))), SV.free(PA.nvars(sk), 0n, DPS.pins2(sk))))
  -> GJ.InvN(~F, DV.jac(~F, x, KP.pickk(SK.Sketch.eqs(sk), 0n, ST.alleqs(STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk)))))), ST.allvars(STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk)))))), SV.len(ST.allvars(STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))))))):
  PM.reg_kd(~F, PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk)), SK.Sketch.eqs(sk), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk), x, DTP.vend_pass2(sk, hA_of(sk, ha), hcov, hwf), struct_d(sk, ha, hcov, hwf),
    (%kept_good_d(sk, ha, hcov, hwf) : DV.Regular(~F, x, _, SV.free(PA.nvars(sk), 0n, ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk)))))
      hr))

# and every block's Jacobian is invertible
def block_invs_d(~F: O.OField, +sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}, +x: M.Vec(~F), hr: DV.Regular(~F, x, SV.solved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk))), SV.free(PA.nvars(sk), 0n, DPS.pins2(sk)))) -> BI.BInv(~F, x, SK.Sketch.eqs(sk), STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))))):
  +sf = STP.skok_sf(SK.Sketch.eqs(sk), PA.nvars(sk), DPS.solved_pos2(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk)))), struct_d(sk, ha, hcov, hwf))
  BI.inv_blocks(~F, x, SK.Sketch.eqs(sk), STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk)))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), STP.sfacts_ch(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk)))), sf), STP.sfacts_vpd(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk)))), sf), STP.sfacts_lk(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk)))), sf),
    regular_blocks_d(~F, sk, ha, hcov, hwf, x, hr))
