# bend-cad: the structure the plan follows over the system solved
# (lib/pass.bend: skel; PLAN-sk13a S5). Proofs only.
#
# The pass's positions good (its bp) and their matching by dependence
# give the variable side's end (lib/perfpf.bend: vend_pass), and
# lib/structpf.bend's blocks are built from it with the syntactic
# adjacency, as the plan checker reads equations: vside does not mention
# the adjacency, so skel_kd, reg_kd and inv_blocks apply as they did to
# the red stage's matching. And the system solved is the full system at
# good (kept_good_d), so reading it through positions in good is reading
# the full system (kept_reorder_d); the plan's pins are the pass's pins
# (pins_skel); a regular point of the system solved in the free
# variables has every block's Jacobian invertible (block_invs_d).
#
# Generated from tools/drafts/skdpf.draft by tools/expand.py; edit the
# draft.

import Base
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


def hA_of(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}) -> {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}:
  GM.adjb_dadjs(SK.Sketch.eqs(sk), PA.nvars(sk), ha)

# the blocks over the dependence matching are lib/structpf.bend's
def struct_d(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}) -> {STP.skok(SK.Sketch.eqs(sk), PA.nvars(sk), PA.solved_pos(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))))) == True{} : Bool}:
  STP.skel_kd(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk)), SK.Sketch.eqs(sk), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk), PF.vend_pass(sk, hA_of(sk, ha)), ha)

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
def kept_good_d(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}) -> {SV.solved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk))) == KP.pickk(SK.Sketch.eqs(sk), 0n, PA.solved_pos(sk)) : List<&2, E.QExpr>}:
  +hi = PF.final_inv.a(sk, hA_of(sk, ha))
  Equal.trans(List<&2, E.QExpr>, SV.solved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk))), SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk)), KP.pickk(SK.Sketch.eqs(sk), 0n, PA.solved_pos(sk)), SP.solved_end(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk))),
    Equal.trans(List<&2, E.QExpr>, SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk)), PP.ps.B(PA.final_st(sk)), KP.pickk(SK.Sketch.eqs(sk), 0n, PA.solved_pos(sk)), Equal.sym(List<&2, E.QExpr>, PP.ps.B(PA.final_st(sk)), SV.presolved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk)), PP.pinv_B(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PA.final_st(sk), hi)),
      Equal.trans(List<&2, E.QExpr>, PP.ps.B(PA.final_st(sk)), SV.picked(SK.Sketch.eqs(sk), PP.ps.bp(PA.final_st(sk))), KP.pickk(SK.Sketch.eqs(sk), 0n, PA.solved_pos(sk)), PP.pinv_p(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)), SV.ncons(sk), PA.final_st(sk), hi),
        (%PF.bp_eq(PA.final_st(sk)) : {SV.picked(SK.Sketch.eqs(sk), _) == KP.pickk(SK.Sketch.eqs(sk), 0n, PA.solved_pos(sk)) : List<&2, E.QExpr>}
          picked_pickk(SK.Sketch.eqs(sk), PA.solved_pos(sk))))))

def kept_len_d(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}) -> {SV.neqs(SV.solved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk)))) == SV.len(PA.solved_pos(sk)) : Nat}:
  %Equal.sym(List<&2, E.QExpr>, SV.solved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk))), KP.pickk(SK.Sketch.eqs(sk), 0n, PA.solved_pos(sk)), kept_good_d(sk, ha)) : {SV.neqs(_) == SV.len(PA.solved_pos(sk)) : Nat}
  KP.pk_len(SK.Sketch.eqs(sk), 0n, PA.solved_pos(sk))

# reading the system solved through positions in good is reading the full
# system
def kept_reorder_d(+sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +vp: List<&2, Nat>, ys: List<&2, Nat>, hs: {L.subl(ys, PA.solved_pos(sk)) == True{} : Bool}) -> {PL.reorder(vp, SV.solved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk))), ST.positions(ys, PA.solved_pos(sk))) == PL.reorder(vp, SK.Sketch.eqs(sk), ys) : List<&2, E.QExpr>}:
  %Equal.sym(List<&2, E.QExpr>, SV.solved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk))), KP.pickk(SK.Sketch.eqs(sk), 0n, PA.solved_pos(sk)), kept_good_d(sk, ha)) : {PL.reorder(vp, _, ST.positions(ys, PA.solved_pos(sk))) == PL.reorder(vp, SK.Sketch.eqs(sk), ys) : List<&2, E.QExpr>}
  KP.re_pick(ys, vp, SK.Sketch.eqs(sk), PA.solved_pos(sk), hs)

# The pins
# --------

# the plan's pins are the pass's
def pins_skel(+sk: SK.Sketch) -> {SO.skel.pins(PA.skel(sk)) == PA.pins(sk) : List<&2, Nat>}:
  MX.ntake_app(ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.allvars(ST.blocks.of(ST.adj(SK.Sketch.eqs(sk)), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.comps(ST.adj(SK.Sketch.eqs(sk)), ST.invert(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), 0n, ST.nones(PA.nvars(sk))), PA.solved_pos(sk), ST.len.q(SK.Sketch.eqs(sk))))))

# The blocks' Jacobians
# ---------------------

# a regular point of the system solved, in the free variables the pass
# leaves: the Jacobian in block order is invertible
def regular_blocks_d(~F: O.OField, +sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +x: M.Vec(~F), hr: DV.Regular(~F, x, SV.solved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk))), SV.free(PA.nvars(sk), 0n, PA.pins(sk))))
  -> GJ.InvN(~F, DV.jac(~F, x, KP.pickk(SK.Sketch.eqs(sk), 0n, ST.alleqs(STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk)))))), ST.allvars(STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk)))))), SV.len(ST.allvars(STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))))))):
  PM.reg_kd(~F, PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk)), SK.Sketch.eqs(sk), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk), x, PF.vend_pass(sk, hA_of(sk, ha)), struct_d(sk, ha),
    (%kept_good_d(sk, ha) : DV.Regular(~F, x, _, SV.free(PA.nvars(sk), 0n, ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk)))))
      hr))

# and every block's Jacobian is invertible
def block_invs_d(~F: O.OField, +sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +x: M.Vec(~F), hr: DV.Regular(~F, x, SV.solved(sk, SV.reds(PA.classes(sk)), SV.dropped(PA.classes(sk))), SV.free(PA.nvars(sk), 0n, PA.pins(sk)))) -> BI.BInv(~F, x, SK.Sketch.eqs(sk), STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))))):
  +sf = STP.skok_sf(SK.Sketch.eqs(sk), PA.nvars(sk), PA.solved_pos(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk)))), struct_d(sk, ha))
  BI.inv_blocks(~F, x, SK.Sketch.eqs(sk), STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk)))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), STP.sfacts_ch(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk)))), sf), STP.sfacts_vpd(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk)))), sf), STP.sfacts_lk(ST.adj(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), STP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk)))), sf),
    regular_blocks_d(~F, sk, ha, x, hr))
