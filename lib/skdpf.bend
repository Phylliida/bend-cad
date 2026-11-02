# bend-cad: the structure the plan follows over the system solved
# (lib/pass.bend: skel; PLAN-sk13a S5). Proofs only.
#
# Since the sk-13b switch (2026-11-02), what this file proved about
# sk-13a's pass, Honest or solver is proven in lib/dskdpf.bend; what is
# left here is what that proof reuses, and the description below is of
# the sk-13a proof.
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

# The pins
# --------

# the plan's pins are the pass's
def pins_skel(+sk: SK.Sketch) -> {SO.skel.pins(PA.skel(sk)) == PA.pins(sk) : List<&2, Nat>}:
  MX.ntake_app(ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.allvars(ST.blocks.of(ST.adj(SK.Sketch.eqs(sk)), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), ST.comps(ST.adj(SK.Sketch.eqs(sk)), ST.invert(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.solved_pos(sk))), 0n, ST.nones(PA.nvars(sk))), PA.solved_pos(sk), ST.len.q(SK.Sketch.eqs(sk))))))

# The blocks' Jacobians
# ---------------------
