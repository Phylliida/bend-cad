# bend-cad: the blocks' inverses under solve_complete (DESIGN §10.4 "C6
# plan", C6b), restated so the gate checks lib/binvpf.bend and
# lib/locpf.bend until the completeness proof imports them. In every
# ordered field F:
# - lib/binvpf.bend: at a regular solution x (in the solver's free
#   variables) every block of the solver's structure has an invertible
#   Jacobian (its equations in its unknowns, sketch numbering):
#   blocks_invertible;
# - lib/locpf.bend: that inverse, read as C5 wants it: the block's local
#   Jacobian (equations renumbered, at its unknowns ++ its parameters'
#   values, all read from x in block order) has an inverse of norm
#   ibd(...): local_inverse.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/deriv.bend as DV
import ../lib/karith.bend as KA
import ../lib/certdef.bend as C
import ../lib/slope.bend as SL
import ../lib/struct.bend as ST
import ../lib/plan.bend as PL
import ../lib/planpf.bend as PP
import ../lib/solve.bend as SO
import ../lib/listpf.bend as L
import ../lib/dfspf.bend as D
import ../lib/maxpf.bend as MX
import ../lib/structpf.bend as SP
import ../lib/keptpf.bend as KP
import ../lib/gjpf.bend as GJ
import ../lib/normpf.bend as NP
import ../lib/binvpf.bend as BI
import ../lib/locpf.bend as LC

def blocks_invertible(~F: O.OField, +sk: SK.Sketch, +ha: {D.adjb(ST.adj(SK.Sketch.eqs(sk)), SO.nvars(sk)) == True{} : Bool}, +x: M.Vec(~F), hr: DV.Regular(~F, x, SO.kept(sk), SV.free(SO.nvars(sk), 0n, SO.pins_of(sk)))) -> BI.BInv(~F, x, SK.Sketch.eqs(sk), SP.kblocks(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk), ST.KD.vm(MX.kvs(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk))), ST.KD.red(MX.kvs(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), SO.nvars(sk), SO.good_of(sk))))):
  BI.block_invs(~F, sk, ha, x, hr)

def local_inverse(~F: O.OField, +x: M.Vec(~F), +vp: List<&2, Nat>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +full: List<&2, E.QExpr>, +es: List<&2, Nat>, +vs: List<&2, Nat>, +hrun: {LC.posrun(vp, vs, o, 0n) == True{} : Bool}, +hvs: {L.subl(vs, vp) == True{} : Bool}, +hn: {SV.len(vs) == n : Nat}, +hr: {LC.rowsok(full, vp, o, n, pars, es) == True{} : Bool}, +hX: {KA.natle(Nat.add(o, n), M.len(~F, LC.xperm(~F, x, vp))) == True{} : Bool}, h: GJ.InvN(~F, DV.jac(~F, x, KP.pickk(full, 0n, es), vs), SV.len(vs))) -> NP.InvB(~F, DV.jac(~F, C.app(~F, PP.ftake(~F, n, PP.fdrop(~F, o, LC.xperm(~F, x, vp))), PP.zmap(~F, PP.ftake(~F, o, LC.xperm(~F, x, vp)), pars)), PL.renames(o, n, pars, PL.reorder(vp, full, es)), ST.iota(n, 0n)), n, LC.ibd(~F, DV.jac(~F, x, KP.pickk(full, 0n, es), vs), SV.len(vs), h)):
  LC.loc_invb(~F, x, vp, o, n, pars, full, es, vs, hrun, hvs, hn, hr, hX, h)
