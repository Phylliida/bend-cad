# bend-cad: the blocks in turn under solve_complete (DESIGN §10.4 "C6
# plan", C6c), restated so the gate checks lib/pblkpf.bend until the
# completeness proof imports it. In every ordered field F, for a solution
# x of the kept equations whose blocks are invertible (lib/binvpf.bend's
# BInv), a drawing g near x, d <= h and the smallness t qch < 1: from
# offset o with the box so far (gc, gr) holding x (block order) with
# radii in [0, h T], the solver's pblocks returns PBOk, the plan
# checker's walk accepts the final box, which extends (gc, gr), has nv
# entries, holds x and has radii at most h tch (blocks_in_turn).

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/deriv.bend as DV
import ../lib/karith.bend as KA
import ../lib/kinst.bend as KI
import ../lib/certdef.bend as C
import ../lib/numer.bend as NU
import ../lib/struct.bend as ST
import ../lib/plan.bend as PL
import ../lib/planpf.bend as PP
import ../lib/fvec.bend as FV
import ../lib/listpf.bend as L
import ../lib/gjpf.bend as GJ
import ../lib/apxpf.bend as AP
import ../lib/nwtpf.bend as NW
import ../lib/keptpf.bend as KP
import ../lib/structpf.bend as SP
import ../lib/maxpf.bend as MX
import ../lib/binvpf.bend as BI
import ../lib/locpf.bend as LC
import ../lib/pblkpf.bend as PB

def blocks_in_turn(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +full: List<&2, E.QExpr>, +good: List<&2, Nat>, +vp: List<&2, Nat>, +nv: Nat, +vm: List<&2, Maybe<&2, Nat>>, +x: M.Vec(~F), +g: List<&2, S.D>, +g0: List<&2, S.D>, +pins: List<&2, Nat>, +p: Nat, +q2: Nat, +hp2: {p == 1n+(1n+q2) : Nat}, +d: O.C(F), +hd0: O.le(~F, O.zero(F), d), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hdy: {SV.dyeqs(KP.pickk(full, 0n, good)) == True{} : Bool}, +hzg: SK.Zeros(~F, x, KP.pickk(full, 0n, good)), +hN: SV.Near(~KI.dnum(), ~F, ~H, nv, 0n, g, x, d, pins, g0), +hvd: {SV.distinct(vp) == True{} : Bool}, +hvl: {SV.len(vp) == nv : Nat}, kb: List<&2, ST.SB>, +binv: BI.BInv(~F, x, full, kb), +known: List<&2, Nat>, +o: Nat, +ho: {SV.len(known) == o : Nat}, +hvp: {vp == ST.app(known, ST.allvars(kb)) : List<&2, Nat>}, +hsw: {SP.swalk(ST.renum.bs(ST.skbs(kb, ST.adj(full), vp), good), PL.reorder(vp, full, ST.alleqs(kb)), o, nv) == True{} : Bool}, +hch: {SP.vchain(kb, known, ST.adj(full)) == True{} : Bool}, +hlk: {SP.lkb(vm, kb) == True{} : Bool}, +hgs: {L.subl(ST.alleqs(kb), good) == True{} : Bool}, +hfr: {MX.disj(ST.allvars(kb), pins) == True{} : Bool}, +hbe: {SV.below(ST.allvars(kb), nv) == True{} : Bool}, +gc: List<&2, S.D>, +gr: List<&2, S.D>, +hlc: {KA.klen(~KI.dnum(), gc) == o : Nat}, +hlr: {KA.klen(~KI.dnum(), gr) == o : Nat}, +hpb: PP.pbox(~KI.dnum(), ~F, ~H, gc, gr, o, PP.ftake(~F, o, LC.xperm(~F, x, vp))), +hrn: FV.rnn(~F, M.ofdv(~F, gr)), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hrb: M.vbnd.all(~F, M.ofdv(~F, gr), O.mul(F, NW.hnw(~F, p), tt)), +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), PB.qch(~F, full, good, vp, x, kb, binv, o, tt)), O.one(F))) -> PB.PG(~F, ~H, vp, nv, x, p, o, gc, gr, PL.reorder(vp, full, ST.alleqs(kb)), PB.tch(~F, full, good, vp, x, kb, binv, o, tt), NU.pblocks(ST.renum.bs(ST.skbs(kb, ST.adj(full), vp), good), NU.bcert(ST.renum.bs(ST.skbs(kb, ST.adj(full), vp), good), PL.reorder(vp, full, ST.alleqs(kb)), NU.dpick(g, vp), p, o, gc, gr), PL.reorder(vp, full, ST.alleqs(kb)), NU.dpick(g, vp), p, o, gc, gr, Nil{})):
  PB.pb_ok(~F, ~H, full, good, vp, nv, vm, x, g, g0, pins, p, q2, hp2, d, hd0, hdh, hdy, hzg, hN, hvd, hvl, kb, binv, known, o, ho, hvp, hsw, hch, hlk, hgs, hfr, hbe, gc, gr, hlc, hlr, hpb, hrn, tt, htt, hrb, hsq)
