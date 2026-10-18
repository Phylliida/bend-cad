# bend-cad: Newton in a block, for solve_complete (DESIGN §10.4, C5b).
# Proofs only.
#
# The block's equations f(y; z) vanish at x_b ++ x_z, where the Jacobian
# in the unknowns has an inverse of norm at most b. The solver runs Newton
# at the parameters' centers pc from the drawing y0 (within d of x_b, the
# centers within rho of x_z). Each step is y' = y - A f(y; pc) + e with
# |e| <= h = 2^-(p+1) and A from C4's elimination (lib/apxpf.bend). The
# first step lands within E1 of x_b. The second moves at most 8h, the
# settle test, even when rho is many units of h: the parameter offset is
# the same in both steps and cancels, leaving second-order terms. So
# newton returns y1 or y2, within EN = 8h + E1 of x_b.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/box.bend as BX
import ../spec/knum.bend as N
import ../spec/deriv.bend as DV
import ./karith.bend as KA
import ./kball.bend as KB
import ./cert.bend as CK
import ./certdef.bend as C
import ./certpf.bend as CP
import ./kinst.bend as KI
import ./numer.bend as NU
import ./struct.bend as ST
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./fmat.bend as FM
import ./fvec.bend as FV
import ./dmat.bend as DM
import ./gjpf.bend as GJ
import ./normpf.bend as NP
import ./dgjpf.bend as DG
import ./bndpf.bend as BP
import ./roundpf.bend as RP
import ./apxpf.bend as AP

# The block in F
# --------------

# Newton's rounding: 2^-(p+1)
def hnw(~F: O.OField, +p: Nat) -> O.C(F):
  M.ofd(~F, S.D{S.Zpos{S.XH{}}, 1n+p})

# y's point: y ++ pc
def pt(~F: O.OField, +y: List<&2, S.D>, +pc: List<&2, S.D>) -> M.Vec(~F):
  C.app(~F, M.ofdv(~F, y), M.ofdv(~F, pc))

def gv(~F: O.OField, +eqs: List<&2, E.QExpr>, +y: List<&2, S.D>, +pc: List<&2, S.D>) -> M.Vec(~F):
  C.fvals(~F, eqs, pt(~F, y, pc))

# the Jacobian in the n unknowns at x
def jc(~F: O.OField, +eqs: List<&2, E.QExpr>, +n: Nat, +x: M.Vec(~F)) -> M.Mat(~F):
  DV.jac(~F, x, eqs, ST.iota(n, 0n))

# One step
# --------

def ofd_sub(~F: O.OField, +y: S.D, +d: S.D) -> {M.ofd(~F, S.D.sub(y, d)) == O.add(F, M.ofd(~F, y), O.neg(F, M.ofd(~F, d))) : O.C(F)}:
  %Equal.sym(O.C(F), O.neg(F, M.ofd(~F, d)), M.ofd(~F, S.D.neg(d)), DM.ofd_neg(~F, d)) : {M.ofd(~F, S.D.sub(y, d)) == O.add(F, M.ofd(~F, y), _) : O.C(F)}
  Equal.sym(O.C(F), O.add(F, M.ofd(~F, y), M.ofd(~F, S.D.neg(d))), M.ofd(~F, S.D.add(y, S.D.neg(d))), DM.ofd_add(~F, y, S.D.neg(d)))

# the rounded step y - d is within h of y - d, entry by entry
def round_ok(~F: O.OField, ys: List<&2, S.D>, ds: List<&2, S.D>, +p: Nat, hl: {M.len(~F, M.ofdv(~F, ys)) == M.len(~F, M.ofdv(~F, ds)) : Nat}) -> M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, NU.nstep.round(ys, ds, p)), BX.vsub(~F, M.ofdv(~F, ys), M.ofdv(~F, ds))), hnw(~F, p)):
  match ys ds:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} Con{d, dt}:
      FO.absurd(M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, NU.nstep.round(Nil{}, Con{d, dt}, p)), BX.vsub(~F, Nil{}, M.ofdv(~F, Con{d, dt}))), hnw(~F, p)), FV.zero_ne(M.len(~F, M.ofdv(~F, dt)), hl))
    case Con{y, yt} Nil{}:
      FO.absurd(M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, NU.nstep.round(Con{y, yt}, Nil{}, p)), BX.vsub(~F, M.ofdv(~F, Con{y, yt}), Nil{})), hnw(~F, p)), FV.succ_ne(M.len(~F, M.ofdv(~F, yt)), hl))
    case Con{+y, +yt} Con{+d, +dt}:
      ((%ofd_sub(~F, y, d) : M.bnd(~F, O.add(F, M.ofd(~F, NU.dround(S.D.sub(y, d), p)), O.neg(F, _)), hnw(~F, p))
          RP.dround_err(~F, S.D.sub(y, d), p)),
       round_ok(~F, yt, dt, p, FV.succ_inj(M.len(~F, M.ofdv(~F, yt)), M.len(~F, M.ofdv(~F, dt)), hl)))

def len_round(~F: O.OField, ys: List<&2, S.D>, ds: List<&2, S.D>, +p: Nat) -> {M.len(~F, M.ofdv(~F, NU.nstep.round(ys, ds, p))) == M.len(~F, M.ofdv(~F, ys)) : Nat}:
  match ys ds:
    case Nil{} ds:
      {==}
    case Con{+y, +yt} Nil{}:
      %Equal.sym(Nat, M.len(~F, M.ofdv(~F, NU.nstep.round(yt, Nil{}, p))), M.len(~F, M.ofdv(~F, yt)), len_round(~F, yt, Nil{}, p)) : {1n+_ == 1n+M.len(~F, M.ofdv(~F, yt)) : Nat}
      {==}
    case Con{+y, +yt} Con{+d, +dt}:
      %Equal.sym(Nat, M.len(~F, M.ofdv(~F, NU.nstep.round(yt, dt, p))), M.len(~F, M.ofdv(~F, yt)), len_round(~F, yt, dt, p)) : {1n+_ == 1n+M.len(~F, M.ofdv(~F, yt)) : Nat}
      {==}

# a step from y to y2: A good for the Jacobian at y's point, n rows, and
# y2 within h of y - A f(y; pc)
def Step(~F: O.OField, +n: Nat, +eqs: List<&2, E.QExpr>, +pc: List<&2, S.D>, +ea: O.C(F), +p: Nat, +y: List<&2, S.D>, +y2: List<&2, S.D>) -> Data:
  Sigma<&2, &2, M.Mat(~F), A => M.Both(DG.agood(~F, n, jc(~F, eqs, n, pt(~F, y, pc)), A, ea), M.Both({GJ.nrows(~F, A) == n : Nat}, M.Both(M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, y2), BX.vsub(~F, M.ofdv(~F, y), M.matvec(~F, A, gv(~F, eqs, y, pc)))), hnw(~F, p)), {M.len(~F, M.ofdv(~F, y2)) == n : Nat})))>

# what a step's outcome promises: never singular, and a Step
def NSR(~F: O.OField, +n: Nat, +eqs: List<&2, E.QExpr>, +pc: List<&2, S.D>, +ea: O.C(F), +p: Nat, +y: List<&2, S.D>, r: Maybe<&2, List<&2, S.D>>) -> Type:
  match r:
    case None{}:
      Empty
    case Some{y2}:
      Step(~F, n, eqs, pc, ea, p, y, y2)

def step_rnd(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +p: Nat, +y: List<&2, S.D>, +inv: List<&2, List<&2, S.D>>, +hl: {M.len(~F, M.ofdv(~F, y)) == M.len(~F, M.ofdv(~F, NU.dmatvec(inv, NU.vals(eqs, NU.dapp(y, pc))))) : Nat}) -> M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, NU.nstep.round(y, NU.dmatvec(inv, NU.vals(eqs, NU.dapp(y, pc))), p)), BX.vsub(~F, M.ofdv(~F, y), M.matvec(~F, M.ofdm(~F, inv), gv(~F, eqs, y, pc)))), hnw(~F, p)):
  +rd = M.ofdv(~F, NU.nstep.round(y, NU.dmatvec(inv, NU.vals(eqs, NU.dapp(y, pc))), p))
  %AP.dapp_ofd(~F, y, pc) : M.vbnd.all(~F, BX.vsub(~F, rd, BX.vsub(~F, M.ofdv(~F, y), M.matvec(~F, M.ofdm(~F, inv), C.fvals(~F, eqs, _)))), hnw(~F, p))
  %AP.dvals_ofd(~F, ~H, eqs, NU.dapp(y, pc), hh) : M.vbnd.all(~F, BX.vsub(~F, rd, BX.vsub(~F, M.ofdv(~F, y), M.matvec(~F, M.ofdm(~F, inv), _))), hnw(~F, p))
  %AP.dmatvec_ofd(~F, inv, NU.vals(eqs, NU.dapp(y, pc))) : M.vbnd.all(~F, BX.vsub(~F, rd, BX.vsub(~F, M.ofdv(~F, y), _)), hnw(~F, p))
  round_ok(~F, y, NU.dmatvec(inv, NU.vals(eqs, NU.dapp(y, pc))), p, hl)

def step_len(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +pc: List<&2, S.D>, +y: List<&2, S.D>, +ly: {M.len(~F, M.ofdv(~F, y)) == n : Nat}, +inv: List<&2, List<&2, S.D>>, +hr: {GJ.nrows(~F, M.ofdm(~F, inv)) == n : Nat}) -> {M.len(~F, M.ofdv(~F, y)) == M.len(~F, M.ofdv(~F, NU.dmatvec(inv, NU.vals(eqs, NU.dapp(y, pc))))) : Nat}:
  %Equal.sym(M.Vec(~F), M.ofdv(~F, NU.dmatvec(inv, NU.vals(eqs, NU.dapp(y, pc)))), M.matvec(~F, M.ofdm(~F, inv), M.ofdv(~F, NU.vals(eqs, NU.dapp(y, pc)))), AP.dmatvec_ofd(~F, inv, NU.vals(eqs, NU.dapp(y, pc)))) : {M.len(~F, M.ofdv(~F, y)) == M.len(~F, _) : Nat}
  %GJ.len_matvec(~F, M.ofdm(~F, inv), M.ofdv(~F, NU.vals(eqs, NU.dapp(y, pc)))) : {M.len(~F, M.ofdv(~F, y)) == _ : Nat}
  Equal.trans(Nat, M.len(~F, M.ofdv(~F, y)), n, GJ.nrows(~F, M.ofdm(~F, inv)), ly, Equal.sym(Nat, GJ.nrows(~F, M.ofdm(~F, inv)), n, hr))

def nstep_ok.some(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +ea: O.C(F), +p: Nat, +y: List<&2, S.D>, +ly: {M.len(~F, M.ofdv(~F, y)) == n : Nat}, +inv: List<&2, List<&2, S.D>>, hm: M.Both({GJ.nrows(~F, M.ofdm(~F, inv)) == n : Nat}, DG.agood(~F, n, jc(~F, eqs, n, pt(~F, y, pc)), M.ofdm(~F, inv), ea))) -> Step(~F, n, eqs, pc, ea, p, y, NU.nstep.round(y, NU.dmatvec(inv, NU.vals(eqs, NU.dapp(y, pc))), p)):
  (+h1, h2) = hm
  (M.ofdm(~F, inv), (h2, (h1, (step_rnd(~F, ~H, n, eqs, hh, pc, p, y, inv, step_len(~F, ~H, n, eqs, pc, y, ly, inv, h1)),
    Equal.trans(Nat, M.len(~F, M.ofdv(~F, NU.nstep.round(y, NU.dmatvec(inv, NU.vals(eqs, NU.dapp(y, pc))), p))), M.len(~F, M.ofdv(~F, y)), n, len_round(~F, y, NU.dmatvec(inv, NU.vals(eqs, NU.dapp(y, pc))), p), ly)))))

def nstep_ok.go(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +ea: O.C(F), +p: Nat, +y: List<&2, S.D>, +ly: {M.len(~F, M.ofdv(~F, y)) == n : Nat}, m: Maybe<&2, List<&2, List<&2, S.D>>>, hm: DG.dinv_res(~F, n, jc(~F, eqs, n, pt(~F, y, pc)), ea, m)) -> NSR(~F, n, eqs, pc, ea, p, y, NU.nstep.of(y, m, NU.vals(eqs, NU.dapp(y, pc)), p)):
  match m:
    case None{}:
      hm
    case Some{+inv}:
      nstep_ok.some(~F, ~H, n, eqs, hh, pc, ea, p, y, ly, inv, hm)

def invb_dapp(~F: O.OField, +n: Nat, +eqs: List<&2, E.QExpr>, +pc: List<&2, S.D>, +y: List<&2, S.D>, +b: O.C(F), hJ: NP.InvB(~F, jc(~F, eqs, n, pt(~F, y, pc)), n, b)) -> NP.InvB(~F, DV.jac(~F, M.ofdv(~F, NU.dapp(y, pc)), eqs, ST.iota(n, 0n)), n, b):
  %Equal.sym(M.Vec(~F), M.ofdv(~F, NU.dapp(y, pc)), C.app(~F, M.ofdv(~F, y), M.ofdv(~F, pc)), AP.dapp_ofd(~F, y, pc)) : NP.InvB(~F, DV.jac(~F, _, eqs, ST.iota(n, 0n)), n, b)
  hJ

def mall_dapp(~F: O.OField, +n: Nat, +eqs: List<&2, E.QExpr>, +pc: List<&2, S.D>, +y: List<&2, S.D>, +g: O.C(F), hj: DG.mall(~F, jc(~F, eqs, n, pt(~F, y, pc)), g)) -> DG.mall(~F, DV.jac(~F, M.ofdv(~F, NU.dapp(y, pc)), eqs, ST.iota(n, 0n)), g):
  %Equal.sym(M.Vec(~F), M.ofdv(~F, NU.dapp(y, pc)), C.app(~F, M.ofdv(~F, y), M.ofdv(~F, pc)), AP.dapp_ofd(~F, y, pc)) : DG.mall(~F, DV.jac(~F, _, eqs, ST.iota(n, 0n)), g)
  hj

def elim_pt(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +w: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +y: List<&2, S.D>, +g: O.C(F), +b: O.C(F), +hg: O.le(~F, O.zero(F), g), +hb: O.le(~F, O.zero(F), b), +hJ: NP.InvB(~F, jc(~F, eqs, n, pt(~F, y, pc)), n, b), +hj: DG.mall(~F, jc(~F, eqs, n, pt(~F, y, pc)), g), +hsm: AP.small(~F, n, g, b, w)) -> DG.dinv_res(~F, n, jc(~F, eqs, n, pt(~F, y, pc)), AP.epsa(~F, n, g, b, w), NU.dinverse(n, w, NU.jac(eqs, n, NU.dapp(y, pc)))):
  %AP.dapp_ofd(~F, y, pc) : DG.dinv_res(~F, n, DV.jac(~F, _, eqs, ST.iota(n, 0n)), AP.epsa(~F, n, g, b, w), NU.dinverse(n, w, NU.jac(eqs, n, NU.dapp(y, pc))))
  AP.elim_at(~F, ~H, n, w, eqs, hn, hh, NU.dapp(y, pc), g, b, hg, hb, invb_dapp(~F, n, eqs, pc, y, b, hJ), mall_dapp(~F, n, eqs, pc, y, g, hj), hsm)

# the solver's step from y is a Step (C4 at the Jacobian of y's point)
def nstep_ok(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +p: Nat, +y: List<&2, S.D>, +ly: {M.len(~F, M.ofdv(~F, y)) == n : Nat}, +g: O.C(F), +b: O.C(F), +hg: O.le(~F, O.zero(F), g), +hb: O.le(~F, O.zero(F), b), +hJ: NP.InvB(~F, jc(~F, eqs, n, pt(~F, y, pc)), n, b), +hj: DG.mall(~F, jc(~F, eqs, n, pt(~F, y, pc)), g), +hsm: AP.small(~F, n, g, b, NU.wbits(p))) -> NSR(~F, n, eqs, pc, AP.epsa(~F, n, g, b, NU.wbits(p)), p, y, NU.nstep(eqs, n, pc, p, y)):
  nstep_ok.go(~F, ~H, n, eqs, hh, pc, AP.epsa(~F, n, g, b, NU.wbits(p)), p, y, ly, NU.dinverse(n, NU.wbits(p), NU.jac(eqs, n, NU.dapp(y, pc))), elim_pt(~F, ~H, n, NU.wbits(p), eqs, hn, hh, pc, y, g, b, hg, hb, hJ, hj, hsm))
