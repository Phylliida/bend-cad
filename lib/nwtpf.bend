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

# The constants
# -------------
# b2 = 2b (the Jacobian's inverse at a visited point), ea = C4's bound on
# I - A J at P + 32 bits, al = (1 + n ea) b2 (|A w| <= al |w|), g0c bounds
# f at the drawing, dl0 the first step, e1 the first iterate's distance
# to x_b, en the answer's, dx every point's.


def bt2(~F: O.OField, +b: O.C(F)) -> O.C(F):
  O.add(F, b, b)

def ea(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat) -> O.C(F):
  AP.epsa(~F, n, ms, bt2(~F, b), NU.wbits(p))

def al(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat) -> O.C(F):
  AP.alf(~F, n, ea(~F, n, m, b, lam, ms, d, rho, p), bt2(~F, b))

def g0c(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat) -> O.C(F):
  O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, n), ms), d), O.mul(F, O.mul(F, FR.ofn(~F, m), ms), rho))

def dl0(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat) -> O.C(F):
  O.add(F, O.mul(F, al(~F, n, m, b, lam, ms, d, rho, p), g0c(~F, n, m, b, lam, ms, d, rho, p)), hnw(~F, p))

def e1(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat) -> O.C(F):
  O.add(F, hnw(~F, p), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, n), ea(~F, n, m, b, lam, ms, d, rho, p)), d), O.mul(F, al(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, O.add(F, d, rho))), d))), O.mul(F, al(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, O.mul(F, FR.ofn(~F, m), ms), rho))))

def en(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat) -> O.C(F):
  O.add(F, O.mul(F, FR.ofn(~F, 8n), hnw(~F, p)), e1(~F, n, m, b, lam, ms, d, rho, p))

def dx(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat) -> O.C(F):
  O.add(F, O.add(F, d, rho), O.add(F, en(~F, n, m, b, lam, ms, d, rho, p), dl0(~F, n, m, b, lam, ms, d, rho, p)))

# the second step's terms beyond 2h (the settle test needs them below 6h)
def settle(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat) -> O.C(F):
  O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, n), ea(~F, n, m, b, lam, ms, d, rho, p)), hnw(~F, p)), O.mul(F, al(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dl0(~F, n, m, b, lam, ms, d, rho, p))), hnw(~F, p)))), O.add(F, O.mul(F, al(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dl0(~F, n, m, b, lam, ms, d, rho, p))), O.mul(F, bt2(~F, b), g0c(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, al(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, O.mul(F, FR.ofn(~F, n), ms), O.mul(F, O.mul(F, FR.ofn(~F, n), ea(~F, n, m, b, lam, ms, d, rho, p)), O.mul(F, bt2(~F, b), g0c(~F, n, m, b, lam, ms, d, rho, p)))))))


def hnw_nn(~F: O.OField, +p: Nat) -> O.le(~F, O.zero(F), hnw(~F, p)):
  DG.u_nn(~F, 1n+p)

def bt2_nn(~F: O.OField, +b: O.C(F), +hb0: O.le(~F, O.zero(F), b)) -> O.le(~F, O.zero(F), bt2(~F, b)):
  FO.nonneg_add(~F, b, b, hb0, hb0)

def ea_nn(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho)) -> O.le(~F, O.zero(F), ea(~F, n, m, b, lam, ms, d, rho, p)):
  AP.epsa_nn(~F, n, ms, bt2(~F, b), NU.wbits(p), hm0, bt2_nn(~F, b, hb0))

def al_nn(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho)) -> O.le(~F, O.zero(F), al(~F, n, m, b, lam, ms, d, rho, p)):
  AP.alf_nn(~F, n, ea(~F, n, m, b, lam, ms, d, rho, p), bt2(~F, b), ea_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0), bt2_nn(~F, b, hb0))

def nms_nn(~F: O.OField, +k: Nat, +ms: O.C(F), +hm0: O.le(~F, O.zero(F), ms)) -> O.le(~F, O.zero(F), O.mul(F, FR.ofn(~F, k), ms)):
  FO.mul_nonneg(~F, FR.ofn(~F, k), ms, DG.ofn_nn(~F, k), hm0)

def g0c_nn(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho)) -> O.le(~F, O.zero(F), g0c(~F, n, m, b, lam, ms, d, rho, p)):
  FO.nonneg_add(~F, O.mul(F, O.mul(F, FR.ofn(~F, n), ms), d), O.mul(F, O.mul(F, FR.ofn(~F, m), ms), rho), FO.mul_nonneg(~F, O.mul(F, FR.ofn(~F, n), ms), d, nms_nn(~F, n, ms, hm0), hd0), FO.mul_nonneg(~F, O.mul(F, FR.ofn(~F, m), ms), rho, nms_nn(~F, m, ms, hm0), hr0))

def dl0_nn(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho)) -> O.le(~F, O.zero(F), dl0(~F, n, m, b, lam, ms, d, rho, p)):
  FO.nonneg_add(~F, O.mul(F, al(~F, n, m, b, lam, ms, d, rho, p), g0c(~F, n, m, b, lam, ms, d, rho, p)), hnw(~F, p), FO.mul_nonneg(~F, al(~F, n, m, b, lam, ms, d, rho, p), g0c(~F, n, m, b, lam, ms, d, rho, p), al_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0), g0c_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0)), hnw_nn(~F, p))

def e1_nn(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho)) -> O.le(~F, O.zero(F), e1(~F, n, m, b, lam, ms, d, rho, p)):
  +hea = ea_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0)
  +hal = al_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0)
  FO.nonneg_add(~F, hnw(~F, p), O.add(F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, n), ea(~F, n, m, b, lam, ms, d, rho, p)), d), O.mul(F, al(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, O.add(F, d, rho))), d))), O.mul(F, al(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, O.mul(F, FR.ofn(~F, m), ms), rho))), hnw_nn(~F, p),
    FO.nonneg_add(~F, O.add(F, O.mul(F, O.mul(F, FR.ofn(~F, n), ea(~F, n, m, b, lam, ms, d, rho, p)), d), O.mul(F, al(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, O.add(F, d, rho))), d))), O.mul(F, al(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, O.mul(F, FR.ofn(~F, m), ms), rho)),
      FO.nonneg_add(~F, O.mul(F, O.mul(F, FR.ofn(~F, n), ea(~F, n, m, b, lam, ms, d, rho, p)), d), O.mul(F, al(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, O.add(F, d, rho))), d)), FO.mul_nonneg(~F, O.mul(F, FR.ofn(~F, n), ea(~F, n, m, b, lam, ms, d, rho, p)), d, nms_nn(~F, n, ea(~F, n, m, b, lam, ms, d, rho, p), hea), hd0),
        FO.mul_nonneg(~F, al(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, O.add(F, d, rho))), d), hal, FO.mul_nonneg(~F, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, O.add(F, d, rho))), d, nms_nn(~F, n, O.mul(F, lam, O.add(F, d, rho)), FO.mul_nonneg(~F, lam, O.add(F, d, rho), hl0, FO.nonneg_add(~F, d, rho, hd0, hr0))), hd0))),
      FO.mul_nonneg(~F, al(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, O.mul(F, FR.ofn(~F, m), ms), rho), hal, FO.mul_nonneg(~F, O.mul(F, FR.ofn(~F, m), ms), rho, nms_nn(~F, m, ms, hm0), hr0))))

def en_nn(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho)) -> O.le(~F, O.zero(F), en(~F, n, m, b, lam, ms, d, rho, p)):
  FO.nonneg_add(~F, O.mul(F, FR.ofn(~F, 8n), hnw(~F, p)), e1(~F, n, m, b, lam, ms, d, rho, p), nms_nn(~F, 8n, hnw(~F, p), hnw_nn(~F, p)), e1_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0))

def dx_nn(~F: O.OField, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho)) -> O.le(~F, O.zero(F), dx(~F, n, m, b, lam, ms, d, rho, p)):
  FO.nonneg_add(~F, O.add(F, d, rho), O.add(F, en(~F, n, m, b, lam, ms, d, rho, p), dl0(~F, n, m, b, lam, ms, d, rho, p)), FO.nonneg_add(~F, d, rho, hd0, hr0), FO.nonneg_add(~F, en(~F, n, m, b, lam, ms, d, rho, p), dl0(~F, n, m, b, lam, ms, d, rho, p), en_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0), dl0_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0)))

# Vectors and boxes
# -----------------

def len_app(~F: O.OField, u: M.Vec(~F), +w: M.Vec(~F)) -> {M.len(~F, C.app(~F, u, w)) == Nat.add(M.len(~F, u), M.len(~F, w)) : Nat}:
  match u:
    case Nil{}:
      {==}
    case Con{a, t}:
      %Equal.sym(Nat, M.len(~F, C.app(~F, t, w)), Nat.add(M.len(~F, t), M.len(~F, w)), len_app(~F, t, w)) : {1n+_ == 1n+Nat.add(M.len(~F, t), M.len(~F, w)) : Nat}
      {==}

def len_app2(~F: O.OField, +u: M.Vec(~F), +w: M.Vec(~F), +n: Nat, +m: Nat, lu: {M.len(~F, u) == n : Nat}, lw: {M.len(~F, w) == m : Nat}) -> {M.len(~F, C.app(~F, u, w)) == Nat.add(n, m) : Nat}:
  %lu : {M.len(~F, C.app(~F, u, w)) == Nat.add(_, m) : Nat}
  %lw : {M.len(~F, C.app(~F, u, w)) == Nat.add(M.len(~F, u), _) : Nat}
  len_app(~F, u, w)

def vall_app(~F: O.OField, u: M.Vec(~F), +w: M.Vec(~F), +t: O.C(F), hu: M.vbnd.all(~F, u, t), hw: M.vbnd.all(~F, w, t)) -> M.vbnd.all(~F, C.app(~F, u, w), t):
  match u:
    case Nil{}:
      hw
    case Con{+a, +us}:
      (h1, h2) = hu
      (h1, vall_app(~F, us, w, t, h2, hw))

# entry by entry, (u1 ++ z1) - (u2 ++ z2) is within t when both parts are
def vall_appsub(~F: O.OField, +u1: M.Vec(~F), +u2: M.Vec(~F), +z1: M.Vec(~F), +z2: M.Vec(~F), +t: O.C(F), hl: {M.len(~F, u1) == M.len(~F, u2) : Nat}, hu: M.vbnd.all(~F, BX.vsub(~F, u1, u2), t), hz: M.vbnd.all(~F, BX.vsub(~F, z1, z2), t)) -> M.vbnd.all(~F, BX.vsub(~F, C.app(~F, u1, z1), C.app(~F, u2, z2)), t):
  %Equal.sym(M.Vec(~F), BX.vsub(~F, C.app(~F, u1, z1), C.app(~F, u2, z2)), C.app(~F, BX.vsub(~F, u1, u2), BX.vsub(~F, z1, z2)), FV.vsub_app(~F, u1, u2, z1, z2, hl)) : M.vbnd.all(~F, _, t)
  vall_app(~F, BX.vsub(~F, u1, u2), BX.vsub(~F, z1, z2), t, hu, hz)

def vall_of_vn(~F: O.OField, +v: M.Vec(~F), +t: O.C(F), h: O.le(~F, NP.vn(~F, v), t)) -> M.vbnd.all(~F, v, t):
  FM.vall_mono(~F, v, NP.vn(~F, v), t, FV.vmax_all(~F, v), FM.sub_nonneg(~F, NP.vn(~F, v), t, h))

def vall_le(~F: O.OField, +v: M.Vec(~F), +s: O.C(F), +t: O.C(F), h: M.vbnd.all(~F, v, s), hst: O.le(~F, s, t)) -> M.vbnd.all(~F, v, t):
  FM.vall_mono(~F, v, s, t, h, FM.sub_nonneg(~F, s, t, hst))

# |c_k| <= bb - rad when c is within dc of xs, |xs_k| <= bb - 1, dc + rad <= 1
def gnear(~F: O.OField, c: M.Vec(~F), xs: M.Vec(~F), +bb: O.C(F), +dc: O.C(F), +rad: O.C(F), hx: M.vbnd.all(~F, xs, O.sub(~F, bb, O.one(F))), hc: M.vbnd.all(~F, BX.vsub(~F, c, xs), dc), +hs: O.le(~F, O.add(F, dc, rad), O.one(F)), hl: {M.len(~F, c) == M.len(~F, xs) : Nat}) -> M.vbnd.all(~F, c, O.sub(~F, bb, rad)):
  match c xs:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} Con{b, bs}:
      FO.absurd(M.vbnd.all(~F, Nil{}, O.sub(~F, bb, rad)), FV.zero_ne(M.len(~F, bs), hl))
    case Con{a, as} Nil{}:
      FO.absurd(M.vbnd.all(~F, Con{a, as}, O.sub(~F, bb, rad)), FV.succ_ne(M.len(~F, as), hl))
    case Con{+a, +as} Con{+b, +bs}:
      (hx1, hx2) = hx
      (hc1, hc2) = hc
      (FM.bnd_mono(~F, a, O.add(F, O.sub(~F, bb, O.one(F)), dc), O.sub(~F, bb, rad),
         KB.bnd_val(~F, O.add(F, b, O.sub(~F, a, b)), a, O.add(F, O.sub(~F, bb, O.one(F)), dc), FR.fring_eq(~F, [a, b], E.ZAdd{E.ZVar{1n}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}}, E.ZVar{0n}, {==}), FM.bnd_add(~F, b, O.sub(~F, bb, O.one(F)), O.sub(~F, a, b), dc, hx1, hc1)),
         FM.nn_eq(~F, O.sub(~F, O.sub(~F, bb, rad), O.add(F, O.sub(~F, bb, O.one(F)), dc)), O.sub(~F, O.one(F), O.add(F, dc, rad)), FR.fring_eq(~F, [bb, rad, dc], E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZVar{2n}, E.ZVar{1n}}}, E.ZSub{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{2n}}}, {==}), FM.sub_nonneg(~F, O.add(F, dc, rad), O.one(F), hs))),
       gnear(~F, as, bs, bb, dc, rad, hx2, hc2, hs, FV.succ_inj(M.len(~F, as), M.len(~F, bs), hl)))

def vsub_zr(~F: O.OField, u: M.Vec(~F), +n: Nat, lu: {M.len(~F, u) == n : Nat}) -> {BX.vsub(~F, u, GJ.zeros(~F, n)) == u : M.Vec(~F)}:
  match u n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+k:
      FO.absurd({BX.vsub(~F, Nil{}, GJ.zeros(~F, 1n+k)) == Nil{} : M.Vec(~F)}, FV.zero_ne(k, lu))
    case Con{+a, +t} 0n:
      FO.absurd({BX.vsub(~F, Con{a, t}, GJ.zeros(~F, 0n)) == Con{a, t} : M.Vec(~F)}, FV.succ_ne(M.len(~F, t), lu))
    case Con{+a, +t} 1n+k:
      %Equal.sym(M.Vec(~F), BX.vsub(~F, t, GJ.zeros(~F, k)), t, vsub_zr(~F, t, k, FV.succ_inj(M.len(~F, t), k, lu))) : {Con{O.sub(~F, a, O.zero(F)), _} == Con{a, t} : M.Vec(~F)}
      %FR.fring_eq(~F, [a], E.ZVar{0n}, E.ZSub{E.ZVar{0n}, E.ZCst{S.Z0{}}}, {==}) : {Con{_, t} == Con{a, t} : M.Vec(~F)}
      {==}

def vall_self(~F: O.OField, v: M.Vec(~F), +t: O.C(F), +ht: O.le(~F, O.zero(F), t)) -> M.vbnd.all(~F, BX.vsub(~F, v, v), t):
  match v:
    case Nil{}:
      Unit{}
    case Con{+a, +vs}:
      (KB.bnd_subself(~F, a, t, ht), vall_self(~F, vs, t, ht))

def bnd_swap(~F: O.OField, +a: O.C(F), +b: O.C(F), +t: O.C(F), h: M.bnd(~F, O.sub(~F, a, b), t)) -> M.bnd(~F, O.sub(~F, b, a), t):
  KB.bnd_val(~F, O.neg(F, O.sub(~F, a, b)), O.sub(~F, b, a), t, FR.fring_eq(~F, [a, b], E.ZNeg{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}}, E.ZSub{E.ZVar{1n}, E.ZVar{0n}}, {==}), FM.bnd_neg(~F, O.sub(~F, a, b), t, h))

def bnd_nn0(~F: O.OField, +a: O.C(F), +t: O.C(F), h: M.bnd(~F, O.neg(F, a), t)) -> M.bnd(~F, a, t):
  KB.bnd_val(~F, O.neg(F, O.neg(F, a)), a, t, FR.fring_eq(~F, [a], E.ZNeg{E.ZNeg{E.ZVar{0n}}}, E.ZVar{0n}, {==}), FM.bnd_neg(~F, O.neg(F, a), t, h))

def vall_unneg(~F: O.OField, w: M.Vec(~F), +t: O.C(F), h: M.vbnd.all(~F, M.vneg(~F, w), t)) -> M.vbnd.all(~F, w, t):
  match w:
    case Nil{}:
      Unit{}
    case Con{+b, +ws}:
      (h1, h2) = h
      (bnd_nn0(~F, b, t, h1), vall_unneg(~F, ws, t, h2))

# a bound on u - w is one on w - u
def vall_swap(~F: O.OField, u: M.Vec(~F), w: M.Vec(~F), +t: O.C(F), h: M.vbnd.all(~F, BX.vsub(~F, u, w), t)) -> M.vbnd.all(~F, BX.vsub(~F, w, u), t):
  match u w:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} Con{+b, +ws}:
      vall_unneg(~F, Con{b, ws}, t, h)
    case Con{+a, +us} Nil{}:
      FM.vall_neg(~F, Con{a, us}, t, h)
    case Con{+a, +us} Con{+b, +ws}:
      (h1, h2) = h
      (bnd_swap(~F, a, b, t, h1), vall_swap(~F, us, ws, t, h2))

def mm_le(~F: O.OField, +a: O.C(F), +a2: O.C(F), +b: O.C(F), +b2: O.C(F), +hb: O.le(~F, O.zero(F), b), +ha2: O.le(~F, O.zero(F), a2), ha: O.le(~F, a, a2), hb2: O.le(~F, b, b2)) -> O.le(~F, O.mul(F, a, b), O.mul(F, a2, b2)):
  DM.le_trans(~F, O.mul(F, a, b), O.mul(F, a2, b), O.mul(F, a2, b2), FV.mul_le_r(~F, a, a2, b, hb, ha), FV.mul_le(~F, a2, b, b2, ha2, hb2))

def nrows_smat(~F: O.OField, +x1: M.Vec(~F), +x2: M.Vec(~F), eqs: List<&2, E.QExpr>, +cnt: Nat, +lo: Nat) -> {GJ.nrows(~F, CP.smat(~F, x1, x2, eqs, cnt, lo)) == CK.eqlen(eqs) : Nat}:
  match eqs:
    case Nil{}:
      {==}
    case Con{e, es}:
      %Equal.sym(Nat, GJ.nrows(~F, CP.smat(~F, x1, x2, es, cnt, lo)), CK.eqlen(es), nrows_smat(~F, x1, x2, es, cnt, lo)) : {1n+_ == 1n+CK.eqlen(es) : Nat}
      {==}

def nrows_mneg(~F: O.OField, a: M.Mat(~F)) -> {GJ.nrows(~F, M.mneg(~F, a)) == GJ.nrows(~F, a) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{r, t}:
      %Equal.sym(Nat, GJ.nrows(~F, M.mneg(~F, t)), GJ.nrows(~F, t), nrows_mneg(~F, t)) : {1n+_ == 1n+GJ.nrows(~F, t) : Nat}
      {==}

def nrows_madd(~F: O.OField, a: M.Mat(~F), b: M.Mat(~F), +n: Nat, ha: {GJ.nrows(~F, a) == n : Nat}, hb: {GJ.nrows(~F, b) == n : Nat}) -> {GJ.nrows(~F, M.madd(~F, a, b)) == n : Nat}:
  match a b:
    case Nil{} b:
      hb
    case Con{r, rs} Nil{}:
      ha
    case Con{+r, +rs} Con{+t, +ts}:
      match n:
        case 0n:
          FO.absurd({GJ.nrows(~F, M.madd(~F, Con{r, rs}, Con{t, ts})) == 0n : Nat}, FV.succ_ne(GJ.nrows(~F, rs), ha))
        case 1n+k:
          %Equal.sym(Nat, GJ.nrows(~F, M.madd(~F, rs, ts)), k, nrows_madd(~F, rs, ts, k, FV.succ_inj(GJ.nrows(~F, rs), k, ha), FV.succ_inj(GJ.nrows(~F, ts), k, hb))) : {1n+_ == 1n+k : Nat}
          {==}

# the n x n difference S - J has n rows
def nrows_sj(~F: O.OField, +x1: M.Vec(~F), +x2: M.Vec(~F), +c: M.Vec(~F), +eqs: List<&2, E.QExpr>, +n: Nat, +hn: {CK.eqlen(eqs) == n : Nat}) -> {GJ.nrows(~F, M.madd(~F, CP.smat(~F, x1, x2, eqs, n, 0n), M.mneg(~F, jc(~F, eqs, n, c)))) == n : Nat}:
  nrows_madd(~F, CP.smat(~F, x1, x2, eqs, n, 0n), M.mneg(~F, jc(~F, eqs, n, c)), n, Equal.trans(Nat, GJ.nrows(~F, CP.smat(~F, x1, x2, eqs, n, 0n)), CK.eqlen(eqs), n, nrows_smat(~F, x1, x2, eqs, n, 0n), hn),
    Equal.trans(Nat, GJ.nrows(~F, M.mneg(~F, jc(~F, eqs, n, c))), GJ.nrows(~F, jc(~F, eqs, n, c)), n, nrows_mneg(~F, jc(~F, eqs, n, c)), AP.nrows_jacn(~F, c, eqs, n, hn)))

def le_sub_one(~F: O.OField, +bb: O.C(F), +t: O.C(F), h: O.le(~F, t, O.one(F))) -> O.le(~F, O.sub(~F, bb, O.one(F)), O.sub(~F, bb, t)):
  FV.le_of_sub(~F, O.sub(~F, bb, O.one(F)), O.sub(~F, bb, t), FM.nn_eq(~F, O.sub(~F, O.sub(~F, bb, t), O.sub(~F, bb, O.one(F))), O.sub(~F, O.one(F), t), FR.fring_eq(~F, [bb, t], E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{1n}}, E.ZSub{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), FM.sub_nonneg(~F, t, O.one(F), h)))

# x + x <= 1, 0 <= x: x <= 1
def le_one_of2(~F: O.OField, +x: O.C(F), +hx: O.le(~F, O.zero(F), x), h: O.le(~F, O.add(F, x, x), O.one(F))) -> O.le(~F, x, O.one(F)):
  DM.le_trans(~F, x, O.add(F, x, x), O.one(F), FV.le_of_sub(~F, x, O.add(F, x, x), FM.nn_eq(~F, O.sub(~F, O.add(F, x, x), x), x, FR.fring_eq(~F, [x], E.ZVar{0n}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{0n}}, E.ZVar{0n}}, {==}), hx)), h)

# a <= a + b and b <= a + b for nonnegatives
def le_addr(~F: O.OField, +a: O.C(F), +b: O.C(F), +hb: O.le(~F, O.zero(F), b)) -> O.le(~F, a, O.add(F, a, b)):
  FV.le_of_sub(~F, a, O.add(F, a, b), FM.nn_eq(~F, O.sub(~F, O.add(F, a, b), a), b, FR.fring_eq(~F, [a, b], E.ZVar{1n}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{0n}}, {==}), hb))

def le_addl(~F: O.OField, +a: O.C(F), +b: O.C(F), +ha: O.le(~F, O.zero(F), a)) -> O.le(~F, b, O.add(F, a, b)):
  FV.le_of_sub(~F, b, O.add(F, a, b), FM.nn_eq(~F, O.sub(~F, O.add(F, a, b), b), a, FR.fring_eq(~F, [a, b], E.ZVar{0n}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{1n}}, {==}), ha))

# The block's context
# -------------------


def dx_le1(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, dx(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, 6n), hnw(~F, p)))) -> O.le(~F, dx(~F, n, m, b, lam, ms, d, rho, p), O.one(F)):
  le_one_of2(~F, dx(~F, n, m, b, lam, ms, d, rho, p), dx_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0), s1)

def rho_le_dx(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, dx(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, 6n), hnw(~F, p)))) -> O.le(~F, rho, dx(~F, n, m, b, lam, ms, d, rho, p)):
  DM.le_trans(~F, rho, O.add(F, d, rho), dx(~F, n, m, b, lam, ms, d, rho, p), le_addl(~F, d, rho, hd0), le_addr(~F, O.add(F, d, rho), O.add(F, en(~F, n, m, b, lam, ms, d, rho, p), dl0(~F, n, m, b, lam, ms, d, rho, p)), FO.nonneg_add(~F, en(~F, n, m, b, lam, ms, d, rho, p), dl0(~F, n, m, b, lam, ms, d, rho, p), en_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0), dl0_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0))))

def dr_le_dx(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, dx(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, 6n), hnw(~F, p)))) -> O.le(~F, O.add(F, d, rho), dx(~F, n, m, b, lam, ms, d, rho, p)):
  le_addr(~F, O.add(F, d, rho), O.add(F, en(~F, n, m, b, lam, ms, d, rho, p), dl0(~F, n, m, b, lam, ms, d, rho, p)), FO.nonneg_add(~F, en(~F, n, m, b, lam, ms, d, rho, p), dl0(~F, n, m, b, lam, ms, d, rho, p), en_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0), dl0_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0)))

def d_le_dx(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, dx(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, 6n), hnw(~F, p)))) -> O.le(~F, d, dx(~F, n, m, b, lam, ms, d, rho, p)):
  DM.le_trans(~F, d, O.add(F, d, rho), dx(~F, n, m, b, lam, ms, d, rho, p), le_addr(~F, d, rho, hr0), dr_le_dx(~F, ~H, n, m, eqs, hn, hh, hbl, pc, lpc, p, xb, xz, lxb, lxz, hz, bb, lam, ms, b, d, rho, hb0, hl0, hm0, hd0, hr0, hbb0, hbb, hq, hJ, hzc, hsm, s1, s2, s4))

def en_le_dx(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, dx(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, 6n), hnw(~F, p)))) -> O.le(~F, en(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)):
  DM.le_trans(~F, en(~F, n, m, b, lam, ms, d, rho, p), O.add(F, en(~F, n, m, b, lam, ms, d, rho, p), dl0(~F, n, m, b, lam, ms, d, rho, p)), dx(~F, n, m, b, lam, ms, d, rho, p), le_addr(~F, en(~F, n, m, b, lam, ms, d, rho, p), dl0(~F, n, m, b, lam, ms, d, rho, p), dl0_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0)), le_addl(~F, O.add(F, d, rho), O.add(F, en(~F, n, m, b, lam, ms, d, rho, p), dl0(~F, n, m, b, lam, ms, d, rho, p)), FO.nonneg_add(~F, d, rho, hd0, hr0)))

def dl0_le_dx(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, dx(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, 6n), hnw(~F, p)))) -> O.le(~F, dl0(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)):
  DM.le_trans(~F, dl0(~F, n, m, b, lam, ms, d, rho, p), O.add(F, en(~F, n, m, b, lam, ms, d, rho, p), dl0(~F, n, m, b, lam, ms, d, rho, p)), dx(~F, n, m, b, lam, ms, d, rho, p), le_addl(~F, en(~F, n, m, b, lam, ms, d, rho, p), dl0(~F, n, m, b, lam, ms, d, rho, p), en_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0)), le_addl(~F, O.add(F, d, rho), O.add(F, en(~F, n, m, b, lam, ms, d, rho, p), dl0(~F, n, m, b, lam, ms, d, rho, p)), FO.nonneg_add(~F, d, rho, hd0, hr0)))

def e1_le_en(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, dx(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, 6n), hnw(~F, p)))) -> O.le(~F, e1(~F, n, m, b, lam, ms, d, rho, p), en(~F, n, m, b, lam, ms, d, rho, p)):
  le_addl(~F, O.mul(F, FR.ofn(~F, 8n), hnw(~F, p)), e1(~F, n, m, b, lam, ms, d, rho, p), nms_nn(~F, 8n, hnw(~F, p), hnw_nn(~F, p)))

def lxs(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, dx(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, 6n), hnw(~F, p)))) -> {M.len(~F, C.app(~F, xb, xz)) == Nat.add(n, m) : Nat}:
  len_app2(~F, xb, xz, n, m, lxb, lxz)

def lpt(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, dx(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, 6n), hnw(~F, p))), +y: List<&2, S.D>, +ly: {M.len(~F, M.ofdv(~F, y)) == n : Nat}) -> {M.len(~F, pt(~F, y, pc)) == Nat.add(n, m) : Nat}:
  len_app2(~F, M.ofdv(~F, y), M.ofdv(~F, pc), n, m, ly, lpc)

def lpt_xs(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, dx(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, 6n), hnw(~F, p))), +y: List<&2, S.D>, +ly: {M.len(~F, M.ofdv(~F, y)) == n : Nat}) -> {M.len(~F, pt(~F, y, pc)) == M.len(~F, C.app(~F, xb, xz)) : Nat}:
  Equal.trans(Nat, M.len(~F, pt(~F, y, pc)), Nat.add(n, m), M.len(~F, C.app(~F, xb, xz)), lpt(~F, ~H, n, m, eqs, hn, hh, hbl, pc, lpc, p, xb, xz, lxb, lxz, hz, bb, lam, ms, b, d, rho, hb0, hl0, hm0, hd0, hr0, hbb0, hbb, hq, hJ, hzc, hsm, s1, s2, s4, y, ly), Equal.sym(Nat, M.len(~F, C.app(~F, xb, xz)), Nat.add(n, m), lxs(~F, ~H, n, m, eqs, hn, hh, hbl, pc, lpc, p, xb, xz, lxb, lxz, hz, bb, lam, ms, b, d, rho, hb0, hl0, hm0, hd0, hr0, hbb0, hbb, hq, hJ, hzc, hsm, s1, s2, s4)))

def lyb(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, dx(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, 6n), hnw(~F, p))), +y: List<&2, S.D>, +ly: {M.len(~F, M.ofdv(~F, y)) == n : Nat}) -> {M.len(~F, M.ofdv(~F, y)) == M.len(~F, xb) : Nat}:
  Equal.trans(Nat, M.len(~F, M.ofdv(~F, y)), n, M.len(~F, xb), ly, Equal.sym(Nat, M.len(~F, xb), n, lxb))

# the box of radius dx around x_b ++ x_z has grade (bb, 1)
def gbig(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, dx(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, 6n), hnw(~F, p)))) -> BP.gbox(~BP.fnum(~F), ~F, ~BP.femb(~F), dx(~F, n, m, b, lam, ms, d, rho, p), bb, AP.fbx(~F, C.app(~F, xb, xz), dx(~F, n, m, b, lam, ms, d, rho, p))):
  AP.gbox_fbx(~F, C.app(~F, xb, xz), dx(~F, n, m, b, lam, ms, d, rho, p), bb, dx_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0), vall_le(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F)), O.sub(~F, bb, dx(~F, n, m, b, lam, ms, d, rho, p)), hbb, le_sub_one(~F, bb, dx(~F, n, m, b, lam, ms, d, rho, p), dx_le1(~F, ~H, n, m, eqs, hn, hh, hbl, pc, lpc, p, xb, xz, lxb, lxz, hz, bb, lam, ms, b, d, rho, hb0, hl0, hm0, hd0, hr0, hbb0, hbb, hq, hJ, hzc, hsm, s1, s2, s4))))

# y's point is within dx of x_b ++ x_z when y is within dx of x_b
def ptnear(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, dx(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, 6n), hnw(~F, p))), +y: List<&2, S.D>, +ly: {M.len(~F, M.ofdv(~F, y)) == n : Nat}, +t: O.C(F), hy: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, y), xb), t), ht: O.le(~F, t, dx(~F, n, m, b, lam, ms, d, rho, p))) -> M.vbnd.all(~F, BX.vsub(~F, pt(~F, y, pc), C.app(~F, xb, xz)), dx(~F, n, m, b, lam, ms, d, rho, p)):
  vall_appsub(~F, M.ofdv(~F, y), xb, M.ofdv(~F, pc), xz, dx(~F, n, m, b, lam, ms, d, rho, p), lyb(~F, ~H, n, m, eqs, hn, hh, hbl, pc, lpc, p, xb, xz, lxb, lxz, hz, bb, lam, ms, b, d, rho, hb0, hl0, hm0, hd0, hr0, hbb0, hbb, hq, hJ, hzc, hsm, s1, s2, s4, y, ly), vall_le(~F, BX.vsub(~F, M.ofdv(~F, y), xb), t, dx(~F, n, m, b, lam, ms, d, rho, p), hy, ht), vall_le(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho, dx(~F, n, m, b, lam, ms, d, rho, p), hzc, rho_le_dx(~F, ~H, n, m, eqs, hn, hh, hbl, pc, lpc, p, xb, xz, lxb, lxz, hz, bb, lam, ms, b, d, rho, hb0, hl0, hm0, hd0, hr0, hbb0, hbb, hq, hJ, hzc, hsm, s1, s2, s4)))

def inbig(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, dx(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, 6n), hnw(~F, p))), +y: List<&2, S.D>, +ly: {M.len(~F, M.ofdv(~F, y)) == n : Nat}, +t: O.C(F), hy: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, y), xb), t), ht: O.le(~F, t, dx(~F, n, m, b, lam, ms, d, rho, p))) -> KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), pt(~F, y, pc), AP.fbx(~F, C.app(~F, xb, xz), dx(~F, n, m, b, lam, ms, d, rho, p))):
  AP.inbox_fbx(~F, pt(~F, y, pc), C.app(~F, xb, xz), dx(~F, n, m, b, lam, ms, d, rho, p), ptnear(~F, ~H, n, m, eqs, hn, hh, hbl, pc, lpc, p, xb, xz, lxb, lxz, hz, bb, lam, ms, b, d, rho, hb0, hl0, hm0, hd0, hr0, hbb0, hbb, hq, hJ, hzc, hsm, s1, s2, s4, y, ly, t, hy, ht), lpt_xs(~F, ~H, n, m, eqs, hn, hh, hbl, pc, lpc, p, xb, xz, lxb, lxz, hz, bb, lam, ms, b, d, rho, hb0, hl0, hm0, hd0, hr0, hbb0, hbb, hq, hJ, hzc, hsm, s1, s2, s4, y, ly))

def xs_inbig(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, dx(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, 6n), hnw(~F, p)))) -> KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), C.app(~F, xb, xz), AP.fbx(~F, C.app(~F, xb, xz), dx(~F, n, m, b, lam, ms, d, rho, p))):
  AP.inbox_fbx(~F, C.app(~F, xb, xz), C.app(~F, xb, xz), dx(~F, n, m, b, lam, ms, d, rho, p), vall_self(~F, C.app(~F, xb, xz), dx(~F, n, m, b, lam, ms, d, rho, p), dx_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0)), {==})

# at a visited point: the Jacobian keeps an inverse of norm <= 2b, entries <= ms
def pt_inv(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, dx(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, 6n), hnw(~F, p))), +y: List<&2, S.D>, +ly: {M.len(~F, M.ofdv(~F, y)) == n : Nat}, +t: O.C(F), hy: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, y), xb), t), ht: O.le(~F, t, dx(~F, n, m, b, lam, ms, d, rho, p))) -> NP.InvB(~F, jc(~F, eqs, n, pt(~F, y, pc)), n, bt2(~F, b)):
  AP.invb_at(~F, n, eqs, hn, dx(~F, n, m, b, lam, ms, d, rho, p), bb, dx_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0), hbb0, C.app(~F, xb, xz), gbig(~F, ~H, n, m, eqs, hn, hh, hbl, pc, lpc, p, xb, xz, lxb, lxz, hz, bb, lam, ms, b, d, rho, hb0, hl0, hm0, hd0, hr0, hbb0, hbb, hq, hJ, hzc, hsm, s1, s2, s4), pt(~F, y, pc), inbig(~F, ~H, n, m, eqs, hn, hh, hbl, pc, lpc, p, xb, xz, lxb, lxz, hz, bb, lam, ms, b, d, rho, hb0, hl0, hm0, hd0, hr0, hbb0, hbb, hq, hJ, hzc, hsm, s1, s2, s4, y, ly, t, hy, ht), lam, ms, hl0, hq, b, hJ, s2)

def pt_maj(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, dx(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, 6n), hnw(~F, p))), +y: List<&2, S.D>, +ly: {M.len(~F, M.ofdv(~F, y)) == n : Nat}, +t: O.C(F), hy: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, y), xb), t), ht: O.le(~F, t, dx(~F, n, m, b, lam, ms, d, rho, p))) -> M.Both(DG.mall(~F, jc(~F, eqs, n, pt(~F, y, pc)), ms), NP.rowsle(~F, jc(~F, eqs, n, pt(~F, y, pc)), n, O.mul(F, FR.ofn(~F, n), ms))):
  AP.jac_maj(~F, dx(~F, n, m, b, lam, ms, d, rho, p), bb, dx_nn(~F, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0), hbb0, C.app(~F, xb, xz), gbig(~F, ~H, n, m, eqs, hn, hh, hbl, pc, lpc, p, xb, xz, lxb, lxz, hz, bb, lam, ms, b, d, rho, hb0, hl0, hm0, hd0, hr0, hbb0, hbb, hq, hJ, hzc, hsm, s1, s2, s4), pt(~F, y, pc), inbig(~F, ~H, n, m, eqs, hn, hh, hbl, pc, lpc, p, xb, xz, lxb, lxz, hz, bb, lam, ms, b, d, rho, hb0, hl0, hm0, hd0, hr0, hbb0, hbb, hq, hJ, hzc, hsm, s1, s2, s4, y, ly, t, hy, ht), lam, ms, hm0, eqs, hq, n, 0n)

# the solver's step from a visited point
def nstep_vis(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +hsm: AP.small(~F, n, ms, bt2(~F, b), NU.wbits(p)), +s1: O.le(~F, O.add(F, dx(~F, n, m, b, lam, ms, d, rho, p), dx(~F, n, m, b, lam, ms, d, rho, p)), O.one(F)), +s2: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p)))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, dx(~F, n, m, b, lam, ms, d, rho, p))))), O.one(F)), +s4: O.le(~F, settle(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, FR.ofn(~F, 6n), hnw(~F, p))), +y: List<&2, S.D>, +ly: {M.len(~F, M.ofdv(~F, y)) == n : Nat}, +t: O.C(F), +hy: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, y), xb), t), +ht: O.le(~F, t, dx(~F, n, m, b, lam, ms, d, rho, p))) -> NSR(~F, n, eqs, pc, ea(~F, n, m, b, lam, ms, d, rho, p), p, y, NU.nstep(eqs, n, pc, p, y)):
  nstep_ok(~F, ~H, n, eqs, hn, hh, pc, p, y, ly, ms, bt2(~F, b), hm0, bt2_nn(~F, b, hb0), pt_inv(~F, ~H, n, m, eqs, hn, hh, hbl, pc, lpc, p, xb, xz, lxb, lxz, hz, bb, lam, ms, b, d, rho, hb0, hl0, hm0, hd0, hr0, hbb0, hbb, hq, hJ, hzc, hsm, s1, s2, s4, y, ly, t, hy, ht), AP.both_l(DG.mall(~F, jc(~F, eqs, n, pt(~F, y, pc)), ms), NP.rowsle(~F, jc(~F, eqs, n, pt(~F, y, pc)), n, O.mul(F, FR.ofn(~F, n), ms)), pt_maj(~F, ~H, n, m, eqs, hn, hh, hbl, pc, lpc, p, xb, xz, lxb, lxz, hz, bb, lam, ms, b, d, rho, hb0, hl0, hm0, hd0, hr0, hbb0, hbb, hq, hJ, hzc, hsm, s1, s2, s4, y, ly, t, hy, ht)), hsm)
