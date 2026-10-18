# bend-cad: one block in scale form under solve_complete (DESIGN §10.4
# "C6 plan", C6a), restated so the gate checks lib/pmono.bend and
# lib/scalepf.bend until the completeness proof imports them. In every
# ordered field F:
# - lib/pmono.bend: a polynomial in + and * over atoms with 0 <= a_i <= c_i
#   (fixed) or 0 <= a_i <= t c_i (small), 0 <= t <= 1, is at most t times
#   its value at the bounds when every monomial has a small atom;
# - lib/scalepf.bend: block_ok (lib/blockpf.bend) holds with its
#   smallness hypotheses replaced by d <= h, rho <= h T and t Q < 1
#   (h = 2^-(p+1), t = 2^-(p/2), Q = qblk(n, m, b, lam, ms, T)
#   independent of p, d and rho): one_block_sc. The radius bound rbc is
#   at most h Phi (radius_sc), and Phi >= T (phi_ge).

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/box.bend as BX
import ../spec/knum.bend as N
import ../lib/kinst.bend as KI
import ../lib/numer.bend as NU
import ../lib/fring.bend as FR
import ../lib/fvec.bend as FV
import ../lib/cert.bend as CK
import ../lib/certdef.bend as C
import ../lib/gjpf.bend as GJ
import ../lib/normpf.bend as NP
import ../lib/apxpf.bend as AP
import ../lib/nwtpf.bend as NW
import ../lib/blockpf.bend as BK
import ../lib/pmono.bend as PM
import ../lib/scalepf.bend as SC

def poly_linear(~F: O.OField, +env: List<&2, PM.Atm<O.C(F)>>, +t: O.C(F), +h: PM.Bnd(~F, env, t), +ht0: O.le(~F, O.zero(F), t), +ht1: O.le(~F, t, O.one(F)), e: PM.PE, +hd: {PM.d1(PM.svs(~F, env), e) == True{} : Bool}) -> O.le(~F, PM.peval(~F, PM.avs(~F, env), e), O.mul(F, t, PM.peval(~F, PM.cvs(~F, env), e))):
  PM.pe_lin(~F, env, t, h, ht0, ht1, e, hd)

def one_block_sc(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +hbl: {CK.allbelow(Nat.add(n, m), eqs) == True{} : Bool}, +pc: List<&2, S.D>, +lpc: {M.len(~F, M.ofdv(~F, pc)) == m : Nat}, +p: Nat, +xb: M.Vec(~F), +xz: M.Vec(~F), +lxb: {M.len(~F, xb) == n : Nat}, +lxz: {M.len(~F, xz) == m : Nat}, +hz: {C.fvals(~F, eqs, C.app(~F, xb, xz)) == GJ.zeros(~F, n) : M.Vec(~F)}, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +b: O.C(F), +d: O.C(F), +rho: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +hbb0: O.le(~F, O.zero(F), bb), +hbb: M.vbnd.all(~F, C.app(~F, xb, xz), O.sub(~F, bb, O.one(F))), +hq: AP.eqok(~F, bb, lam, ms, eqs), +hJ: NP.InvB(~F, NW.jc(~F, eqs, n, C.app(~F, xb, xz)), n, b), +hzc: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, pc), xz), rho), +y0: List<&2, S.D>, +ly0: {M.len(~F, M.ofdv(~F, y0)) == n : Nat}, +hy0: M.vbnd.all(~F, BX.vsub(~F, M.ofdv(~F, y0), xb), d), +q2: Nat, +hp2: {p == 1n+(1n+q2) : Nat}, +pr: List<&2, S.D>, +lpr: {M.len(~F, M.ofdv(~F, pr)) == m : Nat}, +hpn: FV.rnn(~F, M.ofdv(~F, pr)), +hzr: BX.rbnd(~F, BX.vsub(~F, xz, M.ofdv(~F, pc)), M.ofdv(~F, pr)), +hpr: M.vbnd.all(~F, M.ofdv(~F, pr), rho), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hrh: O.le(~F, rho, O.mul(F, NW.hnw(~F, p), tt)), +hsq: O.lt(F, O.mul(F, AP.vbit(~F, Nat.div(p, 2n)), SC.qblk(~F, n, m, b, lam, ms, tt)), O.one(F))) -> BK.bgood(~F, n, eqs, xb, BK.rbc(~F, n, m, b, lam, ms, d, rho, p), pc, pr, NU.block(eqs, n, pc, pr, y0, p)):
  SC.block_sc(~F, ~H, n, m, eqs, hn, hh, hbl, pc, lpc, p, xb, xz, lxb, lxz, hz, bb, lam, ms, b, d, rho, hb0, hl0, hm0, hd0, hr0, hbb0, hbb, hq, hJ, hzc, y0, ly0, hy0, q2, hp2, pr, lpr, hpn, hzr, hpr, tt, htt, hdh, hrh, hsq)

def radius_sc(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +d: O.C(F), +rho: O.C(F), +p: Nat, +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +hd0: O.le(~F, O.zero(F), d), +hr0: O.le(~F, O.zero(F), rho), +tt: O.C(F), +htt: O.le(~F, O.zero(F), tt), +hdh: O.le(~F, d, NW.hnw(~F, p)), +hrh: O.le(~F, rho, O.mul(F, NW.hnw(~F, p), tt))) -> O.le(~F, BK.rbc(~F, n, m, b, lam, ms, d, rho, p), O.mul(F, NW.hnw(~F, p), SC.phib(~F, n, m, b, lam, ms, tt))):
  SC.rb_sc(~F, ~H, n, m, b, lam, ms, d, rho, p, hb0, hl0, hm0, hd0, hr0, tt, htt, hdh, hrh)

def phi_ge(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +m: Nat, +b: O.C(F), +lam: O.C(F), +ms: O.C(F), +tt: O.C(F), +hb0: O.le(~F, O.zero(F), b), +hl0: O.le(~F, O.zero(F), lam), +hm0: O.le(~F, O.zero(F), ms), +htt: O.le(~F, O.zero(F), tt)) -> O.le(~F, tt, SC.phib(~F, n, m, b, lam, ms, tt)):
  SC.phib_ge(~F, ~H, n, m, b, lam, ms, tt, hb0, hl0, hm0, htt)
