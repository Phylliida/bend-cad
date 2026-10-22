# bend-cad: lib/gnumer.bend's block and plan return exactly numer.bend's
# sent through the map h : KI.dnum() -> K of laws R (lib/pops.bend): for
# every K, W and R, GN.plan(W, es, nv, sk, h g0, p) is h of NU.plan(es,
# nv, sk, g0, p) (plan_t). Proven like lib/gnewtpf.bend, bottom up through
# numer's definitions. Untrusted; PLAN-sk13w W4.

# Generated from tools/drafts/gplanpf.draft by tools/expand.py; edit the
# draft.


import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/knum.bend as N
import ./certdef.bend as C
import ./kinst.bend as KI
import ./plan.bend as PL
import ./struct.bend as ST
import ./numer.bend as NU
import ./khom.bend as KH
import ./pops.bend as PO
import ./gnumer.bend as GN
import ./gmap.bend as GM
import ./gelimpf.bend as GE
import ./gnewtpf.bend as GW

# A block
# -------

def block_r_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, m: Maybe<&2, S.D>, +n: Nat, +yc: List<&2, S.D>, +ym: List<&2, List<&2, S.D>>, +pc: List<&2, S.D>, +pr: List<&2, S.D>) -> {GN.block.r(~K, ~W, GM.hmd(~K, ~PO.hom(K, W, R), m), n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr)) == GM.hbr(~K, ~PO.hom(K, W, R), NU.block.r(m, n, yc, ym, pc, pr)) : GN.GBR<K>}:
  match m:
    case None{}:
      {==}
    case Some{+r}:
      %GW.mkcert_t(~K, ~W, ~R, n, yc, r, ym, pc, pr) : {GN.GBOk{GN.mkcert(~K, ~W, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), r), KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr))} == GN.GBOk{_} : GN.GBR<K>}
      {==}

def block_ym_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +ym: List<&2, List<&2, S.D>>, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +e: S.D) -> {GN.block.ym(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym), eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), e)) == GM.hbr(~K, ~PO.hom(K, W, R), NU.block.ym(ym, eqs, n, yc, pc, pr, e)) : GN.GBR<K>}:
  %block_r_t(~K, ~W, ~R, NU.rsearch(64n, NU.okr(eqs, n, yc, NU.r0(eqs, n, yc, ym, pc, pr, e), ym, pc, pr), eqs, n, yc, NU.r0(eqs, n, yc, ym, pc, pr, e), ym, pc, pr), n, yc, ym, pc, pr) : {GN.block.ym(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym), eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), e)) == _ : GN.GBR<K>}
  %GW.rsearch_t(~K, ~W, ~R, 64n, NU.okr(eqs, n, yc, NU.r0(eqs, n, yc, ym, pc, pr, e), ym, pc, pr), eqs, n, yc, NU.r0(eqs, n, yc, ym, pc, pr, e), ym, pc, pr) : {GN.block.ym(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym), eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), e)) == GN.block.r(~K, ~W, _, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr)) : GN.GBR<K>}
  %GW.okr_t(~K, ~W, ~R, eqs, n, yc, NU.r0(eqs, n, yc, ym, pc, pr, e), ym, pc, pr) : {GN.block.ym(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym), eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), e)) == GN.block.r(~K, ~W, GN.rsearch(~K, ~W, 64n, _, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.r0(eqs, n, yc, ym, pc, pr, e)), KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr)), n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr)) : GN.GBR<K>}
  %GW.r0_t(~K, ~W, ~R, eqs, n, yc, ym, pc, pr, e) : {GN.block.ym(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym), eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), e)) == GN.block.r(~K, ~W, GN.rsearch(~K, ~W, 64n, GN.okr(~K, ~W, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), _, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr)), eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), _, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr)), n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr)) : GN.GBR<K>}
  {==}

def block_y2_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, m: Maybe<&2, List<&2, List<&2, S.D>>>, +p: Nat, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>) -> {GN.block.y2(~K, ~W, GM.hmm(~K, ~PO.hom(K, W, R), m), p, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr)) == GM.hbr(~K, ~PO.hom(K, W, R), NU.block.y2(m, p, eqs, n, yc, pc, pr)) : GN.GBR<K>}:
  match m:
    case None{}:
      {==}
    case Some{+inv}:
      %block_ym_t(~K, ~W, ~R, NU.ysig(Nat.div(p, 2n), inv), eqs, n, yc, pc, pr, NU.eta(p)) : {GN.block.ym(~K, ~W, GN.ysig(~K, ~W, Nat.div(p, 2n), KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), inv)), eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr), PO.ofd(K, W, NU.eta(p))) == _ : GN.GBR<K>}
      %GW.ysig_t(~K, ~W, ~R, Nat.div(p, 2n), inv) : {GN.block.ym(~K, ~W, GN.ysig(~K, ~W, Nat.div(p, 2n), KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), inv)), eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr), PO.ofd(K, W, NU.eta(p))) == GN.block.ym(~K, ~W, _, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.eta(p))) : GN.GBR<K>}
      %PO.l_ofd(K, W, R)(NU.eta(p)) : {GN.block.ym(~K, ~W, GN.ysig(~K, ~W, Nat.div(p, 2n), KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), inv)), eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr), PO.ofd(K, W, NU.eta(p))) == GN.block.ym(~K, ~W, GN.ysig(~K, ~W, Nat.div(p, 2n), KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), inv)), eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr), _) : GN.GBR<K>}
      {==}

def block_y_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, m: Maybe<&2, List<&2, S.D>>, +p: Nat, +eqs: List<&2, E.QExpr>, +n: Nat, +pc: List<&2, S.D>, +pr: List<&2, S.D>) -> {GN.block.y(~K, ~W, GM.hmv(~K, ~PO.hom(K, W, R), m), p, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr)) == GM.hbr(~K, ~PO.hom(K, W, R), NU.block.y(m, p, eqs, n, pc, pr)) : GN.GBR<K>}:
  match m:
    case None{}:
      {==}
    case Some{+yc}:
      %block_y2_t(~K, ~W, ~R, NU.dinverse(n, NU.wbits(p), NU.jac(eqs, n, NU.dapp(yc, pc))), p, eqs, n, yc, pc, pr) : {GN.block.y2(~K, ~W, GN.dinverse(~K, ~W, n, NU.wbits(p), GN.jac(~K, ~W, eqs, n, GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc)))), p, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr)) == _ : GN.GBR<K>}
      %GE.dinverse_t(~K, ~W, ~R, n, NU.wbits(p), NU.jac(eqs, n, NU.dapp(yc, pc))) : {GN.block.y2(~K, ~W, GN.dinverse(~K, ~W, n, NU.wbits(p), GN.jac(~K, ~W, eqs, n, GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc)))), p, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr)) == GN.block.y2(~K, ~W, _, p, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr)) : GN.GBR<K>}
      %GW.jac_t(~K, ~W, ~R, eqs, n, NU.dapp(yc, pc)) : {GN.block.y2(~K, ~W, GN.dinverse(~K, ~W, n, NU.wbits(p), GN.jac(~K, ~W, eqs, n, GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc)))), p, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr)) == GN.block.y2(~K, ~W, GN.dinverse(~K, ~W, n, NU.wbits(p), _), p, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr)) : GN.GBR<K>}
      %GE.dapp_t(~K, ~W, ~R, yc, pc) : {GN.block.y2(~K, ~W, GN.dinverse(~K, ~W, n, NU.wbits(p), GN.jac(~K, ~W, eqs, n, GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc)))), p, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr)) == GN.block.y2(~K, ~W, GN.dinverse(~K, ~W, n, NU.wbits(p), GN.jac(~K, ~W, eqs, n, _)), p, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr)) : GN.GBR<K>}
      {==}

def block_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +eqs: List<&2, E.QExpr>, +n: Nat, +pc: List<&2, S.D>, +pr: List<&2, S.D>, +y0: List<&2, S.D>, +p: Nat) -> {GN.block(~K, ~W, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y0), p) == GM.hbr(~K, ~PO.hom(K, W, R), NU.block(eqs, n, pc, pr, y0, p)) : GN.GBR<K>}:
  %block_y_t(~K, ~W, ~R, NU.newton(40n, eqs, n, pc, p, NU.NMore{y0}), p, eqs, n, pc, pr) : {GN.block(~K, ~W, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y0), p) == _ : GN.GBR<K>}
  %GW.newton_t(~K, ~W, ~R, 40n, eqs, n, pc, p, NU.NMore{y0}) : {GN.block(~K, ~W, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), y0), p) == GN.block.y(~K, ~W, _, p, eqs, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr)) : GN.GBR<K>}
  {==}

def bcert_n_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +n: Nat, +pars: List<&2, Nat>, +sys: List<&2, E.QExpr>, +g0b: List<&2, S.D>, +p: Nat, +o: Nat, +gc: List<&2, S.D>, +gr: List<&2, S.D>) -> {GN.bcert.n(~K, ~W, n, pars, sys, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, o, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)) == GM.hbr(~K, ~PO.hom(K, W, R), NU.bcert.n(n, pars, sys, g0b, p, o, gc, gr)) : GN.GBR<K>}:
  %block_t(~K, ~W, ~R, PL.renames(o, n, pars, PL.takeq(n, sys)), n, NU.dpick(gc, pars), NU.dpick(gr, pars), NU.dtake(n, NU.ddrop(o, g0b)), p) : {GN.bcert.n(~K, ~W, n, pars, sys, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, o, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)) == _ : GN.GBR<K>}
  %GW.dpick_t(~K, ~W, ~R, gc, pars) : {GN.bcert.n(~K, ~W, n, pars, sys, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, o, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)) == GN.block(~K, ~W, PL.renames(o, n, pars, PL.takeq(n, sys)), n, _, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dpick(gr, pars)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dtake(n, NU.ddrop(o, g0b))), p) : GN.GBR<K>}
  %GW.dpick_t(~K, ~W, ~R, gr, pars) : {GN.bcert.n(~K, ~W, n, pars, sys, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, o, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)) == GN.block(~K, ~W, PL.renames(o, n, pars, PL.takeq(n, sys)), n, GN.dpick(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), pars), _, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dtake(n, NU.ddrop(o, g0b))), p) : GN.GBR<K>}
  %GW.dtake_t(~K, ~W, ~R, n, NU.ddrop(o, g0b)) : {GN.bcert.n(~K, ~W, n, pars, sys, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, o, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)) == GN.block(~K, ~W, PL.renames(o, n, pars, PL.takeq(n, sys)), n, GN.dpick(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), pars), GN.dpick(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), pars), _, p) : GN.GBR<K>}
  %GE.ddrop_t(~K, ~W, ~R, o, g0b) : {GN.bcert.n(~K, ~W, n, pars, sys, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, o, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)) == GN.block(~K, ~W, PL.renames(o, n, pars, PL.takeq(n, sys)), n, GN.dpick(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), pars), GN.dpick(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), pars), GN.dtake(~K, ~W, n, _), p) : GN.GBR<K>}
  {==}

def bcert_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, bs: List<&2, ST.SkB>, +sys: List<&2, E.QExpr>, +g0b: List<&2, S.D>, +p: Nat, +o: Nat, +gc: List<&2, S.D>, +gr: List<&2, S.D>) -> {GN.bcert(~K, ~W, bs, sys, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, o, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)) == GM.hbr(~K, ~PO.hom(K, W, R), NU.bcert(bs, sys, g0b, p, o, gc, gr)) : GN.GBR<K>}:
  match bs:
    case Nil{}:
      {==}
    case Con{ST.SkB{es, vs, pars}, t}:
      bcert_n_t(~K, ~W, ~R, ST.len(es), pars, sys, g0b, p, o, gc, gr)

# The blocks in turn
# ------------------

def revpb_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, xs: List<&2, PL.PBlock<KI.dnum()>>, acc: List<&2, PL.PBlock<KI.dnum()>>) -> {GN.revpb.go(~K, ~W, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), acc)) == KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.revpb.go(xs, acc)) : List<&2, PL.PBlock<K>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{b, t}:
      revpb_t(~K, ~W, ~R, t, Con{b, acc})

# the box grown by one certificate's centers and radii
def gc2_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +gc: List<&2, S.D>, +c: C.Cert<KI.dnum()>) -> {GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), GN.cert.yc(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c))) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dapp(gc, NU.cert.yc(c))) : N.KVec(~K)}:
  %GE.dapp_t(~K, ~W, ~R, gc, NU.cert.yc(c)) : {GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), GN.cert.yc(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c))) == _ : N.KVec(~K)}
  %GW.cyc_t(~K, ~W, ~R, c) : {GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), GN.cert.yc(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c))) == GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), _) : N.KVec(~K)}
  {==}

def gr2_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +gr: List<&2, S.D>, +n: Nat, +c: C.Cert<KI.dnum()>) -> {GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), GN.dtake(~K, ~W, n, GN.cert.yr(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c)))) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dapp(gr, NU.dtake(n, NU.cert.yr(c)))) : N.KVec(~K)}:
  %GE.dapp_t(~K, ~W, ~R, gr, NU.dtake(n, NU.cert.yr(c))) : {GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), GN.dtake(~K, ~W, n, GN.cert.yr(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c)))) == _ : N.KVec(~K)}
  %GW.dtake_t(~K, ~W, ~R, n, NU.cert.yr(c)) : {GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), GN.dtake(~K, ~W, n, GN.cert.yr(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c)))) == GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), _) : N.KVec(~K)}
  %GW.cyr_t(~K, ~W, ~R, c) : {GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), GN.dtake(~K, ~W, n, GN.cert.yr(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c)))) == GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), GN.dtake(~K, ~W, n, _)) : N.KVec(~K)}
  {==}

def pblocks_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, bs: List<&2, ST.SkB>, cur: NU.BR, +sys: List<&2, E.QExpr>, +g0b: List<&2, S.D>, +p: Nat, +o: Nat, +gc: List<&2, S.D>, +gr: List<&2, S.D>, +acc: List<&2, PL.PBlock<KI.dnum()>>) -> {GN.pblocks(~K, ~W, bs, GM.hbr(~K, ~PO.hom(K, W, R), cur), sys, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, o, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), acc)) == GM.hpbr(~K, ~PO.hom(K, W, R), NU.pblocks(bs, cur, sys, g0b, p, o, gc, gr, acc)) : GN.GPBR<K>}:
  match bs cur:
    case Nil{} NU.BOk{c}:
      %revpb_t(~K, ~W, ~R, acc, Nil{}) : {GN.GPBOk{GN.GPB{GN.revpb.go(~K, ~W, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), acc), Nil{}), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)}} == GN.GPBOk{GN.GPB{_, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)}} : GN.GPBR<K>}
      {==}
    case Nil{} NU.BRetry{}:
      %revpb_t(~K, ~W, ~R, acc, Nil{}) : {GN.GPBOk{GN.GPB{GN.revpb.go(~K, ~W, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), acc), Nil{}), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)}} == GN.GPBOk{GN.GPB{_, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)}} : GN.GPBR<K>}
      {==}
    case Nil{} NU.BStop{}:
      %revpb_t(~K, ~W, ~R, acc, Nil{}) : {GN.GPBOk{GN.GPB{GN.revpb.go(~K, ~W, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), acc), Nil{}), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)}} == GN.GPBOk{GN.GPB{_, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)}} : GN.GPBR<K>}
      {==}
    case Con{ST.SkB{+es, vs, +pars}, +t} NU.BRetry{}:
      {==}
    case Con{ST.SkB{+es, vs, +pars}, +t} NU.BStop{}:
      {==}
    case Con{ST.SkB{+es, vs, +pars}, +t} NU.BOk{+c}:
      %pblocks_t(~K, ~W, ~R, t, NU.bcert(t, PL.dropq(ST.len(es), sys), g0b, p, Nat.add(o, ST.len(es)), NU.dapp(gc, NU.cert.yc(c)), NU.dapp(gr, NU.dtake(ST.len(es), NU.cert.yr(c)))), PL.dropq(ST.len(es), sys), g0b, p, Nat.add(o, ST.len(es)), NU.dapp(gc, NU.cert.yc(c)), NU.dapp(gr, NU.dtake(ST.len(es), NU.cert.yr(c))), Con{PL.PBlock{ST.len(es), pars, c}, acc}) : {GN.pblocks(~K, ~W, t, GN.bcert(~K, ~W, t, PL.dropq(ST.len(es), sys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, Nat.add(o, ST.len(es)), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), GN.cert.yc(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c))), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), GN.dtake(~K, ~W, ST.len(es), GN.cert.yr(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c))))), PL.dropq(ST.len(es), sys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, Nat.add(o, ST.len(es)), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), GN.cert.yc(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c))), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), GN.dtake(~K, ~W, ST.len(es), GN.cert.yr(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c)))), Con{PL.PBlock{ST.len(es), pars, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c)}, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), acc)}) == _ : GN.GPBR<K>}
      %bcert_t(~K, ~W, ~R, t, PL.dropq(ST.len(es), sys), g0b, p, Nat.add(o, ST.len(es)), NU.dapp(gc, NU.cert.yc(c)), NU.dapp(gr, NU.dtake(ST.len(es), NU.cert.yr(c)))) : {GN.pblocks(~K, ~W, t, GN.bcert(~K, ~W, t, PL.dropq(ST.len(es), sys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, Nat.add(o, ST.len(es)), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), GN.cert.yc(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c))), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), GN.dtake(~K, ~W, ST.len(es), GN.cert.yr(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c))))), PL.dropq(ST.len(es), sys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, Nat.add(o, ST.len(es)), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), GN.cert.yc(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c))), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), GN.dtake(~K, ~W, ST.len(es), GN.cert.yr(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c)))), Con{PL.PBlock{ST.len(es), pars, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c)}, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), acc)}) == GN.pblocks(~K, ~W, t, _, PL.dropq(ST.len(es), sys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, Nat.add(o, ST.len(es)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dapp(gc, NU.cert.yc(c))), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dapp(gr, NU.dtake(ST.len(es), NU.cert.yr(c)))), Con{PL.PBlock{ST.len(es), pars, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c)}, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), acc)}) : GN.GPBR<K>}
      %gc2_t(~K, ~W, ~R, gc, c) : {GN.pblocks(~K, ~W, t, GN.bcert(~K, ~W, t, PL.dropq(ST.len(es), sys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, Nat.add(o, ST.len(es)), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), GN.cert.yc(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c))), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), GN.dtake(~K, ~W, ST.len(es), GN.cert.yr(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c))))), PL.dropq(ST.len(es), sys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, Nat.add(o, ST.len(es)), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), GN.cert.yc(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c))), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), GN.dtake(~K, ~W, ST.len(es), GN.cert.yr(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c)))), Con{PL.PBlock{ST.len(es), pars, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c)}, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), acc)}) == GN.pblocks(~K, ~W, t, GN.bcert(~K, ~W, t, PL.dropq(ST.len(es), sys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, Nat.add(o, ST.len(es)), _, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dapp(gr, NU.dtake(ST.len(es), NU.cert.yr(c))))), PL.dropq(ST.len(es), sys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, Nat.add(o, ST.len(es)), _, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dapp(gr, NU.dtake(ST.len(es), NU.cert.yr(c)))), Con{PL.PBlock{ST.len(es), pars, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c)}, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), acc)}) : GN.GPBR<K>}
      %gr2_t(~K, ~W, ~R, gr, ST.len(es), c) : {GN.pblocks(~K, ~W, t, GN.bcert(~K, ~W, t, PL.dropq(ST.len(es), sys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, Nat.add(o, ST.len(es)), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), GN.cert.yc(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c))), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), GN.dtake(~K, ~W, ST.len(es), GN.cert.yr(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c))))), PL.dropq(ST.len(es), sys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, Nat.add(o, ST.len(es)), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), GN.cert.yc(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c))), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), GN.dtake(~K, ~W, ST.len(es), GN.cert.yr(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c)))), Con{PL.PBlock{ST.len(es), pars, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c)}, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), acc)}) == GN.pblocks(~K, ~W, t, GN.bcert(~K, ~W, t, PL.dropq(ST.len(es), sys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, Nat.add(o, ST.len(es)), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), GN.cert.yc(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c))), _), PL.dropq(ST.len(es), sys), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, Nat.add(o, ST.len(es)), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), GN.cert.yc(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c))), _, Con{PL.PBlock{ST.len(es), pars, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c)}, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), acc)}) : GN.GPBR<K>}
      {==}

# The plan
# --------

def unperm_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, n: Nat, +k: Nat, +xs: List<&2, S.D>, +vp: List<&2, Nat>) -> {GN.unperm(~K, ~W, n, k, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), vp) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.unperm(n, k, xs, vp)) : N.KVec(~K)}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      %GW.dlook_t(~K, ~W, ~R, xs, ST.pos(k, vp)) : {Con{GN.dlook(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), ST.pos(k, vp)), GN.unperm(~K, ~W, m, 1n+k, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), vp)} == Con{_, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.unperm(m, 1n+k, xs, vp))} : N.KVec(~K)}
      %unperm_t(~K, ~W, ~R, m, 1n+k, xs, vp) : {Con{GN.dlook(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), ST.pos(k, vp)), GN.unperm(~K, ~W, m, 1n+k, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), vp)} == Con{GN.dlook(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), ST.pos(k, vp)), _} : N.KVec(~K)}
      {==}

def plan_fin_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +nv: Nat, m: NU.PBR) -> {GN.plan.fin(~K, ~W, vp, ep, np, nv, GM.hpbr(~K, ~PO.hom(K, W, R), m)) == GM.hpr(~K, ~PO.hom(K, W, R), NU.plan.fin(vp, ep, np, nv, m)) : GN.GPR<K>}:
  match m:
    case NU.PBRetry{}:
      {==}
    case NU.PBStop{}:
      {==}
    case NU.PBOk{NU.PB{+bs, +gc, +gr}}:
      %unperm_t(~K, ~W, ~R, nv, 0n, gc, vp) : {GN.GPOk{GN.GNP{PL.Plan{vp, ep, np, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), bs)}, GN.unperm(~K, ~W, nv, 0n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), vp), GN.unperm(~K, ~W, nv, 0n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), vp)}} == GN.GPOk{GN.GNP{PL.Plan{vp, ep, np, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), bs)}, _, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.unperm(nv, 0n, gr, vp))}} : GN.GPR<K>}
      %unperm_t(~K, ~W, ~R, nv, 0n, gr, vp) : {GN.GPOk{GN.GNP{PL.Plan{vp, ep, np, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), bs)}, GN.unperm(~K, ~W, nv, 0n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), vp), GN.unperm(~K, ~W, nv, 0n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), vp)}} == GN.GPOk{GN.GNP{PL.Plan{vp, ep, np, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), bs)}, GN.unperm(~K, ~W, nv, 0n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), vp), _}} : GN.GPR<K>}
      {==}

def plan_go_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +es: List<&2, E.QExpr>, +nv: Nat, +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, ST.SkB>, +g0b: List<&2, S.D>, +p: Nat) -> {GN.plan.go(~K, ~W, es, nv, vp, ep, np, bs, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p) == GM.hpr(~K, ~PO.hom(K, W, R), NU.plan.go(es, nv, vp, ep, np, bs, g0b, p)) : GN.GPR<K>}:
  %plan_fin_t(~K, ~W, ~R, vp, ep, np, nv, NU.pblocks(bs, NU.bcert(bs, PL.reorder(vp, es, ep), g0b, p, np, NU.dtake(np, g0b), NU.dreps(np, NU.dzero())), PL.reorder(vp, es, ep), g0b, p, np, NU.dtake(np, g0b), NU.dreps(np, NU.dzero()), Nil{})) : {GN.plan.go(~K, ~W, es, nv, vp, ep, np, bs, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p) == _ : GN.GPR<K>}
  %pblocks_t(~K, ~W, ~R, bs, NU.bcert(bs, PL.reorder(vp, es, ep), g0b, p, np, NU.dtake(np, g0b), NU.dreps(np, NU.dzero())), PL.reorder(vp, es, ep), g0b, p, np, NU.dtake(np, g0b), NU.dreps(np, NU.dzero()), Nil{}) : {GN.plan.go(~K, ~W, es, nv, vp, ep, np, bs, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p) == GN.plan.fin(~K, ~W, vp, ep, np, nv, _) : GN.GPR<K>}
  %bcert_t(~K, ~W, ~R, bs, PL.reorder(vp, es, ep), g0b, p, np, NU.dtake(np, g0b), NU.dreps(np, NU.dzero())) : {GN.plan.go(~K, ~W, es, nv, vp, ep, np, bs, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p) == GN.plan.fin(~K, ~W, vp, ep, np, nv, GN.pblocks(~K, ~W, bs, _, PL.reorder(vp, es, ep), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, np, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dtake(np, g0b)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dreps(np, NU.dzero())), Nil{})) : GN.GPR<K>}
  %GW.dtake_t(~K, ~W, ~R, np, g0b) : {GN.plan.go(~K, ~W, es, nv, vp, ep, np, bs, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p) == GN.plan.fin(~K, ~W, vp, ep, np, nv, GN.pblocks(~K, ~W, bs, GN.bcert(~K, ~W, bs, PL.reorder(vp, es, ep), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, np, _, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dreps(np, NU.dzero()))), PL.reorder(vp, es, ep), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, np, _, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dreps(np, NU.dzero())), Nil{})) : GN.GPR<K>}
  %GE.dreps_t(~K, ~W, ~R, np, NU.dzero()) : {GN.plan.go(~K, ~W, es, nv, vp, ep, np, bs, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p) == GN.plan.fin(~K, ~W, vp, ep, np, nv, GN.pblocks(~K, ~W, bs, GN.bcert(~K, ~W, bs, PL.reorder(vp, es, ep), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, np, GN.dtake(~K, ~W, np, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b)), _), PL.reorder(vp, es, ep), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, np, GN.dtake(~K, ~W, np, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b)), _, Nil{})) : GN.GPR<K>}
  %GE.dzero_t(~K, ~W, ~R) : {GN.plan.go(~K, ~W, es, nv, vp, ep, np, bs, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p) == GN.plan.fin(~K, ~W, vp, ep, np, nv, GN.pblocks(~K, ~W, bs, GN.bcert(~K, ~W, bs, PL.reorder(vp, es, ep), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, np, GN.dtake(~K, ~W, np, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b)), GN.dreps(~K, ~W, np, _)), PL.reorder(vp, es, ep), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b), p, np, GN.dtake(~K, ~W, np, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0b)), GN.dreps(~K, ~W, np, _), Nil{})) : GN.GPR<K>}
  {==}

# numer's plan at any K is numer's, mapped
def plan_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +es: List<&2, E.QExpr>, +nv: Nat, sk: ST.Skel, +g0: List<&2, S.D>, +p: Nat) -> {GN.plan(~K, ~W, es, nv, sk, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p) == GM.hpr(~K, ~PO.hom(K, W, R), NU.plan(es, nv, sk, g0, p)) : GN.GPR<K>}:
  match sk:
    case ST.Skel{+vp, +ep, +np, +bs, red}:
      %plan_go_t(~K, ~W, ~R, es, nv, vp, ep, np, bs, NU.dpick(g0, vp), p) : {GN.plan.go(~K, ~W, es, nv, vp, ep, np, bs, GN.dpick(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), vp), p) == _ : GN.GPR<K>}
      %GW.dpick_t(~K, ~W, ~R, g0, vp) : {GN.plan.go(~K, ~W, es, nv, vp, ep, np, bs, GN.dpick(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), vp), p) == GN.plan.go(~K, ~W, es, nv, vp, ep, np, bs, _, p) : GN.GPR<K>}
      {==}
