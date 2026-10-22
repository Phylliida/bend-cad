# bend-cad: the fast solver (lib/fast.bend) returns exactly what the solver
# (lib/solve.bend) returns, for any computing numbers K with the proposer's
# operations W and laws R relating them to KI.dnum() (lib/pops.bend): its
# proposer gives numer's plan through the map (lib/gplanpf.bend: plan_t),
# its verdict on the mapped answer is SO.final's (the checker through the
# map: lib/planhpf.bend), and the answer sent back through tod is the
# solver's. At the CLI's word dyadics in base 2^14 (FS.wsolve), with the
# word laws at that base, it is SO.solve: wsolve_eq. Every law about the
# solver holds for it (PLAN-sk13w W6).


import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/knum.bend as N
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ./certdef.bend as C
import ./karith.bend as KA
import ./kinst.bend as KI
import ./plan.bend as PL
import ./struct.bend as ST
import ./wfdec.bend as WF
import ./verdict.bend as VD
import ./cert.bend as CK
import ./solve.bend as SO
import ./numer.bend as NU
import ./pops.bend as PO
import ./gnumer.bend as GN
import ./gmap.bend as GM
import ./khom.bend as KH
import ./khompf.bend as KP
import ./planhpf.bend as PH
import ./fast.bend as FS

# Conversions with S.D
# --------------------

def ofdv_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, xs: List<&2, S.D>) -> {FS.ofdv(~K, ~W, xs) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs) : N.KVec(~K)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %PO.l_ofd(K, W, R)(x) : {Con{PO.ofd(K, W, x), FS.ofdv(~K, ~W, t)} == Con{_, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t)} : N.KVec(~K)}
      %ofdv_t(~K, ~W, ~R, t) : {Con{PO.ofd(K, W, x), FS.ofdv(~K, ~W, t)} == Con{PO.ofd(K, W, x), _} : N.KVec(~K)}
      {==}

def todv_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, xs: List<&2, S.D>) -> {FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs)) == xs : List<&2, S.D>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %PO.l_tod(K, W, R)(x) : {Con{PO.tod(K, W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t))} == Con{_, t} : List<&2, S.D>}
      %todv_t(~K, ~W, ~R, t) : {Con{PO.tod(K, W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t))} == Con{PO.tod(K, W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x)), _} : List<&2, S.D>}
      {==}

def todm_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, a: List<&2, List<&2, S.D>>) -> {FS.todm(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), a)) == a : List<&2, List<&2, S.D>>}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      %todv_t(~K, ~W, ~R, r) : {Con{FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r)), FS.todm(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t))} == Con{_, t} : List<&2, List<&2, S.D>>}
      %todm_t(~K, ~W, ~R, t) : {Con{FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r)), FS.todm(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t))} == Con{FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r)), _} : List<&2, List<&2, S.D>>}
      {==}


def todcert_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, c: C.Cert<KI.dnum()>) -> {FS.todcert(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c)) == c : C.Cert<KI.dnum()>}:
  match c:
    case C.Cert{+yc, +yr, +q, +ym, +pc, +pr}:
      %todv_t(~K, ~W, ~R, yc) : {C.Cert{FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yr)), PO.tod(K, W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), q)), FS.todm(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr))} == C.Cert{_, yr, q, ym, pc, pr} : C.Cert<KI.dnum()>}
      %todv_t(~K, ~W, ~R, yr) : {C.Cert{FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yr)), PO.tod(K, W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), q)), FS.todm(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr))} == C.Cert{FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc)), _, q, ym, pc, pr} : C.Cert<KI.dnum()>}
      %PO.l_tod(K, W, R)(q) : {C.Cert{FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yr)), PO.tod(K, W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), q)), FS.todm(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr))} == C.Cert{FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yr)), _, ym, pc, pr} : C.Cert<KI.dnum()>}
      %todm_t(~K, ~W, ~R, ym) : {C.Cert{FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yr)), PO.tod(K, W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), q)), FS.todm(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr))} == C.Cert{FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yr)), PO.tod(K, W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), q)), _, pc, pr} : C.Cert<KI.dnum()>}
      %todv_t(~K, ~W, ~R, pc) : {C.Cert{FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yr)), PO.tod(K, W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), q)), FS.todm(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr))} == C.Cert{FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yr)), PO.tod(K, W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), q)), FS.todm(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym)), _, pr} : C.Cert<KI.dnum()>}
      %todv_t(~K, ~W, ~R, pr) : {C.Cert{FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yr)), PO.tod(K, W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), q)), FS.todm(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pr))} == C.Cert{FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), yr)), PO.tod(K, W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), q)), FS.todm(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), ym)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), pc)), _} : C.Cert<KI.dnum()>}
      {==}

def todpb_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, b: PL.PBlock<KI.dnum()>) -> {FS.todpb(~K, ~W, KH.hpb(~KI.dnum(), ~K, ~PO.hom(K, W, R), b)) == b : PL.PBlock<KI.dnum()>}:
  match b:
    case PL.PBlock{+n, +pars, +c}:
      %todcert_t(~K, ~W, ~R, c) : {PL.PBlock{n, pars, FS.todcert(~K, ~W, KH.hcert(~KI.dnum(), ~K, ~PO.hom(K, W, R), c))} == PL.PBlock{n, pars, _} : PL.PBlock<KI.dnum()>}
      {==}

def todpbs_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, bs: List<&2, PL.PBlock<KI.dnum()>>) -> {FS.todpbs(~K, ~W, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), bs)) == bs : List<&2, PL.PBlock<KI.dnum()>>}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %todpb_t(~K, ~W, ~R, b) : {Con{FS.todpb(~K, ~W, KH.hpb(~KI.dnum(), ~K, ~PO.hom(K, W, R), b)), FS.todpbs(~K, ~W, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), t))} == Con{_, t} : List<&2, PL.PBlock<KI.dnum()>>}
      %todpbs_t(~K, ~W, ~R, t) : {Con{FS.todpb(~K, ~W, KH.hpb(~KI.dnum(), ~K, ~PO.hom(K, W, R), b)), FS.todpbs(~K, ~W, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), t))} == Con{FS.todpb(~K, ~W, KH.hpb(~KI.dnum(), ~K, ~PO.hom(K, W, R), b)), _} : List<&2, PL.PBlock<KI.dnum()>>}
      {==}

def todplan_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, p: PL.Plan<KI.dnum()>) -> {FS.todplan(~K, ~W, KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)) == p : PL.Plan<KI.dnum()>}:
  match p:
    case PL.Plan{+vp, +ep, +np, +bs}:
      %todpbs_t(~K, ~W, ~R, bs) : {PL.Plan{vp, ep, np, FS.todpbs(~K, ~W, KH.hpbs(~KI.dnum(), ~K, ~PO.hom(K, W, R), bs))} == PL.Plan{vp, ep, np, _} : PL.Plan<KI.dnum()>}
      {==}

def len_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, xs: List<&2, S.D>) -> {List.length(&2, N.NC(K), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs)) == List.length(&2, N.NC(KI.dnum()), xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %len_t(~K, ~W, ~R, t) : {1n+List.length(&2, N.NC(K), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t)) == 1n+_ : Nat}
      {==}

# The verdict
# -----------

def shape_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +nv: Nat, +nq: Nat, +gc: List<&2, S.D>, +pins: List<&2, Nat>, p: PL.Plan<KI.dnum()>) -> {FS.shape(~K, nv, nq, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), pins, KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)) == SO.shape(nv, nq, gc, pins, p) : Bool}:
  match p:
    case PL.Plan{+vp, +ep, +np, bs}:
      %KP.klen_h(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc) : {KA.band(KA.nateq(KA.klen(~K, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc)), nv), KA.band(KA.nateq(PL.nlen(vp), nv), KA.band(SV.distinct(vp), KA.band(KA.nateq(PL.nlen(ep), nq), SO.nl_eq(SO.ntake(np, vp), pins))))) == KA.band(KA.nateq(_, nv), KA.band(KA.nateq(PL.nlen(vp), nv), KA.band(SV.distinct(vp), KA.band(KA.nateq(PL.nlen(ep), nq), SO.nl_eq(SO.ntake(np, vp), pins))))) : Bool}
      {==}


# SO.final's verdict on an answer is FS.final's on its image
def final_c(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +sk: SK.Sketch, +g0: List<&2, S.D>, +ok: Bool, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +gc: List<&2, S.D>, +gr: List<&2, S.D>, +p: PL.Plan<KI.dnum()>) -> {FS.final(~K, ~W, sk, g0, FS.FOut{ok, cls, pins, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)}) == SO.final(sk, g0, SO.Out{ok, cls, pins, gc, gr, p}) : Bool}:
  %todv_t(~K, ~W, ~R, gc) : {KA.band(SV.held(pins, g0, FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr))), KA.band(WF.wf_dec(SV.mark(SV.reds(cls), sk)), KA.band(BX.Sketch.within(SV.mark(SV.reds(cls), sk), List.length(&2, N.NC(K), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc))), KA.band(PL.check(~K, SV.solved(sk, SV.reds(cls), SV.dropped(cls)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)), KA.band(PL.check_sides(~K, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)), KA.band(FS.shape(~K, SO.nvars(sk), CK.eqlen(SV.solved(sk, SV.reds(cls), SV.dropped(cls))), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), pins, KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)), VD.exact(sk, cls))))))) == KA.band(SV.held(pins, g0, _, gr), KA.band(WF.wf_dec(SV.mark(SV.reds(cls), sk)), KA.band(BX.Sketch.within(SV.mark(SV.reds(cls), sk), List.length(&2, N.NC(KI.dnum()), gc)), KA.band(PL.check(~KI.dnum(), SV.solved(sk, SV.reds(cls), SV.dropped(cls)), gc, gr, p), KA.band(PL.check_sides(~KI.dnum(), SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk)), gc, gr), KA.band(SO.shape(SO.nvars(sk), CK.eqlen(SV.solved(sk, SV.reds(cls), SV.dropped(cls))), gc, pins, p), VD.exact(sk, cls))))))) : Bool}
  %todv_t(~K, ~W, ~R, gr) : {KA.band(SV.held(pins, g0, FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr))), KA.band(WF.wf_dec(SV.mark(SV.reds(cls), sk)), KA.band(BX.Sketch.within(SV.mark(SV.reds(cls), sk), List.length(&2, N.NC(K), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc))), KA.band(PL.check(~K, SV.solved(sk, SV.reds(cls), SV.dropped(cls)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)), KA.band(PL.check_sides(~K, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)), KA.band(FS.shape(~K, SO.nvars(sk), CK.eqlen(SV.solved(sk, SV.reds(cls), SV.dropped(cls))), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), pins, KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)), VD.exact(sk, cls))))))) == KA.band(SV.held(pins, g0, FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc)), _), KA.band(WF.wf_dec(SV.mark(SV.reds(cls), sk)), KA.band(BX.Sketch.within(SV.mark(SV.reds(cls), sk), List.length(&2, N.NC(KI.dnum()), gc)), KA.band(PL.check(~KI.dnum(), SV.solved(sk, SV.reds(cls), SV.dropped(cls)), gc, gr, p), KA.band(PL.check_sides(~KI.dnum(), SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk)), gc, gr), KA.band(SO.shape(SO.nvars(sk), CK.eqlen(SV.solved(sk, SV.reds(cls), SV.dropped(cls))), gc, pins, p), VD.exact(sk, cls))))))) : Bool}
  %len_t(~K, ~W, ~R, gc) : {KA.band(SV.held(pins, g0, FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr))), KA.band(WF.wf_dec(SV.mark(SV.reds(cls), sk)), KA.band(BX.Sketch.within(SV.mark(SV.reds(cls), sk), List.length(&2, N.NC(K), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc))), KA.band(PL.check(~K, SV.solved(sk, SV.reds(cls), SV.dropped(cls)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)), KA.band(PL.check_sides(~K, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)), KA.band(FS.shape(~K, SO.nvars(sk), CK.eqlen(SV.solved(sk, SV.reds(cls), SV.dropped(cls))), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), pins, KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)), VD.exact(sk, cls))))))) == KA.band(SV.held(pins, g0, FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr))), KA.band(WF.wf_dec(SV.mark(SV.reds(cls), sk)), KA.band(BX.Sketch.within(SV.mark(SV.reds(cls), sk), _), KA.band(PL.check(~KI.dnum(), SV.solved(sk, SV.reds(cls), SV.dropped(cls)), gc, gr, p), KA.band(PL.check_sides(~KI.dnum(), SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk)), gc, gr), KA.band(SO.shape(SO.nvars(sk), CK.eqlen(SV.solved(sk, SV.reds(cls), SV.dropped(cls))), gc, pins, p), VD.exact(sk, cls))))))) : Bool}
  %PH.pcheck_h(~KI.dnum(), ~K, ~PO.hom(K, W, R), SV.solved(sk, SV.reds(cls), SV.dropped(cls)), gc, gr, p) : {KA.band(SV.held(pins, g0, FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr))), KA.band(WF.wf_dec(SV.mark(SV.reds(cls), sk)), KA.band(BX.Sketch.within(SV.mark(SV.reds(cls), sk), List.length(&2, N.NC(K), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc))), KA.band(PL.check(~K, SV.solved(sk, SV.reds(cls), SV.dropped(cls)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)), KA.band(PL.check_sides(~K, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)), KA.band(FS.shape(~K, SO.nvars(sk), CK.eqlen(SV.solved(sk, SV.reds(cls), SV.dropped(cls))), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), pins, KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)), VD.exact(sk, cls))))))) == KA.band(SV.held(pins, g0, FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr))), KA.band(WF.wf_dec(SV.mark(SV.reds(cls), sk)), KA.band(BX.Sketch.within(SV.mark(SV.reds(cls), sk), List.length(&2, N.NC(K), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc))), KA.band(_, KA.band(PL.check_sides(~KI.dnum(), SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk)), gc, gr), KA.band(SO.shape(SO.nvars(sk), CK.eqlen(SV.solved(sk, SV.reds(cls), SV.dropped(cls))), gc, pins, p), VD.exact(sk, cls))))))) : Bool}
  %PH.check_sides_h(~KI.dnum(), ~K, ~PO.hom(K, W, R), SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk)), gc, gr) : {KA.band(SV.held(pins, g0, FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr))), KA.band(WF.wf_dec(SV.mark(SV.reds(cls), sk)), KA.band(BX.Sketch.within(SV.mark(SV.reds(cls), sk), List.length(&2, N.NC(K), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc))), KA.band(PL.check(~K, SV.solved(sk, SV.reds(cls), SV.dropped(cls)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)), KA.band(PL.check_sides(~K, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)), KA.band(FS.shape(~K, SO.nvars(sk), CK.eqlen(SV.solved(sk, SV.reds(cls), SV.dropped(cls))), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), pins, KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)), VD.exact(sk, cls))))))) == KA.band(SV.held(pins, g0, FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr))), KA.band(WF.wf_dec(SV.mark(SV.reds(cls), sk)), KA.band(BX.Sketch.within(SV.mark(SV.reds(cls), sk), List.length(&2, N.NC(K), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc))), KA.band(PL.check(~K, SV.solved(sk, SV.reds(cls), SV.dropped(cls)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)), KA.band(_, KA.band(SO.shape(SO.nvars(sk), CK.eqlen(SV.solved(sk, SV.reds(cls), SV.dropped(cls))), gc, pins, p), VD.exact(sk, cls))))))) : Bool}
  %shape_t(~K, ~W, ~R, SO.nvars(sk), CK.eqlen(SV.solved(sk, SV.reds(cls), SV.dropped(cls))), gc, pins, p) : {KA.band(SV.held(pins, g0, FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr))), KA.band(WF.wf_dec(SV.mark(SV.reds(cls), sk)), KA.band(BX.Sketch.within(SV.mark(SV.reds(cls), sk), List.length(&2, N.NC(K), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc))), KA.band(PL.check(~K, SV.solved(sk, SV.reds(cls), SV.dropped(cls)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)), KA.band(PL.check_sides(~K, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)), KA.band(FS.shape(~K, SO.nvars(sk), CK.eqlen(SV.solved(sk, SV.reds(cls), SV.dropped(cls))), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), pins, KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)), VD.exact(sk, cls))))))) == KA.band(SV.held(pins, g0, FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr))), KA.band(WF.wf_dec(SV.mark(SV.reds(cls), sk)), KA.band(BX.Sketch.within(SV.mark(SV.reds(cls), sk), List.length(&2, N.NC(K), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc))), KA.band(PL.check(~K, SV.solved(sk, SV.reds(cls), SV.dropped(cls)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)), KA.band(PL.check_sides(~K, SK.Sketch.sides(SV.mark(SV.cat(SV.reds(cls), SV.ambers(cls)), sk)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)), KA.band(_, VD.exact(sk, cls))))))) : Bool}
  {==}

def accept_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, m: NU.PR, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>) -> {FS.accept(~K, ~W, GM.hpr(~K, ~PO.hom(K, W, R), m), sk, g0, cls, pins) == SO.accept(m, sk, g0, cls, pins) : Bool}:
  match m:
    case NU.POk{NU.NP{+plan, +gc, +gr}}:
      final_c(~K, ~W, ~R, sk, g0, True{}, cls, pins, gc, gr, plan)
    case NU.PRetry{}:
      {==}
    case NU.PStop{}:
      {==}

# The answer
# ----------

def hrun(~K: N.Num, ~H: KH.Hom<KI.dnum(), K>, r: SO.Run) -> FS.FRun<K>:
  match r:
    case SO.Run{ok, m}:
      FS.FRun{ok, GM.hpr(~K, ~H, m)}

def answer_m(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +ok: Bool, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, m: NU.PR) -> {FS.answer(~K, ~W, cls, pins, FS.FRun{ok, GM.hpr(~K, ~PO.hom(K, W, R), m)}) == SO.answer(cls, pins, SO.Run{ok, m}) : SO.Out}:
  match m:
    case NU.POk{NU.NP{+plan, +gc, +gr}}:
      %todv_t(~K, ~W, ~R, gc) : {SO.Out{ok, cls, pins, FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)), FS.todplan(~K, ~W, KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), plan))} == SO.Out{ok, cls, pins, _, gr, plan} : SO.Out}
      %todv_t(~K, ~W, ~R, gr) : {SO.Out{ok, cls, pins, FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)), FS.todplan(~K, ~W, KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), plan))} == SO.Out{ok, cls, pins, FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc)), _, plan} : SO.Out}
      %todplan_t(~K, ~W, ~R, plan) : {SO.Out{ok, cls, pins, FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)), FS.todplan(~K, ~W, KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), plan))} == SO.Out{ok, cls, pins, FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc)), FS.todv(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr)), _} : SO.Out}
      {==}
    case NU.PRetry{}:
      {==}
    case NU.PStop{}:
      {==}

def answer_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, r: SO.Run) -> {FS.answer(~K, ~W, cls, pins, hrun(~K, ~PO.hom(K, W, R), r)) == SO.answer(cls, pins, r) : SO.Out}:
  match r:
    case SO.Run{+ok, +m}:
      answer_m(~K, ~W, ~R, ok, cls, pins, m)
