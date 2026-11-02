# bend-cad: the fast solver (lib/fast.bend) returns exactly what the solver
# (lib/solve.bend) returns, for any computing numbers K with the proposer's
# operations W and laws R relating them to KI.dnum() (lib/pops.bend): its
# proposer gives numer's plan through the map (lib/gplanpf.bend: plan_t),
# its verdict on the mapped answer is SO.checks's (the checker through the
# map: lib/planhpf.bend), and the answer sent back through tod is the
# solver's (solve_l_eq). At the CLI's word dyadics in base 2^12 (FS.wk,
# FS.wo), with the word laws at that base, this is ROADMAP's fast_solve,
# restated in tests/fast_laws.bend, so every law about the solver holds
# for what runs (PLAN-sk13w W6).

# Generated from tools/drafts/fastpf.draft by tools/expand.py; edit the
# draft.


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
import ./gplanpf.bend as GQ
import ./wnumpf.bend as WP
import ./pass.bend as PA

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


# SO.checks's verdict on an answer is FS.checks's on its image
def final_c(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +sk: SK.Sketch, +g0: List<&2, S.D>, +ok: Bool, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +gc: List<&2, S.D>, +gr: List<&2, S.D>, +p: PL.Plan<KI.dnum()>) -> {FS.checks(~K, ~W, sk, g0, FS.FOut{ok, cls, pins, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gc), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), gr), KH.hplan(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)}) == SO.checks(sk, g0, SO.Out{ok, cls, pins, gc, gr, p}) : Bool}:
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

# The precision loop
# ------------------


# the loop on mapped plans is SO.ploop's, mapped
def ploop_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, ps: List<&2, Nat>, ok: Bool, cur: NU.PR, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel) -> {FS.ploop(~K, ~W, ps, ok, GM.hpr(~K, ~PO.hom(K, W, R), cur), sk, g0, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), cls, pins, es, nv, skel) == hrun(~K, ~PO.hom(K, W, R), SO.ploop(ps, ok, cur, sk, g0, cls, pins, es, nv, skel)) : FS.FRun<K>}:
  match ps ok:
    case Nil{} ok:
      {==}
    case Con{p, t} True{}:
      {==}
    case Con{+p, +t} False{}:
      %ploop_t(~K, ~W, ~R, t, SO.accept(NU.plan(es, nv, skel, g0, p), sk, g0, cls, pins), NU.plan(es, nv, skel, g0, p), sk, g0, cls, pins, es, nv, skel) : {FS.ploop(~K, ~W, t, FS.accept(~K, ~W, GN.plan(~K, ~W, es, nv, skel, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p), sk, g0, cls, pins), GN.plan(~K, ~W, es, nv, skel, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p), sk, g0, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), cls, pins, es, nv, skel) == _ : FS.FRun<K>}
      %accept_t(~K, ~W, ~R, NU.plan(es, nv, skel, g0, p), sk, g0, cls, pins) : {FS.ploop(~K, ~W, t, FS.accept(~K, ~W, GN.plan(~K, ~W, es, nv, skel, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p), sk, g0, cls, pins), GN.plan(~K, ~W, es, nv, skel, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p), sk, g0, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), cls, pins, es, nv, skel) == FS.ploop(~K, ~W, t, _, GM.hpr(~K, ~PO.hom(K, W, R), NU.plan(es, nv, skel, g0, p)), sk, g0, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), cls, pins, es, nv, skel) : FS.FRun<K>}
      %GQ.plan_t(~K, ~W, ~R, es, nv, skel, g0, p) : {FS.ploop(~K, ~W, t, FS.accept(~K, ~W, GN.plan(~K, ~W, es, nv, skel, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p), sk, g0, cls, pins), GN.plan(~K, ~W, es, nv, skel, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p), sk, g0, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), cls, pins, es, nv, skel) == FS.ploop(~K, ~W, t, FS.accept(~K, ~W, _, sk, g0, cls, pins), GM.hpr(~K, ~PO.hom(K, W, R), NU.plan(es, nv, skel, g0, p)), sk, g0, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), cls, pins, es, nv, skel) : FS.FRun<K>}
      %GQ.plan_t(~K, ~W, ~R, es, nv, skel, g0, p) : {FS.ploop(~K, ~W, t, FS.accept(~K, ~W, GN.plan(~K, ~W, es, nv, skel, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p), sk, g0, cls, pins), GN.plan(~K, ~W, es, nv, skel, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p), sk, g0, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), cls, pins, es, nv, skel) == FS.ploop(~K, ~W, t, FS.accept(~K, ~W, GN.plan(~K, ~W, es, nv, skel, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p), sk, g0, cls, pins), _, sk, g0, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), cls, pins, es, nv, skel) : FS.FRun<K>}
      {==}

def start_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, ps: List<&2, Nat>, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel) -> {FS.ploop.start(~K, ~W, ps, sk, g0, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), cls, pins, es, nv, skel) == hrun(~K, ~PO.hom(K, W, R), SO.ploop.start(ps, sk, g0, cls, pins, es, nv, skel)) : FS.FRun<K>}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      %ploop_t(~K, ~W, ~R, t, SO.accept(NU.plan(es, nv, skel, g0, p), sk, g0, cls, pins), NU.plan(es, nv, skel, g0, p), sk, g0, cls, pins, es, nv, skel) : {FS.ploop(~K, ~W, t, FS.accept(~K, ~W, GN.plan(~K, ~W, es, nv, skel, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p), sk, g0, cls, pins), GN.plan(~K, ~W, es, nv, skel, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p), sk, g0, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), cls, pins, es, nv, skel) == _ : FS.FRun<K>}
      %accept_t(~K, ~W, ~R, NU.plan(es, nv, skel, g0, p), sk, g0, cls, pins) : {FS.ploop(~K, ~W, t, FS.accept(~K, ~W, GN.plan(~K, ~W, es, nv, skel, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p), sk, g0, cls, pins), GN.plan(~K, ~W, es, nv, skel, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p), sk, g0, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), cls, pins, es, nv, skel) == FS.ploop(~K, ~W, t, _, GM.hpr(~K, ~PO.hom(K, W, R), NU.plan(es, nv, skel, g0, p)), sk, g0, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), cls, pins, es, nv, skel) : FS.FRun<K>}
      %GQ.plan_t(~K, ~W, ~R, es, nv, skel, g0, p) : {FS.ploop(~K, ~W, t, FS.accept(~K, ~W, GN.plan(~K, ~W, es, nv, skel, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p), sk, g0, cls, pins), GN.plan(~K, ~W, es, nv, skel, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p), sk, g0, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), cls, pins, es, nv, skel) == FS.ploop(~K, ~W, t, FS.accept(~K, ~W, _, sk, g0, cls, pins), GM.hpr(~K, ~PO.hom(K, W, R), NU.plan(es, nv, skel, g0, p)), sk, g0, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), cls, pins, es, nv, skel) : FS.FRun<K>}
      %GQ.plan_t(~K, ~W, ~R, es, nv, skel, g0, p) : {FS.ploop(~K, ~W, t, FS.accept(~K, ~W, GN.plan(~K, ~W, es, nv, skel, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p), sk, g0, cls, pins), GN.plan(~K, ~W, es, nv, skel, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p), sk, g0, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), cls, pins, es, nv, skel) == FS.ploop(~K, ~W, t, FS.accept(~K, ~W, GN.plan(~K, ~W, es, nv, skel, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), p), sk, g0, cls, pins), _, sk, g0, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), g0), cls, pins, es, nv, skel) : FS.FRun<K>}
      {==}

# The solver
# ----------

# FS.solve_lw shares the pass's results; unshared, it is this
# walk2 is PA.pass and PA.pass_st at once
def cons_cls(+c: SV.Class, w: FS.PW) -> {Con{c, FS.PW.cls(w)} == FS.PW.cls(FS.pw.cons(c, w)) : List<&2, SV.Class>}:
  match w:
    case FS.PW{cls, st}:
      {==}

def cons_st(+c: SV.Class, w: FS.PW) -> {FS.PW.st(w) == FS.PW.st(FS.pw.cons(c, w)) : PA.PS}:
  match w:
    case FS.PW{cls, st}:
      {==}


def walk2_cls(rs: List<&2, SK.Rec>, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +i: Nat, +st: PA.PS) -> {FS.PW.cls(FS.walk2(rs, es, own, sk, adj, f, i, st)) == PA.pass(rs, es, own, sk, adj, f, i, st) : List<&2, SV.Class>}:
  match rs:
    case Nil{}:
      {==}
    case Con{SK.Rec{id, True{}, k}, +t}:
      %cons_cls(SV.Kept{Nil{}}, FS.walk2(t, es, own, sk, adj, f, 1n+i, st)) : {_ == Con{SV.Kept{Nil{}}, PA.pass(t, es, own, sk, adj, f, 1n+i, st)} : List<&2, SV.Class>}
      %walk2_cls(t, es, own, sk, adj, f, 1n+i, st) : {Con{SV.Kept{Nil{}}, FS.PW.cls(FS.walk2(t, es, own, sk, adj, f, 1n+i, st))} == Con{SV.Kept{Nil{}}, _} : List<&2, SV.Class>}
      {==}
    case Con{SK.Rec{id, False{}, k}, +t}:
      %cons_cls(PA.PO.k(PA.one(es, own, sk, adj, f, i, st)), FS.walk2(t, es, own, sk, adj, f, 1n+i, PA.PO.st(PA.one(es, own, sk, adj, f, i, st)))) : {_ == Con{PA.PO.k(PA.one(es, own, sk, adj, f, i, st)), PA.pass(t, es, own, sk, adj, f, 1n+i, PA.PO.st(PA.one(es, own, sk, adj, f, i, st)))} : List<&2, SV.Class>}
      %walk2_cls(t, es, own, sk, adj, f, 1n+i, PA.PO.st(PA.one(es, own, sk, adj, f, i, st))) : {Con{PA.PO.k(PA.one(es, own, sk, adj, f, i, st)), FS.PW.cls(FS.walk2(t, es, own, sk, adj, f, 1n+i, PA.PO.st(PA.one(es, own, sk, adj, f, i, st))))} == Con{PA.PO.k(PA.one(es, own, sk, adj, f, i, st)), _} : List<&2, SV.Class>}
      {==}

def walk2_st(rs: List<&2, SK.Rec>, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +i: Nat, +st: PA.PS) -> {FS.PW.st(FS.walk2(rs, es, own, sk, adj, f, i, st)) == PA.pass_st(rs, es, own, sk, adj, f, i, st) : PA.PS}:
  match rs:
    case Nil{}:
      {==}
    case Con{SK.Rec{id, True{}, k}, +t}:
      %cons_st(SV.Kept{Nil{}}, FS.walk2(t, es, own, sk, adj, f, 1n+i, st)) : {_ == PA.pass_st(t, es, own, sk, adj, f, 1n+i, st) : PA.PS}
      walk2_st(t, es, own, sk, adj, f, 1n+i, st)
    case Con{SK.Rec{id, False{}, k}, +t}:
      %cons_st(PA.PO.k(PA.one(es, own, sk, adj, f, i, st)), FS.walk2(t, es, own, sk, adj, f, 1n+i, PA.PO.st(PA.one(es, own, sk, adj, f, i, st)))) : {_ == PA.pass_st(t, es, own, sk, adj, f, 1n+i, PA.PO.st(PA.one(es, own, sk, adj, f, i, st))) : PA.PS}
      walk2_st(t, es, own, sk, adj, f, 1n+i, PA.PO.st(PA.one(es, own, sk, adj, f, i, st)))


# FS.solve_lw is SO.solve_lw's form: the pass's results once (walk2), each
# named once
def solve_lw_unf(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +w: Nat) -> {FS.solve_lw(~K, ~W, sk, g0, l, w) == FS.answer(~K, ~W, SO.cls_of(sk), SO.pins_of(sk), FS.ploop.start(~K, ~W, SO.precisions(l, w), sk, g0, FS.ofdv(~K, ~W, g0), SO.cls_of(sk), SO.pins_of(sk), SO.kept(sk), SO.nvars(sk), SO.skel_of(sk))) : SO.Out}:
  %walk2_cls(PA.recs(sk), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 0n, PA.start(PA.nvars(sk))) : {FS.solve_lw(~K, ~W, sk, g0, l, w) == FS.answer(~K, ~W, _, PA.pins(sk), FS.ploop.start(~K, ~W, SO.precisions(l, w), sk, g0, FS.ofdv(~K, ~W, g0), _, PA.pins(sk), SV.solved(sk, SV.reds(_), SV.dropped(_)), PA.nvars(sk), PA.skel(sk))) : SO.Out}
  %walk2_st(PA.recs(sk), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 0n, PA.start(PA.nvars(sk))) : {FS.solve_lw(~K, ~W, sk, g0, l, w) == FS.answer(~K, ~W, FS.PW.cls(FS.walk2(PA.recs(sk), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 0n, PA.start(PA.nvars(sk)))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.PS.bp(_))), FS.ploop.start(~K, ~W, SO.precisions(l, w), sk, g0, FS.ofdv(~K, ~W, g0), FS.PW.cls(FS.walk2(PA.recs(sk), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 0n, PA.start(PA.nvars(sk)))), ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.PS.bp(_))), SV.solved(sk, SV.reds(FS.PW.cls(FS.walk2(PA.recs(sk), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 0n, PA.start(PA.nvars(sk))))), SV.dropped(FS.PW.cls(FS.walk2(PA.recs(sk), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 0n, PA.start(PA.nvars(sk)))))), PA.nvars(sk), ST.renum(ST.skel.kd(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.PS.bp(_), PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), PA.PS.bp(_))), PA.PS.bp(_)))) : SO.Out}
  {==}


def solve_core(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +sk: SK.Sketch, +g0: List<&2, S.D>, +ps: List<&2, Nat>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel) -> {FS.answer(~K, ~W, cls, pins, FS.ploop.start(~K, ~W, ps, sk, g0, FS.ofdv(~K, ~W, g0), cls, pins, es, nv, skel)) == SO.answer(cls, pins, SO.ploop.start(ps, sk, g0, cls, pins, es, nv, skel)) : SO.Out}:
  %answer_t(~K, ~W, ~R, cls, pins, SO.ploop.start(ps, sk, g0, cls, pins, es, nv, skel)) : {FS.answer(~K, ~W, cls, pins, FS.ploop.start(~K, ~W, ps, sk, g0, FS.ofdv(~K, ~W, g0), cls, pins, es, nv, skel)) == _ : SO.Out}
  %start_t(~K, ~W, ~R, ps, sk, g0, cls, pins, es, nv, skel) : {FS.answer(~K, ~W, cls, pins, FS.ploop.start(~K, ~W, ps, sk, g0, FS.ofdv(~K, ~W, g0), cls, pins, es, nv, skel)) == FS.answer(~K, ~W, cls, pins, _) : SO.Out}
  %ofdv_t(~K, ~W, ~R, g0) : {FS.answer(~K, ~W, cls, pins, FS.ploop.start(~K, ~W, ps, sk, g0, FS.ofdv(~K, ~W, g0), cls, pins, es, nv, skel)) == FS.answer(~K, ~W, cls, pins, FS.ploop.start(~K, ~W, ps, sk, g0, _, cls, pins, es, nv, skel)) : SO.Out}
  {==}

def solve_lw_eq(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +w: Nat) -> {FS.solve_lw(~K, ~W, sk, g0, l, w) == SO.solve_lw(sk, g0, l, w) : SO.Out}:
  Equal.trans(SO.Out, FS.solve_lw(~K, ~W, sk, g0, l, w), FS.answer(~K, ~W, SO.cls_of(sk), SO.pins_of(sk), FS.ploop.start(~K, ~W, SO.precisions(l, w), sk, g0, FS.ofdv(~K, ~W, g0), SO.cls_of(sk), SO.pins_of(sk), SO.kept(sk), SO.nvars(sk), SO.skel_of(sk))), SO.solve_lw(sk, g0, l, w), solve_lw_unf(~K, ~W, ~R, sk, g0, l, w), solve_core(~K, ~W, ~R, sk, g0, SO.precisions(l, w), SO.cls_of(sk), SO.pins_of(sk), SO.kept(sk), SO.nvars(sk), SO.skel_of(sk)))

def solve_l_eq(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat) -> {FS.solve_l(~K, ~W, sk, g0, l) == SO.solve_l(sk, g0, l) : SO.Out}:
  solve_lw_eq(~K, ~W, ~R, sk, g0, l, 7n)
