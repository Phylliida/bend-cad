# bend-cad: the draft solver's structure stage never fails (PLAN-sk13b B5.4,
# solve_total over the new pass). Proofs only.
#
# The new pass ends in a state with lib/passpf.bend's invariant
# (lib/dpasspf.bend: final2_inv), so lib/perfpf.bend's reading of it
# applies: the pins are distinct variables and the system solved has a
# perfect matching onto the free variables, by dependence. perfpf's last
# part, over the new pass's end state, classes and pins (the rest of
# perfpf is reused).
#
# Generated from tools/drafts/dtotalpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/box.bend as BX
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as L
import ./struct.bend as ST
import ./dfspf.bend as D
import ./maxpf.bend as MX
import ./pass.bend as PA
import ./solvedpf.bend as SP
import ./gmpf.bend as GM
import ./passpf.bend as PP
import ./solve.bend as SO
import ./wfdec.bend as WF
import ./wfcpf.bend as WC
import ./perfpf.bend as PF
import ./dpass.bend as DPS
import ./dpasspf.bend as DPP
import ./dsolve.bend as DSO


# The system solved is matched onto the free variables
# ----------------------------------------------------

def perfect_of(+sk: SK.Sketch, +hvalid: {MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), PA.PS.vm(DPS.final2_st(sk))) == True{} : Bool}, +hdist: {SV.distinct(ST.somes(PA.PS.vm(DPS.final2_st(sk)))) == True{} : Bool}, +hml: {L.mlen(PA.PS.vm(DPS.final2_st(sk))) == PA.nvars(sk) : Nat},
  +hs1: {L.subl(ST.somes(PA.PS.vm(DPS.final2_st(sk))), PA.PS.bp(DPS.final2_st(sk))) == True{} : Bool}, +hs2: {L.subl(PA.PS.bp(DPS.final2_st(sk)), ST.somes(PA.PS.vm(DPS.final2_st(sk)))) == True{} : Bool}, +hbpd: {SV.distinct(PA.PS.bp(DPS.final2_st(sk))) == True{} : Bool}, +hbpb: {SV.below(PA.PS.bp(DPS.final2_st(sk)), SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool},
  +hB: {PP.ps.B(DPS.final2_st(sk)) == SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk)) : List<&2, E.QExpr>}, +hp: {PP.ps.B(DPS.final2_st(sk)) == SV.picked(SK.Sketch.eqs(sk), PA.PS.bp(DPS.final2_st(sk))) : List<&2, E.QExpr>})
  -> SK.Both({SV.distinct(DPS.pins2(sk)) == True{} : Bool}, {SV.below(DPS.pins2(sk), PA.nvars(sk)) == True{} : Bool}) & (&m: List<&2, Nat> -> SV.Perfect(SV.solved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk))), SV.free(PA.nvars(sk), 0n, DPS.pins2(sk)), m)):
  +vs = PF.pins_kvd(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(DPS.final2_st(sk)), DPS.solved_pos2(sk), hs1, hs2, (%Equal.sym(Nat, ST.len.q(SK.Sketch.eqs(sk)), SV.neqs(SK.Sketch.eqs(sk)), PF.lenq_neqs(SK.Sketch.eqs(sk))) : {SV.below(PA.PS.bp(DPS.final2_st(sk)), _) == True{} : Bool}
    hbpb), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), hvalid, hdist, hml, {==})
  +hcnt = L.eq_ok(Nat.add(SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), SV.len(DPS.pins2(sk))), PA.nvars(sk), PF.vsf_cnt(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(DPS.final2_st(sk)), DPS.solved_pos2(sk), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), DPS.pins2(sk), vs))
  +hfk = PF.cancel_r(SV.len(SV.free(PA.nvars(sk), 0n, DPS.pins2(sk))), SV.len(DPS.pins2(sk)), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), PA.nvars(sk), PF.free_len(PA.nvars(sk), DPS.pins2(sk), PF.vsf_fdist(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(DPS.final2_st(sk)), DPS.solved_pos2(sk), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), DPS.pins2(sk), vs), PF.vsf_fbelow(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(DPS.final2_st(sk)), DPS.solved_pos2(sk), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), DPS.pins2(sk), vs)), hcnt)
  +hbk = KA.natle_antisym(SV.len(PA.PS.bp(DPS.final2_st(sk))), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), L.pig(PA.PS.bp(DPS.final2_st(sk)), ST.somes(PA.PS.vm(DPS.final2_st(sk))), hbpd, hs2), L.pig(ST.somes(PA.PS.vm(DPS.final2_st(sk))), PA.PS.bp(DPS.final2_st(sk)), hdist, hs1))
  +nq = ST.len.q(SK.Sketch.eqs(sk))
  +hkg = MX.keys_tr(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), 0n, PA.nvars(sk), 0n, DPS.solved_pos2(sk), PA.dadjs(SK.Sketch.eqs(sk)), PF.vsf_valid(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(DPS.final2_st(sk)), DPS.solved_pos2(sk), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), DPS.pins2(sk), vs))
  +hkl = PF.keys_kn(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), PF.vsf_scnt(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(DPS.final2_st(sk)), DPS.solved_pos2(sk), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), DPS.pins2(sk), vs))
  +hgk = GM.pigc(MX.keys(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), 0n), DPS.solved_pos2(sk), MX.keys_dist(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), 0n), hkg, (%Equal.sym(Nat, SV.len(MX.keys(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), 0n)), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), hkl) : {KA.natle(SV.len(DPS.solved_pos2(sk)), _) == True{} : Bool}
    L.pig(DPS.solved_pos2(sk), ST.somes(PA.PS.vm(DPS.final2_st(sk))), hbpd, hs2)))
  +hbg = L.subl_refl(PA.PS.bp(DPS.final2_st(sk)))
  +hall = PF.keys_allm(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), PA.PS.bp(DPS.final2_st(sk)), L.subl_trans(PA.PS.bp(DPS.final2_st(sk)), DPS.solved_pos2(sk), MX.keys(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), 0n), hbg, hgk))
  +m = ST.look(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), PA.PS.bp(DPS.final2_st(sk)))
  +hmus = PF.vsf_mus(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(DPS.final2_st(sk)), DPS.solved_pos2(sk), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), DPS.pins2(sk), vs)
  ((PF.vsf_fdist(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(DPS.final2_st(sk)), DPS.solved_pos2(sk), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), DPS.pins2(sk), vs), PF.vsf_fbelow(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(DPS.final2_st(sk)), DPS.solved_pos2(sk), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), DPS.pins2(sk), vs)),
    (m, (L.band_i(SV.eq(SV.len(SV.free(PA.nvars(sk), 0n, DPS.pins2(sk))), SV.len(m)), SV.band(SV.distinct(m), SV.sub(m, SV.free(PA.nvars(sk), 0n, DPS.pins2(sk)))),
        D.eq_of(SV.len(SV.free(PA.nvars(sk), 0n, DPS.pins2(sk))), SV.len(m), Equal.trans(Nat, SV.len(SV.free(PA.nvars(sk), 0n, DPS.pins2(sk))), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), SV.len(m), hfk, Equal.sym(Nat, SV.len(m), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), Equal.trans(Nat, SV.len(m), SV.len(PA.PS.bp(DPS.final2_st(sk))), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), L.look_len(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), PA.PS.bp(DPS.final2_st(sk))), hbk)))),
        L.band_i(SV.distinct(m), SV.sub(m, SV.free(PA.nvars(sk), 0n, DPS.pins2(sk))), L.look_dist(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), PA.PS.bp(DPS.final2_st(sk)), hbpd, hall, PF.vsf_vdist(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(DPS.final2_st(sk)), DPS.solved_pos2(sk), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), DPS.pins2(sk), vs)),
          PF.sub_free(m, ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), PA.nvars(sk), DPS.pins2(sk), L.look_subl(ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), PA.PS.bp(DPS.final2_st(sk)), hall), hmus, PF.vsf_ffree(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(DPS.final2_st(sk)), DPS.solved_pos2(sk), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), DPS.pins2(sk), vs)))),
      (%Equal.trans(List<&2, E.QExpr>, SV.picked(SK.Sketch.eqs(sk), PA.PS.bp(DPS.final2_st(sk))), PP.ps.B(DPS.final2_st(sk)), SV.solved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk))), Equal.sym(List<&2, E.QExpr>, PP.ps.B(DPS.final2_st(sk)), SV.picked(SK.Sketch.eqs(sk), PA.PS.bp(DPS.final2_st(sk))), hp),
          Equal.trans(List<&2, E.QExpr>, PP.ps.B(DPS.final2_st(sk)), SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk)), SV.solved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk))), hB, Equal.sym(List<&2, E.QExpr>, SV.solved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk))), SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk)), SP.solved_end(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)))))) : SV.DepAll(_, m)
        PF.depall_v(SK.Sketch.eqs(sk), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), PA.PS.bp(DPS.final2_st(sk)), PA.nvars(sk), DPS.solved_pos2(sk), PF.vsf_valid(SK.Sketch.eqs(sk), PA.nvars(sk), PA.PS.vm(DPS.final2_st(sk)), DPS.solved_pos2(sk), SV.len(ST.somes(PA.PS.vm(DPS.final2_st(sk)))), ST.KD.vm(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), DPS.solved_pos2(sk))), DPS.pins2(sk), vs), hall, hmus)))))


def f_valid(+sk: SK.Sketch, +hb: {PP.pib(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), PP.ps.rows(DPS.final2_st(sk)), PP.ps.B(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk))) == True{} : Bool}) -> {MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), PA.PS.vm(DPS.final2_st(sk))) == True{} : Bool}:
  (%Equal.sym(List<&2, Maybe<&2, Nat>>, PA.PS.vm(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk)), PF.vm_eq(DPS.final2_st(sk))) : {MX.valid(PA.dadjs(SK.Sketch.eqs(sk)), _) == True{} : Bool}
    PP.pib_valid(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), PP.ps.rows(DPS.final2_st(sk)), PP.ps.B(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk)), hb))

def f_dist(+sk: SK.Sketch, +hb: {PP.pib(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), PP.ps.rows(DPS.final2_st(sk)), PP.ps.B(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk))) == True{} : Bool}) -> {SV.distinct(ST.somes(PA.PS.vm(DPS.final2_st(sk)))) == True{} : Bool}:
  (%Equal.sym(List<&2, Maybe<&2, Nat>>, PA.PS.vm(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk)), PF.vm_eq(DPS.final2_st(sk))) : {SV.distinct(ST.somes(_)) == True{} : Bool}
    PP.pib_dist(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), PP.ps.rows(DPS.final2_st(sk)), PP.ps.B(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk)), hb))

def f_mlen(+sk: SK.Sketch, +hb: {PP.pib(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), PP.ps.rows(DPS.final2_st(sk)), PP.ps.B(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk))) == True{} : Bool}) -> {L.mlen(PA.PS.vm(DPS.final2_st(sk))) == PA.nvars(sk) : Nat}:
  L.eq_ok(L.mlen(PA.PS.vm(DPS.final2_st(sk))), PA.nvars(sk), (%Equal.sym(List<&2, Maybe<&2, Nat>>, PA.PS.vm(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk)), PF.vm_eq(DPS.final2_st(sk))) : {SV.eq(L.mlen(_), PA.nvars(sk)) == True{} : Bool}
    PP.pib_mlen(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), PP.ps.rows(DPS.final2_st(sk)), PP.ps.B(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk)), hb)))

def f_s1(+sk: SK.Sketch, +hb: {PP.pib(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), PP.ps.rows(DPS.final2_st(sk)), PP.ps.B(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk))) == True{} : Bool}) -> {L.subl(ST.somes(PA.PS.vm(DPS.final2_st(sk))), PA.PS.bp(DPS.final2_st(sk))) == True{} : Bool}:
  (%Equal.sym(List<&2, Maybe<&2, Nat>>, PA.PS.vm(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk)), PF.vm_eq(DPS.final2_st(sk))) : {L.subl(ST.somes(_), PA.PS.bp(DPS.final2_st(sk))) == True{} : Bool}
    (%Equal.sym(List<&2, Nat>, PA.PS.bp(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PF.bp_eq(DPS.final2_st(sk))) : {L.subl(ST.somes(PP.ps.vm(DPS.final2_st(sk))), _) == True{} : Bool}
      PP.pib_s1(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), PP.ps.rows(DPS.final2_st(sk)), PP.ps.B(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk)), hb)))

def f_s2(+sk: SK.Sketch, +hb: {PP.pib(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), PP.ps.rows(DPS.final2_st(sk)), PP.ps.B(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk))) == True{} : Bool}) -> {L.subl(PA.PS.bp(DPS.final2_st(sk)), ST.somes(PA.PS.vm(DPS.final2_st(sk)))) == True{} : Bool}:
  (%Equal.sym(List<&2, Maybe<&2, Nat>>, PA.PS.vm(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk)), PF.vm_eq(DPS.final2_st(sk))) : {L.subl(PA.PS.bp(DPS.final2_st(sk)), ST.somes(_)) == True{} : Bool}
    (%Equal.sym(List<&2, Nat>, PA.PS.bp(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PF.bp_eq(DPS.final2_st(sk))) : {L.subl(_, ST.somes(PP.ps.vm(DPS.final2_st(sk)))) == True{} : Bool}
      PP.pib_s2(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), PP.ps.rows(DPS.final2_st(sk)), PP.ps.B(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk)), hb)))

def f_bpd(+sk: SK.Sketch, +hb: {PP.pib(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), PP.ps.rows(DPS.final2_st(sk)), PP.ps.B(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk))) == True{} : Bool}) -> {SV.distinct(PA.PS.bp(DPS.final2_st(sk))) == True{} : Bool}:
  (%Equal.sym(List<&2, Nat>, PA.PS.bp(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PF.bp_eq(DPS.final2_st(sk))) : {SV.distinct(_) == True{} : Bool}
    PP.pib_bpd(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), PP.ps.rows(DPS.final2_st(sk)), PP.ps.B(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk)), hb))

def f_bpb(+sk: SK.Sketch, +hb: {PP.pib(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), PP.ps.rows(DPS.final2_st(sk)), PP.ps.B(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk))) == True{} : Bool}) -> {SV.below(PA.PS.bp(DPS.final2_st(sk)), SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}:
  (%Equal.sym(List<&2, Nat>, PA.PS.bp(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PF.bp_eq(DPS.final2_st(sk))) : {SV.below(_, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}
    PP.pib_bpb(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), PP.ps.rows(DPS.final2_st(sk)), PP.ps.B(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PP.ps.vm(DPS.final2_st(sk)), hb))



def total_pass2(+sk: SK.Sketch, +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool})
  -> SK.Both({SV.distinct(DPS.pins2(sk)) == True{} : Bool}, {SV.below(DPS.pins2(sk), PA.nvars(sk)) == True{} : Bool}) & (&m: List<&2, Nat> -> SV.Perfect(SV.solved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk))), SV.free(PA.nvars(sk), 0n, DPS.pins2(sk)), m)):
  +hi = DPP.final2_inv(sk, hA, hcov, hwf)
  +hb = PP.pinv_b(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), DPS.final2_st(sk), hi)
  perfect_of(sk, f_valid(sk, hb), f_dist(sk, hb), f_mlen(sk, hb), f_s1(sk, hb), f_s2(sk, hb), f_bpd(sk, hb), f_bpb(sk, hb),
    PP.pinv_B(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), DPS.final2_st(sk), hi),
    (%Equal.sym(List<&2, Nat>, PA.PS.bp(DPS.final2_st(sk)), PP.ps.bp(DPS.final2_st(sk)), PF.bp_eq(DPS.final2_st(sk))) : {PP.ps.B(DPS.final2_st(sk)) == SV.picked(SK.Sketch.eqs(sk), _) : List<&2, E.QExpr>}
      PP.pinv_p(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.ncons(sk), DPS.final2_st(sk), hi)))


# The law, for the draft solver
# -----------------------------


def tp2.go(+sk: SK.Sketch, +hwf: {WF.wf_dec(sk) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat,
  t: SK.Both({SV.distinct(DSO.pins_of2(sk)) == True{} : Bool}, {SV.below(DSO.pins_of2(sk), SO.nvars(sk)) == True{} : Bool}) & (&m: List<&2, Nat> -> SV.Perfect(SV.solved(sk, SV.reds(DSO.cls_of2(sk)), SV.dropped(DSO.cls_of2(sk))), SV.free(SO.nvars(sk), 0n, DSO.pins_of2(sk)), m))) -> ({SO.Out.cls(DSO.solve_l2(sk, g0, l)) == DSO.cls_of2(sk) : List<&2, SV.Class>} & ({SO.Out.pins(DSO.solve_l2(sk, g0, l)) == DSO.pins_of2(sk) : List<&2, Nat>} & ({WF.wf_dec(SV.mark(SV.reds(DSO.cls_of2(sk)), sk)) == True{} : Bool} & ({SV.distinct(DSO.pins_of2(sk)) == True{} : Bool} & ({SV.below(DSO.pins_of2(sk), SO.nvars(sk)) == True{} : Bool} & (&m: List<&2, Nat> -> SV.Perfect(SV.solved(sk, SV.reds(DSO.cls_of2(sk)), SV.dropped(DSO.cls_of2(sk))), SV.free(SO.nvars(sk), 0n, DSO.pins_of2(sk)), m))))))):
  (hdb, pm) = t
  (hd, hb) = hdb
  ({==}, ({==}, (WC.wf_mark(SV.reds(DSO.cls_of2(sk)), sk, hwf), (hd, (hb, pm)))))

# the structure stage never fails: the classes and pins are the sketch's
# alone, the sketch less its reds well formed, the pins distinct
# variables, the system solved perfectly matched onto the free variables
def solve_total2(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +g0: List<&2, S.D>, +l: Nat) -> ({SO.Out.cls(DSO.solve_l2(sk, g0, l)) == DSO.cls_of2(sk) : List<&2, SV.Class>} & ({SO.Out.pins(DSO.solve_l2(sk, g0, l)) == DSO.pins_of2(sk) : List<&2, Nat>} & ({WF.wf_dec(SV.mark(SV.reds(DSO.cls_of2(sk)), sk)) == True{} : Bool} & ({SV.distinct(DSO.pins_of2(sk)) == True{} : Bool} & ({SV.below(DSO.pins_of2(sk), SO.nvars(sk)) == True{} : Bool} & (&m: List<&2, Nat> -> SV.Perfect(SV.solved(sk, SV.reds(DSO.cls_of2(sk)), SV.dropped(DSO.cls_of2(sk))), SV.free(SO.nvars(sk), 0n, DSO.pins_of2(sk)), m))))))):
  +hwf = WC.wf_dec_ok(sk, w)
  tp2.go(sk, hwf, g0, l, total_pass2(sk, DPP.adjb2_of(sk, cov, hwf), DPP.hcov_of(sk, cov), hwf))
