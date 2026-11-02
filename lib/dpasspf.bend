# bend-cad: the pass with the direction layer is honest (PLAN-sk13b
# B4.5): DH.Honest(sk, DPS.classes2(sk)), the extended Honest of
# spec/_draft13b.bend. Proofs only.
#
# The proof follows lib/passpf.bend (sk-13a's pass), whose generic lemmas
# it imports (PInv, pib, the list lemmas, the matching and side tests):
# - every class drops only its own equations (downs), now with the walk's
#   direction drops too;
# - the classes so far, which the pass reads for the facts' nd, agree
#   with the final classes on every equation of a constraint before c
#   (pcf: a later class drops only its own equations);
# - each driving constraint's class follows from its decisions: Conflict
#   by the generalized filter (lib/dconflictpf.bend), Kept or Amber or
#   Over with no refutation of either kind (NoRefute2), DropsOk and
#   DropsNd from the walk (lib/dcwpf.bend), the unit's matching and the
#   side tests as before;
# - the closure calls start from the state kept across calls (PLAN-sk13b
#   B4.8): it is valid for facts that the kept constraints' facts extend
#   (DW.WInv), at the context it was built in, and stays so after each
#   constraint (wn_ok), so each call gives Ex and decides as the closure
#   from the start does (ro_eq, the walk's dd_ok).
#
# Generated from tools/drafts/dpasspf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ../spec/solve.bend as SV
import ../spec/_draft13b.bend as DH
import ../spec/dir.bend as DR
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as LI
import ./listpf.bend as L
import ./struct.bend as ST
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./refute.bend as RF
import ./conflict.bend as CO
import ./pass.bend as PA
import ./kbpf.bend as KB
import ./ownpf.bend as OW
import ./solvedpf.bend as SP
import ./clslpf.bend as CL
import ./prepf.bend as PR
import ./cwpf.bend as CW
import ./gmpf.bend as GM
import ./dfspf.bend as D
import ./maxpf.bend as MX
import ./solve.bend as SO
import ./redpf.bend as RP
import ./wfcpf.bend as WC
import ./covpf.bend as CV
import ./wfdec.bend as WF
import ./passpf.bend as PP
import ./dconflict.bend as DCF
import ./dconflictpf.bend as DCP
import ./dcwpf.bend as DCW
import ./dpass.bend as DPS
import ./dpassmpf.bend as DPM
import ./dclose.bend as DC
import ./dmemopf.bend as MP
import ./dbridgepf.bend as BRG
import ./dwarmpf.bend as DW

def absurd(-A: Type, x: Empty) -> A:
  match x:


# Every class drops only its own equations
# ----------------------------------------

def cwo2.dir(m: Maybe<&2, DR.Der>, +own: List<&2, Nat>, +c: Nat, +k: Nat, +e: E.QExpr, +r: EL.Res, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>,
  +ho: {SV.eq(SV.nth(own, k), c) == True{} : Bool}, +h: {KB.allo(own, SV.drops(ds), c) == True{} : Bool}) -> {KB.allo(own, SV.drops(CW.cw.ds(DPS.cw2.dir(m, k, e, r, rows, B, bp, ds, us, es, fs))), c) == True{} : Bool}:
  match m:
    case Some{+der}:
      LI.band_i(SV.eq(SV.nth(own, k), c), KB.allo(own, SV.drops(ds), c), ho, h)
    case None{}:
      h

def cwo2.pick(b: Bool, +own: List<&2, Nat>, +c: Nat, +k: Nat, +e: E.QExpr, +r: EL.Res, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>, +sk: SK.Sketch, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +W: DC.WK,
  +ho: {SV.eq(SV.nth(own, k), c) == True{} : Bool}, +h: {KB.allo(own, SV.drops(ds), c) == True{} : Bool}) -> {KB.allo(own, SV.drops(CW.cw.ds(DPS.cw2.pick(b, k, e, r, rows, B, bp, ds, us, sk, c, F0, cx, W))), c) == True{} : Bool}:
  match b:
    case True{}:
      LI.band_i(SV.eq(SV.nth(own, k), c), KB.allo(own, SV.drops(ds), c), ho, h)
    case False{}:
      cwo2.dir(DPS.ddec(sk, DPS.fk(sk, c, F0, ds, k), cx, e, DPS.cstat(sk, c), W), own, c, k, e, r, rows, B, bp, ds, us, SV.ents(sk), DPS.fk(sk, c, F0, ds, k), ho, h)

def cwo2.at(b: Bool, +own: List<&2, Nat>, +c: Nat, +k: Nat, +e: E.QExpr, st: PA.CW, +sk: SK.Sketch, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +W: DC.WK, +eb: {SV.eq(SV.nth(own, k), c) == b : Bool}, +h: {KB.allo(own, SV.drops(CW.cw.ds(st)), c) == True{} : Bool})
  -> {KB.allo(own, SV.drops(CW.cw.ds(DPS.cw2.at(b, k, e, st, sk, c, F0, cx, W))), c) == True{} : Bool}:
  match b:
    case True{}:
      match st:
        case PA.CW{+rows, +B, +bp, +ds, +us}:
          cwo2.pick(EP.isnil(EP.resp(EL.resid(rows, e))), own, c, k, e, EL.resid(rows, e), rows, B, bp, ds, us, sk, F0, cx, W, eb, h)
    case False{}:
      h

# the walk drops only c's equations
def cw2_own(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +c: Nat, +k: Nat, +st: PA.CW, +sk: SK.Sketch, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +W: DC.WK, +h: {KB.allo(own, SV.drops(CW.cw.ds(st)), c) == True{} : Bool})
  -> {KB.allo(own, SV.drops(CW.cw.ds(DPS.cwalk2(es, own, c, k, st, sk, F0, cx, W))), c) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case Con{+e, +t}:
      cw2_own(t, own, c, 1n+k, DPS.cw2.at(SV.eq(SV.nth(own, k), c), k, e, st, sk, c, F0, cx, W), sk, F0, cx, W, cwo2.at(SV.eq(SV.nth(own, k), c), own, c, k, e, st, sk, F0, cx, W, {==}, h))

def one2_down.c(b: Bool, +sk: SK.Sketch, +c: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +cls: List<&2, SV.Class>, +cx: List<&2, E.QExpr>, +W: DC.WK)
  -> {KB.allo(SV.owners(sk), SV.kdrops(PA.PO.k(DPS.one2.c(b, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), c, kb, rows, B, bp, vm, cls, cx, W))), c) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      PP.one_down.w(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), kb, sk, cls, True{}, 0n), cx, W), sk, c, kb, rows, B, bp, vm,
        cw2_own(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), kb, sk, cls, True{}, 0n), cx, W, {==}))

def one2_down(st: PA.PS, +sk: SK.Sketch, +c: Nat, +cls: List<&2, SV.Class>, +W: DC.WK, +foA: DC.FO) -> {KB.allo(SV.owners(sk), SV.kdrops(PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), c, st, cls, W, foA))), c) == True{} : Bool}:
  match st:
    case PA.PS{+kb, +rows, +B, +bp, +vm}:
      one2_down.c(DCF.refutable2.o(sk, c, kb, DC.FO.o(foA)), sk, c, kb, rows, B, bp, vm, cls, SV.eqs_of(sk, Con{c, kb}), W)


def pass2_down(rs: List<&2, SK.Rec>, +sk: SK.Sketch, +i: Nat, +st: PA.PS, +cls: List<&2, SV.Class>, +W: DC.WK) -> {CL.downs(SV.owners(sk), DPS.pass2(rs, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, cls, W), i) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{SK.Rec{id, True{}, k}, +t}:
      L.band_i(True{}, CL.downs(SV.owners(sk), DPS.pass2(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, st, DPS.csnoc(cls, SV.Kept{Nil{}}), W), 1n+i), {==}, pass2_down(t, sk, 1n+i, st, DPS.csnoc(cls, SV.Kept{Nil{}}), W))
    case Con{SK.Rec{id, False{}, k}, +t}:
      L.band_i(KB.allo(SV.owners(sk), SV.kdrops(PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, cls, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), i), CL.downs(SV.owners(sk), DPS.pass2(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, PA.PO.st(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, cls, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))), DPS.csnoc(cls, PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, cls, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DPS.wnext(SV.is_red(PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, cls, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wk.next(DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))), 1n+i),
        one2_down(st, sk, i, cls, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))), pass2_down(t, sk, 1n+i, PA.PO.st(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, cls, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))), DPS.csnoc(cls, PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, cls, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DPS.wnext(SV.is_red(PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, cls, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wk.next(DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))))

# the final classes drop only their own equations
def classes2_down(+sk: SK.Sketch) -> {CL.downs(SV.owners(sk), DPS.classes2(sk), 0n) == True{} : Bool}:
  pass2_down(PA.recs(sk), sk, 0n, PA.start(PA.nvars(sk)), Nil{}, DC.wk0(SV.ents(sk), DCF.tv(sk), DC.SP{Nil{}, Nil{}}))

def clsn_pass2(rs: List<&2, SK.Rec>, +sk: SK.Sketch, +i: Nat, +st: PA.PS, +cls: List<&2, SV.Class>, +W: DC.WK) -> {SV.clsn(DPS.pass2(rs, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, cls, W)) == SV.clen(rs) : Nat}:
  match rs:
    case Nil{}:
      {==}
    case Con{SK.Rec{id, True{}, k}, +t}:
      %clsn_pass2(t, sk, 1n+i, st, DPS.csnoc(cls, SV.Kept{Nil{}}), W) : {1n+SV.clsn(DPS.pass2(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, st, DPS.csnoc(cls, SV.Kept{Nil{}}), W)) == 1n+_ : Nat}
      {==}
    case Con{SK.Rec{id, False{}, k}, +t}:
      %clsn_pass2(t, sk, 1n+i, PA.PO.st(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, cls, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))), DPS.csnoc(cls, PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, cls, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DPS.wnext(SV.is_red(PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, cls, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wk.next(DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))) : {1n+SV.clsn(DPS.pass2(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, PA.PO.st(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, cls, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))), DPS.csnoc(cls, PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, cls, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DPS.wnext(SV.is_red(PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, cls, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wk.next(DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))) == 1n+_ : Nat}
      {==}

# The classes so far
# ------------------
# The pass reads the facts' nd from the classes before c (pc); the spec
# reads them from the final classes. These agree on every equation whose
# constraint is before c: the final classes are pc followed by classes at
# c or later, which drop only their own equations.

def ccat(xs: List<&2, SV.Class>, ys: List<&2, SV.Class>) -> List<&2, SV.Class>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, ccat(t, ys)}

def ccat_snoc(xs: List<&2, SV.Class>, +y: SV.Class, +zs: List<&2, SV.Class>) -> {ccat(DPS.csnoc(xs, y), zs) == ccat(xs, Con{y, zs}) : List<&2, SV.Class>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %ccat_snoc(t, y, zs) : {Con{h, ccat(DPS.csnoc(t, y), zs)} == Con{h, _} : List<&2, SV.Class>}
      {==}

def dcat_assoc(xs: List<&2, SV.Drop>, +ys: List<&2, SV.Drop>, +zs: List<&2, SV.Drop>) -> {SV.dcat(SV.dcat(xs, ys), zs) == SV.dcat(xs, SV.dcat(ys, zs)) : List<&2, SV.Drop>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %dcat_assoc(t, ys, zs) : {Con{h, SV.dcat(SV.dcat(t, ys), zs)} == Con{h, _} : List<&2, SV.Drop>}
      {==}

def cdrops_ccat(xs: List<&2, SV.Class>, +ys: List<&2, SV.Class>) -> {SV.cdrops(ccat(xs, ys)) == SV.dcat(SV.cdrops(xs), SV.cdrops(ys)) : List<&2, SV.Drop>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(List<&2, SV.Drop>, SV.cdrops(ccat(t, ys)), SV.dcat(SV.cdrops(t), SV.cdrops(ys)), cdrops_ccat(t, ys)) : {SV.dcat(SV.kdd(h), _) == SV.dcat(SV.dcat(SV.kdd(h), SV.cdrops(t)), SV.cdrops(ys)) : List<&2, SV.Drop>}
      Equal.sym(List<&2, SV.Drop>, SV.dcat(SV.dcat(SV.kdd(h), SV.cdrops(t)), SV.cdrops(ys)), SV.dcat(SV.kdd(h), SV.dcat(SV.cdrops(t), SV.cdrops(ys))), dcat_assoc(SV.kdd(h), SV.cdrops(t), SV.cdrops(ys)))

def drops_dcat(xs: List<&2, SV.Drop>, +ys: List<&2, SV.Drop>) -> {SV.drops(SV.dcat(xs, ys)) == SV.cat(SV.drops(xs), SV.drops(ys)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{SV.Drop{+j, +nd, +q}, +t}:
      %Equal.sym(List<&2, Nat>, SV.drops(SV.dcat(t, ys)), SV.cat(SV.drops(t), SV.drops(ys)), drops_dcat(t, ys)) : {Con{j, _} == Con{j, SV.cat(SV.drops(t), SV.drops(ys))} : List<&2, Nat>}
      {==}

def kdd_drops(k: SV.Class) -> {SV.drops(SV.kdd(k)) == SV.kdrops(k) : List<&2, Nat>}:
  match k:
    case SV.Kept{ds}:
      {==}
    case SV.Amber{ds, rs}:
      {==}
    case SV.Over{j, s, w}:
      {==}
    case SV.Conflict{s, nd}:
      {==}

def dd_eq(cls: List<&2, SV.Class>) -> {SV.drops(SV.cdrops(cls)) == SV.dropped(cls) : List<&2, Nat>}:
  match cls:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %Equal.sym(List<&2, Nat>, SV.drops(SV.dcat(SV.kdd(h), SV.cdrops(t))), SV.cat(SV.drops(SV.kdd(h)), SV.drops(SV.cdrops(t))), drops_dcat(SV.kdd(h), SV.cdrops(t))) : {_ == SV.cat(SV.kdrops(h), SV.dropped(t)) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, SV.drops(SV.kdd(h)), SV.kdrops(h), kdd_drops(h)) : {SV.cat(_, SV.drops(SV.cdrops(t))) == SV.cat(SV.kdrops(h), SV.dropped(t)) : List<&2, Nat>}
      %Equal.sym(List<&2, Nat>, SV.drops(SV.cdrops(t)), SV.dropped(t), dd_eq(t)) : {SV.cat(SV.kdrops(h), _) == SV.cat(SV.kdrops(h), SV.dropped(t)) : List<&2, Nat>}
      {==}

def bor_fl(a: Bool, +b: Bool, h: {SV.bor(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.tf(h))
    case False{}:
      {==}

def bor_fr(a: Bool, +b: Bool, h: {SV.bor(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      absurd({b == False{} : Bool}, KA.tf(h))
    case False{}:
      h

# an equation no drop names has no nd
def dna(dd: List<&2, SV.Drop>, +j: Nat, +h: {SV.mem(j, SV.drops(dd)) == False{} : Bool}) -> {SV.dnd.go(dd, j) == Nil{} : List<&2, Nat>}:
  match dd:
    case Nil{}:
      {==}
    case Con{SV.Drop{+i, +nd, +q}, +t}:
      +hji = bor_fl(SV.eq(j, i), SV.mem(j, SV.drops(t)), h)
      %Equal.sym(Bool, SV.eq(i, j), False{}, Equal.trans(Bool, SV.eq(i, j), SV.eq(j, i), False{}, LI.eq_sym(i, j), hji)) : {SV.dnd.pick(_, nd, SV.dnd.go(t, j)) == Nil{} : List<&2, Nat>}
      dna(t, j, bor_fr(SV.eq(j, i), SV.mem(j, SV.drops(t)), h))

# drops after the ones that name j do not change j's nd
def dnc(xs: List<&2, SV.Drop>, +ys: List<&2, SV.Drop>, +j: Nat, +h: {SV.mem(j, SV.drops(ys)) == False{} : Bool}) -> {SV.dnd.go(SV.dcat(xs, ys), j) == SV.dnd.go(xs, j) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      dna(ys, j, h)
    case Con{SV.Drop{+i, +nd, +q}, +t}:
      %dnc(t, ys, j, h) : {SV.dnd.pick(SV.eq(i, j), nd, SV.dnd.go(SV.dcat(t, ys), j)) == SV.dnd.pick(SV.eq(i, j), nd, _) : List<&2, Nat>}
      {==}

def nodrop_x(+X: List<&2, SV.Class>, +own: List<&2, Nat>, +i: Nat, +j: Nat, +hD: {CL.downs(own, X, i) == True{} : Bool}, +hl: {SV.lt(SV.nth(own, j), i) == True{} : Bool}) -> {SV.mem(j, SV.drops(SV.cdrops(X))) == False{} : Bool}:
  %Equal.sym(List<&2, Nat>, SV.drops(SV.cdrops(X)), SV.dropped(X), dd_eq(X)) : {SV.mem(j, _) == False{} : Bool}
  %Equal.sym(Bool, SV.mem(j, SV.dropped(X)), SV.mem(j, CL.dk_abs(X, i, SV.nth(own, j))), CL.mem_dropped_dk(own, X, i, j, hD)) : {_ == False{} : Bool}
  %Equal.sym(List<&2, Nat>, CL.dk_abs(X, i, SV.nth(own, j)), Nil{}, CL.dk_lt(X, i, SV.nth(own, j), hl)) : {SV.mem(j, _) == False{} : Bool}
  {==}

# j's nd is the same in the classes so far and in them followed by X
def dnd_pc(+pc: List<&2, SV.Class>, +X: List<&2, SV.Class>, +own: List<&2, Nat>, +i: Nat, +j: Nat, +hD: {CL.downs(own, X, i) == True{} : Bool}, +hl: {SV.lt(SV.nth(own, j), i) == True{} : Bool})
  -> {SV.dnd_at(pc, j) == SV.dnd_at(ccat(pc, X), j) : List<&2, Nat>}:
  %Equal.sym(List<&2, SV.Drop>, SV.cdrops(ccat(pc, X)), SV.dcat(SV.cdrops(pc), SV.cdrops(X)), cdrops_ccat(pc, X)) : {SV.dnd.go(SV.cdrops(pc), j) == SV.dnd.go(_, j) : List<&2, Nat>}
  Equal.sym(List<&2, Nat>, SV.dnd.go(SV.dcat(SV.cdrops(pc), SV.cdrops(X)), j), SV.dnd.go(SV.cdrops(pc), j), dnc(SV.cdrops(pc), SV.cdrops(X), j, nodrop_x(X, own, i, j, hD, hl)))


def pcf.c(b: Bool, +e: E.QExpr, +own: List<&2, Nat>, +cs: List<&2, Nat>, +sk: SK.Sketch, +pc: List<&2, SV.Class>, +X: List<&2, SV.Class>, +i: Nat, +k: Nat, +R0: List<&2, DR.Fact>, eb: {SV.mem(SV.nth(own, k), cs) == b : Bool},
  +hb: {SV.below(cs, i) == True{} : Bool}, +hD: {CL.downs(own, X, i) == True{} : Bool})
  -> {SV.facts.pick(b, DR.Fact{e, SV.dnd_at(pc, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(own, k)))}, R0) == SV.facts.pick(b, DR.Fact{e, SV.dnd_at(ccat(pc, X), k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(own, k)))}, R0) : List<&2, DR.Fact>}:
  match b:
    case True{}:
      %dnd_pc(pc, X, own, i, k, hD, D.below_mem(SV.nth(own, k), cs, i, eb, hb)) : {Con{DR.Fact{e, SV.dnd_at(pc, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(own, k)))}, R0} == Con{DR.Fact{e, _, SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(own, k)))}, R0} : List<&2, DR.Fact>}
      {==}
    case False{}:
      {==}

# the facts of constraints before i read the same nd from pc as from pc
# followed by later classes
def pcf(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +cs: List<&2, Nat>, +sk: SK.Sketch, +pc: List<&2, SV.Class>, +X: List<&2, SV.Class>, +i: Nat, +k: Nat, +hb: {SV.below(cs, i) == True{} : Bool}, +hD: {CL.downs(own, X, i) == True{} : Bool})
  -> {SV.facts.go(es, own, cs, sk, pc, True{}, k) == SV.facts.go(es, own, cs, sk, ccat(pc, X), True{}, k) : List<&2, DR.Fact>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %pcf(t, own, cs, sk, pc, X, i, 1n+k, hb, hD) : {SV.facts.pick(SV.mem(SV.nth(own, k), cs), DR.Fact{e, SV.dnd_at(pc, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(own, k)))}, SV.facts.go(t, own, cs, sk, pc, True{}, 1n+k)) == SV.facts.pick(SV.mem(SV.nth(own, k), cs), DR.Fact{e, SV.dnd_at(ccat(pc, X), k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(own, k)))}, _) : List<&2, DR.Fact>}
      pcf.c(SV.mem(SV.nth(own, k), cs), e, own, cs, sk, pc, X, i, k, SV.facts.go(t, own, cs, sk, pc, True{}, 1n+k), {==}, hb, hD)

# the classes from position m on drop only their own equations
def downs_cdrop(+own: List<&2, Nat>, m: Nat, cls: List<&2, SV.Class>, +j: Nat, +h: {CL.downs(own, cls, j) == True{} : Bool}) -> {CL.downs(own, CL.cdrop(m, cls), Nat.add(m, j)) == True{} : Bool}:
  match m cls:
    case 0n cls:
      h
    case 1n++k Nil{}:
      {==}
    case 1n++k Con{+hh, +t}:
      %Equal.sym(Nat, 1n+Nat.add(k, j), Nat.add(k, 1n+j), LN.add_succ(k, j)) : {CL.downs(own, CL.cdrop(k, t), _) == True{} : Bool}
      downs_cdrop(own, k, t, 1n+j, LI.band_r(KB.allo(own, SV.kdrops(hh), j), CL.downs(own, t, 1n+j), h))

# one step of the classes so far: pc followed by the classes from i is the
# final list, then so is pc and the class at i followed by those from i+1
def hpc_step(+pc: List<&2, SV.Class>, +K: SV.Class, +tail: List<&2, SV.Class>, +i: Nat, +cls: List<&2, SV.Class>, +hc: {CL.cdrop(i, cls) == Con{K, tail} : List<&2, SV.Class>}, hpc: {ccat(pc, CL.cdrop(i, cls)) == cls : List<&2, SV.Class>})
  -> {ccat(DPS.csnoc(pc, K), CL.cdrop(1n+i, cls)) == cls : List<&2, SV.Class>}:
  %Equal.sym(List<&2, SV.Class>, CL.cdrop(1n+i, cls), tail, CL.cdrop_step(cls, i, K, tail, hc)) : {ccat(DPS.csnoc(pc, K), _) == cls : List<&2, SV.Class>}
  %Equal.sym(List<&2, SV.Class>, ccat(DPS.csnoc(pc, K), tail), ccat(pc, Con{K, tail}), ccat_snoc(pc, K, tail)) : {_ == cls : List<&2, SV.Class>}
  %hc : {ccat(pc, _) == cls : List<&2, SV.Class>}
  hpc

# Each driving constraint's class
# -------------------------------


# c is red, or driven: nothing changes but the position
def step_same(+sk: SK.Sketch, +i: Nat, +st: PA.PS, hi: PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, st), +hz: {SP.zc(SV.owners(sk), i, SV.reds(DPS.classes2(sk))) == True{} : Bool}, +hdc: {KB.dcond(sk, SV.reds(DPS.classes2(sk)), i) == False{} : Bool})
  -> PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), 1n+i, st):
  (+hb, q1) = hi
  (+hk, q2) = q1
  (hK, q3) = q2
  (hl, q4) = q3
  (hB, hp) = q4
  (PP.pib_mk(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), 1n+i, PP.ps.rows(st), PP.ps.B(st), PP.ps.bp(st), PP.ps.vm(st), PP.pib_rinv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PP.ps.rows(st), PP.ps.B(st), PP.ps.bp(st), PP.ps.vm(st), hb), PP.pib_dist(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PP.ps.rows(st), PP.ps.B(st), PP.ps.bp(st), PP.ps.vm(st), hb), PP.pib_mlen(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PP.ps.rows(st), PP.ps.B(st), PP.ps.bp(st), PP.ps.vm(st), hb), PP.pib_valid(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PP.ps.rows(st), PP.ps.B(st), PP.ps.bp(st), PP.ps.vm(st), hb), PP.pib_s1(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PP.ps.rows(st), PP.ps.B(st), PP.ps.bp(st), PP.ps.vm(st), hb), PP.pib_s2(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PP.ps.rows(st), PP.ps.B(st), PP.ps.bp(st), PP.ps.vm(st), hb), PP.pib_bpd(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PP.ps.rows(st), PP.ps.B(st), PP.ps.bp(st), PP.ps.vm(st), hb), PP.pib_bpb(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PP.ps.rows(st), PP.ps.B(st), PP.ps.bp(st), PP.ps.vm(st), hb),
      PP.allpre_up(PP.ps.bp(st), SV.owners(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PP.pib_pre(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PP.ps.rows(st), PP.ps.B(st), PP.ps.bp(st), PP.ps.vm(st), hb))),
    (Equal.trans(List<&2, Nat>, PP.ps.kb(st), SV.kept_before(sk, SV.reds(DPS.classes2(sk)), i), SV.kept_before(sk, SV.reds(DPS.classes2(sk)), 1n+i), hk, Equal.sym(List<&2, Nat>, SV.kept_before(sk, SV.reds(DPS.classes2(sk)), 1n+i), SV.kept_before(sk, SV.reds(DPS.classes2(sk)), i),
        (%hdc : {SV.kept_before(sk, SV.reds(DPS.classes2(sk)), 1n+i) == KB.kpk(_, SV.kept_before(sk, SV.reds(DPS.classes2(sk)), i), i) : List<&2, Nat>}
          KB.kb_next(sk, SV.reds(DPS.classes2(sk)), i)))),
    ((%hdc : KB.KBP(sk, SV.reds(DPS.classes2(sk)), KB.kpk(_, PP.ps.kb(st), i), 1n+i)
        KB.kbp_next(sk, SV.reds(DPS.classes2(sk)), PP.ps.kb(st), i, hK)),
    (hl,
    (Equal.trans(List<&2, E.QExpr>, PP.ps.B(st), SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i), SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), 1n+i), hB, Equal.sym(List<&2, E.QExpr>, SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), 1n+i), SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i), SP.presolved_same(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, hz))),
      hp)))))

# c is kept: its equations not dropped join the basis, its unit the
# matching, and c the kept constraints
def step_kept(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +vm2: List<&2, Maybe<&2, Nat>>, +K: SV.Class, hi: PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}), hcw: CW.CWInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.CW{rows2, B2, bp2, dd, us}), +hgok: {GM.gok(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2) == True{} : Bool},
  +hK: {SV.class_at(DPS.classes2(sk), i) == K : SV.Class}, +hkd: {SV.kdrops(K) == SV.drops(dd) : List<&2, Nat>}, +hred: {SV.mem(i, SV.reds(DPS.classes2(sk))) == False{} : Bool}, +hdrv: {SV.driving(sk, i) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), DPS.classes2(sk), 0n) == True{} : Bool})
  -> PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), 1n+i, PA.PS{CO.lsnoc(kb, i), rows2, B2, bp2, vm2}):
  (+hb, q1) = hi
  (+hk, q2) = q1
  (hKB, q3) = q2
  (hl, q4) = q3
  (hB, hp) = q4
  (+hcb, c1) = hcw
  (hcl, c2) = c1
  (hcB, c3) = c2
  (hcp, hbp2) = c3
  +d = SV.drops(dd)
  +hdc = PP.dcond_t(sk, SV.reds(DPS.classes2(sk)), i, hdrv, hred)
  +hown = CW.cwb_uown(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb)
  +hdis = CW.cwb_udisj(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb)
  +hbpd = PP.dist_cat(bp, us, PP.pib_bpd(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm, hb), CW.cwb_udist(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb), PP.nonein_pre(bp, SV.owners(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, us, PP.pib_pre(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm, hb), hown))
  +hbpb = PP.below_cat(bp, us, SV.neqs(SK.Sketch.eqs(sk)), PP.pib_bpb(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm, hb), CW.cwb_ubelow(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb))
  +hpre = PP.allpre_cat(bp, us, SV.owners(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), 1n+i, PP.allpre_up(bp, SV.owners(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PP.pib_pre(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm, hb)), PP.allpre_us(us, SV.owners(sk), SV.reds(DPS.classes2(sk)), DPS.classes2(sk), i, K, d, hD, hK, hkd, hown, hred, hdis))
  +E2 = Equal.sym(List<&2, Nat>, bp2, SV.cat(bp, us), hbp2)
  (PP.pib_mk(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), 1n+i, rows2, B2, bp2, vm2, CW.cwb_rinv(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb), GM.gok_dist(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2, hgok), GM.gok_mlen(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2, hgok), GM.gok_valid(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2, hgok),
      (%E2 : {L.subl(ST.somes(vm2), _) == True{} : Bool}
        GM.gok_s1(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2, hgok)),
      (%E2 : {L.subl(_, ST.somes(vm2)) == True{} : Bool}
        GM.gok_s2(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2, hgok)),
      (%E2 : {SV.distinct(_) == True{} : Bool}
        hbpd),
      (%E2 : {SV.below(_, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}
        hbpb),
      (%E2 : {PP.allpre(_, SV.owners(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), 1n+i) == True{} : Bool}
        hpre)),
    (Equal.trans(List<&2, Nat>, CO.lsnoc(kb, i), CO.lsnoc(SV.kept_before(sk, SV.reds(DPS.classes2(sk)), i), i), SV.kept_before(sk, SV.reds(DPS.classes2(sk)), 1n+i), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => CO.lsnoc(z, i), kb, SV.kept_before(sk, SV.reds(DPS.classes2(sk)), i), hk),
        Equal.sym(List<&2, Nat>, SV.kept_before(sk, SV.reds(DPS.classes2(sk)), 1n+i), CO.lsnoc(SV.kept_before(sk, SV.reds(DPS.classes2(sk)), i), i), (%hdc : {SV.kept_before(sk, SV.reds(DPS.classes2(sk)), 1n+i) == KB.kpk(_, SV.kept_before(sk, SV.reds(DPS.classes2(sk)), i), i) : List<&2, Nat>}
          KB.kb_next(sk, SV.reds(DPS.classes2(sk)), i)))),
    ((%hdc : KB.KBP(sk, SV.reds(DPS.classes2(sk)), KB.kpk(_, kb, i), 1n+i)
        KB.kbp_next(sk, SV.reds(DPS.classes2(sk)), kb, i, hKB)),
    (hcl,
    (Equal.trans(List<&2, E.QExpr>, B2, SK.cat(SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i), SV.own_rest(sk, i, d, SV.neqs(SK.Sketch.eqs(sk)))), SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), 1n+i), hcB,
        Equal.sym(List<&2, E.QExpr>, SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), 1n+i), SK.cat(SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i), SV.own_rest(sk, i, d, SV.neqs(SK.Sketch.eqs(sk)))), SP.presolved_kept(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), d, i, hred, PP.agree_of(SV.owners(sk), SV.owners(sk), DPS.classes2(sk), i, K, d, 0n, {==}, hD, hK, hkd)))),
      hcp)))))

# the pass's class at c and its state after
def StepRes2(+sk: SK.Sketch, +i: Nat, +o: PA.PO) -> Type:
  DH.Fate.driving(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PO.k(o)) & PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), 1n+i, PA.PO.st(o))

def red_of(+sk: SK.Sketch, +i: Nat, +K: SV.Class, +hK: {SV.class_at(DPS.classes2(sk), i) == K : SV.Class}) -> {SV.mem(i, SV.reds(DPS.classes2(sk))) == SV.is_red(K) : Bool}:
  Equal.trans(Bool, SV.mem(i, SV.reds(DPS.classes2(sk))), SV.is_red(SV.class_at(DPS.classes2(sk), i)), SV.is_red(K), CL.mem_reds(DPS.classes2(sk), i), Equal.cong(SV.Class, Bool, z => SV.is_red(z), SV.class_at(DPS.classes2(sk), i), K, hK))


# c's context, read from the pass's kept constraints
def hcx_of(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +hkb: {kb == SV.kept_before(sk, SV.reds(DPS.classes2(sk)), i) : List<&2, Nat>}) -> {SV.eqs_of(sk, Con{i, kb}) == SV.ctx(sk, SV.reds(DPS.classes2(sk)), i) : List<&2, E.QExpr>}:
  Equal.cong(List<&2, Nat>, List<&2, E.QExpr>, z => SV.eqs_of(sk, Con{i, z}), kb, SV.kept_before(sk, SV.reds(DPS.classes2(sk)), i), hkb)

def kb_below(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, hk: KB.KBP(sk, SV.reds(DPS.classes2(sk)), kb, i)) -> {SV.below(kb, i) == True{} : Bool}:
  +h = KB.kbp_bool(sk, SV.reds(DPS.classes2(sk)), kb, i, hk)
  LI.band_l(SV.below(kb, i), SV.band(SV.all_driving(sk, kb), SV.none_in(kb, SV.reds(DPS.classes2(sk)))), LI.band_r(SV.distinct(kb), SV.band(SV.below(kb, i), SV.band(SV.all_driving(sk, kb), SV.none_in(kb, SV.reds(DPS.classes2(sk))))), h))

def downs_at(+sk: SK.Sketch, +i: Nat, +hD: {CL.downs(SV.owners(sk), DPS.classes2(sk), 0n) == True{} : Bool}) -> {CL.downs(SV.owners(sk), CL.cdrop(i, DPS.classes2(sk)), i) == True{} : Bool}:
  (%Equal.sym(Nat, i, Nat.add(i, 0n), LN.add_zero(i)) : {CL.downs(SV.owners(sk), CL.cdrop(i, DPS.classes2(sk)), _) == True{} : Bool}
    downs_cdrop(SV.owners(sk), i, DPS.classes2(sk), 0n, hD))

# the facts the pass reads for c are the spec's
def hf0_of(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +pc: List<&2, SV.Class>, +hkb: {kb == SV.kept_before(sk, SV.reds(DPS.classes2(sk)), i) : List<&2, Nat>}, +hb: {SV.below(kb, i) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), DPS.classes2(sk), 0n) == True{} : Bool},
  +hpc: {ccat(pc, CL.cdrop(i, DPS.classes2(sk))) == DPS.classes2(sk) : List<&2, SV.Class>}) -> {SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), kb, sk, pc, True{}, 0n) == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), SV.kept_before(sk, SV.reds(DPS.classes2(sk)), i), sk, DPS.classes2(sk), True{}, 0n) : List<&2, DR.Fact>}:
  %hkb : {SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), kb, sk, pc, True{}, 0n) == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), _, sk, DPS.classes2(sk), True{}, 0n) : List<&2, DR.Fact>}
  %hpc : {SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), kb, sk, pc, True{}, 0n) == SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), kb, sk, _, True{}, 0n) : List<&2, DR.Fact>}
  pcf(SK.Sketch.eqs(sk), SV.owners(sk), kb, sk, pc, CL.cdrop(i, DPS.classes2(sk)), i, 0n, hb, downs_at(sk, i, hD))

# no refutation of either kind
def nr2_of(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +hkb: {kb == SV.kept_before(sk, SV.reds(DPS.classes2(sk)), i) : List<&2, Nat>}, +eb: {DCF.refutable2(sk, i, kb, SV.eqs_of(sk, Con{i, kb})) == False{} : Bool}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> SV.NoRefute2(sk, SV.reds(DPS.classes2(sk)), i):
  (PR.norefute(sk, SV.reds(DPS.classes2(sk)), i, (%hkb : {CO.refutable(sk, i, _) == False{} : Bool}
      DCP.r2f.0(sk, i, kb, SV.eqs_of(sk, Con{i, kb}), eb))),
   (%hkb : SV.NoDirRef(sk, i, _, SV.ctx(sk, SV.reds(DPS.classes2(sk)), i))
     (%hcx_of(sk, i, kb, hkb) : SV.NoDirRef(sk, i, kb, _)
       DCP.dnone(sk, i, kb, SV.eqs_of(sk, Con{i, kb}), DCP.r2f.d(sk, i, kb, SV.eqs_of(sk, Con{i, kb}), eb), hcov, hwf))))

# a conflict: the generalized filter's support and nd
def step.conf2(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +hi: PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}), +hr: {DCF.refutable2(sk, i, kb, SV.eqs_of(sk, Con{i, kb})) == True{} : Bool},
  +hK: {SV.class_at(DPS.classes2(sk), i) == SV.Conflict{DCF.support2(sk, i, SV.eqs_of(sk, Con{i, kb}), kb), DCF.cnd(sk, i, DCF.support2(sk, i, SV.eqs_of(sk, Con{i, kb}), kb), SV.eqs_of(sk, Con{i, kb}))} : SV.Class}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> StepRes2(sk, i, PA.PO{SV.Conflict{DCF.support2(sk, i, SV.eqs_of(sk, Con{i, kb}), kb), DCF.cnd(sk, i, DCF.support2(sk, i, SV.eqs_of(sk, Con{i, kb}), kb), SV.eqs_of(sk, Con{i, kb}))}, PA.PS{kb, rows, B, bp, vm}}):
  +hkb = PP.pinv_kb(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi)
  +hcx = hcx_of(sk, i, kb, hkb)
  +hred = red_of(sk, i, SV.Conflict{DCF.support2(sk, i, SV.eqs_of(sk, Con{i, kb}), kb), DCF.cnd(sk, i, DCF.support2(sk, i, SV.eqs_of(sk, Con{i, kb}), kb), SV.eqs_of(sk, Con{i, kb}))}, hK)
  ((%Equal.sym(List<&2, E.QExpr>, SV.eqs_of(sk, Con{i, kb}), SV.ctx(sk, SV.reds(DPS.classes2(sk)), i), hcx) : DH.ConflictOk(sk, SV.reds(DPS.classes2(sk)), i, DCF.support2(sk, i, _, kb), DCF.cnd(sk, i, DCF.support2(sk, i, _, kb), _))
      DCP.conflict2_ok(sk, SV.reds(DPS.classes2(sk)), i, kb, KB.kbp_bool(sk, SV.reds(DPS.classes2(sk)), kb, i, PP.pinv_kbp(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi)),
        (%hcx : {DCF.refutable2(sk, i, kb, _) == True{} : Bool}
          hr), hcov, hwf)),
   step_same(sk, i, PA.PS{kb, rows, B, bp, vm}, hi, SP.zc_red(SV.owners(sk), i, SV.reds(DPS.classes2(sk)), hred), PP.dcond_f(sk, SV.reds(DPS.classes2(sk)), i, hred)))

def bpus_dist(+sk: SK.Sketch, +i: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +us: List<&2, Nat>, +hb: {PP.pib(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm) == True{} : Bool},
  +hud: {SV.distinct(us) == True{} : Bool}, +hown: {KB.allo(SV.owners(sk), us, i) == True{} : Bool}) -> {SV.distinct(SV.cat(bp, us)) == True{} : Bool}:
  PP.dist_cat(bp, us, PP.pib_bpd(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm, hb), hud, PP.nonein_pre(bp, SV.owners(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, us, PP.pib_pre(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm, hb), hown))

def step.over(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>, +j: Nat, +s: List<&2, Nat>, +x: List<&2, Nat>,
  +hi: PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}), hdo: DH.DropsOk(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, SV.drops(dd)), +hcb: {CW.cwb(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us) == True{} : Bool}, hnr: SV.NoRefute2(sk, SV.reds(DPS.classes2(sk)), i),
  gr: GM.GRes(SK.Sketch.eqs(sk), PA.nvars(sk), bp, us, ST.GFail{ST.Red{j, s, x}}), +hK: {SV.class_at(DPS.classes2(sk), i) == SV.Over{j, s, x} : SV.Class}) -> StepRes2(sk, i, PA.PO{SV.Over{j, s, x}, PA.PS{kb, rows, B, bp, vm}}):
  (+hb2, hov) = gr
  +hred = red_of(sk, i, SV.Over{j, s, x}, hK)
  +hr2 = L.band_r(SV.mem(j, us), SV.band(SV.mem(j, s), L.subl(s, SV.cat(bp, us))), hb2)
  ((hnr, (SV.drops(dd), (hdo, (L.band_i(SV.eq(SV.nth(SV.owners(sk), j), i), SV.band(SV.mem(j, s), SV.clean(SV.owners(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.drops(dd), i, s)),
      PP.allo_mem(SV.owners(sk), us, i, j, CW.cwb_uown(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb), L.band_l(SV.mem(j, us), SV.band(SV.mem(j, s), L.subl(s, SV.cat(bp, us))), hb2)),
      L.band_i(SV.mem(j, s), SV.clean(SV.owners(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.drops(dd), i, s), L.band_l(SV.mem(j, s), L.subl(s, SV.cat(bp, us)), hr2),
        PP.clean_of(s, SV.owners(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), SV.drops(dd), i, bp, us, L.band_r(SV.mem(j, s), L.subl(s, SV.cat(bp, us)), hr2), PP.pib_pre(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm, PP.pinv_b(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi)), CW.cwb_uown(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb), CW.cwb_udisj(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb)))), hov)))),
    step_same(sk, i, PA.PS{kb, rows, B, bp, vm}, hi, SP.zc_red(SV.owners(sk), i, SV.reds(DPS.classes2(sk)), hred), PP.dcond_f(sk, SV.reds(DPS.classes2(sk)), i, hred)))


def imp_at(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rs: List<&2, SV.Ref>, +em: {PA.srefs(SV.csides(sk, [i]), sk, kb, i, 0n) == Some{rs} : Maybe<&2, List<&2, SV.Ref>>}, +hkb: {kb == SV.kept_before(sk, SV.reds(DPS.classes2(sk)), i) : List<&2, Nat>}, +j: Nat, hj: {SV.lt(j, SV.slen(SV.csides(sk, [i]))) == True{} : Bool})
  -> SV.Implied(sk, SV.reds(DPS.classes2(sk)), i, j):
  (%hkb : PR.ImpK(sk, _, i, j)
    PR.srefs_some(SV.csides(sk, [i]), sk, kb, i, 0n, rs, em, j, hj))

def notimp(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +em: {PA.srefs(SV.csides(sk, [i]), sk, kb, i, 0n) == None{} : Maybe<&2, List<&2, SV.Ref>>}, +hkb: {kb == SV.kept_before(sk, SV.reds(DPS.classes2(sk)), i) : List<&2, Nat>}) -> &j: Nat -> ({SV.lt(j, SV.slen(SV.csides(sk, [i]))) == True{} : Bool} & SV.NotImplied(sk, SV.reds(DPS.classes2(sk)), i, j)):
  (%hkb : PR.NotK(sk, _, i, 0n, SV.slen(SV.csides(sk, [i])))
    PR.srefs_none(SV.csides(sk, [i]), sk, kb, i, 0n, em))

def noamb(+sk: SK.Sketch, +i: Nat, +dd: List<&2, SV.Drop>, +ea: {SV.is_amberable(sk, i, SV.drops(dd)) == False{} : Bool}, ha: {SV.is_amberable(sk, i, SV.drops(dd)) == True{} : Bool}) -> &j: Nat -> ({SV.lt(j, SV.slen(SV.csides(sk, [i]))) == True{} : Bool} & SV.NotImplied(sk, SV.reds(DPS.classes2(sk)), i, j)):
  absurd(&j: Nat -> ({SV.lt(j, SV.slen(SV.csides(sk, [i]))) == True{} : Bool} & SV.NotImplied(sk, SV.reds(DPS.classes2(sk)), i, j)), KA.tf(Equal.trans(Bool, True{}, SV.is_amberable(sk, i, SV.drops(dd)), False{}, Equal.sym(Bool, SV.is_amberable(sk, i, SV.drops(dd)), True{}, ha), ea)))


def step.a(m: Maybe<&2, List<&2, SV.Ref>>, +sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +dd: List<&2, SV.Drop>, +em: {PA.srefs(SV.csides(sk, [i]), sk, kb, i, 0n) == m : Maybe<&2, List<&2, SV.Ref>>}, +ea: {SV.is_amberable(sk, i, SV.drops(dd)) == True{} : Bool},
  hnr: SV.NoRefute2(sk, SV.reds(DPS.classes2(sk)), i), hdo: DH.DropsOk(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, SV.drops(dd)), hnd: DH.DropsNd(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, dd), hmt: SV.Matchable(SK.cat(SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i), SV.own_rest(sk, i, SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk))))), +hkb: {kb == SV.kept_before(sk, SV.reds(DPS.classes2(sk)), i) : List<&2, Nat>})
  -> DH.Fate.driving(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.one.a(PA.srefs(SV.csides(sk, [i]), sk, kb, i, 0n), dd)):
  match m:
    case None{}:
      %Equal.sym(Maybe<&2, List<&2, SV.Ref>>, PA.srefs(SV.csides(sk, [i]), sk, kb, i, 0n), None{}, em) : DH.Fate.driving(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.one.a(_, dd))
      (hnr, (hdo, (hnd, (hmt, ha => notimp(sk, i, kb, em, hkb)))))
    case Some{+rs}:
      %Equal.sym(Maybe<&2, List<&2, SV.Ref>>, PA.srefs(SV.csides(sk, [i]), sk, kb, i, 0n), Some{rs}, em) : DH.Fate.driving(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.one.a(_, dd))
      (hnr, (hdo, (hnd, (ea, j => hj => imp_at(sk, i, kb, rs, em, hkb, j, hj)))))

def step.k(a: Bool, +sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +dd: List<&2, SV.Drop>, +ea: {SV.is_amberable(sk, i, SV.drops(dd)) == a : Bool}, hnr: SV.NoRefute2(sk, SV.reds(DPS.classes2(sk)), i), hdo: DH.DropsOk(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, SV.drops(dd)), hnd: DH.DropsNd(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, dd), hmt: SV.Matchable(SK.cat(SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i), SV.own_rest(sk, i, SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk))))),
  +hkb: {kb == SV.kept_before(sk, SV.reds(DPS.classes2(sk)), i) : List<&2, Nat>}) -> DH.Fate.driving(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd)):
  match a:
    case True{}:
      %Equal.sym(Bool, SV.is_amberable(sk, i, SV.drops(dd)), True{}, ea) : DH.Fate.driving(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.one.k(_, sk, kb, i, dd))
      step.a(PA.srefs(SV.csides(sk, [i]), sk, kb, i, 0n), sk, i, kb, dd, {==}, ea, hnr, hdo, hnd, hmt, hkb)
    case False{}:
      %Equal.sym(Bool, SV.is_amberable(sk, i, SV.drops(dd)), False{}, ea) : DH.Fate.driving(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.one.k(_, sk, kb, i, dd))
      (hnr, (hdo, (hnd, (hmt, ha => noamb(sk, i, dd, ea, ha)))))


def mt_eq(+sk: SK.Sketch, +i: Nat, +bp: List<&2, Nat>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>, hcB: {B2 == SK.cat(SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i), SV.own_rest(sk, i, SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk)))) : List<&2, E.QExpr>},
  hcp: {B2 == SV.picked(SK.Sketch.eqs(sk), bp2) : List<&2, E.QExpr>}, hbp2: {bp2 == SV.cat(bp, us) : List<&2, Nat>}) -> {SV.picked(SK.Sketch.eqs(sk), SV.cat(bp, us)) == SK.cat(SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i), SV.own_rest(sk, i, SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk)))) : List<&2, E.QExpr>}:
  Equal.trans(List<&2, E.QExpr>, SV.picked(SK.Sketch.eqs(sk), SV.cat(bp, us)), SV.picked(SK.Sketch.eqs(sk), bp2), SK.cat(SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i), SV.own_rest(sk, i, SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk)))),
    Equal.cong(List<&2, Nat>, List<&2, E.QExpr>, z => SV.picked(SK.Sketch.eqs(sk), z), SV.cat(bp, us), bp2, Equal.sym(List<&2, Nat>, bp2, SV.cat(bp, us), hbp2)),
    Equal.trans(List<&2, E.QExpr>, SV.picked(SK.Sketch.eqs(sk), bp2), B2, SK.cat(SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i), SV.own_rest(sk, i, SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk)))), Equal.sym(List<&2, E.QExpr>, B2, SV.picked(SK.Sketch.eqs(sk), bp2), hcp), hcB))

def mt_of(+sk: SK.Sketch, +i: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>, +vm2: List<&2, Maybe<&2, Nat>>,
  +hb: {PP.pib(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm) == True{} : Bool}, +hcb: {CW.cwb(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us) == True{} : Bool},
  hcB: {B2 == SK.cat(SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i), SV.own_rest(sk, i, SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk)))) : List<&2, E.QExpr>}, hcp: {B2 == SV.picked(SK.Sketch.eqs(sk), bp2) : List<&2, E.QExpr>}, hbp2: {bp2 == SV.cat(bp, us) : List<&2, Nat>},
  +hgok: {GM.gok(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2) == True{} : Bool}) -> SV.Matchable(SK.cat(SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i), SV.own_rest(sk, i, SV.drops(dd), SV.neqs(SK.Sketch.eqs(sk))))):
  (%mt_eq(sk, i, bp, B2, bp2, dd, us, hcB, hcp, hbp2) : SV.Matchable(_)
    GM.matchable_of(SK.Sketch.eqs(sk), vm2, SV.cat(bp, us), GM.gok_valid(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2, hgok), GM.gok_s2(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2, hgok),
      bpus_dist(sk, i, rows, B, bp, vm, us, hb, CW.cwb_udist(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb), CW.cwb_uown(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb))))

def step.ok(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>, +vm2: List<&2, Maybe<&2, Nat>>,
  +hi: PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}), hdo: DH.DropsOk(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, SV.drops(dd)), hnd: DH.DropsNd(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, dd), +hci: CW.CWInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.CW{rows2, B2, bp2, dd, us}), hnr: SV.NoRefute2(sk, SV.reds(DPS.classes2(sk)), i),
  +hgok: {GM.gok(SK.Sketch.eqs(sk), PA.nvars(sk), SV.cat(bp, us), vm2) == True{} : Bool}, +hK: {SV.class_at(DPS.classes2(sk), i) == PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd) : SV.Class}, +hdrv: {SV.driving(sk, i) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), DPS.classes2(sk), 0n) == True{} : Bool})
  -> StepRes2(sk, i, PA.PO{PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd), PA.PS{CO.lsnoc(kb, i), rows2, B2, bp2, vm2}}):
  (+hcb, c1) = hci
  (hcl, c2) = c1
  (hcB, c3) = c2
  (hcp, hbp2) = c3
  +hb = PP.pinv_b(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi)
  (step.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, i, kb, dd, {==}, hnr, hdo, hnd, mt_of(sk, i, rows, B, bp, vm, rows2, B2, bp2, dd, us, vm2, hb, hcb, hcB, hcp, hbp2, hgok), PP.pinv_kb(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi)),
    step_kept(sk, i, kb, rows, B, bp, vm, rows2, B2, bp2, dd, us, vm2, PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd), hi, hci, hgok, hK, PP.onek_kd(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd),
      Equal.trans(Bool, SV.mem(i, SV.reds(DPS.classes2(sk))), SV.is_red(PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd)), False{}, red_of(sk, i, PA.one.k(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd), hK), PP.onek_red(SV.is_amberable(sk, i, SV.drops(dd)), sk, kb, i, dd)), hdrv, hD))


def step.g(g: ST.GS, +sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +hi: PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}), hdo: DH.DropsOk(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, SV.drops(dd)), hnd: DH.DropsNd(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, dd), +hci: CW.CWInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.CW{rows2, B2, bp2, dd, us}), hnr: SV.NoRefute2(sk, SV.reds(DPS.classes2(sk)), i), gr: GM.GRes(SK.Sketch.eqs(sk), PA.nvars(sk), bp, us, g),
  +hK: {SV.class_at(DPS.classes2(sk), i) == PA.PO.k(PA.one.g(g, sk, i, kb, rows, B, bp, vm, PA.CW{rows2, B2, bp2, dd, us})) : SV.Class}, +hdrv: {SV.driving(sk, i) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), DPS.classes2(sk), 0n) == True{} : Bool}) -> StepRes2(sk, i, PA.one.g(g, sk, i, kb, rows, B, bp, vm, PA.CW{rows2, B2, bp2, dd, us})):
  match g:
    case ST.GFail{ST.Red{+j, +s, +x}}:
      step.over(sk, i, kb, rows, B, bp, vm, rows2, B2, bp2, dd, us, j, s, x, hi, hdo, CW.inv_b(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.CW{rows2, B2, bp2, dd, us}, hci), hnr, gr, hK)
    case ST.GOk{+vm2}:
      step.ok(sk, i, kb, rows, B, bp, vm, rows2, B2, bp2, dd, us, vm2, hi, hdo, hnd, hci, hnr, gr, hK, hdrv, hD)

def gli_of(+sk: SK.Sketch, +i: Nat, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +hb: {PP.pib(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm) == True{} : Bool}, +hcb: {CW.cwb(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us) == True{} : Bool}, +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}) -> {GM.gli(SK.Sketch.eqs(sk), PA.nvars(sk), bp, us, vm) == True{} : Bool}:
  GM.gli_mk(SK.Sketch.eqs(sk), PA.nvars(sk), bp, us, vm, PP.pib_dist(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm, hb), PP.pib_mlen(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm, hb), PP.pib_valid(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm, hb),
    PP.pib_s1(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm, hb), PP.pib_s2(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm, hb),
    bpus_dist(sk, i, rows, B, bp, vm, us, hb, CW.cwb_udist(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb), CW.cwb_uown(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb)),
    PP.below_cat(bp, us, SV.neqs(SK.Sketch.eqs(sk)), PP.pib_bpb(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm, hb), CW.cwb_ubelow(sk, i, SV.neqs(SK.Sketch.eqs(sk)), rows2, B2, dd, us, hcb)), hA)


def step.w2(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +hi: PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}), hdo: DH.DropsOk(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, SV.drops(dd)), hnd: DH.DropsNd(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, dd), +hci: CW.CWInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.CW{rows2, B2, bp2, dd, us}), hnr: SV.NoRefute2(sk, SV.reds(DPS.classes2(sk)), i),
  +hK: {SV.class_at(DPS.classes2(sk), i) == PA.PO.k(PA.one.g(PA.grpl(us, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), ST.GOk{vm}), sk, i, kb, rows, B, bp, vm, PA.CW{rows2, B2, bp2, dd, us})) : SV.Class}, +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hdrv: {SV.driving(sk, i) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), DPS.classes2(sk), 0n) == True{} : Bool})
  -> StepRes2(sk, i, PA.one.g(PA.grpl(us, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), ST.GOk{vm}), sk, i, kb, rows, B, bp, vm, PA.CW{rows2, B2, bp2, dd, us})):
  step.g(PA.grpl(us, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), ST.GOk{vm}), sk, i, kb, rows, B, bp, vm, rows2, B2, bp2, dd, us, hi, hdo, hnd, hci, hnr,
    GM.gl_ok(us, SK.Sketch.eqs(sk), PA.nvars(sk), bp, vm, gli_of(sk, i, rows, B, bp, vm, rows2, B2, dd, us, PP.pinv_b(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi), CW.inv_b(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.CW{rows2, B2, bp2, dd, us}, hci), hA)), hK, hdrv, hD)

def step.w4(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +hi: PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}), hdo: DH.DropsOk(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, SV.drops(dd)), hq: (DH.DropsNd(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, dd) & CW.CWInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.CW{rows2, B2, bp2, dd, us})), hnr: SV.NoRefute2(sk, SV.reds(DPS.classes2(sk)), i),
  +hK: {SV.class_at(DPS.classes2(sk), i) == PA.PO.k(PA.one.g(PA.grpl(us, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), ST.GOk{vm}), sk, i, kb, rows, B, bp, vm, PA.CW{rows2, B2, bp2, dd, us})) : SV.Class}, +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hdrv: {SV.driving(sk, i) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), DPS.classes2(sk), 0n) == True{} : Bool})
  -> StepRes2(sk, i, PA.one.g(PA.grpl(us, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), ST.GOk{vm}), sk, i, kb, rows, B, bp, vm, PA.CW{rows2, B2, bp2, dd, us})):
  (hnd, hci) = hq
  step.w2(sk, i, kb, rows, B, bp, vm, rows2, B2, bp2, dd, us, hi, hdo, hnd, hci, hnr, hK, hA, hdrv, hD)

def step.w3(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +hi: PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}), hcw: (DH.DropsOk(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, SV.drops(dd)) & (DH.DropsNd(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, dd) & CW.CWInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), PA.CW{rows2, B2, bp2, dd, us}))), hnr: SV.NoRefute2(sk, SV.reds(DPS.classes2(sk)), i),
  +hK: {SV.class_at(DPS.classes2(sk), i) == PA.PO.k(PA.one.g(PA.grpl(us, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), ST.GOk{vm}), sk, i, kb, rows, B, bp, vm, PA.CW{rows2, B2, bp2, dd, us})) : SV.Class}, +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hdrv: {SV.driving(sk, i) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), DPS.classes2(sk), 0n) == True{} : Bool})
  -> StepRes2(sk, i, PA.one.g(PA.grpl(us, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), ST.GOk{vm}), sk, i, kb, rows, B, bp, vm, PA.CW{rows2, B2, bp2, dd, us})):
  (hdo, hq) = hcw
  step.w4(sk, i, kb, rows, B, bp, vm, rows2, B2, bp2, dd, us, hi, hdo, hq, hnr, hK, hA, hdrv, hD)

def step.w(w: PA.CW, +sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +hi: PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}),
  hcw: (DH.DropsOk(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, SV.drops(CW.cw.ds(w))) & (DH.DropsNd(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, CW.cw.ds(w)) & CW.CWInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, bp, SV.neqs(SK.Sketch.eqs(sk)), w))), hnr: SV.NoRefute2(sk, SV.reds(DPS.classes2(sk)), i),
  +hK: {SV.class_at(DPS.classes2(sk), i) == PA.PO.k(PA.one.w(w, sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm)) : SV.Class}, +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hdrv: {SV.driving(sk, i) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), DPS.classes2(sk), 0n) == True{} : Bool}) -> StepRes2(sk, i, PA.one.w(w, sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm)):
  match w:
    case PA.CW{+rows2, +B2, +bp2, +dd, +us}:
      step.w3(sk, i, kb, rows, B, bp, vm, rows2, B2, bp2, dd, us, hi, hcw, hnr, hK, hA, hdrv, hD)


def step.c(b: Bool, +sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +pc: List<&2, SV.Class>, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, kb), SV.eqs_of(sk, Con{i, kb}), DCF.tv(sk), W),
  +eb: {DCF.refutable2(sk, i, kb, SV.eqs_of(sk, Con{i, kb})) == b : Bool},
  +hi: PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}), +hK: {SV.class_at(DPS.classes2(sk), i) == PA.PO.k(DPS.one2.c(DCF.refutable2(sk, i, kb, SV.eqs_of(sk, Con{i, kb})), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm, pc, SV.eqs_of(sk, Con{i, kb}), W)) : SV.Class}, +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hdrv: {SV.driving(sk, i) == True{} : Bool},
  +hD: {CL.downs(SV.owners(sk), DPS.classes2(sk), 0n) == True{} : Bool}, +hpc: {ccat(pc, CL.cdrop(i, DPS.classes2(sk))) == DPS.classes2(sk) : List<&2, SV.Class>}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> StepRes2(sk, i, DPS.one2.c(DCF.refutable2(sk, i, kb, SV.eqs_of(sk, Con{i, kb})), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm, pc, SV.eqs_of(sk, Con{i, kb}), W)):
  match b:
    case True{}:
      %Equal.sym(Bool, DCF.refutable2(sk, i, kb, SV.eqs_of(sk, Con{i, kb})), True{}, eb) : StepRes2(sk, i, DPS.one2.c(_, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm, pc, SV.eqs_of(sk, Con{i, kb}), W))
      step.conf2(sk, i, kb, rows, B, bp, vm, hi, eb,
        (%eb : {SV.class_at(DPS.classes2(sk), i) == PA.PO.k(DPS.one2.c(_, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm, pc, SV.eqs_of(sk, Con{i, kb}), W)) : SV.Class}
          hK), hcov, hwf)
    case False{}:
      %Equal.sym(Bool, DCF.refutable2(sk, i, kb, SV.eqs_of(sk, Con{i, kb})), False{}, eb) : StepRes2(sk, i, DPS.one2.c(_, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm, pc, SV.eqs_of(sk, Con{i, kb}), W))
      +hkb = PP.pinv_kb(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi)
      step.w(DPS.cwalk2(SK.Sketch.eqs(sk), SV.owners(sk), i, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), kb, sk, pc, True{}, 0n), SV.eqs_of(sk, Con{i, kb}), W), sk, i, kb, rows, B, bp, vm, hi,
        DCW.cw2_final(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, SV.facts.go(SK.Sketch.eqs(sk), SV.owners(sk), kb, sk, pc, True{}, 0n), SV.eqs_of(sk, Con{i, kb}), hf0_of(sk, i, kb, pc, hkb, kb_below(sk, i, kb, PP.pinv_kbp(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi)), hD, hpc), hcx_of(sk, i, kb, hkb), W, (%hkb : DW.WInv(SV.ents(sk), SV.rfacts(sk, _), SV.eqs_of(sk, Con{i, kb}), DCF.tv(sk), W)
          hw), rows, B, bp,
          PP.pib_rinv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm, PP.pinv_b(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi)), PP.pinv_rlen(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi), PP.pinv_B(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi), PP.pinv_p(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi),
          PP.pib_bpb(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm, PP.pinv_b(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi)), PP.pib_pre(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, rows, B, bp, vm, PP.pinv_b(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi)), hcov, hwf),
        nr2_of(sk, i, kb, hkb, eb, hcov, hwf),
        (%eb : {SV.class_at(DPS.classes2(sk), i) == PA.PO.k(DPS.one2.c(_, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm, pc, SV.eqs_of(sk, Con{i, kb}), W)) : SV.Class}
          hK), hA, hdrv, hD)


# c's facts extend the kept ones'
def hr_of(+sk: SK.Sketch, +kb: List<&2, Nat>, +i: Nat, +hb: {SV.below(kb, i) == True{} : Bool}) -> MP.Pre(SV.rfacts(sk, kb), SV.rfacts(sk, Con{i, kb})):
  %Equal.sym(List<&2, DR.Fact>, SV.rfacts(sk, Con{i, kb}), SV.fcat(SV.rfacts(sk, kb), SV.rfacts(sk, Con{i, Nil{}})), DPM.rfacts_split(sk, kb, i, hb)) : MP.Pre(SV.rfacts(sk, kb), _)
  MP.pre_cat(SV.rfacts(sk, kb), SV.rfacts(sk, kb), SV.rfacts(sk, Con{i, Nil{}}), MP.pre_refl(SV.rfacts(sk, kb)))

# a driving constraint, W at its context: the call on c's facts from W
# decides the refutation as the closure from the start does
def hon.dk(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +pc: List<&2, SV.Class>, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, kb), SV.eqs_of(sk, Con{i, kb}), DCF.tv(sk), W),
  +hi: PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}), +hK: {SV.class_at(DPS.classes2(sk), i) == PA.PO.k(DPS.one2.c(DCF.refutable2.o(sk, i, kb, DC.FO.o(DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, kb}), DCF.tv(sk), W))), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm, pc, SV.eqs_of(sk, Con{i, kb}), W)) : SV.Class},
  +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hdrv: {SV.driving(sk, i) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), DPS.classes2(sk), 0n) == True{} : Bool}, +hpc: {ccat(pc, CL.cdrop(i, DPS.classes2(sk))) == DPS.classes2(sk) : List<&2, SV.Class>}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> StepRes2(sk, i, DPS.one2.c(DCF.refutable2.o(sk, i, kb, DC.FO.o(DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, kb}), DCF.tv(sk), W))), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm, pc, SV.eqs_of(sk, Con{i, kb}), W)):
  +ro = DCP.ro_eq(sk, i, kb, SV.eqs_of(sk, Con{i, kb}), DC.FO.o(DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, kb}), DCF.tv(sk), W)), DW.wcall_ex(SV.ents(sk), SV.rfacts(sk, kb), SV.rfacts(sk, Con{i, kb}), SV.eqs_of(sk, Con{i, kb}), DCF.tv(sk), W, hw,
    hr_of(sk, kb, i, kb_below(sk, i, kb, PP.pinv_kbp(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi))), BRG.zb_tv(sk, hcov), BRG.fb_rf(sk, Con{i, kb}, hcov, hwf)), hcov, hwf)
  %Equal.sym(Bool, DCF.refutable2.o(sk, i, kb, DC.FO.o(DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, kb}), DCF.tv(sk), W))), DCF.refutable2(sk, i, kb, SV.eqs_of(sk, Con{i, kb})), ro) : StepRes2(sk, i, DPS.one2.c(_, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm, pc, SV.eqs_of(sk, Con{i, kb}), W))
  step.c(DCF.refutable2(sk, i, kb, SV.eqs_of(sk, Con{i, kb})), sk, i, kb, rows, B, bp, vm, pc, W, hw, {==}, hi,
    (%ro : {SV.class_at(DPS.classes2(sk), i) == PA.PO.k(DPS.one2.c(_, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, kb, rows, B, bp, vm, pc, SV.eqs_of(sk, Con{i, kb}), W)) : SV.Class}
      hK), hA, hdrv, hD, hpc, hcov, hwf)

# a driving constraint at i: its class and the next state
def hon.d(st: PA.PS, +sk: SK.Sketch, +i: Nat, +pc: List<&2, SV.Class>, +W: DC.WK, +cw: List<&2, E.QExpr>, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, DPS.pkb(st)), cw, DCF.tv(sk), W), +hi: PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, st),
  +hK: {SV.class_at(DPS.classes2(sk), i) == PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))) : SV.Class}, +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hdrv: {SV.driving(sk, i) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), DPS.classes2(sk), 0n) == True{} : Bool}, +hpc: {ccat(pc, CL.cdrop(i, DPS.classes2(sk))) == DPS.classes2(sk) : List<&2, SV.Class>}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool})
  -> StepRes2(sk, i, DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))):
  match st:
    case PA.PS{+kb, +rows, +B, +bp, +vm}:
      hon.dk(sk, i, kb, rows, B, bp, vm, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, kb}), DC.SP{Nil{}, Nil{}}), W), DW.wk_at_ok(SV.ents(sk), SV.rfacts(sk, kb), cw, SV.eqs_of(sk, Con{i, kb}), DCF.tv(sk), W, hw, BRG.zb_tv(sk, hcov)),
        hi, hK, hA, hdrv, hD, hpc, hcov, hwf)

# The state kept across calls
# ---------------------------
# After a driving constraint the pass keeps W at c's context when c is
# red (kb is unchanged), else the fixpoint of c's call, if it ended at
# one: valid for the facts of kb with c.


def wn.b(b: Bool, +sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +W: DC.WK, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, kb), SV.eqs_of(sk, Con{i, kb}), DCF.tv(sk), W), +hbl: {SV.below(kb, i) == True{} : Bool}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool})
  -> DW.WInv(SV.ents(sk), SV.rfacts(sk, DPM.kbn(b, kb, i)), SV.eqs_of(sk, Con{i, kb}), DCF.tv(sk), DPS.wnext(b, W, DC.wk.next(DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, kb}), DCF.tv(sk), W), SV.rfacts(sk, Con{i, kb}), W))):
  match b:
    case True{}:
      hw
    case False{}:
      %Equal.sym(List<&2, DR.Fact>, SV.rfacts(sk, CO.lsnoc(kb, i)), SV.rfacts(sk, Con{i, kb}), DPM.facts_snoc(SK.Sketch.eqs(sk), SV.owners(sk), kb, i, sk, Nil{}, False{}, 0n))
        : DW.WInv(SV.ents(sk), _, SV.eqs_of(sk, Con{i, kb}), DCF.tv(sk), DC.wk.next(DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, kb}), DCF.tv(sk), W), SV.rfacts(sk, Con{i, kb}), W))
      DW.wnext_ok(SV.ents(sk), SV.rfacts(sk, kb), SV.rfacts(sk, Con{i, kb}), SV.rfacts(sk, Con{i, kb}), SV.eqs_of(sk, Con{i, kb}), DCF.tv(sk), W, hw, hr_of(sk, kb, i, hbl), hr_of(sk, kb, i, hbl),
        MP.pre_refl(SV.rfacts(sk, Con{i, kb})), BRG.zb_tv(sk, hcov), BRG.fb_rf(sk, Con{i, kb}, hcov, hwf))

def wn_ok(+st: PA.PS, +sk: SK.Sketch, +i: Nat, +pc: List<&2, SV.Class>, +W: DC.WK, +cw: List<&2, E.QExpr>, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, DPS.pkb(st)), cw, DCF.tv(sk), W), +hbl: {SV.below(DPS.pkb(st), i) == True{} : Bool}, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool})
  -> DW.WInv(SV.ents(sk), SV.rfacts(sk, DPS.pkb(PA.PO.st(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))))), SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DPS.wnext(SV.is_red(PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wk.next(DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))):
  %Equal.sym(List<&2, Nat>, DPS.pkb(PA.PO.st(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DPM.kbn(SV.is_red(PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DPS.pkb(st), i), DPM.one2_kb(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))) : DW.WInv(SV.ents(sk), SV.rfacts(sk, _), SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DPS.wnext(SV.is_red(PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wk.next(DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))
  wn.b(SV.is_red(PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), sk, i, DPS.pkb(st), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DW.wk_at_ok(SV.ents(sk), SV.rfacts(sk, DPS.pkb(st)), cw, SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), W, hw, BRG.zb_tv(sk, hcov)), hbl, hcov, hwf)

def bl_of(st: PA.PS, +sk: SK.Sketch, +i: Nat, +hi: PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, st)) -> {SV.below(DPS.pkb(st), i) == True{} : Bool}:
  match st:
    case PA.PS{+kb, +rows, +B, +bp, +vm}:
      kb_below(sk, i, kb, PP.pinv_kbp(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, PA.PS{kb, rows, B, bp, vm}, hi))

# no facts yet
def hw0(+sk: SK.Sketch, +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}) -> DW.WInv(SV.ents(sk), SV.rfacts(sk, DPS.pkb(PA.start(PA.nvars(sk)))), Nil{}, DCF.tv(sk), DC.wk0(SV.ents(sk), DCF.tv(sk), DC.SP{Nil{}, Nil{}})):
  (Nil{}, (Unit{}, DW.wk0_ok(SV.ents(sk), Nil{}, DCF.tv(sk), BRG.zb_tv(sk, hcov))))

# The pass is honest
# ------------------

def fate_of(+sk: SK.Sketch, +i: Nat, +K: SV.Class, +hK: {SV.class_at(DPS.classes2(sk), i) == K : SV.Class}, +hdr: {SV.driven(sk, i) == False{} : Bool}, f: DH.Fate.driving(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, K)) -> DH.Fate(sk, DPS.classes2(sk), i):
  (%Equal.sym(Bool, SV.driven(sk, i), False{}, hdr) : DH.Fate.pick(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, _, SV.class_at(DPS.classes2(sk), i))
    (%Equal.sym(SV.Class, SV.class_at(DPS.classes2(sk), i), K, hK) : DH.Fate.pick(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, False{}, _)
      f))

def fate_dr(+sk: SK.Sketch, +i: Nat, +hK: {SV.class_at(DPS.classes2(sk), i) == SV.Kept{Nil{}} : SV.Class}, +hdr: {SV.driven(sk, i) == True{} : Bool}) -> DH.Fate(sk, DPS.classes2(sk), i):
  (%Equal.sym(Bool, SV.driven(sk, i), True{}, hdr) : DH.Fate.pick(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, _, SV.class_at(DPS.classes2(sk), i))
    (%Equal.sym(SV.Class, SV.class_at(DPS.classes2(sk), i), SV.Kept{Nil{}}, hK) : DH.Fate.pick(sk, DPS.classes2(sk), SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, True{}, _)
      {==}))

def hon.con(+sk: SK.Sketch, +i: Nat, +st: PA.PS, +pc: List<&2, SV.Class>, +W: DC.WK, +t: List<&2, SK.Rec>, +hK: {SV.class_at(DPS.classes2(sk), i) == PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))) : SV.Class}, +hdr: {SV.driven(sk, i) == False{} : Bool}, sr: StepRes2(sk, i, DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))),
  ih: PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), 1n+i, PA.PO.st(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))) -> DH.Honest.go(sk, DPS.classes2(sk), SV.clen(t), 1n+i)) -> DH.Honest.go(sk, DPS.classes2(sk), 1n+SV.clen(t), i):
  (f1, inv1) = sr
  (fate_of(sk, i, PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))), hK, hdr, f1), ih(inv1))


# from position i on, given the classes from i are the pass's from there
# and the classes so far followed by them are the final ones
def hon(rs: List<&2, SK.Rec>, +sk: SK.Sketch, +i: Nat, +st: PA.PS, +pc: List<&2, SV.Class>, +W: DC.WK, +cw: List<&2, E.QExpr>, +hw: DW.WInv(SV.ents(sk), SV.rfacts(sk, DPS.pkb(st)), cw, DCF.tv(sk), W),
  +hd: {KB.rdrop(i, PA.recs(sk)) == rs : List<&2, SK.Rec>}, +hc: {CL.cdrop(i, DPS.classes2(sk)) == DPS.pass2(rs, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, W) : List<&2, SV.Class>}, +hpc: {ccat(pc, CL.cdrop(i, DPS.classes2(sk))) == DPS.classes2(sk) : List<&2, SV.Class>},
  +hA: {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}, +hD: {CL.downs(SV.owners(sk), DPS.classes2(sk), 0n) == True{} : Bool}, +hi: PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), i, st), +hcov: {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> DH.Honest.go(sk, DPS.classes2(sk), SV.clen(rs), i):
  match rs:
    case Nil{}:
      Unit{}
    case Con{SK.Rec{+id, True{}, +k}, +t}:
      +hdr = PP.drv_at(sk, i, SK.Rec{id, True{}, k}, t, hd)
      (fate_dr(sk, i, CL.ca_of(DPS.classes2(sk), i, SV.Kept{Nil{}}, DPS.pass2(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, st, DPS.csnoc(pc, SV.Kept{Nil{}}), W), hc), hdr),
        hon(t, sk, 1n+i, st, DPS.csnoc(pc, SV.Kept{Nil{}}), W, cw, hw, KB.rdrop_step(i, PA.recs(sk), SK.Rec{id, True{}, k}, t, hd), CL.cdrop_step(DPS.classes2(sk), i, SV.Kept{Nil{}}, DPS.pass2(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, st, DPS.csnoc(pc, SV.Kept{Nil{}}), W), hc),
          hpc_step(pc, SV.Kept{Nil{}}, DPS.pass2(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, st, DPS.csnoc(pc, SV.Kept{Nil{}}), W), i, DPS.classes2(sk), hc, hpc), hA, hD,
          step_same(sk, i, st, hi, SP.zc_noc(SV.owners(sk), i, SV.reds(DPS.classes2(sk)), PP.noc_owners(sk, i, hdr)), PP.dcond_dr(sk, SV.reds(DPS.classes2(sk)), i, hdr)), hcov, hwf))
    case Con{SK.Rec{+id, False{}, +k}, +t}:
      +hK = CL.ca_of(DPS.classes2(sk), i, PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))), DPS.pass2(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, PA.PO.st(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))), DPS.csnoc(pc, PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DPS.wnext(SV.is_red(PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wk.next(DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))), hc)
      hon.con(sk, i, st, pc, W, t, hK, PP.drv_at(sk, i, SK.Rec{id, False{}, k}, t, hd), hon.d(st, sk, i, pc, W, cw, hw, hi, hK, hA, PP.driving_at(sk, i, id, k, t, hd), hD, hpc, hcov, hwf),
        h2 => hon(t, sk, 1n+i, PA.PO.st(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))), DPS.csnoc(pc, PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DPS.wnext(SV.is_red(PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wk.next(DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))), SV.eqs_of(sk, Con{i, DPS.pkb(st)}), wn_ok(st, sk, i, pc, W, cw, hw, bl_of(st, sk, i, hi), hcov, hwf), KB.rdrop_step(i, PA.recs(sk), SK.Rec{id, False{}, k}, t, hd), CL.cdrop_step(DPS.classes2(sk), i, PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))), DPS.pass2(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, PA.PO.st(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))), DPS.csnoc(pc, PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DPS.wnext(SV.is_red(PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wk.next(DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))), hc),
          hpc_step(pc, PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))), DPS.pass2(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, PA.PO.st(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))), DPS.csnoc(pc, PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DPS.wnext(SV.is_red(PA.PO.k(DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st, pc, DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W))))), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W), DC.wk.next(DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)))), i, DPS.classes2(sk), hc, hpc), hA, hD, h2, hcov, hwf))

def pinv0(+sk: SK.Sketch) -> PP.PInv(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), 0n, PA.start(PA.nvars(sk))):
  (PP.pib_mk(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), 0n, Nil{}, Nil{}, Nil{}, ST.nones(PA.nvars(sk)), {==},
      (%Equal.sym(List<&2, Nat>, ST.somes(ST.nones(PA.nvars(sk))), Nil{}, RP.somes_nones(PA.nvars(sk))) : {SV.distinct(_) == True{} : Bool}
        {==}),
      (%Equal.sym(Nat, L.mlen(ST.nones(PA.nvars(sk))), PA.nvars(sk), RP.mlen_nones(PA.nvars(sk))) : {SV.eq(_, PA.nvars(sk)) == True{} : Bool}
        L.eq_refl(PA.nvars(sk))),
      MX.valid_nones(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk), 0n),
      (%Equal.sym(List<&2, Nat>, ST.somes(ST.nones(PA.nvars(sk))), Nil{}, RP.somes_nones(PA.nvars(sk))) : {L.subl(_, Nil{}) == True{} : Bool}
        {==}),
      {==}, {==}, {==}, {==}),
    (Equal.sym(List<&2, Nat>, SV.kept_before(sk, SV.reds(DPS.classes2(sk)), 0n), Nil{}, KB.kb_zero(sk, SV.reds(DPS.classes2(sk)))),
    (KB.kbp_zero(sk, SV.reds(DPS.classes2(sk))),
    ({==},
    (Equal.sym(List<&2, E.QExpr>, SV.presolved(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)), 0n), Nil{}, SP.presolved_zero(sk, SV.reds(DPS.classes2(sk)), SV.dropped(DPS.classes2(sk)))),
      {==})))))

def hcov_of(+sk: SK.Sketch, +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}) -> {BX.Sketch.within(sk, PA.nvars(sk)) == True{} : Bool}:
  (%Equal.sym(Nat, PA.nvars(sk), SO.nvars(sk), PP.nv_eq(sk)) : {BX.Sketch.within(sk, _) == True{} : Bool}
    cov)

def adjb2_of(+sk: SK.Sketch, +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}, +hwf: {WF.wf_dec(sk) == True{} : Bool}) -> {D.adjb(PA.dadjs(SK.Sketch.eqs(sk)), PA.nvars(sk)) == True{} : Bool}:
  GM.adjb_dadjs(SK.Sketch.eqs(sk), PA.nvars(sk), (%Equal.sym(Nat, PA.nvars(sk), SO.nvars(sk), PP.nv_eq(sk)) : {D.adjb(ST.adj(SK.Sketch.eqs(sk)), _) == True{} : Bool}
    CV.cov(sk, SO.nvars(sk), cov, hwf)))

# classes2 has a class per constraint
def clsn_c2(+sk: SK.Sketch) -> {SV.clsn(DPS.classes2(sk)) == SV.clen(PA.recs(sk)) : Nat}:
  clsn_pass2(PA.recs(sk), sk, 0n, PA.start(PA.nvars(sk)), Nil{}, DC.wk0(SV.ents(sk), DCF.tv(sk), DC.SP{Nil{}, Nil{}}))

# the pass with the direction layer is honest (the extended Honest)
def pass2_honest(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +cov: {BX.Sketch.within(sk, SO.nvars(sk)) == True{} : Bool}) -> DH.Honest(sk, DPS.classes2(sk)):
  +hwf = WC.wf_dec_ok(sk, w)
  (Equal.trans(Nat, SV.clsn(DPS.classes2(sk)), SV.clen(PA.recs(sk)), SV.ncons(sk), clsn_c2(sk), Equal.sym(Nat, SV.ncons(sk), SV.clen(PA.recs(sk)), PP.ncons_recs(sk))),
    (%Equal.sym(Nat, SV.ncons(sk), SV.clen(PA.recs(sk)), PP.ncons_recs(sk)) : DH.Honest.go(sk, DPS.classes2(sk), _, 0n)
      hon(PA.recs(sk), sk, 0n, PA.start(PA.nvars(sk)), Nil{}, DC.wk0(SV.ents(sk), DCF.tv(sk), DC.SP{Nil{}, Nil{}}), Nil{}, hw0(sk, hcov_of(sk, cov)), {==}, {==}, {==}, adjb2_of(sk, cov, hwf), classes2_down(sk), pinv0(sk), hcov_of(sk, cov), hwf)))
