# bend-cad: the single pass is honest (PLAN-sk13a S4, law 4). Proofs
# only.
#
# Honest(sk, classes(sk)): each constraint's class is the honest one
# given the final classes' red positions and dropped equations. The pass
# never sees the final lists; its state is related to them below c:
# - kb, its kept constraints, is kept_before(sk, RF, c) (lib/kbpf.bend);
# - B, its basis, is presolved(sk, RF, DF, c) (lib/solvedpf.bend), with
#   echelon rows, positions bp and a valid matching of exactly bp;
# and the final lists are read position by position: c is red exactly when
# its class is, and k is dropped exactly when its owner's class drops it
# (lib/clslpf.bend), which holds because every class drops only its own
# equations (downs, proven first, from the walk alone).
# Then each driving constraint's class follows from its decisions:
# Conflict (lib/prepf.bend), Over by a failed unit (lib/gmpf.bend), Kept
# or Amber by DropsOk (lib/cwpf.bend), the unit's matching and the side
# tests.
#
# Generated from tools/drafts/passpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./nat.bend as LN
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

def absurd(-A: Type, x: Empty) -> A:
  match x:


# Every class drops only its own equations
# ----------------------------------------

def onea_kd(m: Maybe<&2, List<&2, SV.Ref>>, +dd: List<&2, SV.Drop>) -> {SV.kdrops(PA.one.a(m, dd)) == SV.drops(dd) : List<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{rs}:
      {==}

def onek_kd(a: Bool, +sk: SK.Sketch, +kb: List<&2, Nat>, +c: Nat, +dd: List<&2, SV.Drop>) -> {SV.kdrops(PA.one.k(a, sk, kb, c, dd)) == SV.drops(dd) : List<&2, Nat>}:
  match a:
    case True{}:
      onea_kd(PA.srefs(SV.csides(sk, [c]), sk, kb, c, 0n), dd)
    case False{}:
      {==}

def one_down.g(g: ST.GS, +sk: SK.Sketch, +c: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +rows2: List<&2, EL.Row>, +B2: List<&2, E.QExpr>, +bp2: List<&2, Nat>, +dd: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +h: {KB.allo(SV.owners(sk), SV.drops(dd), c) == True{} : Bool}) -> {KB.allo(SV.owners(sk), SV.kdrops(PA.PO.k(PA.one.g(g, sk, c, kb, rows, B, bp, vm, PA.CW{rows2, B2, bp2, dd, us}))), c) == True{} : Bool}:
  match g:
    case ST.GFail{ST.Red{j, s, x}}:
      {==}
    case ST.GOk{vm2}:
      %Equal.sym(List<&2, Nat>, SV.kdrops(PA.one.k(SV.is_amberable(sk, c, SV.drops(dd)), sk, kb, c, dd)), SV.drops(dd), onek_kd(SV.is_amberable(sk, c, SV.drops(dd)), sk, kb, c, dd)) : {KB.allo(SV.owners(sk), _, c) == True{} : Bool}
      h

def one_down.w(w: PA.CW, +sk: SK.Sketch, +c: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +h: {KB.allo(SV.owners(sk), SV.drops(CW.cw.ds(w)), c) == True{} : Bool})
  -> {KB.allo(SV.owners(sk), SV.kdrops(PA.PO.k(PA.one.w(w, sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), c, kb, rows, B, bp, vm))), c) == True{} : Bool}:
  match w:
    case PA.CW{+rows2, +B2, +bp2, +dd, +us}:
      one_down.g(PA.grpl(us, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), ST.GOk{vm}), sk, c, kb, rows, B, bp, vm, rows2, B2, bp2, dd, us, h)

def one_down.c(b: Bool, +sk: SK.Sketch, +c: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +eb: {CO.refutable(sk, c, kb) == b : Bool})
  -> {KB.allo(SV.owners(sk), SV.kdrops(PA.PO.k(PA.one.c(CO.refutable(sk, c, kb), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), c, kb, rows, B, bp, vm))), c) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, CO.refutable(sk, c, kb), True{}, eb) : {KB.allo(SV.owners(sk), SV.kdrops(PA.PO.k(PA.one.c(_, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), c, kb, rows, B, bp, vm))), c) == True{} : Bool}
      {==}
    case False{}:
      %Equal.sym(Bool, CO.refutable(sk, c, kb), False{}, eb) : {KB.allo(SV.owners(sk), SV.kdrops(PA.PO.k(PA.one.c(_, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), c, kb, rows, B, bp, vm))), c) == True{} : Bool}
      one_down.w(PA.cwalk(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}), sk, c, kb, rows, B, bp, vm, CW.cw_own(SK.Sketch.eqs(sk), SV.owners(sk), c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, {==}))

def one_down(st: PA.PS, +sk: SK.Sketch, +c: Nat) -> {KB.allo(SV.owners(sk), SV.kdrops(PA.PO.k(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), c, st))), c) == True{} : Bool}:
  match st:
    case PA.PS{+kb, +rows, +B, +bp, +vm}:
      one_down.c(CO.refutable(sk, c, kb), sk, c, kb, rows, B, bp, vm, {==})

def pass_down(rs: List<&2, SK.Rec>, +sk: SK.Sketch, +i: Nat, +st: PA.PS) -> {CL.downs(SV.owners(sk), PA.pass(rs, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st), i) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{SK.Rec{id, True{}, k}, +t}:
      L.band_i(True{}, CL.downs(SV.owners(sk), PA.pass(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, st), 1n+i), {==}, pass_down(t, sk, 1n+i, st))
    case Con{SK.Rec{id, False{}, k}, +t}:
      L.band_i(KB.allo(SV.owners(sk), SV.kdrops(PA.PO.k(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st))), i), CL.downs(SV.owners(sk), PA.pass(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 1n+i, PA.PO.st(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st))), 1n+i),
        one_down(st, sk, i), pass_down(t, sk, 1n+i, PA.PO.st(PA.one(SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), i, st))))

# the final classes drop only their own equations
def classes_down(+sk: SK.Sketch) -> {CL.downs(SV.owners(sk), PA.classes(sk), 0n) == True{} : Bool}:
  pass_down(PA.recs(sk), sk, 0n, PA.start(PA.nvars(sk)))
