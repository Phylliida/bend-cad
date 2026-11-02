# bend-cad: the fast solver over the pass with the direction layer
# (PLAN-sk13b B5.5), beside lib/fast.bend until the switch. lib/fast.bend's
# solver with lib/dsolve.bend's verdict (the nd sides checked in K too) and
# the new pass run once (walk22: its classes and its end state at once).
# With laws relating K to KI.dnum() it returns exactly what the draft
# solver does (lib/dwfastpf.bend: solve_l2_eq).
#
# Untrusted in the sense of the rest of lib/: its properties are proven,
# nothing about it is assumed.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/knum.bend as N
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/dir.bend as DR
import ./karith.bend as KA
import ./plan.bend as PL
import ./struct.bend as ST
import ./solve.bend as SO
import ./pass.bend as PA
import ./pops.bend as PO
import ./gnumer.bend as GN
import ./dclose.bend as DC
import ./dconflict.bend as DCF
import ./dpass.bend as DPS
import ./fast.bend as FS

# The verdict
# -----------

# the live drops' nd segments are long over the box, checked in K
def ndok(~K: N.Num, +sk: SK.Sketch, +x: FS.FOut<K>) -> Bool:
  PL.check_sides(~K, DR.ndsides(SV.ents(sk), SV.live_nd(FS.FOut.cls(K, x))), FS.FOut.gc(K, x), FS.FOut.gr(K, x))

def final2(~K: N.Num, ~W: PO.POps<K>, +sk: SK.Sketch, +g0: List<&2, S.D>, +x: FS.FOut<K>) -> Bool:
  KA.band(ndok(~K, sk, x), FS.final(~K, ~W, sk, g0, x))

# The precision loop
# ------------------

def accept2(~K: N.Num, ~W: PO.POps<K>, m: GN.GPR<K>, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>) -> Bool:
  match m:
    case GN.GPOk{+x}:
      final2(~K, ~W, sk, g0, FS.found(~K, cls, pins, GN.GPOk{x}))
    case GN.GPRetry{}:
      False{}
    case GN.GPStop{}:
      False{}

def ploop2(~K: N.Num, ~W: PO.POps<K>, ps: List<&2, Nat>, ok: Bool, cur: GN.GPR<K>, +sk: SK.Sketch, +g0: List<&2, S.D>, +g0w: N.KVec(~K), +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel) -> FS.FRun<K>:
  match ps ok:
    case Nil{} ok:
      FS.FRun{ok, cur}
    case Con{p, t} True{}:
      FS.FRun{True{}, cur}
    case Con{+p, t} False{}:
      +nx = GN.plan(~K, ~W, es, nv, skel, g0w, p)
      ploop2(~K, ~W, t, accept2(~K, ~W, nx, sk, g0, cls, pins), nx, sk, g0, g0w, cls, pins, es, nv, skel)

def ploop2.start(~K: N.Num, ~W: PO.POps<K>, ps: List<&2, Nat>, +sk: SK.Sketch, +g0: List<&2, S.D>, +g0w: N.KVec(~K), +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel) -> FS.FRun<K>:
  match ps:
    case Nil{}:
      FS.FRun{False{}, GN.GPRetry{}}
    case Con{+p, t}:
      +nx = GN.plan(~K, ~W, es, nv, skel, g0w, p)
      ploop2(~K, ~W, t, accept2(~K, ~W, nx, sk, g0, cls, pins), nx, sk, g0, g0w, cls, pins, es, nv, skel)

# The pass, once
# --------------
# DPS.pass2 gives the classes and DPS.pass2_st the state the same walk
# ends with; walk22 is that walk once, giving both (lib/dwfastpf.bend:
# walk22_cls, walk22_st).

def walk22(rs: List<&2, SK.Rec>, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +i: Nat, +st: PA.PS, +cls: List<&2, SV.Class>, +W: DC.WK) -> FS.PW:
  match rs:
    case Nil{}:
      FS.PW{Nil{}, st}
    case Con{SK.Rec{id, True{}, k}, t}:
      FS.pw.cons(SV.Kept{Nil{}}, walk22(t, es, own, sk, adj, f, 1n+i, st, DPS.csnoc(cls, SV.Kept{Nil{}}), W))
    case Con{SK.Rec{id, False{}, k}, t}:
      +Wc = DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, DPS.pkb(st)}), DC.SP{Nil{}, Nil{}}), W)
      +foA = DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, DPS.pkb(st)}), DCF.tv(sk), Wc)
      +o = DPS.one2(es, own, sk, adj, f, i, st, cls, Wc, foA)
      FS.pw.cons(PA.PO.k(o), walk22(t, es, own, sk, adj, f, 1n+i, PA.PO.st(o), DPS.csnoc(cls, PA.PO.k(o)), DPS.wnext(SV.is_red(PA.PO.k(o)), Wc, DC.wk.next(foA, SV.rfacts(sk, Con{i, DPS.pkb(st)}), Wc))))

# The solver
# ----------

def solve_kv2(~K: N.Num, ~W: PO.POps<K>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +w: Nat, +cls: List<&2, SV.Class>, +sp: List<&2, Nat>, +kv: ST.KD) -> SO.Out:
  FS.answer(~K, ~W, cls, ST.KD.red(kv), ploop2.start(~K, ~W, SO.precisions(l, w), sk, g0, FS.ofdv(~K, ~W, g0), cls, ST.KD.red(kv), SV.solved(sk, SV.reds(cls), SV.dropped(cls)), PA.nvars(sk), ST.renum(ST.skel.kd(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), sp, kv), sp)))

def solve_st2(~K: N.Num, ~W: PO.POps<K>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +w: Nat, +cls: List<&2, SV.Class>, +sp: List<&2, Nat>, +da: List<&2, List<&2, Nat>>) -> SO.Out:
  solve_kv2(~K, ~W, sk, g0, l, w, cls, sp, PA.kvs(da, ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), sp))

def solve_pw2(~K: N.Num, ~W: PO.POps<K>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +w: Nat, +da: List<&2, List<&2, Nat>>, +pw: FS.PW) -> SO.Out:
  solve_st2(~K, ~W, sk, g0, l, w, FS.PW.cls(pw), PA.PS.bp(FS.PW.st(pw)), da)

def solve_da2(~K: N.Num, ~W: PO.POps<K>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +w: Nat, +da: List<&2, List<&2, Nat>>) -> SO.Out:
  solve_pw2(~K, ~W, sk, g0, l, w, da, walk22(PA.recs(sk), SK.Sketch.eqs(sk), SV.owners(sk), sk, da, 1n+PA.nvars(sk), 0n, PA.start(PA.nvars(sk)), Nil{}, DC.wk0(SV.ents(sk), DCF.tv(sk), DC.SP{Nil{}, Nil{}})))

def solve_lw2(~K: N.Num, ~W: PO.POps<K>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +w: Nat) -> SO.Out:
  solve_da2(~K, ~W, sk, g0, l, w, PA.dadjs(SK.Sketch.eqs(sk)))

def solve_l2(~K: N.Num, ~W: PO.POps<K>, +sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat) -> SO.Out:
  solve_lw2(~K, ~W, sk, g0, l, 7n)

# the draft solver at word dyadics, base 2^12 (lib/fast.bend's wk, wo)
def wsolve_l2(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat) -> SO.Out:
  solve_l2(~FS.wk(), ~FS.wo(), sk, g0, l)

def wsolve2(+sk: SK.Sketch, +g0: List<&2, S.D>) -> SO.Out:
  wsolve_l2(sk, g0, 0n)
