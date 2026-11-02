# bend-cad: the single pass with the direction layer (PLAN-sk13b B4.4,
# B4.5). The constraints are walked once, in order, as in lib/pass.bend;
# each driving constraint c gets the honest class of the extended Honest
# (spec/_draft13b.bend) given the classes before it:
# - Conflict, if c with the kept constraints before it refutes at degree 0
#   or by directions (lib/dconflict.bend), with the generalized deletion
#   filter's support and its nd;
# - otherwise c's equations are walked in order: each is dropped at degree
#   0 (a combination of the basis, as now), else dropped by directions
#   when the closure of the facts it may read holds it (or explodes),
#   with that derivation's nd, else it joins the basis;
# - then Over, Kept and Amber as in lib/pass.bend.
# The facts an equation reads: every equation of the kept constraints
# before c, with its drop's nd (read from the classes so far), and c's own
# earlier equations not dropped; the context is c's (every equation of c
# and of the kept constraints before it).
#
# Untrusted in the sense of the rest of lib/: its properties are proven,
# nothing about it is assumed.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/dir.bend as DR
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./conflict.bend as CO
import ./struct.bend as ST
import ./pass.bend as PA
import ./dclose.bend as DC
import ./dconflict.bend as DCF

# The closure's decision for one equation
# ---------------------------------------
# Some derivation of e (by its statement m), or none: a fixpoint that
# holds e gives its derivation, an explosion derives every equation

def ddec.h(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +e: E.QExpr, +m: Maybe<&2, DR.DStat>) -> Maybe<&2, DR.Der>:
  match b:
    case True{}:
      Some{DC.hold.der(es, fs, t, s, e, m)}
    case False{}:
      None{}

def ddec.o(o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +e: E.QExpr, +m: Maybe<&2, DR.DStat>) -> Maybe<&2, DR.Der>:
  match o:
    case DC.OStep{s}:
      None{}
    case DC.OFix{+s}:
      ddec.h(DC.holds(es, fs, t, s, e, m), es, fs, t, s, e, m)
    case DC.OOne{+d}:
      Some{DC.expl.der(DC.OOne{d}, es, e)}
    case DC.OVoid{+g, +dr, +di}:
      Some{DC.expl.der(DC.OVoid{g, dr, di}, es, e)}

# the decision for e from the run warm-started at W on the facts fs
def ddec(+sk: SK.Sketch, +fs: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +e: E.QExpr, +m: Maybe<&2, DR.DStat>, +W: DC.WK) -> Maybe<&2, DR.Der>:
  ddec.o(DC.FO.o(DC.wcall(SV.ents(sk), fs, DCF.tv(sk), W)), SV.ents(sk), fs, DCF.tv(sk), e, m)

# A constraint's equations
# ------------------------
# As lib/pass.bend's cwalk, over the same state (PA.CW), with the facts of
# the kept constraints before c (F0), c's context (cx) and the run's state
# kept across calls (W, lib/dclose.bend WK) fixed: each equation's call
# starts from W, given the facts past its own.

def cw2.dir(m: Maybe<&2, DR.Der>, +k: Nat, +e: E.QExpr, +r: EL.Res, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, ds: List<&2, SV.Drop>, us: List<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>) -> PA.CW:
  match m:
    case Some{+der}:
      PA.CW{rows, B, bp, Con{SV.Drop{k, DR.nd(es, fs, der), SV.WDer{der}}, ds}, us}
    case None{}:
      PA.CW{EL.rsnoc(rows, EL.row_of(r)), EP.qsnoc(B, e), CO.lsnoc(bp, k), ds, CO.lsnoc(us, k)}

# the facts equation k of c reads
def fk(+sk: SK.Sketch, +c: Nat, +F0: List<&2, DR.Fact>, +ds: List<&2, SV.Drop>, +k: Nat) -> List<&2, DR.Fact>:
  SV.fcat(F0, SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, SV.drops(ds), k, 0n))

# c's statement
def cstat(+sk: SK.Sketch, +c: Nat) -> Maybe<&2, DR.DStat>:
  SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))

def cw2.pick(b: Bool, +k: Nat, +e: E.QExpr, +r: EL.Res, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, us: List<&2, Nat>,
  +sk: SK.Sketch, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +W: DC.WK) -> PA.CW:
  match b:
    case True{}:
      PA.CW{rows, B, bp, Con{PA.drop_of(k, r, e, B, bp), ds}, us}
    case False{}:
      +fs = fk(sk, c, F0, ds, k)
      cw2.dir(ddec(sk, fs, cx, e, cstat(sk, c), W), k, e, r, rows, B, bp, ds, us, SV.ents(sk), fs)

def cw2.res(+k: Nat, +e: E.QExpr, st: PA.CW, +sk: SK.Sketch, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +W: DC.WK) -> PA.CW:
  match st:
    case PA.CW{+rows, +B, +bp, +ds, us}:
      +r = EL.resid(rows, e)
      cw2.pick(EP.isnil(EP.resp(r)), k, e, r, rows, B, bp, ds, us, sk, c, F0, cx, W)

def cw2.at(o: Bool, +k: Nat, +e: E.QExpr, st: PA.CW, +sk: SK.Sketch, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +W: DC.WK) -> PA.CW:
  match o:
    case True{}:
      cw2.res(k, e, st, sk, c, F0, cx, W)
    case False{}:
      st

# the equations es from position k (own the owners)
def cwalk2(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +c: Nat, +k: Nat, st: PA.CW, +sk: SK.Sketch, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +W: DC.WK) -> PA.CW:
  match es:
    case Nil{}:
      st
    case Con{e, t}:
      cwalk2(t, own, c, 1n+k, cw2.at(SV.eq(SV.nth(own, k), c), k, e, st, sk, c, F0, cx, W), sk, F0, cx, W)

# One constraint
# --------------
# The state is lib/pass.bend's PS, with the classes so far beside it.

def one2.c(b: Bool, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +c: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>,
  +cls: List<&2, SV.Class>, +cx: List<&2, E.QExpr>, +W: DC.WK) -> PA.PO:
  match b:
    case True{}:
      PA.PO{SV.Conflict{DCF.support2(sk, c, cx, kb), DCF.cnd(sk, c, DCF.support2(sk, c, cx, kb), cx)}, PA.PS{kb, rows, B, bp, vm}}
    case False{}:
      PA.one.w(cwalk2(es, own, c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, SV.facts.go(es, own, kb, sk, cls, True{}, 0n), cx, W), sk, adj, f, c, kb, rows, B, bp, vm)

# the driving constraint at position c, the classes before it cls, from W
# (at c's context) and foA, the call on c's facts with the kept ones'
def one2(+es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +c: Nat, st: PA.PS, +cls: List<&2, SV.Class>, +W: DC.WK, foA: DC.FO) -> PA.PO:
  match st:
    case PA.PS{+kb, +rows, +B, +bp, +vm}:
      +cx = SV.eqs_of(sk, Con{c, kb})
      one2.c(DCF.refutable2.o(sk, c, kb, DC.FO.o(foA)), es, own, sk, adj, f, c, kb, rows, B, bp, vm, cls, cx, W)

# The pass
# --------
# W is the state kept for the kept constraints' facts so far: at each
# driving constraint it is taken to c's context (kept if the segments
# collapse alike there, else the start for no facts), then a fixpoint of
# c's call is kept when c joins the kept constraints.

def csnoc(xs: List<&2, SV.Class>, +y: SV.Class) -> List<&2, SV.Class>:
  match xs:
    case Nil{}:
      Con{y, Nil{}}
    case Con{h, t}:
      Con{h, csnoc(t, y)}

def pkb(st: PA.PS) -> List<&2, Nat>:
  match st:
    case PA.PS{kb, rows, B, bp, vm}:
      kb

def wnext(b: Bool, +W: DC.WK, +W2: DC.WK) -> DC.WK:
  match b:
    case True{}:
      W
    case False{}:
      W2

# the constraints rs from position i, the classes before them cls
def pass2(rs: List<&2, SK.Rec>, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +i: Nat, +st: PA.PS, +cls: List<&2, SV.Class>, +W: DC.WK) -> List<&2, SV.Class>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{SK.Rec{id, True{}, k}, t}:
      Con{SV.Kept{Nil{}}, pass2(t, es, own, sk, adj, f, 1n+i, st, csnoc(cls, SV.Kept{Nil{}}), W)}
    case Con{SK.Rec{id, False{}, k}, t}:
      +Wc = DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, pkb(st)}), DC.SP{Nil{}, Nil{}}), W)
      +foA = DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, pkb(st)}), DCF.tv(sk), Wc)
      +o = one2(es, own, sk, adj, f, i, st, cls, Wc, foA)
      Con{PA.PO.k(o), pass2(t, es, own, sk, adj, f, 1n+i, PA.PO.st(o), csnoc(cls, PA.PO.k(o)), wnext(SV.is_red(PA.PO.k(o)), Wc, DC.wk.next(foA, SV.rfacts(sk, Con{i, pkb(st)}), Wc)))}

# every constraint's class
def classes2(+sk: SK.Sketch) -> List<&2, SV.Class>:
  pass2(PA.recs(sk), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 0n, PA.start(PA.nvars(sk)), Nil{}, DC.wk0(SV.ents(sk), DCF.tv(sk), DC.SP{Nil{}, Nil{}}))

# The state the pass ends with (the same walk as pass2): its basis is the
# system solved
def pass2_st(rs: List<&2, SK.Rec>, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +i: Nat, +st: PA.PS, +cls: List<&2, SV.Class>, +W: DC.WK) -> PA.PS:
  match rs:
    case Nil{}:
      st
    case Con{SK.Rec{id, True{}, k}, t}:
      pass2_st(t, es, own, sk, adj, f, 1n+i, st, csnoc(cls, SV.Kept{Nil{}}), W)
    case Con{SK.Rec{id, False{}, k}, t}:
      +Wc = DC.wk.at(SV.ents(sk), DCF.tv(sk), DC.sp.of(SV.eqs_of(sk, Con{i, pkb(st)}), DC.SP{Nil{}, Nil{}}), W)
      +foA = DC.wcall(SV.ents(sk), SV.rfacts(sk, Con{i, pkb(st)}), DCF.tv(sk), Wc)
      +o = one2(es, own, sk, adj, f, i, st, cls, Wc, foA)
      pass2_st(t, es, own, sk, adj, f, 1n+i, PA.PO.st(o), csnoc(cls, PA.PO.k(o)), wnext(SV.is_red(PA.PO.k(o)), Wc, DC.wk.next(foA, SV.rfacts(sk, Con{i, pkb(st)}), Wc)))

def final2_st(+sk: SK.Sketch) -> PA.PS:
  pass2_st(PA.recs(sk), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 0n, PA.start(PA.nvars(sk)), Nil{}, DC.wk0(SV.ents(sk), DCF.tv(sk), DC.SP{Nil{}, Nil{}}))

# The structure: the system solved, its pins and its blocks, read off the
# state the pass ends with exactly as lib/pass.bend's solved_pos, pins and
# skel are off final_st
def solved_pos2(+sk: SK.Sketch) -> List<&2, Nat>:
  PA.PS.bp(final2_st(sk))

def pins2(+sk: SK.Sketch) -> List<&2, Nat>:
  ST.KD.red(PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), solved_pos2(sk)))

def skel2(+sk: SK.Sketch) -> ST.Skel:
  ST.renum(ST.skel.kd(ST.adj(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), solved_pos2(sk), PA.kvs(PA.dadjs(SK.Sketch.eqs(sk)), ST.len.q(SK.Sketch.eqs(sk)), PA.nvars(sk), solved_pos2(sk))), solved_pos2(sk))
