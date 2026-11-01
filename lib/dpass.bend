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

def ddec(+sk: SK.Sketch, +fs: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +e: E.QExpr, +m: Maybe<&2, DR.DStat>) -> Maybe<&2, DR.Der>:
  ddec.o(DCF.dcl(sk, fs, cx), SV.ents(sk), fs, DCF.tv(sk), e, m)

# A direction drop's certificate. Its h is the product of nd's squared
# lengths; its multipliers come from the derivation, composed with the
# dropped facts' certificates (PLAN-sk13b B4.6, not built yet: until then
# the verdict cannot pass a direction drop, and the solver does not run
# this pass).
def dcert(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +der: DR.Der, +nd: List<&2, Nat>) -> SV.Comb:
  SV.Comb{DR.ndh(es, nd), Nil{}}

# A constraint's equations
# ------------------------
# As lib/pass.bend's cwalk, over the same state (PA.CW), with the facts of
# the kept constraints before c (F0) and c's context (cx) fixed.

def cw2.dir(m: Maybe<&2, DR.Der>, +k: Nat, +e: E.QExpr, +r: EL.Res, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, ds: List<&2, SV.Drop>, us: List<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>) -> PA.CW:
  match m:
    case Some{+der}:
      PA.CW{rows, B, bp, Con{SV.Drop{k, DR.nd(es, fs, der), dcert(es, fs, der, DR.nd(es, fs, der))}, ds}, us}
    case None{}:
      PA.CW{EL.rsnoc(rows, EL.row_of(r)), EP.qsnoc(B, e), CO.lsnoc(bp, k), ds, CO.lsnoc(us, k)}

# the facts equation k of c reads
def fk(+sk: SK.Sketch, +c: Nat, +F0: List<&2, DR.Fact>, +ds: List<&2, SV.Drop>, +k: Nat) -> List<&2, DR.Fact>:
  SV.fcat(F0, SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, SV.drops(ds), k, 0n))

# c's statement
def cstat(+sk: SK.Sketch, +c: Nat) -> Maybe<&2, DR.DStat>:
  SV.dstat_of(SV.ents(sk), SV.kind_at(sk, c))

def cw2.pick(b: Bool, +k: Nat, +e: E.QExpr, +r: EL.Res, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, us: List<&2, Nat>,
  +sk: SK.Sketch, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>) -> PA.CW:
  match b:
    case True{}:
      PA.CW{rows, B, bp, Con{PA.drop_of(k, r, e, B, bp), ds}, us}
    case False{}:
      cw2.dir(ddec(sk, fk(sk, c, F0, ds, k), cx, e, cstat(sk, c)), k, e, r, rows, B, bp, ds, us, SV.ents(sk), fk(sk, c, F0, ds, k))

def cw2.res(+k: Nat, +e: E.QExpr, st: PA.CW, +sk: SK.Sketch, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>) -> PA.CW:
  match st:
    case PA.CW{+rows, +B, +bp, +ds, us}:
      +r = EL.resid(rows, e)
      cw2.pick(EP.isnil(EP.resp(r)), k, e, r, rows, B, bp, ds, us, sk, c, F0, cx)

def cw2.at(o: Bool, +k: Nat, +e: E.QExpr, st: PA.CW, +sk: SK.Sketch, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>) -> PA.CW:
  match o:
    case True{}:
      cw2.res(k, e, st, sk, c, F0, cx)
    case False{}:
      st

# the equations es from position k (own the owners)
def cwalk2(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +c: Nat, +k: Nat, st: PA.CW, +sk: SK.Sketch, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>) -> PA.CW:
  match es:
    case Nil{}:
      st
    case Con{e, t}:
      cwalk2(t, own, c, 1n+k, cw2.at(SV.eq(SV.nth(own, k), c), k, e, st, sk, c, F0, cx), sk, F0, cx)

# The walk from a start kept across calls (PLAN-sk13b B4.8): M is K and
# its cache for the facts of the kept constraints before c, which F0
# extends; each equation's call extends M by c's facts it reads
# (lib/dpassmpf.bend: cwalk2.m returns what cwalk2 returns).

def ddec.m(+sk: SK.Sketch, +fs: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +e: E.QExpr, +m: Maybe<&2, DR.DStat>, M: DC.MK) -> Maybe<&2, DR.Der>:
  ddec.o(DCF.dcl.m(sk, fs, cx, M), SV.ents(sk), fs, DCF.tv(sk), e, m)

def cw2.pick.m(b: Bool, +k: Nat, +e: E.QExpr, +r: EL.Res, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, us: List<&2, Nat>,
  +sk: SK.Sketch, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +M: DC.MK) -> PA.CW:
  match b:
    case True{}:
      PA.CW{rows, B, bp, Con{PA.drop_of(k, r, e, B, bp), ds}, us}
    case False{}:
      +O = SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, SV.drops(ds), k, 0n)
      +fs = SV.fcat(F0, O)
      cw2.dir(ddec.m(sk, fs, cx, e, cstat(sk, c), DC.mext.m(O, SV.ents(sk), fs, DCF.tv(sk), M)), k, e, r, rows, B, bp, ds, us, SV.ents(sk), fs)

def cw2.res.m(+k: Nat, +e: E.QExpr, st: PA.CW, +sk: SK.Sketch, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +M: DC.MK) -> PA.CW:
  match st:
    case PA.CW{+rows, +B, +bp, +ds, us}:
      +r = EL.resid(rows, e)
      cw2.pick.m(EP.isnil(EP.resp(r)), k, e, r, rows, B, bp, ds, us, sk, c, F0, cx, M)

def cw2.at.m(o: Bool, +k: Nat, +e: E.QExpr, st: PA.CW, +sk: SK.Sketch, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +M: DC.MK) -> PA.CW:
  match o:
    case True{}:
      cw2.res.m(k, e, st, sk, c, F0, cx, M)
    case False{}:
      st

def cwalk2.m(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +c: Nat, +k: Nat, st: PA.CW, +sk: SK.Sketch, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +M: DC.MK) -> PA.CW:
  match es:
    case Nil{}:
      st
    case Con{e, t}:
      cwalk2.m(t, own, c, 1n+k, cw2.at.m(SV.eq(SV.nth(own, k), c), k, e, st, sk, c, F0, cx, M), sk, F0, cx, M)

# One constraint
# --------------
# The state is lib/pass.bend's PS, with the classes so far beside it.

def one2.c(b: Bool, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +c: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>,
  +cls: List<&2, SV.Class>, +cx: List<&2, E.QExpr>) -> PA.PO:
  match b:
    case True{}:
      PA.PO{SV.Conflict{DCF.support2(sk, c, cx, kb), DCF.cnd(sk, c, DCF.support2(sk, c, cx, kb), cx)}, PA.PS{kb, rows, B, bp, vm}}
    case False{}:
      PA.one.w(cwalk2(es, own, c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, SV.facts.go(es, own, kb, sk, cls, True{}, 0n), cx), sk, adj, f, c, kb, rows, B, bp, vm)

# the driving constraint at position c, the classes before it cls
def one2(+es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +c: Nat, st: PA.PS, +cls: List<&2, SV.Class>) -> PA.PO:
  match st:
    case PA.PS{+kb, +rows, +B, +bp, +vm}:
      +cx = SV.eqs_of(sk, Con{c, kb})
      one2.c(DCF.refutable2(sk, c, kb, cx), es, own, sk, adj, f, c, kb, rows, B, bp, vm, cls, cx)

# one2, from M, the start for the kept constraints before c, and MA, the
# start for c with them
def one2.c.m(b: Bool, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +c: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>,
  +cls: List<&2, SV.Class>, +cx: List<&2, E.QExpr>, +M: DC.MK) -> PA.PO:
  match b:
    case True{}:
      PA.PO{SV.Conflict{DCF.support2(sk, c, cx, kb), DCF.cnd(sk, c, DCF.support2(sk, c, cx, kb), cx)}, PA.PS{kb, rows, B, bp, vm}}
    case False{}:
      PA.one.w(cwalk2.m(es, own, c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, SV.facts.go(es, own, kb, sk, cls, True{}, 0n), cx, M), sk, adj, f, c, kb, rows, B, bp, vm)

def one2.m(+es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +c: Nat, st: PA.PS, +cls: List<&2, SV.Class>, +M: DC.MK, +MA: DC.MK) -> PA.PO:
  match st:
    case PA.PS{+kb, +rows, +B, +bp, +vm}:
      +cx = SV.eqs_of(sk, Con{c, kb})
      one2.c.m(DCF.refutable2.m(sk, c, kb, cx, MA), es, own, sk, adj, f, c, kb, rows, B, bp, vm, cls, cx, M)

# The pass
# --------

def csnoc(xs: List<&2, SV.Class>, +y: SV.Class) -> List<&2, SV.Class>:
  match xs:
    case Nil{}:
      Con{y, Nil{}}
    case Con{h, t}:
      Con{h, csnoc(t, y)}

# the constraints rs from position i, the classes before them cls
def pass2(rs: List<&2, SK.Rec>, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +i: Nat, +st: PA.PS, +cls: List<&2, SV.Class>) -> List<&2, SV.Class>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{SK.Rec{id, True{}, k}, t}:
      Con{SV.Kept{Nil{}}, pass2(t, es, own, sk, adj, f, 1n+i, st, csnoc(cls, SV.Kept{Nil{}}))}
    case Con{SK.Rec{id, False{}, k}, t}:
      +o = one2(es, own, sk, adj, f, i, st, cls)
      Con{PA.PO.k(o), pass2(t, es, own, sk, adj, f, 1n+i, PA.PO.st(o), csnoc(cls, PA.PO.k(o)))}

# The pass from a start kept across calls (PLAN-sk13b B4.8): M is K and
# its cache for the facts of the kept constraints so far; after c it is
# c's start when c is kept, else unchanged (lib/dpassmpf.bend: pass2.m
# returns what pass2 returns).

def pkb(st: PA.PS) -> List<&2, Nat>:
  match st:
    case PA.PS{kb, rows, B, bp, vm}:
      kb

def mnext(b: Bool, +M: DC.MK, +MA: DC.MK) -> DC.MK:
  match b:
    case True{}:
      M
    case False{}:
      MA

def pass2.m(rs: List<&2, SK.Rec>, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +i: Nat, +st: PA.PS, +cls: List<&2, SV.Class>, +M: DC.MK) -> List<&2, SV.Class>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{SK.Rec{id, True{}, k}, t}:
      Con{SV.Kept{Nil{}}, pass2.m(t, es, own, sk, adj, f, 1n+i, st, csnoc(cls, SV.Kept{Nil{}}), M)}
    case Con{SK.Rec{id, False{}, k}, t}:
      +MA = DCF.mstart(sk, i, pkb(st), M)
      +o = one2.m(es, own, sk, adj, f, i, st, cls, M, MA)
      Con{PA.PO.k(o), pass2.m(t, es, own, sk, adj, f, 1n+i, PA.PO.st(o), csnoc(cls, PA.PO.k(o)), mnext(SV.is_red(PA.PO.k(o)), M, MA))}

# the start for no constraints
def m0(+sk: SK.Sketch) -> DC.MK:
  DC.mk0(SV.ents(sk), DCF.tv(sk))

# every constraint's class
def classes2(+sk: SK.Sketch) -> List<&2, SV.Class>:
  pass2.m(PA.recs(sk), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 0n, PA.start(PA.nvars(sk)), Nil{}, m0(sk))

# The state the pass ends with (the same walk as pass2): its basis is the
# system solved
def pass2_st(rs: List<&2, SK.Rec>, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +i: Nat, +st: PA.PS, +cls: List<&2, SV.Class>) -> PA.PS:
  match rs:
    case Nil{}:
      st
    case Con{SK.Rec{id, True{}, k}, t}:
      pass2_st(t, es, own, sk, adj, f, 1n+i, st, csnoc(cls, SV.Kept{Nil{}}))
    case Con{SK.Rec{id, False{}, k}, t}:
      +o = one2(es, own, sk, adj, f, i, st, cls)
      pass2_st(t, es, own, sk, adj, f, 1n+i, PA.PO.st(o), csnoc(cls, PA.PO.k(o)))

def pass2_st.m(rs: List<&2, SK.Rec>, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +i: Nat, +st: PA.PS, +cls: List<&2, SV.Class>, +M: DC.MK) -> PA.PS:
  match rs:
    case Nil{}:
      st
    case Con{SK.Rec{id, True{}, k}, t}:
      pass2_st.m(t, es, own, sk, adj, f, 1n+i, st, csnoc(cls, SV.Kept{Nil{}}), M)
    case Con{SK.Rec{id, False{}, k}, t}:
      +MA = DCF.mstart(sk, i, pkb(st), M)
      +o = one2.m(es, own, sk, adj, f, i, st, cls, M, MA)
      pass2_st.m(t, es, own, sk, adj, f, 1n+i, PA.PO.st(o), csnoc(cls, PA.PO.k(o)), mnext(SV.is_red(PA.PO.k(o)), M, MA))

def final2_st(+sk: SK.Sketch) -> PA.PS:
  pass2_st.m(PA.recs(sk), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 0n, PA.start(PA.nvars(sk)), Nil{}, m0(sk))
