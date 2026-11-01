# bend-cad: the facts the pass's closure calls read, and how kb grows,
# for the state kept across calls (PLAN-sk13b B4.8; lib/dpasspf.bend).
# - The facts: rfacts(sk, c : kb) is rfacts(sk, kb) and then c's own, for
#   kb below c (owners are sorted: rfacts_split); F0, what an equation
#   reads before c's own, agrees with rfacts(sk, kb) and is as long (they
#   differ only in nd: facts_pre, facts_len); rfacts(sk, kb ++ [c]) is
#   rfacts(sk, c : kb) (facts_snoc).
# - After c, c joins kb exactly when its class is not red (one2_kb).
# Proofs only.

import Base
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/dir.bend as DR
import ./struct.bend as ST
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./kspace.bend as KS
import ./conflict.bend as CO
import ./pass.bend as PA
import ./dclose.bend as DC
import ./dconflict.bend as DCF
import ./dpass.bend as DPS
import ./dref.bend as DF
import ./dfastpf.bend as FP
import ./dmemopf.bend as MP
import ./listpf.bend as LI
import ./nat.bend as LN
import ./karith.bend as KA
import ./kbpf.bend as KB
import ./ownpf.bend as OW
import ./solvedpf.bend as SP

def absurd(-A: Type, x: Empty) -> A:
  match x:

# The facts
# ---------

def fpick_pre(b: Bool, +f: DR.Fact, +g: DR.Fact, +r1: List<&2, DR.Fact>, +r2: List<&2, DR.Fact>, +hf: MP.FAg(f, g), +hr: MP.Pre(r1, r2)) -> MP.Pre(SV.facts.pick(b, f, r1), SV.facts.pick(b, g, r2)):
  match b:
    case True{}:
      (hf, hr)
    case False{}:
      hr

def fpick_len(b: Bool, +f: DR.Fact, +g: DR.Fact, +r1: List<&2, DR.Fact>, +r2: List<&2, DR.Fact>, +hr: {MP.flen(r1) == MP.flen(r2) : Nat}) -> {MP.flen(SV.facts.pick(b, f, r1)) == MP.flen(SV.facts.pick(b, g, r2)) : Nat}:
  match b:
    case True{}:
      %hr : {1n+MP.flen(r1) == 1n+_ : Nat}
      {==}
    case False{}:
      hr

# the facts of cs, with nd from either classes: they agree, and are as long
def facts_pre(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +cs: List<&2, Nat>, +sk: SK.Sketch, +cls1: List<&2, SV.Class>, +w1: Bool, +cls2: List<&2, SV.Class>, +w2: Bool, +k: Nat)
  -> MP.Pre(SV.facts.go(es, own, cs, sk, cls1, w1, k), SV.facts.go(es, own, cs, sk, cls2, w2, k)):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      fpick_pre(SV.mem(SV.nth(own, k), cs), DR.Fact{e, SV.fnd.pick(w1, cls1, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(own, k)))}, DR.Fact{e, SV.fnd.pick(w2, cls2, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(own, k)))},
        SV.facts.go(t, own, cs, sk, cls1, w1, 1n+k), SV.facts.go(t, own, cs, sk, cls2, w2, 1n+k),
        ({==}, {==}),
        facts_pre(t, own, cs, sk, cls1, w1, cls2, w2, 1n+k))

def facts_len(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +cs: List<&2, Nat>, +sk: SK.Sketch, +cls1: List<&2, SV.Class>, +w1: Bool, +cls2: List<&2, SV.Class>, +w2: Bool, +k: Nat)
  -> {MP.flen(SV.facts.go(es, own, cs, sk, cls1, w1, k)) == MP.flen(SV.facts.go(es, own, cs, sk, cls2, w2, k)) : Nat}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      fpick_len(SV.mem(SV.nth(own, k), cs), DR.Fact{e, SV.fnd.pick(w1, cls1, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(own, k)))}, DR.Fact{e, SV.fnd.pick(w2, cls2, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(own, k)))},
        SV.facts.go(t, own, cs, sk, cls1, w1, 1n+k), SV.facts.go(t, own, cs, sk, cls2, w2, 1n+k), facts_len(t, own, cs, sk, cls1, w1, cls2, w2, 1n+k))

# no constraints, no facts
def facts_none(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +cls: List<&2, SV.Class>, +w: Bool, +k: Nat) -> {SV.facts.go(es, own, Nil{}, sk, cls, w, k) == Nil{} : List<&2, DR.Fact>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      facts_none(t, own, sk, cls, w, 1n+k)

def bor_comm(a: Bool, b: Bool) -> {SV.bor(a, b) == SV.bor(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def mem_sc(+v: Nat, +kb: List<&2, Nat>, +c: Nat) -> {SV.mem(v, CO.lsnoc(kb, c)) == SV.mem(v, Con{c, kb}) : Bool}:
  Equal.trans(Bool, SV.mem(v, CO.lsnoc(kb, c)), SV.bor(SV.mem(v, kb), SV.eq(v, c)), SV.mem(v, Con{c, kb}), KB.mem_snoc(v, kb, c), bor_comm(SV.mem(v, kb), SV.eq(v, c)))

# kb with c after it, or before it: the same facts
def facts_snoc(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +kb: List<&2, Nat>, +c: Nat, +sk: SK.Sketch, +cls: List<&2, SV.Class>, +w: Bool, +k: Nat)
  -> {SV.facts.go(es, own, CO.lsnoc(kb, c), sk, cls, w, k) == SV.facts.go(es, own, Con{c, kb}, sk, cls, w, k) : List<&2, DR.Fact>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %facts_snoc(t, own, kb, c, sk, cls, w, 1n+k) : {SV.facts.pick(SV.mem(SV.nth(own, k), CO.lsnoc(kb, c)), DR.Fact{e, SV.fnd.pick(w, cls, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(own, k)))}, SV.facts.go(t, own, CO.lsnoc(kb, c), sk, cls, w, 1n+k)) == SV.facts.pick(SV.mem(SV.nth(own, k), Con{c, kb}), DR.Fact{e, SV.fnd.pick(w, cls, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(own, k)))}, _) : List<&2, DR.Fact>}
      %mem_sc(SV.nth(own, k), kb, c) : {SV.facts.pick(SV.mem(SV.nth(own, k), CO.lsnoc(kb, c)), DR.Fact{e, SV.fnd.pick(w, cls, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(own, k)))}, SV.facts.go(t, own, CO.lsnoc(kb, c), sk, cls, w, 1n+k)) == SV.facts.pick(_, DR.Fact{e, SV.fnd.pick(w, cls, k), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, SV.nth(own, k)))}, SV.facts.go(t, own, CO.lsnoc(kb, c), sk, cls, w, 1n+k)) : List<&2, DR.Fact>}
      {==}

# Kept constraints, then c's own
# ------------------------------

def fcat_pick(b: Bool, +f: DR.Fact, +A: List<&2, DR.Fact>, +B: List<&2, DR.Fact>) -> {SV.facts.pick(b, f, SV.fcat(A, B)) == SV.fcat(SV.facts.pick(b, f, A), B) : List<&2, DR.Fact>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def nmg.c(b: Bool, +o: Nat, +h: Nat, +t: List<&2, Nat>, +c: Nat, eb: {SV.eq(o, h) == b : Bool}, hl: {SV.lt(h, c) == True{} : Bool}, ho: {SV.lt(o, c) == False{} : Bool}, ih: {SV.mem(o, t) == False{} : Bool})
  -> {SV.bor(SV.eq(o, h), SV.mem(o, t)) == False{} : Bool}:
  match b:
    case True{}:
      absurd({SV.bor(SV.eq(o, h), SV.mem(o, t)) == False{} : Bool}, KA.tf(Equal.trans(Bool, True{}, SV.lt(o, c), False{}, Equal.sym(Bool, SV.lt(o, c), True{}, (%Equal.sym(Nat, o, h, LI.eq_ok(o, h, eb)) : {SV.lt(_, c) == True{} : Bool}
        hl)), ho)))
    case False{}:
      %Equal.sym(Bool, SV.eq(o, h), False{}, eb) : {SV.bor(_, SV.mem(o, t)) == False{} : Bool}
      ih

# at or past kb's bound: not in kb
def nmem_ge(kb: List<&2, Nat>, +o: Nat, +c: Nat, +hb: {SV.below(kb, c) == True{} : Bool}, +ho: {SV.lt(o, c) == False{} : Bool}) -> {SV.mem(o, kb) == False{} : Bool}:
  match kb:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      nmg.c(SV.eq(o, h), o, h, t, c, {==}, LI.band_l(SV.lt(h, c), SV.below(t, c), hb), ho, nmem_ge(t, o, c, LI.band_r(SV.lt(h, c), SV.below(t, c), hb), ho))

def FF(+e: E.QExpr, +sk: SK.Sketch, +o: Nat, +j: Nat) -> DR.Fact:
  DR.Fact{e, SV.fnd.pick(False{}, Nil{}, j), SV.dstat_of(SV.ents(sk), SV.kind_at(sk, o))}

# no owner from j before c: none of kb's facts from j
def facts_nil(es: List<&2, E.QExpr>, own_j: List<&2, Nat>, +own: List<&2, Nat>, +kb: List<&2, Nat>, +sk: SK.Sketch, +c: Nat, +j: Nat,
  +ho: {OW.ndrop(j, own) == own_j : List<&2, Nat>}, +hl: {SV.len(own_j) == SV.neqs(es) : Nat}, +hg: {OW.geall(own_j, c) == True{} : Bool}, +hb: {SV.below(kb, c) == True{} : Bool})
  -> {SV.facts.go(es, own, kb, sk, Nil{}, False{}, j) == Nil{} : List<&2, DR.Fact>}:
  match es own_j:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+o, +ot}:
      absurd({SV.facts.go(Nil{}, own, kb, sk, Nil{}, False{}, j) == Nil{} : List<&2, DR.Fact>}, SP.len_nc(o, ot, hl))
    case Con{+e, +t} Nil{}:
      absurd({SV.facts.go(Con{e, t}, own, kb, sk, Nil{}, False{}, j) == Nil{} : List<&2, DR.Fact>}, SP.len_cn(e, t, hl))
    case Con{+e, +t} Con{+o, +ot}:
      %Equal.sym(Nat, SV.nth(own, j), o, OW.nth_of(own, j, o, ot, ho)) : {SV.facts.pick(SV.mem(_, kb), FF(e, sk, _, j), SV.facts.go(t, own, kb, sk, Nil{}, False{}, 1n+j)) == Nil{} : List<&2, DR.Fact>}
      %Equal.sym(Bool, SV.mem(o, kb), False{}, nmem_ge(kb, o, c, hb, OW.ge_head(o, c, ot, hg))) : {SV.facts.pick(_, FF(e, sk, o, j), SV.facts.go(t, own, kb, sk, Nil{}, False{}, 1n+j)) == Nil{} : List<&2, DR.Fact>}
      facts_nil(t, ot, own, kb, sk, c, 1n+j, OW.ndrop_step(j, own, o, ot, ho), LN.succ_inj(SV.len(ot), SV.neqs(t), hl), OW.ge_tail(o, c, ot, hg), hb)

# the split at one equation, its owner o: x1, x2, x3 whether c : kb, kb,
# [c] take it
def SGb(x1: Bool, x2: Bool, x3: Bool, +F: DR.Fact, +A: List<&2, DR.Fact>, +B: List<&2, DR.Fact>, +Cc: List<&2, DR.Fact>) -> Type:
  {SV.facts.pick(x1, F, A) == SV.fcat(SV.facts.pick(x2, F, B), SV.facts.pick(x3, F, Cc)) : List<&2, DR.Fact>}

def split.c(b1: Bool, b2: Bool, +o: Nat, +c: Nat, +kb: List<&2, Nat>, +F: DR.Fact, +A: List<&2, DR.Fact>, +B: List<&2, DR.Fact>, +Cc: List<&2, DR.Fact>,
  +e1: {SV.lt(o, c) == b1 : Bool}, +e2: {SV.eq(o, c) == b2 : Bool}, +hb: {SV.below(kb, c) == True{} : Bool},
  hnil: {SV.lt(o, c) == False{} : Bool} -> {B == Nil{} : List<&2, DR.Fact>}, +ih: {A == SV.fcat(B, Cc) : List<&2, DR.Fact>})
  -> SGb(SV.bor(SV.eq(o, c), SV.mem(o, kb)), SV.mem(o, kb), SV.bor(SV.eq(o, c), False{}), F, A, B, Cc):
  match b1 b2:
    case True{} True{}:
      absurd(SGb(SV.bor(SV.eq(o, c), SV.mem(o, kb)), SV.mem(o, kb), SV.bor(SV.eq(o, c), False{}), F, A, B, Cc), KA.tf(Equal.trans(Bool, True{}, SV.lt(o, c), False{}, Equal.sym(Bool, SV.lt(o, c), True{}, e1), KB.eq_lt(o, c, e2))))
    case True{} False{}:
      %Equal.sym(Bool, SV.eq(o, c), False{}, e2) : SGb(SV.bor(_, SV.mem(o, kb)), SV.mem(o, kb), SV.bor(_, False{}), F, A, B, Cc)
      %Equal.sym(List<&2, DR.Fact>, A, SV.fcat(B, Cc), ih) : SGb(SV.mem(o, kb), SV.mem(o, kb), False{}, F, _, B, Cc)
      fcat_pick(SV.mem(o, kb), F, B, Cc)
    case False{} True{}:
      %Equal.sym(Bool, SV.eq(o, c), True{}, e2) : SGb(SV.bor(_, SV.mem(o, kb)), SV.mem(o, kb), SV.bor(_, False{}), F, A, B, Cc)
      %Equal.sym(Bool, SV.mem(o, kb), False{}, nmem_ge(kb, o, c, hb, e1)) : SGb(True{}, _, True{}, F, A, B, Cc)
      %Equal.sym(List<&2, DR.Fact>, A, SV.fcat(B, Cc), ih) : SGb(True{}, False{}, True{}, F, _, B, Cc)
      %Equal.sym(List<&2, DR.Fact>, B, Nil{}, hnil(e1)) : SGb(True{}, False{}, True{}, F, SV.fcat(_, Cc), _, Cc)
      {==}
    case False{} False{}:
      %Equal.sym(Bool, SV.eq(o, c), False{}, e2) : SGb(SV.bor(_, SV.mem(o, kb)), SV.mem(o, kb), SV.bor(_, False{}), F, A, B, Cc)
      %Equal.sym(Bool, SV.mem(o, kb), False{}, nmem_ge(kb, o, c, hb, e1)) : SGb(_, _, False{}, F, A, B, Cc)
      ih

def split(es: List<&2, E.QExpr>, own_j: List<&2, Nat>, +own: List<&2, Nat>, +kb: List<&2, Nat>, +sk: SK.Sketch, +c: Nat, +j: Nat,
  +ho: {OW.ndrop(j, own) == own_j : List<&2, Nat>}, +hl: {SV.len(own_j) == SV.neqs(es) : Nat}, +hs: {OW.sorted(own) == True{} : Bool}, +hb: {SV.below(kb, c) == True{} : Bool})
  -> {SV.facts.go(es, own, Con{c, kb}, sk, Nil{}, False{}, j) == SV.fcat(SV.facts.go(es, own, kb, sk, Nil{}, False{}, j), SV.facts.go(es, own, Con{c, Nil{}}, sk, Nil{}, False{}, j)) : List<&2, DR.Fact>}:
  match es own_j:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+o, +ot}:
      absurd({SV.facts.go(Nil{}, own, Con{c, kb}, sk, Nil{}, False{}, j) == SV.fcat(SV.facts.go(Nil{}, own, kb, sk, Nil{}, False{}, j), SV.facts.go(Nil{}, own, Con{c, Nil{}}, sk, Nil{}, False{}, j)) : List<&2, DR.Fact>}, SP.len_nc(o, ot, hl))
    case Con{+e, +t} Nil{}:
      absurd({SV.facts.go(Con{e, t}, own, Con{c, kb}, sk, Nil{}, False{}, j) == SV.fcat(SV.facts.go(Con{e, t}, own, kb, sk, Nil{}, False{}, j), SV.facts.go(Con{e, t}, own, Con{c, Nil{}}, sk, Nil{}, False{}, j)) : List<&2, DR.Fact>}, SP.len_cn(e, t, hl))
    case Con{+e, +t} Con{+o, +ot}:
      +hl2 = LN.succ_inj(SV.len(ot), SV.neqs(t), hl)
      +ho2 = OW.ndrop_step(j, own, o, ot, ho)
      %Equal.sym(Nat, SV.nth(own, j), o, OW.nth_of(own, j, o, ot, ho)) : SGb(SV.bor(SV.eq(_, c), SV.mem(_, kb)), SV.mem(_, kb), SV.bor(SV.eq(_, c), False{}), FF(e, sk, _, j), SV.facts.go(t, own, Con{c, kb}, sk, Nil{}, False{}, 1n+j), SV.facts.go(t, own, kb, sk, Nil{}, False{}, 1n+j), SV.facts.go(t, own, Con{c, Nil{}}, sk, Nil{}, False{}, 1n+j))
      split.c(SV.lt(o, c), SV.eq(o, c), o, c, kb, FF(e, sk, o, j), SV.facts.go(t, own, Con{c, kb}, sk, Nil{}, False{}, 1n+j), SV.facts.go(t, own, kb, sk, Nil{}, False{}, 1n+j), SV.facts.go(t, own, Con{c, Nil{}}, sk, Nil{}, False{}, 1n+j), {==}, {==}, hb,
        hn => facts_nil(t, ot, own, kb, sk, c, 1n+j, ho2, hl2, OW.up_of(own, j, o, ot, c, hs, ho, hn), hb),
        split(t, ot, own, kb, sk, c, 1n+j, ho2, hl2, hs, hb))

# with kb below c: c's facts come after kb's
def rfacts_split(+sk: SK.Sketch, +kb: List<&2, Nat>, +c: Nat, +hb: {SV.below(kb, c) == True{} : Bool}) -> {SV.rfacts(sk, Con{c, kb}) == SV.fcat(SV.rfacts(sk, kb), SV.rfacts(sk, Con{c, Nil{}})) : List<&2, DR.Fact>}:
  split(SK.Sketch.eqs(sk), SV.owners(sk), SV.owners(sk), kb, sk, c, 0n, {==}, OW.len_owners(sk), OW.sorted_owners(sk), hb)

# The calls
# ---------

# Which constraints join kb
# -------------------------

def kbn(b: Bool, +kb: List<&2, Nat>, +c: Nat) -> List<&2, Nat>:
  match b:
    case True{}:
      kb
    case False{}:
      CO.lsnoc(kb, c)

def onea_red(m: Maybe<&2, List<&2, SV.Ref>>, +dd: List<&2, SV.Drop>) -> {SV.is_red(PA.one.a(m, dd)) == False{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+rs}:
      {==}

def onek_red(a: Bool, +sk: SK.Sketch, +kb: List<&2, Nat>, +c: Nat, +dd: List<&2, SV.Drop>) -> {SV.is_red(PA.one.k(a, sk, kb, c, dd)) == False{} : Bool}:
  match a:
    case True{}:
      onea_red(PA.srefs(SV.csides(sk, [c]), sk, kb, c, 0n), dd)
    case False{}:
      {==}

def oneg_kb(g: ST.GS, w: PA.CW, +sk: SK.Sketch, +c: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>)
  -> {DPS.pkb(PA.PO.st(PA.one.g(g, sk, c, kb, rows, B, bp, vm, w))) == kbn(SV.is_red(PA.PO.k(PA.one.g(g, sk, c, kb, rows, B, bp, vm, w))), kb, c) : List<&2, Nat>}:
  match g w:
    case ST.GFail{ST.Red{+j, +s, +x}} PA.CW{+rows2, +B2, +bp2, +dd, +us}:
      {==}
    case ST.GOk{+vm2} PA.CW{+rows2, +B2, +bp2, +dd, +us}:
      %Equal.sym(Bool, SV.is_red(PA.one.k(SV.is_amberable(sk, c, SV.drops(dd)), sk, kb, c, dd)), False{}, onek_red(SV.is_amberable(sk, c, SV.drops(dd)), sk, kb, c, dd)) : {CO.lsnoc(kb, c) == kbn(_, kb, c) : List<&2, Nat>}
      {==}

def one2c_kb(b: Bool, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +c: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +cls: List<&2, SV.Class>, +cx: List<&2, E.QExpr>, +W: DC.WK)
  -> {DPS.pkb(PA.PO.st(DPS.one2.c(b, es, own, sk, adj, f, c, kb, rows, B, bp, vm, cls, cx, W))) == kbn(SV.is_red(PA.PO.k(DPS.one2.c(b, es, own, sk, adj, f, c, kb, rows, B, bp, vm, cls, cx, W))), kb, c) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      oneg_kb(PA.grpl(PA.cw.us(DPS.cwalk2(es, own, c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, SV.facts.go(es, own, kb, sk, cls, True{}, 0n), cx, W)), adj, f, ST.GOk{vm}), DPS.cwalk2(es, own, c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, SV.facts.go(es, own, kb, sk, cls, True{}, 0n), cx, W), sk, c, kb, rows, B, bp, vm)

# c joins kb exactly when its class is not red
def one2_kb(+es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +c: Nat, st: PA.PS, +cls: List<&2, SV.Class>, +W: DC.WK, +foA: DC.FO)
  -> {DPS.pkb(PA.PO.st(DPS.one2(es, own, sk, adj, f, c, st, cls, W, foA))) == kbn(SV.is_red(PA.PO.k(DPS.one2(es, own, sk, adj, f, c, st, cls, W, foA))), DPS.pkb(st), c) : List<&2, Nat>}:
  match st:
    case PA.PS{+kb, +rows, +B, +bp, +vm}:
      one2c_kb(DCF.refutable2.o(sk, c, kb, DC.FO.o(foA)), es, own, sk, adj, f, c, kb, rows, B, bp, vm, cls, SV.eqs_of(sk, Con{c, kb}), W)
