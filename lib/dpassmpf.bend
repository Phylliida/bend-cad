# bend-cad: the pass from a start kept across closure calls is the pass
# (PLAN-sk13b B4.8): pass2.m returns what pass2 returns, so classes2,
# which runs it, is the pass lib/dpasspf.bend proves honest (classes2_eq),
# and final2_st is pass2_st's state (final2_st_eq).
# - The facts: rfacts(sk, c : kb) is rfacts(sk, kb) and then c's own, for
#   kb below c (owners are sorted: rfacts_split); F0, what an equation
#   reads before c's own, agrees with rfacts(sk, kb) and is as long (they
#   differ only in nd: facts_pre, facts_len).
# - So M, the start of rfacts(sk, kb), given c's facts is the start of
#   c's refutation call (mstart_ok), and given c's earlier equations not
#   dropped, the start of that equation's call (lib/dmemopf.bend:
#   mext_reuse); each call returns what the plain one returns.
# - After c the pass keeps c's start exactly when c joins kb (one2_kb).
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

def dcl_m_eq(+sk: SK.Sketch, +fs: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +m: DC.MK, +hm: MP.MemoOk(SV.ents(sk), fs, DCF.tv(sk), m)) -> {DCF.dcl.m(sk, fs, cx, m) == DCF.dcl(sk, fs, cx) : DC.Out}:
  MP.dclose_m_eq(SV.ents(sk), fs, cx, DCF.tv(sk), DC.dfuel(SV.ents(sk), fs), m, hm)

def ddec_m_eq(+sk: SK.Sketch, +fs: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +e: E.QExpr, +st: Maybe<&2, DR.DStat>, +m: DC.MK, +hm: MP.MemoOk(SV.ents(sk), fs, DCF.tv(sk), m))
  -> {DPS.ddec.m(sk, fs, cx, e, st, m) == DPS.ddec(sk, fs, cx, e, st) : Maybe<&2, DR.Der>}:
  %dcl_m_eq(sk, fs, cx, m, hm) : {DPS.ddec.o(DCF.dcl.m(sk, fs, cx, m), SV.ents(sk), fs, DCF.tv(sk), e, st) == DPS.ddec.o(_, SV.ents(sk), fs, DCF.tv(sk), e, st) : Maybe<&2, DR.Der>}
  {==}

def dirref_m_eq(+sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>, +cx: List<&2, E.QExpr>, +ma: DC.MK, +hm: MP.MemoOk(SV.ents(sk), SV.rfacts(sk, Con{c, cs}), DCF.tv(sk), ma))
  -> {DCF.dirref.m(sk, c, cs, cx, ma) == DCF.dirref(sk, c, cs, cx) : Maybe<&2, DR.DRef>}:
  %dcl_m_eq(sk, SV.rfacts(sk, Con{c, cs}), cx, ma, hm) : {DCF.dirref.m(sk, c, cs, cx, ma) == DF.dref(_, SV.ents(sk), SV.rfacts(sk, Con{c, cs}), CO.supp.ss(sk, c, cs), DCF.angl(sk, Con{c, cs})) : Maybe<&2, DR.DRef>}
  {==}

def ref2_m_eq(b: Bool, +sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>, +cx: List<&2, E.QExpr>, +ma: DC.MK, +hm: MP.MemoOk(SV.ents(sk), SV.rfacts(sk, Con{c, cs}), DCF.tv(sk), ma))
  -> {DCF.ref2.bm(b, sk, c, cs, cx, ma) == DCF.ref2.b(b, sk, c, cs, cx) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      %dirref_m_eq(sk, c, cs, cx, ma, hm) : {DCF.issome(DCF.dirref.m(sk, c, cs, cx, ma)) == DCF.issome(_) : Bool}
      {==}

def refutable2_m_eq(+sk: SK.Sketch, +c: Nat, +cs: List<&2, Nat>, +cx: List<&2, E.QExpr>, +ma: DC.MK, +hm: MP.MemoOk(SV.ents(sk), SV.rfacts(sk, Con{c, cs}), DCF.tv(sk), ma))
  -> {DCF.refutable2.m(sk, c, cs, cx, ma) == DCF.refutable2(sk, c, cs, cx) : Bool}:
  ref2_m_eq(CO.refutable(sk, c, cs), sk, c, cs, cx, ma, hm)

# the start of kb's facts, given c's, is the start of c with kb
def mstart_ok(+sk: SK.Sketch, +c: Nat, +kb: List<&2, Nat>, +M: DC.MK, +hm: MP.MemoOk(SV.ents(sk), SV.rfacts(sk, kb), DCF.tv(sk), M), +hb: {SV.below(kb, c) == True{} : Bool})
  -> MP.MemoOk(SV.ents(sk), SV.rfacts(sk, Con{c, kb}), DCF.tv(sk), DCF.mstart(sk, c, kb, M)):
  %Equal.sym(List<&2, DR.Fact>, SV.rfacts(sk, Con{c, kb}), SV.fcat(SV.rfacts(sk, kb), SV.rfacts(sk, Con{c, Nil{}})), rfacts_split(sk, kb, c, hb)) : MP.MemoOk(SV.ents(sk), _, DCF.tv(sk), DC.mext.m(SV.rfacts(sk, Con{c, Nil{}}), SV.ents(sk), _, DCF.tv(sk), M))
  MP.mext_reuse(SV.ents(sk), SV.rfacts(sk, kb), SV.rfacts(sk, kb), SV.rfacts(sk, Con{c, Nil{}}), DCF.tv(sk), M, hm, MP.pre_refl(SV.rfacts(sk, kb)), {==})

# The walk
# --------
# M the start of R, F0 agreeing with R and as long

def cw2_pick_m_eq(b: Bool, +k: Nat, +e: E.QExpr, +r: EL.Res, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +ds: List<&2, SV.Drop>, +us: List<&2, Nat>,
  +sk: SK.Sketch, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +M: DC.MK, +R: List<&2, DR.Fact>, +hm: MP.MemoOk(SV.ents(sk), R, DCF.tv(sk), M), +hp: MP.Pre(R, F0), +hl: {MP.flen(F0) == MP.flen(R) : Nat})
  -> {DPS.cw2.pick.m(b, k, e, r, rows, B, bp, ds, us, sk, c, F0, cx, M) == DPS.cw2.pick(b, k, e, r, rows, B, bp, ds, us, sk, c, F0, cx) : PA.CW}:
  match b:
    case True{}:
      {==}
    case False{}:
      %ddec_m_eq(sk, SV.fcat(F0, SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, SV.drops(ds), k, 0n)), cx, e, DPS.cstat(sk, c), DC.mext.m(SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, SV.drops(ds), k, 0n), SV.ents(sk), SV.fcat(F0, SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, SV.drops(ds), k, 0n)), DCF.tv(sk), M),
          MP.mext_reuse(SV.ents(sk), R, F0, SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, SV.drops(ds), k, 0n), DCF.tv(sk), M, hm, hp, hl))
        : {DPS.cw2.pick.m(False{}, k, e, r, rows, B, bp, ds, us, sk, c, F0, cx, M) == DPS.cw2.dir(_, k, e, r, rows, B, bp, ds, us, SV.ents(sk), SV.fcat(F0, SV.ofacts.go(SK.Sketch.eqs(sk), SV.owners(sk), sk, c, SV.drops(ds), k, 0n))) : PA.CW}
      {==}

def cw2_res_m_eq(+k: Nat, +e: E.QExpr, st: PA.CW, +sk: SK.Sketch, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +M: DC.MK, +R: List<&2, DR.Fact>, +hm: MP.MemoOk(SV.ents(sk), R, DCF.tv(sk), M), +hp: MP.Pre(R, F0), +hl: {MP.flen(F0) == MP.flen(R) : Nat})
  -> {DPS.cw2.res.m(k, e, st, sk, c, F0, cx, M) == DPS.cw2.res(k, e, st, sk, c, F0, cx) : PA.CW}:
  match st:
    case PA.CW{+rows, +B, +bp, +ds, +us}:
      cw2_pick_m_eq(EP.isnil(EP.resp(EL.resid(rows, e))), k, e, EL.resid(rows, e), rows, B, bp, ds, us, sk, c, F0, cx, M, R, hm, hp, hl)

def cw2_at_m_eq(o: Bool, +k: Nat, +e: E.QExpr, +st: PA.CW, +sk: SK.Sketch, +c: Nat, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +M: DC.MK, +R: List<&2, DR.Fact>, +hm: MP.MemoOk(SV.ents(sk), R, DCF.tv(sk), M), +hp: MP.Pre(R, F0), +hl: {MP.flen(F0) == MP.flen(R) : Nat})
  -> {DPS.cw2.at.m(o, k, e, st, sk, c, F0, cx, M) == DPS.cw2.at(o, k, e, st, sk, c, F0, cx) : PA.CW}:
  match o:
    case True{}:
      cw2_res_m_eq(k, e, st, sk, c, F0, cx, M, R, hm, hp, hl)
    case False{}:
      {==}

# the walk from M returns what the walk returns
def cwalk2_m_eq(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +c: Nat, +k: Nat, +st: PA.CW, +sk: SK.Sketch, +F0: List<&2, DR.Fact>, +cx: List<&2, E.QExpr>, +M: DC.MK, +R: List<&2, DR.Fact>, +hm: MP.MemoOk(SV.ents(sk), R, DCF.tv(sk), M), +hp: MP.Pre(R, F0), +hl: {MP.flen(F0) == MP.flen(R) : Nat})
  -> {DPS.cwalk2.m(es, own, c, k, st, sk, F0, cx, M) == DPS.cwalk2(es, own, c, k, st, sk, F0, cx) : PA.CW}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(PA.CW, DPS.cw2.at.m(SV.eq(SV.nth(own, k), c), k, e, st, sk, c, F0, cx, M), DPS.cw2.at(SV.eq(SV.nth(own, k), c), k, e, st, sk, c, F0, cx), cw2_at_m_eq(SV.eq(SV.nth(own, k), c), k, e, st, sk, c, F0, cx, M, R, hm, hp, hl))
        : {DPS.cwalk2.m(t, own, c, 1n+k, _, sk, F0, cx, M) == DPS.cwalk2(t, own, c, 1n+k, DPS.cw2.at(SV.eq(SV.nth(own, k), c), k, e, st, sk, c, F0, cx), sk, F0, cx) : PA.CW}
      cwalk2_m_eq(t, own, c, 1n+k, DPS.cw2.at(SV.eq(SV.nth(own, k), c), k, e, st, sk, c, F0, cx), sk, F0, cx, M, R, hm, hp, hl)

# One constraint
# --------------

def one2c_m_eq(b: Bool, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +c: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>,
  +cls: List<&2, SV.Class>, +cx: List<&2, E.QExpr>, +M: DC.MK, +R: List<&2, DR.Fact>, +hm: MP.MemoOk(SV.ents(sk), R, DCF.tv(sk), M), +hp: MP.Pre(R, SV.facts.go(es, own, kb, sk, cls, True{}, 0n)), +hl: {MP.flen(SV.facts.go(es, own, kb, sk, cls, True{}, 0n)) == MP.flen(R) : Nat})
  -> {DPS.one2.c.m(b, es, own, sk, adj, f, c, kb, rows, B, bp, vm, cls, cx, M) == DPS.one2.c(b, es, own, sk, adj, f, c, kb, rows, B, bp, vm, cls, cx) : PA.PO}:
  match b:
    case True{}:
      {==}
    case False{}:
      %cwalk2_m_eq(es, own, c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, SV.facts.go(es, own, kb, sk, cls, True{}, 0n), cx, M, R, hm, hp, hl) : {DPS.one2.c.m(False{}, es, own, sk, adj, f, c, kb, rows, B, bp, vm, cls, cx, M) == PA.one.w(_, sk, adj, f, c, kb, rows, B, bp, vm) : PA.PO}
      {==}

# one constraint from M (the start of kb's facts) and MA (c's start)
def one2m_eq(+sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +c: Nat, st: PA.PS, +cls: List<&2, SV.Class>, +M: DC.MK, +MA: DC.MK,
  +hm: MP.MemoOk(SV.ents(sk), SV.rfacts(sk, DPS.pkb(st)), DCF.tv(sk), M), +hma: MP.MemoOk(SV.ents(sk), SV.rfacts(sk, Con{c, DPS.pkb(st)}), DCF.tv(sk), MA))
  -> {DPS.one2.m(SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, c, st, cls, M, MA) == DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, c, st, cls) : PA.PO}:
  match st:
    case PA.PS{+kb, +rows, +B, +bp, +vm}:
      %refutable2_m_eq(sk, c, kb, SV.eqs_of(sk, Con{c, kb}), MA, hma) : {DPS.one2.c.m(DCF.refutable2.m(sk, c, kb, SV.eqs_of(sk, Con{c, kb}), MA), SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, c, kb, rows, B, bp, vm, cls, SV.eqs_of(sk, Con{c, kb}), M) == DPS.one2.c(_, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, c, kb, rows, B, bp, vm, cls, SV.eqs_of(sk, Con{c, kb})) : PA.PO}
      one2c_m_eq(DCF.refutable2.m(sk, c, kb, SV.eqs_of(sk, Con{c, kb}), MA), SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, c, kb, rows, B, bp, vm, cls, SV.eqs_of(sk, Con{c, kb}), M, SV.rfacts(sk, kb), hm,
        facts_pre(SK.Sketch.eqs(sk), SV.owners(sk), kb, sk, Nil{}, False{}, cls, True{}, 0n), facts_len(SK.Sketch.eqs(sk), SV.owners(sk), kb, sk, cls, True{}, Nil{}, False{}, 0n))

# The kept constraints after c
# ----------------------------

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

def one2c_kb(b: Bool, +es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +c: Nat, +kb: List<&2, Nat>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +bp: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +cls: List<&2, SV.Class>, +cx: List<&2, E.QExpr>)
  -> {DPS.pkb(PA.PO.st(DPS.one2.c(b, es, own, sk, adj, f, c, kb, rows, B, bp, vm, cls, cx))) == kbn(SV.is_red(PA.PO.k(DPS.one2.c(b, es, own, sk, adj, f, c, kb, rows, B, bp, vm, cls, cx))), kb, c) : List<&2, Nat>}:
  match b:
    case True{}:
      {==}
    case False{}:
      oneg_kb(PA.grpl(PA.cw.us(DPS.cwalk2(es, own, c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, SV.facts.go(es, own, kb, sk, cls, True{}, 0n), cx)), adj, f, ST.GOk{vm}), DPS.cwalk2(es, own, c, 0n, PA.CW{rows, B, bp, Nil{}, Nil{}}, sk, SV.facts.go(es, own, kb, sk, cls, True{}, 0n), cx), sk, c, kb, rows, B, bp, vm)

# c joins kb exactly when its class is not red
def one2_kb(+es: List<&2, E.QExpr>, +own: List<&2, Nat>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +c: Nat, st: PA.PS, +cls: List<&2, SV.Class>)
  -> {DPS.pkb(PA.PO.st(DPS.one2(es, own, sk, adj, f, c, st, cls))) == kbn(SV.is_red(PA.PO.k(DPS.one2(es, own, sk, adj, f, c, st, cls))), DPS.pkb(st), c) : List<&2, Nat>}:
  match st:
    case PA.PS{+kb, +rows, +B, +bp, +vm}:
      one2c_kb(DCF.refutable2(sk, c, kb, SV.eqs_of(sk, Con{c, kb})), es, own, sk, adj, f, c, kb, rows, B, bp, vm, cls, SV.eqs_of(sk, Con{c, kb}))

# The pass
# --------

# kb below i, and M the start of its facts
def KInv(+sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +M: DC.MK) -> Data:
  SK.Both({SV.below(kb, i) == True{} : Bool}, MP.MemoOk(SV.ents(sk), SV.rfacts(sk, kb), DCF.tv(sk), M))

def inv.b(b: Bool, +sk: SK.Sketch, +i: Nat, +kb: List<&2, Nat>, +M: DC.MK, +MA: DC.MK, +hb: {SV.below(kb, i) == True{} : Bool}, +hm: MP.MemoOk(SV.ents(sk), SV.rfacts(sk, kb), DCF.tv(sk), M),
  +hma: MP.MemoOk(SV.ents(sk), SV.rfacts(sk, Con{i, kb}), DCF.tv(sk), MA)) -> KInv(sk, 1n+i, kbn(b, kb, i), DPS.mnext(b, M, MA)):
  match b:
    case True{}:
      (KB.below_up(kb, i, hb), hm)
    case False{}:
      (KB.below_snoc(kb, i, 1n+i, KB.below_up(kb, i, hb), KB.lt_succ(i)), (%Equal.sym(List<&2, DR.Fact>, SV.rfacts(sk, CO.lsnoc(kb, i)), SV.rfacts(sk, Con{i, kb}), facts_snoc(SK.Sketch.eqs(sk), SV.owners(sk), kb, i, sk, Nil{}, False{}, 0n)) : MP.MemoOk(SV.ents(sk), _, DCF.tv(sk), MA)
        hma))

def oo(+sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +i: Nat, +st: PA.PS, +cls: List<&2, SV.Class>) -> PA.PO:
  DPS.one2(SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, i, st, cls)

def ma(+sk: SK.Sketch, +i: Nat, +st: PA.PS, +M: DC.MK) -> DC.MK:
  DCF.mstart(sk, i, DPS.pkb(st), M)

def step_inv(+sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +i: Nat, +st: PA.PS, +cls: List<&2, SV.Class>, +M: DC.MK, +hb: {SV.below(DPS.pkb(st), i) == True{} : Bool}, +hm: MP.MemoOk(SV.ents(sk), SV.rfacts(sk, DPS.pkb(st)), DCF.tv(sk), M))
  -> KInv(sk, 1n+i, DPS.pkb(PA.PO.st(oo(sk, adj, f, i, st, cls))), DPS.mnext(SV.is_red(PA.PO.k(oo(sk, adj, f, i, st, cls))), M, ma(sk, i, st, M))):
  %Equal.sym(List<&2, Nat>, DPS.pkb(PA.PO.st(oo(sk, adj, f, i, st, cls))), kbn(SV.is_red(PA.PO.k(oo(sk, adj, f, i, st, cls))), DPS.pkb(st), i), one2_kb(SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, i, st, cls))
    : KInv(sk, 1n+i, _, DPS.mnext(SV.is_red(PA.PO.k(oo(sk, adj, f, i, st, cls))), M, ma(sk, i, st, M)))
  inv.b(SV.is_red(PA.PO.k(oo(sk, adj, f, i, st, cls))), sk, i, DPS.pkb(st), M, ma(sk, i, st, M), hb, hm, mstart_ok(sk, i, DPS.pkb(st), M, hm, hb))

def pass2m.d(+id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +i: Nat, +st: PA.PS, +cls: List<&2, SV.Class>, +M: DC.MK,
  +hb: {SV.below(DPS.pkb(st), i) == True{} : Bool}, +hm: MP.MemoOk(SV.ents(sk), SV.rfacts(sk, DPS.pkb(st)), DCF.tv(sk), M),
  ih: KInv(sk, 1n+i, DPS.pkb(PA.PO.st(oo(sk, adj, f, i, st, cls))), DPS.mnext(SV.is_red(PA.PO.k(oo(sk, adj, f, i, st, cls))), M, ma(sk, i, st, M)))
    -> {DPS.pass2.m(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, 1n+i, PA.PO.st(oo(sk, adj, f, i, st, cls)), DPS.csnoc(cls, PA.PO.k(oo(sk, adj, f, i, st, cls))), DPS.mnext(SV.is_red(PA.PO.k(oo(sk, adj, f, i, st, cls))), M, ma(sk, i, st, M))) == DPS.pass2(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, 1n+i, PA.PO.st(oo(sk, adj, f, i, st, cls)), DPS.csnoc(cls, PA.PO.k(oo(sk, adj, f, i, st, cls)))) : List<&2, SV.Class>})
  -> {DPS.pass2.m(Con{SK.Rec{id, False{}, k}, t}, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, i, st, cls, M) == DPS.pass2(Con{SK.Rec{id, False{}, k}, t}, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, i, st, cls) : List<&2, SV.Class>}:
  %Equal.sym(PA.PO, DPS.one2.m(SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, i, st, cls, M, ma(sk, i, st, M)), oo(sk, adj, f, i, st, cls), one2m_eq(sk, adj, f, i, st, cls, M, ma(sk, i, st, M), hm, mstart_ok(sk, i, DPS.pkb(st), M, hm, hb)))
    : {Con{PA.PO.k(_), DPS.pass2.m(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, 1n+i, PA.PO.st(_), DPS.csnoc(cls, PA.PO.k(_)), DPS.mnext(SV.is_red(PA.PO.k(_)), M, ma(sk, i, st, M)))} == Con{PA.PO.k(oo(sk, adj, f, i, st, cls)), DPS.pass2(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, 1n+i, PA.PO.st(oo(sk, adj, f, i, st, cls)), DPS.csnoc(cls, PA.PO.k(oo(sk, adj, f, i, st, cls))))} : List<&2, SV.Class>}
  %ih(step_inv(sk, adj, f, i, st, cls, M, hb, hm))
    : {Con{PA.PO.k(oo(sk, adj, f, i, st, cls)), DPS.pass2.m(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, 1n+i, PA.PO.st(oo(sk, adj, f, i, st, cls)), DPS.csnoc(cls, PA.PO.k(oo(sk, adj, f, i, st, cls))), DPS.mnext(SV.is_red(PA.PO.k(oo(sk, adj, f, i, st, cls))), M, ma(sk, i, st, M)))} == Con{PA.PO.k(oo(sk, adj, f, i, st, cls)), _} : List<&2, SV.Class>}
  {==}

# the pass from M returns what the pass returns
def pass2m_eq(rs: List<&2, SK.Rec>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +i: Nat, +st: PA.PS, +cls: List<&2, SV.Class>, +M: DC.MK, h: KInv(sk, i, DPS.pkb(st), M))
  -> {DPS.pass2.m(rs, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, i, st, cls, M) == DPS.pass2(rs, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, i, st, cls) : List<&2, SV.Class>}:
  match rs:
    case Nil{}:
      {==}
    case Con{SK.Rec{+id, True{}, +k}, +t}:
      (hb, hm) = h
      %pass2m_eq(t, sk, adj, f, 1n+i, st, DPS.csnoc(cls, SV.Kept{Nil{}}), M, (KB.below_up(DPS.pkb(st), i, hb), hm)) : {Con{SV.Kept{Nil{}}, DPS.pass2.m(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, 1n+i, st, DPS.csnoc(cls, SV.Kept{Nil{}}), M)} == Con{SV.Kept{Nil{}}, _} : List<&2, SV.Class>}
      {==}
    case Con{SK.Rec{+id, False{}, +k}, +t}:
      (hb, hm) = h
      pass2m.d(id, k, t, sk, adj, f, i, st, cls, M, hb, hm, x => pass2m_eq(t, sk, adj, f, 1n+i, PA.PO.st(oo(sk, adj, f, i, st, cls)), DPS.csnoc(cls, PA.PO.k(oo(sk, adj, f, i, st, cls))), DPS.mnext(SV.is_red(PA.PO.k(oo(sk, adj, f, i, st, cls))), M, ma(sk, i, st, M)), x))

def pst.d(+id: Nat, +k: SK.Constraint, +t: List<&2, SK.Rec>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +i: Nat, +st: PA.PS, +cls: List<&2, SV.Class>, +M: DC.MK,
  +hb: {SV.below(DPS.pkb(st), i) == True{} : Bool}, +hm: MP.MemoOk(SV.ents(sk), SV.rfacts(sk, DPS.pkb(st)), DCF.tv(sk), M),
  ih: KInv(sk, 1n+i, DPS.pkb(PA.PO.st(oo(sk, adj, f, i, st, cls))), DPS.mnext(SV.is_red(PA.PO.k(oo(sk, adj, f, i, st, cls))), M, ma(sk, i, st, M)))
    -> {DPS.pass2_st.m(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, 1n+i, PA.PO.st(oo(sk, adj, f, i, st, cls)), DPS.csnoc(cls, PA.PO.k(oo(sk, adj, f, i, st, cls))), DPS.mnext(SV.is_red(PA.PO.k(oo(sk, adj, f, i, st, cls))), M, ma(sk, i, st, M))) == DPS.pass2_st(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, 1n+i, PA.PO.st(oo(sk, adj, f, i, st, cls)), DPS.csnoc(cls, PA.PO.k(oo(sk, adj, f, i, st, cls)))) : PA.PS})
  -> {DPS.pass2_st.m(Con{SK.Rec{id, False{}, k}, t}, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, i, st, cls, M) == DPS.pass2_st(Con{SK.Rec{id, False{}, k}, t}, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, i, st, cls) : PA.PS}:
  %Equal.sym(PA.PO, DPS.one2.m(SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, i, st, cls, M, ma(sk, i, st, M)), oo(sk, adj, f, i, st, cls), one2m_eq(sk, adj, f, i, st, cls, M, ma(sk, i, st, M), hm, mstart_ok(sk, i, DPS.pkb(st), M, hm, hb)))
    : {DPS.pass2_st.m(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, 1n+i, PA.PO.st(_), DPS.csnoc(cls, PA.PO.k(_)), DPS.mnext(SV.is_red(PA.PO.k(_)), M, ma(sk, i, st, M))) == DPS.pass2_st(t, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, 1n+i, PA.PO.st(oo(sk, adj, f, i, st, cls)), DPS.csnoc(cls, PA.PO.k(oo(sk, adj, f, i, st, cls)))) : PA.PS}
  ih(step_inv(sk, adj, f, i, st, cls, M, hb, hm))

# the state too
def pass2_stm_eq(rs: List<&2, SK.Rec>, +sk: SK.Sketch, +adj: List<&2, List<&2, Nat>>, +f: Nat, +i: Nat, +st: PA.PS, +cls: List<&2, SV.Class>, +M: DC.MK, h: KInv(sk, i, DPS.pkb(st), M))
  -> {DPS.pass2_st.m(rs, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, i, st, cls, M) == DPS.pass2_st(rs, SK.Sketch.eqs(sk), SV.owners(sk), sk, adj, f, i, st, cls) : PA.PS}:
  match rs:
    case Nil{}:
      {==}
    case Con{SK.Rec{+id, True{}, +k}, +t}:
      (hb, hm) = h
      pass2_stm_eq(t, sk, adj, f, 1n+i, st, DPS.csnoc(cls, SV.Kept{Nil{}}), M, (KB.below_up(DPS.pkb(st), i, hb), hm))
    case Con{SK.Rec{+id, False{}, +k}, +t}:
      (hb, hm) = h
      pst.d(id, k, t, sk, adj, f, i, st, cls, M, hb, hm, x => pass2_stm_eq(t, sk, adj, f, 1n+i, PA.PO.st(oo(sk, adj, f, i, st, cls)), DPS.csnoc(cls, PA.PO.k(oo(sk, adj, f, i, st, cls))), DPS.mnext(SV.is_red(PA.PO.k(oo(sk, adj, f, i, st, cls))), M, ma(sk, i, st, M)), x))

# The start
# ---------

def mem0(+sk: SK.Sketch) -> MP.MemoOk(SV.ents(sk), SV.rfacts(sk, Nil{}), DCF.tv(sk), DPS.m0(sk)):
  (%Equal.sym(List<&2, DR.Fact>, SV.rfacts(sk, Nil{}), Nil{}, facts_none(SK.Sketch.eqs(sk), SV.owners(sk), sk, Nil{}, False{}, 0n)) : MP.MemoOk(SV.ents(sk), _, DCF.tv(sk), DPS.m0(sk))
    ({==}, ({==}, FP.kc_of_inv(DC.snodes(DC.segids(SV.ents(sk))), SV.ents(sk), Nil{}, DCF.tv(sk), KS.ks0()))))

def inv0(+sk: SK.Sketch) -> KInv(sk, 0n, DPS.pkb(PA.start(PA.nvars(sk))), DPS.m0(sk)):
  ({==}, mem0(sk))

# classes2 (the pass from the start for no constraints) is the pass
def classes2_eq(+sk: SK.Sketch) -> {DPS.classes2(sk) == DPS.pass2(PA.recs(sk), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 0n, PA.start(PA.nvars(sk)), Nil{}) : List<&2, SV.Class>}:
  pass2m_eq(PA.recs(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 0n, PA.start(PA.nvars(sk)), Nil{}, DPS.m0(sk), inv0(sk))

def final2_st_eq(+sk: SK.Sketch) -> {DPS.final2_st(sk) == DPS.pass2_st(PA.recs(sk), SK.Sketch.eqs(sk), SV.owners(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 0n, PA.start(PA.nvars(sk)), Nil{}) : PA.PS}:
  pass2_stm_eq(PA.recs(sk), sk, PA.dadjs(SK.Sketch.eqs(sk)), 1n+PA.nvars(sk), 0n, PA.start(PA.nvars(sk)), Nil{}, DPS.m0(sk), inv0(sk))
