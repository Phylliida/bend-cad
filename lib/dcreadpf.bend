# bend-cad: reading a fixpoint's checks (PLAN-sk13b B3, "Closure of a
# fixpoint"). Each check of the last round found nothing; here, what that
# says at each element it went over:
# - frame-back: every generator of F has its imaginary part in K;
# - void: no open sketch segment has its direction in K squared;
# - merges: for each root r and each record outside r's component, the
#   label test of r's set at that record's node found nothing.
# Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./listpf.bend as LP2
import ./labpf.bend as LP
import ./lab.bend as LB
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./dclose.bend as DC
import ./dcgenpf.bend as GN
import ./dcsetpf.bend as ST
import ./lspanpf.bend as LS
import ./dcshapepf.bend as SH
import ./pairpf.bend as PP

def absurd(-A: Type, x: Empty) -> A:
  match x:

def dsome_none(+x: DR.Der, h: {Some{x} == None{} : Maybe<&2, DR.Der>}) -> Empty:
  ST.dnone_some(x, Equal.sym(Maybe<&2, DR.Der>, Some{x}, None{}, h))

def mis.some(m: Maybe<&2, List<&2, DC.Mem>>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

def msome_none(+x: List<&2, DC.Mem>, h: {Some{x} == None{} : Maybe<&2, List<&2, DC.Mem>>}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, Equal.cong(Maybe<&2, List<&2, DC.Mem>>, Bool, m => mis.some(m), None{}, Some{x}, Equal.sym(Maybe<&2, List<&2, DC.Mem>>, Some{x}, None{}, h))) : PP.none_some.p(_)
  Unit{}

def iis.some(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

def isome_none(+x: Nat, h: {Some{x} == None{} : Maybe<&2, Nat>}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, Equal.cong(Maybe<&2, Nat>, Bool, m => iis.some(m), None{}, Some{x}, Equal.sym(Maybe<&2, Nat>, Some{x}, None{}, h))) : PP.none_some.p(_)
  Unit{}

# Frame-back
# ----------

def mp2.b(b: Bool, +x: DR.Der, +rest: Maybe<&2, DR.Der>, e: {DC.mpick2(b, x, rest) == None{} : Maybe<&2, DR.Der>}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, dsome_none(x, e))
    case False{}:
      {==}

def mp2.r(b: Bool, +x: DR.Der, +rest: Maybe<&2, DR.Der>, e: {DC.mpick2(b, x, rest) == None{} : Maybe<&2, DR.Der>}) -> {rest == None{} : Maybe<&2, DR.Der>}:
  match b:
    case True{}:
      absurd({rest == None{} : Maybe<&2, DR.Der>}, dsome_none(x, e))
    case False{}:
      e

# frame-back found nothing: every generator of F has its imaginary part in K
def fback_none(gs: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +e: {DC.fback(gs, es, fs, k) == None{} : Maybe<&2, DR.Der>},
  +g: DR.Der, n: Nat, en: {ST.dat(gs, n) == Some{g} : Maybe<&2, DR.Der>}) -> {KS.ks.inb(k, SK.VE.y(DR.Jd.x(DR.concl(es, fs, g)))) == True{} : Bool}:
  match gs n:
    case Nil{} n:
      absurd({KS.ks.inb(k, SK.VE.y(DR.Jd.x(DR.concl(es, fs, g)))) == True{} : Bool}, ST.dnone_some(g, en))
    case Con{+g0, +t} 0n:
      %ST.dsome_inj(g0, g, en) : {KS.ks.inb(k, SK.VE.y(DR.Jd.x(DR.concl(es, fs, _)))) == True{} : Bool}
      LS.bnot_f(KS.ks.inb(k, SK.VE.y(DR.Jd.x(DR.concl(es, fs, g0)))), mp2.b(SV.bnot(KS.ks.inb(k, SK.VE.y(DR.Jd.x(DR.concl(es, fs, g0))))), DR.DBack{g0}, DC.fback(t, es, fs, k), e))
    case Con{+g0, +t} 1n+m:
      fback_none(t, es, fs, k, mp2.r(SV.bnot(KS.ks.inb(k, SK.VE.y(DR.Jd.x(DR.concl(es, fs, g0))))), DR.DBack{g0}, DC.fback(t, es, fs, k), e), g, m, en)

# Void segments
# -------------

def vp.b(f: Bool, +i: Nat, +rest: Maybe<&2, Nat>, e: {DC.vpick(f, i, rest) == None{} : Maybe<&2, Nat>}) -> {f == False{} : Bool}:
  match f:
    case True{}:
      absurd({True{} == False{} : Bool}, isome_none(i, e))
    case False{}:
      {==}

def vp.r(f: Bool, +i: Nat, +rest: Maybe<&2, Nat>, e: {DC.vpick(f, i, rest) == None{} : Maybe<&2, Nat>}) -> {rest == None{} : Maybe<&2, Nat>}:
  match f:
    case True{}:
      absurd({rest == None{} : Maybe<&2, Nat>}, isome_none(i, e))
    case False{}:
      e

def voidseg_none.g(g: Bool, +s: Nat, +i: Nat, +t: List<&2, Nat>, +es: List<&2, SK.Ent>, +cs: DC.SP, +k: KS.KS, eg: {g == SV.eq(s, i) : Bool},
  +e: {DC.vpick(SV.band(SV.bnot(DC.coll(es, cs, i)), DC.fullc(es, k, i)), i, DC.voidseg(t, es, cs, k)) == None{} : Maybe<&2, Nat>},
  hn: {SV.bor(g, SH.nmem(DR.NSeg{s}, DC.snodes(t))) == True{} : Bool},
  ih: {DC.voidseg(t, es, cs, k) == None{} : Maybe<&2, Nat>} -> {SH.nmem(DR.NSeg{s}, DC.snodes(t)) == True{} : Bool} -> {SV.band(SV.bnot(DC.coll(es, cs, s)), DC.fullc(es, k, s)) == False{} : Bool})
  -> {SV.band(SV.bnot(DC.coll(es, cs, s)), DC.fullc(es, k, s)) == False{} : Bool}:
  match g:
    case True{}:
      %Equal.sym(Nat, s, i, LP2.eq_ok(s, i, Equal.sym(Bool, True{}, SV.eq(s, i), eg))) : {SV.band(SV.bnot(DC.coll(es, cs, _)), DC.fullc(es, k, _)) == False{} : Bool}
      vp.b(SV.band(SV.bnot(DC.coll(es, cs, i)), DC.fullc(es, k, i)), i, DC.voidseg(t, es, cs, k), e)
    case False{}:
      ih(vp.r(SV.band(SV.bnot(DC.coll(es, cs, i)), DC.fullc(es, k, i)), i, DC.voidseg(t, es, cs, k), e), hn)

# no void open segment: a sketch segment either is collapsed or has its
# direction outside K squared
def voidseg_none(ids: List<&2, Nat>, +s: Nat, +es: List<&2, SK.Ent>, +cs: DC.SP, +k: KS.KS, e: {DC.voidseg(ids, es, cs, k) == None{} : Maybe<&2, Nat>},
  hn: {SH.nmem(DR.NSeg{s}, DC.snodes(ids)) == True{} : Bool}) -> {SV.band(SV.bnot(DC.coll(es, cs, s)), DC.fullc(es, k, s)) == False{} : Bool}:
  match ids:
    case Nil{}:
      absurd({SV.band(SV.bnot(DC.coll(es, cs, s)), DC.fullc(es, k, s)) == False{} : Bool}, LP.tf(Equal.sym(Bool, False{}, True{}, hn)))
    case Con{+i, +t}:
      voidseg_none.g(SV.eq(s, i), s, i, t, es, cs, k, {==}, e, hn, x => y => voidseg_none(t, s, es, cs, k, x, y))

# Merges
# ------

def mgsp.a(m: Maybe<&2, List<&2, DC.Mem>>, +rest: Maybe<&2, List<&2, DC.Mem>>, e: {DC.mgs.pick(m, rest) == None{} : Maybe<&2, List<&2, DC.Mem>>}) -> {m == None{} : Maybe<&2, List<&2, DC.Mem>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      absurd({Some{x} == None{} : Maybe<&2, List<&2, DC.Mem>>}, msome_none(x, e))

def mgsp.r(m: Maybe<&2, List<&2, DC.Mem>>, +rest: Maybe<&2, List<&2, DC.Mem>>, e: {DC.mgs.pick(m, rest) == None{} : Maybe<&2, List<&2, DC.Mem>>}) -> {rest == None{} : Maybe<&2, List<&2, DC.Mem>>}:
  match m:
    case None{}:
      e
    case Some{+x}:
      absurd({rest == None{} : Maybe<&2, List<&2, DC.Mem>>}, msome_none(x, e))

# the merge search found nothing: neither did it at any root
def mgs_none(rs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +e: {DC.mgs(rs, es, fs, t, s) == None{} : Maybe<&2, List<&2, DC.Mem>>},
  +r: DR.Node, n: Nat, en: {SH.nat(rs, n) == Some{r} : Maybe<&2, DR.Node>}) -> {DC.mgs.root(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r) == None{} : Maybe<&2, List<&2, DC.Mem>>}:
  match rs n:
    case Nil{} n:
      absurd({DC.mgs.root(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r) == None{} : Maybe<&2, List<&2, DC.Mem>>}, SH.nnone_some(r, en))
    case Con{+r0, +tl} 0n:
      %SH.nsome_inj(r0, r, en) : {DC.mgs.root(DC.node_eq(_, DR.NFrame{}), es, fs, t, s, _) == None{} : Maybe<&2, List<&2, DC.Mem>>}
      mgsp.a(DC.mgs.root(DC.node_eq(r0, DR.NFrame{}), es, fs, t, s, r0), DC.mgs(tl, es, fs, t, s), e)
    case Con{+r0, +tl} 1n+j:
      mgs_none(tl, es, fs, t, s, mgsp.r(DC.mgs.root(DC.node_eq(r0, DR.NFrame{}), es, fs, t, s, r0), DC.mgs(tl, es, fs, t, s), e), r, j, en)

def mgFp.a(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, DC.Mem>, +mb: DC.Mem, +b: DR.Node, +rest: Maybe<&2, List<&2, DC.Mem>>,
  e: {DC.mgF.pick(m, es, fs, k, ms, mb, b, rest) == None{} : Maybe<&2, List<&2, DC.Mem>>}) -> {m == None{} : Maybe<&2, DR.Lab>}:
  match m:
    case None{}:
      {==}
    case Some{+w}:
      absurd({Some{w} == None{} : Maybe<&2, DR.Lab>}, msome_none(DC.merge(ms, DR.NFrame{}, DR.DFrame{KS.ks.der(es, fs, k, SK.VE.y(DR.gmul(w, DR.zdir(es, b)))), DR.gmul(w, DR.zdir(es, b))}, w, mb), e))

def mgFp.r(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, DC.Mem>, +mb: DC.Mem, +b: DR.Node, +rest: Maybe<&2, List<&2, DC.Mem>>,
  e: {DC.mgF.pick(m, es, fs, k, ms, mb, b, rest) == None{} : Maybe<&2, List<&2, DC.Mem>>}) -> {rest == None{} : Maybe<&2, List<&2, DC.Mem>>}:
  match m:
    case None{}:
      e
    case Some{+w}:
      absurd({rest == None{} : Maybe<&2, List<&2, DC.Mem>>}, msome_none(DC.merge(ms, DR.NFrame{}, DR.DFrame{KS.ks.der(es, fs, k, SK.VE.y(DR.gmul(w, DR.zdir(es, b)))), DR.gmul(w, DR.zdir(es, b))}, w, mb), e))

def mgFi.r(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, DC.Mem>, +mb: DC.Mem, +b: DR.Node, +rest: Maybe<&2, List<&2, DC.Mem>>,
  e: {DC.mgF.if(f, es, fs, k, ms, mb, b, rest) == None{} : Maybe<&2, List<&2, DC.Mem>>}) -> {rest == None{} : Maybe<&2, List<&2, DC.Mem>>}:
  match f:
    case True{}:
      mgFp.r(LB.ks.lab(es, fs, k, DR.zdir(es, b)), es, fs, k, ms, mb, b, rest, e)
    case False{}:
      e

def mgFi.t(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, DC.Mem>, +mb: DC.Mem, +b: DR.Node, +rb: DR.Node, +rest: Maybe<&2, List<&2, DC.Mem>>,
  ef: {f == SV.bnot(DC.node_eq(rb, DR.NFrame{})) : Bool}, hne: {DC.node_eq(rb, DR.NFrame{}) == False{} : Bool}, e: {DC.mgF.if(f, es, fs, k, ms, mb, b, rest) == None{} : Maybe<&2, List<&2, DC.Mem>>})
  -> {LB.ks.lab(es, fs, k, DR.zdir(es, b)) == None{} : Maybe<&2, DR.Lab>}:
  match f:
    case True{}:
      mgFp.a(LB.ks.lab(es, fs, k, DR.zdir(es, b)), es, fs, k, ms, mb, b, rest, e)
    case False{}:
      absurd({LB.ks.lab(es, fs, k, DR.zdir(es, b)) == None{} : Maybe<&2, DR.Lab>}, LP.tf(Equal.sym(Bool, False{}, True{}, Equal.trans(Bool, False{}, SV.bnot(DC.node_eq(rb, DR.NFrame{})), True{}, ef,
        Equal.cong(Bool, Bool, x => SV.bnot(x), DC.node_eq(rb, DR.NFrame{}), False{}, hne)))))

# the search at one root found nothing: its label test found nothing at
# any record outside its component
def mgF_none(sc: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, DC.Mem>, +e: {DC.mgF(sc, es, fs, k, ms) == None{} : Maybe<&2, List<&2, DC.Mem>>},
  +m: DC.Mem, n: Nat, +en: {SH.mat(sc, n) == Some{m} : Maybe<&2, DC.Mem>}, +hne: {DC.node_eq(DC.Mem.r(m), DR.NFrame{}) == False{} : Bool})
  -> {LB.ks.lab(es, fs, k, DR.zdir(es, DC.Mem.a(m))) == None{} : Maybe<&2, DR.Lab>}:
  match sc n:
    case Nil{} n:
      absurd({LB.ks.lab(es, fs, k, DR.zdir(es, DC.Mem.a(m))) == None{} : Maybe<&2, DR.Lab>}, SH.mnone_some(m, en))
    case Con{DC.Mem{+b0, +rb0, +wb0, +db0}, +tl} 0n:
      %SH.msome_inj(DC.Mem{b0, rb0, wb0, db0}, m, en) : {LB.ks.lab(es, fs, k, DR.zdir(es, DC.Mem.a(_))) == None{} : Maybe<&2, DR.Lab>}
      mgFi.t(SV.bnot(DC.node_eq(rb0, DR.NFrame{})), es, fs, k, ms, DC.Mem{b0, rb0, wb0, db0}, b0, rb0, DC.mgF(tl, es, fs, k, ms), {==},
        Equal.trans(Bool, DC.node_eq(rb0, DR.NFrame{}), DC.node_eq(DC.Mem.r(m), DR.NFrame{}), False{},
          Equal.cong(DC.Mem, Bool, x => DC.node_eq(DC.Mem.r(x), DR.NFrame{}), DC.Mem{b0, rb0, wb0, db0}, m, SH.msome_inj(DC.Mem{b0, rb0, wb0, db0}, m, en)), hne), e)
    case Con{DC.Mem{+b0, +rb0, +wb0, +db0}, +tl} 1n+j:
      mgF_none(tl, es, fs, k, ms, mgFi.r(SV.bnot(DC.node_eq(rb0, DR.NFrame{})), es, fs, k, ms, DC.Mem{b0, rb0, wb0, db0}, b0, DC.mgF(tl, es, fs, k, ms), e), m, j, en, hne)

def mgRp.a(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +r: DR.Node, +ms: List<&2, DC.Mem>, +mb: DC.Mem, +b: DR.Node, +rest: Maybe<&2, List<&2, DC.Mem>>,
  e: {DC.mgR.pick(m, es, fs, t, h, r, ms, mb, b, rest) == None{} : Maybe<&2, List<&2, DC.Mem>>}) -> {m == None{} : Maybe<&2, DR.Lab>}:
  match m:
    case None{}:
      {==}
    case Some{+w}:
      absurd({Some{w} == None{} : Maybe<&2, DR.Lab>}, msome_none(DC.merge(ms, r, HS.hs.der(es, fs, t, r, h, DR.gmul(w, DR.zdir(es, b))), w, mb), e))

def mgRp.r(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +r: DR.Node, +ms: List<&2, DC.Mem>, +mb: DC.Mem, +b: DR.Node, +rest: Maybe<&2, List<&2, DC.Mem>>,
  e: {DC.mgR.pick(m, es, fs, t, h, r, ms, mb, b, rest) == None{} : Maybe<&2, List<&2, DC.Mem>>}) -> {rest == None{} : Maybe<&2, List<&2, DC.Mem>>}:
  match m:
    case None{}:
      e
    case Some{+w}:
      absurd({rest == None{} : Maybe<&2, List<&2, DC.Mem>>}, msome_none(DC.merge(ms, r, HS.hs.der(es, fs, t, r, h, DR.gmul(w, DR.zdir(es, b))), w, mb), e))

def mgRi.r(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +r: DR.Node, +ms: List<&2, DC.Mem>, +mb: DC.Mem, +b: DR.Node, +rest: Maybe<&2, List<&2, DC.Mem>>,
  e: {DC.mgR.if(f, es, fs, t, h, r, ms, mb, b, rest) == None{} : Maybe<&2, List<&2, DC.Mem>>}) -> {rest == None{} : Maybe<&2, List<&2, DC.Mem>>}:
  match f:
    case True{}:
      mgRp.r(LB.hs.lab(es, fs, t, h, DR.zdir(es, b)), es, fs, t, h, r, ms, mb, b, rest, e)
    case False{}:
      e

def mgRi.t(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +r: DR.Node, +ms: List<&2, DC.Mem>, +mb: DC.Mem, +b: DR.Node, +rb: DR.Node, +rest: Maybe<&2, List<&2, DC.Mem>>,
  ef: {f == SV.bnot(DC.node_eq(rb, r)) : Bool}, hne: {DC.node_eq(rb, r) == False{} : Bool}, e: {DC.mgR.if(f, es, fs, t, h, r, ms, mb, b, rest) == None{} : Maybe<&2, List<&2, DC.Mem>>})
  -> {LB.hs.lab(es, fs, t, h, DR.zdir(es, b)) == None{} : Maybe<&2, DR.Lab>}:
  match f:
    case True{}:
      mgRp.a(LB.hs.lab(es, fs, t, h, DR.zdir(es, b)), es, fs, t, h, r, ms, mb, b, rest, e)
    case False{}:
      absurd({LB.hs.lab(es, fs, t, h, DR.zdir(es, b)) == None{} : Maybe<&2, DR.Lab>}, LP.tf(Equal.sym(Bool, False{}, True{}, Equal.trans(Bool, False{}, SV.bnot(DC.node_eq(rb, r)), True{}, ef,
        Equal.cong(Bool, Bool, x => SV.bnot(x), DC.node_eq(rb, r), False{}, hne)))))

# the search at one root found nothing: its label test found nothing at
# any record outside its component
def mgR_none(sc: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +r: DR.Node, +ms: List<&2, DC.Mem>, +e: {DC.mgR(sc, es, fs, t, h, r, ms) == None{} : Maybe<&2, List<&2, DC.Mem>>},
  +m: DC.Mem, n: Nat, +en: {SH.mat(sc, n) == Some{m} : Maybe<&2, DC.Mem>}, +hne: {DC.node_eq(DC.Mem.r(m), r) == False{} : Bool})
  -> {LB.hs.lab(es, fs, t, h, DR.zdir(es, DC.Mem.a(m))) == None{} : Maybe<&2, DR.Lab>}:
  match sc n:
    case Nil{} n:
      absurd({LB.hs.lab(es, fs, t, h, DR.zdir(es, DC.Mem.a(m))) == None{} : Maybe<&2, DR.Lab>}, SH.mnone_some(m, en))
    case Con{DC.Mem{+b0, +rb0, +wb0, +db0}, +tl} 0n:
      %SH.msome_inj(DC.Mem{b0, rb0, wb0, db0}, m, en) : {LB.hs.lab(es, fs, t, h, DR.zdir(es, DC.Mem.a(_))) == None{} : Maybe<&2, DR.Lab>}
      mgRi.t(SV.bnot(DC.node_eq(rb0, r)), es, fs, t, h, r, ms, DC.Mem{b0, rb0, wb0, db0}, b0, rb0, DC.mgR(tl, es, fs, t, h, r, ms), {==},
        Equal.trans(Bool, DC.node_eq(rb0, r), DC.node_eq(DC.Mem.r(m), r), False{},
          Equal.cong(DC.Mem, Bool, x => DC.node_eq(DC.Mem.r(x), r), DC.Mem{b0, rb0, wb0, db0}, m, SH.msome_inj(DC.Mem{b0, rb0, wb0, db0}, m, en)), hne), e)
    case Con{DC.Mem{+b0, +rb0, +wb0, +db0}, +tl} 1n+j:
      mgR_none(tl, es, fs, t, h, r, ms, mgRi.r(SV.bnot(DC.node_eq(rb0, r)), es, fs, t, h, r, ms, DC.Mem{b0, rb0, wb0, db0}, b0, DC.mgR(tl, es, fs, t, h, r, ms), e), m, j, en, hne)

# Links
# -----

def lsome_none(+x: DC.Link, h: {Some{x} == None{} : Maybe<&2, DC.Link>}) -> Empty:
  SH.lnone_some(x, Equal.sym(Maybe<&2, DC.Link>, Some{x}, None{}, h))

def lf.a(m: Maybe<&2, DC.Link>, +rest: Maybe<&2, DC.Link>, e: {DC.lfirst(m, rest) == None{} : Maybe<&2, DC.Link>}) -> {m == None{} : Maybe<&2, DC.Link>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      absurd({Some{x} == None{} : Maybe<&2, DC.Link>}, lsome_none(x, e))

def lf.r(m: Maybe<&2, DC.Link>, +rest: Maybe<&2, DC.Link>, e: {DC.lfirst(m, rest) == None{} : Maybe<&2, DC.Link>}) -> {rest == None{} : Maybe<&2, DC.Link>}:
  match m:
    case None{}:
      e
    case Some{+x}:
      absurd({rest == None{} : Maybe<&2, DC.Link>}, lsome_none(x, e))

def lkg.r(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +rep: DC.Rep, +bs: List<&2, DR.Node>, +rs: List<&2, DR.Node>, +rest: Maybe<&2, DC.Link>,
  e: {DC.lks.go(f, es, fs, t, s, c, rep, bs, rs, rest) == None{} : Maybe<&2, DC.Link>}) -> {rest == None{} : Maybe<&2, DC.Link>}:
  match f:
    case True{}:
      e
    case False{}:
      lf.r(DC.lk.r(rs, es, fs, t, s, c), rest, lf.r(DC.lk.c(bs, es, fs, t, s, c, rep), DC.lfirst(DC.lk.r(rs, es, fs, t, s, c), rest), e))

def lkg.c(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +rep: DC.Rep, +bs: List<&2, DR.Node>, +rs: List<&2, DR.Node>, +rest: Maybe<&2, DC.Link>,
  hf: {f == False{} : Bool}, e: {DC.lks.go(f, es, fs, t, s, c, rep, bs, rs, rest) == None{} : Maybe<&2, DC.Link>}) -> {DC.lk.c(bs, es, fs, t, s, c, rep) == None{} : Maybe<&2, DC.Link>}:
  match f:
    case True{}:
      absurd({DC.lk.c(bs, es, fs, t, s, c, rep) == None{} : Maybe<&2, DC.Link>}, LP.tf(hf))
    case False{}:
      lf.a(DC.lk.c(bs, es, fs, t, s, c, rep), DC.lfirst(DC.lk.r(rs, es, fs, t, s, c), rest), e)

def lkg.rr(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +rep: DC.Rep, +bs: List<&2, DR.Node>, +rs: List<&2, DR.Node>, +rest: Maybe<&2, DC.Link>,
  hf: {f == False{} : Bool}, e: {DC.lks.go(f, es, fs, t, s, c, rep, bs, rs, rest) == None{} : Maybe<&2, DC.Link>}) -> {DC.lk.r(rs, es, fs, t, s, c) == None{} : Maybe<&2, DC.Link>}:
  match f:
    case True{}:
      absurd({DC.lk.r(rs, es, fs, t, s, c) == None{} : Maybe<&2, DC.Link>}, LP.tf(hf))
    case False{}:
      lf.a(DC.lk.r(rs, es, fs, t, s, c), rest, lf.r(DC.lk.c(bs, es, fs, t, s, c, rep), DC.lfirst(DC.lk.r(rs, es, fs, t, s, c), rest), e))

# Nat lists, by membership
def imem(+i: Nat, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      SV.bor(SV.eq(i, h), imem(i, t))

def lks_none.hf(+c: Nat, +c0: Nat, +es: List<&2, SK.Ent>, +s: DC.Sk, eg: {True{} == SV.eq(c, c0) : Bool}, hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool})
  -> {DC.fullc(es, DC.Sk.k(s), c0) == False{} : Bool}:
  %LP2.eq_ok(c, c0, Equal.sym(Bool, True{}, SV.eq(c, c0), eg)) : {DC.fullc(es, DC.Sk.k(s), _) == False{} : Bool}
  hf

def lks_none.hd(+c0: Nat, +tl: List<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +bs: List<&2, DR.Node>, +rs: List<&2, DR.Node>,
  +hf: {DC.fullc(es, DC.Sk.k(s), c0) == False{} : Bool},
  +e: {DC.lks.go(DC.fullc(es, DC.Sk.k(s), c0), es, fs, t, s, c0, DC.crep(es, fs, t, s, c0), bs, rs, DC.lks(tl, es, fs, t, s, bs, rs)) == None{} : Maybe<&2, DC.Link>})
  -> SK.Both({DC.lk.c(bs, es, fs, t, s, c0, DC.crep(es, fs, t, s, c0)) == None{} : Maybe<&2, DC.Link>}, {DC.lk.r(rs, es, fs, t, s, c0) == None{} : Maybe<&2, DC.Link>}):
  (lkg.c(DC.fullc(es, DC.Sk.k(s), c0), es, fs, t, s, c0, DC.crep(es, fs, t, s, c0), bs, rs, DC.lks(tl, es, fs, t, s, bs, rs), hf, e),
   lkg.rr(DC.fullc(es, DC.Sk.k(s), c0), es, fs, t, s, c0, DC.crep(es, fs, t, s, c0), bs, rs, DC.lks(tl, es, fs, t, s, bs, rs), hf, e))

def lks_none.g(g: Bool, +c: Nat, +c0: Nat, +tl: List<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +bs: List<&2, DR.Node>, +rs: List<&2, DR.Node>,
  +eg: {g == SV.eq(c, c0) : Bool}, +hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool},
  +e: {DC.lks.go(DC.fullc(es, DC.Sk.k(s), c0), es, fs, t, s, c0, DC.crep(es, fs, t, s, c0), bs, rs, DC.lks(tl, es, fs, t, s, bs, rs)) == None{} : Maybe<&2, DC.Link>},
  hn: {SV.bor(g, imem(c, tl)) == True{} : Bool},
  ih: {DC.lks(tl, es, fs, t, s, bs, rs) == None{} : Maybe<&2, DC.Link>} -> {imem(c, tl) == True{} : Bool} -> SK.Both({DC.lk.c(bs, es, fs, t, s, c, DC.crep(es, fs, t, s, c)) == None{} : Maybe<&2, DC.Link>}, {DC.lk.r(rs, es, fs, t, s, c) == None{} : Maybe<&2, DC.Link>}))
  -> SK.Both({DC.lk.c(bs, es, fs, t, s, c, DC.crep(es, fs, t, s, c)) == None{} : Maybe<&2, DC.Link>}, {DC.lk.r(rs, es, fs, t, s, c) == None{} : Maybe<&2, DC.Link>}):
  match g:
    case True{}:
      %Equal.sym(Nat, c, c0, LP2.eq_ok(c, c0, Equal.sym(Bool, True{}, SV.eq(c, c0), eg))) : SK.Both({DC.lk.c(bs, es, fs, t, s, _, DC.crep(es, fs, t, s, _)) == None{} : Maybe<&2, DC.Link>}, {DC.lk.r(rs, es, fs, t, s, _) == None{} : Maybe<&2, DC.Link>})
      lks_none.hd(c0, tl, es, fs, t, s, bs, rs, lks_none.hf(c, c0, es, s, eg, hf), e)
    case False{}:
      ih(lkg.r(DC.fullc(es, DC.Sk.k(s), c0), es, fs, t, s, c0, DC.crep(es, fs, t, s, c0), bs, rs, DC.lks(tl, es, fs, t, s, bs, rs), e), hn)

# the link search found nothing: at each collapsed segment not in K
# squared, neither did its two checks
def lks_none(cids: List<&2, Nat>, +c: Nat, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +bs: List<&2, DR.Node>, +rs: List<&2, DR.Node>,
  e: {DC.lks(cids, es, fs, t, s, bs, rs) == None{} : Maybe<&2, DC.Link>}, hn: {imem(c, cids) == True{} : Bool}, +hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool})
  -> SK.Both({DC.lk.c(bs, es, fs, t, s, c, DC.crep(es, fs, t, s, c)) == None{} : Maybe<&2, DC.Link>}, {DC.lk.r(rs, es, fs, t, s, c) == None{} : Maybe<&2, DC.Link>}):
  match cids:
    case Nil{}:
      absurd(SK.Both({DC.lk.c(bs, es, fs, t, s, c, DC.crep(es, fs, t, s, c)) == None{} : Maybe<&2, DC.Link>}, {DC.lk.r(rs, es, fs, t, s, c) == None{} : Maybe<&2, DC.Link>}), LP.tf(Equal.sym(Bool, False{}, True{}, hn)))
    case Con{+c0, +tl}:
      lks_none.g(SV.eq(c, c0), c, c0, tl, es, fs, t, s, bs, rs, {==}, hf, e, hn, x => y => lks_none(tl, c, es, fs, t, s, bs, rs, x, y, hf))

def wsome_none(+x: DR.Lab, h: {Some{x} == None{} : Maybe<&2, DR.Lab>}) -> Empty:
  LP.lnone_some(x, Equal.sym(Maybe<&2, DR.Lab>, Some{x}, None{}, h))

def lkm.a(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +c: Nat, +rep: DC.Rep, +b: DR.Node, +rest: Maybe<&2, DC.Link>,
  e: {DC.lk.mk(m, es, fs, t, k, c, rep, b, rest) == None{} : Maybe<&2, DC.Link>}) -> {m == None{} : Maybe<&2, DR.Lab>}:
  match m:
    case None{}:
      {==}
    case Some{+w}:
      absurd({Some{w} == None{} : Maybe<&2, DR.Lab>}, lsome_none(DC.Link{c, b, w, DC.rep.der(rep, es, fs, t, k, c, DR.gmul(w, DR.zdir(es, b)))}, e))

def lkm.r(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +c: Nat, +rep: DC.Rep, +b: DR.Node, +rest: Maybe<&2, DC.Link>,
  e: {DC.lk.mk(m, es, fs, t, k, c, rep, b, rest) == None{} : Maybe<&2, DC.Link>}) -> {rest == None{} : Maybe<&2, DC.Link>}:
  match m:
    case None{}:
      e
    case Some{+w}:
      absurd({rest == None{} : Maybe<&2, DC.Link>}, lsome_none(DC.Link{c, b, w, DC.rep.der(rep, es, fs, t, k, c, DR.gmul(w, DR.zdir(es, b)))}, e))

def lkci.r(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +rep: DC.Rep, +b: DR.Node, +rest: Maybe<&2, DC.Link>,
  e: {DC.lk.c.if(f, es, fs, t, s, c, rep, b, rest) == None{} : Maybe<&2, DC.Link>}) -> {rest == None{} : Maybe<&2, DC.Link>}:
  match f:
    case True{}:
      e
    case False{}:
      lkm.r(DC.lk.first(DC.rep.basis(rep, es, fs, t, DR.zdir(es, b)), DC.lstored(DC.Sk.ls(s), c, b)), es, fs, t, DC.Sk.k(s), c, rep, b, rest, e)

def lkci.a(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +rep: DC.Rep, +b: DR.Node, +rest: Maybe<&2, DC.Link>, hf: {f == False{} : Bool},
  e: {DC.lk.c.if(f, es, fs, t, s, c, rep, b, rest) == None{} : Maybe<&2, DC.Link>}) -> {DC.lk.first(DC.rep.basis(rep, es, fs, t, DR.zdir(es, b)), DC.lstored(DC.Sk.ls(s), c, b)) == None{} : Maybe<&2, DR.Lab>}:
  match f:
    case True{}:
      absurd({DC.lk.first(DC.rep.basis(rep, es, fs, t, DR.zdir(es, b)), DC.lstored(DC.Sk.ls(s), c, b)) == None{} : Maybe<&2, DR.Lab>}, LP.tf(hf))
    case False{}:
      lkm.a(DC.lk.first(DC.rep.basis(rep, es, fs, t, DR.zdir(es, b)), DC.lstored(DC.Sk.ls(s), c, b)), es, fs, t, DC.Sk.k(s), c, rep, b, rest, e)

def lkc_none.ne(+b: DR.Node, +b0: DR.Node, +c: Nat, eb: {b == b0 : DR.Node}, hne: {DC.node_eq(b, DR.NSeg{c}) == False{} : Bool}) -> {DC.node_eq(b0, DR.NSeg{c}) == False{} : Bool}:
  %eb : {DC.node_eq(_, DR.NSeg{c}) == False{} : Bool}
  hne

def lkc_none.g(g: Bool, +b: DR.Node, +b0: DR.Node, +tl: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +rep: DC.Rep,
  +eg: {g == DC.node_eq(b, b0) : Bool}, +hne: {DC.node_eq(b, DR.NSeg{c}) == False{} : Bool},
  +e: {DC.lk.c.if(DC.node_eq(b0, DR.NSeg{c}), es, fs, t, s, c, rep, b0, DC.lk.c(tl, es, fs, t, s, c, rep)) == None{} : Maybe<&2, DC.Link>},
  hn: {SV.bor(g, SH.nmem(b, tl)) == True{} : Bool},
  ih: {DC.lk.c(tl, es, fs, t, s, c, rep) == None{} : Maybe<&2, DC.Link>} -> {SH.nmem(b, tl) == True{} : Bool} -> {DC.lk.first(DC.rep.basis(rep, es, fs, t, DR.zdir(es, b)), DC.lstored(DC.Sk.ls(s), c, b)) == None{} : Maybe<&2, DR.Lab>})
  -> {DC.lk.first(DC.rep.basis(rep, es, fs, t, DR.zdir(es, b)), DC.lstored(DC.Sk.ls(s), c, b)) == None{} : Maybe<&2, DR.Lab>}:
  match g:
    case True{}:
      %Equal.sym(DR.Node, b, b0, GN.node_eq_ok(b, b0, Equal.sym(Bool, True{}, DC.node_eq(b, b0), eg))) : {DC.lk.first(DC.rep.basis(rep, es, fs, t, DR.zdir(es, _)), DC.lstored(DC.Sk.ls(s), c, _)) == None{} : Maybe<&2, DR.Lab>}
      lkci.a(DC.node_eq(b0, DR.NSeg{c}), es, fs, t, s, c, rep, b0, DC.lk.c(tl, es, fs, t, s, c, rep),
        lkc_none.ne(b, b0, c, GN.node_eq_ok(b, b0, Equal.sym(Bool, True{}, DC.node_eq(b, b0), eg)), hne), e)
    case False{}:
      ih(lkci.r(DC.node_eq(b0, DR.NSeg{c}), es, fs, t, s, c, rep, b0, DC.lk.c(tl, es, fs, t, s, c, rep), e), hn)

# the check of collapsed c against the nodes bs found nothing: at each node
# b other than c, every basis label is in the stored span
def lkc_none(bs: List<&2, DR.Node>, +b: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +rep: DC.Rep,
  e: {DC.lk.c(bs, es, fs, t, s, c, rep) == None{} : Maybe<&2, DC.Link>}, hb: {SH.nmem(b, bs) == True{} : Bool}, +hne: {DC.node_eq(b, DR.NSeg{c}) == False{} : Bool})
  -> {DC.lk.first(DC.rep.basis(rep, es, fs, t, DR.zdir(es, b)), DC.lstored(DC.Sk.ls(s), c, b)) == None{} : Maybe<&2, DR.Lab>}:
  match bs:
    case Nil{}:
      absurd({DC.lk.first(DC.rep.basis(rep, es, fs, t, DR.zdir(es, b)), DC.lstored(DC.Sk.ls(s), c, b)) == None{} : Maybe<&2, DR.Lab>}, LP.tf(Equal.sym(Bool, False{}, True{}, hb)))
    case Con{+b0, +tl}:
      lkc_none.g(DC.node_eq(b, b0), b, b0, tl, es, fs, t, s, c, rep, {==}, hne, e, hb, x => y => lkc_none(tl, b, es, fs, t, s, c, rep, x, y, hne))

def lkrm.a(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +r: DR.Node, +rest: Maybe<&2, DC.Link>,
  e: {DC.lk.r.mk(m, es, fs, t, s, c, r, rest) == None{} : Maybe<&2, DC.Link>}) -> {m == None{} : Maybe<&2, DR.Lab>}:
  match m:
    case None{}:
      {==}
    case Some{+w}:
      absurd({Some{w} == None{} : Maybe<&2, DR.Lab>}, lsome_none(DC.Link{c, r, DR.Lab.conj(w), DR.DTurn{DC.lk.r.der(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r, DR.gmul(w, DR.zseg(es, c))), DR.Lab.conj(w), DR.NSeg{c}}}, e))

def lkrm.r(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +r: DR.Node, +rest: Maybe<&2, DC.Link>,
  e: {DC.lk.r.mk(m, es, fs, t, s, c, r, rest) == None{} : Maybe<&2, DC.Link>}) -> {rest == None{} : Maybe<&2, DC.Link>}:
  match m:
    case None{}:
      e
    case Some{+w}:
      absurd({rest == None{} : Maybe<&2, DC.Link>}, lsome_none(DC.Link{c, r, DR.Lab.conj(w), DR.DTurn{DC.lk.r.der(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r, DR.gmul(w, DR.zseg(es, c))), DR.Lab.conj(w), DR.NSeg{c}}}, e))

def lkr_none.g(g: Bool, +r: DR.Node, +r0: DR.Node, +tl: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat,
  +eg: {g == DC.node_eq(r, r0) : Bool},
  +e: {DC.lk.r.mk(DC.lk.r.first(DC.lk.r.basis(DC.node_eq(r0, DR.NFrame{}), es, fs, t, s, r0, DR.zseg(es, c)), DC.lstored(DC.Sk.ls(s), c, r0)), es, fs, t, s, c, r0, DC.lk.r(tl, es, fs, t, s, c)) == None{} : Maybe<&2, DC.Link>},
  hn: {SV.bor(g, SH.nmem(r, tl)) == True{} : Bool},
  ih: {DC.lk.r(tl, es, fs, t, s, c) == None{} : Maybe<&2, DC.Link>} -> {SH.nmem(r, tl) == True{} : Bool} -> {DC.lk.r.first(DC.lk.r.basis(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r, DR.zseg(es, c)), DC.lstored(DC.Sk.ls(s), c, r)) == None{} : Maybe<&2, DR.Lab>})
  -> {DC.lk.r.first(DC.lk.r.basis(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r, DR.zseg(es, c)), DC.lstored(DC.Sk.ls(s), c, r)) == None{} : Maybe<&2, DR.Lab>}:
  match g:
    case True{}:
      %Equal.sym(DR.Node, r, r0, GN.node_eq_ok(r, r0, Equal.sym(Bool, True{}, DC.node_eq(r, r0), eg))) : {DC.lk.r.first(DC.lk.r.basis(DC.node_eq(_, DR.NFrame{}), es, fs, t, s, _, DR.zseg(es, c)), DC.lstored(DC.Sk.ls(s), c, _)) == None{} : Maybe<&2, DR.Lab>}
      lkrm.a(DC.lk.r.first(DC.lk.r.basis(DC.node_eq(r0, DR.NFrame{}), es, fs, t, s, r0, DR.zseg(es, c)), DC.lstored(DC.Sk.ls(s), c, r0)), es, fs, t, s, c, r0, DC.lk.r(tl, es, fs, t, s, c), e)
    case False{}:
      ih(lkrm.r(DC.lk.r.first(DC.lk.r.basis(DC.node_eq(r0, DR.NFrame{}), es, fs, t, s, r0, DR.zseg(es, c)), DC.lstored(DC.Sk.ls(s), c, r0)), es, fs, t, s, c, r0, DC.lk.r(tl, es, fs, t, s, c), e), hn)

# the check of the roots rs against collapsed c found nothing: at each root
# every basis label's conjugate is in the stored span
def lkr_none(rs: List<&2, DR.Node>, +r: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat,
  e: {DC.lk.r(rs, es, fs, t, s, c) == None{} : Maybe<&2, DC.Link>}, hr: {SH.nmem(r, rs) == True{} : Bool}) -> {DC.lk.r.first(DC.lk.r.basis(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r, DR.zseg(es, c)), DC.lstored(DC.Sk.ls(s), c, r)) == None{} : Maybe<&2, DR.Lab>}:
  match rs:
    case Nil{}:
      absurd({DC.lk.r.first(DC.lk.r.basis(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r, DR.zseg(es, c)), DC.lstored(DC.Sk.ls(s), c, r)) == None{} : Maybe<&2, DR.Lab>}, LP.tf(Equal.sym(Bool, False{}, True{}, hr)))
    case Con{+r0, +tl}:
      lkr_none.g(DC.node_eq(r, r0), r, r0, tl, es, fs, t, s, c, {==}, e, hr, x => y => lkr_none(tl, r, es, fs, t, s, c, x, y))

# Bases in the stored span
# ------------------------

def lkp.q(f: Bool, +w: DR.Lab, +rest: Maybe<&2, DR.Lab>, e: {DC.lk.pick(f, w, rest) == None{} : Maybe<&2, DR.Lab>}) -> {f == True{} : Bool}:
  match f:
    case True{}:
      {==}
    case False{}:
      absurd({False{} == True{} : Bool}, wsome_none(w, e))

def lkp.r(f: Bool, +w: DR.Lab, +rest: Maybe<&2, DR.Lab>, e: {DC.lk.pick(f, w, rest) == None{} : Maybe<&2, DR.Lab>}) -> {rest == None{} : Maybe<&2, DR.Lab>}:
  match f:
    case True{}:
      e
    case False{}:
      absurd({rest == None{} : Maybe<&2, DR.Lab>}, wsome_none(w, e))

def BIn(+st: List<&2, DR.Lab>, +b0: DR.Lab, +b1: DR.Lab) -> Data:
  SK.Both(LS.LSp(LS.lat0(st), LS.lat1(st), b0), LS.LSp(LS.lat0(st), LS.lat1(st), b1))

# the basis search found nothing: both basis labels are in the stored span
def basis_in(ws: List<&2, DR.Lab>, +st: List<&2, DR.Lab>, +e: {DC.lk.first(ws, st) == None{} : Maybe<&2, DR.Lab>}, +hp: {LS.pairok(st) == True{} : Bool}, +nz: LS.LNzs(st))
  -> BIn(st, LS.lat0(ws), LS.lat1(ws)):
  match ws:
    case Nil{}:
      (LS.lsp_zero(LS.lab0(), LS.lat0(st), LS.lat1(st), ({==}, {==})), LS.lsp_zero(LS.lab0(), LS.lat0(st), LS.lat1(st), ({==}, {==})))
    case Con{+w0, Nil{}}:
      (LS.qspan_ok(st, w0, lkp.q(DC.qspan(st, w0), w0, None{}, e), hp, nz), LS.lsp_zero(LS.lab0(), LS.lat0(st), LS.lat1(st), ({==}, {==})))
    case Con{+w0, Con{+w1, +tl}}:
      (LS.qspan_ok(st, w0, lkp.q(DC.qspan(st, w0), w0, DC.lk.first(Con{w1, tl}, st), e), hp, nz),
       LS.qspan_ok(st, w1, lkp.q(DC.qspan(st, w1), w1, DC.lk.first(tl, st), lkp.r(DC.qspan(st, w0), w0, DC.lk.first(Con{w1, tl}, st), e)), hp, nz))

# the same for the roots' check, which stores the conjugates
def basis_inc(ws: List<&2, DR.Lab>, +st: List<&2, DR.Lab>, +e: {DC.lk.r.first(ws, st) == None{} : Maybe<&2, DR.Lab>}, +hp: {LS.pairok(st) == True{} : Bool}, +nz: LS.LNzs(st))
  -> BIn(st, DR.Lab.conj(LS.lat0(ws)), DR.Lab.conj(LS.lat1(ws))):
  match ws:
    case Nil{}:
      (LS.lsp_zero(DR.Lab.conj(LS.lab0()), LS.lat0(st), LS.lat1(st), ({==}, {==})), LS.lsp_zero(DR.Lab.conj(LS.lab0()), LS.lat0(st), LS.lat1(st), ({==}, {==})))
    case Con{+w0, Nil{}}:
      (LS.qspan_ok(st, DR.Lab.conj(w0), lkp.q(DC.qspan(st, DR.Lab.conj(w0)), w0, None{}, e), hp, nz), LS.lsp_zero(DR.Lab.conj(LS.lab0()), LS.lat0(st), LS.lat1(st), ({==}, {==})))
    case Con{+w0, Con{+w1, +tl}}:
      (LS.qspan_ok(st, DR.Lab.conj(w0), lkp.q(DC.qspan(st, DR.Lab.conj(w0)), w0, DC.lk.r.first(Con{w1, tl}, st), e), hp, nz),
       LS.qspan_ok(st, DR.Lab.conj(w1), lkp.q(DC.qspan(st, DR.Lab.conj(w1)), w1, DC.lk.r.first(tl, st), lkp.r(DC.qspan(st, DR.Lab.conj(w0)), w0, DC.lk.r.first(Con{w1, tl}, st), e)), hp, nz))
