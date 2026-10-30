# bend-cad: merges and links are counted (PLAN-sk13b B3, termination).
# - rcount counts the records whose node is their own root. Rerooting old
#   under new moves old's own record off the roots and puts no record on
#   them (a record of new already has new as its root, and old is not new),
#   so every merge takes one away (mgs_dec).
# - DC.lslack counts the links still possible for each pair of a sketch
#   segment and a node: two, less the labels stored. A link is added only
#   when its pair's stored labels do not span it, so fewer than two, and
#   only for a pair in range (lsl_dec). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as LP2
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./lab.bend as LB
import ./dclose.bend as DC
import ./dcgenpf.bend as GN
import ./dcshapepf.bend as SH
import ./dcreadpf.bend as RF

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Roots
# -----

def rb(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def rc1(m: DC.Mem) -> Nat:
  match m:
    case DC.Mem{a, r, w, d}:
      rb(DC.node_eq(a, r))

# the records whose node is their root
def rcount(ms: List<&2, DC.Mem>) -> Nat:
  match ms:
    case Nil{}:
      0n
    case Con{m, t}:
      Nat.add(rc1(m), rcount(t))

def hf_new(+a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, +new: DR.Node, +ms: List<&2, DC.Mem>, ea: {a == new : DR.Node},
  hf: {DC.mem_of(ms, a) == Some{DC.Mem{a, r, w, d}} : Maybe<&2, DC.Mem>}) -> {DC.mem_of(ms, new) == Some{DC.Mem{new, r, w, d}} : Maybe<&2, DC.Mem>}:
  %ea : {DC.mem_of(ms, _) == Some{DC.Mem{_, r, w, d}} : Maybe<&2, DC.Mem>}
  hf

# the record of a root new has new as its root
def rone_root(+a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, +new: DR.Node, +ms: List<&2, DC.Mem>, ea: {a == new : DR.Node},
  hf: {DC.mem_of(ms, a) == Some{DC.Mem{a, r, w, d}} : Maybe<&2, DC.Mem>}, hn: {SH.isroot(ms, new) == True{} : Bool}) -> {DC.node_eq(r, new) == True{} : Bool}:
  (%hf_new(a, r, w, d, new, ms, ea, hf) : {SH.isroot.m(_, new) == True{} : Bool} hn)

def rone_le.t(g: Bool, +a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, +old: DR.Node, +new: DR.Node, +ms: List<&2, DC.Mem>, eg: {g == DC.node_eq(a, new) : Bool},
  ef: {True{} == DC.node_eq(r, old) : Bool}, hf: {DC.mem_of(ms, a) == Some{DC.Mem{a, r, w, d}} : Maybe<&2, DC.Mem>}, hn: {SH.isroot(ms, new) == True{} : Bool},
  hon: {DC.node_eq(old, new) == False{} : Bool}) -> {KA.natle(rb(g), rc1(DC.Mem{a, r, w, d})) == True{} : Bool}:
  match g:
    case True{}:
      +er = GN.node_eq_ok(r, new, rone_root(a, r, w, d, new, ms, GN.node_eq_ok(a, new, Equal.sym(Bool, True{}, DC.node_eq(a, new), eg)), hf, hn))
      absurd({KA.natle(1n, rc1(DC.Mem{a, r, w, d})) == True{} : Bool}, KA.tf(Equal.trans(Bool, True{}, DC.node_eq(old, new), False{},
        Equal.sym(Bool, DC.node_eq(old, new), True{}, SH.node_sym_t(new, old, Equal.sym(Bool, True{}, DC.node_eq(new, old), (%er : {True{} == DC.node_eq(_, old) : Bool} ef)))), hon)))
    case False{}:
      {==}

# rerooting puts no record on the roots
def rone_le(f: Bool, +a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, +ms: List<&2, DC.Mem>,
  ef: {f == DC.node_eq(r, old) : Bool}, hf: {DC.mem_of(ms, a) == Some{DC.Mem{a, r, w, d}} : Maybe<&2, DC.Mem>}, hn: {SH.isroot(ms, new) == True{} : Bool},
  hon: {DC.node_eq(old, new) == False{} : Bool}) -> {KA.natle(rc1(DC.reroot.one(f, a, r, w, d, new, dR, ww, old)), rc1(DC.Mem{a, r, w, d})) == True{} : Bool}:
  match f:
    case True{}:
      rone_le.t(DC.node_eq(a, new), a, r, w, d, old, new, ms, {==}, ef, hf, hn, hon)
    case False{}:
      KA.natle_refl(rc1(DC.Mem{a, r, w, d}))

def rc_le(sc: List<&2, DC.Mem>, +ms: List<&2, DC.Mem>, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, hf: SH.AllFirst(sc, ms), +hn: {SH.isroot(ms, new) == True{} : Bool},
  +hon: {DC.node_eq(old, new) == False{} : Bool}) -> {KA.natle(rcount(DC.reroot(sc, old, new, dR, ww)), rcount(sc)) == True{} : Bool}:
  match sc:
    case Nil{}:
      {==}
    case Con{DC.Mem{+a, +r, +w, +d}, +t}:
      (e0, ht) = hf
      KA.natle_add2(rc1(DC.reroot.one(DC.node_eq(r, old), a, r, w, d, new, dR, ww, old)), rcount(DC.reroot(t, old, new, dR, ww)), rc1(DC.Mem{a, r, w, d}), rcount(t),
        rone_le(DC.node_eq(r, old), a, r, w, d, old, new, dR, ww, ms, {==}, e0, hn, hon), rc_le(t, ms, old, new, dR, ww, ht, hn, hon))

def rc_lt.hd(+a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, +t: List<&2, DC.Mem>, +ms: List<&2, DC.Mem>, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab,
  ht: SH.AllFirst(t, ms), +hn: {SH.isroot(ms, new) == True{} : Bool}, +hon: {DC.node_eq(old, new) == False{} : Bool},
  +ea: {a == old : DR.Node}, +er: {r == old : DR.Node})
  -> {KA.natle(1n+rcount(DC.reroot(Con{DC.Mem{a, r, w, d}, t}, old, new, dR, ww)), rcount(Con{DC.Mem{a, r, w, d}, t})) == True{} : Bool}:
  %Equal.sym(DR.Node, r, old, er) : {KA.natle(1n+Nat.add(rc1(DC.reroot.one(DC.node_eq(_, old), a, _, w, d, new, dR, ww, old)), rcount(DC.reroot(t, old, new, dR, ww))), Nat.add(rb(DC.node_eq(a, _)), rcount(t))) == True{} : Bool}
  %Equal.sym(DR.Node, a, old, ea) : {KA.natle(1n+Nat.add(rc1(DC.reroot.one(DC.node_eq(old, old), _, old, w, d, new, dR, ww, old)), rcount(DC.reroot(t, old, new, dR, ww))), Nat.add(rb(DC.node_eq(_, old)), rcount(t))) == True{} : Bool}
  %Equal.sym(Bool, DC.node_eq(old, old), True{}, SH.node_refl(old)) : {KA.natle(1n+Nat.add(rc1(DC.reroot.one(_, old, old, w, d, new, dR, ww, old)), rcount(DC.reroot(t, old, new, dR, ww))), Nat.add(rb(_), rcount(t))) == True{} : Bool}
  %Equal.sym(Bool, DC.node_eq(old, new), False{}, hon) : {KA.natle(1n+Nat.add(rb(_), rcount(DC.reroot(t, old, new, dR, ww))), Nat.add(1n, rcount(t))) == True{} : Bool}
  rc_le(t, ms, old, new, dR, ww, ht, hn, hon)

def rc_lt.at(sc: List<&2, DC.Mem>, n: Nat, +ms: List<&2, DC.Mem>, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, +m0: DC.Mem, hf: SH.AllFirst(sc, ms),
  +hn: {SH.isroot(ms, new) == True{} : Bool}, +hon: {DC.node_eq(old, new) == False{} : Bool}, e: {SH.mat(sc, n) == Some{m0} : Maybe<&2, DC.Mem>},
  +hna: {DC.node_eq(DC.Mem.a(m0), old) == True{} : Bool}, +hnr: {DC.node_eq(DC.Mem.r(m0), old) == True{} : Bool})
  -> {KA.natle(1n+rcount(DC.reroot(sc, old, new, dR, ww)), rcount(sc)) == True{} : Bool}:
  match sc n:
    case Nil{} n:
      absurd({KA.natle(1n+rcount(DC.reroot(Nil{}, old, new, dR, ww)), rcount(Nil{})) == True{} : Bool}, SH.mnone_some(m0, e))
    case Con{DC.Mem{+a, +r, +w, +d}, +t} 0n:
      (e0, ht) = hf
      +em = Equal.sym(DC.Mem, DC.Mem{a, r, w, d}, m0, SH.msome_inj(DC.Mem{a, r, w, d}, m0, e))
      rc_lt.hd(a, r, w, d, t, ms, old, new, dR, ww, ht, hn, hon,
        GN.node_eq_ok(a, old, (%em : {DC.node_eq(DC.Mem.a(_), old) == True{} : Bool} hna)),
        GN.node_eq_ok(r, old, (%em : {DC.node_eq(DC.Mem.r(_), old) == True{} : Bool} hnr)))
    case Con{DC.Mem{+a, +r, +w, +d}, +t} 1n+k:
      (e0, ht) = hf
      %Equal.sym(Nat, 1n+Nat.add(rc1(DC.reroot.one(DC.node_eq(r, old), a, r, w, d, new, dR, ww, old)), rcount(DC.reroot(t, old, new, dR, ww))),
          Nat.add(rc1(DC.reroot.one(DC.node_eq(r, old), a, r, w, d, new, dR, ww, old)), 1n+rcount(DC.reroot(t, old, new, dR, ww))),
          LN.add_succ(rc1(DC.reroot.one(DC.node_eq(r, old), a, r, w, d, new, dR, ww, old)), rcount(DC.reroot(t, old, new, dR, ww))))
        : {KA.natle(_, Nat.add(rc1(DC.Mem{a, r, w, d}), rcount(t))) == True{} : Bool}
      KA.natle_add2(rc1(DC.reroot.one(DC.node_eq(r, old), a, r, w, d, new, dR, ww, old)), 1n+rcount(DC.reroot(t, old, new, dR, ww)), rc1(DC.Mem{a, r, w, d}), rcount(t),
        rone_le(DC.node_eq(r, old), a, r, w, d, old, new, dR, ww, ms, {==}, e0, hn, hon),
        rc_lt.at(t, k, ms, old, new, dR, ww, m0, ht, hn, hon, e, hna, hnr))

def rc_lt.go(+ms: List<&2, DC.Mem>, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, +a0: DR.Node, +r0: DR.Node, +w0: DR.Lab, +d0: DR.Der,
  mi: SH.MemIn(ms, old, DC.Mem{a0, r0, w0, d0}), hf: SH.AllFirst(ms, ms), +hn: {SH.isroot(ms, new) == True{} : Bool}, +hon: {DC.node_eq(old, new) == False{} : Bool}, +ho: {DC.node_eq(r0, old) == True{} : Bool})
  -> {KA.natle(1n+rcount(DC.reroot(ms, old, new, dR, ww)), rcount(ms)) == True{} : Bool}:
  (hi, hna) = mi
  (n, en) = hi
  rc_lt.at(ms, n, ms, old, new, dR, ww, DC.Mem{a0, r0, w0, d0}, hf, hn, hon, en, hna, ho)

def rc_lt.m(mm: Maybe<&2, DC.Mem>, +ms: List<&2, DC.Mem>, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, hf: SH.AllFirst(ms, ms),
  +hn: {SH.isroot(ms, new) == True{} : Bool}, +hon: {DC.node_eq(old, new) == False{} : Bool}, em: {DC.mem_of(ms, old) == mm : Maybe<&2, DC.Mem>}, ho: {SH.isroot.m(mm, old) == True{} : Bool})
  -> {KA.natle(1n+rcount(DC.reroot(ms, old, new, dR, ww)), rcount(ms)) == True{} : Bool}:
  match mm:
    case None{}:
      absurd({KA.natle(1n+rcount(DC.reroot(ms, old, new, dR, ww)), rcount(ms)) == True{} : Bool}, KA.ft(ho))
    case Some{DC.Mem{+a0, +r0, +w0, +d0}}:
      rc_lt.go(ms, old, new, dR, ww, a0, r0, w0, d0, SH.mem_of_in(ms, old, DC.Mem{a0, r0, w0, d0}, em), hf, hn, hon, ho)

# rerooting a root old under another root new takes one root away
def rc_lt(+ms: List<&2, DC.Mem>, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, hf: SH.AllFirst(ms, ms),
  +hn: {SH.isroot(ms, new) == True{} : Bool}, +hon: {DC.node_eq(old, new) == False{} : Bool}, ho: {SH.isroot(ms, old) == True{} : Bool})
  -> {KA.natle(1n+rcount(DC.reroot(ms, old, new, dR, ww)), rcount(ms)) == True{} : Bool}:
  rc_lt.m(DC.mem_of(ms, old), ms, old, new, dR, ww, hf, hn, hon, {==}, ho)

def band_tl(a: Bool, b: Bool, h: {SV.band(a, SV.bnot(b)) == True{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      match b:
        case True{}:
          absurd({True{} == False{} : Bool}, KA.ft(h))
        case False{}:
          {==}
    case False{}:
      absurd({b == False{} : Bool}, KA.ft(h))

def bnot_t(b: Bool, h: {SV.bnot(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.ft(h))
    case False{}:
      {==}

def mg_dec.go(f: Bool, +ms: List<&2, DC.Mem>, +rr: DR.Node, +d1: DR.Der, +w: DR.Lab, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  ef: {f == SV.band(DC.node_eq(rb, DR.NFrame{}), SV.bnot(DC.node_eq(rr, DR.NFrame{}))) : Bool}, hf: SH.AllFirst(ms, ms), +hrr: {SH.isroot(ms, rr) == True{} : Bool},
  +hF: {SH.isroot(ms, DR.NFrame{}) == True{} : Bool}, hb: {SH.isroot(ms, rb) == True{} : Bool}, hne: {DC.node_eq(rb, rr) == False{} : Bool})
  -> {KA.natle(1n+rcount(DC.merge.go(f, ms, rr, d1, w, b, rb, wb, db)), rcount(ms)) == True{} : Bool}:
  match f:
    case True{}:
      rc_lt(ms, rr, DR.NFrame{}, DR.DThrough{db, DR.DTurn{d1, DR.Lab.conj(w), b}, DR.Lab.conj(wb), b}, LB.lmul(wb, DR.Lab.conj(w)), hf, hF,
        band_tl(DC.node_eq(rb, DR.NFrame{}), DC.node_eq(rr, DR.NFrame{}), Equal.sym(Bool, True{}, SV.band(DC.node_eq(rb, DR.NFrame{}), SV.bnot(DC.node_eq(rr, DR.NFrame{}))), ef)), hrr)
    case False{}:
      rc_lt(ms, rb, rr, DR.DThrough{d1, DR.DTurn{db, DR.Lab.conj(wb), b}, DR.Lab.conj(w), b}, LB.lmul(w, DR.Lab.conj(wb)), hf, hrr, hne, hb)

# merging b's component into the root rr's takes one root away
def mg_dec(+ms: List<&2, DC.Mem>, +rr: DR.Node, +d1: DR.Der, +w: DR.Lab, mb: DC.Mem, hf: SH.AllFirst(ms, ms), +hrr: {SH.isroot(ms, rr) == True{} : Bool},
  +hF: {SH.isroot(ms, DR.NFrame{}) == True{} : Bool}, hb: {SH.isroot(ms, DC.Mem.r(mb)) == True{} : Bool}, hne: {DC.node_eq(DC.Mem.r(mb), rr) == False{} : Bool})
  -> {KA.natle(1n+rcount(DC.merge(ms, rr, d1, w, mb)), rcount(ms)) == True{} : Bool}:
  match mb:
    case DC.Mem{+b, +rb, +wb, +db}:
      mg_dec.go(SV.band(DC.node_eq(rb, DR.NFrame{}), SV.bnot(DC.node_eq(rr, DR.NFrame{}))), ms, rr, d1, w, b, rb, wb, db, {==}, hf, hrr, hF, hb, hne)

# a merge found takes one root away
def OptDec(+ms: List<&2, DC.Mem>, m: Maybe<&2, List<&2, DC.Mem>>) -> Data:
  match m:
    case None{}:
      Unit
    case Some{+x}:
      {KA.natle(1n+rcount(x), rcount(ms)) == True{} : Bool}

def mgF.pick_dec(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, DC.Mem>, +mb: DC.Mem, +b: DR.Node, +rest: Maybe<&2, List<&2, DC.Mem>>,
  hf: SH.AllFirst(ms, ms), +hF: {SH.isroot(ms, DR.NFrame{}) == True{} : Bool}, hb: {SH.isroot(ms, DC.Mem.r(mb)) == True{} : Bool}, hne: {DC.node_eq(DC.Mem.r(mb), DR.NFrame{}) == False{} : Bool},
  hr: OptDec(ms, rest)) -> OptDec(ms, DC.mgF.pick(m, es, fs, k, ms, mb, b, rest)):
  match m:
    case None{}:
      hr
    case Some{+w}:
      mg_dec(ms, DR.NFrame{}, DR.DFrame{KS.ks.der(es, fs, k, SK.VE.y(DR.gmul(w, DR.zdir(es, b)))), DR.gmul(w, DR.zdir(es, b))}, w, mb, hf, hF, hF, hb, hne)

def mgF.if_dec(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, DC.Mem>, +mb: DC.Mem, +b: DR.Node, +rest: Maybe<&2, List<&2, DC.Mem>>,
  ef: {f == SV.bnot(DC.node_eq(DC.Mem.r(mb), DR.NFrame{})) : Bool}, hf: SH.AllFirst(ms, ms), +hF: {SH.isroot(ms, DR.NFrame{}) == True{} : Bool}, hb: {SH.isroot(ms, DC.Mem.r(mb)) == True{} : Bool},
  hr: OptDec(ms, rest)) -> OptDec(ms, DC.mgF.if(f, es, fs, k, ms, mb, b, rest)):
  match f:
    case True{}:
      mgF.pick_dec(LB.ks.lab(es, fs, k, DR.zdir(es, b)), es, fs, k, ms, mb, b, rest, hf, hF, hb,
        bnot_t(DC.node_eq(DC.Mem.r(mb), DR.NFrame{}), Equal.sym(Bool, True{}, SV.bnot(DC.node_eq(DC.Mem.r(mb), DR.NFrame{})), ef)), hr)
    case False{}:
      hr

def mgF_dec(sc: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, DC.Mem>, ho: SH.RootsOk(sc, ms), +hf: SH.AllFirst(ms, ms),
  +hF: {SH.isroot(ms, DR.NFrame{}) == True{} : Bool}) -> OptDec(ms, DC.mgF(sc, es, fs, k, ms)):
  match sc:
    case Nil{}:
      Unit{}
    case Con{DC.Mem{+b, +rb, +wb, +db}, +t}:
      (hb, ht) = ho
      mgF.if_dec(SV.bnot(DC.node_eq(rb, DR.NFrame{})), es, fs, k, ms, DC.Mem{b, rb, wb, db}, b, DC.mgF(t, es, fs, k, ms), {==}, hf, hF, hb, mgF_dec(t, es, fs, k, ms, ht, hf, hF))

def mgR.pick_dec(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +r: DR.Node, +ms: List<&2, DC.Mem>, +mb: DC.Mem, +b: DR.Node, +rest: Maybe<&2, List<&2, DC.Mem>>,
  hf: SH.AllFirst(ms, ms), +hr0: {SH.isroot(ms, r) == True{} : Bool}, +hF: {SH.isroot(ms, DR.NFrame{}) == True{} : Bool}, hb: {SH.isroot(ms, DC.Mem.r(mb)) == True{} : Bool},
  hne: {DC.node_eq(DC.Mem.r(mb), r) == False{} : Bool}, hr: OptDec(ms, rest)) -> OptDec(ms, DC.mgR.pick(m, es, fs, t, h, r, ms, mb, b, rest)):
  match m:
    case None{}:
      hr
    case Some{+w}:
      mg_dec(ms, r, HS.hs.der(es, fs, t, r, h, DR.gmul(w, DR.zdir(es, b))), w, mb, hf, hr0, hF, hb, hne)

def mgR.if_dec(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +r: DR.Node, +ms: List<&2, DC.Mem>, +mb: DC.Mem, +b: DR.Node, +rest: Maybe<&2, List<&2, DC.Mem>>,
  ef: {f == SV.bnot(DC.node_eq(DC.Mem.r(mb), r)) : Bool}, hf: SH.AllFirst(ms, ms), +hr0: {SH.isroot(ms, r) == True{} : Bool}, +hF: {SH.isroot(ms, DR.NFrame{}) == True{} : Bool},
  hb: {SH.isroot(ms, DC.Mem.r(mb)) == True{} : Bool}, hr: OptDec(ms, rest)) -> OptDec(ms, DC.mgR.if(f, es, fs, t, h, r, ms, mb, b, rest)):
  match f:
    case True{}:
      mgR.pick_dec(LB.hs.lab(es, fs, t, h, DR.zdir(es, b)), es, fs, t, h, r, ms, mb, b, rest, hf, hr0, hF, hb,
        bnot_t(DC.node_eq(DC.Mem.r(mb), r), Equal.sym(Bool, True{}, SV.bnot(DC.node_eq(DC.Mem.r(mb), r)), ef)), hr)
    case False{}:
      hr

def mgR_dec(sc: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +r: DR.Node, +ms: List<&2, DC.Mem>, ho: SH.RootsOk(sc, ms), +hf: SH.AllFirst(ms, ms),
  +hr0: {SH.isroot(ms, r) == True{} : Bool}, +hF: {SH.isroot(ms, DR.NFrame{}) == True{} : Bool}) -> OptDec(ms, DC.mgR(sc, es, fs, t, h, r, ms)):
  match sc:
    case Nil{}:
      Unit{}
    case Con{DC.Mem{+b, +rb, +wb, +db}, +tl}:
      (hb, ht) = ho
      mgR.if_dec(SV.bnot(DC.node_eq(rb, r)), es, fs, t, h, r, ms, DC.Mem{b, rb, wb, db}, b, DC.mgR(tl, es, fs, t, h, r, ms), {==}, hf, hr0, hF, hb, mgR_dec(tl, es, fs, t, h, r, ms, ht, hf, hr0, hF))

def mgs.root_dec(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +r: DR.Node, +ho: SH.RootsOk(DC.Sk.ms(s), DC.Sk.ms(s)), +hf: SH.AllFirst(DC.Sk.ms(s), DC.Sk.ms(s)),
  +hF: {SH.isroot(DC.Sk.ms(s), DR.NFrame{}) == True{} : Bool}, hr0: {SH.isroot(DC.Sk.ms(s), r) == True{} : Bool}) -> OptDec(DC.Sk.ms(s), DC.mgs.root(f, es, fs, t, s, r)):
  match f:
    case True{}:
      mgF_dec(DC.Sk.ms(s), es, fs, DC.Sk.k(s), DC.Sk.ms(s), ho, hf, hF)
    case False{}:
      mgR_dec(DC.Sk.ms(s), es, fs, t, DC.rhull(es, fs, t, s, r), r, DC.Sk.ms(s), ho, hf, hr0, hF)

def mgs.pick_dec(m: Maybe<&2, List<&2, DC.Mem>>, +ms: List<&2, DC.Mem>, hm: OptDec(ms, m), +rest: Maybe<&2, List<&2, DC.Mem>>, hr: OptDec(ms, rest)) -> OptDec(ms, DC.mgs.pick(m, rest)):
  match m:
    case None{}:
      hr
    case Some{+x}:
      hm

# the first merge takes one root away
def mgs_dec(rs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, ha: SH.AllRoot(rs, DC.Sk.ms(s)), +ho: SH.RootsOk(DC.Sk.ms(s), DC.Sk.ms(s)),
  +hf: SH.AllFirst(DC.Sk.ms(s), DC.Sk.ms(s)), +hF: {SH.isroot(DC.Sk.ms(s), DR.NFrame{}) == True{} : Bool}) -> OptDec(DC.Sk.ms(s), DC.mgs(rs, es, fs, t, s)):
  match rs:
    case Nil{}:
      Unit{}
    case Con{+r, +tl}:
      (hr0, ht) = ha
      mgs.pick_dec(DC.mgs.root(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r), DC.Sk.ms(s), mgs.root_dec(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r, ho, hf, hF, hr0),
        DC.mgs(tl, es, fs, t, s), mgs_dec(tl, es, fs, t, s, ht, ho, hf, hF))

# Links
# -----

def slot_snoc_le(ws: List<&2, DR.Lab>, +w: DR.Lab) -> {KA.natle(DC.slots(SH.wsnoc(ws, w)), DC.slots(ws)) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{w0, Nil{}}:
      {==}
    case Con{w0, Con{w1, t}}:
      {==}

def slot_snoc_lt(ws: List<&2, DR.Lab>, +w: DR.Lab, hq: {DC.qspan(ws, w) == False{} : Bool}) -> {KA.natle(1n+DC.slots(SH.wsnoc(ws, w)), DC.slots(ws)) == True{} : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{w0, Nil{}}:
      {==}
    case Con{w0, Con{w1, t}}:
      absurd({KA.natle(1n+DC.slots(SH.wsnoc(Con{w0, Con{w1, t}}, w)), 0n) == True{} : Bool}, KA.tf(hq))

def slot_le(f: Bool, +ws: List<&2, DR.Lab>, +w: DR.Lab) -> {KA.natle(DC.slots(SH.wsnoc_if(f, ws, w)), DC.slots(ws)) == True{} : Bool}:
  match f:
    case True{}:
      slot_snoc_le(ws, w)
    case False{}:
      KA.natle_refl(DC.slots(ws))

def lsc_le(bs: List<&2, DR.Node>, +ls: List<&2, DC.Link>, +c: Nat, +cx: Nat, +bx: DR.Node, +wx: DR.Lab, +dx: DR.Der)
  -> {KA.natle(DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, bs), DC.lslack.c(ls, c, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %Equal.sym(List<&2, DR.Lab>, DC.lstored(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, b), SH.wsnoc_if(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), DC.lstored(ls, c, b), wx), SH.lstored_snoc(ls, c, b, cx, bx, wx, dx))
        : {KA.natle(Nat.add(DC.slots(_), DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, t)), Nat.add(DC.slots(DC.lstored(ls, c, b)), DC.lslack.c(ls, c, t))) == True{} : Bool}
      KA.natle_add2(DC.slots(SH.wsnoc_if(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), DC.lstored(ls, c, b), wx)), DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, t), DC.slots(DC.lstored(ls, c, b)), DC.lslack.c(ls, c, t),
        slot_le(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), DC.lstored(ls, c, b), wx), lsc_le(t, ls, c, cx, bx, wx, dx))

def lsl_le(ids: List<&2, Nat>, +bs: List<&2, DR.Node>, +ls: List<&2, DC.Link>, +cx: Nat, +bx: DR.Node, +wx: DR.Lab, +dx: DR.Der)
  -> {KA.natle(DC.lslack(ids, bs, DC.lsnoc(ls, DC.Link{cx, bx, wx, dx})), DC.lslack(ids, bs, ls)) == True{} : Bool}:
  match ids:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      KA.natle_add2(DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, bs), DC.lslack(t, bs, DC.lsnoc(ls, DC.Link{cx, bx, wx, dx})), DC.lslack.c(ls, c, bs), DC.lslack(t, bs, ls),
        lsc_le(bs, ls, c, cx, bx, wx, dx), lsl_le(t, bs, ls, cx, bx, wx, dx))

def hq_rw(+ls: List<&2, DC.Link>, +c: Nat, +b: DR.Node, +cx: Nat, +bx: DR.Node, +wx: DR.Lab, ec: {cx == c : Nat}, eb: {bx == b : DR.Node},
  hq: {DC.qspan(DC.lstored(ls, cx, bx), wx) == False{} : Bool}) -> {DC.qspan(DC.lstored(ls, c, b), wx) == False{} : Bool}:
  %ec : {DC.qspan(DC.lstored(ls, _, b), wx) == False{} : Bool}
  %eb : {DC.qspan(DC.lstored(ls, cx, _), wx) == False{} : Bool}
  hq

def lsc_hd(+b: DR.Node, +ls: List<&2, DC.Link>, +c: Nat, +cx: Nat, +bx: DR.Node, +wx: DR.Lab, +ec: {cx == c : Nat}, +eb: {bx == b : DR.Node},
  hq: {DC.qspan(DC.lstored(ls, cx, bx), wx) == False{} : Bool}) -> {KA.natle(1n+DC.slots(SH.wsnoc_if(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), DC.lstored(ls, c, b), wx)), DC.slots(DC.lstored(ls, c, b))) == True{} : Bool}:
  %Equal.sym(Nat, cx, c, ec) : {KA.natle(1n+DC.slots(SH.wsnoc_if(SV.band(SV.eq(_, c), DC.node_eq(bx, b)), DC.lstored(ls, c, b), wx)), DC.slots(DC.lstored(ls, c, b))) == True{} : Bool}
  %Equal.sym(DR.Node, bx, b, eb) : {KA.natle(1n+DC.slots(SH.wsnoc_if(SV.band(SV.eq(c, c), DC.node_eq(_, b)), DC.lstored(ls, c, b), wx)), DC.slots(DC.lstored(ls, c, b))) == True{} : Bool}
  %Equal.sym(Bool, SV.eq(c, c), True{}, LP2.eq_refl(c)) : {KA.natle(1n+DC.slots(SH.wsnoc_if(SV.band(_, DC.node_eq(b, b)), DC.lstored(ls, c, b), wx)), DC.slots(DC.lstored(ls, c, b))) == True{} : Bool}
  %Equal.sym(Bool, DC.node_eq(b, b), True{}, SH.node_refl(b)) : {KA.natle(1n+DC.slots(SH.wsnoc_if(SV.band(True{}, _), DC.lstored(ls, c, b), wx)), DC.slots(DC.lstored(ls, c, b))) == True{} : Bool}
  slot_snoc_lt(DC.lstored(ls, c, b), wx, hq_rw(ls, c, b, cx, bx, wx, ec, eb, hq))

def lsc_lt.go(g: Bool, +b: DR.Node, +t: List<&2, DR.Node>, +ls: List<&2, DC.Link>, +c: Nat, +cx: Nat, +bx: DR.Node, +wx: DR.Lab, +dx: DR.Der, eg: {g == DC.node_eq(bx, b) : Bool},
  hb: {SV.bor(g, SH.nmem(bx, t)) == True{} : Bool}, +ec: {cx == c : Nat}, +hq: {DC.qspan(DC.lstored(ls, cx, bx), wx) == False{} : Bool},
  ih: {SH.nmem(bx, t) == True{} : Bool} -> {KA.natle(1n+DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, t), DC.lslack.c(ls, c, t)) == True{} : Bool})
  -> {KA.natle(1n+DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, Con{b, t}), DC.lslack.c(ls, c, Con{b, t})) == True{} : Bool}:
  match g:
    case True{}:
      %Equal.sym(List<&2, DR.Lab>, DC.lstored(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, b), SH.wsnoc_if(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), DC.lstored(ls, c, b), wx), SH.lstored_snoc(ls, c, b, cx, bx, wx, dx))
        : {KA.natle(1n+Nat.add(DC.slots(_), DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, t)), Nat.add(DC.slots(DC.lstored(ls, c, b)), DC.lslack.c(ls, c, t))) == True{} : Bool}
      KA.natle_add2(1n+DC.slots(SH.wsnoc_if(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), DC.lstored(ls, c, b), wx)), DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, t), DC.slots(DC.lstored(ls, c, b)), DC.lslack.c(ls, c, t),
        lsc_hd(b, ls, c, cx, bx, wx, ec, GN.node_eq_ok(bx, b, Equal.sym(Bool, True{}, DC.node_eq(bx, b), eg)), hq), lsc_le(t, ls, c, cx, bx, wx, dx))
    case False{}:
      %Equal.sym(List<&2, DR.Lab>, DC.lstored(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, b), SH.wsnoc_if(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), DC.lstored(ls, c, b), wx), SH.lstored_snoc(ls, c, b, cx, bx, wx, dx))
        : {KA.natle(1n+Nat.add(DC.slots(_), DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, t)), Nat.add(DC.slots(DC.lstored(ls, c, b)), DC.lslack.c(ls, c, t))) == True{} : Bool}
      %Equal.sym(Nat, 1n+Nat.add(DC.slots(SH.wsnoc_if(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), DC.lstored(ls, c, b), wx)), DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, t)),
          Nat.add(DC.slots(SH.wsnoc_if(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), DC.lstored(ls, c, b), wx)), 1n+DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, t)),
          LN.add_succ(DC.slots(SH.wsnoc_if(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), DC.lstored(ls, c, b), wx)), DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, t)))
        : {KA.natle(_, Nat.add(DC.slots(DC.lstored(ls, c, b)), DC.lslack.c(ls, c, t))) == True{} : Bool}
      KA.natle_add2(DC.slots(SH.wsnoc_if(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), DC.lstored(ls, c, b), wx)), 1n+DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, t), DC.slots(DC.lstored(ls, c, b)), DC.lslack.c(ls, c, t),
        slot_le(SV.band(SV.eq(cx, c), DC.node_eq(bx, b)), DC.lstored(ls, c, b), wx), ih(hb))

def lsc_lt(bs: List<&2, DR.Node>, +ls: List<&2, DC.Link>, +c: Nat, +cx: Nat, +bx: DR.Node, +wx: DR.Lab, +dx: DR.Der, +ec: {cx == c : Nat}, hb: {SH.nmem(bx, bs) == True{} : Bool},
  +hq: {DC.qspan(DC.lstored(ls, cx, bx), wx) == False{} : Bool}) -> {KA.natle(1n+DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, bs), DC.lslack.c(ls, c, bs)) == True{} : Bool}:
  match bs:
    case Nil{}:
      absurd({KA.natle(1n+0n, 0n) == True{} : Bool}, KA.ft(hb))
    case Con{+b, +t}:
      lsc_lt.go(DC.node_eq(bx, b), b, t, ls, c, cx, bx, wx, dx, {==}, hb, ec, hq, h => lsc_lt(t, ls, c, cx, bx, wx, dx, ec, h, hq))

def lsl_lt.go(g: Bool, +c: Nat, +t: List<&2, Nat>, +bs: List<&2, DR.Node>, +ls: List<&2, DC.Link>, +cx: Nat, +bx: DR.Node, +wx: DR.Lab, +dx: DR.Der, eg: {g == SV.eq(cx, c) : Bool},
  hc: {SV.bor(g, RF.imem(cx, t)) == True{} : Bool}, +hb: {SH.nmem(bx, bs) == True{} : Bool}, +hq: {DC.qspan(DC.lstored(ls, cx, bx), wx) == False{} : Bool},
  ih: {RF.imem(cx, t) == True{} : Bool} -> {KA.natle(1n+DC.lslack(t, bs, DC.lsnoc(ls, DC.Link{cx, bx, wx, dx})), DC.lslack(t, bs, ls)) == True{} : Bool})
  -> {KA.natle(1n+DC.lslack(Con{c, t}, bs, DC.lsnoc(ls, DC.Link{cx, bx, wx, dx})), DC.lslack(Con{c, t}, bs, ls)) == True{} : Bool}:
  match g:
    case True{}:
      KA.natle_add2(1n+DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, bs), DC.lslack(t, bs, DC.lsnoc(ls, DC.Link{cx, bx, wx, dx})), DC.lslack.c(ls, c, bs), DC.lslack(t, bs, ls),
        lsc_lt(bs, ls, c, cx, bx, wx, dx, LP2.eq_ok(cx, c, Equal.sym(Bool, True{}, SV.eq(cx, c), eg)), hb, hq), lsl_le(t, bs, ls, cx, bx, wx, dx))
    case False{}:
      %Equal.sym(Nat, 1n+Nat.add(DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, bs), DC.lslack(t, bs, DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}))),
          Nat.add(DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, bs), 1n+DC.lslack(t, bs, DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}))),
          LN.add_succ(DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, bs), DC.lslack(t, bs, DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}))))
        : {KA.natle(_, Nat.add(DC.lslack.c(ls, c, bs), DC.lslack(t, bs, ls))) == True{} : Bool}
      KA.natle_add2(DC.lslack.c(DC.lsnoc(ls, DC.Link{cx, bx, wx, dx}), c, bs), 1n+DC.lslack(t, bs, DC.lsnoc(ls, DC.Link{cx, bx, wx, dx})), DC.lslack.c(ls, c, bs), DC.lslack(t, bs, ls),
        lsc_le(bs, ls, c, cx, bx, wx, dx), ih(hc))

# a fresh link for a pair in range takes a slot
def lsl_lt(ids: List<&2, Nat>, +bs: List<&2, DR.Node>, +ls: List<&2, DC.Link>, +cx: Nat, +bx: DR.Node, +wx: DR.Lab, +dx: DR.Der, hc: {RF.imem(cx, ids) == True{} : Bool},
  +hb: {SH.nmem(bx, bs) == True{} : Bool}, +hq: {DC.qspan(DC.lstored(ls, cx, bx), wx) == False{} : Bool})
  -> {KA.natle(1n+DC.lslack(ids, bs, DC.lsnoc(ls, DC.Link{cx, bx, wx, dx})), DC.lslack(ids, bs, ls)) == True{} : Bool}:
  match ids:
    case Nil{}:
      absurd({KA.natle(1n+0n, 0n) == True{} : Bool}, KA.ft(hc))
    case Con{+c, +t}:
      lsl_lt.go(SV.eq(cx, c), c, t, bs, ls, cx, bx, wx, dx, {==}, hc, hb, hq, h => lsl_lt(t, bs, ls, cx, bx, wx, dx, h, hb, hq))

# The links found are in range
# ----------------------------

def PIn(+ids: List<&2, Nat>, +bs: List<&2, DR.Node>, m: Maybe<&2, DC.Link>) -> Data:
  match m:
    case None{}:
      Unit
    case Some{DC.Link{+c, +b, w, d}}:
      SK.Both({RF.imem(c, ids) == True{} : Bool}, {SH.nmem(b, bs) == True{} : Bool})

def lkmk_in(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +c: Nat, +rep: DC.Rep, +b: DR.Node, +rest: Maybe<&2, DC.Link>, +ids: List<&2, Nat>, +bs: List<&2, DR.Node>,
  hc: {RF.imem(c, ids) == True{} : Bool}, hb: {SH.nmem(b, bs) == True{} : Bool}, hr: PIn(ids, bs, rest)) -> PIn(ids, bs, DC.lk.mk(m, es, fs, t, k, c, rep, b, rest)):
  match m:
    case None{}:
      hr
    case Some{+w}:
      (hc, hb)

def lkci_in(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +rep: DC.Rep, +b: DR.Node, +rest: Maybe<&2, DC.Link>, +ids: List<&2, Nat>, +bs: List<&2, DR.Node>,
  hc: {RF.imem(c, ids) == True{} : Bool}, hb: {SH.nmem(b, bs) == True{} : Bool}, hr: PIn(ids, bs, rest)) -> PIn(ids, bs, DC.lk.c.if(f, es, fs, t, s, c, rep, b, rest)):
  match f:
    case True{}:
      hr
    case False{}:
      lkmk_in(DC.lk.first(DC.rep.basis(rep, es, fs, t, DR.zdir(es, b)), DC.lstored(DC.Sk.ls(s), c, b)), es, fs, t, DC.Sk.k(s), c, rep, b, rest, ids, bs, hc, hb, hr)

def lkc_in(bs0: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +rep: DC.Rep, +ids: List<&2, Nat>, +bs: List<&2, DR.Node>,
  +hc: {RF.imem(c, ids) == True{} : Bool}, ha: SH.AllNmem(bs0, bs)) -> PIn(ids, bs, DC.lk.c(bs0, es, fs, t, s, c, rep)):
  match bs0:
    case Nil{}:
      Unit{}
    case Con{+b, +tl}:
      (hb, ht) = ha
      lkci_in(DC.node_eq(b, DR.NSeg{c}), es, fs, t, s, c, rep, b, DC.lk.c(tl, es, fs, t, s, c, rep), ids, bs, hc, hb, lkc_in(tl, es, fs, t, s, c, rep, ids, bs, hc, ht))

def lkrmk_in(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +r: DR.Node, +rest: Maybe<&2, DC.Link>, +ids: List<&2, Nat>, +bs: List<&2, DR.Node>,
  hc: {RF.imem(c, ids) == True{} : Bool}, hb: {SH.nmem(r, bs) == True{} : Bool}, hr: PIn(ids, bs, rest)) -> PIn(ids, bs, DC.lk.r.mk(m, es, fs, t, s, c, r, rest)):
  match m:
    case None{}:
      hr
    case Some{+w}:
      (hc, hb)

def lkr_in(rs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +ids: List<&2, Nat>, +bs: List<&2, DR.Node>,
  +hc: {RF.imem(c, ids) == True{} : Bool}, ha: SH.AllNmem(rs, bs)) -> PIn(ids, bs, DC.lk.r(rs, es, fs, t, s, c)):
  match rs:
    case Nil{}:
      Unit{}
    case Con{+r, +tl}:
      (hb, ht) = ha
      lkrmk_in(DC.lk.r.first(DC.lk.r.basis(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r, DR.zseg(es, c)), DC.lstored(DC.Sk.ls(s), c, r)), es, fs, t, s, c, r, DC.lk.r(tl, es, fs, t, s, c), ids, bs,
        hc, hb, lkr_in(tl, es, fs, t, s, c, ids, bs, hc, ht))

def lfirst_in(m: Maybe<&2, DC.Link>, +ids: List<&2, Nat>, +bs: List<&2, DR.Node>, hm: PIn(ids, bs, m), +rest: Maybe<&2, DC.Link>, hr: PIn(ids, bs, rest)) -> PIn(ids, bs, DC.lfirst(m, rest)):
  match m:
    case None{}:
      hr
    case Some{+x}:
      hm

def lksg_in(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +c: Nat, +rep: DC.Rep, +bs0: List<&2, DR.Node>, +rs: List<&2, DR.Node>, +rest: Maybe<&2, DC.Link>,
  +ids: List<&2, Nat>, +bs: List<&2, DR.Node>, +hc: {RF.imem(c, ids) == True{} : Bool}, hb0: SH.AllNmem(bs0, bs), hrs: SH.AllNmem(rs, bs), hr: PIn(ids, bs, rest))
  -> PIn(ids, bs, DC.lks.go(f, es, fs, t, s, c, rep, bs0, rs, rest)):
  match f:
    case True{}:
      hr
    case False{}:
      lfirst_in(DC.lk.c(bs0, es, fs, t, s, c, rep), ids, bs, lkc_in(bs0, es, fs, t, s, c, rep, ids, bs, hc, hb0), DC.lfirst(DC.lk.r(rs, es, fs, t, s, c), rest),
        lfirst_in(DC.lk.r(rs, es, fs, t, s, c), ids, bs, lkr_in(rs, es, fs, t, s, c, ids, bs, hc, hrs), rest, hr))

def pin_widen(m: Maybe<&2, DC.Link>, +i: Nat, +ids: List<&2, Nat>, +bs: List<&2, DR.Node>, h: PIn(ids, bs, m)) -> PIn(Con{i, ids}, bs, m):
  match m:
    case None{}:
      Unit{}
    case Some{DC.Link{+c, +b, w, d}}:
      (hc, hb) = h
      (SH.bor_r(SV.eq(c, i), RF.imem(c, ids), hc), hb)

def imem_hd(+c: Nat, +tl: List<&2, Nat>) -> {RF.imem(c, Con{c, tl}) == True{} : Bool}:
  %Equal.sym(Bool, SV.eq(c, c), True{}, LP2.eq_refl(c)) : {SV.bor(_, RF.imem(c, tl)) == True{} : Bool}
  {==}

# the first new link is for a segment among cids and a node among bs
def lks_in(cids: List<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +bs0: List<&2, DR.Node>, +rs: List<&2, DR.Node>, +bs: List<&2, DR.Node>,
  +hb0: SH.AllNmem(bs0, bs), +hrs: SH.AllNmem(rs, bs)) -> PIn(cids, bs, DC.lks(cids, es, fs, t, s, bs0, rs)):
  match cids:
    case Nil{}:
      Unit{}
    case Con{+c, +tl}:
      lksg_in(DC.fullc(es, DC.Sk.k(s), c), es, fs, t, s, c, DC.crep(es, fs, t, s, c), bs0, rs, DC.lks(tl, es, fs, t, s, bs0, rs), Con{c, tl}, bs, imem_hd(c, tl), hb0, hrs,
        pin_widen(DC.lks(tl, es, fs, t, s, bs0, rs), c, tl, bs, lks_in(tl, es, fs, t, s, bs0, rs, bs, hb0, hrs)))

def roots_in.pick(f: Bool, +a: DR.Node, +rest: List<&2, DR.Node>, +ns: List<&2, DR.Node>, ha: {SH.nmem(a, ns) == True{} : Bool}, hr: SH.AllNmem(rest, ns)) -> SH.AllNmem(DC.roots.pick(f, a, rest), ns):
  match f:
    case True{}:
      (ha, hr)
    case False{}:
      hr

# the roots are among the records' nodes
def roots_in(sc: List<&2, DC.Mem>, +ns: List<&2, DR.Node>, h: SH.RecN(sc, ns)) -> SH.AllNmem(DC.roots(sc), ns):
  match sc:
    case Nil{}:
      Unit{}
    case Con{DC.Mem{+a, +r, +w, +d}, +t}:
      (e0, ht) = h
      roots_in.pick(DC.node_eq(a, r), a, DC.roots(t), ns, e0, roots_in(t, ns, ht))

def imem_tl(+c: Nat, +i: Nat, +t: List<&2, Nat>, h: {RF.imem(c, t) == True{} : Bool}) -> {RF.imem(c, Con{i, t}) == True{} : Bool}:
  SH.bor_r(SV.eq(c, i), RF.imem(c, t), h)

def cids_sub.t(g: Bool, +c: Nat, +i: Nat, +t: List<&2, Nat>, +rest: List<&2, Nat>, eg: {g == SV.eq(c, i) : Bool}, h: {SV.bor(g, RF.imem(c, rest)) == True{} : Bool},
  ih: {RF.imem(c, rest) == True{} : Bool} -> {RF.imem(c, t) == True{} : Bool}) -> {RF.imem(c, Con{i, t}) == True{} : Bool}:
  match g:
    case True{}:
      %eg : {SV.bor(_, RF.imem(c, t)) == True{} : Bool}
      {==}
    case False{}:
      imem_tl(c, i, t, ih(h))

def cids_sub.pick(f: Bool, +c: Nat, +i: Nat, +t: List<&2, Nat>, +rest: List<&2, Nat>, h: {RF.imem(c, DC.ids.pick(f, i, rest)) == True{} : Bool},
  ih: {RF.imem(c, rest) == True{} : Bool} -> {RF.imem(c, t) == True{} : Bool}) -> {RF.imem(c, Con{i, t}) == True{} : Bool}:
  match f:
    case True{}:
      cids_sub.t(SV.eq(c, i), c, i, t, rest, {==}, h, ih)
    case False{}:
      imem_tl(c, i, t, ih(h))

# the collapsed segments are among the segments
def cids_sub(ids: List<&2, Nat>, +c: Nat, +es: List<&2, SK.Ent>, +cs: DC.SP, h: {RF.imem(c, DC.cids(ids, es, cs)) == True{} : Bool}) -> {RF.imem(c, ids) == True{} : Bool}:
  match ids:
    case Nil{}:
      h
    case Con{+i, +t}:
      cids_sub.pick(DC.coll(es, cs, i), c, i, t, DC.cids(t, es, cs), h, x => cids_sub(t, c, es, cs, x))
