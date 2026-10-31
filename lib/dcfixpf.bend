# bend-cad: what the closure's fixpoint tells (PLAN-sk13b B3): a run keeps
# the state's invariant (lib/dcroundpf.bend) and its shape
# (lib/dcshapepf.bend), and an OFix state comes with every check of its
# last round, each in its Bool form: 1 not in K, no open segment void, F's
# generators' imaginary parts in K, no complex line at a free root, no
# merge, no new link.
# Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./kspace.bend as KS
import ./dclose.bend as DC
import ./dcopenpf.bend as OP
import ./dcinvpf.bend as IV
import ./dcroundpf.bend as RD
import ./dcsetpf.bend as ST
import ./dcshapepf.bend as SH
import ./dfastpf.bend as FP

# the checks a fixpoint passed
def Fx(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk) -> Data:
  SK.Both({KS.ks.inb(DC.Sk.k(s), DR.cst(DR.qo())) == False{} : Bool},
  SK.Both({DC.voidseg(ids, es, cs, DC.Sk.k(s)) == None{} : Maybe<&2, Nat>},
  SK.Both({DC.fback(DC.rgens(fs, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, DC.Sk.k(s)) == None{} : Maybe<&2, DR.Der>},
  SK.Both({DC.clxs(DC.roots(DC.Sk.ms(s)), es, fs, t, s) == None{} : Maybe<&2, DR.Der>},
  SK.Both({DC.mgs(DC.roots(DC.Sk.ms(s)), es, fs, t, s) == None{} : Maybe<&2, List<&2, DC.Mem>>},
    {DC.lks(DC.cids(ids, es, cs), es, fs, t, s, Con{DR.NFrame{}, DC.snodes(ids)}, DC.roots(DC.Sk.ms(s))) == None{} : Maybe<&2, DC.Link>})))))

def ShOut(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, o: DC.Out) -> Data:
  match o:
    case DC.OStep{+s}:
      SH.ShInv(es, fs, cs, ids, s)
    case DC.OFix{+s}:
      SK.Both(SH.ShInv(es, fs, cs, ids, s), Fx(es, fs, t, cs, ids, s))
    case DC.OOne{d}:
      Unit
    case DC.OVoid{sg, dr, di}:
      Unit

def r.c4_sh(m: Maybe<&2, DC.Link>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk,
  em: {m == DC.lks(DC.cids(ids, es, cs), es, fs, t, s, Con{DR.NFrame{}, DC.snodes(ids)}, DC.roots(DC.Sk.ms(s))) : Maybe<&2, DC.Link>}, hm: SH.Fr(DC.Sk.ls(s), m),
  +hsh: SH.ShInv(es, fs, cs, ids, s), +e1: {KS.ks.inb(DC.Sk.k(s), DR.cst(DR.qo())) == False{} : Bool}, +e2: {DC.voidseg(ids, es, cs, DC.Sk.k(s)) == None{} : Maybe<&2, Nat>},
  +e3: {DC.fback(DC.rgens(fs, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, DC.Sk.k(s)) == None{} : Maybe<&2, DR.Der>},
  +e4: {DC.clxs(DC.roots(DC.Sk.ms(s)), es, fs, t, s) == None{} : Maybe<&2, DR.Der>}, +e5: {DC.mgs(DC.roots(DC.Sk.ms(s)), es, fs, t, s) == None{} : Maybe<&2, List<&2, DC.Mem>>})
  -> ShOut(es, fs, t, cs, ids, DC.r.c4(m, s)):
  match m:
    case None{}:
      (hsh, (e1, (e2, (e3, (e4, (e5, Equal.sym(Maybe<&2, DC.Link>, None{}, DC.lks(DC.cids(ids, es, cs), es, fs, t, s, Con{DR.NFrame{}, DC.snodes(ids)}, DC.roots(DC.Sk.ms(s))), em)))))))
    case Some{+l}:
      (SH.shi.m(es, fs, cs, ids, s, hsh), (SH.shi.k(es, fs, cs, ids, s, hsh), SH.pl_snoc(DC.Sk.ls(s), l, SH.shi.l(es, fs, cs, ids, s, hsh), hm)))

def r.c3_sh(m: Maybe<&2, List<&2, DC.Mem>>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk,
  em: {m == DC.mgs(DC.roots(DC.Sk.ms(s)), es, fs, t, s) : Maybe<&2, List<&2, DC.Mem>>}, hm: SH.OptSh(es, cs, ids, m),
  +hsh: SH.ShInv(es, fs, cs, ids, s), +e1: {KS.ks.inb(DC.Sk.k(s), DR.cst(DR.qo())) == False{} : Bool}, +e2: {DC.voidseg(ids, es, cs, DC.Sk.k(s)) == None{} : Maybe<&2, Nat>},
  +e3: {DC.fback(DC.rgens(fs, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, DC.Sk.k(s)) == None{} : Maybe<&2, DR.Der>},
  +e4: {DC.clxs(DC.roots(DC.Sk.ms(s)), es, fs, t, s) == None{} : Maybe<&2, DR.Der>})
  -> ShOut(es, fs, t, cs, ids, DC.r.c3(m, es, fs, t, cs, ids, s)):
  match m:
    case None{}:
      r.c4_sh(DC.lks(DC.cids(ids, es, cs), es, fs, t, s, Con{DR.NFrame{}, DC.snodes(ids)}, DC.roots(DC.Sk.ms(s))), es, fs, t, cs, ids, s, {==},
        SH.lks_fr(DC.cids(ids, es, cs), es, fs, t, s, Con{DR.NFrame{}, DC.snodes(ids)}, DC.roots(DC.Sk.ms(s))), hsh, e1, e2, e3, e4,
        Equal.sym(Maybe<&2, List<&2, DC.Mem>>, None{}, DC.mgs(DC.roots(DC.Sk.ms(s)), es, fs, t, s), em))
    case Some{+ms}:
      (hm, (SH.shi.k(es, fs, cs, ids, s, hsh), SH.shi.l(es, fs, cs, ids, s, hsh)))

def r.c2_sh(m: Maybe<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk,
  em: {m == DC.clxs(DC.roots(DC.Sk.ms(s)), es, fs, t, s) : Maybe<&2, DR.Der>}, +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)),
  +hsh: SH.ShInv(es, fs, cs, ids, s), +e1: {KS.ks.inb(DC.Sk.k(s), DR.cst(DR.qo())) == False{} : Bool}, +e2: {DC.voidseg(ids, es, cs, DC.Sk.k(s)) == None{} : Maybe<&2, Nat>},
  +e3: {DC.fback(DC.rgens(fs, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, DC.Sk.k(s)) == None{} : Maybe<&2, DR.Der>})
  -> ShOut(es, fs, t, cs, ids, DC.r.c2(m, es, fs, t, cs, ids, s)):
  match m:
    case None{}:
      r.c3_sh(DC.mgs(DC.roots(DC.Sk.ms(s)), es, fs, t, s), es, fs, t, cs, ids, s, {==},
        SH.mgs_sh(DC.roots(DC.Sk.ms(s)), es, fs, cs, ids, t, s, SH.shi.m(es, fs, cs, ids, s, hsh), SH.roots_root(DC.Sk.ms(s), DC.Sk.ms(s), SH.sh.af(es, cs, ids, DC.Sk.ms(s), SH.shi.m(es, fs, cs, ids, s, hsh)))),
        hsh, e1, e2, e3, Equal.sym(Maybe<&2, DR.Der>, None{}, DC.clxs(DC.roots(DC.Sk.ms(s)), es, fs, t, s), em))
    case Some{+d}:
      (SH.shi.m(es, fs, cs, ids, s, hsh), (SH.kf_add(fs, es, fs, DC.Sk.k(s), d, ST.kri(es, fs, ctx, t, DC.Sk.k(s), hk), SH.shi.k(es, fs, cs, ids, s, hsh)), SH.shi.l(es, fs, cs, ids, s, hsh)))

def r.c1_sh(m: Maybe<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk,
  em: {m == DC.fback(DC.rgens(fs, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, DC.Sk.k(s)) : Maybe<&2, DR.Der>}, +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)),
  +hsh: SH.ShInv(es, fs, cs, ids, s), +e1: {KS.ks.inb(DC.Sk.k(s), DR.cst(DR.qo())) == False{} : Bool}, +e2: {DC.voidseg(ids, es, cs, DC.Sk.k(s)) == None{} : Maybe<&2, Nat>})
  -> ShOut(es, fs, t, cs, ids, DC.r.c1(m, es, fs, t, cs, ids, s)):
  match m:
    case None{}:
      r.c2_sh(DC.clxs(DC.roots(DC.Sk.ms(s)), es, fs, t, s), es, fs, ctx, t, cs, ids, s, {==}, hk, hsh, e1, e2,
        Equal.sym(Maybe<&2, DR.Der>, None{}, DC.fback(DC.rgens(fs, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, DC.Sk.k(s)), em))
    case Some{+d}:
      (SH.shi.m(es, fs, cs, ids, s, hsh), (SH.kf_add(fs, es, fs, DC.Sk.k(s), d, ST.kri(es, fs, ctx, t, DC.Sk.k(s), hk), SH.shi.k(es, fs, cs, ids, s, hsh)), SH.shi.l(es, fs, cs, ids, s, hsh)))

def r.e2_sh(m: Maybe<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk,
  em: {m == DC.voidseg(ids, es, cs, DC.Sk.k(s)) : Maybe<&2, Nat>}, +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)),
  +hsh: SH.ShInv(es, fs, cs, ids, s), +e1: {KS.ks.inb(DC.Sk.k(s), DR.cst(DR.qo())) == False{} : Bool})
  -> ShOut(es, fs, t, cs, ids, DC.r.e2(m, es, fs, t, cs, ids, s)):
  match m:
    case None{}:
      r.c1_sh(DC.fback(DC.rgens(fs, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, DC.Sk.k(s)), es, fs, ctx, t, cs, ids, s, {==}, hk, hsh, e1,
        Equal.sym(Maybe<&2, Nat>, None{}, DC.voidseg(ids, es, cs, DC.Sk.k(s)), em))
    case Some{+g}:
      Unit{}

def r.e1_sh(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk,
  ef: {f == KS.ks.inb(DC.Sk.k(s), DR.cst(DR.qo())) : Bool}, +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hsh: SH.ShInv(es, fs, cs, ids, s))
  -> ShOut(es, fs, t, cs, ids, DC.r.e1(f, es, fs, t, cs, ids, s)):
  match f:
    case True{}:
      Unit{}
    case False{}:
      r.e2_sh(DC.voidseg(ids, es, cs, DC.Sk.k(s)), es, fs, ctx, t, cs, ids, s, {==}, hk, hsh, Equal.sym(Bool, False{}, KS.ks.inb(DC.Sk.k(s), DR.cst(DR.qo())), ef))

# a round keeps the shape, and a fixpoint comes with its checks
def round_sh(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +s: DC.Sk, +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)),
  +hsh: SH.ShInv(es, fs, OP.cspan(ctx), ids, s)) -> ShOut(es, fs, t, OP.cspan(ctx), ids, DC.round(es, fs, t, OP.cspan(ctx), ids, s)):
  r.e1_sh(KS.ks.inb(DC.Sk.k(s), DR.cst(DR.qo())), es, fs, ctx, t, OP.cspan(ctx), ids, s, {==}, hk, hsh)

# The run
# -------

def FixOut(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, o: DC.Out) -> Data:
  match o:
    case DC.OStep{+s}:
      SK.Both(RD.SkInv(es, fs, ctx, t, s), SH.ShInv(es, fs, OP.cspan(ctx), ids, s))
    case DC.OFix{+s}:
      SK.Both(RD.SkInv(es, fs, ctx, t, s), SK.Both(SH.ShInv(es, fs, OP.cspan(ctx), ids, s), Fx(es, fs, t, OP.cspan(ctx), ids, s)))
    case DC.OOne{d}:
      Unit
    case DC.OVoid{sg, dr, di}:
      Unit

def fix_of(o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>,
  h1: RD.OutInv(es, fs, ctx, t, o), h2: ShOut(es, fs, t, OP.cspan(ctx), ids, o)) -> FixOut(es, fs, ctx, t, ids, o):
  match o:
    case DC.OStep{+s}:
      (h1, h2)
    case DC.OFix{+s}:
      (h1, h2)
    case DC.OOne{+d}:
      Unit{}
    case DC.OVoid{+sg, +dr, +di}:
      Unit{}

def skinv_k(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, h: RD.SkInv(es, fs, ctx, t, s)) -> IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)):
  (a, r1) = h
  a

def run_fix(fuel: Nat, o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>,
  ho: FixOut(es, fs, ctx, t, ids, o), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}) -> FixOut(es, fs, ctx, t, ids, DC.run(fuel, o, es, fs, t, OP.cspan(ctx), ids)):
  match fuel o:
    case 0n o:
      ho
    case 1n+f DC.OStep{+s}:
      (+a, b) = ho
      run_fix(f, DC.round(es, fs, t, OP.cspan(ctx), ids, s), es, fs, ctx, t, ids,
        fix_of(DC.round(es, fs, t, OP.cspan(ctx), ids, s), es, fs, ctx, t, ids, RD.round_ok(es, fs, ctx, t, ids, s, a, hz, hb), round_sh(es, fs, ctx, t, ids, s, skinv_k(es, fs, ctx, t, s, a), b)),
        hz, hb)
    case 1n+f DC.OFix{+s}:
      ho
    case 1n+f DC.OOne{+d}:
      ho
    case 1n+f DC.OVoid{+sg, +dr, +di}:
      ho

# whatever the closure returns keeps the invariant and the shape, and a
# fixpoint comes with its last round's checks
def dclose_fix(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +fuel: Nat, +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> FixOut(es, fs, ctx, t, DC.segids(es), DC.dclose(es, fs, ctx, t, fuel)):
  %Equal.sym(DC.Out, DC.dclose(es, fs, ctx, t, fuel), DC.dclose_ref(es, fs, ctx, t, fuel), FP.dclose_eq(es, fs, ctx, t, fuel)) : FixOut(es, fs, ctx, t, DC.segids(es), _)
  run_fix(fuel, DC.OStep{DC.sk0(es, fs, OP.cspan(ctx))}, es, fs, ctx, t, DC.segids(es), (RD.sk0_ok(es, fs, ctx, t, hz, hb), SH.sk0_sh(es, fs, OP.cspan(ctx))), hz, hb)

# a fixpoint the closure returned
def fix_at(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, fuel: Nat, +s: DC.Sk, eo: {DC.dclose(es, fs, ctx, t, fuel) == DC.OFix{s} : DC.Out},
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}) -> FixOut(es, fs, ctx, t, DC.segids(es), DC.OFix{s}):
  %eo : FixOut(es, fs, ctx, t, DC.segids(es), _)
  dclose_fix(es, fs, ctx, t, fuel, hz, hb)
