# bend-cad: the closure stops (PLAN-sk13b B3, termination). The measure mu
# adds the bases' monomials not yet a K pivot (lib/dckslpf.bend), the
# records that are their own root, and the links still possible
# (lib/dcslotpf.bend). Every round that does not stop takes it down:
# frame-back and complex-line rounds add to K a generator in the bases'
# span (lib/dcgspanpf.bend) that K lacks (lib/dcclprogpf.bend), so a new
# pivot among the bases' monomials; a merge takes a root away; a link takes
# a slot. The first state's measure is below DC.dfuel, so the run with that
# fuel never ends on OStep (dclose_term). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as LP2
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./spanpf.bend as SN
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcopenpf.bend as OP
import ./dcinvpf.bend as IV
import ./dcgenpf.bend as GN
import ./dcsetpf.bend as ST
import ./dcroundpf.bend as RD
import ./dcshapepf.bend as SH
import ./dcfixpf.bend as FX
import ./dcreprpf.bend as RR
import ./dcbasepf.bend as BS
import ./dckslpf.bend as KL
import ./dcslotpf.bend as SL
import ./dcgspanpf.bend as GS
import ./dcclprogpf.bend as CP
import ./dfastpf.bend as FP

def absurd(-A: Type, x: Empty) -> A:
  match x:

# The measure
# -----------

def bs(+ids: List<&2, Nat>) -> List<&2, DR.Node>:
  Con{DR.NFrame{}, DC.snodes(ids)}

def mu(+M: List<&2, List<&2, Nat>>, +ids: List<&2, Nat>, +s: DC.Sk) -> Nat:
  Nat.add(KL.kslack(M, KL.pivs(KS.ks.rows(DC.Sk.k(s)))), Nat.add(SL.rcount(DC.Sk.ms(s)), DC.lslack(ids, bs(ids), DC.Sk.ls(s))))

def lt3_a(+a2: Nat, +a: Nat, +X: Nat, h: {KA.natle(1n+a2, a) == True{} : Bool}) -> {KA.natle(1n+Nat.add(a2, X), Nat.add(a, X)) == True{} : Bool}:
  KA.natle_add_rr(1n+a2, a, X, h)

def lt3_b(+a: Nat, +b2: Nat, +b: Nat, +c: Nat, h: {KA.natle(1n+b2, b) == True{} : Bool}) -> {KA.natle(1n+Nat.add(a, Nat.add(b2, c)), Nat.add(a, Nat.add(b, c))) == True{} : Bool}:
  %Equal.sym(Nat, 1n+Nat.add(a, Nat.add(b2, c)), Nat.add(a, 1n+Nat.add(b2, c)), LN.add_succ(a, Nat.add(b2, c))) : {KA.natle(_, Nat.add(a, Nat.add(b, c))) == True{} : Bool}
  KA.natle_add_mono(a, 1n+Nat.add(b2, c), Nat.add(b, c), KA.natle_add_rr(1n+b2, b, c, h))

def lt3_c(+a: Nat, +b: Nat, +c2: Nat, +c: Nat, h: {KA.natle(1n+c2, c) == True{} : Bool}) -> {KA.natle(1n+Nat.add(a, Nat.add(b, c2)), Nat.add(a, Nat.add(b, c))) == True{} : Bool}:
  %Equal.sym(Nat, 1n+Nat.add(a, Nat.add(b, c2)), Nat.add(a, 1n+Nat.add(b, c2)), LN.add_succ(a, Nat.add(b, c2))) : {KA.natle(_, Nat.add(a, Nat.add(b, c))) == True{} : Bool}
  %Equal.sym(Nat, 1n+Nat.add(b, c2), Nat.add(b, 1n+c2), LN.add_succ(b, c2)) : {KA.natle(Nat.add(a, _), Nat.add(a, Nat.add(b, c))) == True{} : Bool}
  KA.natle_add_mono(a, Nat.add(b, 1n+c2), Nat.add(b, c), KA.natle_add_mono(b, 1n+c2, c, h))

# A round
# -------

# a round that does not stop takes the measure down; K stays in the span
def Step(+M: List<&2, List<&2, Nat>>, +ids: List<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +s: DC.Sk, o: DC.Out) -> Data:
  match o:
    case DC.OStep{+s2}:
      SK.Both({KA.natle(1n+mu(M, ids, s2), mu(M, ids, s)) == True{} : Bool}, GS.KSpan(es, fs, DC.Sk.k(s2)))
    case DC.OFix{+s2}:
      GS.KSpan(es, fs, DC.Sk.k(s2))
    case DC.OOne{d}:
      Unit
    case DC.OVoid{g, dr, di}:
      Unit

def c4_link(l: DC.Link, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk, hf: SH.Fr(DC.Sk.ls(s), Some{l}), hp: SL.PIn(DC.cids(ids, es, cs), bs(ids), Some{l}),
  hk: GS.KSpan(es, fs, DC.Sk.k(s))) -> Step(DC.kmons(DC.bases(es, fs)), ids, es, fs, s, DC.OStep{DC.Sk{DC.Sk.k(s), DC.Sk.ms(s), DC.lsnoc(DC.Sk.ls(s), l)}}):
  match l:
    case DC.Link{+cx, +bx, +wx, +dx}:
      (hc, hb) = hp
      (lt3_c(KL.kslack(DC.kmons(DC.bases(es, fs)), KL.pivs(KS.ks.rows(DC.Sk.k(s)))), SL.rcount(DC.Sk.ms(s)), DC.lslack(ids, bs(ids), DC.lsnoc(DC.Sk.ls(s), DC.Link{cx, bx, wx, dx})), DC.lslack(ids, bs(ids), DC.Sk.ls(s)),
         SL.lsl_lt(ids, bs(ids), DC.Sk.ls(s), cx, bx, wx, dx, SL.cids_sub(ids, cx, es, cs, hc), hb, hf)), hk)

def r.c4_t(m: Maybe<&2, DC.Link>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk, hf: SH.Fr(DC.Sk.ls(s), m), hp: SL.PIn(DC.cids(ids, es, cs), bs(ids), m),
  hk: GS.KSpan(es, fs, DC.Sk.k(s))) -> Step(DC.kmons(DC.bases(es, fs)), ids, es, fs, s, DC.r.c4(m, s)):
  match m:
    case None{}:
      hk
    case Some{+l}:
      c4_link(l, es, fs, cs, ids, s, hf, hp, hk)

def r.c3_t(m: Maybe<&2, List<&2, DC.Mem>>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk, hd: SL.OptDec(DC.Sk.ms(s), m),
  +hrn: SH.RecN(DC.Sk.ms(s), bs(ids)), +hk: GS.KSpan(es, fs, DC.Sk.k(s))) -> Step(DC.kmons(DC.bases(es, fs)), ids, es, fs, s, DC.r.c3(m, es, fs, t, cs, ids, s)):
  match m:
    case None{}:
      r.c4_t(DC.lks(DC.cids(ids, es, cs), es, fs, t, s, bs(ids), DC.roots(DC.Sk.ms(s))), es, fs, cs, ids, s,
        SH.lks_fr(DC.cids(ids, es, cs), es, fs, t, s, bs(ids), DC.roots(DC.Sk.ms(s))),
        SL.lks_in(DC.cids(ids, es, cs), es, fs, t, s, bs(ids), DC.roots(DC.Sk.ms(s)), bs(ids), SH.all_nmem(bs(ids)), SL.roots_in(DC.Sk.ms(s), bs(ids), hrn)), hk)
    case Some{+ms2}:
      (lt3_b(KL.kslack(DC.kmons(DC.bases(es, fs)), KL.pivs(KS.ks.rows(DC.Sk.k(s)))), SL.rcount(ms2), SL.rcount(DC.Sk.ms(s)), DC.lslack(ids, bs(ids), DC.Sk.ls(s)), hd), hk)

# a new K generator in the span that K lacks
def kstep(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ids: List<&2, Nat>, +s: DC.Sk, +d: DR.Der,
  +hkr: {EP.rinv(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), 0n) == True{} : Bool}, +hk: GS.KSpan(es, fs, DC.Sk.k(s)),
  +hs: SN.InSpan(DR.Jd.e(DR.concl(es, fs, d)), DC.bases(es, fs)), hn: {KS.ks.inb(DC.Sk.k(s), DR.Jd.e(DR.concl(es, fs, d))) == False{} : Bool})
  -> Step(DC.kmons(DC.bases(es, fs)), ids, es, fs, s, DC.OStep{DC.Sk{KS.ks.add(es, fs, DC.Sk.k(s), d), DC.Sk.ms(s), DC.Sk.ls(s)}}):
  (lt3_a(KL.kslack(DC.kmons(DC.bases(es, fs)), KL.pivs(KS.ks.rows(KS.ks.add(es, fs, DC.Sk.k(s), d)))), KL.kslack(DC.kmons(DC.bases(es, fs)), KL.pivs(KS.ks.rows(DC.Sk.k(s)))),
     Nat.add(SL.rcount(DC.Sk.ms(s)), DC.lslack(ids, bs(ids), DC.Sk.ls(s))),
     KL.ks_add_dec(es, fs, DC.Sk.k(s), d, DC.bases(es, fs), hkr, hk, hs, hn)),
   GS.ks_add_span(es, fs, DC.Sk.k(s), d, hk, hs))

def r.c2_t(m: Maybe<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk, hs: GS.OptS(es, fs, m), hn: CP.OptN(DC.Sk.k(s), es, fs, m),
  +hkr: {EP.rinv(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), 0n) == True{} : Bool}, +hk: GS.KSpan(es, fs, DC.Sk.k(s)),
  +hro: SH.RootsOk(DC.Sk.ms(s), DC.Sk.ms(s)), +haf: SH.AllFirst(DC.Sk.ms(s), DC.Sk.ms(s)), +hF: {SH.isroot(DC.Sk.ms(s), DR.NFrame{}) == True{} : Bool}, +hrn: SH.RecN(DC.Sk.ms(s), bs(ids)))
  -> Step(DC.kmons(DC.bases(es, fs)), ids, es, fs, s, DC.r.c2(m, es, fs, t, cs, ids, s)):
  match m:
    case None{}:
      r.c3_t(DC.mgs(DC.roots(DC.Sk.ms(s)), es, fs, t, s), es, fs, t, cs, ids, s, SL.mgs_dec(DC.roots(DC.Sk.ms(s)), es, fs, t, s, SH.roots_root(DC.Sk.ms(s), DC.Sk.ms(s), haf), hro, haf, hF), hrn, hk)
    case Some{+d}:
      kstep(es, fs, ids, s, d, hkr, hk, hs, hn)

def r.c1_t(m: Maybe<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +s: DC.Sk, hs: GS.OptS(es, fs, m), hn: CP.OptN(DC.Sk.k(s), es, fs, m),
  +hkr: {EP.rinv(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), 0n) == True{} : Bool}, +hk: GS.KSpan(es, fs, DC.Sk.k(s)), +hm: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)),
  +hro: SH.RootsOk(DC.Sk.ms(s), DC.Sk.ms(s)), +haf: SH.AllFirst(DC.Sk.ms(s), DC.Sk.ms(s)), +hF: {SH.isroot(DC.Sk.ms(s), DR.NFrame{}) == True{} : Bool}, +hrn: SH.RecN(DC.Sk.ms(s), bs(ids)))
  -> Step(DC.kmons(DC.bases(es, fs)), ids, es, fs, s, DC.r.c1(m, es, fs, t, OP.cspan(ctx), ids, s)):
  match m:
    case None{}:
      r.c2_t(DC.clxs(DC.roots(DC.Sk.ms(s)), es, fs, t, s), es, fs, t, OP.cspan(ctx), ids, s, GS.clxs_s(DC.roots(DC.Sk.ms(s)), es, fs, ctx, t, s, hm, hk), CP.clxs_n(DC.roots(DC.Sk.ms(s)), es, fs, t, s, hkr),
        hkr, hk, hro, haf, hF, hrn)
    case Some{+d}:
      kstep(es, fs, ids, s, d, hkr, hk, hs, hn)

def r.e2_t(m: Maybe<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +s: DC.Sk,
  +hkr: {EP.rinv(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), 0n) == True{} : Bool}, +hk: GS.KSpan(es, fs, DC.Sk.k(s)), +hm: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)),
  +hro: SH.RootsOk(DC.Sk.ms(s), DC.Sk.ms(s)), +haf: SH.AllFirst(DC.Sk.ms(s), DC.Sk.ms(s)), +hF: {SH.isroot(DC.Sk.ms(s), DR.NFrame{}) == True{} : Bool}, +hrn: SH.RecN(DC.Sk.ms(s), bs(ids)))
  -> Step(DC.kmons(DC.bases(es, fs)), ids, es, fs, s, DC.r.e2(m, es, fs, t, OP.cspan(ctx), ids, s)):
  match m:
    case None{}:
      r.c1_t(DC.fback(DC.rgens(fs, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, DC.Sk.k(s)), es, fs, ctx, t, ids, s,
        GS.fback_s(DC.rgens(fs, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, DC.Sk.k(s), GS.allvs_rgens(es, fs, ctx, t, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s), hm)),
        CP.fback_n(DC.rgens(fs, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, DC.Sk.k(s)), hkr, hk, hm, hro, haf, hF, hrn)
    case Some{g}:
      Unit{}

def r.e1_t(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +s: DC.Sk,
  +hkr: {EP.rinv(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), 0n) == True{} : Bool}, +hk: GS.KSpan(es, fs, DC.Sk.k(s)), +hm: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)),
  +hro: SH.RootsOk(DC.Sk.ms(s), DC.Sk.ms(s)), +haf: SH.AllFirst(DC.Sk.ms(s), DC.Sk.ms(s)), +hF: {SH.isroot(DC.Sk.ms(s), DR.NFrame{}) == True{} : Bool}, +hrn: SH.RecN(DC.Sk.ms(s), bs(ids)))
  -> Step(DC.kmons(DC.bases(es, fs)), ids, es, fs, s, DC.r.e1(f, es, fs, t, OP.cspan(ctx), ids, s)):
  match f:
    case True{}:
      Unit{}
    case False{}:
      r.e2_t(DC.voidseg(ids, es, OP.cspan(ctx), DC.Sk.k(s)), es, fs, ctx, t, ids, s, hkr, hk, hm, hro, haf, hF, hrn)

def ri_r(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, h: ST.RI(B, rows)) -> {EP.rinv(B, rows, 0n) == True{} : Bool}:
  (a, b) = h
  a

def TInv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +s: DC.Sk) -> Data:
  SK.Both(SK.Both(RD.SkInv(es, fs, ctx, t, s), SH.ShInv(es, fs, OP.cspan(ctx), ids, s)), GS.KSpan(es, fs, DC.Sk.k(s)))

def round_t.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +s: DC.Sk, +hsk: RD.SkInv(es, fs, ctx, t, s),
  +hsm: SH.ShM(es, OP.cspan(ctx), ids, DC.Sk.ms(s)), +hk: GS.KSpan(es, fs, DC.Sk.k(s))) -> Step(DC.kmons(DC.bases(es, fs)), ids, es, fs, s, DC.round(es, fs, t, OP.cspan(ctx), ids, s)):
  r.e1_t(KS.ks.inb(DC.Sk.k(s), DR.cst(DR.qo())), es, fs, ctx, t, ids, s,
    ri_r(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.sk.k(es, fs, ctx, t, s, hsk))), hk, RR.sk.ms(es, fs, ctx, t, s, hsk),
    SH.sh.ro(es, OP.cspan(ctx), ids, DC.Sk.ms(s), hsm), SH.sh.af(es, OP.cspan(ctx), ids, DC.Sk.ms(s), hsm), SH.sh.fr(es, OP.cspan(ctx), ids, DC.Sk.ms(s), hsm), SH.sh.rn(es, OP.cspan(ctx), ids, DC.Sk.ms(s), hsm))

# a round that does not stop takes the measure down
def round_t(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +s: DC.Sk, +h: TInv(es, fs, ctx, t, ids, s))
  -> Step(DC.kmons(DC.bases(es, fs)), ids, es, fs, s, DC.round(es, fs, t, OP.cspan(ctx), ids, s)):
  (h1, hk) = h
  (hsk, hsh) = h1
  round_t.go(es, fs, ctx, t, ids, s, hsk, SH.shi.m(es, fs, OP.cspan(ctx), ids, s, hsh), hk)

# The run
# -------

def isstep(o: DC.Out) -> Bool:
  match o:
    case DC.OStep{s}:
      True{}
    case DC.OFix{s}:
      False{}
    case DC.OOne{d}:
      False{}
    case DC.OVoid{g, dr, di}:
      False{}

# a state the fuel left is enough for
def TOut(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +fuel: Nat, o: DC.Out) -> Data:
  match o:
    case DC.OStep{+s}:
      SK.Both(TInv(es, fs, ctx, t, ids, s), {KA.natle(1n+mu(DC.kmons(DC.bases(es, fs)), ids, s), fuel) == True{} : Bool})
    case DC.OFix{s}:
      Unit
    case DC.OOne{d}:
      Unit
    case DC.OVoid{g, dr, di}:
      Unit

def tout_of(o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +s: DC.Sk, +f: Nat,
  hfx: FX.FixOut(es, fs, ctx, t, ids, o), hst: Step(DC.kmons(DC.bases(es, fs)), ids, es, fs, s, o), hle: {KA.natle(mu(DC.kmons(DC.bases(es, fs)), ids, s), f) == True{} : Bool})
  -> TOut(es, fs, ctx, t, ids, f, o):
  match o:
    case DC.OStep{+s2}:
      (hlt, hk) = hst
      ((hfx, hk), KA.natle_trans(1n+mu(DC.kmons(DC.bases(es, fs)), ids, s2), mu(DC.kmons(DC.bases(es, fs)), ids, s), f, hlt, hle))
    case DC.OFix{s2}:
      Unit{}
    case DC.OOne{d}:
      Unit{}
    case DC.OVoid{g, dr, di}:
      Unit{}

def run0(o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, h: TOut(es, fs, ctx, t, ids, 0n, o)) -> {isstep(o) == False{} : Bool}:
  match o:
    case DC.OStep{+s}:
      (hi, hlt) = h
      absurd({True{} == False{} : Bool}, KA.ft(hlt))
    case DC.OFix{s}:
      {==}
    case DC.OOne{d}:
      {==}
    case DC.OVoid{g, dr, di}:
      {==}

def run_t.go(+f: Nat, +s: DC.Sk, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +hi: TInv(es, fs, ctx, t, ids, s),
  hlt: {KA.natle(mu(DC.kmons(DC.bases(es, fs)), ids, s), f) == True{} : Bool}, +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool},
  ih: TOut(es, fs, ctx, t, ids, f, DC.round(es, fs, t, OP.cspan(ctx), ids, s)) -> {isstep(DC.run(f, DC.round(es, fs, t, OP.cspan(ctx), ids, s), es, fs, t, OP.cspan(ctx), ids)) == False{} : Bool})
  -> {isstep(DC.run(f, DC.round(es, fs, t, OP.cspan(ctx), ids, s), es, fs, t, OP.cspan(ctx), ids)) == False{} : Bool}:
  (h1, hk) = hi
  (+hsk, +hsh) = h1
  ih(tout_of(DC.round(es, fs, t, OP.cspan(ctx), ids, s), es, fs, ctx, t, ids, s, f,
    FX.fix_of(DC.round(es, fs, t, OP.cspan(ctx), ids, s), es, fs, ctx, t, ids, RD.round_ok(es, fs, ctx, t, ids, s, hsk, hz, hb), FX.round_sh(es, fs, ctx, t, ids, s, FX.skinv_k(es, fs, ctx, t, s, hsk), hsh)),
    round_t(es, fs, ctx, t, ids, s, hi), hlt))

# with fuel past the measure the run does not end on a step
def run_t(fuel: Nat, o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, h: TOut(es, fs, ctx, t, ids, fuel, o),
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}) -> {isstep(DC.run(fuel, o, es, fs, t, OP.cspan(ctx), ids)) == False{} : Bool}:
  match fuel o:
    case 0n o:
      run0(o, es, fs, ctx, t, ids, h)
    case 1n++f DC.OStep{+s}:
      (+hi, hlt) = h
      run_t.go(f, s, es, fs, ctx, t, ids, hi, hlt, hz, hb,
        x => run_t(f, DC.round(es, fs, t, OP.cspan(ctx), ids, s), es, fs, ctx, t, ids, x, hz, hb))
    case 1n+f DC.OFix{s}:
      {==}
    case 1n+f DC.OOne{d}:
      {==}
    case 1n+f DC.OVoid{g, dr, di}:
      {==}

# The first state
# ---------------

def rb_le(b: Bool) -> {KA.natle(SL.rb(b), 1n) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rcm.pick(b: Bool, +n: DR.Node, +rest: List<&2, DC.Mem>, +k: Nat, h: {KA.natle(SL.rcount(rest), k) == True{} : Bool}) -> {KA.natle(SL.rcount(DC.mpick(b, n, rest)), 1n+k) == True{} : Bool}:
  match b:
    case True{}:
      KA.natle_add2(SL.rb(DC.node_eq(n, n)), SL.rcount(rest), 1n, k, rb_le(DC.node_eq(n, n)), h)
    case False{}:
      KA.natle_succ(SL.rcount(rest), k, h)

# at most one root per node
def rcount_minit(ns: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +cs: DC.SP) -> {KA.natle(SL.rcount(DC.minit(ns, es, cs)), DC.nlen(ns)) == True{} : Bool}:
  match ns:
    case Nil{}:
      {==}
    case Con{+n, +tl}:
      rcm.pick(DC.isopen(es, cs, n), n, DC.minit(tl, es, cs), DC.nlen(tl), rcount_minit(tl, es, cs))

# the first state's measure is below the fuel
def mu0(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +cs: DC.SP) -> {KA.natle(1n+mu(DC.kmons(DC.bases(es, fs)), DC.segids(es), DC.sk0(es, fs, cs)), DC.dfuel(es, fs)) == True{} : Bool}:
  KA.natle_add2(KL.kslack(DC.kmons(DC.bases(es, fs)), KL.pivs(KS.ks.rows(DC.kinit(es, fs, fs, 0n, KS.ks0())))), Nat.add(SL.rcount(DC.minit(bs(DC.segids(es)), es, cs)), DC.lslack(DC.segids(es), bs(DC.segids(es)), Nil{})),
    DC.mlen(DC.kmons(DC.bases(es, fs))), Nat.add(DC.nlen(bs(DC.segids(es))), DC.lslack(DC.segids(es), bs(DC.segids(es)), Nil{})),
    KL.kslack_bound(DC.kmons(DC.bases(es, fs)), KL.pivs(KS.ks.rows(DC.kinit(es, fs, fs, 0n, KS.ks0())))),
    KA.natle_add2(SL.rcount(DC.minit(bs(DC.segids(es)), es, cs)), DC.lslack(DC.segids(es), bs(DC.segids(es)), Nil{}), DC.nlen(bs(DC.segids(es))), DC.lslack(DC.segids(es), bs(DC.segids(es)), Nil{}),
      rcount_minit(bs(DC.segids(es)), es, cs), KA.natle_refl(DC.lslack(DC.segids(es), bs(DC.segids(es)), Nil{}))))

# The theorem
# -----------

# with DC.dfuel the closure ends at a fixpoint or an explosion, never on a
# step
def dclose_term(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> {isstep(DC.dclose(es, fs, ctx, t, DC.dfuel(es, fs))) == False{} : Bool}:
  %Equal.sym(DC.Out, DC.dclose(es, fs, ctx, t, DC.dfuel(es, fs)), DC.dclose_ref(es, fs, ctx, t, DC.dfuel(es, fs)), FP.dclose_eq(es, fs, ctx, t, DC.dfuel(es, fs))) : {isstep(_) == False{} : Bool}
  run_t(DC.dfuel(es, fs), DC.OStep{DC.sk0(es, fs, OP.cspan(ctx))}, es, fs, ctx, t, DC.segids(es),
    (((RD.sk0_ok(es, fs, ctx, t, hz, hb), SH.sk0_sh(es, fs, OP.cspan(ctx))), GS.kinit_span(fs, es, fs, 0n, KS.ks0(), Unit{})), mu0(es, fs, OP.cspan(ctx))), hz, hb)

def dclose_nostep(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, eo: {DC.dclose(es, fs, ctx, t, DC.dfuel(es, fs)) == DC.OStep{s} : DC.Out},
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}) -> Empty:
  KA.tf((%eo : {isstep(_) == False{} : Bool}
    dclose_term(es, fs, ctx, t, hz, hb)))
