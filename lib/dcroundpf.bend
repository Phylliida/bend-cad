# bend-cad: the closure's rounds keep its invariant (PLAN-sk13b B3). The
# skeleton's invariant SkInv is K's (KInvD), the members' and links'
# (MsOk, LsOk) and their labels nonzero (MsNz, LsNz). Merges keep the
# labels nonzero (mgs_nz); a round keeps SkInv, or ends in a fixpoint
# keeping it, or in an explosion with its witnesses (round_ok); so does the
# initial state (sk0_ok), and so does the whole run (dclose_ok).
# Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./listpf.bend as LP2
import ./seppf.bend as SP
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./hspacepf.bend as HP
import ./lab.bend as LB
import ./labpf.bend as LP
import ./labnzpf.bend as NZ
import ./dclose.bend as DC
import ./dcopenpf.bend as OP
import ./dcvd.bend as VD
import ./dcinvpf.bend as IV
import ./dcbelowpf.bend as BL
import ./dcgenpf.bend as GN
import ./dcderpf.bend as DD
import ./dcmergepf.bend as MG
import ./dcclxpf.bend as CX
import ./dcreppf.bend as RP
import ./dclinkpf.bend as LK
import ./dfastpf.bend as FP

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Merges keep the labels nonzero
# ------------------------------

def OptNzs(m: Maybe<&2, List<&2, DC.Mem>>) -> Data:
  match m:
    case Some{x}:
      RP.MsNz(x)
    case None{}:
      Unit

def reroot.nz2(f: Bool, +a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, +old: DR.Node, +nw: NZ.Nz(w), +hw: NZ.Nz(ww),
  +rest: List<&2, DC.Mem>, hr: RP.MsNz(rest)) -> RP.MsNz(Con{DC.reroot.one(f, a, r, w, d, new, dR, ww, old), rest}):
  match f:
    case True{}:
      (NZ.nz_trim(LB.lmul(ww, w), NZ.nz_mul(ww, w, hw, nw)), hr)
    case False{}:
      (nw, hr)

def reroot_nz(ms: List<&2, DC.Mem>, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab, hn: RP.MsNz(ms), +hw: NZ.Nz(ww)) -> RP.MsNz(DC.reroot(ms, old, new, dR, ww)):
  match ms:
    case Nil{}:
      Unit{}
    case Con{DC.Mem{+a, +r, +w, +d}, +tl}:
      (nw, rt) = hn
      reroot.nz2(DC.node_eq(r, old), a, r, w, d, new, dR, ww, old, nw, hw, DC.reroot(tl, old, new, dR, ww), reroot_nz(tl, old, new, dR, ww, rt, hw))

def merge.go_nz(f: Bool, +ms: List<&2, DC.Mem>, +rr: DR.Node, +d1: DR.Der, +w: DR.Lab, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +hn: RP.MsNz(ms), +hw: NZ.Nz(w), +hwb: NZ.Nz(wb))
  -> RP.MsNz(DC.merge.go(f, ms, rr, d1, w, b, rb, wb, db)):
  match f:
    case True{}:
      reroot_nz(ms, rr, DR.NFrame{}, DR.DThrough{db, DR.DTurn{d1, DR.Lab.conj(w), b}, DR.Lab.conj(wb), b}, LB.ltrim(LB.lmul(wb, DR.Lab.conj(w))), hn, NZ.nz_trim(LB.lmul(wb, DR.Lab.conj(w)), NZ.nz_mul(wb, DR.Lab.conj(w), hwb, NZ.nz_conj(w, hw))))
    case False{}:
      reroot_nz(ms, rb, rr, DR.DThrough{d1, DR.DTurn{db, DR.Lab.conj(wb), b}, DR.Lab.conj(w), b}, LB.ltrim(LB.lmul(w, DR.Lab.conj(wb))), hn, NZ.nz_trim(LB.lmul(w, DR.Lab.conj(wb)), NZ.nz_mul(w, DR.Lab.conj(wb), hw, NZ.nz_conj(wb, hwb))))

def merge_nz(+ms: List<&2, DC.Mem>, +rr: DR.Node, +d1: DR.Der, +w: DR.Lab, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +hn: RP.MsNz(ms), +hw: NZ.Nz(w), +hwb: NZ.Nz(wb))
  -> RP.MsNz(DC.merge(ms, rr, d1, w, DC.Mem{b, rb, wb, db})):
  merge.go_nz(SV.band(DC.node_eq(rb, DR.NFrame{}), SV.bnot(DC.node_eq(rr, DR.NFrame{}))), ms, rr, d1, w, b, rb, wb, db, hn, hw, hwb)

def mgF.pick_nz(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, DC.Mem>, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  em: {LB.ks.lab(es, fs, k, DR.zdir(es, b)) == m : Maybe<&2, DR.Lab>}, +hn: RP.MsNz(ms), +hwb: NZ.Nz(wb), +rest: Maybe<&2, List<&2, DC.Mem>>, hr: OptNzs(rest))
  -> OptNzs(DC.mgF.pick(m, es, fs, k, ms, DC.Mem{b, rb, wb, db}, b, rest)):
  match m:
    case None{}:
      hr
    case Some{+w}:
      merge_nz(ms, DR.NFrame{}, DR.DFrame{KS.ks.der(es, fs, k, SK.VE.y(DR.gmul(w, DR.zdir(es, b)))), DR.gmul(w, DR.zdir(es, b))}, w, b, rb, wb, db, hn, NZ.ks_lab_nz(es, fs, k, DR.zdir(es, b), w, em), hwb)

def mgF.if_nz(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, DC.Mem>, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  +hn: RP.MsNz(ms), +hwb: NZ.Nz(wb), +rest: Maybe<&2, List<&2, DC.Mem>>, hr: OptNzs(rest)) -> OptNzs(DC.mgF.if(f, es, fs, k, ms, DC.Mem{b, rb, wb, db}, b, rest)):
  match f:
    case True{}:
      mgF.pick_nz(LB.ks.lab(es, fs, k, DR.zdir(es, b)), es, fs, k, ms, b, rb, wb, db, {==}, hn, hwb, rest, hr)
    case False{}:
      hr

def mgF_nz(sc: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +ms: List<&2, DC.Mem>, hsc: RP.MsNz(sc), +hn: RP.MsNz(ms)) -> OptNzs(DC.mgF(sc, es, fs, k, ms)):
  match sc:
    case Nil{}:
      Unit{}
    case Con{DC.Mem{+b, +rb, +wb, +db}, +tl}:
      (hwb, rt) = hsc
      mgF.if_nz(SV.bnot(DC.node_eq(rb, DR.NFrame{})), es, fs, k, ms, b, rb, wb, db, hn, hwb, DC.mgF(tl, es, fs, k, ms), mgF_nz(tl, es, fs, k, ms, rt, hn))

def mgR.pick_nz(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +r: DR.Node, +ms: List<&2, DC.Mem>, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  em: {LB.hs.lab(es, fs, t, h, DR.zdir(es, b)) == m : Maybe<&2, DR.Lab>}, +hn: RP.MsNz(ms), +hwb: NZ.Nz(wb), +rest: Maybe<&2, List<&2, DC.Mem>>, hr: OptNzs(rest))
  -> OptNzs(DC.mgR.pick(m, es, fs, t, h, r, ms, DC.Mem{b, rb, wb, db}, b, rest)):
  match m:
    case None{}:
      hr
    case Some{+w}:
      merge_nz(ms, r, HS.hs.der(es, fs, t, r, h, DR.gmul(w, DR.zdir(es, b))), w, b, rb, wb, db, hn, NZ.hs_lab_nz(es, fs, t, h, DR.zdir(es, b), w, em), hwb)

def mgR.if_nz(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +r: DR.Node, +ms: List<&2, DC.Mem>, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  +hn: RP.MsNz(ms), +hwb: NZ.Nz(wb), +rest: Maybe<&2, List<&2, DC.Mem>>, hr: OptNzs(rest)) -> OptNzs(DC.mgR.if(f, es, fs, t, h, r, ms, DC.Mem{b, rb, wb, db}, b, rest)):
  match f:
    case True{}:
      mgR.pick_nz(LB.hs.lab(es, fs, t, h, DR.zdir(es, b)), es, fs, t, h, r, ms, b, rb, wb, db, {==}, hn, hwb, rest, hr)
    case False{}:
      hr

def mgR_nz(sc: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +r: DR.Node, +ms: List<&2, DC.Mem>, hsc: RP.MsNz(sc), +hn: RP.MsNz(ms)) -> OptNzs(DC.mgR(sc, es, fs, t, h, r, ms)):
  match sc:
    case Nil{}:
      Unit{}
    case Con{DC.Mem{+b, +rb, +wb, +db}, +tl}:
      (hwb, rt) = hsc
      mgR.if_nz(SV.bnot(DC.node_eq(rb, r)), es, fs, t, h, r, ms, b, rb, wb, db, hn, hwb, DC.mgR(tl, es, fs, t, h, r, ms), mgR_nz(tl, es, fs, t, h, r, ms, rt, hn))

def mgs.root_nz(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +r: DR.Node, +hn: RP.MsNz(DC.Sk.ms(s))) -> OptNzs(DC.mgs.root(f, es, fs, t, s, r)):
  match f:
    case True{}:
      mgF_nz(DC.Sk.ms(s), es, fs, DC.Sk.k(s), DC.Sk.ms(s), hn, hn)
    case False{}:
      mgR_nz(DC.Sk.ms(s), es, fs, t, DC.rhull(es, fs, t, s, r), r, DC.Sk.ms(s), hn, hn)

def mgs.pick_nz(m: Maybe<&2, List<&2, DC.Mem>>, hm: OptNzs(m), +rest: Maybe<&2, List<&2, DC.Mem>>, hr: OptNzs(rest)) -> OptNzs(DC.mgs.pick(m, rest)):
  match m:
    case None{}:
      hr
    case Some{+x}:
      hm

# the first merge keeps the labels nonzero
def mgs_nz(rs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +hn: RP.MsNz(DC.Sk.ms(s))) -> OptNzs(DC.mgs(rs, es, fs, t, s)):
  match rs:
    case Nil{}:
      Unit{}
    case Con{+r, +tl}:
      mgs.pick_nz(DC.mgs.root(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r), mgs.root_nz(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r, hn), DC.mgs(tl, es, fs, t, s), mgs_nz(tl, es, fs, t, s, hn))

# The skeleton's invariant
# ------------------------

def SkInv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk) -> Data:
  SK.Both(IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), SK.Both(GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), SK.Both(GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), SK.Both(RP.MsNz(DC.Sk.ms(s)), RP.LsNz(DC.Sk.ls(s))))))

# a K derivation of e: VD, a K judgment, the same as e
def KD(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +d: DR.Der, +e: E.QExpr) -> Data:
  SK.Both(VD.VD(es, fs, ctx, d), SK.Both(VD.Isk(DR.concl(es, fs, d)), VD.SameD(DR.Jd.e(DR.concl(es, fs, d)), e)))

def OutInv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, o: DC.Out) -> Data:
  match o:
    case DC.OStep{+s}:
      SkInv(es, fs, ctx, t, s)
    case DC.OFix{+s}:
      SkInv(es, fs, ctx, t, s)
    case DC.OOne{+d}:
      KD(es, fs, ctx, d, DR.cst(DR.qo()))
    case DC.OVoid{+g, +dr, +di}:
      SK.Both(VD.OpenD(es, ctx, DR.NSeg{g}), SK.Both(KD(es, fs, ctx, dr, SK.VE.x(DR.zseg(es, g))), KD(es, fs, ctx, di, SK.VE.y(DR.zseg(es, g)))))

def lsok_snoc(ls: List<&2, DC.Link>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +l: DC.Link, h: GN.LsOk(es, fs, ctx, t, ls), hl: GN.LOkD(es, fs, ctx, t, l))
  -> GN.LsOk(es, fs, ctx, t, DC.lsnoc(ls, l)):
  match ls:
    case Nil{}:
      (hl, Unit{})
    case Con{+h0, +tl}:
      (g, rt) = h
      (g, lsok_snoc(tl, es, fs, ctx, t, l, rt, hl))

def lsnz_one(l: DC.Link, hl: LK.LNz(l)) -> RP.LsNz(Con{l, Nil{}}):
  match l:
    case DC.Link{c, b, +w, d}:
      (hl, Unit{})

def lsnz_snoc(ls: List<&2, DC.Link>, +l: DC.Link, h: RP.LsNz(ls), hl: LK.LNz(l)) -> RP.LsNz(DC.lsnoc(ls, l)):
  match ls:
    case Nil{}:
      lsnz_one(l, hl)
    case Con{DC.Link{+c, +b, +w, +d}, +tl}:
      (g, rt) = h
      (g, lsnz_snoc(tl, l, rt, hl))

# The stages
# ----------

def r.c4_ok(m: Maybe<&2, DC.Link>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, hm: LK.OptL(es, fs, ctx, t, m), +hs: SkInv(es, fs, ctx, t, s))
  -> OutInv(es, fs, ctx, t, DC.r.c4(m, s)):
  match m:
    case None{}:
      hs
    case Some{+l}:
      (hl, nl) = hm
      (hk, r1) = hs
      (hms, r2) = r1
      (hls, r3) = r2
      (hmsn, hlsn) = r3
      (hk, (hms, (lsok_snoc(DC.Sk.ls(s), es, fs, ctx, t, l, hls, hl), (hmsn, lsnz_snoc(DC.Sk.ls(s), l, hlsn, nl)))))

def r.c3_ok(m: Maybe<&2, List<&2, DC.Mem>>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +s: DC.Sk,
  hm: MG.OptMs(es, fs, ctx, t, m), hmn: OptNzs(m), +hs: SkInv(es, fs, ctx, t, s), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> OutInv(es, fs, ctx, t, DC.r.c3(m, es, fs, t, OP.cspan(ctx), ids, s)):
  match m:
    case None{}:
      (hk, r1) = hs
      (+hms, r2) = r1
      (hls, r3) = r2
      (hmsn, hlsn) = r3
      r.c4_ok(DC.lks(DC.cids(ids, es, OP.cspan(ctx)), es, fs, t, s, Con{DR.NFrame{}, DC.snodes(ids)}, DC.roots(DC.Sk.ms(s))), es, fs, ctx, t, s,
        LK.lks_ok(DC.cids(ids, es, OP.cspan(ctx)), es, fs, ctx, t, s, Con{DR.NFrame{}, DC.snodes(ids)}, DC.roots(DC.Sk.ms(s)), MG.roots_open(DC.Sk.ms(s), es, fs, ctx, t, hms), hk, hms, hls, hmsn, hlsn, hz, hb), hs)
    case Some{+x}:
      (hk, r1) = hs
      (hms, r2) = r1
      (hls, r3) = r2
      (hmsn, hlsn) = r3
      (hk, (hm, (hls, (hmn, hlsn))))

def r.c2_ok(m: Maybe<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +s: DC.Sk,
  hm: CX.OptK(es, fs, ctx, t, m), +hs: SkInv(es, fs, ctx, t, s), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> OutInv(es, fs, ctx, t, DC.r.c2(m, es, fs, t, OP.cspan(ctx), ids, s)):
  match m:
    case None{}:
      (+hk, r1) = hs
      (+hms, r2) = r1
      (+hls, r3) = r2
      (+hmsn, hlsn) = r3
      r.c3_ok(DC.mgs(DC.roots(DC.Sk.ms(s)), es, fs, t, s), es, fs, ctx, t, ids, s,
        MG.mgs_ok(DC.roots(DC.Sk.ms(s)), es, fs, ctx, t, s, MG.roots_open(DC.Sk.ms(s), es, fs, ctx, t, hms), hk, hms, hls, hz, hb), mgs_nz(DC.roots(DC.Sk.ms(s)), es, fs, t, s, hmsn), hs, hz, hb)
    case Some{+d}:
      (hk, r1) = hs
      (hms, r2) = r1
      (hls, r3) = r2
      (hmsn, hlsn) = r3
      (IV.ks_add_invd(es, fs, ctx, t, DC.Sk.k(s), d, hk, hm), (hms, (hls, (hmsn, hlsn))))

def r.c1_ok(m: Maybe<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +s: DC.Sk,
  hm: CX.OptK(es, fs, ctx, t, m), +hs: SkInv(es, fs, ctx, t, s), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> OutInv(es, fs, ctx, t, DC.r.c1(m, es, fs, t, OP.cspan(ctx), ids, s)):
  match m:
    case None{}:
      (+hk, r1) = hs
      (+hms, r2) = r1
      (+hls, r3) = r2
      (hmsn, hlsn) = r3
      r.c2_ok(DC.clxs(DC.roots(DC.Sk.ms(s)), es, fs, t, s), es, fs, ctx, t, ids, s,
        CX.clxs_ok(DC.roots(DC.Sk.ms(s)), es, fs, ctx, t, s, MG.roots_open(DC.Sk.ms(s), es, fs, ctx, t, hms), hk, hms, hls, hz, hb), hs, hz, hb)
    case Some{+d}:
      (hk, r1) = hs
      (hms, r2) = r1
      (hls, r3) = r2
      (hmsn, hlsn) = r3
      (IV.ks_add_invd(es, fs, ctx, t, DC.Sk.k(s), d, hk, hm), (hms, (hls, (hmsn, hlsn))))

def OptVS(+es: List<&2, SK.Ent>, +cs: DC.SP, +k: KS.KS, m: Maybe<&2, Nat>) -> Data:
  match m:
    case Some{+g}:
      SK.Both({SV.bnot(DC.coll(es, cs, g)) == True{} : Bool}, {DC.fullc(es, k, g) == True{} : Bool})
    case None{}:
      Unit

def vpick_ok(f: Bool, +es: List<&2, SK.Ent>, +cs: DC.SP, +k: KS.KS, +i: Nat, +ef: {f == SV.band(SV.bnot(DC.coll(es, cs, i)), DC.fullc(es, k, i)) : Bool}, +rest: Maybe<&2, Nat>, hr: OptVS(es, cs, k, rest))
  -> OptVS(es, cs, k, DC.vpick(f, i, rest)):
  match f:
    case True{}:
      (LP2.band_l(SV.bnot(DC.coll(es, cs, i)), DC.fullc(es, k, i), Equal.sym(Bool, True{}, SV.band(SV.bnot(DC.coll(es, cs, i)), DC.fullc(es, k, i)), ef)),
       LP2.band_r(SV.bnot(DC.coll(es, cs, i)), DC.fullc(es, k, i), Equal.sym(Bool, True{}, SV.band(SV.bnot(DC.coll(es, cs, i)), DC.fullc(es, k, i)), ef)))
    case False{}:
      hr

def voidseg_ok(ids: List<&2, Nat>, +es: List<&2, SK.Ent>, +cs: DC.SP, +k: KS.KS) -> OptVS(es, cs, k, DC.voidseg(ids, es, cs, k)):
  match ids:
    case Nil{}:
      Unit{}
    case Con{+i, +tl}:
      vpick_ok(SV.band(SV.bnot(DC.coll(es, cs, i)), DC.fullc(es, k, i)), es, cs, k, i, {==}, DC.voidseg(tl, es, cs, k), voidseg_ok(tl, es, cs, k))

def r.e2_ok(m: Maybe<&2, Nat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +s: DC.Sk,
  hm: OptVS(es, OP.cspan(ctx), DC.Sk.k(s), m), +hs: SkInv(es, fs, ctx, t, s), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> OutInv(es, fs, ctx, t, DC.r.e2(m, es, fs, t, OP.cspan(ctx), ids, s)):
  match m:
    case None{}:
      (+hk, r1) = hs
      (+hms, r2) = r1
      (+hls, r3) = r2
      (hmsn, hlsn) = r3
      r.c1_ok(DC.fback(DC.rgens(fs, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, DC.Sk.k(s)), es, fs, ctx, t, ids, s,
        CX.fback_ok(DC.rgens(fs, DR.NFrame{}, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, ctx, t, DC.Sk.k(s), GN.rgens_ok(DC.Sk.ms(s), es, fs, ctx, t, DR.NFrame{}, DC.Sk.ls(s), hz, hb, hms, hls)), hs, hz, hb)
    case Some{+g}:
      (ho, +hf) = hm
      (+hk, r1) = hs
      (ho, (DD.ks_der_okd(es, fs, ctx, t, DC.Sk.k(s), SK.VE.x(DR.zseg(es, g)), hk, LP2.band_l(KS.ks.inb(DC.Sk.k(s), SK.VE.x(DR.zseg(es, g))), KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.zseg(es, g))), hf)),
             DD.ks_der_okd(es, fs, ctx, t, DC.Sk.k(s), SK.VE.y(DR.zseg(es, g)), hk, LP2.band_r(KS.ks.inb(DC.Sk.k(s), SK.VE.x(DR.zseg(es, g))), KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.zseg(es, g))), hf))))

def r.e1_ok(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +s: DC.Sk, ef: {f == KS.ks.inb(DC.Sk.k(s), DR.cst(DR.qo())) : Bool},
  +hs: SkInv(es, fs, ctx, t, s), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> OutInv(es, fs, ctx, t, DC.r.e1(f, es, fs, t, OP.cspan(ctx), ids, s)):
  match f:
    case True{}:
      (hk, r1) = hs
      DD.ks_der_okd(es, fs, ctx, t, DC.Sk.k(s), DR.cst(DR.qo()), hk, Equal.sym(Bool, True{}, KS.ks.inb(DC.Sk.k(s), DR.cst(DR.qo())), ef))
    case False{}:
      r.e2_ok(DC.voidseg(ids, es, OP.cspan(ctx), DC.Sk.k(s)), es, fs, ctx, t, ids, s, voidseg_ok(ids, es, OP.cspan(ctx), DC.Sk.k(s)), hs, hz, hb)

# a round keeps the invariant, or ends with what it found
def round_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>, +s: DC.Sk, +hs: SkInv(es, fs, ctx, t, s),
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}) -> OutInv(es, fs, ctx, t, DC.round(es, fs, t, OP.cspan(ctx), ids, s)):
  r.e1_ok(KS.ks.inb(DC.Sk.k(s), DR.cst(DR.qo())), es, fs, ctx, t, ids, s, {==}, hs, hz, hb)

# The initial state
# -----------------

def kgen_prem(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +i: Nat, +e: E.QExpr, +nd: List<&2, Nat>, +ds: Maybe<&2, DR.DStat>,
  ef: {Some{DR.Fact{e, nd, ds}} == DR.fact_at(fs, i) : Maybe<&2, DR.Fact>}, he: {SP.vbelow(e, t) == True{} : Bool}) -> IV.KGen(es, fs, ctx, t, DR.DPrem{i}):
  %ef : SK.Both({VD.hasf(_) == True{} : Bool}, SK.Both({VD.isk(DR.JK{DR.fact.e(_)}) == True{} : Bool}, {SP.vbelow(DR.fact.e(_), t) == True{} : Bool}))
  ({==}, ({==}, he))

def kinit_ok(rest: List<&2, DR.Fact>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +i: Nat, +k: KS.KS,
  +h: {GN.fdrop(i, fs) == rest : List<&2, DR.Fact>}, +hb: {DC.fb(rest, t) == True{} : Bool}, hk: IV.KInvD(es, fs, ctx, t, k)) -> IV.KInvD(es, fs, ctx, t, DC.kinit(es, fs, rest, i, k)):
  match rest:
    case Nil{}:
      hk
    case Con{DR.Fact{+e, +nd, +ds}, +tl}:
      kinit_ok(tl, es, fs, ctx, t, 1n+i, KS.ks.add(es, fs, k, DR.DPrem{i}), GN.fdrop_tl(i, fs, DR.Fact{e, nd, ds}, tl, h),
        LP2.band_r(DC.fb.ds(ds, t), DC.fb(tl, t), LP2.band_r(SP.vbelow(e, t), SV.band(DC.fb.ds(ds, t), DC.fb(tl, t)), hb)),
        IV.ks_add_invd(es, fs, ctx, t, k, DR.DPrem{i}, hk,
          kgen_prem(es, fs, ctx, t, i, e, nd, ds, Equal.sym(Maybe<&2, DR.Fact>, DR.fact_at(fs, i), Some{DR.Fact{e, nd, ds}}, GN.fat_drop(i, fs, DR.Fact{e, nd, ds}, tl, h)),
            LP2.band_l(SP.vbelow(e, t), SV.band(DC.fb.ds(ds, t), DC.fb(tl, t)), hb))))

def mpick_ok(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +n: DR.Node, +eb: {b == DC.isopen(es, OP.cspan(ctx), n) : Bool}, +hz: {DC.zb(es, t) == True{} : Bool},
  +rest: List<&2, DC.Mem>, hr: GN.MsOk(es, fs, ctx, t, rest)) -> GN.MsOk(es, fs, ctx, t, DC.mpick(b, n, rest)):
  match b:
    case True{}:
      ((Unit{}, ({==}, ({==}, (GN.one(DR.zdir(es, n)), (Equal.sym(Bool, True{}, DC.isopen(es, OP.cspan(ctx), n), eb), (Equal.sym(Bool, True{}, DC.isopen(es, OP.cspan(ctx), n), eb), BL.zdir_below(es, t, n, hz))))))), hr)
    case False{}:
      hr

def minit_ok(ns: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +hz: {DC.zb(es, t) == True{} : Bool})
  -> GN.MsOk(es, fs, ctx, t, DC.minit(ns, es, OP.cspan(ctx))):
  match ns:
    case Nil{}:
      Unit{}
    case Con{+n, +tl}:
      mpick_ok(DC.isopen(es, OP.cspan(ctx), n), es, fs, ctx, t, n, {==}, hz, DC.minit(tl, es, OP.cspan(ctx)), minit_ok(tl, es, fs, ctx, t, hz))

def mpick_nz(b: Bool, +n: DR.Node, +rest: List<&2, DC.Mem>, hr: RP.MsNz(rest)) -> RP.MsNz(DC.mpick(b, n, rest)):
  match b:
    case True{}:
      ({==}, hr)
    case False{}:
      hr

def minit_nz(ns: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +cs: DC.SP) -> RP.MsNz(DC.minit(ns, es, cs)):
  match ns:
    case Nil{}:
      Unit{}
    case Con{+n, +tl}:
      mpick_nz(DC.isopen(es, cs, n), n, DC.minit(tl, es, cs), minit_nz(tl, es, cs))

# the initial state keeps the invariant
def sk0_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> SkInv(es, fs, ctx, t, DC.sk0(es, fs, OP.cspan(ctx))):
  (kinit_ok(fs, es, fs, ctx, t, 0n, KS.ks0(), {==}, hb, ({==}, ({==}, Unit{}))),
   (minit_ok(Con{DR.NFrame{}, DC.snodes(DC.segids(es))}, es, fs, ctx, t, hz), (Unit{}, (minit_nz(Con{DR.NFrame{}, DC.snodes(DC.segids(es))}, es, OP.cspan(ctx)), Unit{}))))

# The run
# -------

def run_ok(fuel: Nat, o: DC.Out, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ids: List<&2, Nat>,
  ho: OutInv(es, fs, ctx, t, o), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}) -> OutInv(es, fs, ctx, t, DC.run(fuel, o, es, fs, t, OP.cspan(ctx), ids)):
  match fuel o:
    case 0n o:
      ho
    case 1n+f DC.OStep{+s}:
      run_ok(f, DC.round(es, fs, t, OP.cspan(ctx), ids, s), es, fs, ctx, t, ids, round_ok(es, fs, ctx, t, ids, s, ho, hz, hb), hz, hb)
    case 1n+f DC.OFix{+s}:
      ho
    case 1n+f DC.OOne{+d}:
      ho
    case 1n+f DC.OVoid{+sg, +dr, +di}:
      ho

# whatever the closure returns keeps the invariant: a state, or an
# explosion with its witnesses
def dclose_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +fuel: Nat, +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> OutInv(es, fs, ctx, t, DC.dclose(es, fs, ctx, t, fuel)):
  %Equal.sym(DC.Out, DC.dclose(es, fs, ctx, t, fuel), DC.dclose_ref(es, fs, ctx, t, fuel), FP.dclose_eq(es, fs, ctx, t, fuel)) : OutInv(es, fs, ctx, t, _)
  run_ok(fuel, DC.OStep{DC.sk0(es, fs, OP.cspan(ctx))}, es, fs, ctx, t, DC.segids(es), sk0_ok(es, fs, ctx, t, hz, hb), hz, hb)
