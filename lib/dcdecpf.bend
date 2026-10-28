# bend-cad: the closure's negative answers are right (PLAN-sk13b B3, the
# decision interface). At a fixpoint whose sets hold neither the target
# equation e (K) nor its direction statement (par), no valid derivation
# proves it: by the closure theorem its conclusion would be represented,
# and each set's Bool test passes what the set holds. So the spec's
# NotDirDerivable follows from the closure's run. Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./q.bend as LQ
import ./qring.bend as QR
import ./qalg.bend as QA
import ./identpf.bend as ID
import ./listpf.bend as LP2
import ./labpf.bend as LP
import ./lab.bend as LB
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcopenpf.bend as OP
import ./dcinvpf.bend as IV
import ./dcgenpf.bend as GN
import ./dcmergepf.bend as MG
import ./dcreppf.bend as RP
import ./dcroundpf.bend as RD
import ./dcsetpf.bend as ST
import ./dcnodepf.bend as ND
import ./labalgpf.bend as LA
import ./labnzpf.bend as NZ
import ./dcshapepf.bend as SH
import ./dcfixpf.bend as FX
import ./dcreadpf.bend as RF
import ./dclinepf.bend as CL
import ./lspanpf.bend as LS
import ./dcreprpf.bend as RR

import ./dcbelowpf.bend as BL
import ./dcturnpf.bend as TU
import ./dcpushpf.bend as PU

import ./dcturncpf.bend as TC

import ./dclopf.bend as LO

import ./dcftiepf.bend as FT

import ./dcclosepf.bend as CC
import ../spec/_draft13b.bend as SD

def absurd(-A: Type, x: Empty) -> A:
  match x:

def bor_ff.l(a: Bool, +b: Bool, h: {SV.bor(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      {==}

def bor_ff.r(a: Bool, +b: Bool, h: {SV.bor(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      absurd({b == False{} : Bool}, LP.tf(h))
    case False{}:
      h

# Each set's test passes what it holds
# ------------------------------------

def rs_inb(r: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +y: SK.VE, h: ST.InSt(es, fs, DC.Sk.k(s), ND.rset(es, fs, t, s, r), y)) -> {DC.rset.inb(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r, y) == True{} : Bool}:
  match r:
    case DR.NFrame{}:
      h
    case DR.NSeg{+c}:
      ST.hin_bool(es, fs, DR.NSeg{c}, t, DC.rhull(es, fs, t, s, DR.NSeg{c}), y, ST.hri(es, fs, ctx, DR.NSeg{c}, t, DC.rhull(es, fs, t, s, DR.NSeg{c}), GN.rhull_inv(es, fs, ctx, t, s, DR.NSeg{c}, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))), h)

def cs_inb.t(m: Maybe<&2, DC.LD>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +y: SK.VE, h: ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep.t(m, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), y)) -> {DC.rep.inb(DC.crep.t(m, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), t, y) == True{} : Bool}:
  match m:
    case None{}:
      ST.hin_bool(es, fs, DR.NSeg{c}, t, DC.hfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, t, HS.hs0()), y, ST.hri(es, fs, ctx, DR.NSeg{c}, t, DC.hfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, t, HS.hs0()), IV.hfold_inv(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, ctx, DR.NSeg{c}, t, HS.hs0(), IV.hs0_invd(es, fs, ctx, DR.NSeg{c}, t), IV.allpd_cat(es, fs, ctx, DR.NSeg{c}, t, DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c), RP.kgens_of(DC.Sk.k(s), es, fs, ctx, t, DR.NSeg{c}, RR.h.k(es, fs, ctx, t, s, H), BL.zdir_below(es, t, DR.NSeg{c}, RR.h.z(es, fs, ctx, t, s, H))), RP.cgens_ok(es, fs, ctx, t, s, c, RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))))), h)
    case Some{DC.LD{+u, du}}:
      h

def cs_inb.f(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +y: SK.VE, h: ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep.f(b, es, fs, t, s, c), c), y)) -> {DC.rep.inb(DC.crep.f(b, es, fs, t, s, c), t, y) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      cs_inb.t(DC.cties(DC.Sk.ls(s), c, DC.Sk.ms(s)), es, fs, ctx, t, s, H, c, y, h)

def cs_inb(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +y: SK.VE, h: ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), y)) -> {DC.rep.inb(DC.crep(es, fs, t, s, c), t, y) == True{} : Bool}:
  cs_inb.f(DC.fullc(es, DC.Sk.k(s), c), es, fs, ctx, t, s, H, c, y, h)

def rp_inb.n(a: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +y: SK.VE, h: RR.rp.m(None{}, es, fs, t, s, a, y)) -> {DC.par.n(a, es, fs, t, s, y) == True{} : Bool}:
  match a:
    case DR.NFrame{}:
      h
    case DR.NSeg{+c}:
      cs_inb(es, fs, ctx, t, s, H, c, y, h)

# what a node's set holds passes the state's par test
def rp_inb(mm: Maybe<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +y: SK.VE, h: RR.rp.m(mm, es, fs, t, s, a, y)) -> {DC.par.m(mm, es, fs, t, s, a, y) == True{} : Bool}:
  match mm:
    case Some{DC.Mem{a2, +r, +w, d}}:
      rs_inb(r, es, fs, ctx, t, s, H, DR.gmul(w, y), h)
    case None{}:
      rp_inb.n(a, es, fs, ctx, t, s, H, y, h)

# The negative answer
# -------------------

def dec.p(m: Maybe<&2, DR.DStat>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +a: DR.Node, +x: SK.VE, hs: {DC.stat.inb(m, es, fs, t, s) == False{} : Bool}, rep: RR.Repr(es, fs, t, s, DR.JP{a, x}), hp: SD.Proves.p(es, m, a, x)) -> Empty:
  match m:
    case Some{DR.DStat{+b, +y, +l}}:
      (ea, sv) = hp
      LP.tf(Equal.trans(Bool, True{}, DC.par.inb(es, fs, t, s, DR.NSeg{b}, y), False{},
        Equal.sym(Bool, DC.par.inb(es, fs, t, s, DR.NSeg{b}, y), True{}, rp_inb(DC.mem_of(DC.Sk.ms(s), DR.NSeg{b}), es, fs, ctx, t, s, H, DR.NSeg{b}, y,
          RR.rp_tr(DC.mem_of(DC.Sk.ms(s), DR.NSeg{b}), es, fs, ctx, t, s, H, DR.NSeg{b}, x, y, RR.rp_node(a, DR.NSeg{b}, es, fs, t, s, x, ea, rep), VD.samevd_of(x, y, sv)))), hs))
    case None{}:
      hp

def dec.j(j: DR.Jd, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +e: E.QExpr, +m: Maybe<&2, DR.DStat>, hk: {KS.ks.inb(DC.Sk.k(s), e) == False{} : Bool}, hs: {DC.stat.inb(m, es, fs, t, s) == False{} : Bool}, rep: RR.Repr(es, fs, t, s, j),
  hp: SD.Proves(es, m, e, j)) -> Empty:
  match j:
    case DR.JK{+f}:
      LP.tf(Equal.trans(Bool, True{}, KS.ks.inb(DC.Sk.k(s), e), False{}, Equal.sym(Bool, KS.ks.inb(DC.Sk.k(s), e), True{}, ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), f, e, ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)), rep, VD.samed_of(f, e, hp))), hk))
    case DR.JP{+a, +x}:
      dec.p(m, es, fs, ctx, t, s, H, a, x, hs, rep, hp)

# at a fixpoint holding neither e nor the statement m, no valid derivation proves e
def dec_none(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +e: E.QExpr, +m: Maybe<&2, DR.DStat>, +hh: {DC.holds(es, fs, t, s, e, m) == False{} : Bool}, +d: DR.Der, hv: DR.Valid(es, fs, ctx, d), hp: SD.Proves(es, m, e, DR.concl(es, fs, d))) -> Empty:
  dec.j(DR.concl(es, fs, d), es, fs, ctx, t, s, H, e, m, bor_ff.l(KS.ks.inb(DC.Sk.k(s), e), DC.stat.inb(m, es, fs, t, s), hh), bor_ff.r(KS.ks.inb(DC.Sk.k(s), e), DC.stat.inb(m, es, fs, t, s), hh), CC.closed(d, es, fs, ctx, t, s, H, hv), hp)

# the closure's run decides NotDirDerivable when its fixpoint holds neither
def not_dir(+sk: SK.Sketch, +cls: List<&2, SD.Class>, +red: List<&2, Nat>, +c: Nat, +dd: List<&2, Nat>, +i: Nat, +t: Nat, fuel: Nat, +s: DC.Sk,
  +eo: {DC.dclose(SD.ents(sk), SD.dfacts(sk, cls, red, c, dd, i), SD.ctx(sk, red, c), t, fuel) == DC.OFix{s} : DC.Out}, +hz: {DC.zb(SD.ents(sk), t) == True{} : Bool}, +hb: {DC.fb(SD.dfacts(sk, cls, red, c, dd, i), t) == True{} : Bool},
  +hh: {DC.holds(SD.ents(sk), SD.dfacts(sk, cls, red, c, dd, i), t, s, SD.eqat(SK.Sketch.eqs(sk), i), SD.dstat_of(SD.ents(sk), SD.kind_at(sk, c))) == False{} : Bool}) -> SD.NotDirDerivable(sk, cls, red, c, dd, i):
  dv => hv => hp => dec_none(SD.ents(sk), SD.dfacts(sk, cls, red, c, dd, i), SD.ctx(sk, red, c), t, s, (FX.fix_at(SD.ents(sk), SD.dfacts(sk, cls, red, c, dd, i), SD.ctx(sk, red, c), t, fuel, s, eo, hz, hb), (hz, hb)), SD.eqat(SK.Sketch.eqs(sk), i), SD.dstat_of(SD.ents(sk), SD.kind_at(sk, c)), hh, dv, hv, hp)
