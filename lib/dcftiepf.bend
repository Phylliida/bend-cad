# bend-cad: the closure theorem at links into F's component (PLAN-sk13b B3,
# "Turn and through"). A collapsed c with such a link is Tied to the first
# one's label U; every such link's tie T has cross(T, z_c) in K (its turn is
# F's generator, then frame-back), so two independent ties would put z_c in
# K squared; hence T is a real multiple of U, and T times F's set lies in
# Tied(U). Proofs only.

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

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Where c's tie comes from
# ------------------------

def ldis_some(m: Maybe<&2, DC.LD>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

def ld_none_some(+x: DC.LD, h: {None{} == Some{x} : Maybe<&2, DC.LD>}) -> Empty:
  LP.tf(Equal.sym(Bool, False{}, True{}, Equal.cong(Maybe<&2, DC.LD>, Bool, m => ldis_some(m), None{}, Some{x}, h)))

def ld_some_none(+x: DC.LD, h: {Some{x} == None{} : Maybe<&2, DC.LD>}) -> Empty:
  ld_none_some(x, Equal.sym(Maybe<&2, DC.LD>, Some{x}, None{}, h))

def ldu(m: Maybe<&2, DC.LD>, +d: DR.Lab) -> DR.Lab:
  match m:
    case Some{DC.LD{u, du}}:
      u
    case None{}:
      d

def ld_u(+u1: DR.Lab, +d1: DR.Der, +u: DR.Lab, +du: DR.Der, h: {Some{DC.LD{u1, d1}} == Some{DC.LD{u, du}} : Maybe<&2, DC.LD>}) -> {u == u1 : DR.Lab}:
  Equal.cong(Maybe<&2, DC.LD>, DR.Lab, m => ldu(m, u1), Some{DC.LD{u, du}}, Some{DC.LD{u1, d1}}, Equal.sym(Maybe<&2, DC.LD>, Some{DC.LD{u1, d1}}, Some{DC.LD{u, du}}, h))

def ctl(l: DC.Link, +t: List<&2, DC.Link>, +c: Nat, +ms: List<&2, DC.Mem>) -> Maybe<&2, DC.LD>:
  match l:
    case DC.Link{c2, +b, +wl, +dl}:
      DC.ctie.if(SV.eq(c2, c), DC.mem_of(ms, b), b, wl, dl, DC.cties(t, c, ms))

def pick_rest(b: Bool, +x: DC.LD, +rest: Maybe<&2, DC.LD>, e: {DC.ctie.pick(b, x, rest) == None{} : Maybe<&2, DC.LD>}) -> {rest == None{} : Maybe<&2, DC.LD>}:
  match b:
    case True{}:
      absurd({rest == None{} : Maybe<&2, DC.LD>}, ld_some_none(x, e))
    case False{}:
      e

def mem_rest(m: Maybe<&2, DC.Mem>, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, +rest: Maybe<&2, DC.LD>, e: {DC.ctie.mem(m, b, wl, dl, rest) == None{} : Maybe<&2, DC.LD>}) -> {rest == None{} : Maybe<&2, DC.LD>}:
  match m:
    case None{}:
      e
    case Some{DC.Mem{a, +rb, +wb, +db}}:
      pick_rest(DC.node_eq(rb, DR.NFrame{}), DC.LD{LB.lmul(wl, DR.Lab.conj(wb)), DR.DThrough{dl, DR.DTurn{db, DR.Lab.conj(wb), b}, DR.Lab.conj(wl), b}}, rest, e)

def if_rest(f: Bool, +m: Maybe<&2, DC.Mem>, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, +rest: Maybe<&2, DC.LD>, e: {DC.ctie.if(f, m, b, wl, dl, rest) == None{} : Maybe<&2, DC.LD>}) -> {rest == None{} : Maybe<&2, DC.LD>}:
  match f:
    case True{}:
      mem_rest(m, b, wl, dl, rest, e)
    case False{}:
      e

def ctl_rest(l: DC.Link, +t: List<&2, DC.Link>, +c: Nat, +ms: List<&2, DC.Mem>, e: {ctl(l, t, c, ms) == None{} : Maybe<&2, DC.LD>}) -> {DC.cties(t, c, ms) == None{} : Maybe<&2, DC.LD>}:
  match l:
    case DC.Link{+c2, +b, +wl, +dl}:
      if_rest(SV.eq(c2, c), DC.mem_of(ms, b), b, wl, dl, DC.cties(t, c, ms), e)

def cti_none(+m: Maybe<&2, DC.Mem>, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, +rest: Maybe<&2, DC.LD>, +a: DR.Node, +wb: DR.Lab, +db: DR.Der, em: {m == Some{DC.Mem{a, DR.NFrame{}, wb, db}} : Maybe<&2, DC.Mem>},
  e: {DC.ctie.if(True{}, m, b, wl, dl, rest) == None{} : Maybe<&2, DC.LD>}) -> Empty:
  ld_some_none(DC.LD{LB.lmul(wl, DR.Lab.conj(wb)), DR.DThrough{dl, DR.DTurn{db, DR.Lab.conj(wb), b}, DR.Lab.conj(wl), b}}, Equal.trans(Maybe<&2, DC.LD>, DC.ctie.if(True{}, Some{DC.Mem{a, DR.NFrame{}, wb, db}}, b, wl, dl, rest), DC.ctie.if(True{}, m, b, wl, dl, rest), None{},
    Equal.sym(Maybe<&2, DC.LD>, DC.ctie.if(True{}, m, b, wl, dl, rest), DC.ctie.if(True{}, Some{DC.Mem{a, DR.NFrame{}, wb, db}}, b, wl, dl, rest), Equal.cong(Maybe<&2, DC.Mem>, Maybe<&2, DC.LD>, q => DC.ctie.if(True{}, q, b, wl, dl, rest), m, Some{DC.Mem{a, DR.NFrame{}, wb, db}}, em)), e))

def ctn.hd(+c3: Nat, +b3: DR.Node, +w3: DR.Lab, +d3: DR.Der, +t: List<&2, DC.Link>, +c: Nat, +ms: List<&2, DC.Mem>, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, en: {Some{DC.Link{c3, b3, w3, d3}} == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>},
  ec: {SV.eq(c2, c) == True{} : Bool}, +a: DR.Node, +wb: DR.Lab, +db: DR.Der, embl: {DC.mem_of(ms, bl) == Some{DC.Mem{a, DR.NFrame{}, wb, db}} : Maybe<&2, DC.Mem>}, e: {ctl(DC.Link{c3, b3, w3, d3}, t, c, ms) == None{} : Maybe<&2, DC.LD>}) -> Empty:
  cti_none(DC.mem_of(ms, bl), bl, wl, dl, DC.cties(t, c, ms), a, wb, db, embl,
    Equal.trans(Maybe<&2, DC.LD>, DC.ctie.if(True{}, DC.mem_of(ms, bl), bl, wl, dl, DC.cties(t, c, ms)), ctl(DC.Link{c2, bl, wl, dl}, t, c, ms), None{},
      Equal.cong(Bool, Maybe<&2, DC.LD>, f => DC.ctie.if(f, DC.mem_of(ms, bl), bl, wl, dl, DC.cties(t, c, ms)), True{}, SV.eq(c2, c), Equal.sym(Bool, SV.eq(c2, c), True{}, ec)),
      Equal.trans(Maybe<&2, DC.LD>, ctl(DC.Link{c2, bl, wl, dl}, t, c, ms), ctl(DC.Link{c3, b3, w3, d3}, t, c, ms), None{},
        Equal.cong(DC.Link, Maybe<&2, DC.LD>, l => ctl(l, t, c, ms), DC.Link{c2, bl, wl, dl}, DC.Link{c3, b3, w3, d3}, Equal.sym(DC.Link, DC.Link{c3, b3, w3, d3}, DC.Link{c2, bl, wl, dl}, SH.lsome_inj(DC.Link{c3, b3, w3, d3}, DC.Link{c2, bl, wl, dl}, en))), e)))

# a link from c into F's component means c has a tie
def ct_none(ls: List<&2, DC.Link>, n: Nat, +c: Nat, +ms: List<&2, DC.Mem>, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, en: {SH.lat(ls, n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>}, +ec: {SV.eq(c2, c) == True{} : Bool},
  +a: DR.Node, +wb: DR.Lab, +db: DR.Der, +embl: {DC.mem_of(ms, bl) == Some{DC.Mem{a, DR.NFrame{}, wb, db}} : Maybe<&2, DC.Mem>}, e: {DC.cties(ls, c, ms) == None{} : Maybe<&2, DC.LD>}) -> Empty:
  match ls n:
    case Nil{} n:
      SH.lnone_some(DC.Link{c2, bl, wl, dl}, en)
    case Con{DC.Link{+c3, +b3, +w3, +d3}, +t} 0n:
      ctn.hd(c3, b3, w3, d3, t, c, ms, c2, bl, wl, dl, en, ec, a, wb, db, embl, e)
    case Con{DC.Link{+c3, +b3, +w3, +d3}, +t} 1n+j:
      ct_none(t, j, c, ms, c2, bl, wl, dl, en, ec, a, wb, db, embl, ctl_rest(DC.Link{c3, b3, w3, d3}, t, c, ms, e))

def ct.okm(mm: Maybe<&2, DC.Mem>, +wl: DR.Lab, +u: DR.Lab) -> Data:
  match mm:
    case Some{DC.Mem{a, +rb, +wb, d}}:
      SK.Both({DC.node_eq(rb, DR.NFrame{}) == True{} : Bool}, {u == LB.lmul(wl, DR.Lab.conj(wb)) : DR.Lab})
    case None{}:
      {True{} == False{} : Bool}

def ct.ok(m: Maybe<&2, DC.Link>, +ms: List<&2, DC.Mem>, +c: Nat, +u: DR.Lab) -> Data:
  match m:
    case Some{DC.Link{+c2, +b, +wl, dl}}:
      SK.Both({SV.eq(c2, c) == True{} : Bool}, ct.okm(DC.mem_of(ms, b), wl, u))
    case None{}:
      {True{} == False{} : Bool}

# the tie u is a link's from c into F's component: its label times the conjugate of its node's
def CT(+ls: List<&2, DC.Link>, +ms: List<&2, DC.Mem>, +c: Nat, +u: DR.Lab) -> Data:
  Sigma<&2, &2, Nat, n => ct.ok(SH.lat(ls, n), ms, c, u)>

def ct_tl.go(+x: DC.Link, +t: List<&2, DC.Link>, +ms: List<&2, DC.Mem>, +c: Nat, +u: DR.Lab, +n: Nat, +p: ct.ok(SH.lat(t, n), ms, c, u)) -> CT(Con{x, t}, ms, c, u):
  (1n+n, p)

def ct_tl(+x: DC.Link, +t: List<&2, DC.Link>, +ms: List<&2, DC.Mem>, +c: Nat, +u: DR.Lab, h: CT(t, ms, c, u)) -> CT(Con{x, t}, ms, c, u):
  (+n, +p) = h
  ct_tl.go(x, t, ms, c, u, n, p)

def ct_hd.p(+c3: Nat, +b3: DR.Node, +w3: DR.Lab, +d3: DR.Der, +ms: List<&2, DC.Mem>, +c: Nat, +u: DR.Lab, +a: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  ef: {True{} == SV.eq(c3, c) : Bool}, emm: {Some{DC.Mem{a, rb, wb, db}} == DC.mem_of(ms, b3) : Maybe<&2, DC.Mem>}, er: {True{} == DC.node_eq(rb, DR.NFrame{}) : Bool},
  eu: {u == LB.lmul(w3, DR.Lab.conj(wb)) : DR.Lab}) -> ct.ok(Some{DC.Link{c3, b3, w3, d3}}, ms, c, u):
  %emm : SK.Both({SV.eq(c3, c) == True{} : Bool}, ct.okm(_, w3, u))
  (Equal.sym(Bool, True{}, SV.eq(c3, c), ef), (Equal.sym(Bool, True{}, DC.node_eq(rb, DR.NFrame{}), er), eu))

def ctf.p(pb: Bool, +c3: Nat, +b3: DR.Node, +w3: DR.Lab, +d3: DR.Der, +t: List<&2, DC.Link>, +ms: List<&2, DC.Mem>, +c: Nat, +u: DR.Lab, +du: DR.Der, +a: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  ef: {True{} == SV.eq(c3, c) : Bool}, emm: {Some{DC.Mem{a, rb, wb, db}} == DC.mem_of(ms, b3) : Maybe<&2, DC.Mem>}, epb: {pb == DC.node_eq(rb, DR.NFrame{}) : Bool},
  e: {DC.ctie.pick(pb, DC.LD{LB.lmul(w3, DR.Lab.conj(wb)), DR.DThrough{d3, DR.DTurn{db, DR.Lab.conj(wb), b3}, DR.Lab.conj(w3), b3}}, DC.cties(t, c, ms)) == Some{DC.LD{u, du}} : Maybe<&2, DC.LD>}, ih: {DC.cties(t, c, ms) == Some{DC.LD{u, du}} : Maybe<&2, DC.LD>} -> CT(t, ms, c, u)) -> CT(Con{DC.Link{c3, b3, w3, d3}, t}, ms, c, u):
  match pb:
    case True{}:
      (0n, ct_hd.p(c3, b3, w3, d3, ms, c, u, a, rb, wb, db, ef, emm, epb, ld_u(LB.lmul(w3, DR.Lab.conj(wb)), DR.DThrough{d3, DR.DTurn{db, DR.Lab.conj(wb), b3}, DR.Lab.conj(w3), b3}, u, du, e)))
    case False{}:
      ct_tl(DC.Link{c3, b3, w3, d3}, t, ms, c, u, ih(e))

def ctf.m(m: Maybe<&2, DC.Mem>, +c3: Nat, +b3: DR.Node, +w3: DR.Lab, +d3: DR.Der, +t: List<&2, DC.Link>, +ms: List<&2, DC.Mem>, +c: Nat, +u: DR.Lab, +du: DR.Der,
  ef: {True{} == SV.eq(c3, c) : Bool}, emm: {m == DC.mem_of(ms, b3) : Maybe<&2, DC.Mem>}, e: {DC.ctie.mem(m, b3, w3, d3, DC.cties(t, c, ms)) == Some{DC.LD{u, du}} : Maybe<&2, DC.LD>},
  ih: {DC.cties(t, c, ms) == Some{DC.LD{u, du}} : Maybe<&2, DC.LD>} -> CT(t, ms, c, u)) -> CT(Con{DC.Link{c3, b3, w3, d3}, t}, ms, c, u):
  match m:
    case None{}:
      ct_tl(DC.Link{c3, b3, w3, d3}, t, ms, c, u, ih(e))
    case Some{DC.Mem{+a, +rb, +wb, +db}}:
      ctf.p(DC.node_eq(rb, DR.NFrame{}), c3, b3, w3, d3, t, ms, c, u, du, a, rb, wb, db, ef, emm, {==}, e, ih)

def ctf.f(f: Bool, m: Maybe<&2, DC.Mem>, +c3: Nat, +b3: DR.Node, +w3: DR.Lab, +d3: DR.Der, +t: List<&2, DC.Link>, +ms: List<&2, DC.Mem>, +c: Nat, +u: DR.Lab, +du: DR.Der,
  ef: {f == SV.eq(c3, c) : Bool}, emm: {m == DC.mem_of(ms, b3) : Maybe<&2, DC.Mem>}, e: {DC.ctie.if(f, m, b3, w3, d3, DC.cties(t, c, ms)) == Some{DC.LD{u, du}} : Maybe<&2, DC.LD>},
  ih: {DC.cties(t, c, ms) == Some{DC.LD{u, du}} : Maybe<&2, DC.LD>} -> CT(t, ms, c, u)) -> CT(Con{DC.Link{c3, b3, w3, d3}, t}, ms, c, u):
  match f:
    case True{}:
      ctf.m(m, c3, b3, w3, d3, t, ms, c, u, du, ef, emm, e, ih)
    case False{}:
      ct_tl(DC.Link{c3, b3, w3, d3}, t, ms, c, u, ih(e))

# c's tie comes from a link into F's component
def ct_from(ls: List<&2, DC.Link>, +c: Nat, +ms: List<&2, DC.Mem>, +u: DR.Lab, +du: DR.Der, e: {DC.cties(ls, c, ms) == Some{DC.LD{u, du}} : Maybe<&2, DC.LD>}) -> CT(ls, ms, c, u):
  match ls:
    case Nil{}:
      absurd(CT(Nil{}, ms, c, u), ld_none_some(DC.LD{u, du}, e))
    case Con{DC.Link{+c3, +b3, +w3, +d3}, +t}:
      ctf.f(SV.eq(c3, c), DC.mem_of(ms, b3), c3, b3, w3, d3, t, ms, c, u, du, {==}, {==}, e, x => ct_from(t, c, ms, u, du, x))

# Every tie's cross with z_c is in K
# ----------------------------------

def lkok_mk(+ls: List<&2, DC.Link>, +n: Nat, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +c: Nat, +b: DR.Node, +w: DR.Lab, en: {SH.lat(ls, n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>},
  ec: {SV.eq(c2, c) == True{} : Bool}, eb: {DC.node_eq(bl, b) == True{} : Bool}, ew: {wl == w : DR.Lab}) -> PU.lk.ok(SH.lat(ls, n), c, b, w):
  %Equal.sym(Maybe<&2, DC.Link>, SH.lat(ls, n), Some{DC.Link{c2, bl, wl, dl}}, en) : PU.lk.ok(_, c, b, w)
  (ec, (eb, ew))

def lkw(l: DC.Link) -> DR.Lab:
  match l:
    case DC.Link{c, b, w, d}:
      w

def lsn_at(ls: List<&2, DC.Link>, n: Nat, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, en: {SH.lat(ls, n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>}, h: RP.LsNz(ls)) -> NZ.Nz(wl):
  match ls n:
    case Nil{} n:
      absurd(NZ.Nz(wl), SH.lnone_some(DC.Link{c2, bl, wl, dl}, en))
    case Con{DC.Link{+c3, +b3, +w3, +d3}, +tl} 0n:
      (nw, rt) = h
      %SH.lsome_inj(DC.Link{c3, b3, w3, d3}, DC.Link{c2, bl, wl, dl}, en) : NZ.Nz(lkw(_))
      nw
    case Con{DC.Link{+c3, +b3, +w3, +d3}, +tl} 1n+j:
      (nw, rt) = h
      lsn_at(tl, j, c2, bl, wl, dl, en, rt)

def ct.sv(+wl: DR.Lab, +wb: DR.Lab, +z: SK.VE) -> VD.SameVD(DR.gmul(wb, DR.gmul(DR.Lab.conj(wl), z)), DR.gmul(DR.Lab.conj(LB.lmul(wl, DR.Lab.conj(wb))), z)):
  MG.samevd_sym(DR.gmul(DR.Lab.conj(LB.lmul(wl, DR.Lab.conj(wb))), z), DR.gmul(wb, DR.gmul(DR.Lab.conj(wl), z)), GN.samevd_tr(DR.gmul(DR.Lab.conj(LB.lmul(wl, DR.Lab.conj(wb))), z), DR.gmul(DR.Lab.conj(wl), DR.gmul(DR.Lab.conj(DR.Lab.conj(wb)), z)), DR.gmul(wb, DR.gmul(DR.Lab.conj(wl), z)), LA.gconj_mul(wl, DR.Lab.conj(wb), z), GN.samevd_tr(DR.gmul(DR.Lab.conj(wl), DR.gmul(DR.Lab.conj(DR.Lab.conj(wb)), z)), DR.gmul(DR.Lab.conj(wl), DR.gmul(wb, z)), DR.gmul(wb, DR.gmul(DR.Lab.conj(wl), z)), MG.gmul_cong(DR.Lab.conj(wl), DR.gmul(DR.Lab.conj(DR.Lab.conj(wb)), z), DR.gmul(wb, z), MG.samevd_sym(DR.gmul(wb, z), DR.gmul(DR.Lab.conj(DR.Lab.conj(wb)), z), GN.cc(wb, z))), LA.gswap(DR.Lab.conj(wl), wb, z))))

# a link from c to a node b of F's component (record (b2, F, w_b)): cross(w_l conj(w_b), z_c) is in K
def crossT(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +n: Nat, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +en: {SH.lat(DC.Sk.ls(s), n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>}, +ec: {SV.eq(c2, c) == True{} : Bool}, +b: DR.Node, +eb: {DC.node_eq(bl, b) == True{} : Bool},
  +b2: DR.Node, +wb: DR.Lab, +db: DR.Der, +nb: Nat, +enb: {SH.mat(DC.Sk.ms(s), nb) == Some{DC.Mem{b2, DR.NFrame{}, wb, db}} : Maybe<&2, DC.Mem>}, +eab: {b2 == b : DR.Node}) -> {KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.gmul(DR.Lab.conj(LB.lmul(wl, DR.Lab.conj(wb))), DR.zdir(es, DR.NSeg{c})))) == True{} : Bool}:
  ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), SK.VE.y(DR.gmul(wb, DR.gmul(DR.Lab.conj(wl), DR.zdir(es, DR.NSeg{c})))), SK.VE.y(DR.gmul(DR.Lab.conj(LB.lmul(wl, DR.Lab.conj(wb))), DR.zdir(es, DR.NSeg{c}))), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)),
    TC.act_ll(es, fs, ctx, t, s, H, c, b, wl, b2, DR.NFrame{}, wb, db, nb, enb, eab, (n, lkok_mk(DC.Sk.ls(s), n, c2, bl, wl, dl, c, b, wl, en, ec, eb, {==}))),
    RR.svy(DR.gmul(wb, DR.gmul(DR.Lab.conj(wl), DR.zdir(es, DR.NSeg{c}))), DR.gmul(DR.Lab.conj(LB.lmul(wl, DR.Lab.conj(wb))), DR.zdir(es, DR.NSeg{c})), ct.sv(wl, wb, DR.zdir(es, DR.NSeg{c}))))

# Two independent ties put z_c in K squared
# ----------------------------------------

def imv.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +u: DR.Lab, +t2: DR.Lab, +v: DR.Lab, +hs: LS.LSp(DR.Lab.conj(u), DR.Lab.conj(t2), DR.Lab.conj(v)), +hu: {KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.gmul(DR.Lab.conj(u), DR.zdir(es, DR.NSeg{c})))) == True{} : Bool}, +ht: {KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.gmul(DR.Lab.conj(t2), DR.zdir(es, DR.NSeg{c})))) == True{} : Bool}) -> {KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.gmul(DR.Lab.conj(v), DR.zdir(es, DR.NSeg{c})))) == True{} : Bool}:
  ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), ST.lin2(LA.lab.c(LS.lsp.p(DR.Lab.conj(u), DR.Lab.conj(t2), DR.Lab.conj(v), hs)), SK.VE.y(DR.gmul(DR.Lab.conj(u), DR.zdir(es, DR.NSeg{c}))), LA.lab.s(LS.lsp.p(DR.Lab.conj(u), DR.Lab.conj(t2), DR.Lab.conj(v), hs)), SK.VE.y(DR.gmul(DR.Lab.conj(t2), DR.zdir(es, DR.NSeg{c})))), SK.VE.y(DR.gmul(DR.Lab.conj(v), DR.zdir(es, DR.NSeg{c}))), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)),
    ST.ri.lin(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), LA.lab.c(LS.lsp.p(DR.Lab.conj(u), DR.Lab.conj(t2), DR.Lab.conj(v), hs)), SK.VE.y(DR.gmul(DR.Lab.conj(u), DR.zdir(es, DR.NSeg{c}))), LA.lab.s(LS.lsp.p(DR.Lab.conj(u), DR.Lab.conj(t2), DR.Lab.conj(v), hs)), SK.VE.y(DR.gmul(DR.Lab.conj(t2), DR.zdir(es, DR.NSeg{c}))), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)), hu, ht),
    RR.svy(DR.vlin(LA.lab.c(LS.lsp.p(DR.Lab.conj(u), DR.Lab.conj(t2), DR.Lab.conj(v), hs)), DR.gmul(DR.Lab.conj(u), DR.zdir(es, DR.NSeg{c})), LA.lab.s(LS.lsp.p(DR.Lab.conj(u), DR.Lab.conj(t2), DR.Lab.conj(v), hs)), DR.gmul(DR.Lab.conj(t2), DR.zdir(es, DR.NSeg{c}))), DR.gmul(DR.Lab.conj(v), DR.zdir(es, DR.NSeg{c})),
      MG.samevd_sym(DR.gmul(DR.Lab.conj(v), DR.zdir(es, DR.NSeg{c})), DR.vlin(LA.lab.c(LS.lsp.p(DR.Lab.conj(u), DR.Lab.conj(t2), DR.Lab.conj(v), hs)), DR.gmul(DR.Lab.conj(u), DR.zdir(es, DR.NSeg{c})), LA.lab.s(LS.lsp.p(DR.Lab.conj(u), DR.Lab.conj(t2), DR.Lab.conj(v), hs)), DR.gmul(DR.Lab.conj(t2), DR.zdir(es, DR.NSeg{c}))), LS.lsp_form(DR.Lab.conj(u), DR.Lab.conj(t2), DR.Lab.conj(v), hs, DR.zdir(es, DR.NSeg{c})))))

# a real combination v of two ties has cross(v, z_c) in K
def imv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +u: DR.Lab, +t2: DR.Lab, +v: DR.Lab, +hs: LS.LSp(u, t2, v), +hu: {KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.gmul(DR.Lab.conj(u), DR.zdir(es, DR.NSeg{c})))) == True{} : Bool}, +ht: {KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.gmul(DR.Lab.conj(t2), DR.zdir(es, DR.NSeg{c})))) == True{} : Bool}) -> {KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.gmul(DR.Lab.conj(v), DR.zdir(es, DR.NSeg{c})))) == True{} : Bool}:
  imv.go(es, fs, ctx, t, s, H, c, u, t2, v, LS.lsp_conj(v, u, t2, hs), hu, ht)

def ni.q(+X: S.Q, +Y: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(S.Q.neg(DR.qo()), S.Q.add(S.Q.mul(S.Q.neg(DR.qo()), X), S.Q.mul(DR.qz(), Y))), S.Q.mul(DR.qz(), S.Q.add(S.Q.mul(S.Q.neg(DR.qo()), X), S.Q.mul(DR.qz(), Y)))), X):
  QR.qring_eq([X, Y], E.QAdd{E.QMul{E.QNeg{E.QCst{DR.qo()}}, E.QAdd{E.QMul{E.QNeg{E.QCst{DR.qo()}}, E.QVar{0n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}}}, E.QMul{E.QCst{DR.qz()}, E.QAdd{E.QMul{E.QNeg{E.QCst{DR.qo()}}, E.QVar{0n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}}}}, E.QVar{0n}, {==})

def ni.at(+p: List<&2, S.Q>, +z: SK.VE) -> S.Q.eq(E.qeval(p, ST.lin2(S.Q.neg(DR.qo()), SK.VE.y(DR.gmul(DR.Lab.conj(DC.li()), z)), DR.qz(), SK.VE.y(DR.gmul(DR.Lab.conj(DC.li()), z)))), E.qeval(p, SK.VE.x(z))):
  ni.q(E.qeval(p, SK.VE.x(z)), E.qeval(p, SK.VE.y(z)))

def two_ties(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +u: DR.Lab, +t2: DR.Lab, +hd: {DC.lpar(u, t2) == False{} : Bool}, +hu: {KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.gmul(DR.Lab.conj(u), DR.zdir(es, DR.NSeg{c})))) == True{} : Bool}, +ht: {KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.gmul(DR.Lab.conj(t2), DR.zdir(es, DR.NSeg{c})))) == True{} : Bool}) -> {DC.fullc(es, DC.Sk.k(s), c) == True{} : Bool}:
  RR.fullc_t(es, DC.Sk.k(s), c,
    ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), ST.lin2(S.Q.neg(DR.qo()), SK.VE.y(DR.gmul(DR.Lab.conj(DC.li()), DR.zdir(es, DR.NSeg{c}))), DR.qz(), SK.VE.y(DR.gmul(DR.Lab.conj(DC.li()), DR.zdir(es, DR.NSeg{c})))), SK.VE.x(DR.zdir(es, DR.NSeg{c})), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)),
      ST.ri.lin(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), S.Q.neg(DR.qo()), SK.VE.y(DR.gmul(DR.Lab.conj(DC.li()), DR.zdir(es, DR.NSeg{c}))), DR.qz(), SK.VE.y(DR.gmul(DR.Lab.conj(DC.li()), DR.zdir(es, DR.NSeg{c}))), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)), imv(es, fs, ctx, t, s, H, c, u, t2, DC.li(), LS.qs2.go(u, t2, DC.li(), hd), hu, ht), imv(es, fs, ctx, t, s, H, c, u, t2, DC.li(), LS.qs2.go(u, t2, DC.li(), hd), hu, ht)),
      ID.qzero_ident(ST.lin2(S.Q.neg(DR.qo()), SK.VE.y(DR.gmul(DR.Lab.conj(DC.li()), DR.zdir(es, DR.NSeg{c}))), DR.qz(), SK.VE.y(DR.gmul(DR.Lab.conj(DC.li()), DR.zdir(es, DR.NSeg{c})))), SK.VE.x(DR.zdir(es, DR.NSeg{c})), p => ni.at(p, DR.zdir(es, DR.NSeg{c})))),
    ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), SK.VE.y(DR.gmul(DR.Lab.conj(DC.lone()), DR.zdir(es, DR.NSeg{c}))), SK.VE.y(DR.zdir(es, DR.NSeg{c})), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)), imv(es, fs, ctx, t, s, H, c, u, t2, DC.lone(), LS.qs2.go(u, t2, DC.lone(), hd), hu, ht), RR.svy(DR.gmul(DR.Lab.conj(DC.lone()), DR.zdir(es, DR.NSeg{c})), DR.zdir(es, DR.NSeg{c}), LO.c1g(DR.zdir(es, DR.NSeg{c})))))

def par.q(q: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +u: DR.Lab, +t2: DR.Lab, eq: {q == DC.lpar(u, t2) : Bool}, +hu: {KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.gmul(DR.Lab.conj(u), DR.zdir(es, DR.NSeg{c})))) == True{} : Bool}, +ht: {KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.gmul(DR.Lab.conj(t2), DR.zdir(es, DR.NSeg{c})))) == True{} : Bool}, hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool}) -> {DC.lpar(u, t2) == True{} : Bool}:
  match q:
    case True{}:
      Equal.sym(Bool, True{}, DC.lpar(u, t2), eq)
    case False{}:
      absurd({DC.lpar(u, t2) == True{} : Bool}, PU.nf(es, DC.Sk.k(s), c, two_ties(es, fs, ctx, t, s, H, c, u, t2, Equal.sym(Bool, False{}, DC.lpar(u, t2), eq), hu, ht), hf))

# so ties are parallel (c not in K squared)
def par_of(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +u: DR.Lab, +t2: DR.Lab, +hu: {KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.gmul(DR.Lab.conj(u), DR.zdir(es, DR.NSeg{c})))) == True{} : Bool}, +ht: {KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.gmul(DR.Lab.conj(t2), DR.zdir(es, DR.NSeg{c})))) == True{} : Bool}, hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool}) -> {DC.lpar(u, t2) == True{} : Bool}:
  par.q(DC.lpar(u, t2), es, fs, ctx, t, s, H, c, u, t2, {==}, hu, ht, hf)

# Tied sets
# ---------

def vsp.qx(+X: S.Q) -> S.Q.eq(X, S.Q.add(S.Q.mul(DR.qo(), X), S.Q.mul(DR.qo(), DR.qz()))):
  QR.qring_eq([X], E.QVar{0n}, E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qo()}, E.QCst{DR.qz()}}}, {==})

def vsp.qy(+Y: S.Q) -> S.Q.eq(Y, S.Q.add(S.Q.mul(DR.qo(), DR.qz()), S.Q.mul(DR.qo(), Y))):
  QR.qring_eq([Y], E.QVar{0n}, E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QCst{DR.qz()}}, E.QMul{E.QCst{DR.qo()}, E.QVar{0n}}}, {==})

def vsplit(+yb: SK.VE) -> VD.SameVD(yb, DR.vlin(DR.qo(), SK.VE{SK.VE.x(yb), DR.zeroe()}, DR.qo(), SK.VE{DR.zeroe(), SK.VE.y(yb)})):
  (ID.qzero_ident(SK.VE.x(yb), SK.VE.x(DR.vlin(DR.qo(), SK.VE{SK.VE.x(yb), DR.zeroe()}, DR.qo(), SK.VE{DR.zeroe(), SK.VE.y(yb)})), p => vsp.qx(E.qeval(p, SK.VE.x(yb)))), ID.qzero_ident(SK.VE.y(yb), SK.VE.y(DR.vlin(DR.qo(), SK.VE{SK.VE.x(yb), DR.zeroe()}, DR.qo(), SK.VE{DR.zeroe(), SK.VE.y(yb)})), p => vsp.qy(E.qeval(p, SK.VE.y(yb)))))

def tz.q(+c0: S.Q, +s0: S.Q, +X: S.Q) -> S.Q.eq(DR.qz(), S.Q.sub(S.Q.mul(S.Q.sub(S.Q.mul(c0, DR.qo()), S.Q.mul(s0, DR.qz())), S.Q.add(S.Q.mul(s0, X), S.Q.mul(c0, DR.qz()))),
  S.Q.mul(S.Q.add(S.Q.mul(s0, DR.qo()), S.Q.mul(c0, DR.qz())), S.Q.sub(S.Q.mul(c0, X), S.Q.mul(s0, DR.qz()))))):
  QR.qring_eq([c0, s0, X], E.QCst{DR.qz()}, E.QSub{E.QMul{E.QSub{E.QMul{E.QVar{0n}, E.QCst{DR.qo()}}, E.QMul{E.QVar{1n}, E.QCst{DR.qz()}}}, E.QAdd{E.QMul{E.QVar{1n}, E.QVar{2n}}, E.QMul{E.QVar{0n}, E.QCst{DR.qz()}}}},
    E.QMul{E.QAdd{E.QMul{E.QVar{1n}, E.QCst{DR.qo()}}, E.QMul{E.QVar{0n}, E.QCst{DR.qz()}}}, E.QSub{E.QMul{E.QVar{0n}, E.QVar{2n}}, E.QMul{E.QVar{1n}, E.QCst{DR.qz()}}}}}, {==})

def tz.at(+p: List<&2, S.Q>, +c0: S.Q, +s0: S.Q, +x: E.QExpr) -> S.Q.eq(E.qeval(p, DR.zeroe()), E.qeval(p, SK.VE.cross(DC.lform(DR.Lab{c0, s0}), DR.gmul(DR.Lab{c0, s0}, SK.VE{x, DR.zeroe()})))):
  tz.q(c0, s0, E.qeval(p, x))

# u x (x real) is in Tied(u): cross(u, u x) = 0
def tz(u: DR.Lab, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +du: DR.Der, +x: E.QExpr) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{u, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), DR.gmul(u, SK.VE{x, DR.zeroe()})):
  match u:
    case DR.Lab{+c0, +s0}:
      ST.ri.tr(DC.crosses(es, fs, DR.Lab{c0, s0}, DC.ts.ds(DC.tfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, DR.Lab{c0, s0}, DC.TS{Nil{}, Nil{}}))), DC.ts.rows(DC.tfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, DR.Lab{c0, s0}, DC.TS{Nil{}, Nil{}})), DR.zeroe(), SK.VE.cross(DC.lform(DR.Lab{c0, s0}), DR.gmul(DR.Lab{c0, s0}, SK.VE{x, DR.zeroe()})), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{DR.Lab{c0, s0}, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), ND.sok_coll.t(Some{DC.LD{DR.Lab{c0, s0}, du}}, es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))), ST.ri.z0(DC.crosses(es, fs, DR.Lab{c0, s0}, DC.ts.ds(DC.tfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, DR.Lab{c0, s0}, DC.TS{Nil{}, Nil{}}))), DC.ts.rows(DC.tfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, DR.Lab{c0, s0}, DC.TS{Nil{}, Nil{}})), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{DR.Lab{c0, s0}, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), ND.sok_coll.t(Some{DC.LD{DR.Lab{c0, s0}, du}}, es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H)))),
        ID.qzero_ident(DR.zeroe(), SK.VE.cross(DC.lform(DR.Lab{c0, s0}), DR.gmul(DR.Lab{c0, s0}, SK.VE{x, DR.zeroe()})), p => tz.at(p, c0, s0, x)))

# u y is in Tied(u) when Im y is in K
def tied_u(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +u: DR.Lab, +du: DR.Der, +yb: SK.VE, +hy: {KS.ks.inb(DC.Sk.k(s), SK.VE.y(yb)) == True{} : Bool}) -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{u, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), DR.gmul(u, yb)):
  ST.st_tr(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{u, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), DR.vlin(DR.qo(), DR.gmul(u, SK.VE{SK.VE.x(yb), DR.zeroe()}), DR.qo(), DR.gmul(u, SK.VE{DR.zeroe(), SK.VE.y(yb)})), DR.gmul(u, yb), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{u, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), ND.sok_coll.t(Some{DC.LD{u, du}}, es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))),
    ST.st_lin(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{u, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), DR.qo(), DR.gmul(u, SK.VE{SK.VE.x(yb), DR.zeroe()}), DR.qo(), DR.gmul(u, SK.VE{DR.zeroe(), SK.VE.y(yb)}), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{u, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), ND.sok_coll.t(Some{DC.LD{u, du}}, es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))), tz(u, es, fs, ctx, t, s, H, c, du, SK.VE.x(yb)),
      ND.k2_in(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{u, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), DR.gmul(u, SK.VE{DR.zeroe(), SK.VE.y(yb)}), ND.sok_coll.t(Some{DC.LD{u, du}}, es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)), RR.k2b.x(es, fs, DC.Sk.k(s), DR.gmul(u, SK.VE{DR.zeroe(), SK.VE.y(yb)}), RR.k2_gmul(u, es, fs, DC.Sk.k(s), SK.VE{DR.zeroe(), SK.VE.y(yb)}, ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)), ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H))), hy)),
        RR.k2b.y(es, fs, DC.Sk.k(s), DR.gmul(u, SK.VE{DR.zeroe(), SK.VE.y(yb)}), RR.k2_gmul(u, es, fs, DC.Sk.k(s), SK.VE{DR.zeroe(), SK.VE.y(yb)}, ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)), ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H))), hy)))),
    MG.samevd_sym(DR.gmul(u, yb), DR.vlin(DR.qo(), DR.gmul(u, SK.VE{SK.VE.x(yb), DR.zeroe()}), DR.qo(), DR.gmul(u, SK.VE{DR.zeroe(), SK.VE.y(yb)})), GN.samevd_tr(DR.gmul(u, yb), DR.gmul(u, DR.vlin(DR.qo(), SK.VE{SK.VE.x(yb), DR.zeroe()}, DR.qo(), SK.VE{DR.zeroe(), SK.VE.y(yb)})), DR.vlin(DR.qo(), DR.gmul(u, SK.VE{SK.VE.x(yb), DR.zeroe()}), DR.qo(), DR.gmul(u, SK.VE{DR.zeroe(), SK.VE.y(yb)})), MG.gmul_cong(u, yb, DR.vlin(DR.qo(), SK.VE{SK.VE.x(yb), DR.zeroe()}, DR.qo(), SK.VE{DR.zeroe(), SK.VE.y(yb)}), vsplit(yb)), LA.gmul_vlin(u, DR.qo(), SK.VE{SK.VE.x(yb), DR.zeroe()}, DR.qo(), SK.VE{DR.zeroe(), SK.VE.y(yb)}))))

# a tie parallel to u, times F's set, lies in Tied(u)
def tie_act(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +u: DR.Lab, +du: DR.Der, +wl: DR.Lab, +wb: DR.Lab, +y: SK.VE, +hpar: LS.LSp(u, LS.lab0(), LB.lmul(wl, DR.Lab.conj(wb))), +hy: {KS.ks.inb(DC.Sk.k(s), SK.VE.y(DR.gmul(wb, y))) == True{} : Bool}, +hw: NZ.Nz(wb))
  -> ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{u, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), DR.gmul(wl, y)):
  TU.descale(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{u, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), DC.lnorm(wb), DR.gmul(wl, y), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{u, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), ND.sok_coll.t(Some{DC.LD{u, du}}, es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))),
    ST.st_tr(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{u, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), DR.gmul(LB.lmul(wl, DR.Lab.conj(wb)), DR.gmul(wb, y)), DR.vlin(DC.lnorm(wb), DR.gmul(wl, y), DR.qz(), DR.gmul(wl, y)), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{u, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), ND.sok_coll.t(Some{DC.LD{u, du}}, es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))),
      TC.lsp_in(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{u, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), u, LS.lab0(), LB.lmul(wl, DR.Lab.conj(wb)), DR.gmul(wb, y), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{u, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), ND.sok_coll.t(Some{DC.LD{u, du}}, es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))), hpar, tied_u(es, fs, ctx, t, s, H, c, u, du, DR.gmul(wb, y), hy),
        ST.st_tr(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{u, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), DR.zerov(), DR.gmul(LS.lab0(), DR.gmul(wb, y)), ND.sok_ok(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{u, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), ND.sok_coll.t(Some{DC.LD{u, du}}, es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H))), ND.k2_in(es, fs, t, DC.Sk.k(s), ND.cset(DC.crep.t(Some{DC.LD{u, du}}, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), DR.zerov(), ND.sok_coll.t(Some{DC.LD{u, du}}, es, fs, ctx, t, s, c, RR.h.k(es, fs, ctx, t, s, H), RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.msn(es, fs, ctx, t, s, H), RR.h.lsn(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)), ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H))), ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)))),
          MG.samevd_sym(DR.gmul(LS.lab0(), DR.gmul(wb, y)), DR.zerov(), TU.lzv(LS.lab0(), DR.gmul(wb, y), ({==}, {==}))))),
      TU.unwb(wl, wb, y)), hw)
