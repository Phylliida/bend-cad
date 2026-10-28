# bend-cad: the closure theorem's links (PLAN-sk13b B3, "Turn and
# through"). A stored label is a link's; a rotation that sends each kept
# generator of a hull into a set sends the hull's whole set there (the
# kept generators are among the fold's inputs). Proofs only.

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
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./dcbelowpf.bend as BL
import ./hspacepf.bend as HP
import ./dcturnpf.bend as TU


def absurd(-A: Type, x: Empty) -> A:
  match x:

# Stored labels are links' labels
# -------------------------------

def wat(ws: List<&2, DR.Lab>, n: Nat) -> Maybe<&2, DR.Lab>:
  match ws n:
    case Nil{} n:
      None{}
    case Con{w, t} 0n:
      Some{w}
    case Con{w, t} 1n+k:
      wat(t, k)

def wsome_or(m: Maybe<&2, DR.Lab>, +d: DR.Lab) -> DR.Lab:
  match m:
    case Some{x}:
      x
    case None{}:
      d

def wis_some(m: Maybe<&2, DR.Lab>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

def wsome_inj(+x: DR.Lab, +y: DR.Lab, h: {Some{x} == Some{y} : Maybe<&2, DR.Lab>}) -> {x == y : DR.Lab}:
  Equal.cong(Maybe<&2, DR.Lab>, DR.Lab, m => wsome_or(m, x), Some{x}, Some{y}, h)

def wnone_some(+y: DR.Lab, h: {None{} == Some{y} : Maybe<&2, DR.Lab>}) -> Empty:
  LP.tf(Equal.sym(Bool, False{}, True{}, Equal.cong(Maybe<&2, DR.Lab>, Bool, m => wis_some(m), None{}, Some{y}, h)))

# the link at a position is from c to b, with label w
def lk.ok(m: Maybe<&2, DC.Link>, +c: Nat, +b: DR.Node, +w: DR.Lab) -> Data:
  match m:
    case Some{DC.Link{+c2, +bl, +wl, dl}}:
      SK.Both({SV.eq(c2, c) == True{} : Bool}, SK.Both({DC.node_eq(bl, b) == True{} : Bool}, {wl == w : DR.Lab}))
    case None{}:
      {True{} == False{} : Bool}

def LIn(+ls: List<&2, DC.Link>, +c: Nat, +b: DR.Node, +w: DR.Lab) -> Data:
  Sigma<&2, &2, Nat, n => lk.ok(SH.lat(ls, n), c, b, w)>

def lin_tl.go(+x: DC.Link, +tl: List<&2, DC.Link>, +c: Nat, +b: DR.Node, +w: DR.Lab, +n: Nat, +e: lk.ok(SH.lat(tl, n), c, b, w)) -> LIn(Con{x, tl}, c, b, w):
  (1n+n, e)

def lin_tl(+x: DC.Link, +tl: List<&2, DC.Link>, +c: Nat, +b: DR.Node, +w: DR.Lab, h: LIn(tl, c, b, w)) -> LIn(Con{x, tl}, c, b, w):
  (+n, +e) = h
  lin_tl.go(x, tl, c, b, w, n, e)

def lin_hd(+c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +t: List<&2, DC.Link>, +c: Nat, +b: DR.Node, +w: DR.Lab, +eg: {True{} == SV.band(SV.eq(c2, c), DC.node_eq(bl, b)) : Bool}, ew: {wl == w : DR.Lab})
  -> LIn(Con{DC.Link{c2, bl, wl, dl}, t}, c, b, w):
  (0n, (LP2.band_l(SV.eq(c2, c), DC.node_eq(bl, b), Equal.sym(Bool, True{}, SV.band(SV.eq(c2, c), DC.node_eq(bl, b)), eg)), (LP2.band_r(SV.eq(c2, c), DC.node_eq(bl, b), Equal.sym(Bool, True{}, SV.band(SV.eq(c2, c), DC.node_eq(bl, b)), eg)), ew)))

def lin0.g(g: Bool, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +t: List<&2, DC.Link>, +c: Nat, +b: DR.Node, +w: DR.Lab, +eg: {g == SV.band(SV.eq(c2, c), DC.node_eq(bl, b)) : Bool},
  ej: {wat(DC.lstored.pick(g, wl, DC.lstored(t, c, b)), 0n) == Some{w} : Maybe<&2, DR.Lab>}, ih: {wat(DC.lstored(t, c, b), 0n) == Some{w} : Maybe<&2, DR.Lab>} -> LIn(t, c, b, w)) -> LIn(Con{DC.Link{c2, bl, wl, dl}, t}, c, b, w):
  match g:
    case True{}:
      lin_hd(c2, bl, wl, dl, t, c, b, w, eg, wsome_inj(wl, w, ej))
    case False{}:
      lin_tl(DC.Link{c2, bl, wl, dl}, t, c, b, w, ih(ej))

def lin1.g(g: Bool, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +t: List<&2, DC.Link>, +c: Nat, +b: DR.Node, +w: DR.Lab, +j: Nat, +eg: {g == SV.band(SV.eq(c2, c), DC.node_eq(bl, b)) : Bool},
  ej: {wat(DC.lstored.pick(g, wl, DC.lstored(t, c, b)), 1n+j) == Some{w} : Maybe<&2, DR.Lab>}, iha: {wat(DC.lstored(t, c, b), j) == Some{w} : Maybe<&2, DR.Lab>} -> LIn(t, c, b, w),
  ihb: {wat(DC.lstored(t, c, b), 1n+j) == Some{w} : Maybe<&2, DR.Lab>} -> LIn(t, c, b, w)) -> LIn(Con{DC.Link{c2, bl, wl, dl}, t}, c, b, w):
  match g:
    case True{}:
      lin_tl(DC.Link{c2, bl, wl, dl}, t, c, b, w, iha(ej))
    case False{}:
      lin_tl(DC.Link{c2, bl, wl, dl}, t, c, b, w, ihb(ej))

# a stored label is the label of a link from c to b
def lin_of(ls: List<&2, DC.Link>, j: Nat, +c: Nat, +b: DR.Node, +w: DR.Lab, ej: {wat(DC.lstored(ls, c, b), j) == Some{w} : Maybe<&2, DR.Lab>}) -> LIn(ls, c, b, w):
  match ls j:
    case Nil{} j:
      absurd(LIn(Nil{}, c, b, w), wnone_some(w, ej))
    case Con{DC.Link{+c2, +bl, +wl, +dl}, +t} 0n:
      lin0.g(SV.band(SV.eq(c2, c), DC.node_eq(bl, b)), c2, bl, wl, dl, t, c, b, w, {==}, ej, x => lin_of(t, 0n, c, b, w, x))
    case Con{DC.Link{+c2, +bl, +wl, +dl}, +t} 1n++jj:
      lin1.g(SV.band(SV.eq(c2, c), DC.node_eq(bl, b)), c2, bl, wl, dl, t, c, b, w, jj, {==}, ej, x => lin_of(t, jj, c, b, w, x), x => lin_of(t, 1n+jj, c, b, w, x))

# a label read off the stored ones: 0, or a link's
def lzor.f(f: Bool, +ls: List<&2, DC.Link>, +c: Nat, +b: DR.Node, +w: DR.Lab) -> Data:
  match f:
    case True{}:
      {w == LS.lab0() : DR.Lab}
    case False{}:
      LIn(ls, c, b, w)

def LZor(+ls: List<&2, DC.Link>, +c: Nat, +b: DR.Node, +w: DR.Lab) -> Data:
  Sigma<&2, &2, Bool, f => lzor.f(f, ls, c, b, w)>

def lat0_of.s(st: List<&2, DR.Lab>, +ls: List<&2, DC.Link>, +c: Nat, +b: DR.Node, est: {DC.lstored(ls, c, b) == st : List<&2, DR.Lab>}) -> LZor(ls, c, b, LS.lat0(st)):
  match st:
    case Nil{}:
      (True{}, {==})
    case Con{+w0, +t}:
      (False{}, lin_of(ls, 0n, c, b, w0, Equal.cong(List<&2, DR.Lab>, Maybe<&2, DR.Lab>, l => wat(l, 0n), DC.lstored(ls, c, b), Con{w0, t}, est)))

def lat1_of.s(st: List<&2, DR.Lab>, +ls: List<&2, DC.Link>, +c: Nat, +b: DR.Node, est: {DC.lstored(ls, c, b) == st : List<&2, DR.Lab>}) -> LZor(ls, c, b, LS.lat1(st)):
  match st:
    case Nil{}:
      (True{}, {==})
    case Con{+w0, Nil{}}:
      (True{}, {==})
    case Con{+w0, Con{+w1, +t}}:
      (False{}, lin_of(ls, 1n, c, b, w1, Equal.cong(List<&2, DR.Lab>, Maybe<&2, DR.Lab>, l => wat(l, 1n), DC.lstored(ls, c, b), Con{w0, Con{w1, t}}, est)))

# the first two stored labels: each 0 or a link's
def lat0_of(+ls: List<&2, DC.Link>, +c: Nat, +b: DR.Node) -> LZor(ls, c, b, LS.lat0(DC.lstored(ls, c, b))):
  lat0_of.s(DC.lstored(ls, c, b), ls, c, b, {==})

def lat1_of(+ls: List<&2, DC.Link>, +c: Nat, +b: DR.Node) -> LZor(ls, c, b, LS.lat1(DC.lstored(ls, c, b))):
  lat1_of.s(DC.lstored(ls, c, b), ls, c, b, {==})

# Records of links
# ----------------

def lok_at(ls: List<&2, DC.Link>, n: Nat, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +l: DC.Link,
  en: {SH.lat(ls, n) == Some{l} : Maybe<&2, DC.Link>}, h: GN.LsOk(es, fs, ctx, t, ls)) -> GN.LOkD(es, fs, ctx, t, l):
  match ls n:
    case Nil{} n:
      absurd(GN.LOkD(es, fs, ctx, t, l), SH.lnone_some(l, en))
    case Con{+l0, tl} 0n:
      (a, rt) = h
      %SH.lsome_inj(l0, l, en) : GN.LOkD(es, fs, ctx, t, _)
      a
    case Con{+l0, tl} 1n+j:
      (a, rt) = h
      lok_at(tl, j, es, fs, ctx, t, l, en, rt)

# a link's derivation proves par(c, ·)
def lok.a(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, +b: DR.Node, +w: DR.Lab, +d: DR.Der, h: GN.LOkD(es, fs, ctx, t, DC.Link{c, b, w, d}))
  -> {DR.Jd.a(DR.concl(es, fs, d)) == DR.NSeg{c} : DR.Node}:
  (h1, r1) = h
  (h2, r2) = r1
  (h3, r3) = r2
  h3

# Pushing a rotation through a hull
# ---------------------------------

# every listed generator's form, rotated by L, is in st
def AllD(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +st: ST.St, +L: DR.Lab) -> Data:
  match ds:
    case Nil{}:
      Unit
    case Con{+d, tl}:
      SK.Both(ST.InSt(es, fs, k, st, DR.gmul(L, DR.Jd.x(DR.concl(es, fs, d)))), AllD(tl, es, fs, k, st, L))

def alld_snoc(ds: List<&2, DR.Der>, +d: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +st: ST.St, +L: DR.Lab, h: AllD(ds, es, fs, k, st, L), hd: ST.InSt(es, fs, k, st, DR.gmul(L, DR.Jd.x(DR.concl(es, fs, d))))) -> AllD(KS.dsnoc(ds, d), es, fs, k, st, L):
  match ds:
    case Nil{}:
      (hd, Unit{})
    case Con{+d0, t}:
      (h1, h2) = h
      (h1, alld_snoc(t, d, es, fs, k, st, L, h2, hd))

def hadd.pick(b: Bool, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +r: EL.Res, +d: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +st: ST.St, +L: DR.Lab, hh: AllD(ds, es, fs, k, st, L), hd: ST.InSt(es, fs, k, st, DR.gmul(L, DR.Jd.x(DR.concl(es, fs, d)))))
  -> AllD(HS.hs.ds(HS.hs.pick(b, rows, ds, r, d)), es, fs, k, st, L):
  match b:
    case True{}:
      hh
    case False{}:
      alld_snoc(ds, d, es, fs, k, st, L, hh, hd)

def hadd_alld(h: HS.HS, +t: Nat, +d: DR.Der, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +st: ST.St, +L: DR.Lab, hh: AllD(HS.hs.ds(h), es, fs, k, st, L), hd: ST.InSt(es, fs, k, st, DR.gmul(L, DR.Jd.x(DR.concl(es, fs, d))))) -> AllD(HS.hs.ds(HS.hs.add(es, fs, t, h, d)), es, fs, k, st, L):
  match h:
    case HS.HS{+rows, +ds}:
      hadd.pick(EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), rows, ds, EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), d, es, fs, k, st, L, hh, hd)

# the kept generators are among the inputs
def hfold_alld(ds: List<&2, DR.Der>, +h: HS.HS, +t: Nat, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +st: ST.St, +L: DR.Lab, hds: AllD(ds, es, fs, k, st, L), hh: AllD(HS.hs.ds(h), es, fs, k, st, L)) -> AllD(HS.hs.ds(DC.hfold(ds, es, fs, t, h)), es, fs, k, st, L):
  match ds:
    case Nil{}:
      hh
    case Con{+d, tl}:
      (h1, h2) = hds
      hfold_alld(tl, HS.hs.add(es, fs, t, h, d), t, es, fs, k, st, L, h2, hadd_alld(h, t, d, es, fs, k, st, L, hh, h1))

def push_ds(ls: List<&2, S.Q>, ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +st: ST.St, +L: DR.Lab, +t: Nat, +r: DR.Node, +ok: ST.StOk(es, fs, t, k, st), +hz: ST.InSt(es, fs, k, st, DR.gmul(L, DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))), h: AllD(ds, es, fs, k, st, L))
  -> ST.InSt(es, fs, k, st, DR.gmul(L, HS.clin(es, r, ls, HS.hxs(es, fs, ds)))):
  match ls ds:
    case Con{+l, +lt} Con{+d, +dt}:
      (h1, h2) = h
      ST.st_tr(es, fs, t, k, st, DR.vlin(l, DR.gmul(L, DR.Jd.x(DR.concl(es, fs, d))), DR.qo(), DR.gmul(L, HS.clin(es, r, lt, HS.hxs(es, fs, dt)))), DR.gmul(L, DR.vlin(l, DR.Jd.x(DR.concl(es, fs, d)), DR.qo(), HS.clin(es, r, lt, HS.hxs(es, fs, dt)))), ok,
        ST.st_lin(es, fs, t, k, st, l, DR.gmul(L, DR.Jd.x(DR.concl(es, fs, d))), DR.qo(), DR.gmul(L, HS.clin(es, r, lt, HS.hxs(es, fs, dt))), ok, h1, push_ds(lt, dt, es, fs, k, st, L, t, r, ok, hz, h2)),
        MG.samevd_sym(DR.gmul(L, DR.vlin(l, DR.Jd.x(DR.concl(es, fs, d)), DR.qo(), HS.clin(es, r, lt, HS.hxs(es, fs, dt)))), DR.vlin(l, DR.gmul(L, DR.Jd.x(DR.concl(es, fs, d))), DR.qo(), DR.gmul(L, HS.clin(es, r, lt, HS.hxs(es, fs, dt)))), LA.gmul_vlin(L, l, DR.Jd.x(DR.concl(es, fs, d)), DR.qo(), HS.clin(es, r, lt, HS.hxs(es, fs, dt)))))
    case Nil{} ds:
      hz
    case Con{+l, +lt} Nil{}:
      hz

def push.go(+h: HS.HS, +r: DR.Node, +y: SK.VE, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +st: ST.St, +L: DR.Lab, +t: Nat, +ok: ST.StOk(es, fs, t, k, st), +hz: ST.InSt(es, fs, k, st, DR.gmul(L, DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))), +ls: List<&2, S.Q>,
  +sv: VD.SameVD(y, HS.clin(es, r, ls, HS.hxs(es, fs, HS.hs.ds(h)))), hall: AllD(HS.hs.ds(h), es, fs, k, st, L)) -> ST.InSt(es, fs, k, st, DR.gmul(L, y)):
  ST.st_tr(es, fs, t, k, st, DR.gmul(L, HS.clin(es, r, ls, HS.hxs(es, fs, HS.hs.ds(h)))), DR.gmul(L, y), ok, push_ds(ls, HS.hs.ds(h), es, fs, k, st, L, t, r, ok, hz, hall),
    MG.gmul_cong(L, HS.clin(es, r, ls, HS.hxs(es, fs, HS.hs.ds(h))), y, MG.samevd_sym(y, HS.clin(es, r, ls, HS.hxs(es, fs, HS.hs.ds(h))), sv)))

# a hull's set, rotated by L, is in st when its kept generators are
def push(+h: HS.HS, +r: DR.Node, +y: SK.VE, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +st: ST.St, +L: DR.Lab, +t: Nat, +ok: ST.StOk(es, fs, t, k, st), +hz: ST.InSt(es, fs, k, st, DR.gmul(L, DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))), hin: ST.HIn(es, fs, r, h, y), hall: AllD(HS.hs.ds(h), es, fs, k, st, L))
  -> ST.InSt(es, fs, k, st, DR.gmul(L, y)):
  (+ls, +sv) = hin
  push.go(h, r, y, es, fs, k, st, L, t, ok, hz, ls, sv, hall)

# K squared in a set, rotated
# ---------------------------

def vz.q(+X: S.Q) -> S.Q.eq(DR.qz(), S.Q.add(S.Q.mul(DR.qz(), X), S.Q.mul(DR.qz(), X))):
  QR.qring_eq([X], E.QCst{DR.qz()}, E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}}, {==})

# a form with both parts in K, rotated, is in a set holding K squared
def k2r(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +st: ST.St, +L: DR.Lab, +y: SK.VE, +sok: ND.SOk(es, fs, t, k, st), +kr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)),
  +hx: {KS.ks.inb(k, SK.VE.x(y)) == True{} : Bool}, +hy: {KS.ks.inb(k, SK.VE.y(y)) == True{} : Bool}) -> ST.InSt(es, fs, k, st, DR.gmul(L, y)):
  ND.k2_in(es, fs, t, k, st, DR.gmul(L, y), sok, kr, RR.k2b.x(es, fs, k, DR.gmul(L, y), RR.k2_gmul(L, es, fs, k, y, kr, hx, hy)), RR.k2b.y(es, fs, k, DR.gmul(L, y), RR.k2_gmul(L, es, fs, k, y, kr, hx, hy)))

# 0 z + 0 z, rotated, is in it
def hz0(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +st: ST.St, +L: DR.Lab, +z: SK.VE, +sok: ND.SOk(es, fs, t, k, st), +kr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k))) -> ST.InSt(es, fs, k, st, DR.gmul(L, DR.vlin(DR.qz(), z, DR.qz(), z))):
  k2r(es, fs, t, k, st, L, DR.vlin(DR.qz(), z, DR.qz(), z), sok, kr,
    ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), DR.zeroe(), SK.VE.x(DR.vlin(DR.qz(), z, DR.qz(), z)), kr, ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), kr), ID.qzero_ident(DR.zeroe(), SK.VE.x(DR.vlin(DR.qz(), z, DR.qz(), z)), p => vz.q(E.qeval(p, SK.VE.x(z))))),
    ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), DR.zeroe(), SK.VE.y(DR.vlin(DR.qz(), z, DR.qz(), z)), kr, ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), kr), ID.qzero_ident(DR.zeroe(), SK.VE.y(DR.vlin(DR.qz(), z, DR.qz(), z)), p => vz.q(E.qeval(p, SK.VE.y(z))))))

def kg.re(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +st: ST.St, +L: DR.Lab, +r: DR.Node, +dk: DR.Der, +sok: ND.SOk(es, fs, t, k, st), +kr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)), +he: {KS.ks.inb(k, DR.Jd.e(DR.concl(es, fs, dk))) == True{} : Bool}) -> ST.InSt(es, fs, k, st, DR.gmul(L, DR.Jd.x(DR.concl(es, fs, HS.kre(r, dk))))):
  ST.st_tr(es, fs, t, k, st, DR.gmul(L, ST.kv.re(DR.Jd.e(DR.concl(es, fs, dk)))), DR.gmul(L, DR.Jd.x(DR.concl(es, fs, HS.kre(r, dk)))), ND.sok_ok(es, fs, t, k, st, sok),
    k2r(es, fs, t, k, st, L, ST.kv.re(DR.Jd.e(DR.concl(es, fs, dk))), sok, kr, he, ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), kr)),
    MG.gmul_cong(L, ST.kv.re(DR.Jd.e(DR.concl(es, fs, dk))), DR.Jd.x(DR.concl(es, fs, HS.kre(r, dk))), MG.samevd_sym(DR.Jd.x(DR.concl(es, fs, HS.kre(r, dk))), ST.kv.re(DR.Jd.e(DR.concl(es, fs, dk))), ND.kre_v(es, fs, r, dk))))

def kg.im(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +st: ST.St, +L: DR.Lab, +r: DR.Node, +dk: DR.Der, +sok: ND.SOk(es, fs, t, k, st), +kr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)), +he: {KS.ks.inb(k, DR.Jd.e(DR.concl(es, fs, dk))) == True{} : Bool}) -> ST.InSt(es, fs, k, st, DR.gmul(L, DR.Jd.x(DR.concl(es, fs, HS.kim(r, dk))))):
  ST.st_tr(es, fs, t, k, st, DR.gmul(L, ST.kv.im(DR.Jd.e(DR.concl(es, fs, dk)))), DR.gmul(L, DR.Jd.x(DR.concl(es, fs, HS.kim(r, dk)))), ND.sok_ok(es, fs, t, k, st, sok),
    k2r(es, fs, t, k, st, L, ST.kv.im(DR.Jd.e(DR.concl(es, fs, dk))), sok, kr, ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), kr), he),
    MG.gmul_cong(L, ST.kv.im(DR.Jd.e(DR.concl(es, fs, dk))), DR.Jd.x(DR.concl(es, fs, HS.kim(r, dk))), MG.samevd_sym(DR.Jd.x(DR.concl(es, fs, HS.kim(r, dk))), ST.kv.im(DR.Jd.e(DR.concl(es, fs, dk))), ND.kim_v(es, fs, r, dk))))

# K squared's generators, rotated, are in a set holding K squared
def alld_kg(kds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +st: ST.St, +L: DR.Lab, +r: DR.Node, +sok: ND.SOk(es, fs, t, k, st), +kr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)), ha: OP.AllIn(KS.kexprs(es, fs, kds), KS.kexprs(es, fs, KS.ks.ds(k))))
  -> AllD(DC.kgens(r, kds), es, fs, k, st, L):
  match kds:
    case Nil{}:
      Unit{}
    case Con{+dk, kt}:
      (+h1, h2) = ha
      (kg.re(es, fs, t, k, st, L, r, dk, sok, kr, ST.ri.zero(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), DR.Jd.e(DR.concl(es, fs, dk)), kr, h1)),
       (kg.im(es, fs, t, k, st, L, r, dk, sok, kr, ST.ri.zero(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), DR.Jd.e(DR.concl(es, fs, dk)), kr, h1)), alld_kg(kt, es, fs, t, k, st, L, r, sok, kr, h2)))

# Links' generators, by position
# ------------------------------

def dpk.hd(b: Bool, +x: DR.Der, +rest: List<&2, DR.Der>, eb: {b == True{} : Bool}) -> ST.InD(x, DC.dpick(b, x, rest)):
  match b:
    case True{}:
      ST.ind_hd(x, rest)
    case False{}:
      absurd(ST.InD(x, rest), LP.tf(Equal.sym(Bool, False{}, True{}, eb)))

def dpk.tl(b: Bool, +x: DR.Der, +rest: List<&2, DR.Der>, +g: DR.Der, h: ST.InD(g, rest)) -> ST.InD(g, DC.dpick(b, x, rest)):
  match b:
    case True{}:
      ST.ind_tl(g, x, rest, h)
    case False{}:
      h

# the turn of a link to member a, passed through a, is among a's link generators
def ll_in(ls: List<&2, DC.Link>, n: Nat, +a: DR.Node, +wa: DR.Lab, +da: DR.Der, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, en: {SH.lat(ls, n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>}, +hb: {DC.node_eq(bl, a) == True{} : Bool})
  -> ST.InD(DC.thr(da, wa, a, DR.DTurn{dl, DR.Lab.conj(wl), a}), DC.llinks(ls, a, wa, da)):
  match ls n:
    case Nil{} n:
      absurd(ST.InD(DC.thr(da, wa, a, DR.DTurn{dl, DR.Lab.conj(wl), a}), Nil{}), SH.lnone_some(DC.Link{c2, bl, wl, dl}, en))
    case Con{DC.Link{+c3, +b3, +w3, +d3}, +t} 0n:
      %Equal.sym(DC.Link, DC.Link{c3, b3, w3, d3}, DC.Link{c2, bl, wl, dl}, SH.lsome_inj(DC.Link{c3, b3, w3, d3}, DC.Link{c2, bl, wl, dl}, en)) : ST.InD(DC.thr(da, wa, a, DR.DTurn{dl, DR.Lab.conj(wl), a}), DC.llinks(Con{_, t}, a, wa, da))
      dpk.hd(DC.node_eq(bl, a), DC.thr(da, wa, a, DR.DTurn{dl, DR.Lab.conj(wl), a}), DC.llinks(t, a, wa, da), hb)
    case Con{DC.Link{+c3, +b3, +w3, +d3}, +t} 1n+j:
      dpk.tl(DC.node_eq(b3, a), DC.thr(da, wa, a, DR.DTurn{d3, DR.Lab.conj(w3), a}), DC.llinks(t, a, wa, da), DC.thr(da, wa, a, DR.DTurn{dl, DR.Lab.conj(wl), a}), ll_in(t, j, a, wa, da, c2, bl, wl, dl, en, hb))

# the turn of a link into collapsed c is among c's in-link generators
def li_in(ls: List<&2, DC.Link>, n: Nat, +c: Nat, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, en: {SH.lat(ls, n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>}, +hb: {DC.node_eq(bl, DR.NSeg{c}) == True{} : Bool})
  -> ST.InD(DR.DTurn{dl, DR.Lab.conj(wl), DR.NSeg{c}}, DC.lins(ls, c)):
  match ls n:
    case Nil{} n:
      absurd(ST.InD(DR.DTurn{dl, DR.Lab.conj(wl), DR.NSeg{c}}, Nil{}), SH.lnone_some(DC.Link{c2, bl, wl, dl}, en))
    case Con{DC.Link{+c3, +b3, +w3, +d3}, +t} 0n:
      %Equal.sym(DC.Link, DC.Link{c3, b3, w3, d3}, DC.Link{c2, bl, wl, dl}, SH.lsome_inj(DC.Link{c3, b3, w3, d3}, DC.Link{c2, bl, wl, dl}, en)) : ST.InD(DR.DTurn{dl, DR.Lab.conj(wl), DR.NSeg{c}}, DC.lins(Con{_, t}, c))
      dpk.hd(DC.node_eq(bl, DR.NSeg{c}), DR.DTurn{dl, DR.Lab.conj(wl), DR.NSeg{c}}, DC.lins(t, c), hb)
    case Con{DC.Link{+c3, +b3, +w3, +d3}, +t} 1n+j:
      dpk.tl(DC.node_eq(b3, DR.NSeg{c}), DR.DTurn{d3, DR.Lab.conj(w3), DR.NSeg{c}}, DC.lins(t, c), DR.DTurn{dl, DR.Lab.conj(wl), DR.NSeg{c}}, li_in(t, j, c, c2, bl, wl, dl, en, hb))

# what a link from c gives c is among c's out-link generators
def lo_in(ls: List<&2, DC.Link>, n: Nat, +c: Nat, +fs: List<&2, DR.Fact>, +ms: List<&2, DC.Mem>, +all: List<&2, DC.Link>, +c2: Nat, +bl: DR.Node, +wl: DR.Lab, +dl: DR.Der, +g: DR.Der, en: {SH.lat(ls, n) == Some{DC.Link{c2, bl, wl, dl}} : Maybe<&2, DC.Link>},
  +ec: {SV.eq(c2, c) == True{} : Bool}, hg: ST.InD(g, Con{dl, DC.lout.mem(DC.mem_of(ms, bl), fs, ms, all, bl, wl, dl)})) -> ST.InD(g, DC.louts(ls, c, fs, ms, all)):
  match ls n:
    case Nil{} n:
      absurd(ST.InD(g, Nil{}), SH.lnone_some(DC.Link{c2, bl, wl, dl}, en))
    case Con{DC.Link{+c3, +b3, +w3, +d3}, +t} 0n:
      %Equal.sym(DC.Link, DC.Link{c3, b3, w3, d3}, DC.Link{c2, bl, wl, dl}, SH.lsome_inj(DC.Link{c3, b3, w3, d3}, DC.Link{c2, bl, wl, dl}, en)) : ST.InD(g, DC.louts(Con{_, t}, c, fs, ms, all))
      RR.rgi.hd(SV.eq(c2, c), g, Con{dl, DC.lout.mem(DC.mem_of(ms, bl), fs, ms, all, bl, wl, dl)}, DC.louts(t, c, fs, ms, all), ec, hg)
    case Con{DC.Link{+c3, +b3, +w3, +d3}, +t} 1n+j:
      RR.rgi.tl(SV.eq(c3, c), g, Con{d3, DC.lout.mem(DC.mem_of(ms, b3), fs, ms, all, b3, w3, d3)}, DC.louts(t, c, fs, ms, all), lo_in(t, j, c, fs, ms, all, c2, bl, wl, dl, g, en, ec, hg))

def lg.at(+h: DR.Der, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der) -> DR.Der:
  DR.DThrough{dl, DR.DThrough{DR.DTurn{db, DR.Lab.conj(wb), b}, h, wb, rb}, DR.Lab.conj(wl), b}

def lg_in.go(hs: List<&2, DR.Der>, j: Nat, +h: DR.Der, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, ej: {ST.dat(hs, j) == Some{h} : Maybe<&2, DR.Der>})
  -> {ST.dat(DC.lout.gens(hs, b, wl, dl, rb, wb, db), j) == Some{lg.at(h, b, wl, dl, rb, wb, db)} : Maybe<&2, DR.Der>}:
  match hs j:
    case Nil{} j:
      absurd({None{} == Some{lg.at(h, b, wl, dl, rb, wb, db)} : Maybe<&2, DR.Der>}, ST.dnone_some(h, ej))
    case Con{+h0, +tl} 0n:
      Equal.cong(DR.Der, Maybe<&2, DR.Der>, q => Some{lg.at(q, b, wl, dl, rb, wb, db)}, h0, h, ST.dsome_inj(h0, h, ej))
    case Con{+h0, +tl} 1n+m:
      lg_in.go(tl, m, h, b, wl, dl, rb, wb, db, ej)

def lg_in.n(+hs: List<&2, DR.Der>, +j: Nat, +h: DR.Der, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +ej: {ST.dat(hs, j) == Some{h} : Maybe<&2, DR.Der>})
  -> ST.InD(lg.at(h, b, wl, dl, rb, wb, db), DC.lout.gens(hs, b, wl, dl, rb, wb, db)):
  (j, lg_in.go(hs, j, h, b, wl, dl, rb, wb, db, ej))

# a root's generator, turned through b along a link, is among the link's
def lg_in(+hs: List<&2, DR.Der>, +h: DR.Der, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, hh: ST.InD(h, hs))
  -> ST.InD(lg.at(h, b, wl, dl, rb, wb, db), DC.lout.gens(hs, b, wl, dl, rb, wb, db)):
  (+j, +ej) = hh
  lg_in.n(hs, j, h, b, wl, dl, rb, wb, db, ej)

def dcat_snoc(pre: List<&2, DR.Der>, +h: DR.Der, +xt: List<&2, DR.Der>) -> {DC.dcat(KS.dsnoc(pre, h), xt) == DC.dcat(pre, Con{h, xt}) : List<&2, DR.Der>}:
  match pre:
    case Nil{}:
      {==}
    case Con{+p, pt}:
      Equal.cong(List<&2, DR.Der>, List<&2, DR.Der>, l => Con{p, l}, DC.dcat(KS.dsnoc(pt, h), xt), DC.dcat(pt, Con{h, xt}), dcat_snoc(pt, h, xt))

# A collapsed node not in K squared is a checked segment
# ------------------------------------------------------

def ipick_tl(f: Bool, +c: Nat, +i: Nat, +rest: List<&2, Nat>, h: {RF.imem(c, rest) == True{} : Bool}) -> {RF.imem(c, DC.ids.pick(f, i, rest)) == True{} : Bool}:
  match f:
    case True{}:
      SH.bor_r(SV.eq(c, i), RF.imem(c, rest), h)
    case False{}:
      h

def ipick_hd(f: Bool, +c: Nat, +rest: List<&2, Nat>, ef: {f == True{} : Bool}) -> {RF.imem(c, DC.ids.pick(f, c, rest)) == True{} : Bool}:
  match f:
    case True{}:
      %Equal.sym(Bool, SV.eq(c, c), True{}, LP2.eq_refl(c)) : {SV.bor(_, RF.imem(c, rest)) == True{} : Bool}
      {==}
    case False{}:
      absurd({RF.imem(c, rest) == True{} : Bool}, LP.tf(Equal.sym(Bool, False{}, True{}, ef)))

def cids.g(g: Bool, +c: Nat, +s0: Nat, +tl: List<&2, Nat>, +es: List<&2, SK.Ent>, +cs: DC.SP, eg: {g == SV.eq(c, s0) : Bool}, hn: {SV.bor(g, SH.nmem(DR.NSeg{c}, DC.snodes(tl))) == True{} : Bool},
  +hc: {DC.coll(es, cs, c) == True{} : Bool}, ih: {SH.nmem(DR.NSeg{c}, DC.snodes(tl)) == True{} : Bool} -> {RF.imem(c, DC.cids(tl, es, cs)) == True{} : Bool})
  -> {RF.imem(c, DC.cids(Con{s0, tl}, es, cs)) == True{} : Bool}:
  match g:
    case True{}:
      %LP2.eq_ok(c, s0, Equal.sym(Bool, True{}, SV.eq(c, s0), eg)) : {RF.imem(c, DC.cids(Con{_, tl}, es, cs)) == True{} : Bool}
      ipick_hd(DC.coll(es, cs, c), c, DC.cids(tl, es, cs), hc)
    case False{}:
      ipick_tl(DC.coll(es, cs, s0), c, s0, DC.cids(tl, es, cs), ih(hn))

# a segment collapsed in the context is among the collapsed ids
def cids_in(ids: List<&2, Nat>, +c: Nat, +es: List<&2, SK.Ent>, +cs: DC.SP, hn: {SH.nmem(DR.NSeg{c}, DC.snodes(ids)) == True{} : Bool}, +hc: {DC.coll(es, cs, c) == True{} : Bool})
  -> {RF.imem(c, DC.cids(ids, es, cs)) == True{} : Bool}:
  match ids:
    case Nil{}:
      absurd({False{} == True{} : Bool}, LP.tf(Equal.sym(Bool, False{}, True{}, hn)))
    case Con{+s0, +tl}:
      cids.g(SV.eq(c, s0), c, s0, tl, es, cs, {==}, hn, hc, x => cids_in(tl, c, es, cs, x, hc))

def kz.q(+p: List<&2, S.Q>) -> S.Q.eq(DR.qz(), S.Q.sub(E.qeval(p, SK.var(0n)), E.qeval(p, SK.var(0n)))):
  LQ.q_sym(S.Q.sub(E.qeval(p, SK.var(0n)), E.qeval(p, SK.var(0n))), DR.qz(), RR.zc.q(E.qeval(p, SK.var(0n))))

def kz.x(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s)) -> {KS.ks.inb(DC.Sk.k(s), SK.VE.x(SK.Seg.dir(SK.Seg{SK.Pt{0n, 0n}, SK.Pt{0n, 0n}}))) == True{} : Bool}:
  ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), DR.zeroe(), SK.VE.x(SK.Seg.dir(SK.Seg{SK.Pt{0n, 0n}, SK.Pt{0n, 0n}})), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)), ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H))), ID.qzero_ident(DR.zeroe(), SK.VE.x(SK.Seg.dir(SK.Seg{SK.Pt{0n, 0n}, SK.Pt{0n, 0n}})), p => kz.q(p)))

def kz.y(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s)) -> {KS.ks.inb(DC.Sk.k(s), SK.VE.y(SK.Seg.dir(SK.Seg{SK.Pt{0n, 0n}, SK.Pt{0n, 0n}}))) == True{} : Bool}:
  ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), DR.zeroe(), SK.VE.y(SK.Seg.dir(SK.Seg{SK.Pt{0n, 0n}, SK.Pt{0n, 0n}})), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H)), ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)), ST.kri(es, fs, ctx, t, DC.Sk.k(s), RR.h.k(es, fs, ctx, t, s, H))), ID.qzero_ident(DR.zeroe(), SK.VE.y(SK.Seg.dir(SK.Seg{SK.Pt{0n, 0n}, SK.Pt{0n, 0n}})), p => kz.q(p)))

def fz0(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s)) -> {SV.band(KS.ks.inb(DC.Sk.k(s), SK.VE.x(SK.Seg.dir(SK.Seg{SK.Pt{0n, 0n}, SK.Pt{0n, 0n}}))), KS.ks.inb(DC.Sk.k(s), SK.VE.y(SK.Seg.dir(SK.Seg{SK.Pt{0n, 0n}, SK.Pt{0n, 0n}})))) == True{} : Bool}:
  %Equal.sym(Bool, KS.ks.inb(DC.Sk.k(s), SK.VE.x(SK.Seg.dir(SK.Seg{SK.Pt{0n, 0n}, SK.Pt{0n, 0n}}))), True{}, kz.x(es, fs, ctx, t, s, H)) : {SV.band(_, KS.ks.inb(DC.Sk.k(s), SK.VE.y(SK.Seg.dir(SK.Seg{SK.Pt{0n, 0n}, SK.Pt{0n, 0n}})))) == True{} : Bool}
  kz.y(es, fs, ctx, t, s, H)

def nf(+es: List<&2, SK.Ent>, +k: KS.KS, +c: Nat, e: {DC.fullc(es, k, c) == True{} : Bool}, hf: {DC.fullc(es, k, c) == False{} : Bool}) -> Empty:
  LP.tf(Equal.trans(Bool, True{}, DC.fullc(es, k, c), False{}, Equal.sym(Bool, DC.fullc(es, k, c), True{}, e), hf))

def fz.p(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +x: Nat, +y: Nat, eg: {SK.find(c, es) == Some{SK.GPoint{x, y}} : Maybe<&2, SK.Geo>}) -> {DC.fullc(es, DC.Sk.k(s), c) == True{} : Bool}:
  %Equal.sym(Maybe<&2, SK.Geo>, SK.find(c, es), Some{SK.GPoint{x, y}}, eg) : {SV.band(KS.ks.inb(DC.Sk.k(s), SK.VE.x(SK.Seg.dir(SK.seg.of(es, _)))), KS.ks.inb(DC.Sk.k(s), SK.VE.y(SK.Seg.dir(SK.seg.of(es, _))))) == True{} : Bool}
  fz0(es, fs, ctx, t, s, H)

def fz.c(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +x: Nat, +y: Nat, eg: {SK.find(c, es) == Some{SK.GCirc{x, y}} : Maybe<&2, SK.Geo>}) -> {DC.fullc(es, DC.Sk.k(s), c) == True{} : Bool}:
  %Equal.sym(Maybe<&2, SK.Geo>, SK.find(c, es), Some{SK.GCirc{x, y}}, eg) : {SV.band(KS.ks.inb(DC.Sk.k(s), SK.VE.x(SK.Seg.dir(SK.seg.of(es, _)))), KS.ks.inb(DC.Sk.k(s), SK.VE.y(SK.Seg.dir(SK.seg.of(es, _))))) == True{} : Bool}
  fz0(es, fs, ctx, t, s, H)

def fz.a(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +x: Nat, +y: Nat, +z: Nat, eg: {SK.find(c, es) == Some{SK.GArc{x, y, z}} : Maybe<&2, SK.Geo>}) -> {DC.fullc(es, DC.Sk.k(s), c) == True{} : Bool}:
  %Equal.sym(Maybe<&2, SK.Geo>, SK.find(c, es), Some{SK.GArc{x, y, z}}, eg) : {SV.band(KS.ks.inb(DC.Sk.k(s), SK.VE.x(SK.Seg.dir(SK.seg.of(es, _)))), KS.ks.inb(DC.Sk.k(s), SK.VE.y(SK.Seg.dir(SK.seg.of(es, _))))) == True{} : Bool}
  fz0(es, fs, ctx, t, s, H)

def fz.n(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, eg: {SK.find(c, es) == None{} : Maybe<&2, SK.Geo>}) -> {DC.fullc(es, DC.Sk.k(s), c) == True{} : Bool}:
  %Equal.sym(Maybe<&2, SK.Geo>, SK.find(c, es), None{}, eg) : {SV.band(KS.ks.inb(DC.Sk.k(s), SK.VE.x(SK.Seg.dir(SK.seg.of(es, _)))), KS.ks.inb(DC.Sk.k(s), SK.VE.y(SK.Seg.dir(SK.seg.of(es, _))))) == True{} : Bool}
  fz0(es, fs, ctx, t, s, H)

def cinfo.g(g: SK.Geo, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +eg: {SK.find(c, es) == Some{g} : Maybe<&2, SK.Geo>}, emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}, hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool}) -> {RF.imem(c, DC.cids(DC.segids(es), es, OP.cspan(ctx))) == True{} : Bool}:
  match g:
    case SK.GPoint{+x, +y}:
      absurd({RF.imem(c, DC.cids(DC.segids(es), es, OP.cspan(ctx))) == True{} : Bool}, nf(es, DC.Sk.k(s), c, fz.p(es, fs, ctx, t, s, H, c, x, y, eg), hf))
    case SK.GSeg{+p, +q}:
      cids_in(DC.segids(es), c, es, OP.cspan(ctx), RR.seg_in(es, c, p, q, eg), RR.bor_f(DC.coll(es, OP.cspan(ctx), c), RR.mn_none(DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}), DC.coll(es, OP.cspan(ctx), c), emc,
        RR.recs_at(DC.segids(es), c, es, OP.cspan(ctx), DC.Sk.ms(s), SH.sh.rs(es, OP.cspan(ctx), DC.segids(es), DC.Sk.ms(s), SH.shi.m(es, fs, OP.cspan(ctx), DC.segids(es), s, RR.h.sh(es, fs, ctx, t, s, H))), RR.seg_in(es, c, p, q, eg)))))
    case SK.GCirc{+x, +y}:
      absurd({RF.imem(c, DC.cids(DC.segids(es), es, OP.cspan(ctx))) == True{} : Bool}, nf(es, DC.Sk.k(s), c, fz.c(es, fs, ctx, t, s, H, c, x, y, eg), hf))
    case SK.GArc{+x, +y, +z}:
      absurd({RF.imem(c, DC.cids(DC.segids(es), es, OP.cspan(ctx))) == True{} : Bool}, nf(es, DC.Sk.k(s), c, fz.a(es, fs, ctx, t, s, H, c, x, y, z, eg), hf))

def cinfo.m(mg: Maybe<&2, SK.Geo>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, eg: {SK.find(c, es) == mg : Maybe<&2, SK.Geo>}, emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}, hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool}) -> {RF.imem(c, DC.cids(DC.segids(es), es, OP.cspan(ctx))) == True{} : Bool}:
  match mg:
    case Some{+g}:
      cinfo.g(g, es, fs, ctx, t, s, H, c, eg, emc, hf)
    case None{}:
      absurd({RF.imem(c, DC.cids(DC.segids(es), es, OP.cspan(ctx))) == True{} : Bool}, nf(es, DC.Sk.k(s), c, fz.n(es, fs, ctx, t, s, H, c, eg), hf))

# a node with no record, not in K squared, is a checked collapsed segment
def cinfo(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}, hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool}) -> {RF.imem(c, DC.cids(DC.segids(es), es, OP.cspan(ctx))) == True{} : Bool}:
  cinfo.m(SK.find(c, es), es, fs, ctx, t, s, H, c, {==}, emc, hf)

def fx.lks(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +cs: DC.SP, +ids: List<&2, Nat>, +s: DC.Sk, h: FX.Fx(es, fs, t, cs, ids, s))
  -> {DC.lks(DC.cids(ids, es, cs), es, fs, t, s, Con{DR.NFrame{}, DC.snodes(ids)}, DC.roots(DC.Sk.ms(s))) == None{} : Maybe<&2, DC.Link>}:
  (a, r1) = h
  (b, r2) = r1
  (c, r3) = r2
  (d, r4) = r3
  (e, f) = r4
  f

def lkc.of(+c: Nat, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), h: SK.Both({DC.lk.c(Con{DR.NFrame{}, DC.snodes(DC.segids(es))}, es, fs, t, s, c, DC.crep(es, fs, t, s, c)) == None{} : Maybe<&2, DC.Link>}, {DC.lk.r(DC.roots(DC.Sk.ms(s)), es, fs, t, s, c) == None{} : Maybe<&2, DC.Link>}))
  -> {DC.lk.c(Con{DR.NFrame{}, DC.snodes(DC.segids(es))}, es, fs, t, s, c, DC.crep(es, fs, t, s, c)) == None{} : Maybe<&2, DC.Link>}:
  (a, b) = h
  a

def lkr.of(+c: Nat, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), h: SK.Both({DC.lk.c(Con{DR.NFrame{}, DC.snodes(DC.segids(es))}, es, fs, t, s, c, DC.crep(es, fs, t, s, c)) == None{} : Maybe<&2, DC.Link>}, {DC.lk.r(DC.roots(DC.Sk.ms(s)), es, fs, t, s, c) == None{} : Maybe<&2, DC.Link>}))
  -> {DC.lk.r(DC.roots(DC.Sk.ms(s)), es, fs, t, s, c) == None{} : Maybe<&2, DC.Link>}:
  (a, b) = h
  b

# the link checks at a collapsed node not in K squared found nothing
def lkcr(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}, +hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool}) -> SK.Both({DC.lk.c(Con{DR.NFrame{}, DC.snodes(DC.segids(es))}, es, fs, t, s, c, DC.crep(es, fs, t, s, c)) == None{} : Maybe<&2, DC.Link>}, {DC.lk.r(DC.roots(DC.Sk.ms(s)), es, fs, t, s, c) == None{} : Maybe<&2, DC.Link>}):
  RF.lks_none(DC.cids(DC.segids(es), es, OP.cspan(ctx)), c, es, fs, t, s, Con{DR.NFrame{}, DC.snodes(DC.segids(es))}, DC.roots(DC.Sk.ms(s)), fx.lks(es, fs, t, OP.cspan(ctx), DC.segids(es), s, RR.h.fx(es, fs, ctx, t, s, H)), cinfo(es, fs, ctx, t, s, H, c, emc, hf), hf)

# a node with a record is not a node without one
def ne.q(q: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +b: DR.Node, +c: Nat, +m: DC.Mem, eq: {q == DC.node_eq(b, DR.NSeg{c}) : Bool}, emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{m} : Maybe<&2, DC.Mem>}, emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>})
  -> {DC.node_eq(b, DR.NSeg{c}) == False{} : Bool}:
  match q:
    case True{}:
      absurd({DC.node_eq(b, DR.NSeg{c}) == False{} : Bool}, SH.mnone_some(m, Equal.trans(Maybe<&2, DC.Mem>, None{}, DC.mem_of(DC.Sk.ms(s), b), Some{m},
        Equal.trans(Maybe<&2, DC.Mem>, None{}, DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}), DC.mem_of(DC.Sk.ms(s), b), Equal.sym(Maybe<&2, DC.Mem>, DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}), None{}, emc),
          Equal.cong(DR.Node, Maybe<&2, DC.Mem>, n => DC.mem_of(DC.Sk.ms(s), n), DR.NSeg{c}, b, Equal.sym(DR.Node, b, DR.NSeg{c}, GN.node_eq_ok(b, DR.NSeg{c}, Equal.sym(Bool, True{}, DC.node_eq(b, DR.NSeg{c}), eq))))), emb)))
    case False{}:
      Equal.sym(Bool, False{}, DC.node_eq(b, DR.NSeg{c}), eq)

def ne_rec(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +b: DR.Node, +c: Nat, +m: DC.Mem, emb: {DC.mem_of(DC.Sk.ms(s), b) == Some{m} : Maybe<&2, DC.Mem>}, emc: {DC.mem_of(DC.Sk.ms(s), DR.NSeg{c}) == None{} : Maybe<&2, DC.Mem>}) -> {DC.node_eq(b, DR.NSeg{c}) == False{} : Bool}:
  ne.q(DC.node_eq(b, DR.NSeg{c}), es, fs, ctx, t, s, H, b, c, m, {==}, emb, emc)

# Bases at a collapsed node
# -------------------------

def bc.t(m: Maybe<&2, DC.LD>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +z: SK.VE, +v: DR.Lab, +hz: HP.VBelow(z, t), hv: ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep.t(m, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), DR.gmul(v, z)))
  -> LS.LSp(LS.lat0(DC.rep.basis(DC.crep.t(m, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), es, fs, t, z)), LS.lat1(DC.rep.basis(DC.crep.t(m, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), es, fs, t, z)), v):
  match m:
    case None{}:
      LS.bfree_ok(LB.hs.lab(es, fs, t, DC.hfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, t, HS.hs0()), z), es, fs, ctx, DR.NSeg{c}, t, DC.Sk.k(s), DC.hfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, t, HS.hs0()), z, {==}, IV.hfold_inv(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, ctx, DR.NSeg{c}, t, HS.hs0(), IV.hs0_invd(es, fs, ctx, DR.NSeg{c}, t), IV.allpd_cat(es, fs, ctx, DR.NSeg{c}, t, DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c), RP.kgens_of(DC.Sk.k(s), es, fs, ctx, t, DR.NSeg{c}, RR.h.k(es, fs, ctx, t, s, H), BL.zdir_below(es, t, DR.NSeg{c}, RR.h.z(es, fs, ctx, t, s, H))), RP.cgens_ok(es, fs, ctx, t, s, c, RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H)))), BL.zdir_below(es, t, DR.NSeg{c}, RR.h.z(es, fs, ctx, t, s, H)), hz, v, hv)
    case Some{DC.LD{+u, du}}:
      LS.btied_ok(DC.ts.lab(es, fs, u, DC.tfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, u, DC.TS{Nil{}, Nil{}}), z), es, fs, ctx, DR.NSeg{c}, t, DC.Sk.k(s), u, DC.tfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, u, DC.TS{Nil{}, Nil{}}), z, {==}, RP.tfold_inv(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, ctx, DR.NSeg{c}, t, u, DC.TS{Nil{}, Nil{}}, ({==}, ({==}, Unit{})), IV.allpd_cat(es, fs, ctx, DR.NSeg{c}, t, DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c), RP.kgens_of(DC.Sk.k(s), es, fs, ctx, t, DR.NSeg{c}, RR.h.k(es, fs, ctx, t, s, H), BL.zdir_below(es, t, DR.NSeg{c}, RR.h.z(es, fs, ctx, t, s, H))), RP.cgens_ok(es, fs, ctx, t, s, c, RR.h.ms(es, fs, ctx, t, s, H), RR.h.ls(es, fs, ctx, t, s, H), RR.h.z(es, fs, ctx, t, s, H), RR.h.b(es, fs, ctx, t, s, H)))), v, hv)

def bc.f(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +z: SK.VE, +v: DR.Lab, eb: {b == False{} : Bool}, +hz: HP.VBelow(z, t), hv: ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep.f(b, es, fs, t, s, c), c), DR.gmul(v, z)))
  -> LS.LSp(LS.lat0(DC.rep.basis(DC.crep.f(b, es, fs, t, s, c), es, fs, t, z)), LS.lat1(DC.rep.basis(DC.crep.f(b, es, fs, t, s, c), es, fs, t, z)), v):
  match b:
    case True{}:
      absurd(LS.LSp(LS.lat0(DC.rep.basis(DC.RFull{}, es, fs, t, z)), LS.lat1(DC.rep.basis(DC.RFull{}, es, fs, t, z)), v), LP.tf(eb))
    case False{}:
      bc.t(DC.cties(DC.Sk.ls(s), c, DC.Sk.ms(s)), es, fs, ctx, t, s, H, c, z, v, hz, hv)

# the basis of a collapsed set not in K squared spans every v with v z in it
def bc_c(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +H: RR.Hyp(es, fs, ctx, t, s), +c: Nat, +z: SK.VE, +v: DR.Lab, hf: {DC.fullc(es, DC.Sk.k(s), c) == False{} : Bool}, +hz: HP.VBelow(z, t), hv: ST.InSt(es, fs, DC.Sk.k(s), ND.cset(DC.crep(es, fs, t, s, c), c), DR.gmul(v, z))) -> LS.LSp(LS.lat0(DC.rep.basis(DC.crep(es, fs, t, s, c), es, fs, t, z)), LS.lat1(DC.rep.basis(DC.crep(es, fs, t, s, c), es, fs, t, z)), v):
  bc.f(DC.fullc(es, DC.Sk.k(s), c), es, fs, ctx, t, s, H, c, z, v, hf, hz, hv)
