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
