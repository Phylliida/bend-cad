# bend-cad: the closure's collapsed sets are right (PLAN-sk13b B3). A
# collapsed segment c's generators (lib/dclose.bend's cgens: its own
# direction, its statements, each link from c with what it gives through
# its open node, and the turns of the links into c) are valid parallel
# judgments at c with forms below t (cgens_ok), so its free hull keeps the
# invariant (crep_free). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./listpf.bend as LP2
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./cwpf.bend as CW
import ./lab.bend as LB
import ./labnzpf.bend as NZ
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./hspacepf.bend as HP
import ./pairpf.bend as PP
import ./labpf.bend as LP
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcinvpf.bend as IV
import ./dcbelowpf.bend as BL
import ./dcgenpf.bend as GN
import ./dcmergepf.bend as MG

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Finding a member
# ----------------

def OptMem(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +a: DR.Node, m: Maybe<&2, DC.Mem>) -> Data:
  match m:
    case Some{x}:
      SK.Both({DC.Mem.a(x) == a : DR.Node}, GN.MOkD(es, fs, ctx, t, x))
    case None{}:
      Unit

def mem_or_ok(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +a: DR.Node, +m: DC.Mem, +rest: Maybe<&2, DC.Mem>,
  ef: {f == DC.node_eq(DC.Mem.a(m), a) : Bool}, hm: GN.MOkD(es, fs, ctx, t, m), hr: OptMem(es, fs, ctx, t, a, rest)) -> OptMem(es, fs, ctx, t, a, DC.mem_or(f, m, rest)):
  match f:
    case True{}:
      (GN.node_eq_ok(DC.Mem.a(m), a, Equal.sym(Bool, True{}, DC.node_eq(DC.Mem.a(m), a), ef)), hm)
    case False{}:
      hr

# the member found for a is a's, and keeps the invariant
def mem_of_ok(ms: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +a: DR.Node, hms: GN.MsOk(es, fs, ctx, t, ms))
  -> OptMem(es, fs, ctx, t, a, DC.mem_of(ms, a)):
  match ms:
    case Nil{}:
      Unit{}
    case Con{+m, +tl}:
      (hm, rt) = hms
      mem_or_ok(DC.node_eq(DC.Mem.a(m), a), es, fs, ctx, t, a, m, DC.mem_of(tl, a), {==}, hm, mem_of_ok(tl, es, fs, ctx, t, a, rt))

# What a link from c gives c
# --------------------------

def zref(+es: List<&2, SK.Ent>, +g: DR.Lab, +a1: DR.Node, +rb: DR.Node, e: {a1 == rb : DR.Node}) -> VD.SameVD(DR.gmul(g, DR.zdir(es, a1)), DR.gmul(g, DR.zdir(es, rb))):
  %Equal.sym(DR.Node, a1, rb, e) : VD.SameVD(DR.gmul(g, DR.zdir(es, _)), DR.gmul(g, DR.zdir(es, rb)))
  MG.samevd_refl(DR.gmul(g, DR.zdir(es, rb)))

def svb_move(+es: List<&2, SK.Ent>, +x: SK.VE, +w: DR.Lab, +a: DR.Node, +b: DR.Node, e: {a == b : DR.Node}, sv: VD.SameVD(x, DR.gmul(w, DR.zdir(es, a)))) -> VD.SameVD(x, DR.gmul(w, DR.zdir(es, b))):
  %e : VD.SameVD(x, DR.gmul(w, DR.zdir(es, _)))
  sv

def ob_move(+es: List<&2, SK.Ent>, +ctx: List<&2, E.QExpr>, +a: DR.Node, +b: DR.Node, e: {a == b : DR.Node}, h: VD.OpenD(es, ctx, a)) -> VD.OpenD(es, ctx, b):
  %e : VD.OpenD(es, ctx, _)
  h

# the tie: through b into F's component, par(c, wl conj(wb) (1, 0))
def tie_gen(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, +a: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  +hz: {DC.zb(es, t) == True{} : Bool}, +ea2: {a == b : DR.Node}, hm: GN.MOkD(es, fs, ctx, t, DC.Mem{a, rb, wb, db}), hl: GN.LOkD(es, fs, ctx, t, DC.Link{c, b, wl, dl}))
  -> IV.PGenD(es, fs, ctx, DR.NSeg{c}, t, DR.DThrough{dl, DR.DTurn{db, DR.Lab.conj(wb), b}, DR.Lab.conj(wl), b}):
  (vb, r1) = hm
  (pb, r2) = r1
  (eb, r3) = r2
  (svb, r4) = r3
  (oa, r5) = r4
  (orb, bb) = r5
  (vl, s1) = hl
  (pl, s2) = s1
  (el, s3) = s2
  (svl, bl) = s3
  ((vl, ((vb, (pb, MG.ccw(es, fs, db, wb, b, svb_move(es, DR.Jd.x(DR.concl(es, fs, db)), wb, a, b, ea2, svb)))), (pl, ({==}, (MG.ccw(es, fs, dl, wl, b, svl), ({==}, ob_move(es, ctx, a, b, ea2, oa))))))),
   ({==}, (el, BL.vb_gmul(DR.Lab.conj(DR.Lab.conj(wl)), DR.gmul(DR.Lab.conj(wb), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, db)))), t,
     BL.vb_gmul(DR.Lab.conj(wb), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, db))), t, BL.zdir_below(es, t, DR.Jd.a(DR.concl(es, fs, db)), hz))))))

# through b to the root's generator h: par(c, wl conj(wb) y)
def thru_gen(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, +a: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  +ea2: {a == b : DR.Node}, +hm: GN.MOkD(es, fs, ctx, t, DC.Mem{a, rb, wb, db}), +hl: GN.LOkD(es, fs, ctx, t, DC.Link{c, b, wl, dl}), +h: DR.Der, hh: IV.PGenD(es, fs, ctx, rb, t, h))
  -> IV.PGenD(es, fs, ctx, DR.NSeg{c}, t, DR.DThrough{dl, DR.DThrough{DR.DTurn{db, DR.Lab.conj(wb), b}, h, wb, rb}, DR.Lab.conj(wl), b}):
  (vb, r1) = hm
  (pb, r2) = r1
  (eb, r3) = r2
  (svb, r4) = r3
  (oa, r5) = r4
  (orb, bb) = r5
  (vl, s1) = hl
  (pl, s2) = s1
  (el, s3) = s2
  (svl, bl) = s3
  (vh, q1) = hh
  (ph, q2) = q1
  (ehh, bh) = q2
  ((vl, (((vb, (pb, MG.ccw(es, fs, db, wb, b, svb_move(es, DR.Jd.x(DR.concl(es, fs, db)), wb, a, b, ea2, svb)))), (vh, ({==}, (ph, (zref(es, DR.Lab.conj(wb), DR.Jd.a(DR.concl(es, fs, db)), rb, eb), (ehh, orb)))))),
     (pl, ({==}, (MG.ccw(es, fs, dl, wl, b, svl), ({==}, ob_move(es, ctx, a, b, ea2, oa))))))),
   ({==}, (el, BL.vb_gmul(DR.Lab.conj(DR.Lab.conj(wl)), DR.gmul(DR.Lab.conj(wb), DR.Jd.x(DR.concl(es, fs, h))), t, BL.vb_gmul(DR.Lab.conj(wb), DR.Jd.x(DR.concl(es, fs, h)), t, bh)))))

def lout.gens_ok(hs: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, +a: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  +ea2: {a == b : DR.Node}, +hm: GN.MOkD(es, fs, ctx, t, DC.Mem{a, rb, wb, db}), +hl: GN.LOkD(es, fs, ctx, t, DC.Link{c, b, wl, dl}), hhs: IV.AllPD(es, fs, ctx, rb, t, hs))
  -> IV.AllPD(es, fs, ctx, DR.NSeg{c}, t, DC.lout.gens(hs, b, wl, dl, rb, wb, db)):
  match hs:
    case Nil{}:
      Unit{}
    case Con{+h, tl}:
      (g, rt) = hhs
      (thru_gen(es, fs, ctx, t, c, b, wl, dl, a, rb, wb, db, ea2, hm, hl, h, g), lout.gens_ok(tl, es, fs, ctx, t, c, b, wl, dl, a, rb, wb, db, ea2, hm, hl, rt))

def lout.root_ok(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ms: List<&2, DC.Mem>, +ls: List<&2, DC.Link>, +c: Nat, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der,
  +a: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, +ea2: {a == b : DR.Node}, +hm: GN.MOkD(es, fs, ctx, t, DC.Mem{a, rb, wb, db}), +hl: GN.LOkD(es, fs, ctx, t, DC.Link{c, b, wl, dl}),
  +hms: GN.MsOk(es, fs, ctx, t, ms), +hls: GN.LsOk(es, fs, ctx, t, ls), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> IV.AllPD(es, fs, ctx, DR.NSeg{c}, t, DC.lout.root(f, fs, ms, ls, b, wl, dl, rb, wb, db)):
  match f:
    case True{}:
      (tie_gen(es, fs, ctx, t, c, b, wl, dl, a, rb, wb, db, hz, ea2, hm, hl), Unit{})
    case False{}:
      lout.gens_ok(DC.rgens(fs, rb, ms, ls), es, fs, ctx, t, c, b, wl, dl, a, rb, wb, db, ea2, hm, hl, GN.rgens_ok(ms, es, fs, ctx, t, rb, ls, hz, hb, hms, hls))

def lout.mem_ok(m: Maybe<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ms: List<&2, DC.Mem>, +ls: List<&2, DC.Link>, +c: Nat, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der,
  hmo: OptMem(es, fs, ctx, t, b, m), +hl: GN.LOkD(es, fs, ctx, t, DC.Link{c, b, wl, dl}),
  +hms: GN.MsOk(es, fs, ctx, t, ms), +hls: GN.LsOk(es, fs, ctx, t, ls), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> IV.AllPD(es, fs, ctx, DR.NSeg{c}, t, DC.lout.mem(m, fs, ms, ls, b, wl, dl)):
  match m:
    case None{}:
      Unit{}
    case Some{DC.Mem{+a, +rb, +wb, +db}}:
      (ea, hm) = hmo
      lout.root_ok(DC.node_eq(rb, DR.NFrame{}), es, fs, ctx, t, ms, ls, c, b, wl, dl, a, rb, wb, db, ea, hm, hl, hms, hls, hz, hb)

def lok_move(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c2: Nat, +c: Nat, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, e: {c2 == c : Nat}, h: GN.LOkD(es, fs, ctx, t, DC.Link{c2, b, wl, dl}))
  -> GN.LOkD(es, fs, ctx, t, DC.Link{c, b, wl, dl}):
  %e : GN.LOkD(es, fs, ctx, t, DC.Link{_, b, wl, dl})
  h

def lgen_self(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, hl: GN.LOkD(es, fs, ctx, t, DC.Link{c, b, wl, dl}))
  -> IV.PGenD(es, fs, ctx, DR.NSeg{c}, t, dl):
  (vl, s1) = hl
  (pl, s2) = s1
  (el, s3) = s2
  (svl, bl) = s3
  (vl, (pl, (el, bl)))

def louts.yes(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ms: List<&2, DC.Mem>, +all: List<&2, DC.Link>, +c: Nat, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der,
  +hl: GN.LOkD(es, fs, ctx, t, DC.Link{c, b, wl, dl}), +hms: GN.MsOk(es, fs, ctx, t, ms), +hall: GN.LsOk(es, fs, ctx, t, all), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool},
  +rest: List<&2, DR.Der>, ih: IV.AllPD(es, fs, ctx, DR.NSeg{c}, t, rest))
  -> IV.AllPD(es, fs, ctx, DR.NSeg{c}, t, DC.dcatif(True{}, Con{dl, DC.lout.mem(DC.mem_of(ms, b), fs, ms, all, b, wl, dl)}, rest)):
  IV.allpd_cat(es, fs, ctx, DR.NSeg{c}, t, Con{dl, DC.lout.mem(DC.mem_of(ms, b), fs, ms, all, b, wl, dl)}, rest,
    (lgen_self(es, fs, ctx, t, c, b, wl, dl, hl), lout.mem_ok(DC.mem_of(ms, b), es, fs, ctx, t, ms, all, c, b, wl, dl, mem_of_ok(ms, es, fs, ctx, t, b, hms), hl, hms, hall, hz, hb)), ih)

def louts.pick(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ms: List<&2, DC.Mem>, +all: List<&2, DC.Link>, +c: Nat, +c2: Nat, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der,
  ef: {f == SV.eq(c2, c) : Bool}, hl: GN.LOkD(es, fs, ctx, t, DC.Link{c2, b, wl, dl}),
  +hms: GN.MsOk(es, fs, ctx, t, ms), +hall: GN.LsOk(es, fs, ctx, t, all), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool},
  +rest: List<&2, DR.Der>, ih: IV.AllPD(es, fs, ctx, DR.NSeg{c}, t, rest))
  -> IV.AllPD(es, fs, ctx, DR.NSeg{c}, t, DC.dcatif(f, Con{dl, DC.lout.mem(DC.mem_of(ms, b), fs, ms, all, b, wl, dl)}, rest)):
  match f:
    case True{}:
      louts.yes(es, fs, ctx, t, ms, all, c, b, wl, dl, lok_move(es, fs, ctx, t, c2, c, b, wl, dl, LP2.eq_ok(c2, c, Equal.sym(Bool, True{}, SV.eq(c2, c), ef)), hl), hms, hall, hz, hb, rest, ih)
    case False{}:
      ih

def louts_ok(ls: List<&2, DC.Link>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, +ms: List<&2, DC.Mem>, +all: List<&2, DC.Link>,
  hls: GN.LsOk(es, fs, ctx, t, ls), +hms: GN.MsOk(es, fs, ctx, t, ms), +hall: GN.LsOk(es, fs, ctx, t, all), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> IV.AllPD(es, fs, ctx, DR.NSeg{c}, t, DC.louts(ls, c, fs, ms, all)):
  match ls:
    case Nil{}:
      Unit{}
    case Con{DC.Link{+c2, +b, +wl, +dl}, +tl}:
      (hl, rt) = hls
      louts.pick(SV.eq(c2, c), es, fs, ctx, t, ms, all, c, c2, b, wl, dl, {==}, hl, hms, hall, hz, hb, DC.louts(tl, c, fs, ms, all), louts_ok(tl, es, fs, ctx, t, c, ms, all, rt, hms, hall, hz, hb))

def lins.pick(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, +c2: Nat, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der,
  ef: {f == DC.node_eq(b, DR.NSeg{c}) : Bool}, hl: GN.LOkD(es, fs, ctx, t, DC.Link{c2, b, wl, dl}), +hz: {DC.zb(es, t) == True{} : Bool},
  +rest: List<&2, DR.Der>, ih: IV.AllPD(es, fs, ctx, DR.NSeg{c}, t, rest)) -> IV.AllPD(es, fs, ctx, DR.NSeg{c}, t, DC.dpick(f, DR.DTurn{dl, DR.Lab.conj(wl), DR.NSeg{c}}, rest)):
  match f:
    case True{}:
      (GN.turn_gen(es, fs, ctx, t, DR.NSeg{c}, c2, b, wl, dl, hz, GN.node_eq_ok(b, DR.NSeg{c}, Equal.sym(Bool, True{}, DC.node_eq(b, DR.NSeg{c}), ef)), hl), ih)
    case False{}:
      ih

def lins_ok(ls: List<&2, DC.Link>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, hls: GN.LsOk(es, fs, ctx, t, ls), +hz: {DC.zb(es, t) == True{} : Bool})
  -> IV.AllPD(es, fs, ctx, DR.NSeg{c}, t, DC.lins(ls, c)):
  match ls:
    case Nil{}:
      Unit{}
    case Con{DC.Link{+c2, +b, +wl, +dl}, +tl}:
      (hl, rt) = hls
      lins.pick(DC.node_eq(b, DR.NSeg{c}), es, fs, ctx, t, c, c2, b, wl, dl, {==}, hl, hz, DC.lins(tl, c), lins_ok(tl, es, fs, ctx, t, c, rt, hz))

# c's generators are right at c
def cgens_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +c: Nat,
  +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> IV.AllPD(es, fs, ctx, DR.NSeg{c}, t, DC.cgens(fs, s, c)):
  ((Unit{}, ({==}, ({==}, BL.zdir_below(es, t, DR.NSeg{c}, hz)))),
   IV.allpd_cat(es, fs, ctx, DR.NSeg{c}, t, DC.pprems(DC.stats(fs, c, 0n)), DC.dcat(DC.louts(DC.Sk.ls(s), c, fs, DC.Sk.ms(s), DC.Sk.ls(s)), DC.lins(DC.Sk.ls(s), c)),
     GN.nstats_ok(DR.NSeg{c}, es, fs, ctx, t, hb),
     IV.allpd_cat(es, fs, ctx, DR.NSeg{c}, t, DC.louts(DC.Sk.ls(s), c, fs, DC.Sk.ms(s), DC.Sk.ls(s)), DC.lins(DC.Sk.ls(s), c),
       louts_ok(DC.Sk.ls(s), es, fs, ctx, t, c, DC.Sk.ms(s), DC.Sk.ls(s), hls, hms, hls, hz, hb), lins_ok(DC.Sk.ls(s), es, fs, ctx, t, c, hls, hz))))

# Nonzero labels, as lists
# ------------------------

def MsNz(ms: List<&2, DC.Mem>) -> Data:
  match ms:
    case Nil{}:
      Unit
    case Con{DC.Mem{a, r, +w, d}, tl}:
      SK.Both(NZ.Nz(w), MsNz(tl))

def LsNz(ls: List<&2, DC.Link>) -> Data:
  match ls:
    case Nil{}:
      Unit
    case Con{DC.Link{c, b, +w, d}, tl}:
      SK.Both(NZ.Nz(w), LsNz(tl))

def OptNz(m: Maybe<&2, DC.Mem>) -> Data:
  match m:
    case Some{DC.Mem{a, r, +w, d}}:
      NZ.Nz(w)
    case None{}:
      Unit

def mem_or_nz(f: Bool, m: DC.Mem, +rest: Maybe<&2, DC.Mem>, hm: OptNz(Some{m}), hr: OptNz(rest)) -> OptNz(DC.mem_or(f, m, rest)):
  match f:
    case True{}:
      hm
    case False{}:
      hr

def mem_of_nz(ms: List<&2, DC.Mem>, +a: DR.Node, hn: MsNz(ms)) -> OptNz(DC.mem_of(ms, a)):
  match ms:
    case Nil{}:
      Unit{}
    case Con{DC.Mem{+b, +r, +w, +d}, +tl}:
      (hw, rt) = hn
      mem_or_nz(DC.node_eq(DC.Mem.a(DC.Mem{b, r, w, d}), a), DC.Mem{b, r, w, d}, DC.mem_of(tl, a), hw, mem_of_nz(tl, a, rt))

# The tied span
# -------------

def TInvD(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +u: DR.Lab, s: DC.TS) -> Data:
  match s:
    case DC.TS{+rows, +ds}:
      SK.Both({EP.rinv(DC.crosses(es, fs, u, ds), rows, 0n) == True{} : Bool}, SK.Both({EL.rlen(rows) == SV.neqs(DC.crosses(es, fs, u, ds)) : Nat}, IV.AllPD(es, fs, ctx, r, t, ds)))

def crosses_snoc(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, ds: List<&2, DR.Der>, +d: DR.Der)
  -> {DC.crosses(es, fs, u, KS.dsnoc(ds, d)) == EP.qsnoc(DC.crosses(es, fs, u, ds), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))) : List<&2, E.QExpr>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+h0, +tl}:
      %Equal.sym(List<&2, E.QExpr>, DC.crosses(es, fs, u, KS.dsnoc(tl, d)), EP.qsnoc(DC.crosses(es, fs, u, tl), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))), crosses_snoc(es, fs, u, tl, d))
        : {Con{SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, h0))), _} == Con{SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, h0))), EP.qsnoc(DC.crosses(es, fs, u, tl), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d))))} : List<&2, E.QExpr>}
      {==}

def ts_add.rinv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der,
  hr: {EP.rinv(DC.crosses(es, fs, u, ds), rows, 0n) == True{} : Bool}, hl: {EL.rlen(rows) == SV.neqs(DC.crosses(es, fs, u, ds)) : Nat},
  hne: {EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))) == False{} : Bool})
  -> {EP.rinv(DC.crosses(es, fs, u, KS.dsnoc(ds, d)), EL.rsnoc(rows, EL.row_of(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))), 0n) == True{} : Bool}:
  %Equal.sym(List<&2, E.QExpr>, DC.crosses(es, fs, u, KS.dsnoc(ds, d)), EP.qsnoc(DC.crosses(es, fs, u, ds), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))), crosses_snoc(es, fs, u, ds, d))
    : {EP.rinv(_, EL.rsnoc(rows, EL.row_of(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))), 0n) == True{} : Bool}
  EP.new_rinv(DC.crosses(es, fs, u, ds), rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d))), hr, hl, hne)

def ts_add.len(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der, +x: EL.Row,
  hl: {EL.rlen(rows) == SV.neqs(DC.crosses(es, fs, u, ds)) : Nat})
  -> {EL.rlen(EL.rsnoc(rows, x)) == SV.neqs(DC.crosses(es, fs, u, KS.dsnoc(ds, d))) : Nat}:
  %Equal.sym(List<&2, E.QExpr>, DC.crosses(es, fs, u, KS.dsnoc(ds, d)), EP.qsnoc(DC.crosses(es, fs, u, ds), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))), crosses_snoc(es, fs, u, ds, d)) : {EL.rlen(EL.rsnoc(rows, x)) == SV.neqs(_) : Nat}
  PP.len_snoc(DC.crosses(es, fs, u, ds), rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d))), x, hl)

def ts_add.pick(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +u: DR.Lab, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +d: DR.Der, b: Bool,
  eb: {b == EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))) : Bool},
  +hr: {EP.rinv(DC.crosses(es, fs, u, ds), rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(DC.crosses(es, fs, u, ds)) : Nat}, ha: IV.AllPD(es, fs, ctx, r, t, ds), +hd: IV.PGenD(es, fs, ctx, r, t, d))
  -> TInvD(es, fs, ctx, r, t, u, DC.ts.pick(b, rows, ds, EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))), d)):
  match b:
    case True{}:
      (hr, (hl, ha))
    case False{}:
      (ts_add.rinv(es, fs, u, rows, ds, d, hr, hl, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))), eb)),
       (ts_add.len(es, fs, u, rows, ds, d, EL.row_of(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d))))), hl), IV.allpd_snoc(es, fs, ctx, r, t, ds, d, ha, hd)))

def ts_add_inv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +u: DR.Lab, s: DC.TS, +d: DR.Der, hi: TInvD(es, fs, ctx, r, t, u, s), +hd: IV.PGenD(es, fs, ctx, r, t, d))
  -> TInvD(es, fs, ctx, r, t, u, DC.ts.add(es, fs, u, s, d)):
  match s:
    case DC.TS{+rows, +ds}:
      (hr, r1) = hi
      (hl, ha) = r1
      ts_add.pick(es, fs, ctx, r, t, u, rows, ds, d, EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d)))))), {==}, hr, hl, ha, hd)

# folding generators into the tied span keeps its invariant
def tfold_inv(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +u: DR.Lab, +s: DC.TS,
  hi: TInvD(es, fs, ctx, r, t, u, s), hd: IV.AllPD(es, fs, ctx, r, t, ds)) -> TInvD(es, fs, ctx, r, t, u, DC.tfold(ds, es, fs, u, s)):
  match ds:
    case Nil{}:
      hi
    case Con{+d, tl}:
      (g, rt) = hd
      tfold_inv(tl, es, fs, ctx, r, t, u, DC.ts.add(es, fs, u, s, d), ts_add_inv(es, fs, ctx, r, t, u, s, d, hi, g), rt)

# The tie
# -------

def TieOk(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, +u: DR.Lab, +du: DR.Der) -> Data:
  SK.Both(IV.PGenD(es, fs, ctx, DR.NSeg{c}, t, du), SK.Both(VD.SameVD(DR.Jd.x(DR.concl(es, fs, du)), DC.lform(u)), NZ.Nz(u)))

def OptTie(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, m: Maybe<&2, DC.LD>) -> Data:
  match m:
    case Some{DC.LD{+u, +du}}:
      TieOk(es, fs, ctx, t, c, u, du)
    case None{}:
      Unit

def tie_same(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +wl: DR.Lab, +wb: DR.Lab, +db: DR.Der, +rb: DR.Node, eb: {DR.Jd.a(DR.concl(es, fs, db)) == rb : DR.Node}, ef: {rb == DR.NFrame{} : DR.Node})
  -> VD.SameVD(DR.gmul(DR.Lab.conj(DR.Lab.conj(wl)), DR.gmul(DR.Lab.conj(wb), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, db))))), DC.lform(LB.lmul(wl, DR.Lab.conj(wb)))):
  MG.zmove(es, DR.Lab.conj(DR.Lab.conj(wl)), DR.Lab.conj(wb), DR.Jd.a(DR.concl(es, fs, db)), DR.NFrame{}, DC.lform(LB.lmul(wl, DR.Lab.conj(wb))),
    Equal.trans(DR.Node, DR.Jd.a(DR.concl(es, fs, db)), rb, DR.NFrame{}, eb, ef), MG.ccomp(wl, DR.Lab.conj(wb), DR.zdir(es, DR.NFrame{})))

def tie_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, +a: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  +hz: {DC.zb(es, t) == True{} : Bool}, +ea: {a == b : DR.Node}, +hm: GN.MOkD(es, fs, ctx, t, DC.Mem{a, rb, wb, db}), +hl: GN.LOkD(es, fs, ctx, t, DC.Link{c, b, wl, dl}),
  ef: {rb == DR.NFrame{} : DR.Node}, hwl: NZ.Nz(wl), hwb: NZ.Nz(wb))
  -> TieOk(es, fs, ctx, t, c, LB.lmul(wl, DR.Lab.conj(wb)), DR.DThrough{dl, DR.DTurn{db, DR.Lab.conj(wb), b}, DR.Lab.conj(wl), b}):
  (vb, r1) = hm
  (pb, r2) = r1
  (eb, r3) = r2
  (tie_gen(es, fs, ctx, t, c, b, wl, dl, a, rb, wb, db, hz, ea, hm, hl), (tie_same(es, fs, wl, wb, db, rb, eb, ef), NZ.nz_mul(wl, DR.Lab.conj(wb), hwl, NZ.nz_conj(wb, hwb))))

def ctie.pick_ok(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, +a: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  ef: {f == DC.node_eq(rb, DR.NFrame{}) : Bool}, +hz: {DC.zb(es, t) == True{} : Bool}, +ea: {a == b : DR.Node}, +hm: GN.MOkD(es, fs, ctx, t, DC.Mem{a, rb, wb, db}), +hl: GN.LOkD(es, fs, ctx, t, DC.Link{c, b, wl, dl}),
  hwl: NZ.Nz(wl), hwb: NZ.Nz(wb), +rest: Maybe<&2, DC.LD>, hr: OptTie(es, fs, ctx, t, c, rest))
  -> OptTie(es, fs, ctx, t, c, DC.ctie.pick(f, DC.LD{LB.lmul(wl, DR.Lab.conj(wb)), DR.DThrough{dl, DR.DTurn{db, DR.Lab.conj(wb), b}, DR.Lab.conj(wl), b}}, rest)):
  match f:
    case True{}:
      tie_ok(es, fs, ctx, t, c, b, wl, dl, a, rb, wb, db, hz, ea, hm, hl, GN.node_eq_ok(rb, DR.NFrame{}, Equal.sym(Bool, True{}, DC.node_eq(rb, DR.NFrame{}), ef)), hwl, hwb)
    case False{}:
      hr

def ctie.mem_ok(m: Maybe<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der,
  hmo: OptMem(es, fs, ctx, t, b, m), hn: OptNz(m), +hz: {DC.zb(es, t) == True{} : Bool}, +hl: GN.LOkD(es, fs, ctx, t, DC.Link{c, b, wl, dl}), hwl: NZ.Nz(wl),
  +rest: Maybe<&2, DC.LD>, hr: OptTie(es, fs, ctx, t, c, rest)) -> OptTie(es, fs, ctx, t, c, DC.ctie.mem(m, b, wl, dl, rest)):
  match m:
    case None{}:
      hr
    case Some{DC.Mem{+a, +rb, +wb, +db}}:
      (ea, hm) = hmo
      ctie.pick_ok(DC.node_eq(rb, DR.NFrame{}), es, fs, ctx, t, c, b, wl, dl, a, rb, wb, db, {==}, hz, ea, hm, hl, hwl, hn, rest, hr)

def ctie.if_ok(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ms: List<&2, DC.Mem>, +c: Nat, +c2: Nat, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der,
  ef: {f == SV.eq(c2, c) : Bool}, hl: GN.LOkD(es, fs, ctx, t, DC.Link{c2, b, wl, dl}), hwl: NZ.Nz(wl), +hms: GN.MsOk(es, fs, ctx, t, ms), +hmsn: MsNz(ms), +hz: {DC.zb(es, t) == True{} : Bool},
  +rest: Maybe<&2, DC.LD>, hr: OptTie(es, fs, ctx, t, c, rest)) -> OptTie(es, fs, ctx, t, c, DC.ctie.if(f, DC.mem_of(ms, b), b, wl, dl, rest)):
  match f:
    case True{}:
      ctie.mem_ok(DC.mem_of(ms, b), es, fs, ctx, t, c, b, wl, dl, mem_of_ok(ms, es, fs, ctx, t, b, hms), mem_of_nz(ms, b, hmsn), hz,
        lok_move(es, fs, ctx, t, c2, c, b, wl, dl, LP2.eq_ok(c2, c, Equal.sym(Bool, True{}, SV.eq(c2, c), ef)), hl), hwl, rest, hr)
    case False{}:
      hr

# c's first tie is valid, the same as u (1, 0), and u is nonzero
def cties_ok(ls: List<&2, DC.Link>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, +ms: List<&2, DC.Mem>,
  hls: GN.LsOk(es, fs, ctx, t, ls), hlsn: LsNz(ls), +hms: GN.MsOk(es, fs, ctx, t, ms), +hmsn: MsNz(ms), +hz: {DC.zb(es, t) == True{} : Bool}) -> OptTie(es, fs, ctx, t, c, DC.cties(ls, c, ms)):
  match ls:
    case Nil{}:
      Unit{}
    case Con{DC.Link{+c2, +b, +wl, +dl}, +tl}:
      (hl, rt) = hls
      (hwl, rn) = hlsn
      ctie.if_ok(SV.eq(c2, c), es, fs, ctx, t, ms, c, c2, b, wl, dl, {==}, hl, hwl, hms, hmsn, hz, DC.cties(tl, c, ms), cties_ok(tl, es, fs, ctx, t, c, ms, rt, rn, hms, hmsn, hz))

# The collapsed set
# -----------------

def RepOk(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +k: KS.KS, +c: Nat, r: DC.Rep) -> Data:
  match r:
    case DC.RFull{}:
      {DC.fullc(es, k, c) == True{} : Bool}
    case DC.RFree{+h}:
      IV.HInvD(es, fs, ctx, DR.NSeg{c}, t, h)
    case DC.RTied{+u, +du, +ts}:
      SK.Both(TInvD(es, fs, ctx, DR.NSeg{c}, t, u, ts), TieOk(es, fs, ctx, t, c, u, du))

def crep.t_ok(m: Maybe<&2, DC.LD>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +k: KS.KS, +c: Nat, +gens: List<&2, DR.Der>,
  hm: OptTie(es, fs, ctx, t, c, m), hg: IV.AllPD(es, fs, ctx, DR.NSeg{c}, t, gens)) -> RepOk(es, fs, ctx, t, k, c, DC.crep.t(m, es, fs, t, gens)):
  match m:
    case None{}:
      IV.hfold_inv(gens, es, fs, ctx, DR.NSeg{c}, t, HS.hs0(), IV.hs0_invd(es, fs, ctx, DR.NSeg{c}, t), hg)
    case Some{DC.LD{+u, +du}}:
      (tfold_inv(gens, es, fs, ctx, DR.NSeg{c}, t, u, DC.TS{Nil{}, Nil{}}, ({==}, ({==}, Unit{})), hg), hm)

def kgens_of(k: KS.KS, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +r: DR.Node, hk: IV.KInvD(es, fs, ctx, t, k), +hzr: HP.VBelow(DR.zdir(es, r), t))
  -> IV.AllPD(es, fs, ctx, r, t, DC.kgens(r, KS.ks.ds(k))):
  match k:
    case KS.KS{+rows, +ds}:
      (hr, r1) = hk
      (hl, ha) = r1
      GN.kgens_ok(ds, es, fs, ctx, t, r, hzr, ha)

def crep.f_ok(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +c: Nat, eb: {b == DC.fullc(es, DC.Sk.k(s), c) : Bool},
  +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: MsNz(DC.Sk.ms(s)), +hlsn: LsNz(DC.Sk.ls(s)),
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}) -> RepOk(es, fs, ctx, t, DC.Sk.k(s), c, DC.crep.f(b, es, fs, t, s, c)):
  match b:
    case True{}:
      Equal.sym(Bool, True{}, DC.fullc(es, DC.Sk.k(s), c), eb)
    case False{}:
      crep.t_ok(DC.cties(DC.Sk.ls(s), c, DC.Sk.ms(s)), es, fs, ctx, t, DC.Sk.k(s), c, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)),
        cties_ok(DC.Sk.ls(s), es, fs, ctx, t, c, DC.Sk.ms(s), hls, hlsn, hms, hmsn, hz),
        IV.allpd_cat(es, fs, ctx, DR.NSeg{c}, t, DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c),
          kgens_of(DC.Sk.k(s), es, fs, ctx, t, DR.NSeg{c}, hk, BL.zdir_below(es, t, DR.NSeg{c}, hz)), cgens_ok(es, fs, ctx, t, s, c, hms, hls, hz, hb)))

# a collapsed segment's set keeps its invariant
def crep_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +c: Nat,
  +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: MsNz(DC.Sk.ms(s)), +hlsn: LsNz(DC.Sk.ls(s)),
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}) -> RepOk(es, fs, ctx, t, DC.Sk.k(s), c, DC.crep(es, fs, t, s, c)):
  crep.f_ok(DC.fullc(es, DC.Sk.k(s), c), es, fs, ctx, t, s, c, {==}, hk, hms, hls, hmsn, hlsn, hz, hb)
