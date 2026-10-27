# bend-cad: the closure's merges keep the members' invariant (PLAN-sk13b
# B3). A merge's derivation dR, proving par(new, x) with x the same as
# W z_old, is itself a member record of old under new (MOkD of
# Mem{old, new, W, dR}); moving old's members under new keeps MOkD
# (reroot_ok), by g (h x) = (g h) x. Both kinds of merge build such a dR
# (merge_ok), and the merges the label and frame tests find are right
# (mgs_ok). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./q.bend as LQ
import ./qalg.bend as QA
import ./identpf.bend as ID
import ./listpf.bend as LP2
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./hspacepf.bend as HP
import ./lab.bend as LB
import ./labpf.bend as LP
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcinvpf.bend as IV
import ./dcbelowpf.bend as BL
import ./dcgenpf.bend as GN
import ./dcderpf.bend as DD

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Identities
# ----------

def samed_sym.at(+p: List<&2, S.Q>, +a: E.QExpr, +b: E.QExpr, +h: VD.SameD(a, b)) -> S.Q.eq(E.qeval(p, b), E.qeval(p, a)):
  LQ.q_sym(E.qeval(p, a), E.qeval(p, b), ID.ident_ok(a, b, h)(p))

def samevd_sym(+u: SK.VE, +v: SK.VE, h: VD.SameVD(u, v)) -> VD.SameVD(v, u):
  (+a, +b) = h
  (ID.qzero_ident(SK.VE.x(v), SK.VE.x(u), p => samed_sym.at(p, SK.VE.x(u), SK.VE.x(v), a)), ID.qzero_ident(SK.VE.y(v), SK.VE.y(u), p => samed_sym.at(p, SK.VE.y(u), SK.VE.y(v), b)))

def samevd_refl(+u: SK.VE) -> VD.SameVD(u, u):
  (ID.qzero_ident(SK.VE.x(u), SK.VE.x(u), p => LQ.q_refl(E.qeval(p, SK.VE.x(u)))), ID.qzero_ident(SK.VE.y(u), SK.VE.y(u), p => LQ.q_refl(E.qeval(p, SK.VE.y(u)))))

def gcong.ax(+p: List<&2, S.Q>, +c: S.Q, +s: S.Q, +x: SK.VE, +y: SK.VE, +hx: VD.SameD(SK.VE.x(x), SK.VE.x(y)), +hy: VD.SameD(SK.VE.y(x), SK.VE.y(y)))
  -> S.Q.eq(E.qeval(p, SK.VE.x(DR.gmul(DR.Lab{c, s}, x))), E.qeval(p, SK.VE.x(DR.gmul(DR.Lab{c, s}, y)))):
  QA.sub_cong(S.Q.mul(c, E.qeval(p, SK.VE.x(x))), S.Q.mul(c, E.qeval(p, SK.VE.x(y))), S.Q.mul(s, E.qeval(p, SK.VE.y(x))), S.Q.mul(s, E.qeval(p, SK.VE.y(y))),
    LQ.q_mul_cong_r(c, E.qeval(p, SK.VE.x(x)), E.qeval(p, SK.VE.x(y)), ID.ident_ok(SK.VE.x(x), SK.VE.x(y), hx)(p)),
    LQ.q_mul_cong_r(s, E.qeval(p, SK.VE.y(x)), E.qeval(p, SK.VE.y(y)), ID.ident_ok(SK.VE.y(x), SK.VE.y(y), hy)(p)))

def gcong.ay(+p: List<&2, S.Q>, +c: S.Q, +s: S.Q, +x: SK.VE, +y: SK.VE, +hx: VD.SameD(SK.VE.x(x), SK.VE.x(y)), +hy: VD.SameD(SK.VE.y(x), SK.VE.y(y)))
  -> S.Q.eq(E.qeval(p, SK.VE.y(DR.gmul(DR.Lab{c, s}, x))), E.qeval(p, SK.VE.y(DR.gmul(DR.Lab{c, s}, y)))):
  QA.add_cong(S.Q.mul(s, E.qeval(p, SK.VE.x(x))), S.Q.mul(s, E.qeval(p, SK.VE.x(y))), S.Q.mul(c, E.qeval(p, SK.VE.y(x))), S.Q.mul(c, E.qeval(p, SK.VE.y(y))),
    LQ.q_mul_cong_r(s, E.qeval(p, SK.VE.x(x)), E.qeval(p, SK.VE.x(y)), ID.ident_ok(SK.VE.x(x), SK.VE.x(y), hx)(p)),
    LQ.q_mul_cong_r(c, E.qeval(p, SK.VE.y(x)), E.qeval(p, SK.VE.y(y)), ID.ident_ok(SK.VE.y(x), SK.VE.y(y), hy)(p)))

# x = y gives g x = g y
def gmul_cong(g: DR.Lab, +x: SK.VE, +y: SK.VE, h: VD.SameVD(x, y)) -> VD.SameVD(DR.gmul(g, x), DR.gmul(g, y)):
  match g:
    case DR.Lab{+c, +s}:
      (+hx, +hy) = h
      (ID.qzero_ident(SK.VE.x(DR.gmul(DR.Lab{c, s}, x)), SK.VE.x(DR.gmul(DR.Lab{c, s}, y)), p => gcong.ax(p, c, s, x, y, hx, hy)),
       ID.qzero_ident(SK.VE.y(DR.gmul(DR.Lab{c, s}, x)), SK.VE.y(DR.gmul(DR.Lab{c, s}, y)), p => gcong.ay(p, c, s, x, y, hx, hy)))

# g (h x) = (g h) x
def compd(+g: DR.Lab, +h: DR.Lab, +x: SK.VE) -> VD.SameVD(DR.gmul(g, DR.gmul(h, x)), DR.gmul(LB.lmul(g, h), x)):
  VD.samevd_of(DR.gmul(g, DR.gmul(h, x)), DR.gmul(LB.lmul(g, h), x), LP.gmul_comp(g, h, x))

# conj(conj(g)) (h x) = (g h) x
def ccomp(+g: DR.Lab, +h: DR.Lab, +x: SK.VE) -> VD.SameVD(DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), DR.gmul(h, x)), DR.gmul(LB.lmul(g, h), x)):
  GN.samevd_tr(DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), DR.gmul(h, x)), DR.gmul(g, DR.gmul(h, x)), DR.gmul(LB.lmul(g, h), x),
    samevd_sym(DR.gmul(g, DR.gmul(h, x)), DR.gmul(DR.Lab.conj(DR.Lab.conj(g)), DR.gmul(h, x)), GN.cc(g, DR.gmul(h, x))), compd(g, h, x))

# Rerooting
# ---------

def reroot.yes(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der,
  +old: DR.Node, +new: DR.Node, +ww: DR.Lab, +dR: DR.Der, er: {r == old : DR.Node}, hm: GN.MOkD(es, fs, ctx, t, DC.Mem{a, r, w, d}), +hR: GN.MOkD(es, fs, ctx, t, DC.Mem{old, new, ww, dR}))
  -> GN.MOkD(es, fs, ctx, t, DC.Mem{a, new, LB.lmul(ww, w), DR.DThrough{dR, d, DR.Lab.conj(ww), old}}):
  (v, r1) = hm
  (p, r2) = r1
  (ea, r3) = r2
  (sv, r4) = r3
  (oa, r5) = r4
  (orr, b) = r5
  (vR, s1) = hR
  (pR, s2) = s1
  (eR, s3) = s2
  (svR, s4) = s3
  (oold, s5) = s4
  (onew, bR) = s5
  ((vR, (v, (pR, (p, (GN.samevd_tr(DR.Jd.x(DR.concl(es, fs, dR)), DR.gmul(ww, DR.zdir(es, old)), DR.gmul(DR.Lab.conj(DR.Lab.conj(ww)), DR.zdir(es, old)), svR, GN.cc(ww, DR.zdir(es, old))),
     (Equal.trans(DR.Node, DR.Jd.a(DR.concl(es, fs, d)), r, old, ea, er), oold)))))),
   ({==}, (eR, (GN.samevd_tr(DR.gmul(DR.Lab.conj(DR.Lab.conj(ww)), DR.Jd.x(DR.concl(es, fs, d))), DR.gmul(DR.Lab.conj(DR.Lab.conj(ww)), DR.gmul(w, DR.zdir(es, a))), DR.gmul(LB.lmul(ww, w), DR.zdir(es, a)),
       gmul_cong(DR.Lab.conj(DR.Lab.conj(ww)), DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(w, DR.zdir(es, a)), sv), ccomp(ww, w, DR.zdir(es, a))),
     (oa, (onew, BL.vb_gmul(DR.Lab.conj(DR.Lab.conj(ww)), DR.Jd.x(DR.concl(es, fs, d)), t, b)))))))

def reroot.ok1(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der,
  +old: DR.Node, +new: DR.Node, +ww: DR.Lab, +dR: DR.Der, ef: {f == DC.node_eq(r, old) : Bool}, hm: GN.MOkD(es, fs, ctx, t, DC.Mem{a, r, w, d}), +hR: GN.MOkD(es, fs, ctx, t, DC.Mem{old, new, ww, dR}))
  -> GN.MOkD(es, fs, ctx, t, DC.reroot.one(f, a, r, w, d, new, dR, ww, old)):
  match f:
    case True{}:
      reroot.yes(es, fs, ctx, t, a, r, w, d, old, new, ww, dR, GN.node_eq_ok(r, old, Equal.sym(Bool, True{}, DC.node_eq(r, old), ef)), hm, hR)
    case False{}:
      hm

# moving old's members under new keeps the invariant
def reroot_ok(ms: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +old: DR.Node, +new: DR.Node, +dR: DR.Der, +ww: DR.Lab,
  hms: GN.MsOk(es, fs, ctx, t, ms), +hR: GN.MOkD(es, fs, ctx, t, DC.Mem{old, new, ww, dR})) -> GN.MsOk(es, fs, ctx, t, DC.reroot(ms, old, new, dR, ww)):
  match ms:
    case Nil{}:
      Unit{}
    case Con{DC.Mem{+a, +r, +w, +d}, tl}:
      (hm, rt) = hms
      (reroot.ok1(DC.node_eq(r, old), es, fs, ctx, t, a, r, w, d, old, new, ww, dR, {==}, hm, hR), reroot_ok(tl, es, fs, ctx, t, old, new, dR, ww, rt, hR))

# Merges
# ------

def zmove(+es: List<&2, SK.Ent>, +g: DR.Lab, +h: DR.Lab, +a1: DR.Node, +rr: DR.Node, +y: SK.VE, e: {a1 == rr : DR.Node}, hs: VD.SameVD(DR.gmul(g, DR.gmul(h, DR.zdir(es, rr))), y))
  -> VD.SameVD(DR.gmul(g, DR.gmul(h, DR.zdir(es, a1))), y):
  %Equal.sym(DR.Node, a1, rr, e) : VD.SameVD(DR.gmul(g, DR.gmul(h, DR.zdir(es, _))), y)
  hs

def ccw(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +d: DR.Der, +w: DR.Lab, +b: DR.Node, +sv: VD.SameVD(DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(w, DR.zdir(es, b))))
  -> VD.SameVD(DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(DR.Lab.conj(DR.Lab.conj(w)), DR.zdir(es, b))):
  GN.samevd_tr(DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(w, DR.zdir(es, b)), DR.gmul(DR.Lab.conj(DR.Lab.conj(w)), DR.zdir(es, b)), sv, GN.cc(w, DR.zdir(es, b)))

# F's component absorbs rr's: dR proves par(F, wb conj(w) z_rr)
def merge_ok.frame(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +rr: DR.Node, +d1: DR.Der, +w: DR.Lab, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  +hz: {DC.zb(es, t) == True{} : Bool}, erb: {rb == DR.NFrame{} : DR.Node}, h1: GN.MOkD(es, fs, ctx, t, DC.Mem{b, rr, w, d1}), hb: GN.MOkD(es, fs, ctx, t, DC.Mem{b, rb, wb, db}))
  -> GN.MOkD(es, fs, ctx, t, DC.Mem{rr, DR.NFrame{}, LB.lmul(wb, DR.Lab.conj(w)), DR.DThrough{db, DR.DTurn{d1, DR.Lab.conj(w), b}, DR.Lab.conj(wb), b}}):
  (v1, r1) = h1
  (p1, r2) = r1
  (+e1, r3) = r2
  (sv1, r4) = r3
  (ob, r5) = r4
  (orr, b1) = r5
  (vb, s1) = hb
  (pb, s2) = s1
  (eb, s3) = s2
  (svb, s4) = s3
  (ob2, s5) = s4
  (orb, bb) = s5
  ((vb, ((v1, (p1, ccw(es, fs, d1, w, b, sv1))), (pb, ({==}, (ccw(es, fs, db, wb, b, svb), ({==}, ob)))))),
   ({==}, (Equal.trans(DR.Node, DR.Jd.a(DR.concl(es, fs, db)), rb, DR.NFrame{}, eb, erb),
     (zmove(es, DR.Lab.conj(DR.Lab.conj(wb)), DR.Lab.conj(w), DR.Jd.a(DR.concl(es, fs, d1)), rr, DR.gmul(LB.lmul(wb, DR.Lab.conj(w)), DR.zdir(es, rr)), e1, ccomp(wb, DR.Lab.conj(w), DR.zdir(es, rr))),
      (orr, ({==}, BL.vb_gmul(DR.Lab.conj(DR.Lab.conj(wb)), DR.gmul(DR.Lab.conj(w), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, d1)))), t,
        BL.vb_gmul(DR.Lab.conj(w), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, d1))), t, BL.zdir_below(es, t, DR.Jd.a(DR.concl(es, fs, d1)), hz)))))))))

# rr's component absorbs rb's: dR proves par(rr, w conj(wb) z_rb)
def merge_ok.into(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +rr: DR.Node, +d1: DR.Der, +w: DR.Lab, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  +hz: {DC.zb(es, t) == True{} : Bool}, h1: GN.MOkD(es, fs, ctx, t, DC.Mem{b, rr, w, d1}), hb: GN.MOkD(es, fs, ctx, t, DC.Mem{b, rb, wb, db}))
  -> GN.MOkD(es, fs, ctx, t, DC.Mem{rb, rr, LB.lmul(w, DR.Lab.conj(wb)), DR.DThrough{d1, DR.DTurn{db, DR.Lab.conj(wb), b}, DR.Lab.conj(w), b}}):
  (v1, r1) = h1
  (p1, r2) = r1
  (e1, r3) = r2
  (sv1, r4) = r3
  (ob, r5) = r4
  (orr, b1) = r5
  (vb, s1) = hb
  (pb, s2) = s1
  (+eb, s3) = s2
  (svb, s4) = s3
  (ob2, s5) = s4
  (orb, bb) = s5
  ((v1, ((vb, (pb, ccw(es, fs, db, wb, b, svb))), (p1, ({==}, (ccw(es, fs, d1, w, b, sv1), ({==}, ob)))))),
   ({==}, (e1,
     (zmove(es, DR.Lab.conj(DR.Lab.conj(w)), DR.Lab.conj(wb), DR.Jd.a(DR.concl(es, fs, db)), rb, DR.gmul(LB.lmul(w, DR.Lab.conj(wb)), DR.zdir(es, rb)), eb, ccomp(w, DR.Lab.conj(wb), DR.zdir(es, rb))),
      (orb, (orr, BL.vb_gmul(DR.Lab.conj(DR.Lab.conj(w)), DR.gmul(DR.Lab.conj(wb), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, db)))), t,
        BL.vb_gmul(DR.Lab.conj(wb), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, db))), t, BL.zdir_below(es, t, DR.Jd.a(DR.concl(es, fs, db)), hz)))))))))

def merge_ok.go(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ms: List<&2, DC.Mem>, +rr: DR.Node, +d1: DR.Der, +w: DR.Lab, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  +hz: {DC.zb(es, t) == True{} : Bool}, ef: {f == SV.band(DC.node_eq(rb, DR.NFrame{}), SV.bnot(DC.node_eq(rr, DR.NFrame{}))) : Bool}, hms: GN.MsOk(es, fs, ctx, t, ms),
  h1: GN.MOkD(es, fs, ctx, t, DC.Mem{b, rr, w, d1}), hb: GN.MOkD(es, fs, ctx, t, DC.Mem{b, rb, wb, db})) -> GN.MsOk(es, fs, ctx, t, DC.merge.go(f, ms, rr, d1, w, b, rb, wb, db)):
  match f:
    case True{}:
      reroot_ok(ms, es, fs, ctx, t, rr, DR.NFrame{}, DR.DThrough{db, DR.DTurn{d1, DR.Lab.conj(w), b}, DR.Lab.conj(wb), b}, LB.lmul(wb, DR.Lab.conj(w)), hms,
        merge_ok.frame(es, fs, ctx, t, rr, d1, w, b, rb, wb, db, hz,
          GN.node_eq_ok(rb, DR.NFrame{}, LP2.band_l(DC.node_eq(rb, DR.NFrame{}), SV.bnot(DC.node_eq(rr, DR.NFrame{})), Equal.sym(Bool, True{}, SV.band(DC.node_eq(rb, DR.NFrame{}), SV.bnot(DC.node_eq(rr, DR.NFrame{}))), ef))), h1, hb))
    case False{}:
      reroot_ok(ms, es, fs, ctx, t, rb, rr, DR.DThrough{d1, DR.DTurn{db, DR.Lab.conj(wb), b}, DR.Lab.conj(w), b}, LB.lmul(w, DR.Lab.conj(wb)), hms,
        merge_ok.into(es, fs, ctx, t, rr, d1, w, b, rb, wb, db, hz, h1, hb))

# a merge keeps the invariant, given d1 proves par(rr, w z_b) as a member
# record of b would
def merge_ok(m: DC.Mem, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ms: List<&2, DC.Mem>, +rr: DR.Node, +d1: DR.Der, +w: DR.Lab,
  +hz: {DC.zb(es, t) == True{} : Bool}, hms: GN.MsOk(es, fs, ctx, t, ms), hm: GN.MOkD(es, fs, ctx, t, m), h1: GN.MOkD(es, fs, ctx, t, DC.Mem{DC.Mem.a(m), rr, w, d1}))
  -> GN.MsOk(es, fs, ctx, t, DC.merge(ms, rr, d1, w, m)):
  match m:
    case DC.Mem{+b, +rb, +wb, +db}:
      merge_ok.go(SV.band(DC.node_eq(rb, DR.NFrame{}), SV.bnot(DC.node_eq(rr, DR.NFrame{}))), es, fs, ctx, t, ms, rr, d1, w, b, rb, wb, db, hz, {==}, hms, h1, hm)

# The merges found
# ----------------

def OptMs(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, m: Maybe<&2, List<&2, DC.Mem>>) -> Data:
  match m:
    case Some{x}:
      GN.MsOk(es, fs, ctx, t, x)
    case None{}:
      Unit

def AllOpenD(+es: List<&2, SK.Ent>, +ctx: List<&2, E.QExpr>, rs: List<&2, DR.Node>) -> Data:
  match rs:
    case Nil{}:
      Unit
    case Con{+r, tl}:
      SK.Both(VD.OpenD(es, ctx, r), AllOpenD(es, ctx, tl))

def roots_open.pick(f: Bool, +es: List<&2, SK.Ent>, +ctx: List<&2, E.QExpr>, +a: DR.Node, +oa: VD.OpenD(es, ctx, a), +rest: List<&2, DR.Node>, ih: AllOpenD(es, ctx, rest))
  -> AllOpenD(es, ctx, DC.roots.pick(f, a, rest)):
  match f:
    case True{}:
      (oa, ih)
    case False{}:
      ih

# the roots are open
def roots_open(ms: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, hms: GN.MsOk(es, fs, ctx, t, ms)) -> AllOpenD(es, ctx, DC.roots(ms)):
  match ms:
    case Nil{}:
      Unit{}
    case Con{DC.Mem{+a, +r, +w, +d}, +tl}:
      (hm, rt) = hms
      (v, r1) = hm
      (p, r2) = r1
      (e, r3) = r2
      (sv, r4) = r3
      (oa, r5) = r4
      roots_open.pick(DC.node_eq(a, r), es, ctx, a, oa, DC.roots(tl), roots_open(tl, es, fs, ctx, t, rt))

def mok_open(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der, hm: GN.MOkD(es, fs, ctx, t, DC.Mem{b, rb, wb, db}))
  -> VD.OpenD(es, ctx, b):
  (v, r1) = hm
  (p, r2) = r1
  (e, r3) = r2
  (sv, r4) = r3
  (oa, r5) = r4
  oa

# the frame test's label gives F a member record of b
def mgF.h1(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +k: KS.KS, +b: DR.Node, +w: DR.Lab, +ob: VD.OpenD(es, ctx, b), +hz: {DC.zb(es, t) == True{} : Bool},
  kd: SK.Both(VD.VD(es, fs, ctx, KS.ks.der(es, fs, k, SK.VE.y(DR.gmul(w, DR.zdir(es, b))))), SK.Both(VD.Isk(DR.concl(es, fs, KS.ks.der(es, fs, k, SK.VE.y(DR.gmul(w, DR.zdir(es, b)))))), VD.SameD(DR.Jd.e(DR.concl(es, fs, KS.ks.der(es, fs, k, SK.VE.y(DR.gmul(w, DR.zdir(es, b)))))), SK.VE.y(DR.gmul(w, DR.zdir(es, b)))))))
  -> GN.MOkD(es, fs, ctx, t, DC.Mem{b, DR.NFrame{}, w, DR.DFrame{KS.ks.der(es, fs, k, SK.VE.y(DR.gmul(w, DR.zdir(es, b)))), DR.gmul(w, DR.zdir(es, b))}}):
  (v, r1) = kd
  (ik, sd) = r1
  ((v, (ik, sd)), ({==}, ({==}, (samevd_refl(DR.gmul(w, DR.zdir(es, b))), (ob, ({==}, BL.vb_gmul(w, DR.zdir(es, b), t, BL.zdir_below(es, t, b, hz))))))))

def mgF.pick_ok(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +k: KS.KS, +ms: List<&2, DC.Mem>, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  em: {LB.ks.lab(es, fs, k, DR.zdir(es, b)) == m : Maybe<&2, DR.Lab>}, +hk: IV.KInvD(es, fs, ctx, t, k), +hms: GN.MsOk(es, fs, ctx, t, ms), +hmb: GN.MOkD(es, fs, ctx, t, DC.Mem{b, rb, wb, db}), +hz: {DC.zb(es, t) == True{} : Bool},
  +rest: Maybe<&2, List<&2, DC.Mem>>, hrest: OptMs(es, fs, ctx, t, rest)) -> OptMs(es, fs, ctx, t, DC.mgF.pick(m, es, fs, k, ms, DC.Mem{b, rb, wb, db}, b, rest)):
  match m:
    case None{}:
      hrest
    case Some{+w}:
      merge_ok(DC.Mem{b, rb, wb, db}, es, fs, ctx, t, ms, DR.NFrame{}, DR.DFrame{KS.ks.der(es, fs, k, SK.VE.y(DR.gmul(w, DR.zdir(es, b)))), DR.gmul(w, DR.zdir(es, b))}, w, hz, hms, hmb,
        mgF.h1(es, fs, ctx, t, k, b, w, mok_open(es, fs, ctx, t, b, rb, wb, db, hmb), hz,
          DD.ks_der_okd(es, fs, ctx, t, k, SK.VE.y(DR.gmul(w, DR.zdir(es, b))), hk, LP.ks_lab_ok(es, fs, ctx, k, DR.zdir(es, b), w, IV.kinv_of(es, fs, ctx, t, k, hk), em))))

def mgF.if_ok(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +k: KS.KS, +ms: List<&2, DC.Mem>, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  +hk: IV.KInvD(es, fs, ctx, t, k), +hms: GN.MsOk(es, fs, ctx, t, ms), +hmb: GN.MOkD(es, fs, ctx, t, DC.Mem{b, rb, wb, db}), +hz: {DC.zb(es, t) == True{} : Bool},
  +rest: Maybe<&2, List<&2, DC.Mem>>, hrest: OptMs(es, fs, ctx, t, rest)) -> OptMs(es, fs, ctx, t, DC.mgF.if(f, es, fs, k, ms, DC.Mem{b, rb, wb, db}, b, rest)):
  match f:
    case True{}:
      mgF.pick_ok(LB.ks.lab(es, fs, k, DR.zdir(es, b)), es, fs, ctx, t, k, ms, b, rb, wb, db, {==}, hk, hms, hmb, hz, rest, hrest)
    case False{}:
      hrest

def mgF_ok(sc: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +k: KS.KS, +ms: List<&2, DC.Mem>,
  hsc: GN.MsOk(es, fs, ctx, t, sc), +hk: IV.KInvD(es, fs, ctx, t, k), +hms: GN.MsOk(es, fs, ctx, t, ms), +hz: {DC.zb(es, t) == True{} : Bool}) -> OptMs(es, fs, ctx, t, DC.mgF(sc, es, fs, k, ms)):
  match sc:
    case Nil{}:
      Unit{}
    case Con{DC.Mem{+b, +rb, +wb, +db}, +tl}:
      (hm, rt) = hsc
      mgF.if_ok(SV.bnot(DC.node_eq(rb, DR.NFrame{})), es, fs, ctx, t, k, ms, b, rb, wb, db, hk, hms, hm, hz, DC.mgF(tl, es, fs, k, ms), mgF_ok(tl, es, fs, ctx, t, k, ms, rt, hk, hms, hz))

# the hull label test's label gives r a member record of b
def mgR.h1(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +h: HS.HS, +r: DR.Node, +b: DR.Node, +w: DR.Lab, +ob: VD.OpenD(es, ctx, b), +orr: VD.OpenD(es, ctx, r),
  hd: SK.Both(SK.Both(SK.Both(VD.VD(es, fs, ctx, HS.hs.der(es, fs, t, r, h, DR.gmul(w, DR.zdir(es, b)))), SK.Both(VD.Isp(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, DR.gmul(w, DR.zdir(es, b))))), {DR.Jd.a(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, DR.gmul(w, DR.zdir(es, b))))) == r : DR.Node})),
       HP.VBelow(DR.Jd.x(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, DR.gmul(w, DR.zdir(es, b))))), t)), VD.SameVD(DR.Jd.x(DR.concl(es, fs, HS.hs.der(es, fs, t, r, h, DR.gmul(w, DR.zdir(es, b))))), DR.gmul(w, DR.zdir(es, b)))))
  -> GN.MOkD(es, fs, ctx, t, DC.Mem{b, r, w, HS.hs.der(es, fs, t, r, h, DR.gmul(w, DR.zdir(es, b)))}):
  (vb, sv) = hd
  (vpa, bx) = vb
  (v, r1) = vpa
  (p, ea) = r1
  (v, (p, (ea, (sv, (ob, (orr, bx))))))

def mgR.pick_ok(m: Maybe<&2, DR.Lab>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +h: HS.HS, +r: DR.Node, +ms: List<&2, DC.Mem>, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  em: {LB.hs.lab(es, fs, t, h, DR.zdir(es, b)) == m : Maybe<&2, DR.Lab>}, +hi: IV.HInvD(es, fs, ctx, r, t, h), +orr: VD.OpenD(es, ctx, r), +hms: GN.MsOk(es, fs, ctx, t, ms), +hmb: GN.MOkD(es, fs, ctx, t, DC.Mem{b, rb, wb, db}), +hz: {DC.zb(es, t) == True{} : Bool},
  +rest: Maybe<&2, List<&2, DC.Mem>>, hrest: OptMs(es, fs, ctx, t, rest)) -> OptMs(es, fs, ctx, t, DC.mgR.pick(m, es, fs, t, h, r, ms, DC.Mem{b, rb, wb, db}, b, rest)):
  match m:
    case None{}:
      hrest
    case Some{+w}:
      merge_ok(DC.Mem{b, rb, wb, db}, es, fs, ctx, t, ms, r, HS.hs.der(es, fs, t, r, h, DR.gmul(w, DR.zdir(es, b))), w, hz, hms, hmb,
        mgR.h1(es, fs, ctx, t, h, r, b, w, mok_open(es, fs, ctx, t, b, rb, wb, db, hmb), orr,
          DD.hs_der_okd(es, fs, ctx, r, t, h, DR.gmul(w, DR.zdir(es, b)), hi, LP.hs_lab_ok(es, fs, ctx, r, t, h, DR.zdir(es, b), w, IV.hinv_of(es, fs, ctx, r, t, h, hi), em),
            BL.vb_gmul(w, DR.zdir(es, b), t, BL.zdir_below(es, t, b, hz)), BL.zdir_below(es, t, r, hz))))

def mgR.if_ok(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +h: HS.HS, +r: DR.Node, +ms: List<&2, DC.Mem>, +b: DR.Node, +rb: DR.Node, +wb: DR.Lab, +db: DR.Der,
  +hi: IV.HInvD(es, fs, ctx, r, t, h), +orr: VD.OpenD(es, ctx, r), +hms: GN.MsOk(es, fs, ctx, t, ms), +hmb: GN.MOkD(es, fs, ctx, t, DC.Mem{b, rb, wb, db}), +hz: {DC.zb(es, t) == True{} : Bool},
  +rest: Maybe<&2, List<&2, DC.Mem>>, hrest: OptMs(es, fs, ctx, t, rest)) -> OptMs(es, fs, ctx, t, DC.mgR.if(f, es, fs, t, h, r, ms, DC.Mem{b, rb, wb, db}, b, rest)):
  match f:
    case True{}:
      mgR.pick_ok(LB.hs.lab(es, fs, t, h, DR.zdir(es, b)), es, fs, ctx, t, h, r, ms, b, rb, wb, db, {==}, hi, orr, hms, hmb, hz, rest, hrest)
    case False{}:
      hrest

def mgR_ok(sc: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +h: HS.HS, +r: DR.Node, +ms: List<&2, DC.Mem>,
  hsc: GN.MsOk(es, fs, ctx, t, sc), +hi: IV.HInvD(es, fs, ctx, r, t, h), +orr: VD.OpenD(es, ctx, r), +hms: GN.MsOk(es, fs, ctx, t, ms), +hz: {DC.zb(es, t) == True{} : Bool}) -> OptMs(es, fs, ctx, t, DC.mgR(sc, es, fs, t, h, r, ms)):
  match sc:
    case Nil{}:
      Unit{}
    case Con{DC.Mem{+b, +rb, +wb, +db}, +tl}:
      (hm, rt) = hsc
      mgR.if_ok(SV.bnot(DC.node_eq(rb, r)), es, fs, ctx, t, h, r, ms, b, rb, wb, db, hi, orr, hms, hm, hz, DC.mgR(tl, es, fs, t, h, r, ms), mgR_ok(tl, es, fs, ctx, t, h, r, ms, rt, hi, orr, hms, hz))

def mgs.pick_ok(m: Maybe<&2, List<&2, DC.Mem>>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, hm: OptMs(es, fs, ctx, t, m), +rest: Maybe<&2, List<&2, DC.Mem>>, hr: OptMs(es, fs, ctx, t, rest))
  -> OptMs(es, fs, ctx, t, DC.mgs.pick(m, rest)):
  match m:
    case None{}:
      hr
    case Some{+x}:
      hm

def mgs.root_ok(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +r: DR.Node, +orr: VD.OpenD(es, ctx, r),
  +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> OptMs(es, fs, ctx, t, DC.mgs.root(f, es, fs, t, s, r)):
  match f:
    case True{}:
      mgF_ok(DC.Sk.ms(s), es, fs, ctx, t, DC.Sk.k(s), DC.Sk.ms(s), hms, hk, hms, hz)
    case False{}:
      mgR_ok(DC.Sk.ms(s), es, fs, ctx, t, DC.rhull(es, fs, t, s, r), r, DC.Sk.ms(s), hms, GN.rhull_inv(es, fs, ctx, t, s, r, hk, hms, hls, hz, hb), orr, hms, hz)

# the first merge found keeps the members' invariant
def mgs_ok(rs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, hro: AllOpenD(es, ctx, rs),
  +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> OptMs(es, fs, ctx, t, DC.mgs(rs, es, fs, t, s)):
  match rs:
    case Nil{}:
      Unit{}
    case Con{+r, +tl}:
      (orr, rt) = hro
      mgs.pick_ok(DC.mgs.root(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r), es, fs, ctx, t, mgs.root_ok(DC.node_eq(r, DR.NFrame{}), es, fs, ctx, t, s, r, orr, hk, hms, hls, hz, hb),
        DC.mgs(tl, es, fs, t, s), mgs_ok(tl, es, fs, ctx, t, s, rt, hk, hms, hls, hz, hb))
