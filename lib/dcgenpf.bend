# bend-cad: the closure's root generators are right (PLAN-sk13b B3). With
# the members' and links' invariants (MOkD, LOkD), every generator of an
# open root r (lib/dclose.bend's rgens: the members' derivations, their
# statements and link turns passed through them) and every K-squared
# generator is a valid parallel judgment at r with its form below t
# (rgens_ok, kgens_ok), so every rebuilt root hull keeps its invariant
# (rhull_inv). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./q.bend as LQ
import ./qring.bend as QR
import ./qalg.bend as QA
import ./qnorm.bend as QN
import ./identpf.bend as ID
import ./listpf.bend as LP2
import ./seppf.bend as SP
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./hspacepf.bend as HP
import ./lab.bend as LB
import ./labpf.bend as LP
import ./pairpf.bend as PP
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcinvpf.bend as IV
import ./dcbelowpf.bend as BL

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Label identities, as Data
# -------------------------

def samed_tr.at(+p: List<&2, S.Q>, +a: E.QExpr, +b: E.QExpr, +c: E.QExpr, +h1: VD.SameD(a, b), +h2: VD.SameD(b, c)) -> S.Q.eq(E.qeval(p, a), E.qeval(p, c)):
  LQ.q_trans(E.qeval(p, a), E.qeval(p, b), E.qeval(p, c), ID.ident_ok(a, b, h1)(p), ID.ident_ok(b, c, h2)(p))

def samed_tr(+a: E.QExpr, +b: E.QExpr, +c: E.QExpr, +h1: VD.SameD(a, b), +h2: VD.SameD(b, c)) -> VD.SameD(a, c):
  ID.qzero_ident(a, c, p => samed_tr.at(p, a, b, c, h1, h2))

def samevd_tr(+u: SK.VE, +v: SK.VE, +w: SK.VE, h1: VD.SameVD(u, v), h2: VD.SameVD(v, w)) -> VD.SameVD(u, w):
  (a1, b1) = h1
  (a2, b2) = h2
  (samed_tr(SK.VE.x(u), SK.VE.x(v), SK.VE.x(w), a1, a2), samed_tr(SK.VE.y(u), SK.VE.y(v), SK.VE.y(w), b1, b2))

def negneg.n(n: S.Z, +d: S.Pos) -> S.Q.eq(S.Q{n, d}, S.Q.neg(S.Q.neg(S.Q{n, d}))):
  match n:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      {==}
    case S.Zneg{p}:
      {==}

def negneg(q: S.Q) -> S.Q.eq(q, S.Q.neg(S.Q.neg(q))):
  match q:
    case S.Q{n, d}:
      negneg.n(n, d)

def cc.ax(+p: List<&2, S.Q>, +c: S.Q, +s: S.Q, +z: SK.VE) -> S.Q.eq(E.qeval(p, SK.VE.x(DR.gmul(DR.Lab{c, s}, z))), E.qeval(p, SK.VE.x(DR.gmul(DR.Lab.conj(DR.Lab.conj(DR.Lab{c, s})), z)))):
  QA.sub_cong(S.Q.mul(c, E.qeval(p, SK.VE.x(z))), S.Q.mul(c, E.qeval(p, SK.VE.x(z))), S.Q.mul(s, E.qeval(p, SK.VE.y(z))), S.Q.mul(S.Q.neg(S.Q.neg(s)), E.qeval(p, SK.VE.y(z))),
    LQ.q_refl(S.Q.mul(c, E.qeval(p, SK.VE.x(z)))), LQ.q_mul_cong_l(s, S.Q.neg(S.Q.neg(s)), E.qeval(p, SK.VE.y(z)), negneg(s)))

def cc.ay(+p: List<&2, S.Q>, +c: S.Q, +s: S.Q, +z: SK.VE) -> S.Q.eq(E.qeval(p, SK.VE.y(DR.gmul(DR.Lab{c, s}, z))), E.qeval(p, SK.VE.y(DR.gmul(DR.Lab.conj(DR.Lab.conj(DR.Lab{c, s})), z)))):
  QA.add_cong(S.Q.mul(s, E.qeval(p, SK.VE.x(z))), S.Q.mul(S.Q.neg(S.Q.neg(s)), E.qeval(p, SK.VE.x(z))), S.Q.mul(c, E.qeval(p, SK.VE.y(z))), S.Q.mul(c, E.qeval(p, SK.VE.y(z))),
    LQ.q_mul_cong_l(s, S.Q.neg(S.Q.neg(s)), E.qeval(p, SK.VE.x(z)), negneg(s)), LQ.q_refl(S.Q.mul(c, E.qeval(p, SK.VE.y(z)))))

# w z = conj(conj(w)) z
def cc(w: DR.Lab, +z: SK.VE) -> VD.SameVD(DR.gmul(w, z), DR.gmul(DR.Lab.conj(DR.Lab.conj(w)), z)):
  match w:
    case DR.Lab{+c, +s}:
      VD.samevd_of(DR.gmul(DR.Lab{c, s}, z), DR.gmul(DR.Lab.conj(DR.Lab.conj(DR.Lab{c, s})), z), (p => cc.ax(p, c, s, z), p => cc.ay(p, c, s, z)))

def one.ax(+p: List<&2, S.Q>, +z: SK.VE) -> S.Q.eq(E.qeval(p, SK.VE.x(z)), E.qeval(p, SK.VE.x(DR.gmul(DC.lone(), z)))):
  QR.qring_eq([E.qeval(p, SK.VE.x(z)), E.qeval(p, SK.VE.y(z))], E.QVar{0n}, E.QSub{E.QMul{E.QCst{DR.qo()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}}, {==})

def one.ay(+p: List<&2, S.Q>, +z: SK.VE) -> S.Q.eq(E.qeval(p, SK.VE.y(z)), E.qeval(p, SK.VE.y(DR.gmul(DC.lone(), z)))):
  QR.qring_eq([E.qeval(p, SK.VE.x(z)), E.qeval(p, SK.VE.y(z))], E.QVar{1n}, E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qo()}, E.QVar{1n}}}, {==})

# z = 1 z
def one(+z: SK.VE) -> VD.SameVD(z, DR.gmul(DC.lone(), z)):
  VD.samevd_of(z, DR.gmul(DC.lone(), z), (p => one.ax(p, z), p => one.ay(p, z)))

# Trimmed labels
# --------------

def gtrim.ax(+p: List<&2, S.Q>, +c: S.Q, +s: S.Q, +x: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.x(DR.gmul(DR.Lab{c, s}, x))), E.qeval(p, SK.VE.x(DR.gmul(DR.Lab{LB.qtrim(c), LB.qtrim(s)}, x)))):
  QA.sub_cong(S.Q.mul(c, E.qeval(p, SK.VE.x(x))), S.Q.mul(LB.qtrim(c), E.qeval(p, SK.VE.x(x))), S.Q.mul(s, E.qeval(p, SK.VE.y(x))), S.Q.mul(LB.qtrim(s), E.qeval(p, SK.VE.y(x))),
    LQ.q_mul_cong_l(c, LB.qtrim(c), E.qeval(p, SK.VE.x(x)), LQ.q_sym(LB.qtrim(c), c, LP.qtrim_ok(c))),
    LQ.q_mul_cong_l(s, LB.qtrim(s), E.qeval(p, SK.VE.y(x)), LQ.q_sym(LB.qtrim(s), s, LP.qtrim_ok(s))))

def gtrim.ay(+p: List<&2, S.Q>, +c: S.Q, +s: S.Q, +x: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.y(DR.gmul(DR.Lab{c, s}, x))), E.qeval(p, SK.VE.y(DR.gmul(DR.Lab{LB.qtrim(c), LB.qtrim(s)}, x)))):
  QA.add_cong(S.Q.mul(s, E.qeval(p, SK.VE.x(x))), S.Q.mul(LB.qtrim(s), E.qeval(p, SK.VE.x(x))), S.Q.mul(c, E.qeval(p, SK.VE.y(x))), S.Q.mul(LB.qtrim(c), E.qeval(p, SK.VE.y(x))),
    LQ.q_mul_cong_l(s, LB.qtrim(s), E.qeval(p, SK.VE.x(x)), LQ.q_sym(LB.qtrim(s), s, LP.qtrim_ok(s))),
    LQ.q_mul_cong_l(c, LB.qtrim(c), E.qeval(p, SK.VE.y(x)), LQ.q_sym(LB.qtrim(c), c, LP.qtrim_ok(c))))

# a trimmed label acts as the label
def gtrim(g: DR.Lab, +x: SK.VE) -> VD.SameVD(DR.gmul(g, x), DR.gmul(LB.ltrim(g), x)):
  match g:
    case DR.Lab{+c, +s}:
      VD.samevd_of(DR.gmul(DR.Lab{c, s}, x), DR.gmul(DR.Lab{LB.qtrim(c), LB.qtrim(s)}, x), (p => gtrim.ax(p, c, s, x), p => gtrim.ay(p, c, s, x)))

def gtrim_c.ax(+p: List<&2, S.Q>, +c: S.Q, +s: S.Q, +x: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.x(DR.gmul(DR.Lab{c, S.Q.neg(s)}, x))), E.qeval(p, SK.VE.x(DR.gmul(DR.Lab{LB.qtrim(c), S.Q.neg(LB.qtrim(s))}, x)))):
  QA.sub_cong(S.Q.mul(c, E.qeval(p, SK.VE.x(x))), S.Q.mul(LB.qtrim(c), E.qeval(p, SK.VE.x(x))), S.Q.mul(S.Q.neg(s), E.qeval(p, SK.VE.y(x))), S.Q.mul(S.Q.neg(LB.qtrim(s)), E.qeval(p, SK.VE.y(x))),
    LQ.q_mul_cong_l(c, LB.qtrim(c), E.qeval(p, SK.VE.x(x)), LQ.q_sym(LB.qtrim(c), c, LP.qtrim_ok(c))),
    LQ.q_mul_cong_l(S.Q.neg(s), S.Q.neg(LB.qtrim(s)), E.qeval(p, SK.VE.y(x)), LQ.q_neg_cong(s, LB.qtrim(s), LQ.q_sym(LB.qtrim(s), s, LP.qtrim_ok(s)))))

def gtrim_c.ay(+p: List<&2, S.Q>, +c: S.Q, +s: S.Q, +x: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.y(DR.gmul(DR.Lab{c, S.Q.neg(s)}, x))), E.qeval(p, SK.VE.y(DR.gmul(DR.Lab{LB.qtrim(c), S.Q.neg(LB.qtrim(s))}, x)))):
  QA.add_cong(S.Q.mul(S.Q.neg(s), E.qeval(p, SK.VE.x(x))), S.Q.mul(S.Q.neg(LB.qtrim(s)), E.qeval(p, SK.VE.x(x))), S.Q.mul(c, E.qeval(p, SK.VE.y(x))), S.Q.mul(LB.qtrim(c), E.qeval(p, SK.VE.y(x))),
    LQ.q_mul_cong_l(S.Q.neg(s), S.Q.neg(LB.qtrim(s)), E.qeval(p, SK.VE.x(x)), LQ.q_neg_cong(s, LB.qtrim(s), LQ.q_sym(LB.qtrim(s), s, LP.qtrim_ok(s)))),
    LQ.q_mul_cong_l(c, LB.qtrim(c), E.qeval(p, SK.VE.y(x)), LQ.q_sym(LB.qtrim(c), c, LP.qtrim_ok(c))))

# and its conjugate acts as the label's
def gtrim_c(g: DR.Lab, +x: SK.VE) -> VD.SameVD(DR.gmul(DR.Lab.conj(g), x), DR.gmul(DR.Lab.conj(LB.ltrim(g)), x)):
  match g:
    case DR.Lab{+c, +s}:
      VD.samevd_of(DR.gmul(DR.Lab{c, S.Q.neg(s)}, x), DR.gmul(DR.Lab{LB.qtrim(c), S.Q.neg(LB.qtrim(s))}, x), (p => gtrim_c.ax(p, c, s, x), p => gtrim_c.ay(p, c, s, x)))

# Nodes
# -----

def node_eq_ok(a: DR.Node, b: DR.Node, h: {DC.node_eq(a, b) == True{} : Bool}) -> {a == b : DR.Node}:
  match a b:
    case DR.NFrame{} DR.NFrame{}:
      {==}
    case DR.NFrame{} DR.NSeg{t}:
      absurd({DR.NFrame{} == DR.NSeg{t} : DR.Node}, LP.tf(Equal.sym(Bool, False{}, True{}, h)))
    case DR.NSeg{s} DR.NFrame{}:
      absurd({DR.NSeg{s} == DR.NFrame{} : DR.Node}, LP.tf(Equal.sym(Bool, False{}, True{}, h)))
    case DR.NSeg{s} DR.NSeg{t}:
      Equal.cong(Nat, DR.Node, n => DR.NSeg{n}, s, t, LP2.eq_ok(s, t, h))

# The members and links
# ---------------------

# a member: d proves par(r, x) validly, x the same as w z_a and below t,
# a and r open
def MOkD(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, m: DC.Mem) -> Data:
  match m:
    case DC.Mem{+a, +r, +w, +d}:
      SK.Both(VD.VD(es, fs, ctx, d), SK.Both(VD.Isp(DR.concl(es, fs, d)), SK.Both({DR.Jd.a(DR.concl(es, fs, d)) == r : DR.Node},
        SK.Both(VD.SameVD(DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(w, DR.zdir(es, a))), SK.Both(VD.OpenD(es, ctx, a), SK.Both(VD.OpenD(es, ctx, r), HP.VBelow(DR.Jd.x(DR.concl(es, fs, d)), t)))))))

# a member's label may be trimmed
def mok_trim(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der, h: MOkD(es, fs, ctx, t, DC.Mem{a, r, w, d}))
  -> MOkD(es, fs, ctx, t, DC.Mem{a, r, LB.ltrim(w), d}):
  (v, r1) = h
  (p, r2) = r1
  (ea, r3) = r2
  (sv, r4) = r3
  (v, (p, (ea, (samevd_tr(DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(w, DR.zdir(es, a)), DR.gmul(LB.ltrim(w), DR.zdir(es, a)), sv, gtrim(w, DR.zdir(es, a))), r4))))

def MsOk(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, ms: List<&2, DC.Mem>) -> Data:
  match ms:
    case Nil{}:
      Unit
    case Con{+m, tl}:
      SK.Both(MOkD(es, fs, ctx, t, m), MsOk(es, fs, ctx, t, tl))

# a link: d proves par(c, x) validly, x the same as w z_b and below t
def LOkD(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, l: DC.Link) -> Data:
  match l:
    case DC.Link{+c, +b, +w, +d}:
      SK.Both(VD.VD(es, fs, ctx, d), SK.Both(VD.Isp(DR.concl(es, fs, d)), SK.Both({DR.Jd.a(DR.concl(es, fs, d)) == DR.NSeg{c} : DR.Node},
        SK.Both(VD.SameVD(DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(w, DR.zdir(es, b))), HP.VBelow(DR.Jd.x(DR.concl(es, fs, d)), t)))))

def LsOk(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, ls: List<&2, DC.Link>) -> Data:
  match ls:
    case Nil{}:
      Unit
    case Con{+l, tl}:
      SK.Both(LOkD(es, fs, ctx, t, l), LsOk(es, fs, ctx, t, tl))

# Through a member
# ----------------

# d2 proves par(a, y) validly with y below t: through a gives par(r, w y)
def thr_gen(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der,
  +hv: VD.VD(es, fs, ctx, d), +hp: VD.Isp(DR.concl(es, fs, d)), +ha: {DR.Jd.a(DR.concl(es, fs, d)) == r : DR.Node}, +hs: VD.SameVD(DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(w, DR.zdir(es, a))), +ho: VD.OpenD(es, ctx, a),
  +d2: DR.Der, g2: IV.PGenD(es, fs, ctx, a, t, d2)) -> IV.PGenD(es, fs, ctx, r, t, DC.thr(d, w, a, d2)):
  (v2, r1) = g2
  (p2, r2) = r1
  (a2, b2) = r2
  ((hv, (v2, (hp, (p2, (samevd_tr(DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(w, DR.zdir(es, a)), DR.gmul(DR.Lab.conj(DR.Lab.conj(w)), DR.zdir(es, a)), hs, cc(w, DR.zdir(es, a))), (a2, ho)))))),
   ({==}, (ha, BL.vb_gmul(DR.Lab.conj(DR.Lab.conj(w)), DR.Jd.x(DR.concl(es, fs, d2)), t, b2))))

def lstats_ok(ps: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der,
  +hv: VD.VD(es, fs, ctx, d), +hp: VD.Isp(DR.concl(es, fs, d)), +ha: {DR.Jd.a(DR.concl(es, fs, d)) == r : DR.Node}, +hs: VD.SameVD(DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(w, DR.zdir(es, a))), +ho: VD.OpenD(es, ctx, a),
  h: IV.AllPD(es, fs, ctx, a, t, ps)) -> IV.AllPD(es, fs, ctx, r, t, DC.lstats(ps, a, w, d)):
  match ps:
    case Nil{}:
      Unit{}
    case Con{+p, tl}:
      (g, rt) = h
      (thr_gen(es, fs, ctx, t, a, r, w, d, hv, hp, ha, hs, ho, p, g), lstats_ok(tl, es, fs, ctx, t, a, r, w, d, hv, hp, ha, hs, ho, rt))

# Statements
# ----------

def fdrop(i: Nat, fs: List<&2, DR.Fact>) -> List<&2, DR.Fact>:
  DC.fdrop(i, fs)

def lis_con(l: List<&2, DR.Fact>) -> Bool:
  match l:
    case Nil{}:
      False{}
    case Con{f, tl}:
      True{}

def fhd(l: List<&2, DR.Fact>, +d: DR.Fact) -> DR.Fact:
  match l:
    case Nil{}:
      d
    case Con{f, tl}:
      f

def ftl(l: List<&2, DR.Fact>) -> List<&2, DR.Fact>:
  match l:
    case Nil{}:
      Nil{}
    case Con{f, tl}:
      tl

def lnil_con(+f: DR.Fact, +tl: List<&2, DR.Fact>, h: {Nil{} == Con{f, tl} : List<&2, DR.Fact>}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, Equal.cong(List<&2, DR.Fact>, Bool, l => lis_con(l), Nil{}, Con{f, tl}, h)) : PP.none_some.p(_)
  Unit{}

def fat_drop(i: Nat, fs: List<&2, DR.Fact>, +f: DR.Fact, +tl: List<&2, DR.Fact>, h: {fdrop(i, fs) == Con{f, tl} : List<&2, DR.Fact>}) -> {DR.fact_at(fs, i) == Some{f} : Maybe<&2, DR.Fact>}:
  match i fs:
    case 0n Nil{}:
      absurd({None{} == Some{f} : Maybe<&2, DR.Fact>}, lnil_con(f, tl, h))
    case 0n Con{+f2, +t2}:
      Equal.cong(List<&2, DR.Fact>, Maybe<&2, DR.Fact>, l => Some{fhd(l, f)}, Con{f2, t2}, Con{f, tl}, h)
    case 1n+j Nil{}:
      absurd({None{} == Some{f} : Maybe<&2, DR.Fact>}, lnil_con(f, tl, h))
    case 1n+j Con{f2, t2}:
      fat_drop(j, t2, f, tl, h)

def fdrop_tl(i: Nat, fs: List<&2, DR.Fact>, +f: DR.Fact, +tl: List<&2, DR.Fact>, h: {fdrop(i, fs) == Con{f, tl} : List<&2, DR.Fact>}) -> {fdrop(1n+i, fs) == tl : List<&2, DR.Fact>}:
  match i fs:
    case 0n Nil{}:
      absurd({Nil{} == tl : List<&2, DR.Fact>}, lnil_con(f, tl, h))
    case 0n Con{+f2, +t2}:
      Equal.cong(List<&2, DR.Fact>, List<&2, DR.Fact>, l => ftl(l), Con{f2, t2}, Con{f, tl}, h)
    case 1n+j Nil{}:
      absurd({Nil{} == tl : List<&2, DR.Fact>}, lnil_con(f, tl, h))
    case 1n+j Con{f2, t2}:
      fdrop_tl(j, t2, f, tl, h)

# what a statement at s brings, read off the fact
def SGen(m: Maybe<&2, DR.Fact>, +s: Nat, +t: Nat) -> Data:
  SK.Both({VD.hass(m) == True{} : Bool}, SK.Both(VD.Isp(DR.fact.pj(m)), SK.Both({DR.Jd.a(DR.fact.pj(m)) == DR.NSeg{s} : DR.Node}, HP.VBelow(DR.Jd.x(DR.fact.pj(m)), t))))

def stat_gen(ds: Maybe<&2, DR.DStat>, +e: E.QExpr, +nd: List<&2, Nat>, +s: Nat, +t: Nat, +hb: {DC.fb.ds(ds, t) == True{} : Bool}, +hok: {DC.stat_ok(ds, s) == True{} : Bool})
  -> SGen(Some{DR.Fact{e, nd, ds}}, s, t):
  match ds:
    case Some{DR.DStat{+a, +x, +l}}:
      (LP2.band_r(SV.eq(a, s), DR.qnz(l), hok), ({==}, (Equal.cong(Nat, DR.Node, n => DR.NSeg{n}, a, s, LP2.eq_ok(a, s, LP2.band_l(SV.eq(a, s), DR.qnz(l), hok))),
        (LP2.band_l(SP.vbelow(SK.VE.x(x), t), SP.vbelow(SK.VE.y(x), t), hb), LP2.band_r(SP.vbelow(SK.VE.x(x), t), SP.vbelow(SK.VE.y(x), t), hb)))))
    case None{}:
      absurd(SGen(Some{DR.Fact{e, nd, None{}}}, s, t), LP.tf(Equal.sym(Bool, False{}, True{}, hok)))

def stat_at(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +s: Nat, +t: Nat, +i: Nat, +f: DR.Fact, e: {Some{f} == DR.fact_at(fs, i) : Maybe<&2, DR.Fact>}, hf: SGen(Some{f}, s, t))
  -> IV.PGenD(es, fs, ctx, DR.NSeg{s}, t, DR.DPPrem{i}):
  %e : SGen(_, s, t)
  hf

def stats_ok.pick(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +s: Nat, +t: Nat, +i: Nat, +e: E.QExpr, +nd: List<&2, Nat>, +ds: Maybe<&2, DR.DStat>, +tl: List<&2, DR.Fact>,
  eb: {b == DC.stat_ok(ds, s) : Bool}, +h: {fdrop(i, fs) == Con{DR.Fact{e, nd, ds}, tl} : List<&2, DR.Fact>}, +hb: {DC.fb.ds(ds, t) == True{} : Bool},
  ih: IV.AllPD(es, fs, ctx, DR.NSeg{s}, t, DC.pprems(DC.stats(tl, s, 1n+i)))) -> IV.AllPD(es, fs, ctx, DR.NSeg{s}, t, DC.pprems(DC.stats.pick(b, i, DC.stats(tl, s, 1n+i)))):
  match b:
    case True{}:
      (stat_at(es, fs, ctx, s, t, i, DR.Fact{e, nd, ds}, Equal.sym(Maybe<&2, DR.Fact>, DR.fact_at(fs, i), Some{DR.Fact{e, nd, ds}}, fat_drop(i, fs, DR.Fact{e, nd, ds}, tl, h)),
         stat_gen(ds, e, nd, s, t, hb, Equal.sym(Bool, True{}, DC.stat_ok(ds, s), eb))), ih)
    case False{}:
      ih

# the statements at s, from position i on (rest = the facts from i)
def stats_ok(rest: List<&2, DR.Fact>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +s: Nat, +t: Nat, +i: Nat,
  +h: {fdrop(i, fs) == rest : List<&2, DR.Fact>}, +hb: {DC.fb(rest, t) == True{} : Bool}) -> IV.AllPD(es, fs, ctx, DR.NSeg{s}, t, DC.pprems(DC.stats(rest, s, i))):
  match rest:
    case Nil{}:
      Unit{}
    case Con{DR.Fact{+e, +nd, +ds}, +tl}:
      stats_ok.pick(DC.stat_ok(ds, s), es, fs, ctx, s, t, i, e, nd, ds, tl, {==}, h,
        LP2.band_l(DC.fb.ds(ds, t), DC.fb(tl, t), LP2.band_r(SP.vbelow(e, t), SV.band(DC.fb.ds(ds, t), DC.fb(tl, t)), hb)),
        stats_ok(tl, es, fs, ctx, s, t, 1n+i, fdrop_tl(i, fs, DR.Fact{e, nd, ds}, tl, h),
          LP2.band_r(DC.fb.ds(ds, t), DC.fb(tl, t), LP2.band_r(SP.vbelow(e, t), SV.band(DC.fb.ds(ds, t), DC.fb(tl, t)), hb))))

def nstats_ok(n: DR.Node, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> IV.AllPD(es, fs, ctx, n, t, DC.pprems(DC.nstats(fs, n))):
  match n:
    case DR.NFrame{}:
      Unit{}
    case DR.NSeg{+s}:
      stats_ok(fs, es, fs, ctx, s, t, 0n, {==}, hb)

# Link turns
# ----------

def sv_move(+x: SK.VE, +w: DR.Lab, +es: List<&2, SK.Ent>, +a: DR.Node, +b: DR.Node, e: {b == a : DR.Node}, sv: VD.SameVD(x, DR.gmul(w, DR.zdir(es, b)))) -> VD.SameVD(x, DR.gmul(w, DR.zdir(es, a))):
  %e : VD.SameVD(x, DR.gmul(w, DR.zdir(es, _)))
  sv

# a link from c to a, turned at a: par(a, conj(w) z_c)
def turn_gen(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +a: DR.Node, +c: Nat, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der,
  +hz: {DC.zb(es, t) == True{} : Bool}, e: {b == a : DR.Node}, hl: LOkD(es, fs, ctx, t, DC.Link{c, b, wl, dl})) -> IV.PGenD(es, fs, ctx, a, t, DR.DTurn{dl, DR.Lab.conj(wl), a}):
  (v, r1) = hl
  (p, r2) = r1
  (ea, r3) = r2
  (sv, bx) = r3
  ((v, (p, samevd_tr(DR.Jd.x(DR.concl(es, fs, dl)), DR.gmul(wl, DR.zdir(es, a)), DR.gmul(DR.Lab.conj(DR.Lab.conj(wl)), DR.zdir(es, a)),
      sv_move(DR.Jd.x(DR.concl(es, fs, dl)), wl, es, a, b, e, sv), cc(wl, DR.zdir(es, a))))),
   ({==}, ({==}, BL.vb_gmul(DR.Lab.conj(wl), DR.zdir(es, DR.Jd.a(DR.concl(es, fs, dl))), t, BL.zdir_below(es, t, DR.Jd.a(DR.concl(es, fs, dl)), hz)))))

def llinks_ok.pick(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der,
  +hv: VD.VD(es, fs, ctx, d), +hp: VD.Isp(DR.concl(es, fs, d)), +ha: {DR.Jd.a(DR.concl(es, fs, d)) == r : DR.Node}, +hs: VD.SameVD(DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(w, DR.zdir(es, a))), +ho: VD.OpenD(es, ctx, a),
  +hz: {DC.zb(es, t) == True{} : Bool}, +c: Nat, +b: DR.Node, +wl: DR.Lab, +dl: DR.Der, ef: {f == DC.node_eq(b, a) : Bool}, hl: LOkD(es, fs, ctx, t, DC.Link{c, b, wl, dl}),
  +rest: List<&2, DR.Der>, ih: IV.AllPD(es, fs, ctx, r, t, rest)) -> IV.AllPD(es, fs, ctx, r, t, DC.dpick(f, DC.thr(d, w, a, DR.DTurn{dl, DR.Lab.conj(wl), a}), rest)):
  match f:
    case True{}:
      (thr_gen(es, fs, ctx, t, a, r, w, d, hv, hp, ha, hs, ho, DR.DTurn{dl, DR.Lab.conj(wl), a},
         turn_gen(es, fs, ctx, t, a, c, b, wl, dl, hz, node_eq_ok(b, a, Equal.sym(Bool, True{}, DC.node_eq(b, a), ef)), hl)), ih)
    case False{}:
      ih

def llinks_ok(ls: List<&2, DC.Link>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +a: DR.Node, +r: DR.Node, +w: DR.Lab, +d: DR.Der,
  +hv: VD.VD(es, fs, ctx, d), +hp: VD.Isp(DR.concl(es, fs, d)), +ha: {DR.Jd.a(DR.concl(es, fs, d)) == r : DR.Node}, +hs: VD.SameVD(DR.Jd.x(DR.concl(es, fs, d)), DR.gmul(w, DR.zdir(es, a))), +ho: VD.OpenD(es, ctx, a),
  +hz: {DC.zb(es, t) == True{} : Bool}, hls: LsOk(es, fs, ctx, t, ls)) -> IV.AllPD(es, fs, ctx, r, t, DC.llinks(ls, a, w, d)):
  match ls:
    case Nil{}:
      Unit{}
    case Con{DC.Link{+c, +b, +wl, +dl}, +tl}:
      (hl, rt) = hls
      llinks_ok.pick(DC.node_eq(b, a), es, fs, ctx, t, a, r, w, d, hv, hp, ha, hs, ho, hz, c, b, wl, dl, {==}, hl,
        DC.llinks(tl, a, w, d), llinks_ok(tl, es, fs, ctx, t, a, r, w, d, hv, hp, ha, hs, ho, hz, rt))

# Roots
# -----

def gen_self(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +r: DR.Node, +d: DR.Der,
  +hv: VD.VD(es, fs, ctx, d), +hp: VD.Isp(DR.concl(es, fs, d)), +ha: {DR.Jd.a(DR.concl(es, fs, d)) == r : DR.Node}, +hb: HP.VBelow(DR.Jd.x(DR.concl(es, fs, d)), t)) -> IV.PGenD(es, fs, ctx, r, t, d):
  (hv, (hp, (ha, hb)))

# a member's generators are right at its root
def mgens_ok(m: DC.Mem, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +ls: List<&2, DC.Link>,
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}, hm: MOkD(es, fs, ctx, t, m), +hls: LsOk(es, fs, ctx, t, ls)) -> IV.AllPD(es, fs, ctx, DC.Mem.r(m), t, DC.mgens(fs, ls, m)):
  match m:
    case DC.Mem{+a, +r, +w, +d}:
      (+hv, r1) = hm
      (+hp, r2) = r1
      (+ha, r3) = r2
      (+hs, r4) = r3
      (+ho, r5) = r4
      (hor, hbx) = r5
      (gen_self(es, fs, ctx, t, r, d, hv, hp, ha, hbx),
       IV.allpd_cat(es, fs, ctx, r, t, DC.lstats(DC.pprems(DC.nstats(fs, a)), a, w, d), DC.llinks(ls, a, w, d),
         lstats_ok(DC.pprems(DC.nstats(fs, a)), es, fs, ctx, t, a, r, w, d, hv, hp, ha, hs, ho, nstats_ok(a, es, fs, ctx, t, hb)),
         llinks_ok(ls, es, fs, ctx, t, a, r, w, d, hv, hp, ha, hs, ho, hz, hls)))

def ap_move(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +a: DR.Node, +r: DR.Node, +ds: List<&2, DR.Der>, e: {a == r : DR.Node}, h: IV.AllPD(es, fs, ctx, a, t, ds))
  -> IV.AllPD(es, fs, ctx, r, t, ds):
  %e : IV.AllPD(es, fs, ctx, _, t, ds)
  h

def rgens_ok.pick(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +r: DR.Node, +ls: List<&2, DC.Link>, +m: DC.Mem,
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}, hm: MOkD(es, fs, ctx, t, m), +hls: LsOk(es, fs, ctx, t, ls), ef: {f == DC.node_eq(DC.Mem.r(m), r) : Bool},
  +rest: List<&2, DR.Der>, ih: IV.AllPD(es, fs, ctx, r, t, rest)) -> IV.AllPD(es, fs, ctx, r, t, DC.dcatif(f, DC.mgens(fs, ls, m), rest)):
  match f:
    case True{}:
      IV.allpd_cat(es, fs, ctx, r, t, DC.mgens(fs, ls, m), rest,
        ap_move(es, fs, ctx, t, DC.Mem.r(m), r, DC.mgens(fs, ls, m), node_eq_ok(DC.Mem.r(m), r, Equal.sym(Bool, True{}, DC.node_eq(DC.Mem.r(m), r), ef)), mgens_ok(m, es, fs, ctx, t, ls, hz, hb, hm, hls)), ih)
    case False{}:
      ih

# a root's generators are right
def rgens_ok(ms: List<&2, DC.Mem>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +r: DR.Node, +ls: List<&2, DC.Link>,
  +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}, hms: MsOk(es, fs, ctx, t, ms), +hls: LsOk(es, fs, ctx, t, ls)) -> IV.AllPD(es, fs, ctx, r, t, DC.rgens(fs, r, ms, ls)):
  match ms:
    case Nil{}:
      Unit{}
    case Con{+m, +tl}:
      (hm, rt) = hms
      rgens_ok.pick(DC.node_eq(DC.Mem.r(m), r), es, fs, ctx, t, r, ls, m, hz, hb, hm, hls, {==}, DC.rgens(fs, r, tl, ls), rgens_ok(tl, es, fs, ctx, t, r, ls, hz, hb, rt, hls))

# K squared
# ---------

def kre_gen(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +r: DR.Node, +d: DR.Der, +hzr: HP.VBelow(DR.zdir(es, r), t), hk: IV.KGen(es, fs, ctx, t, d))
  -> IV.PGenD(es, fs, ctx, r, t, HS.kre(r, d)):
  (v, r1) = hk
  (k, b) = r1
  (((Unit{}, (Unit{}, ({==}, ({==}, {==})))), (v, (Unit{}, ({==}, (k, {==}))))), ({==}, ({==}, BL.vb_kre(DR.zdir(es, r), DR.Jd.e(DR.concl(es, fs, d)), t, hzr, b))))

def kim_gen(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +r: DR.Node, +d: DR.Der, +hzr: HP.VBelow(DR.zdir(es, r), t), hk: IV.KGen(es, fs, ctx, t, d))
  -> IV.PGenD(es, fs, ctx, r, t, HS.kim(r, d)):
  (v, r1) = hk
  (k, b) = r1
  (((Unit{}, (Unit{}, ({==}, ({==}, {==})))), (Unit{}, (v, ({==}, ({==}, k))))), ({==}, ({==}, BL.vb_kim(DR.zdir(es, r), DR.Jd.e(DR.concl(es, fs, d)), t, hzr, b))))

def kgens_ok(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +r: DR.Node, +hzr: HP.VBelow(DR.zdir(es, r), t), hk: IV.AllKD(es, fs, ctx, t, ds))
  -> IV.AllPD(es, fs, ctx, r, t, DC.kgens(r, ds)):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, tl}:
      (+g, rt) = hk
      (kre_gen(es, fs, ctx, t, r, d, hzr, g), (kim_gen(es, fs, ctx, t, r, d, hzr, g), kgens_ok(tl, es, fs, ctx, t, r, hzr, rt)))

def khull_inv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, k: KS.KS, +r: DR.Node, hk: IV.KInvD(es, fs, ctx, t, k), +hzr: HP.VBelow(DR.zdir(es, r), t))
  -> IV.HInvD(es, fs, ctx, r, t, DC.khull(es, fs, t, k, r)):
  match k:
    case KS.KS{+rows, +ds}:
      (hr, r1) = hk
      (hl, ha) = r1
      IV.hfold_inv(DC.kgens(r, ds), es, fs, ctx, r, t, HS.hs0(), IV.hs0_invd(es, fs, ctx, r, t), kgens_ok(ds, es, fs, ctx, t, r, hzr, ha))

# every rebuilt root hull keeps the invariant
def rhull_inv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +r: DR.Node,
  hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), hms: MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> IV.HInvD(es, fs, ctx, r, t, DC.rhull(es, fs, t, s, r)):
  IV.hfold_inv(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, ctx, r, t, DC.khull(es, fs, t, DC.Sk.k(s), r),
    khull_inv(es, fs, ctx, t, DC.Sk.k(s), r, hk, BL.zdir_below(es, t, r, hz)),
    rgens_ok(DC.Sk.ms(s), es, fs, ctx, t, r, DC.Sk.ls(s), hz, hb, hms, hls))
