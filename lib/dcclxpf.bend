# bend-cad: the closure's new K facts are right (PLAN-sk13b B3). Frame-back
# turns a generator of F into K(Im x) (fback_ok). The complex-line check
# (lib/dclose.bend's cl.go) inserts i g_j's encodings after a root hull's
# rows; at a zero residual, the elimination's multipliers split over the
# hull's generators and the inserted ones (lin_ecat), and since i and the
# encoding are linear (encim_clin), x = g_j - (the inserted ones'
# combination) has i x in the hull: the complex line's two premises are
# both derivable, so its K fact is a K generator (clxs_ok). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./q.bend as LQ
import ./qring.bend as QR
import ./qalg.bend as QA
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./drvpf.bend as DV
import ./cwpf.bend as CW
import ./listpf.bend as LP2
import ./seppf.bend as SP
import ./spanpf.bend as SN
import ./pair.bend as PT
import ./pairpf.bend as PP
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./hspacepf.bend as HP
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcinvpf.bend as IV
import ./dcbelowpf.bend as BL
import ./dcgenpf.bend as GN
import ./dcderpf.bend as DD
import ./dcmergepf.bend as MG

def absurd(-A: Type, x: Empty) -> A:
  match x:

def OptK(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, m: Maybe<&2, DR.Der>) -> Data:
  match m:
    case Some{d}:
      IV.KGen(es, fs, ctx, t, d)
    case None{}:
      Unit

# Frame-back
# ----------

def fback.pick(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +g: DR.Der, hg: IV.PGenD(es, fs, ctx, DR.NFrame{}, t, g), +rest: Maybe<&2, DR.Der>, hr: OptK(es, fs, ctx, t, rest))
  -> OptK(es, fs, ctx, t, DC.mpick2(b, DR.DBack{g}, rest)):
  match b:
    case True{}:
      (v, r1) = hg
      (p, r2) = r1
      (ea, bx) = r2
      (by, bz) = bx
      ((v, (p, ea)), ({==}, bz))
    case False{}:
      hr

# a generator of F with its imaginary part outside K gives a K generator
def fback_ok(gs: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +k: KS.KS, hg: IV.AllPD(es, fs, ctx, DR.NFrame{}, t, gs))
  -> OptK(es, fs, ctx, t, DC.fback(gs, es, fs, k)):
  match gs:
    case Nil{}:
      Unit{}
    case Con{+g, +tl}:
      (h0, rt) = hg
      fback.pick(SV.bnot(KS.ks.inb(k, SK.VE.y(DR.Jd.x(DR.concl(es, fs, g))))), es, fs, ctx, t, g, h0, DC.fback(tl, es, fs, k), fback_ok(tl, es, fs, ctx, t, k, rt))

# Lists and linearity
# -------------------

def ecat(xs: List<&2, E.QExpr>, ys: List<&2, E.QExpr>) -> List<&2, E.QExpr>:
  match xs:
    case Nil{}:
      ys
    case Con{x, tl}:
      Con{x, ecat(tl, ys)}

# i times each form, encoded
def imx(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, ds: List<&2, DR.Der>) -> List<&2, E.QExpr>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{d, tl}:
      Con{HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), imx(es, fs, t, tl)}

def imxs(xs: List<&2, SK.VE>, +t: Nat) -> List<&2, E.QExpr>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, tl}:
      Con{HS.enc(DR.imul(x), t), imxs(tl, t)}

def imx_xs(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, ds: List<&2, DR.Der>) -> {imx(es, fs, t, ds) == imxs(HS.hxs(es, fs, ds), t) : List<&2, E.QExpr>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +tl}:
      %Equal.sym(List<&2, E.QExpr>, imx(es, fs, t, tl), imxs(HS.hxs(es, fs, tl), t), imx_xs(es, fs, t, tl)) : {Con{HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), _} == imxs(HS.hxs(es, fs, Con{d, tl}), t) : List<&2, E.QExpr>}
      {==}

def ecat_nil(B: List<&2, E.QExpr>) -> {ecat(B, Nil{}) == B : List<&2, E.QExpr>}:
  match B:
    case Nil{}:
      {==}
    case Con{+b, +bt}:
      %Equal.sym(List<&2, E.QExpr>, ecat(bt, Nil{}), bt, ecat_nil(bt)) : {Con{b, _} == Con{b, bt} : List<&2, E.QExpr>}
      {==}

def ecat_snoc(B: List<&2, E.QExpr>, +I: List<&2, E.QExpr>, +e: E.QExpr) -> {ecat(B, EP.qsnoc(I, e)) == EP.qsnoc(ecat(B, I), e) : List<&2, E.QExpr>}:
  match B:
    case Nil{}:
      {==}
    case Con{+b, +bt}:
      %Equal.sym(List<&2, E.QExpr>, ecat(bt, EP.qsnoc(I, e)), EP.qsnoc(ecat(bt, I), e), ecat_snoc(bt, I, e)) : {Con{b, _} == Con{b, EP.qsnoc(ecat(bt, I), e)} : List<&2, E.QExpr>}
      {==}

def imx_snoc(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, ds: List<&2, DR.Der>, +d: DR.Der) -> {imx(es, fs, t, KS.dsnoc(ds, d)) == EP.qsnoc(imx(es, fs, t, ds), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)) : List<&2, E.QExpr>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+h0, +tl}:
      %Equal.sym(List<&2, E.QExpr>, imx(es, fs, t, KS.dsnoc(tl, d)), EP.qsnoc(imx(es, fs, t, tl), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), imx_snoc(es, fs, t, tl, d))
        : {Con{HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, h0))), t), _} == Con{HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, h0))), t), EP.qsnoc(imx(es, fs, t, tl), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))} : List<&2, E.QExpr>}
      {==}

def aassoc(+a: S.Q, +b: S.Q, +c: S.Q) -> S.Q.eq(S.Q.add(a, S.Q.add(b, c)), S.Q.add(S.Q.add(a, b), c)):
  QR.qring_eq([a, b, c], E.QAdd{E.QVar{0n}, E.QAdd{E.QVar{1n}, E.QVar{2n}}}, E.QAdd{E.QAdd{E.QVar{0n}, E.QVar{1n}}, E.QVar{2n}}, {==})

# a combination over B then I splits into B's part and I's
def lin_ecat.at(+p: List<&2, S.Q>, ls: List<&2, S.Q>, B: List<&2, E.QExpr>, +I: List<&2, E.QExpr>)
  -> S.Q.eq(E.qeval(p, SV.lin(ls, ecat(B, I))), S.Q.add(E.qeval(p, SV.lin(SN.ltrunc(ls, B), B)), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(B), ls), I)))):
  match ls B:
    case Con{+l, +lt} Con{+b, +bt}:
      LQ.q_trans(S.Q.add(S.Q.mul(l, E.qeval(p, b)), E.qeval(p, SV.lin(lt, ecat(bt, I)))),
        S.Q.add(S.Q.mul(l, E.qeval(p, b)), S.Q.add(E.qeval(p, SV.lin(SN.ltrunc(lt, bt), bt)), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(bt), lt), I)))),
        S.Q.add(S.Q.add(S.Q.mul(l, E.qeval(p, b)), E.qeval(p, SV.lin(SN.ltrunc(lt, bt), bt))), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(bt), lt), I))),
        LQ.q_add_cong_r(S.Q.mul(l, E.qeval(p, b)), E.qeval(p, SV.lin(lt, ecat(bt, I))), S.Q.add(E.qeval(p, SV.lin(SN.ltrunc(lt, bt), bt)), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(bt), lt), I))), lin_ecat.at(p, lt, bt, I)),
        aassoc(S.Q.mul(l, E.qeval(p, b)), E.qeval(p, SV.lin(SN.ltrunc(lt, bt), bt)), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(bt), lt), I))))
    case Nil{} B:
      %Equal.sym(List<&2, S.Q>, PT.qdrop(SV.neqs(B), Nil{}), Nil{}, PP.qdrop_nil(SV.neqs(B))) : S.Q.eq(E.qeval(p, SV.lin(Nil{}, ecat(B, I))), S.Q.add(E.qeval(p, SV.lin(Nil{}, B)), E.qeval(p, SV.lin(_, I))))
      QR.qring_eq(Nil{}, E.QCst{DR.qz()}, E.QAdd{E.QCst{DR.qz()}, E.QCst{DR.qz()}}, {==})
    case Con{+l, +lt} Nil{}:
      QR.qring_eq([E.qeval(p, SV.lin(Con{l, lt}, I))], E.QVar{0n}, E.QAdd{E.QCst{DR.qz()}, E.QVar{0n}}, {==})

# i times a combination, encoded, is the combination of the encodings of i x_1, i x_2
def encim(+m1: S.Q, +m2: S.Q, +x1: S.Q, +y1: S.Q, +x2: S.Q, +y2: S.Q, +tt: S.Q) -> S.Q.eq(S.Q.add(S.Q.neg(S.Q.add(S.Q.mul(m1, y1), S.Q.mul(m2, y2))), S.Q.mul(tt, S.Q.add(S.Q.mul(m1, x1), S.Q.mul(m2, x2)))), S.Q.add(S.Q.mul(m1, S.Q.add(S.Q.neg(y1), S.Q.mul(tt, x1))), S.Q.mul(m2, S.Q.add(S.Q.neg(y2), S.Q.mul(tt, x2))))):
  QA.ch4(S.Q.add(S.Q.neg(S.Q.add(S.Q.mul(m1, y1), S.Q.mul(m2, y2))), S.Q.mul(tt, S.Q.add(S.Q.mul(m1, x1), S.Q.mul(m2, x2)))), S.Q.add(S.Q.add(S.Q.neg(S.Q.mul(m1, y1)), S.Q.neg(S.Q.mul(m2, y2))), S.Q.add(S.Q.mul(tt, S.Q.mul(m1, x1)), S.Q.mul(tt, S.Q.mul(m2, x2)))), S.Q.add(S.Q.add(S.Q.neg(S.Q.mul(m1, y1)), S.Q.mul(tt, S.Q.mul(m1, x1))), S.Q.add(S.Q.neg(S.Q.mul(m2, y2)), S.Q.mul(tt, S.Q.mul(m2, x2)))), S.Q.add(S.Q.add(S.Q.mul(m1, S.Q.neg(y1)), S.Q.mul(m1, S.Q.mul(tt, x1))), S.Q.add(S.Q.mul(m2, S.Q.neg(y2)), S.Q.mul(m2, S.Q.mul(tt, x2)))), S.Q.add(S.Q.mul(m1, S.Q.add(S.Q.neg(y1), S.Q.mul(tt, x1))), S.Q.mul(m2, S.Q.add(S.Q.neg(y2), S.Q.mul(tt, x2)))),
    QA.add_cong(S.Q.neg(S.Q.add(S.Q.mul(m1, y1), S.Q.mul(m2, y2))), S.Q.add(S.Q.neg(S.Q.mul(m1, y1)), S.Q.neg(S.Q.mul(m2, y2))), S.Q.mul(tt, S.Q.add(S.Q.mul(m1, x1), S.Q.mul(m2, x2))), S.Q.add(S.Q.mul(tt, S.Q.mul(m1, x1)), S.Q.mul(tt, S.Q.mul(m2, x2))), QA.negadd(S.Q.mul(m1, y1), S.Q.mul(m2, y2)), QA.ldist(tt, S.Q.mul(m1, x1), S.Q.mul(m2, x2))),
    QA.m4(S.Q.neg(S.Q.mul(m1, y1)), S.Q.neg(S.Q.mul(m2, y2)), S.Q.mul(tt, S.Q.mul(m1, x1)), S.Q.mul(tt, S.Q.mul(m2, x2))),
    QA.add_cong(S.Q.add(S.Q.neg(S.Q.mul(m1, y1)), S.Q.mul(tt, S.Q.mul(m1, x1))), S.Q.add(S.Q.mul(m1, S.Q.neg(y1)), S.Q.mul(m1, S.Q.mul(tt, x1))), S.Q.add(S.Q.neg(S.Q.mul(m2, y2)), S.Q.mul(tt, S.Q.mul(m2, x2))), S.Q.add(S.Q.mul(m2, S.Q.neg(y2)), S.Q.mul(m2, S.Q.mul(tt, x2))), QA.add_cong(S.Q.neg(S.Q.mul(m1, y1)), S.Q.mul(m1, S.Q.neg(y1)), S.Q.mul(tt, S.Q.mul(m1, x1)), S.Q.mul(m1, S.Q.mul(tt, x1)), LQ.q_sym(S.Q.mul(m1, S.Q.neg(y1)), S.Q.neg(S.Q.mul(m1, y1)), QA.mneg(m1, y1)), QA.mswap(tt, m1, x1)), QA.add_cong(S.Q.neg(S.Q.mul(m2, y2)), S.Q.mul(m2, S.Q.neg(y2)), S.Q.mul(tt, S.Q.mul(m2, x2)), S.Q.mul(m2, S.Q.mul(tt, x2)), LQ.q_sym(S.Q.mul(m2, S.Q.neg(y2)), S.Q.neg(S.Q.mul(m2, y2)), QA.mneg(m2, y2)), QA.mswap(tt, m2, x2))),
    QA.add_cong(S.Q.add(S.Q.mul(m1, S.Q.neg(y1)), S.Q.mul(m1, S.Q.mul(tt, x1))), S.Q.mul(m1, S.Q.add(S.Q.neg(y1), S.Q.mul(tt, x1))), S.Q.add(S.Q.mul(m2, S.Q.neg(y2)), S.Q.mul(m2, S.Q.mul(tt, x2))), S.Q.mul(m2, S.Q.add(S.Q.neg(y2), S.Q.mul(tt, x2))), LQ.q_sym(S.Q.mul(m1, S.Q.add(S.Q.neg(y1), S.Q.mul(tt, x1))), S.Q.add(S.Q.mul(m1, S.Q.neg(y1)), S.Q.mul(m1, S.Q.mul(tt, x1))), QA.ldist(m1, S.Q.neg(y1), S.Q.mul(tt, x1))), LQ.q_sym(S.Q.mul(m2, S.Q.add(S.Q.neg(y2), S.Q.mul(tt, x2))), S.Q.add(S.Q.mul(m2, S.Q.neg(y2)), S.Q.mul(m2, S.Q.mul(tt, x2))), QA.ldist(m2, S.Q.neg(y2), S.Q.mul(tt, x2)))))

def encim_vlin.at(+p: List<&2, S.Q>, +m1: S.Q, +x1: SK.VE, +m2: S.Q, +x2: SK.VE, +t: Nat)
  -> S.Q.eq(E.qeval(p, HS.enc(DR.imul(DR.vlin(m1, x1, m2, x2)), t)), E.qeval(p, E.QAdd{E.QMul{E.QCst{m1}, HS.enc(DR.imul(x1), t)}, E.QMul{E.QCst{m2}, HS.enc(DR.imul(x2), t)}})):
  encim(m1, m2, E.qeval(p, SK.VE.x(x1)), E.qeval(p, SK.VE.y(x1)), E.qeval(p, SK.VE.x(x2)), E.qeval(p, SK.VE.y(x2)), E.qlookup(p, t))

def encim_clin.base(+p: List<&2, S.Q>, +z: SK.VE, +t: Nat) -> S.Q.eq(E.qeval(p, HS.enc(DR.imul(DR.vlin(DR.qz(), z, DR.qz(), z)), t)), DR.qz()):
  LQ.q_trans(E.qeval(p, HS.enc(DR.imul(DR.vlin(DR.qz(), z, DR.qz(), z)), t)), S.Q.add(S.Q.mul(DR.qz(), E.qeval(p, HS.enc(DR.imul(z), t))), S.Q.mul(DR.qz(), E.qeval(p, HS.enc(DR.imul(z), t)))), DR.qz(),
    encim_vlin.at(p, DR.qz(), z, DR.qz(), z, t),
    QR.qring_eq([E.qeval(p, HS.enc(DR.imul(z), t))], E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}}, E.QCst{DR.qz()}, {==}))

# i times a combination of forms, encoded, is the combination of their
# i times, encoded
def encim_clin.at(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +r: DR.Node, ls: List<&2, S.Q>, xs: List<&2, SK.VE>, +t: Nat)
  -> S.Q.eq(E.qeval(p, HS.enc(DR.imul(HS.clin(es, r, ls, xs)), t)), E.qeval(p, SV.lin(ls, imxs(xs, t)))):
  match ls xs:
    case Con{+l, +lt} Con{+x, +xt}:
      QA.ch3(E.qeval(p, HS.enc(DR.imul(HS.clin(es, r, Con{l, lt}, Con{x, xt})), t)),
        S.Q.add(S.Q.mul(l, E.qeval(p, HS.enc(DR.imul(x), t))), S.Q.mul(DR.qo(), E.qeval(p, HS.enc(DR.imul(HS.clin(es, r, lt, xt)), t)))),
        S.Q.add(S.Q.mul(l, E.qeval(p, HS.enc(DR.imul(x), t))), E.qeval(p, HS.enc(DR.imul(HS.clin(es, r, lt, xt)), t))),
        S.Q.add(S.Q.mul(l, E.qeval(p, HS.enc(DR.imul(x), t))), E.qeval(p, SV.lin(lt, imxs(xt, t)))),
        encim_vlin.at(p, l, x, DR.qo(), HS.clin(es, r, lt, xt), t),
        LQ.q_add_cong_r(S.Q.mul(l, E.qeval(p, HS.enc(DR.imul(x), t))), S.Q.mul(DR.qo(), E.qeval(p, HS.enc(DR.imul(HS.clin(es, r, lt, xt)), t))), E.qeval(p, HS.enc(DR.imul(HS.clin(es, r, lt, xt)), t)), QA.one_mul(E.qeval(p, HS.enc(DR.imul(HS.clin(es, r, lt, xt)), t)))),
        LQ.q_add_cong_r(S.Q.mul(l, E.qeval(p, HS.enc(DR.imul(x), t))), E.qeval(p, HS.enc(DR.imul(HS.clin(es, r, lt, xt)), t)), E.qeval(p, SV.lin(lt, imxs(xt, t))), encim_clin.at(p, es, r, lt, xt, t)))
    case Nil{} xs:
      encim_clin.base(p, DR.zdir(es, r), t)
    case Con{+l, +lt} Nil{}:
      encim_clin.base(p, DR.zdir(es, r), t)

# The complex line's relation
# ---------------------------

def rel_move(+ed: E.QExpr, +ls2: List<&2, S.Q>, +bb: List<&2, E.QExpr>, +B: List<&2, E.QExpr>, +I: List<&2, E.QExpr>, ebb: {bb == ecat(B, I) : List<&2, E.QExpr>}, h: SV.Ident(ed, SV.lin(ls2, bb)))
  -> SV.Ident(ed, SV.lin(ls2, ecat(B, I))):
  %ebb : SV.Ident(ed, SV.lin(ls2, _))
  h

def imx_move(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +p: List<&2, S.Q>, +ls: List<&2, S.Q>, +prev: List<&2, DR.Der>)
  -> S.Q.eq(E.qeval(p, SV.lin(ls, imx(es, fs, t, prev))), E.qeval(p, SV.lin(ls, imxs(HS.hxs(es, fs, prev), t)))):
  %Equal.sym(List<&2, E.QExpr>, imx(es, fs, t, prev), imxs(HS.hxs(es, fs, prev), t), imx_xs(es, fs, t, prev)) : S.Q.eq(E.qeval(p, SV.lin(ls, _)), E.qeval(p, SV.lin(ls, imxs(HS.hxs(es, fs, prev), t))))
  LQ.q_refl(E.qeval(p, SV.lin(ls, imxs(HS.hxs(es, fs, prev), t))))

# with e's multipliers ls2 over B then i times prev's forms, x = g - (the
# second part's combination) has enc(i x) = the first part's combination
def cl.rel.at(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +r: DR.Node, +d: DR.Der, +prev: List<&2, DR.Der>, +B: List<&2, E.QExpr>, +ls2: List<&2, S.Q>,
  hid: SV.Ident(HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), SV.lin(ls2, ecat(B, imx(es, fs, t, prev)))))
  -> S.Q.eq(E.qeval(p, HS.enc(DR.imul(DR.vlin(DR.qo(), DR.Jd.x(DR.concl(es, fs, d)), S.Q.neg(DR.qo()), HS.clin(es, r, PT.qdrop(SV.neqs(B), ls2), HS.hxs(es, fs, prev)))), t)), E.qeval(p, SV.lin(SN.ltrunc(ls2, B), B))):
  QA.ch4(E.qeval(p, HS.enc(DR.imul(DR.vlin(DR.qo(), DR.Jd.x(DR.concl(es, fs, d)), S.Q.neg(DR.qo()), HS.clin(es, r, PT.qdrop(SV.neqs(B), ls2), HS.hxs(es, fs, prev)))), t)),
    S.Q.add(S.Q.mul(DR.qo(), E.qeval(p, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), S.Q.mul(S.Q.neg(DR.qo()), E.qeval(p, HS.enc(DR.imul(HS.clin(es, r, PT.qdrop(SV.neqs(B), ls2), HS.hxs(es, fs, prev))), t)))),
    S.Q.add(S.Q.mul(DR.qo(), S.Q.add(E.qeval(p, SV.lin(SN.ltrunc(ls2, B), B)), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(B), ls2), imx(es, fs, t, prev))))), S.Q.mul(S.Q.neg(DR.qo()), E.qeval(p, HS.enc(DR.imul(HS.clin(es, r, PT.qdrop(SV.neqs(B), ls2), HS.hxs(es, fs, prev))), t)))),
    S.Q.add(S.Q.mul(DR.qo(), S.Q.add(E.qeval(p, SV.lin(SN.ltrunc(ls2, B), B)), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(B), ls2), imxs(HS.hxs(es, fs, prev), t))))), S.Q.mul(S.Q.neg(DR.qo()), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(B), ls2), imxs(HS.hxs(es, fs, prev), t))))),
    E.qeval(p, SV.lin(SN.ltrunc(ls2, B), B)),
    encim_vlin.at(p, DR.qo(), DR.Jd.x(DR.concl(es, fs, d)), S.Q.neg(DR.qo()), HS.clin(es, r, PT.qdrop(SV.neqs(B), ls2), HS.hxs(es, fs, prev)), t),
    LQ.q_add_cong_l(S.Q.mul(DR.qo(), E.qeval(p, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), S.Q.mul(DR.qo(), S.Q.add(E.qeval(p, SV.lin(SN.ltrunc(ls2, B), B)), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(B), ls2), imx(es, fs, t, prev))))),
      S.Q.mul(S.Q.neg(DR.qo()), E.qeval(p, HS.enc(DR.imul(HS.clin(es, r, PT.qdrop(SV.neqs(B), ls2), HS.hxs(es, fs, prev))), t))),
      LQ.q_mul_cong_r(DR.qo(), E.qeval(p, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), S.Q.add(E.qeval(p, SV.lin(SN.ltrunc(ls2, B), B)), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(B), ls2), imx(es, fs, t, prev)))),
        LQ.q_trans(E.qeval(p, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), E.qeval(p, SV.lin(ls2, ecat(B, imx(es, fs, t, prev)))), S.Q.add(E.qeval(p, SV.lin(SN.ltrunc(ls2, B), B)), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(B), ls2), imx(es, fs, t, prev)))),
          hid(p), lin_ecat.at(p, ls2, B, imx(es, fs, t, prev))))),
    QA.add_cong(S.Q.mul(DR.qo(), S.Q.add(E.qeval(p, SV.lin(SN.ltrunc(ls2, B), B)), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(B), ls2), imx(es, fs, t, prev))))),
      S.Q.mul(DR.qo(), S.Q.add(E.qeval(p, SV.lin(SN.ltrunc(ls2, B), B)), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(B), ls2), imxs(HS.hxs(es, fs, prev), t))))),
      S.Q.mul(S.Q.neg(DR.qo()), E.qeval(p, HS.enc(DR.imul(HS.clin(es, r, PT.qdrop(SV.neqs(B), ls2), HS.hxs(es, fs, prev))), t))),
      S.Q.mul(S.Q.neg(DR.qo()), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(B), ls2), imxs(HS.hxs(es, fs, prev), t)))),
      LQ.q_mul_cong_r(DR.qo(), S.Q.add(E.qeval(p, SV.lin(SN.ltrunc(ls2, B), B)), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(B), ls2), imx(es, fs, t, prev)))), S.Q.add(E.qeval(p, SV.lin(SN.ltrunc(ls2, B), B)), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(B), ls2), imxs(HS.hxs(es, fs, prev), t)))),
        LQ.q_add_cong_r(E.qeval(p, SV.lin(SN.ltrunc(ls2, B), B)), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(B), ls2), imx(es, fs, t, prev))), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(B), ls2), imxs(HS.hxs(es, fs, prev), t))), imx_move(es, fs, t, p, PT.qdrop(SV.neqs(B), ls2), prev))),
      LQ.q_mul_cong_r(S.Q.neg(DR.qo()), E.qeval(p, HS.enc(DR.imul(HS.clin(es, r, PT.qdrop(SV.neqs(B), ls2), HS.hxs(es, fs, prev))), t)), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(B), ls2), imxs(HS.hxs(es, fs, prev), t))), encim_clin.at(p, es, r, PT.qdrop(SV.neqs(B), ls2), HS.hxs(es, fs, prev), t))),
    QR.qring_eq([E.qeval(p, SV.lin(SN.ltrunc(ls2, B), B)), E.qeval(p, SV.lin(PT.qdrop(SV.neqs(B), ls2), imxs(HS.hxs(es, fs, prev), t)))],
      E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QAdd{E.QVar{0n}, E.QVar{1n}}}, E.QMul{E.QCst{S.Q.neg(DR.qo())}, E.QVar{1n}}}, E.QVar{0n}, {==}))

# The complex line's K fact
# -------------------------

def cl.rel.px(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +r: DR.Node, +d: DR.Der, +prev: List<&2, DR.Der>, +B: List<&2, E.QExpr>, +ls2: List<&2, S.Q>,
  hid: SV.Ident(HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), SV.lin(ls2, ecat(B, imx(es, fs, t, prev)))))
  -> S.Q.eq(E.qeval(p, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, DR.DPLin{DR.qo(), d, S.Q.neg(DR.qo()), HS.pchain(r, PT.qdrop(SV.neqs(B), ls2), prev)}))), t)), E.qeval(p, SV.lin(SN.ltrunc(ls2, B), B))):
  %Equal.sym(SK.VE, DR.Jd.x(DR.concl(es, fs, HS.pchain(r, PT.qdrop(SV.neqs(B), ls2), prev))), HS.clin(es, r, PT.qdrop(SV.neqs(B), ls2), HS.hxs(es, fs, prev)), HP.pchain_x(es, fs, r, PT.qdrop(SV.neqs(B), ls2), prev))
    : S.Q.eq(E.qeval(p, HS.enc(DR.imul(DR.vlin(DR.qo(), DR.Jd.x(DR.concl(es, fs, d)), S.Q.neg(DR.qo()), _)), t)), E.qeval(p, SV.lin(SN.ltrunc(ls2, B), B)))
  cl.rel.at(p, es, fs, t, r, d, prev, B, ls2, hid)

def open_move(+es: List<&2, SK.Ent>, +ctx: List<&2, E.QExpr>, +a: DR.Node, +r: DR.Node, e: {a == r : DR.Node}, h: VD.OpenD(es, ctx, r)) -> VD.OpenD(es, ctx, a):
  %Equal.sym(DR.Node, a, r, e) : VD.OpenD(es, ctx, _)
  h

def dline_below(re: Bool, +x: SK.VE, +t: Nat, +bx: {SP.vbelow(SK.VE.x(x), t) == True{} : Bool}, +by: {SP.vbelow(SK.VE.y(x), t) == True{} : Bool}) -> {SP.vbelow(DR.dline.e(re, x), t) == True{} : Bool}:
  match re:
    case True{}:
      bx
    case False{}:
      by

def dline_kgen(re: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +r: DR.Node, +px: DR.Der, +d2: DR.Der,
  +vp: VD.VD(es, fs, ctx, px), +pp: VD.Isp(DR.concl(es, fs, px)), +ap: {DR.Jd.a(DR.concl(es, fs, px)) == r : DR.Node}, +bp: HP.VBelow(DR.Jd.x(DR.concl(es, fs, px)), t),
  +v2: VD.VD(es, fs, ctx, d2), +p2: VD.Isp(DR.concl(es, fs, d2)), +a2: {DR.Jd.a(DR.concl(es, fs, d2)) == r : DR.Node}, +s2: VD.SameVD(DR.Jd.x(DR.concl(es, fs, d2)), DR.imul(DR.Jd.x(DR.concl(es, fs, px)))),
  +orr: VD.OpenD(es, ctx, r)) -> IV.KGen(es, fs, ctx, t, DR.DLine{px, d2, re}):
  (bx, by) = bp
  ((vp, (v2, (pp, (p2, (Equal.trans(DR.Node, DR.Jd.a(DR.concl(es, fs, px)), r, DR.Jd.a(DR.concl(es, fs, d2)), ap, Equal.sym(DR.Node, DR.Jd.a(DR.concl(es, fs, d2)), r, a2)),
     (open_move(es, ctx, DR.Jd.a(DR.concl(es, fs, px)), r, ap, orr), s2)))))), ({==}, dline_below(re, DR.Jd.x(DR.concl(es, fs, px)), t, bx, by)))


# x = g - (the inserted ones' combination), as a derivation: VD, at r, below t
def cl.px(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +r: DR.Node, +d: DR.Der, +lsI: List<&2, S.Q>, +prev: List<&2, DR.Der>, +hz: {DC.zb(es, t) == True{} : Bool},
  hd: IV.PGenD(es, fs, ctx, r, t, d), +hp: IV.AllPD(es, fs, ctx, r, t, prev),
  pk: SK.Both(VD.VD(es, fs, ctx, HS.pchain(r, lsI, prev)), SK.Both(VD.Isp(DR.concl(es, fs, HS.pchain(r, lsI, prev))), {DR.Jd.a(DR.concl(es, fs, HS.pchain(r, lsI, prev))) == r : DR.Node})))
  -> SK.Both(SK.Both(VD.VD(es, fs, ctx, DR.DPLin{DR.qo(), d, S.Q.neg(DR.qo()), HS.pchain(r, lsI, prev)}), SK.Both(VD.Isp(DR.concl(es, fs, DR.DPLin{DR.qo(), d, S.Q.neg(DR.qo()), HS.pchain(r, lsI, prev)})), {DR.Jd.a(DR.concl(es, fs, DR.DPLin{DR.qo(), d, S.Q.neg(DR.qo()), HS.pchain(r, lsI, prev)})) == r : DR.Node})),
       HP.VBelow(DR.Jd.x(DR.concl(es, fs, DR.DPLin{DR.qo(), d, S.Q.neg(DR.qo()), HS.pchain(r, lsI, prev)})), t)):
  (vd, r1) = hd
  (pd, r2) = r1
  (+ad, bd) = r2
  (vpc, s1) = pk
  (ppc, apc) = s1
  (((vd, (vpc, (pd, (ppc, Equal.trans(DR.Node, DR.Jd.a(DR.concl(es, fs, d)), r, DR.Jd.a(DR.concl(es, fs, HS.pchain(r, lsI, prev))), ad, Equal.sym(DR.Node, DR.Jd.a(DR.concl(es, fs, HS.pchain(r, lsI, prev))), r, apc)))))), ({==}, ad)),
   HP.vlin_below(DR.qo(), DR.Jd.x(DR.concl(es, fs, d)), S.Q.neg(DR.qo()), DR.Jd.x(DR.concl(es, fs, HS.pchain(r, lsI, prev))), t, bd,
     DD.hs_der.below(es, fs, r, t, lsI, prev, HP.clin_below(es, r, t, lsI, HS.hxs(es, fs, prev), DD.allpd_below(prev, es, fs, ctx, r, t, hp), BL.zdir_below(es, t, r, hz)))))

def cl.fin(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +r: DR.Node, +px: DR.Der, +d2: DR.Der, +orr: VD.OpenD(es, ctx, r),
  pxk: SK.Both(SK.Both(VD.VD(es, fs, ctx, px), SK.Both(VD.Isp(DR.concl(es, fs, px)), {DR.Jd.a(DR.concl(es, fs, px)) == r : DR.Node})), HP.VBelow(DR.Jd.x(DR.concl(es, fs, px)), t)),
  dk: SK.Both(SK.Both(SK.Both(VD.VD(es, fs, ctx, d2), SK.Both(VD.Isp(DR.concl(es, fs, d2)), {DR.Jd.a(DR.concl(es, fs, d2)) == r : DR.Node})), HP.VBelow(DR.Jd.x(DR.concl(es, fs, d2)), t)), VD.SameVD(DR.Jd.x(DR.concl(es, fs, d2)), DR.imul(DR.Jd.x(DR.concl(es, fs, px))))))
  -> IV.KGen(es, fs, ctx, t, DC.cl.k(b, px, d2)):
  match b:
    case True{}:
      (vpa, bp) = pxk
      (vp, q1) = vpa
      (pp, ap) = q1
      (vb3, s2) = dk
      (vpa2, b2) = vb3
      (v2, r1) = vpa2
      (p2, a2) = r1
      dline_kgen(False{}, es, fs, ctx, t, r, px, d2, vp, pp, ap, bp, v2, p2, a2, s2, orr)
    case False{}:
      (vpa, bp) = pxk
      (vp, q1) = vpa
      (pp, ap) = q1
      (vb3, s2) = dk
      (vpa2, b2) = vb3
      (v2, r1) = vpa2
      (p2, a2) = r1
      dline_kgen(True{}, es, fs, ctx, t, r, px, d2, vp, pp, ap, bp, v2, p2, a2, s2, orr)

def cl.fin2(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +r: DR.Node, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +k: KS.KS, +px: DR.Der,
  +hrv: {EP.rinv(HS.encs(HS.hxs(es, fs, ds), t), rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(HS.encs(HS.hxs(es, fs, ds), t)) : Nat}, +ha: IV.AllPD(es, fs, ctx, r, t, ds),
  +orr: VD.OpenD(es, ctx, r), +hz: {DC.zb(es, t) == True{} : Bool}, inb: {HS.hs.inb(HS.HS{rows, ds}, DR.imul(DR.Jd.x(DR.concl(es, fs, px))), t) == True{} : Bool},
  +pxk: SK.Both(SK.Both(VD.VD(es, fs, ctx, px), SK.Both(VD.Isp(DR.concl(es, fs, px)), {DR.Jd.a(DR.concl(es, fs, px)) == r : DR.Node})), HP.VBelow(DR.Jd.x(DR.concl(es, fs, px)), t)))
  -> IV.KGen(es, fs, ctx, t, DC.cl.k(KS.ks.inb(k, SK.VE.x(DR.Jd.x(DR.concl(es, fs, px)))), px, HS.hs.der(es, fs, t, r, HS.HS{rows, ds}, DR.imul(DR.Jd.x(DR.concl(es, fs, px)))))):
  (vpa, bp) = pxk
  cl.fin(KS.ks.inb(k, SK.VE.x(DR.Jd.x(DR.concl(es, fs, px)))), es, fs, ctx, t, r, px, HS.hs.der(es, fs, t, r, HS.HS{rows, ds}, DR.imul(DR.Jd.x(DR.concl(es, fs, px)))), orr, pxk,
    DD.hs_der_okd(es, fs, ctx, r, t, HS.HS{rows, ds}, DR.imul(DR.Jd.x(DR.concl(es, fs, px))), (hrv, (hl, ha)), inb, BL.vb_imul(DR.Jd.x(DR.concl(es, fs, px)), t, bp), BL.zdir_below(es, t, r, hz)))

# at a zero residual, the complex line's K fact is a K generator
def cl.found_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +r: DR.Node, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +k: KS.KS,
  +d: DR.Der, +rows2: List<&2, EL.Row>, +bb: List<&2, E.QExpr>, +prev: List<&2, DR.Der>,
  +hrv: {EP.rinv(HS.encs(HS.hxs(es, fs, ds), t), rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(HS.encs(HS.hxs(es, fs, ds), t)) : Nat}, +ha: IV.AllPD(es, fs, ctx, r, t, ds),
  +orr: VD.OpenD(es, ctx, r), +hz: {DC.zb(es, t) == True{} : Bool}, +hd: IV.PGenD(es, fs, ctx, r, t, d), +hp: IV.AllPD(es, fs, ctx, r, t, prev),
  +ebb: {bb == ecat(HS.encs(HS.hxs(es, fs, ds), t), imx(es, fs, t, prev)) : List<&2, E.QExpr>}, +hr2: {EP.rinv(bb, rows2, 0n) == True{} : Bool},
  hnil: {EP.isnil(EP.resp(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)))) == True{} : Bool})
  -> IV.KGen(es, fs, ctx, t, DC.cl.found(es, fs, t, r, HS.HS{rows, ds}, k, d, EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), bb, prev)):
  cl.fin2(es, fs, ctx, t, r, rows, ds, k,
    DR.DPLin{DR.qo(), d, S.Q.neg(DR.qo()), HS.pchain(r, PT.qdrop(SV.neqs(HS.encs(HS.hxs(es, fs, ds), t)), DV.dropls(DV.rescb(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), DV.resbt(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), bb)), prev)},
    hrv, hl, ha, orr, hz,
    SN.zero_of_in(HS.encs(HS.hxs(es, fs, ds), t), rows,
      HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, DR.DPLin{DR.qo(), d, S.Q.neg(DR.qo()), HS.pchain(r, PT.qdrop(SV.neqs(HS.encs(HS.hxs(es, fs, ds), t)), DV.dropls(DV.rescb(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), DV.resbt(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), bb)), prev)}))), t),
      hrv, hl,
      SN.in_of_ident(HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, DR.DPLin{DR.qo(), d, S.Q.neg(DR.qo()), HS.pchain(r, PT.qdrop(SV.neqs(HS.encs(HS.hxs(es, fs, ds), t)), DV.dropls(DV.rescb(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), DV.resbt(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), bb)), prev)}))), t),
        HS.encs(HS.hxs(es, fs, ds), t),
        SN.ltrunc(DV.dropls(DV.rescb(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), DV.resbt(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), bb), HS.encs(HS.hxs(es, fs, ds), t)),
        p => cl.rel.px(p, es, fs, t, r, d, prev, HS.encs(HS.hxs(es, fs, ds), t),
          DV.dropls(DV.rescb(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), DV.resbt(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), bb),
          rel_move(HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), DV.dropls(DV.rescb(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), DV.resbt(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), bb),
            bb, HS.encs(HS.hxs(es, fs, ds), t), imx(es, fs, t, prev), ebb, DV.derivable(bb, rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), hr2, hnil))))),
    cl.px(es, fs, ctx, t, r, d, PT.qdrop(SV.neqs(HS.encs(HS.hxs(es, fs, ds), t)), DV.dropls(DV.rescb(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), DV.resbt(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), bb)), prev, hz, hd, hp,
      DD.pchain_okd(PT.qdrop(SV.neqs(HS.encs(HS.hxs(es, fs, ds), t)), DV.dropls(DV.rescb(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), DV.resbt(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), bb)), prev, es, fs, ctx, r, t, hp)))

# The walk
# --------

def ebb_step(+B: List<&2, E.QExpr>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +prev: List<&2, DR.Der>, +d: DR.Der, +bb: List<&2, E.QExpr>, ebb: {bb == ecat(B, imx(es, fs, t, prev)) : List<&2, E.QExpr>})
  -> {EP.qsnoc(bb, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)) == ecat(B, imx(es, fs, t, KS.dsnoc(prev, d))) : List<&2, E.QExpr>}:
  %Equal.sym(List<&2, E.QExpr>, bb, ecat(B, imx(es, fs, t, prev)), ebb) : {EP.qsnoc(_, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)) == ecat(B, imx(es, fs, t, KS.dsnoc(prev, d))) : List<&2, E.QExpr>}
  %Equal.sym(List<&2, E.QExpr>, imx(es, fs, t, KS.dsnoc(prev, d)), EP.qsnoc(imx(es, fs, t, prev), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), imx_snoc(es, fs, t, prev, d))
    : {EP.qsnoc(ecat(B, imx(es, fs, t, prev)), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)) == ecat(B, _) : List<&2, E.QExpr>}
  Equal.sym(List<&2, E.QExpr>, ecat(B, EP.qsnoc(imx(es, fs, t, prev), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), EP.qsnoc(ecat(B, imx(es, fs, t, prev)), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)),
    ecat_snoc(B, imx(es, fs, t, prev), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)))

def cl.go_pick(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +rows2: List<&2, EL.Row>, +ex: E.QExpr, +found: DR.Der, +rest: Maybe<&2, DR.Der>,
  eb: {b == EP.isnil(EP.resp(EL.resid(rows2, ex))) : Bool}, fk: {EP.isnil(EP.resp(EL.resid(rows2, ex))) == True{} : Bool} -> IV.KGen(es, fs, ctx, t, found),
  ik: {EP.isnil(EP.resp(EL.resid(rows2, ex))) == False{} : Bool} -> OptK(es, fs, ctx, t, rest)) -> OptK(es, fs, ctx, t, DC.cl.pick(b, found, rest)):
  match b:
    case True{}:
      fk(Equal.sym(Bool, True{}, EP.isnil(EP.resp(EL.resid(rows2, ex))), eb))
    case False{}:
      ik(Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows2, ex))), eb))

# the walk over the kept non-K generators finds only K generators
def cl.go_ok(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +r: DR.Node, +rows: List<&2, EL.Row>, +hds0: List<&2, DR.Der>, +k: KS.KS,
  +rows2: List<&2, EL.Row>, +bb: List<&2, E.QExpr>, +prev: List<&2, DR.Der>,
  +hrv: {EP.rinv(HS.encs(HS.hxs(es, fs, hds0), t), rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(HS.encs(HS.hxs(es, fs, hds0), t)) : Nat}, +ha: IV.AllPD(es, fs, ctx, r, t, hds0),
  +orr: VD.OpenD(es, ctx, r), +hz: {DC.zb(es, t) == True{} : Bool}, +hp: IV.AllPD(es, fs, ctx, r, t, prev),
  +ebb: {bb == ecat(HS.encs(HS.hxs(es, fs, hds0), t), imx(es, fs, t, prev)) : List<&2, E.QExpr>}, +hr2: {EP.rinv(bb, rows2, 0n) == True{} : Bool}, +hl2: {EL.rlen(rows2) == SV.neqs(bb) : Nat},
  hds: IV.AllPD(es, fs, ctx, r, t, ds)) -> OptK(es, fs, ctx, t, DC.cl.go(ds, es, fs, t, r, HS.HS{rows, hds0}, k, rows2, bb, prev)):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, +tl}:
      (+g, rt) = hds
      cl.go_pick(EP.isnil(EP.resp(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)))), es, fs, ctx, t, rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t),
        DC.cl.found(es, fs, t, r, HS.HS{rows, hds0}, k, d, EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), bb, prev),
        DC.cl.go(tl, es, fs, t, r, HS.HS{rows, hds0}, k, EL.rsnoc(rows2, EL.row_of(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)))), EP.qsnoc(bb, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), KS.dsnoc(prev, d)),
        {==},
        hn => cl.found_ok(es, fs, ctx, t, r, rows, hds0, k, d, rows2, bb, prev, hrv, hl, ha, orr, hz, g, hp, ebb, hr2, hn),
        hn => cl.go_ok(tl, es, fs, ctx, t, r, rows, hds0, k, EL.rsnoc(rows2, EL.row_of(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)))), EP.qsnoc(bb, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), KS.dsnoc(prev, d),
          hrv, hl, ha, orr, hz, IV.allpd_snoc(es, fs, ctx, r, t, prev, d, hp, g),
          ebb_step(HS.encs(HS.hxs(es, fs, hds0), t), es, fs, t, prev, d, bb, ebb),
          EP.new_rinv(bb, rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), hr2, hl2, hn),
          PP.len_snoc(bb, rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), EL.row_of(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))), hl2), rt))

def allpd_ddrop(n: Nat, ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, h: IV.AllPD(es, fs, ctx, r, t, ds)) -> IV.AllPD(es, fs, ctx, r, t, DC.ddrop(n, ds)):
  match n ds:
    case 0n ds:
      h
    case 1n+m Nil{}:
      Unit{}
    case 1n+m Con{+d, +tl}:
      (g, rt) = h
      allpd_ddrop(m, tl, es, fs, ctx, r, t, rt)

def clx_ok.go2(+rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +n: Nat, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +r: DR.Node, +k: KS.KS,
  +hrv: {EP.rinv(HS.encs(HS.hxs(es, fs, ds), t), rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(HS.encs(HS.hxs(es, fs, ds), t)) : Nat}, +ha: IV.AllPD(es, fs, ctx, r, t, ds),
  +orr: VD.OpenD(es, ctx, r), +hz: {DC.zb(es, t) == True{} : Bool})
  -> OptK(es, fs, ctx, t, DC.cl.go(DC.ddrop(n, ds), es, fs, t, r, HS.HS{rows, ds}, k, rows, HS.encs(HS.hxs(es, fs, ds), t), Nil{})):
  cl.go_ok(DC.ddrop(n, ds), es, fs, ctx, t, r, rows, ds, k, rows, HS.encs(HS.hxs(es, fs, ds), t), Nil{}, hrv, hl, ha, orr, hz, Unit{},
    Equal.sym(List<&2, E.QExpr>, ecat(HS.encs(HS.hxs(es, fs, ds), t), Nil{}), HS.encs(HS.hxs(es, fs, ds), t), ecat_nil(HS.encs(HS.hxs(es, fs, ds), t))), hrv, hl, allpd_ddrop(n, ds, es, fs, ctx, r, t, ha))

def clx_ok.go(h: HS.HS, +n: Nat, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +r: DR.Node, +k: KS.KS, hi: IV.HInvD(es, fs, ctx, r, t, h), +orr: VD.OpenD(es, ctx, r), +hz: {DC.zb(es, t) == True{} : Bool})
  -> OptK(es, fs, ctx, t, DC.cl.go(DC.ddrop(n, HS.hs.ds(h)), es, fs, t, r, h, k, HS.hs.rows(h), HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), Nil{})):
  match h:
    case HS.HS{+rows, +ds}:
      (hrv, r1) = hi
      (hl, ha) = r1
      clx_ok.go2(rows, ds, n, es, fs, ctx, t, r, k, hrv, hl, ha, orr, hz)

# the complex-line check at an open root finds only K generators
def clx_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +r: DR.Node, +orr: VD.OpenD(es, ctx, r),
  +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> OptK(es, fs, ctx, t, DC.clx(es, fs, t, s, r)):
  clx_ok.go(DC.rhull(es, fs, t, s, r), DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), es, fs, ctx, t, r, DC.Sk.k(s), GN.rhull_inv(es, fs, ctx, t, s, r, hk, hms, hls, hz, hb), orr, hz)

def clxs.pick_ok(m: Maybe<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, hm: OptK(es, fs, ctx, t, m), +rest: Maybe<&2, DR.Der>, hr: OptK(es, fs, ctx, t, rest))
  -> OptK(es, fs, ctx, t, DC.clxs.pick(m, rest)):
  match m:
    case None{}:
      hr
    case Some{+d}:
      hm

def clxs.if_ok(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +r: DR.Node, +orr: VD.OpenD(es, ctx, r),
  +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool},
  +rest: Maybe<&2, DR.Der>, hr: OptK(es, fs, ctx, t, rest)) -> OptK(es, fs, ctx, t, DC.clxs.if(f, es, fs, t, s, r, rest)):
  match f:
    case True{}:
      clxs.pick_ok(DC.clx(es, fs, t, s, r), es, fs, ctx, t, clx_ok(es, fs, ctx, t, s, r, orr, hk, hms, hls, hz, hb), rest, hr)
    case False{}:
      hr

# the first complex line found is a K generator
def clxs_ok(rs: List<&2, DR.Node>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, hro: MG.AllOpenD(es, ctx, rs),
  +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> OptK(es, fs, ctx, t, DC.clxs(rs, es, fs, t, s)):
  match rs:
    case Nil{}:
      Unit{}
    case Con{+r, +tl}:
      (orr, rt) = hro
      clxs.if_ok(SV.bnot(DC.node_eq(r, DR.NFrame{})), es, fs, ctx, t, s, r, orr, hk, hms, hls, hz, hb, DC.clxs(tl, es, fs, t, s), clxs_ok(tl, es, fs, ctx, t, s, rt, hk, hms, hls, hz, hb))
