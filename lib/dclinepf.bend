# bend-cad: no complex line at a fixpoint (PLAN-sk13b B3). At a free root r
# whose complex-line check found nothing, a form y with y and i y both in
# r's hull set has both parts in K: y is a combination of the hull's kept
# K-squared part and its other kept generators b_j; then sum mu_j (i b_j)
# = i y - i (the K part) is in the set, so each mu_j is 0 (the check put
# every i b_j in with a nonzero residual: indset), and y is its K part.
# Proofs only.

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
import ./identpf.bend as ID
import ./spanpf.bend as SN
import ./pairpf.bend as PP
import ./pair.bend as PT
import ./listpf.bend as LP2
import ./labpf.bend as LP
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./hspacepf.bend as HP
import ./indset.bend as IS
import ./indsetpf.bend as IP
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcgenpf.bend as GN
import ./dcmergepf.bend as MG
import ./dcclxpf.bend as CX
import ./dcsetpf.bend as ST
import ./dcnodepf.bend as ND

def absurd(-A: Type, x: Empty) -> A:
  match x:

# The check's inserted forms
# --------------------------

def cp.b(b: Bool, +found: DR.Der, +rest: Maybe<&2, DR.Der>, e: {DC.cl.pick(b, found, rest) == None{} : Maybe<&2, DR.Der>}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, ST.dnone_some(found, Equal.sym(Maybe<&2, DR.Der>, Some{found}, None{}, e)))
    case False{}:
      {==}

def cp.r(b: Bool, +found: DR.Der, +rest: Maybe<&2, DR.Der>, e: {DC.cl.pick(b, found, rest) == None{} : Maybe<&2, DR.Der>}) -> {rest == None{} : Maybe<&2, DR.Der>}:
  match b:
    case True{}:
      absurd({rest == None{} : Maybe<&2, DR.Der>}, ST.dnone_some(found, Equal.sym(Maybe<&2, DR.Der>, Some{found}, None{}, e)))
    case False{}:
      e

def cg.hd(+x: E.QExpr, +rows2: List<&2, EL.Row>, h: {EP.isnil(EP.resp(EL.resid(rows2, x))) == False{} : Bool}) -> {SV.bnot(EP.isnil(EP.resp(EL.resid(rows2, x)))) == True{} : Bool}:
  %Equal.sym(Bool, EP.isnil(EP.resp(EL.resid(rows2, x))), False{}, h) : {SV.bnot(_) == True{} : Bool}
  {==}

# the check found nothing: i times each kept generator passed indset
def clgo_ind(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +r: DR.Node, +h: HS.HS, +k: KS.KS, +rows2: List<&2, EL.Row>, +bb: List<&2, E.QExpr>, +prev: List<&2, DR.Der>,
  +e: {DC.cl.go(ds, es, fs, t, r, h, k, rows2, bb, prev) == None{} : Maybe<&2, DR.Der>}) -> {IS.indset(CX.imx(es, fs, t, ds), rows2) == True{} : Bool}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +tl}:
      HP.band_tt(SV.bnot(EP.isnil(EP.resp(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))))), IS.indset(CX.imx(es, fs, t, tl), EL.rsnoc(rows2, EL.row_of(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t))))),
        cg.hd(HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), rows2,
          cp.b(EP.isnil(EP.resp(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)))), DC.cl.found(es, fs, t, r, h, k, d, EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), bb, prev),
            DC.cl.go(tl, es, fs, t, r, h, k, EL.rsnoc(rows2, EL.row_of(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)))), EP.qsnoc(bb, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), KS.dsnoc(prev, d)), e)),
        clgo_ind(tl, es, fs, t, r, h, k, EL.rsnoc(rows2, EL.row_of(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)))), EP.qsnoc(bb, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), KS.dsnoc(prev, d),
          cp.r(EP.isnil(EP.resp(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)))), DC.cl.found(es, fs, t, r, h, k, d, EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t), bb, prev),
            DC.cl.go(tl, es, fs, t, r, h, k, EL.rsnoc(rows2, EL.row_of(EL.resid(rows2, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)))), EP.qsnoc(bb, HS.enc(DR.imul(DR.Jd.x(DR.concl(es, fs, d))), t)), KS.dsnoc(prev, d)), e)))

# Prefixes
# --------

# P is a prefix of L
def Pfx(+P: List<&2, DR.Der>, +L: List<&2, DR.Der>) -> Data:
  {DC.dcat(P, DC.ddrop(DC.dlen(P), L)) == L : List<&2, DR.Der>}

def pfx_self(P: List<&2, DR.Der>) -> Pfx(P, P):
  match P:
    case Nil{}:
      {==}
    case Con{+x, +tl}:
      Equal.cong(List<&2, DR.Der>, List<&2, DR.Der>, l => Con{x, l}, DC.dcat(tl, DC.ddrop(DC.dlen(tl), tl)), tl, pfx_self(tl))

def dhd(l: List<&2, DR.Der>, +d: DR.Der) -> DR.Der:
  match l:
    case Nil{}:
      d
    case Con{x, t}:
      x

def dtl(l: List<&2, DR.Der>) -> List<&2, DR.Der>:
  match l:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      t

def dlis(l: List<&2, DR.Der>) -> Bool:
  match l:
    case Nil{}:
      False{}
    case Con{x, t}:
      True{}

def pfx_snoc.c(+x: DR.Der, +Pt: List<&2, DR.Der>, +y: DR.Der, +Lt: List<&2, DR.Der>, +d: DR.Der,
  h: {Con{x, DC.dcat(Pt, DC.ddrop(DC.dlen(Pt), Lt))} == Con{y, Lt} : List<&2, DR.Der>}, ih: Pfx(Pt, KS.dsnoc(Lt, d)))
  -> {Con{x, DC.dcat(Pt, DC.ddrop(DC.dlen(Pt), KS.dsnoc(Lt, d)))} == Con{y, KS.dsnoc(Lt, d)} : List<&2, DR.Der>}:
  %Equal.cong(List<&2, DR.Der>, DR.Der, l => dhd(l, x), Con{x, DC.dcat(Pt, DC.ddrop(DC.dlen(Pt), Lt))}, Con{y, Lt}, h) : {Con{x, DC.dcat(Pt, DC.ddrop(DC.dlen(Pt), KS.dsnoc(Lt, d)))} == Con{_, KS.dsnoc(Lt, d)} : List<&2, DR.Der>}
  Equal.cong(List<&2, DR.Der>, List<&2, DR.Der>, l => Con{x, l}, DC.dcat(Pt, DC.ddrop(DC.dlen(Pt), KS.dsnoc(Lt, d))), KS.dsnoc(Lt, d), ih)

def pfx_tl(+x: DR.Der, +Pt: List<&2, DR.Der>, +y: DR.Der, +Lt: List<&2, DR.Der>, h: {Con{x, DC.dcat(Pt, DC.ddrop(DC.dlen(Pt), Lt))} == Con{y, Lt} : List<&2, DR.Der>}) -> Pfx(Pt, Lt):
  Equal.cong(List<&2, DR.Der>, List<&2, DR.Der>, l => dtl(l), Con{x, DC.dcat(Pt, DC.ddrop(DC.dlen(Pt), Lt))}, Con{y, Lt}, h)

# a prefix stays one when the list grows at its end
def pfx_snoc(P: List<&2, DR.Der>, L: List<&2, DR.Der>, +d: DR.Der, +h: Pfx(P, L)) -> Pfx(P, KS.dsnoc(L, d)):
  match P L:
    case Nil{} L:
      {==}
    case Con{+x, +Pt} Nil{}:
      absurd(Pfx(Con{x, Pt}, KS.dsnoc(Nil{}, d)), LP.tf(Equal.cong(List<&2, DR.Der>, Bool, l => dlis(l), Con{x, DC.dcat(Pt, Nil{})}, Nil{}, h)))
    case Con{+x, +Pt} Con{+y, +Lt}:
      pfx_snoc.c(x, Pt, y, Lt, d, h, pfx_snoc(Pt, Lt, d, pfx_tl(x, Pt, y, Lt, h)))

def pfx_add.pick(b: Bool, +P: List<&2, DR.Der>, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +res: EL.Res, +d: DR.Der, h: Pfx(P, ds)) -> Pfx(P, HS.hs.ds(HS.hs.pick(b, rows, ds, res, d))):
  match b:
    case True{}:
      h
    case False{}:
      pfx_snoc(P, ds, d, h)

def pfx_add(+P: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, h: HS.HS, +d: DR.Der, hp: Pfx(P, HS.hs.ds(h))) -> Pfx(P, HS.hs.ds(HS.hs.add(es, fs, t, h, d))):
  match h:
    case HS.HS{+rows, +ds}:
      pfx_add.pick(EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), P, rows, ds, EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), d, hp)

# folding more generators in keeps the kept list's prefix
def pfx_fold(gs: List<&2, DR.Der>, +P: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, hp: Pfx(P, HS.hs.ds(h))) -> Pfx(P, HS.hs.ds(DC.hfold(gs, es, fs, t, h))):
  match gs:
    case Nil{}:
      hp
    case Con{+d, tl}:
      pfx_fold(tl, P, es, fs, t, HS.hs.add(es, fs, t, h, d), pfx_add(P, es, fs, t, h, d, hp))

# Combinations over a concatenation
# ---------------------------------

def vcat(xs: List<&2, SK.VE>, +ys: List<&2, SK.VE>) -> List<&2, SK.VE>:
  match xs:
    case Nil{}:
      ys
    case Con{x, t}:
      Con{x, vcat(t, ys)}

def hxs_cat(xs: List<&2, DR.Der>, +ys: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>) -> {HS.hxs(es, fs, DC.dcat(xs, ys)) == vcat(HS.hxs(es, fs, xs), HS.hxs(es, fs, ys)) : List<&2, SK.VE>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +tl}:
      Equal.cong(List<&2, SK.VE>, List<&2, SK.VE>, l => Con{DR.Jd.x(DR.concl(es, fs, x)), l}, HS.hxs(es, fs, DC.dcat(tl, ys)), vcat(HS.hxs(es, fs, tl), HS.hxs(es, fs, ys)), hxs_cat(tl, ys, es, fs))

def vlen(xs: List<&2, SK.VE>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, t}:
      1n+vlen(t)

def qdrop_tl(n: Nat, ls: List<&2, S.Q>) -> {PT.qdrop(1n+n, ls) == PT.qdrop(n, SN.qtl(ls)) : List<&2, S.Q>}:
  match ls:
    case Nil{}:
      Equal.sym(List<&2, S.Q>, PT.qdrop(n, Nil{}), Nil{}, PP.qdrop_nil(n))
    case Con{+l, +lt}:
      {==}

def ca.q(+a: S.Q, +X: S.Q, +P: S.Q, +Q: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(a, X), S.Q.mul(DR.qo(), S.Q.add(S.Q.mul(DR.qo(), P), S.Q.mul(DR.qo(), Q)))), S.Q.add(S.Q.mul(DR.qo(), S.Q.add(S.Q.mul(a, X), S.Q.mul(DR.qo(), P))), S.Q.mul(DR.qo(), Q))):
  QR.qring_eq([a, X, P, Q], E.QAdd{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QMul{E.QCst{DR.qo()}, E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QVar{2n}}, E.QMul{E.QCst{DR.qo()}, E.QVar{3n}}}}}, E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QAdd{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QMul{E.QCst{DR.qo()}, E.QVar{2n}}}}, E.QMul{E.QCst{DR.qo()}, E.QVar{3n}}}, {==})

def ca.ax(+p: List<&2, S.Q>, +a: S.Q, +x: SK.VE, +P: SK.VE, +Q: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.x(DR.vlin(a, x, DR.qo(), DR.vlin(DR.qo(), P, DR.qo(), Q)))), E.qeval(p, SK.VE.x(DR.vlin(DR.qo(), DR.vlin(a, x, DR.qo(), P), DR.qo(), Q)))):
  ca.q(a, E.qeval(p, SK.VE.x(x)), E.qeval(p, SK.VE.x(P)), E.qeval(p, SK.VE.x(Q)))

def ca.ay(+p: List<&2, S.Q>, +a: S.Q, +x: SK.VE, +P: SK.VE, +Q: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.y(DR.vlin(a, x, DR.qo(), DR.vlin(DR.qo(), P, DR.qo(), Q)))), E.qeval(p, SK.VE.y(DR.vlin(DR.qo(), DR.vlin(a, x, DR.qo(), P), DR.qo(), Q)))):
  ca.q(a, E.qeval(p, SK.VE.y(x)), E.qeval(p, SK.VE.y(P)), E.qeval(p, SK.VE.y(Q)))

def cassoc(+a: S.Q, +x: SK.VE, +P: SK.VE, +Q: SK.VE) -> VD.SameVD(DR.vlin(a, x, DR.qo(), DR.vlin(DR.qo(), P, DR.qo(), Q)), DR.vlin(DR.qo(), DR.vlin(a, x, DR.qo(), P), DR.qo(), Q)):
  (ID.qzero_ident(SK.VE.x(DR.vlin(a, x, DR.qo(), DR.vlin(DR.qo(), P, DR.qo(), Q))), SK.VE.x(DR.vlin(DR.qo(), DR.vlin(a, x, DR.qo(), P), DR.qo(), Q)), p => ca.ax(p, a, x, P, Q)),
   ID.qzero_ident(SK.VE.y(DR.vlin(a, x, DR.qo(), DR.vlin(DR.qo(), P, DR.qo(), Q))), SK.VE.y(DR.vlin(DR.qo(), DR.vlin(a, x, DR.qo(), P), DR.qo(), Q)), p => ca.ay(p, a, x, P, Q)))

def cn.q(+Z: S.Q, +C: S.Q) -> S.Q.eq(C, S.Q.add(S.Q.mul(DR.qo(), S.Q.add(S.Q.mul(DR.qz(), Z), S.Q.mul(DR.qz(), Z))), S.Q.mul(DR.qo(), C))):
  QR.qring_eq([Z, C], E.QVar{1n}, E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}}}, E.QMul{E.QCst{DR.qo()}, E.QVar{1n}}}, {==})

def cnil.ax(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +r: DR.Node, +y: SK.VE) -> S.Q.eq(E.qeval(p, SK.VE.x(y)), E.qeval(p, SK.VE.x(DR.vlin(DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), DR.qo(), y)))):
  cn.q(E.qeval(p, SK.VE.x(DR.zdir(es, r))), E.qeval(p, SK.VE.x(y)))

def cnil.ay(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +r: DR.Node, +y: SK.VE) -> S.Q.eq(E.qeval(p, SK.VE.y(y)), E.qeval(p, SK.VE.y(DR.vlin(DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), DR.qo(), y)))):
  cn.q(E.qeval(p, SK.VE.y(DR.zdir(es, r))), E.qeval(p, SK.VE.y(y)))

def cnil(+es: List<&2, SK.Ent>, +r: DR.Node, +y: SK.VE) -> VD.SameVD(y, DR.vlin(DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), DR.qo(), y)):
  (ID.qzero_ident(SK.VE.x(y), SK.VE.x(DR.vlin(DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), DR.qo(), y)), p => cnil.ax(p, es, r, y)),
   ID.qzero_ident(SK.VE.y(y), SK.VE.y(DR.vlin(DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), DR.qo(), y)), p => cnil.ay(p, es, r, y)))

# a combination over xa then xb splits: the first |xa| coefficients take xa
def clin_cat(xa: List<&2, SK.VE>, +xb: List<&2, SK.VE>, +es: List<&2, SK.Ent>, +r: DR.Node, +ls: List<&2, S.Q>)
  -> VD.SameVD(HS.clin(es, r, ls, vcat(xa, xb)), DR.vlin(DR.qo(), HS.clin(es, r, ls, xa), DR.qo(), HS.clin(es, r, PT.qdrop(vlen(xa), ls), xb))):
  match xa:
    case Nil{}:
      GN.samevd_tr(HS.clin(es, r, ls, xb), DR.vlin(DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), DR.qo(), HS.clin(es, r, ls, xb)), DR.vlin(DR.qo(), HS.clin(es, r, ls, Nil{}), DR.qo(), HS.clin(es, r, ls, xb)),
        cnil(es, r, HS.clin(es, r, ls, xb)),
        ST.vcong(DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), HS.clin(es, r, ls, Nil{}), DR.qo(), HS.clin(es, r, ls, xb), HS.clin(es, r, ls, xb), MG.samevd_sym(HS.clin(es, r, ls, Nil{}), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), ST.clin_nil(ls, es, r)), MG.samevd_refl(HS.clin(es, r, ls, xb))))
    case Con{+x, +xt}:
      %Equal.sym(List<&2, S.Q>, PT.qdrop(1n+vlen(xt), ls), PT.qdrop(vlen(xt), SN.qtl(ls)), qdrop_tl(vlen(xt), ls)) : VD.SameVD(HS.clin(es, r, ls, Con{x, vcat(xt, xb)}), DR.vlin(DR.qo(), HS.clin(es, r, ls, Con{x, xt}), DR.qo(), HS.clin(es, r, _, xb)))
      GN.samevd_tr(HS.clin(es, r, ls, Con{x, vcat(xt, xb)}), DR.vlin(SN.qhd(ls), x, DR.qo(), HS.clin(es, r, SN.qtl(ls), vcat(xt, xb))), DR.vlin(DR.qo(), HS.clin(es, r, ls, Con{x, xt}), DR.qo(), HS.clin(es, r, PT.qdrop(vlen(xt), SN.qtl(ls)), xb)),
        ST.clin_ht(ls, es, r, x, vcat(xt, xb)),
        GN.samevd_tr(DR.vlin(SN.qhd(ls), x, DR.qo(), HS.clin(es, r, SN.qtl(ls), vcat(xt, xb))), DR.vlin(SN.qhd(ls), x, DR.qo(), DR.vlin(DR.qo(), HS.clin(es, r, SN.qtl(ls), xt), DR.qo(), HS.clin(es, r, PT.qdrop(vlen(xt), SN.qtl(ls)), xb))),
          DR.vlin(DR.qo(), HS.clin(es, r, ls, Con{x, xt}), DR.qo(), HS.clin(es, r, PT.qdrop(vlen(xt), SN.qtl(ls)), xb)),
          ST.vcong(SN.qhd(ls), x, x, DR.qo(), HS.clin(es, r, SN.qtl(ls), vcat(xt, xb)), DR.vlin(DR.qo(), HS.clin(es, r, SN.qtl(ls), xt), DR.qo(), HS.clin(es, r, PT.qdrop(vlen(xt), SN.qtl(ls)), xb)), MG.samevd_refl(x), clin_cat(xt, xb, es, r, SN.qtl(ls))),
          GN.samevd_tr(DR.vlin(SN.qhd(ls), x, DR.qo(), DR.vlin(DR.qo(), HS.clin(es, r, SN.qtl(ls), xt), DR.qo(), HS.clin(es, r, PT.qdrop(vlen(xt), SN.qtl(ls)), xb))),
            DR.vlin(DR.qo(), DR.vlin(SN.qhd(ls), x, DR.qo(), HS.clin(es, r, SN.qtl(ls), xt)), DR.qo(), HS.clin(es, r, PT.qdrop(vlen(xt), SN.qtl(ls)), xb)),
            DR.vlin(DR.qo(), HS.clin(es, r, ls, Con{x, xt}), DR.qo(), HS.clin(es, r, PT.qdrop(vlen(xt), SN.qtl(ls)), xb)),
            cassoc(SN.qhd(ls), x, HS.clin(es, r, SN.qtl(ls), xt), HS.clin(es, r, PT.qdrop(vlen(xt), SN.qtl(ls)), xb)),
            ST.vcong(DR.qo(), DR.vlin(SN.qhd(ls), x, DR.qo(), HS.clin(es, r, SN.qtl(ls), xt)), HS.clin(es, r, ls, Con{x, xt}), DR.qo(), HS.clin(es, r, PT.qdrop(vlen(xt), SN.qtl(ls)), xb), HS.clin(es, r, PT.qdrop(vlen(xt), SN.qtl(ls)), xb),
              MG.samevd_sym(HS.clin(es, r, ls, Con{x, xt}), DR.vlin(SN.qhd(ls), x, DR.qo(), HS.clin(es, r, SN.qtl(ls), xt)), ST.clin_ht(ls, es, r, x, xt)),
              MG.samevd_refl(HS.clin(es, r, PT.qdrop(vlen(xt), SN.qtl(ls)), xb))))))
