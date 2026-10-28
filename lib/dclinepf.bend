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
import ./qnorm.bend as QN
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
import ./lspanpf.bend as LS
import ./dcreppf.bend as RP
import ./dcinvpf.bend as IV

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

# K's generators are in K
# -----------------------

def in_unit.at(+p: List<&2, S.Q>, +e: E.QExpr, +bt: List<&2, E.QExpr>) -> S.Q.eq(E.qeval(p, e), E.qeval(p, SV.lin(Con{DR.qo(), Nil{}}, Con{e, bt}))):
  QR.qring_eq([E.qeval(p, e)], E.QVar{0n}, E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QVar{0n}}, E.QCst{DR.qz()}}, {==})

def in_wid.q(+L: S.Q, +B: S.Q) -> S.Q.eq(L, S.Q.add(S.Q.mul(DR.qz(), B), L)):
  QR.qring_eq([L, B], E.QVar{0n}, E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}, E.QVar{0n}}, {==})

def in_wid.at(+p: List<&2, S.Q>, +e: E.QExpr, +b: E.QExpr, +bt: List<&2, E.QExpr>, +ls: List<&2, S.Q>, hi: SV.Ident(e, SV.lin(ls, bt)))
  -> S.Q.eq(E.qeval(p, e), E.qeval(p, SV.lin(Con{DR.qz(), ls}, Con{b, bt}))):
  LQ.q_trans(E.qeval(p, e), E.qeval(p, SV.lin(ls, bt)), E.qeval(p, SV.lin(Con{DR.qz(), ls}, Con{b, bt})), hi(p), in_wid.q(E.qeval(p, SV.lin(ls, bt)), E.qeval(p, b)))

def in_wid.go(+e: E.QExpr, +b: E.QExpr, +bt: List<&2, E.QExpr>, +ls: List<&2, S.Q>, +q0: {QN.qzero(E.QSub{e, SV.lin(ls, bt)}) == True{} : Bool}) -> SN.InSpan(e, Con{b, bt}):
  SN.in_of_ident(e, Con{b, bt}, Con{DR.qz(), ls}, p => in_wid.at(p, e, b, bt, ls, ID.ident_ok(e, SV.lin(ls, bt), q0)))

# a span grows to the front
def in_wid(+e: E.QExpr, +b: E.QExpr, +bt: List<&2, E.QExpr>, h: SN.InSpan(e, bt)) -> SN.InSpan(e, Con{b, bt}):
  (+ls, +q0) = h
  in_wid.go(e, b, bt, ls, q0)

# each of the K generators ds (a suffix) is in the span B
def AIn(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +B: List<&2, E.QExpr>) -> Data:
  match ds:
    case Nil{}:
      Unit
    case Con{+d, +tl}:
      SK.Both(SN.InSpan(DR.Jd.e(DR.concl(es, fs, d)), B), AIn(tl, es, fs, B))

def ain_wid(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +b: E.QExpr, +bt: List<&2, E.QExpr>, h: AIn(ds, es, fs, bt)) -> AIn(ds, es, fs, Con{b, bt}):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, +tl}:
      (a, rt) = h
      (in_wid(DR.Jd.e(DR.concl(es, fs, d)), b, bt, a), ain_wid(tl, es, fs, b, bt, rt))

def ain_all(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>) -> AIn(ds, es, fs, KS.kexprs(es, fs, ds)):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, +tl}:
      (SN.in_of_ident(DR.Jd.e(DR.concl(es, fs, d)), KS.kexprs(es, fs, Con{d, tl}), Con{DR.qo(), Nil{}}, p => in_unit.at(p, DR.Jd.e(DR.concl(es, fs, d)), KS.kexprs(es, fs, tl))),
       ain_wid(tl, es, fs, DR.Jd.e(DR.concl(es, fs, d)), KS.kexprs(es, fs, tl), ain_all(tl, es, fs)))

# Forms with both parts in K
# --------------------------

def K2(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +x: SK.VE) -> Data:
  SK.Both({KS.ks.inb(k, SK.VE.x(x)) == True{} : Bool}, {KS.ks.inb(k, SK.VE.y(x)) == True{} : Bool})

def K2L(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, ds: List<&2, DR.Der>) -> Data:
  match ds:
    case Nil{}:
      Unit
    case Con{+d, +tl}:
      SK.Both(K2(es, fs, k, DR.Jd.x(DR.concl(es, fs, d))), K2L(es, fs, k, tl))

def svx(+u: SK.VE, +v: SK.VE, h: VD.SameVD(u, v)) -> VD.SameD(SK.VE.x(u), SK.VE.x(v)):
  (a, b) = h
  a

def svy(+u: SK.VE, +v: SK.VE, h: VD.SameVD(u, v)) -> VD.SameD(SK.VE.y(u), SK.VE.y(v)):
  (a, b) = h
  b

def z0.at(+p: List<&2, S.Q>) -> S.Q.eq(E.qeval(p, DR.zeroe()), E.qeval(p, DR.zeroe())):
  LQ.q_refl(DR.qz())

# a form the same as (e, 0) or (0, e), e in K, has both parts in K
def k2_kv(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +x: SK.VE, +y: SK.VE, +hr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)), +e: VD.SameVD(x, y), +hx: {KS.ks.inb(k, SK.VE.x(y)) == True{} : Bool},
  +hy: {KS.ks.inb(k, SK.VE.y(y)) == True{} : Bool}) -> K2(es, fs, k, x):
  (ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), SK.VE.x(y), SK.VE.x(x), hr, hx, svx(y, x, MG.samevd_sym(x, y, e))),
   ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), SK.VE.y(y), SK.VE.y(x), hr, hy, svy(y, x, MG.samevd_sym(x, y, e))))

def k2_kgens.go(+d: DR.Der, +tl: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +r: DR.Node, +hr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)), +he: {KS.ks.inb(k, DR.Jd.e(DR.concl(es, fs, d))) == True{} : Bool},
  ht: K2L(es, fs, k, DC.kgens(r, tl))) -> K2L(es, fs, k, DC.kgens(r, Con{d, tl})):
  (k2_kv(es, fs, k, DR.Jd.x(DR.concl(es, fs, HS.kre(r, d))), ST.kv.re(DR.Jd.e(DR.concl(es, fs, d))), hr, ND.kre_v(es, fs, r, d), he, ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), hr)),
   (k2_kv(es, fs, k, DR.Jd.x(DR.concl(es, fs, HS.kim(r, d))), ST.kv.im(DR.Jd.e(DR.concl(es, fs, d))), hr, ND.kim_v(es, fs, r, d), ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), hr), he), ht))

def k2_kgens(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +r: DR.Node, +hr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)), h: AIn(ds, es, fs, KS.kexprs(es, fs, KS.ks.ds(k)))) -> K2L(es, fs, k, DC.kgens(r, ds)):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, +tl}:
      (a, rt) = h
      k2_kgens.go(d, tl, es, fs, k, r, hr, ST.ri.zero(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), DR.Jd.e(DR.concl(es, fs, d)), hr, a), k2_kgens(tl, es, fs, k, r, hr, rt))

def k2_snoc(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +d: DR.Der, h: K2L(es, fs, k, ds), +hd: K2(es, fs, k, DR.Jd.x(DR.concl(es, fs, d))))
  -> K2L(es, fs, k, KS.dsnoc(ds, d)):
  match ds:
    case Nil{}:
      (hd, Unit{})
    case Con{+d0, +tl}:
      (a, rt) = h
      (a, k2_snoc(tl, es, fs, k, d, rt, hd))

def k2_add.pick(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +res: EL.Res, +d: DR.Der,
  h: K2L(es, fs, k, ds), +hd: K2(es, fs, k, DR.Jd.x(DR.concl(es, fs, d)))) -> K2L(es, fs, k, HS.hs.ds(HS.hs.pick(b, rows, ds, res, d))):
  match b:
    case True{}:
      h
    case False{}:
      k2_snoc(ds, es, fs, k, d, h, hd)

def k2_add(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, h: HS.HS, +d: DR.Der, hk: K2L(es, fs, k, HS.hs.ds(h)), +hd: K2(es, fs, k, DR.Jd.x(DR.concl(es, fs, d))))
  -> K2L(es, fs, k, HS.hs.ds(HS.hs.add(es, fs, t, h, d))):
  match h:
    case HS.HS{+rows, +ds}:
      k2_add.pick(EP.isnil(EP.resp(EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)))), es, fs, k, rows, ds, EL.resid(rows, HS.enc(DR.Jd.x(DR.concl(es, fs, d)), t)), d, hk, hd)

# folding forms with both parts in K keeps the kept ones so
def k2_fold(gs: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +h: HS.HS, hk: K2L(es, fs, k, HS.hs.ds(h)), hg: K2L(es, fs, k, gs))
  -> K2L(es, fs, k, HS.hs.ds(DC.hfold(gs, es, fs, t, h))):
  match gs:
    case Nil{}:
      hk
    case Con{+d, +tl}:
      (a, rt) = hg
      k2_fold(tl, es, fs, t, k, HS.hs.add(es, fs, t, h, d), k2_add(es, fs, t, k, h, d, hk, a), rt)

def K2V(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, xs: List<&2, SK.VE>) -> Data:
  match xs:
    case Nil{}:
      Unit
    case Con{+x, tl}:
      SK.Both(K2(es, fs, k, x), K2V(es, fs, k, tl))

def k2v_of(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, h: K2L(es, fs, k, ds)) -> K2V(es, fs, k, HS.hxs(es, fs, ds)):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, +tl}:
      (a, rt) = h
      (a, k2v_of(tl, es, fs, k, rt))

def kb.q(+Z: S.Q) -> S.Q.eq(DR.qz(), S.Q.add(S.Q.mul(DR.qz(), Z), S.Q.mul(DR.qz(), Z))):
  QR.qring_eq([Z], E.QCst{DR.qz()}, E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}}, {==})

def k2v.hd(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +x: SK.VE, +xt: List<&2, SK.VE>, h: K2V(es, fs, k, Con{x, xt})) -> K2(es, fs, k, x):
  (a, rt) = h
  a

def k2v.tl(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +x: SK.VE, +xt: List<&2, SK.VE>, h: K2V(es, fs, k, Con{x, xt})) -> K2V(es, fs, k, xt):
  (a, rt) = h
  rt

def k2_base(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +r: DR.Node, +hr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k))) -> K2(es, fs, k, DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))):
  (ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), DR.zeroe(), SK.VE.x(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))), hr, ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), hr), ID.qzero_ident(DR.zeroe(), SK.VE.x(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))), p => kb.q(E.qeval(p, SK.VE.x(DR.zdir(es, r)))))),
   ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), DR.zeroe(), SK.VE.y(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))), hr, ST.ri.z0(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), hr), ID.qzero_ident(DR.zeroe(), SK.VE.y(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))), p => kb.q(E.qeval(p, SK.VE.y(DR.zdir(es, r)))))))

def k2_lin.go(+l: S.Q, +x: SK.VE, +rest: SK.VE, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +hr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)), x1: {KS.ks.inb(k, SK.VE.x(x)) == True{} : Bool},
  y1: {KS.ks.inb(k, SK.VE.y(x)) == True{} : Bool}, hrest: K2(es, fs, k, rest)) -> K2(es, fs, k, DR.vlin(l, x, DR.qo(), rest)):
  (x2, y2) = hrest
  (ST.ri.lin(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), l, SK.VE.x(x), DR.qo(), SK.VE.x(rest), hr, x1, x2), ST.ri.lin(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), l, SK.VE.y(x), DR.qo(), SK.VE.y(rest), hr, y1, y2))

def k2_lin(+l: S.Q, +x: SK.VE, +rest: SK.VE, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +hr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)), hx: K2(es, fs, k, x), hrest: K2(es, fs, k, rest))
  -> K2(es, fs, k, DR.vlin(l, x, DR.qo(), rest)):
  (x1, y1) = hx
  k2_lin.go(l, x, rest, es, fs, k, hr, x1, y1, hrest)

# a combination of forms with both parts in K has both parts in K
def k2_clin(ls: List<&2, S.Q>, xs: List<&2, SK.VE>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +r: DR.Node, +hr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)), +h: K2V(es, fs, k, xs))
  -> K2(es, fs, k, HS.clin(es, r, ls, xs)):
  match ls xs:
    case Con{+l, +lt} Con{+x, +xt}:
      k2_lin(l, x, HS.clin(es, r, lt, xt), es, fs, k, hr, k2v.hd(es, fs, k, x, xt, h), k2_clin(lt, xt, es, fs, k, r, hr, k2v.tl(es, fs, k, x, xt, h)))
    case Nil{} xs:
      k2_base(es, fs, k, r, hr)
    case Con{+l, +lt} Nil{}:
      k2_base(es, fs, k, r, hr)

# Zero coefficients
# -----------------

def cz.q(+l: S.Q, +X: S.Q, +Z: S.Q, h: S.Q.eq(l, DR.qz())) -> S.Q.eq(S.Q.add(S.Q.mul(l, X), S.Q.mul(DR.qo(), S.Q.add(S.Q.mul(DR.qz(), Z), S.Q.mul(DR.qz(), Z)))), S.Q.add(S.Q.mul(DR.qz(), Z), S.Q.mul(DR.qz(), Z))):
  LQ.q_trans(S.Q.add(S.Q.mul(l, X), S.Q.mul(DR.qo(), S.Q.add(S.Q.mul(DR.qz(), Z), S.Q.mul(DR.qz(), Z)))), S.Q.add(S.Q.mul(DR.qz(), X), S.Q.mul(DR.qo(), S.Q.add(S.Q.mul(DR.qz(), Z), S.Q.mul(DR.qz(), Z)))), S.Q.add(S.Q.mul(DR.qz(), Z), S.Q.mul(DR.qz(), Z)),
    LQ.q_add_cong_l(S.Q.mul(l, X), S.Q.mul(DR.qz(), X), S.Q.mul(DR.qo(), S.Q.add(S.Q.mul(DR.qz(), Z), S.Q.mul(DR.qz(), Z))), LQ.q_mul_cong_l(l, DR.qz(), X, h)), QR.qring_eq([X, Z], E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qo()}, E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}}}}, E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}}, {==}))

def cz.ax(+p: List<&2, S.Q>, +l: S.Q, +x: SK.VE, +es: List<&2, SK.Ent>, +r: DR.Node, +hl: {DR.qnz(l) == False{} : Bool})
  -> S.Q.eq(E.qeval(p, SK.VE.x(DR.vlin(l, x, DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))))), E.qeval(p, SK.VE.x(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))))):
  cz.q(l, E.qeval(p, SK.VE.x(x)), E.qeval(p, SK.VE.x(DR.zdir(es, r))), LP.qnz_f(l, hl))

def cz.ay(+p: List<&2, S.Q>, +l: S.Q, +x: SK.VE, +es: List<&2, SK.Ent>, +r: DR.Node, +hl: {DR.qnz(l) == False{} : Bool})
  -> S.Q.eq(E.qeval(p, SK.VE.y(DR.vlin(l, x, DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))))), E.qeval(p, SK.VE.y(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))))):
  cz.q(l, E.qeval(p, SK.VE.y(x)), E.qeval(p, SK.VE.y(DR.zdir(es, r))), LP.qnz_f(l, hl))

def cz(+l: S.Q, +x: SK.VE, +es: List<&2, SK.Ent>, +r: DR.Node, +hl: {DR.qnz(l) == False{} : Bool}) -> VD.SameVD(DR.vlin(l, x, DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))):
  (ID.qzero_ident(SK.VE.x(DR.vlin(l, x, DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))), SK.VE.x(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))), p => cz.ax(p, l, x, es, r, hl)),
   ID.qzero_ident(SK.VE.y(DR.vlin(l, x, DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))), SK.VE.y(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))), p => cz.ay(p, l, x, es, r, hl)))

# every coefficient 0: the combination is 0
def clin_zero(ls: List<&2, S.Q>, xs: List<&2, SK.VE>, +es: List<&2, SK.Ent>, +r: DR.Node, +t: Nat, +h: {IS.allz(ls, CX.imxs(xs, t)) == True{} : Bool})
  -> VD.SameVD(HS.clin(es, r, ls, xs), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))):
  match ls xs:
    case Con{+l, +lt} Con{+x, +xt}:
      GN.samevd_tr(DR.vlin(l, x, DR.qo(), HS.clin(es, r, lt, xt)), DR.vlin(l, x, DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)),
        ST.vcong(l, x, x, DR.qo(), HS.clin(es, r, lt, xt), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), MG.samevd_refl(x),
          clin_zero(lt, xt, es, r, t, LP2.band_r(SV.bnot(DR.qnz(l)), IS.allz(lt, CX.imxs(xt, t)), h))),
        cz(l, x, es, r, IP.bnot_t(DR.qnz(l), LP2.band_l(SV.bnot(DR.qnz(l)), IS.allz(lt, CX.imxs(xt, t)), h))))
    case Nil{} xs:
      MG.samevd_refl(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))
    case Con{+l, +lt} Nil{}:
      MG.samevd_refl(DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))

# i times
# -------

def ic.ax(+p: List<&2, S.Q>, +a: SK.VE, +b: SK.VE, +hy: VD.SameD(SK.VE.y(a), SK.VE.y(b))) -> S.Q.eq(E.qeval(p, SK.VE.x(DR.imul(a))), E.qeval(p, SK.VE.x(DR.imul(b)))):
  LQ.q_neg_cong(E.qeval(p, SK.VE.y(a)), E.qeval(p, SK.VE.y(b)), ID.ident_ok(SK.VE.y(a), SK.VE.y(b), hy)(p))

def imul_cong(+a: SK.VE, +b: SK.VE, h: VD.SameVD(a, b)) -> VD.SameVD(DR.imul(a), DR.imul(b)):
  (+hx, +hy) = h
  (ID.qzero_ident(SK.VE.x(DR.imul(a)), SK.VE.x(DR.imul(b)), p => ic.ax(p, a, b, hy)), hx)

def is.qx(+A: S.Q, +B: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(DR.qo(), S.Q.neg(S.Q.add(S.Q.mul(DR.qo(), A), S.Q.mul(DR.qo(), B)))), S.Q.mul(S.Q.neg(DR.qo()), S.Q.neg(A))), S.Q.neg(B)):
  QR.qring_eq([A, B], E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QNeg{E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qo()}, E.QVar{1n}}}}}, E.QMul{E.QNeg{E.QCst{DR.qo()}}, E.QNeg{E.QVar{0n}}}}, E.QNeg{E.QVar{1n}}, {==})

def is.qy(+A: S.Q, +B: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(DR.qo(), S.Q.add(S.Q.mul(DR.qo(), A), S.Q.mul(DR.qo(), B))), S.Q.mul(S.Q.neg(DR.qo()), A)), B):
  QR.qring_eq([A, B], E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qo()}, E.QVar{1n}}}}, E.QMul{E.QNeg{E.QCst{DR.qo()}}, E.QVar{0n}}}, E.QVar{1n}, {==})

def is.ax(+p: List<&2, S.Q>, +a: SK.VE, +b: SK.VE) -> S.Q.eq(E.qeval(p, SK.VE.x(DR.vlin(DR.qo(), DR.imul(DR.vlin(DR.qo(), a, DR.qo(), b)), S.Q.neg(DR.qo()), DR.imul(a)))), E.qeval(p, SK.VE.x(DR.imul(b)))):
  is.qx(E.qeval(p, SK.VE.y(a)), E.qeval(p, SK.VE.y(b)))

def is.ay(+p: List<&2, S.Q>, +a: SK.VE, +b: SK.VE) -> S.Q.eq(E.qeval(p, SK.VE.y(DR.vlin(DR.qo(), DR.imul(DR.vlin(DR.qo(), a, DR.qo(), b)), S.Q.neg(DR.qo()), DR.imul(a)))), E.qeval(p, SK.VE.y(DR.imul(b)))):
  is.qy(E.qeval(p, SK.VE.x(a)), E.qeval(p, SK.VE.x(b)))

# i (a + b) - i a = i b
def isub(+a: SK.VE, +b: SK.VE) -> VD.SameVD(DR.vlin(DR.qo(), DR.imul(DR.vlin(DR.qo(), a, DR.qo(), b)), S.Q.neg(DR.qo()), DR.imul(a)), DR.imul(b)):
  (ID.qzero_ident(SK.VE.x(DR.vlin(DR.qo(), DR.imul(DR.vlin(DR.qo(), a, DR.qo(), b)), S.Q.neg(DR.qo()), DR.imul(a))), SK.VE.x(DR.imul(b)), p => is.ax(p, a, b)),
   ID.qzero_ident(SK.VE.y(DR.vlin(DR.qo(), DR.imul(DR.vlin(DR.qo(), a, DR.qo(), b)), S.Q.neg(DR.qo()), DR.imul(a))), SK.VE.y(DR.imul(b)), p => is.ay(p, a, b)))

def vb.q(+K: S.Q, +Z: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(DR.qo(), K), S.Q.mul(DR.qo(), S.Q.add(S.Q.mul(DR.qz(), Z), S.Q.mul(DR.qz(), Z)))), K):
  QR.qring_eq([K, Z], E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qo()}, E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}}}}, E.QVar{0n}, {==})

def vb1.ax(+p: List<&2, S.Q>, +a: SK.VE, +es: List<&2, SK.Ent>, +r: DR.Node) -> S.Q.eq(E.qeval(p, SK.VE.x(DR.vlin(DR.qo(), a, DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))))), E.qeval(p, SK.VE.x(a))):
  vb.q(E.qeval(p, SK.VE.x(a)), E.qeval(p, SK.VE.x(DR.zdir(es, r))))

def vb1.ay(+p: List<&2, S.Q>, +a: SK.VE, +es: List<&2, SK.Ent>, +r: DR.Node) -> S.Q.eq(E.qeval(p, SK.VE.y(DR.vlin(DR.qo(), a, DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))))), E.qeval(p, SK.VE.y(a))):
  vb.q(E.qeval(p, SK.VE.y(a)), E.qeval(p, SK.VE.y(DR.zdir(es, r))))

# a + 0 = a
def vb1(+a: SK.VE, +es: List<&2, SK.Ent>, +r: DR.Node) -> VD.SameVD(DR.vlin(DR.qo(), a, DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))), a):
  (ID.qzero_ident(SK.VE.x(DR.vlin(DR.qo(), a, DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))), SK.VE.x(a), p => vb1.ax(p, a, es, r)),
   ID.qzero_ident(SK.VE.y(DR.vlin(DR.qo(), a, DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)))), SK.VE.y(a), p => vb1.ay(p, a, es, r)))

def ng.q(+e: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(S.Q.neg(DR.qo()), e), S.Q.mul(DR.qz(), e)), S.Q.neg(e)):
  QR.qring_eq([e], E.QAdd{E.QMul{E.QNeg{E.QCst{DR.qo()}}, E.QVar{0n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}}, E.QNeg{E.QVar{0n}}, {==})

def ng.at(+p: List<&2, S.Q>, +e: E.QExpr) -> S.Q.eq(E.qeval(p, ST.lin2(S.Q.neg(DR.qo()), e, DR.qz(), e)), E.qeval(p, E.QNeg{e})):
  ng.q(E.qeval(p, e))

# K holds -e with e
def kneg(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +e: E.QExpr, +hr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)), +h: {KS.ks.inb(k, e) == True{} : Bool})
  -> {KS.ks.inb(k, E.QNeg{e}) == True{} : Bool}:
  ST.ri.tr(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), ST.lin2(S.Q.neg(DR.qo()), e, DR.qz(), e), E.QNeg{e}, hr, ST.ri.lin(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k), S.Q.neg(DR.qo()), e, DR.qz(), e, hr, h, h),
    ID.qzero_ident(ST.lin2(S.Q.neg(DR.qo()), e, DR.qz(), e), E.QNeg{e}, p => ng.at(p, e)))

# K squared is closed under i
def k2_imul(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +x: SK.VE, +hr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)), h: K2(es, fs, k, x)) -> K2(es, fs, k, DR.imul(x)):
  (+hx, +hy) = h
  (kneg(es, fs, k, SK.VE.y(x), hr, hy), hx)

# The argument
# ------------

def k2.x(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +x: SK.VE, h: K2(es, fs, k, x)) -> {KS.ks.inb(k, SK.VE.x(x)) == True{} : Bool}:
  (a, b) = h
  a

def k2.y(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +x: SK.VE, h: K2(es, fs, k, x)) -> {KS.ks.inb(k, SK.VE.y(x)) == True{} : Bool}:
  (a, b) = h
  b

def ri.r(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, h: ST.RI(B, rows)) -> {EP.rinv(B, rows, 0n) == True{} : Bool}:
  (a, b) = h
  a

def ri.l(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, h: ST.RI(B, rows)) -> {EL.rlen(rows) == SV.neqs(B) : Nat}:
  (a, b) = h
  b

def enc_sym.at(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +r: DR.Node, +ls: List<&2, S.Q>, +xs: List<&2, SK.VE>, +t: Nat)
  -> S.Q.eq(E.qeval(p, SV.lin(ls, CX.imxs(xs, t))), E.qeval(p, HS.enc(DR.imul(HS.clin(es, r, ls, xs)), t))):
  LQ.q_sym(E.qeval(p, HS.enc(DR.imul(HS.clin(es, r, ls, xs)), t)), E.qeval(p, SV.lin(ls, CX.imxs(xs, t))), CX.encim_clin.at(p, es, r, ls, xs, t))

# the hull's kept list is the K part's, then the rest
def cl.xs(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +r: DR.Node) -> {HS.hxs(es, fs, HS.hs.ds(DC.rhull(es, fs, t, s, r))) == vcat(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r))))) : List<&2, SK.VE>}:
  Equal.trans(List<&2, SK.VE>, HS.hxs(es, fs, HS.hs.ds(DC.rhull(es, fs, t, s, r))), HS.hxs(es, fs, DC.dcat(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)), DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r))))), vcat(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r))))),
    Equal.cong(List<&2, DR.Der>, List<&2, SK.VE>, l => HS.hxs(es, fs, l), HS.hs.ds(DC.rhull(es, fs, t, s, r)), DC.dcat(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)), DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)))),
      Equal.sym(List<&2, DR.Der>, DC.dcat(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)), DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)))), HS.hs.ds(DC.rhull(es, fs, t, s, r)), pfx_fold(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)), es, fs, t, DC.khull(es, fs, t, DC.Sk.k(s), r), pfx_self(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))))),
    hxs_cat(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)), DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r))), es, fs))

def cl.sv1(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +r: DR.Node, +y: SK.VE, +nu: List<&2, S.Q>, sv1: VD.SameVD(y, HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.rhull(es, fs, t, s, r))))))
  -> VD.SameVD(y, HS.clin(es, r, nu, vcat(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r))))))):
  %cl.xs(es, fs, t, s, r) : VD.SameVD(y, HS.clin(es, r, nu, _))
  sv1

def cl.ind(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +r: DR.Node, hclx: {DC.clx(es, fs, t, s, r) == None{} : Maybe<&2, DR.Der>})
  -> {IS.indset(CX.imxs(HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)))), t), HS.hs.rows(DC.rhull(es, fs, t, s, r))) == True{} : Bool}:
  %CX.imx_xs(es, fs, t, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)))) : {IS.indset(_, HS.hs.rows(DC.rhull(es, fs, t, s, r))) == True{} : Bool}
  clgo_ind(DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r))), es, fs, t, r, DC.rhull(es, fs, t, s, r), DC.Sk.k(s), HS.hs.rows(DC.rhull(es, fs, t, s, r)), HS.encs(HS.hxs(es, fs, HS.hs.ds(DC.rhull(es, fs, t, s, r))), t), Nil{}, hclx)

def cl.k2k(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +r: DR.Node, +nu: List<&2, S.Q>, +kr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s)))) -> K2(es, fs, DC.Sk.k(s), HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))))):
  k2_clin(nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), es, fs, DC.Sk.k(s), r, kr, k2v_of(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)), es, fs, DC.Sk.k(s),
    k2_fold(DC.kgens(r, KS.ks.ds(DC.Sk.k(s))), es, fs, t, DC.Sk.k(s), HS.hs0(), Unit{}, k2_kgens(KS.ks.ds(DC.Sk.k(s)), es, fs, DC.Sk.k(s), r, kr, ain_all(KS.ks.ds(DC.Sk.k(s)), es, fs)))))

def cl.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +r: DR.Node, +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: RP.MsNz(DC.Sk.ms(s)), +hlsn: RP.LsNz(DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}, +hclx: {DC.clx(es, fs, t, s, r) == None{} : Maybe<&2, DR.Der>},
  +y: SK.VE, +nu: List<&2, S.Q>, +svy: VD.SameVD(y, DR.vlin(DR.qo(), HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), DR.qo(), HS.clin(es, r, PT.qdrop(vlen(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), nu), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r))))))), +h2: ST.HIn(es, fs, r, DC.rhull(es, fs, t, s, r), DR.imul(y)), +kr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(DC.Sk.k(s))), KS.ks.rows(DC.Sk.k(s))), +k2K: K2(es, fs, DC.Sk.k(s), HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))))) -> K2(es, fs, DC.Sk.k(s), y):
  k2_kv(es, fs, DC.Sk.k(s), y, HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), kr,
    GN.samevd_tr(y, DR.vlin(DR.qo(), HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), DR.qo(), HS.clin(es, r, PT.qdrop(vlen(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), nu), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)))))), HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), svy,
      GN.samevd_tr(DR.vlin(DR.qo(), HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), DR.qo(), HS.clin(es, r, PT.qdrop(vlen(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), nu), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)))))), DR.vlin(DR.qo(), HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), DR.qo(), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r))), HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))),
        ST.vcong(DR.qo(), HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), DR.qo(), HS.clin(es, r, PT.qdrop(vlen(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), nu), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r))))), DR.vlin(DR.qz(), DR.zdir(es, r), DR.qz(), DR.zdir(es, r)), MG.samevd_refl(HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))))),
          clin_zero(PT.qdrop(vlen(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), nu), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)))), es, r, t,
            IP.indset_ok(CX.imxs(HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)))), t), HS.encs(HS.hxs(es, fs, HS.hs.ds(DC.rhull(es, fs, t, s, r))), t), HS.hs.rows(DC.rhull(es, fs, t, s, r)), ri.r(HS.encs(HS.hxs(es, fs, HS.hs.ds(DC.rhull(es, fs, t, s, r))), t), HS.hs.rows(DC.rhull(es, fs, t, s, r)), ST.hri(es, fs, ctx, r, t, DC.rhull(es, fs, t, s, r), GN.rhull_inv(es, fs, ctx, t, s, r, hk, hms, hls, hz, hb))), ri.l(HS.encs(HS.hxs(es, fs, HS.hs.ds(DC.rhull(es, fs, t, s, r))), t), HS.hs.rows(DC.rhull(es, fs, t, s, r)), ST.hri(es, fs, ctx, r, t, DC.rhull(es, fs, t, s, r), GN.rhull_inv(es, fs, ctx, t, s, r, hk, hms, hls, hz, hb))), cl.ind(es, fs, t, s, r, hclx), PT.qdrop(vlen(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), nu),
              PP.in_tr(HS.enc(DR.imul(HS.clin(es, r, PT.qdrop(vlen(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), nu), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)))))), t), SV.lin(PT.qdrop(vlen(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), nu), CX.imxs(HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)))), t)), HS.encs(HS.hxs(es, fs, HS.hs.ds(DC.rhull(es, fs, t, s, r))), t),
                LS.hin_span(es, fs, r, t, DC.rhull(es, fs, t, s, r), DR.imul(HS.clin(es, r, PT.qdrop(vlen(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), nu), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)))))),
                  ST.hin_tr(es, fs, r, DC.rhull(es, fs, t, s, r), DR.vlin(DR.qo(), DR.imul(y), S.Q.neg(DR.qo()), DR.imul(HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))))), DR.imul(HS.clin(es, r, PT.qdrop(vlen(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), nu), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)))))),
                    ST.hin_lin(es, fs, r, DC.rhull(es, fs, t, s, r), DR.qo(), DR.imul(y), S.Q.neg(DR.qo()), DR.imul(HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))))), h2,
                      ND.k2_in(es, fs, t, DC.Sk.k(s), ST.SH{DC.rhull(es, fs, t, s, r), r}, DR.imul(HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))))), ND.sok_root.go(False{}, es, fs, ctx, t, s, r, hk, hms, hls, hmsn, hlsn, hz, hb), kr,
                        k2.x(es, fs, DC.Sk.k(s), DR.imul(HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))))), k2_imul(es, fs, DC.Sk.k(s), HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), kr, k2K)), k2.y(es, fs, DC.Sk.k(s), DR.imul(HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))))), k2_imul(es, fs, DC.Sk.k(s), HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), kr, k2K)))),
                    GN.samevd_tr(DR.vlin(DR.qo(), DR.imul(y), S.Q.neg(DR.qo()), DR.imul(HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))))), DR.vlin(DR.qo(), DR.imul(DR.vlin(DR.qo(), HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), DR.qo(), HS.clin(es, r, PT.qdrop(vlen(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), nu), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r))))))), S.Q.neg(DR.qo()), DR.imul(HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))))), DR.imul(HS.clin(es, r, PT.qdrop(vlen(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), nu), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)))))),
                      ST.vcong(DR.qo(), DR.imul(y), DR.imul(DR.vlin(DR.qo(), HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), DR.qo(), HS.clin(es, r, PT.qdrop(vlen(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), nu), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r))))))), S.Q.neg(DR.qo()), DR.imul(HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))))), DR.imul(HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))))), imul_cong(y, DR.vlin(DR.qo(), HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), DR.qo(), HS.clin(es, r, PT.qdrop(vlen(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), nu), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)))))), svy), MG.samevd_refl(DR.imul(HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))))))),
                      isub(HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), HS.clin(es, r, PT.qdrop(vlen(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), nu), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r))))))))),
                p => enc_sym.at(p, es, r, PT.qdrop(vlen(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), nu), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)))), t))))),
        vb1(HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), es, r))),
    k2.x(es, fs, DC.Sk.k(s), HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), k2K), k2.y(es, fs, DC.Sk.k(s), HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), k2K))

def cl.nu(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +r: DR.Node, +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: RP.MsNz(DC.Sk.ms(s)), +hlsn: RP.LsNz(DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}, +hclx: {DC.clx(es, fs, t, s, r) == None{} : Maybe<&2, DR.Der>},
  +y: SK.VE, +nu: List<&2, S.Q>, +sv1: VD.SameVD(y, HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.rhull(es, fs, t, s, r))))), +h2: ST.HIn(es, fs, r, DC.rhull(es, fs, t, s, r), DR.imul(y))) -> K2(es, fs, DC.Sk.k(s), y):
  cl.go(es, fs, ctx, t, s, r, hk, hms, hls, hmsn, hlsn, hz, hb, hclx, y, nu,
    GN.samevd_tr(y, HS.clin(es, r, nu, vcat(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)))))), DR.vlin(DR.qo(), HS.clin(es, r, nu, HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), DR.qo(), HS.clin(es, r, PT.qdrop(vlen(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r)))), nu), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)))))), cl.sv1(es, fs, t, s, r, y, nu, sv1), clin_cat(HS.hxs(es, fs, HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hxs(es, fs, DC.ddrop(DC.dlen(HS.hs.ds(DC.khull(es, fs, t, DC.Sk.k(s), r))), HS.hs.ds(DC.rhull(es, fs, t, s, r)))), es, r, nu)),
    h2, ST.kri(es, fs, ctx, t, DC.Sk.k(s), hk), cl.k2k(es, fs, t, s, r, nu, ST.kri(es, fs, ctx, t, DC.Sk.k(s), hk)))

# no complex line at a free root whose check found nothing: y and i y in
# its set put both parts of y in K
def cline(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +r: DR.Node, +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: RP.MsNz(DC.Sk.ms(s)), +hlsn: RP.LsNz(DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool}, +hclx: {DC.clx(es, fs, t, s, r) == None{} : Maybe<&2, DR.Der>},
  +y: SK.VE, h1: ST.HIn(es, fs, r, DC.rhull(es, fs, t, s, r), y), +h2: ST.HIn(es, fs, r, DC.rhull(es, fs, t, s, r), DR.imul(y))) -> K2(es, fs, DC.Sk.k(s), y):
  (+nu, +sv1) = h1
  cl.nu(es, fs, ctx, t, s, r, hk, hms, hls, hmsn, hlsn, hz, hb, hclx, y, nu, sv1, h2)
