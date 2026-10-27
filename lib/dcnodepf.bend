# bend-cad: the closure theorem's node sets (PLAN-sk13b B3): K's generators
# are in every rebuilt hull and tied set (they enter first), so each set
# holds K squared; the generators of each node are in its set.
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
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./hspacepf.bend as HP
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcinvpf.bend as IV
import ./dcbelowpf.bend as BL
import ./dcgenpf.bend as GN
import ./dcmergepf.bend as MG
import ./dcreppf.bend as RP
import ./dcsetpf.bend as ST

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Folds of concatenations
# -----------------------

def hfold_cat(xs: List<&2, DR.Der>, +ys: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS)
  -> {DC.hfold(DC.dcat(xs, ys), es, fs, t, h) == DC.hfold(ys, es, fs, t, DC.hfold(xs, es, fs, t, h)) : HS.HS}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, xt}:
      hfold_cat(xt, ys, es, fs, t, HS.hs.add(es, fs, t, h, x))

def tfold_cat(xs: List<&2, DR.Der>, +ys: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +s: DC.TS)
  -> {DC.tfold(DC.dcat(xs, ys), es, fs, u, s) == DC.tfold(ys, es, fs, u, DC.tfold(xs, es, fs, u, s)) : DC.TS}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, xt}:
      tfold_cat(xt, ys, es, fs, u, DC.ts.add(es, fs, u, s, x))

# K's generators as forms
# -----------------------

def kv.x(+Z: S.Q, +X: S.Q) -> S.Q.eq(S.Q.add(S.Q.add(S.Q.mul(DR.qz(), Z), S.Q.mul(DR.qz(), Z)), X), X):
  QR.qring_eq([Z, X], E.QAdd{E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}}, E.QVar{1n}}, E.QVar{1n}, {==})

def kv.z(+Z: S.Q) -> S.Q.eq(S.Q.add(S.Q.add(S.Q.mul(DR.qz(), Z), S.Q.mul(DR.qz(), Z)), DR.qz()), DR.qz()):
  QR.qring_eq([Z], E.QAdd{E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}}, E.QCst{DR.qz()}}, E.QCst{DR.qz()}, {==})

def kv.ax(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +r: DR.Node, +d: DR.Der)
  -> S.Q.eq(S.Q.add(S.Q.add(S.Q.mul(DR.qz(), E.qeval(p, SK.VE.x(DR.zdir(es, r)))), S.Q.mul(DR.qz(), E.qeval(p, SK.VE.x(DR.zdir(es, r))))), E.qeval(p, DR.Jd.e(DR.concl(es, fs, d)))), E.qeval(p, DR.Jd.e(DR.concl(es, fs, d)))):
  kv.x(E.qeval(p, SK.VE.x(DR.zdir(es, r))), E.qeval(p, DR.Jd.e(DR.concl(es, fs, d))))

def kv.ay(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +r: DR.Node, +d: DR.Der)
  -> S.Q.eq(S.Q.add(S.Q.add(S.Q.mul(DR.qz(), E.qeval(p, SK.VE.y(DR.zdir(es, r)))), S.Q.mul(DR.qz(), E.qeval(p, SK.VE.y(DR.zdir(es, r))))), E.qeval(p, DR.Jd.e(DR.concl(es, fs, d)))), E.qeval(p, DR.Jd.e(DR.concl(es, fs, d)))):
  kv.x(E.qeval(p, SK.VE.y(DR.zdir(es, r))), E.qeval(p, DR.Jd.e(DR.concl(es, fs, d))))

# kre's form is (e, 0)
def kre_v(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +r: DR.Node, +d: DR.Der) -> VD.SameVD(DR.Jd.x(DR.concl(es, fs, HS.kre(r, d))), ST.kv.re(DR.Jd.e(DR.concl(es, fs, d)))):
  (ID.qzero_ident(SK.VE.x(DR.Jd.x(DR.concl(es, fs, HS.kre(r, d)))), DR.Jd.e(DR.concl(es, fs, d)), p => kv.ax(p, es, fs, r, d)),
   ID.qzero_ident(SK.VE.y(DR.Jd.x(DR.concl(es, fs, HS.kre(r, d)))), DR.zeroe(), p => kv.z(E.qeval(p, SK.VE.y(DR.zdir(es, r))))))

# kim's form is (0, e)
def kim_v(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +r: DR.Node, +d: DR.Der) -> VD.SameVD(DR.Jd.x(DR.concl(es, fs, HS.kim(r, d))), ST.kv.im(DR.Jd.e(DR.concl(es, fs, d)))):
  (ID.qzero_ident(SK.VE.x(DR.Jd.x(DR.concl(es, fs, HS.kim(r, d)))), DR.zeroe(), p => kv.z(E.qeval(p, SK.VE.x(DR.zdir(es, r))))),
   ID.qzero_ident(SK.VE.y(DR.Jd.x(DR.concl(es, fs, HS.kim(r, d)))), DR.Jd.e(DR.concl(es, fs, d)), p => kv.ay(p, es, fs, r, d)))

def pgd.below(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +d: DR.Der, h: IV.PGenD(es, fs, ctx, r, t, d)) -> HP.VBelow(DR.Jd.x(DR.concl(es, fs, d)), t):
  (v, r1) = h
  (i, r2) = r1
  (e, b) = r2
  b

def apk.re(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +d: DR.Der, +tl: List<&2, DR.Der>, h: IV.AllPD(es, fs, ctx, r, t, DC.kgens(r, Con{d, tl})))
  -> IV.PGenD(es, fs, ctx, r, t, HS.kre(r, d)):
  (a, r1) = h
  a

def apk.im(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +d: DR.Der, +tl: List<&2, DR.Der>, h: IV.AllPD(es, fs, ctx, r, t, DC.kgens(r, Con{d, tl})))
  -> IV.PGenD(es, fs, ctx, r, t, HS.kim(r, d)):
  (a, r1) = h
  (b, c) = r1
  b

def apk.tl(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +d: DR.Der, +tl: List<&2, DR.Der>, h: IV.AllPD(es, fs, ctx, r, t, DC.kgens(r, Con{d, tl})))
  -> IV.AllPD(es, fs, ctx, r, t, DC.kgens(r, tl)):
  (a, r1) = h
  (b, c) = r1
  c

# K's generators d pass H, through their kre and kim derivations
def KGh(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +r: DR.Node, +H: HS.HS, ds: List<&2, DR.Der>) -> Data:
  match ds:
    case Nil{}:
      Unit
    case Con{+d, +tl}:
      SK.Both({HS.hs.inb(H, DR.Jd.x(DR.concl(es, fs, HS.kre(r, d))), t) == True{} : Bool}, SK.Both({HS.hs.inb(H, DR.Jd.x(DR.concl(es, fs, HS.kim(r, d))), t) == True{} : Bool}, KGh(es, fs, t, r, H, tl)))

def kgh.re(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +r: DR.Node, +H: HS.HS, +d: DR.Der, +tl: List<&2, DR.Der>, h: KGh(es, fs, t, r, H, Con{d, tl})) -> {HS.hs.inb(H, DR.Jd.x(DR.concl(es, fs, HS.kre(r, d))), t) == True{} : Bool}:
  (a, r1) = h
  a

def kgh.im(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +r: DR.Node, +H: HS.HS, +d: DR.Der, +tl: List<&2, DR.Der>, h: KGh(es, fs, t, r, H, Con{d, tl})) -> {HS.hs.inb(H, DR.Jd.x(DR.concl(es, fs, HS.kim(r, d))), t) == True{} : Bool}:
  (a, r1) = h
  (b, c) = r1
  b

def kgh.tl(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +r: DR.Node, +H: HS.HS, +d: DR.Der, +tl: List<&2, DR.Der>, h: KGh(es, fs, t, r, H, Con{d, tl})) -> KGh(es, fs, t, r, H, tl):
  (a, r1) = h
  (b, c) = r1
  c

# K's generators folded in first stay in, whatever is folded in after
def kgh_fold(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +r: DR.Node, +h: HS.HS, +more: List<&2, DR.Der>, +hr: ST.RI(HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), HS.hs.rows(h)))
  -> KGh(es, fs, t, r, DC.hfold(more, es, fs, t, DC.hfold(DC.kgens(r, ds), es, fs, t, h)), ds):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, +tl}:
      (ST.hs_fold_mono(more, es, fs, t, DC.hfold(DC.kgens(r, tl), es, fs, t, HS.hs.add(es, fs, t, HS.hs.add(es, fs, t, h, HS.kre(r, d)), HS.kim(r, d))), HS.enc(DR.Jd.x(DR.concl(es, fs, HS.kre(r, d))), t), ST.hs_fold_ri(DC.kgens(r, tl), es, fs, t, HS.hs.add(es, fs, t, HS.hs.add(es, fs, t, h, HS.kre(r, d)), HS.kim(r, d)), ST.hs_add_ri(es, fs, t, HS.hs.add(es, fs, t, h, HS.kre(r, d)), HS.kim(r, d), ST.hs_add_ri(es, fs, t, h, HS.kre(r, d), hr))),
         ST.hs_fold_mono(DC.kgens(r, tl), es, fs, t, HS.hs.add(es, fs, t, HS.hs.add(es, fs, t, h, HS.kre(r, d)), HS.kim(r, d)), HS.enc(DR.Jd.x(DR.concl(es, fs, HS.kre(r, d))), t), ST.hs_add_ri(es, fs, t, HS.hs.add(es, fs, t, h, HS.kre(r, d)), HS.kim(r, d), ST.hs_add_ri(es, fs, t, h, HS.kre(r, d), hr)),
           ST.hs_add_mono(es, fs, t, HS.hs.add(es, fs, t, h, HS.kre(r, d)), HS.kim(r, d), HS.enc(DR.Jd.x(DR.concl(es, fs, HS.kre(r, d))), t), ST.hs_add_ri(es, fs, t, h, HS.kre(r, d), hr), ST.hs_add_new(es, fs, t, h, HS.kre(r, d), hr)))),
       (ST.hs_fold_mono(more, es, fs, t, DC.hfold(DC.kgens(r, tl), es, fs, t, HS.hs.add(es, fs, t, HS.hs.add(es, fs, t, h, HS.kre(r, d)), HS.kim(r, d))), HS.enc(DR.Jd.x(DR.concl(es, fs, HS.kim(r, d))), t), ST.hs_fold_ri(DC.kgens(r, tl), es, fs, t, HS.hs.add(es, fs, t, HS.hs.add(es, fs, t, h, HS.kre(r, d)), HS.kim(r, d)), ST.hs_add_ri(es, fs, t, HS.hs.add(es, fs, t, h, HS.kre(r, d)), HS.kim(r, d), ST.hs_add_ri(es, fs, t, h, HS.kre(r, d), hr))),
          ST.hs_fold_mono(DC.kgens(r, tl), es, fs, t, HS.hs.add(es, fs, t, HS.hs.add(es, fs, t, h, HS.kre(r, d)), HS.kim(r, d)), HS.enc(DR.Jd.x(DR.concl(es, fs, HS.kim(r, d))), t), ST.hs_add_ri(es, fs, t, HS.hs.add(es, fs, t, h, HS.kre(r, d)), HS.kim(r, d), ST.hs_add_ri(es, fs, t, h, HS.kre(r, d), hr)),
            ST.hs_add_new(es, fs, t, HS.hs.add(es, fs, t, h, HS.kre(r, d)), HS.kim(r, d), ST.hs_add_ri(es, fs, t, h, HS.kre(r, d), hr)))),
        kgh_fold(tl, es, fs, t, r, HS.hs.add(es, fs, t, HS.hs.add(es, fs, t, h, HS.kre(r, d)), HS.kim(r, d)), more, ST.hs_add_ri(es, fs, t, HS.hs.add(es, fs, t, h, HS.kre(r, d)), HS.kim(r, d), ST.hs_add_ri(es, fs, t, h, HS.kre(r, d), hr)))))

# K's generators d pass H, through their kre and kim derivations
def KGt(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +r: DR.Node, +H: DC.TS, ds: List<&2, DR.Der>) -> Data:
  match ds:
    case Nil{}:
      Unit
    case Con{+d, +tl}:
      SK.Both({DC.ts.inb(H, u, DR.Jd.x(DR.concl(es, fs, HS.kre(r, d)))) == True{} : Bool}, SK.Both({DC.ts.inb(H, u, DR.Jd.x(DR.concl(es, fs, HS.kim(r, d)))) == True{} : Bool}, KGt(es, fs, u, r, H, tl)))

def kgt.re(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +r: DR.Node, +H: DC.TS, +d: DR.Der, +tl: List<&2, DR.Der>, h: KGt(es, fs, u, r, H, Con{d, tl})) -> {DC.ts.inb(H, u, DR.Jd.x(DR.concl(es, fs, HS.kre(r, d)))) == True{} : Bool}:
  (a, r1) = h
  a

def kgt.im(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +r: DR.Node, +H: DC.TS, +d: DR.Der, +tl: List<&2, DR.Der>, h: KGt(es, fs, u, r, H, Con{d, tl})) -> {DC.ts.inb(H, u, DR.Jd.x(DR.concl(es, fs, HS.kim(r, d)))) == True{} : Bool}:
  (a, r1) = h
  (b, c) = r1
  b

def kgt.tl(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +r: DR.Node, +H: DC.TS, +d: DR.Der, +tl: List<&2, DR.Der>, h: KGt(es, fs, u, r, H, Con{d, tl})) -> KGt(es, fs, u, r, H, tl):
  (a, r1) = h
  (b, c) = r1
  c

# K's generators folded in first stay in, whatever is folded in after
def kgt_fold(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +r: DR.Node, +h: DC.TS, +more: List<&2, DR.Der>, +hr: ST.RI(DC.crosses(es, fs, u, DC.ts.ds(h)), DC.ts.rows(h)))
  -> KGt(es, fs, u, r, DC.tfold(more, es, fs, u, DC.tfold(DC.kgens(r, ds), es, fs, u, h)), ds):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, +tl}:
      (ST.ts_fold_mono(more, es, fs, u, DC.tfold(DC.kgens(r, tl), es, fs, u, DC.ts.add(es, fs, u, DC.ts.add(es, fs, u, h, HS.kre(r, d)), HS.kim(r, d))), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, HS.kre(r, d)))), ST.ts_fold_ri(DC.kgens(r, tl), es, fs, u, DC.ts.add(es, fs, u, DC.ts.add(es, fs, u, h, HS.kre(r, d)), HS.kim(r, d)), ST.ts_add_ri(es, fs, u, DC.ts.add(es, fs, u, h, HS.kre(r, d)), HS.kim(r, d), ST.ts_add_ri(es, fs, u, h, HS.kre(r, d), hr))),
         ST.ts_fold_mono(DC.kgens(r, tl), es, fs, u, DC.ts.add(es, fs, u, DC.ts.add(es, fs, u, h, HS.kre(r, d)), HS.kim(r, d)), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, HS.kre(r, d)))), ST.ts_add_ri(es, fs, u, DC.ts.add(es, fs, u, h, HS.kre(r, d)), HS.kim(r, d), ST.ts_add_ri(es, fs, u, h, HS.kre(r, d), hr)),
           ST.ts_add_mono(es, fs, u, DC.ts.add(es, fs, u, h, HS.kre(r, d)), HS.kim(r, d), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, HS.kre(r, d)))), ST.ts_add_ri(es, fs, u, h, HS.kre(r, d), hr), ST.ts_add_new(es, fs, u, h, HS.kre(r, d), hr)))),
       (ST.ts_fold_mono(more, es, fs, u, DC.tfold(DC.kgens(r, tl), es, fs, u, DC.ts.add(es, fs, u, DC.ts.add(es, fs, u, h, HS.kre(r, d)), HS.kim(r, d))), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, HS.kim(r, d)))), ST.ts_fold_ri(DC.kgens(r, tl), es, fs, u, DC.ts.add(es, fs, u, DC.ts.add(es, fs, u, h, HS.kre(r, d)), HS.kim(r, d)), ST.ts_add_ri(es, fs, u, DC.ts.add(es, fs, u, h, HS.kre(r, d)), HS.kim(r, d), ST.ts_add_ri(es, fs, u, h, HS.kre(r, d), hr))),
          ST.ts_fold_mono(DC.kgens(r, tl), es, fs, u, DC.ts.add(es, fs, u, DC.ts.add(es, fs, u, h, HS.kre(r, d)), HS.kim(r, d)), SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, HS.kim(r, d)))), ST.ts_add_ri(es, fs, u, DC.ts.add(es, fs, u, h, HS.kre(r, d)), HS.kim(r, d), ST.ts_add_ri(es, fs, u, h, HS.kre(r, d), hr)),
            ST.ts_add_new(es, fs, u, DC.ts.add(es, fs, u, h, HS.kre(r, d)), HS.kim(r, d), ST.ts_add_ri(es, fs, u, h, HS.kre(r, d), hr)))),
        kgt_fold(tl, es, fs, u, r, DC.ts.add(es, fs, u, DC.ts.add(es, fs, u, h, HS.kre(r, d)), HS.kim(r, d)), more, ST.ts_add_ri(es, fs, u, DC.ts.add(es, fs, u, h, HS.kre(r, d)), HS.kim(r, d), ST.ts_add_ri(es, fs, u, h, HS.kre(r, d), hr)))))

# The K generators' facts in the sets' terms
# ------------------------------------------

def kg_of_h(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +k: KS.KS, +r: DR.Node, +H: HS.HS,
  +hr: ST.RI(HS.encs(HS.hxs(es, fs, HS.hs.ds(H)), t), HS.hs.rows(H)), +hb: HP.AllBelow(HS.hxs(es, fs, HS.hs.ds(H)), t), +hzr: HP.VBelow(DR.zdir(es, r), t),
  +kg: KGh(es, fs, t, r, H, ds), +ap: IV.AllPD(es, fs, ctx, r, t, DC.kgens(r, ds))) -> ST.KG(es, fs, k, ST.SH{H, r}, ds):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, +tl}:
      (ST.hin_tr(es, fs, r, H, DR.Jd.x(DR.concl(es, fs, HS.kre(r, d))), ST.kv.re(DR.Jd.e(DR.concl(es, fs, d))),
         ST.hin_of(es, fs, r, t, H, DR.Jd.x(DR.concl(es, fs, HS.kre(r, d))), hr, hb, hzr, pgd.below(es, fs, ctx, r, t, HS.kre(r, d), apk.re(es, fs, ctx, r, t, d, tl, ap)), kgh.re(es, fs, t, r, H, d, tl, kg)),
         kre_v(es, fs, r, d)),
       (ST.hin_tr(es, fs, r, H, DR.Jd.x(DR.concl(es, fs, HS.kim(r, d))), ST.kv.im(DR.Jd.e(DR.concl(es, fs, d))),
          ST.hin_of(es, fs, r, t, H, DR.Jd.x(DR.concl(es, fs, HS.kim(r, d))), hr, hb, hzr, pgd.below(es, fs, ctx, r, t, HS.kim(r, d), apk.im(es, fs, ctx, r, t, d, tl, ap)), kgh.im(es, fs, t, r, H, d, tl, kg)),
          kim_v(es, fs, r, d)),
        kg_of_h(tl, es, fs, ctx, t, k, r, H, hr, hb, hzr, kgh.tl(es, fs, t, r, H, d, tl, kg), apk.tl(es, fs, ctx, r, t, d, tl, ap))))

def kg_of_t(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +r: DR.Node, +u: DR.Lab, +H: DC.TS,
  +hr: ST.RI(DC.crosses(es, fs, u, DC.ts.ds(H)), DC.ts.rows(H)), +kg: KGt(es, fs, u, r, H, ds)) -> ST.KG(es, fs, k, ST.ST{u, H}, ds):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, +tl}:
      (ST.tin_tr(es, fs, u, H, DR.Jd.x(DR.concl(es, fs, HS.kre(r, d))), ST.kv.re(DR.Jd.e(DR.concl(es, fs, d))), hr, kgt.re(es, fs, u, r, H, d, tl, kg), kre_v(es, fs, r, d)),
       (ST.tin_tr(es, fs, u, H, DR.Jd.x(DR.concl(es, fs, HS.kim(r, d))), ST.kv.im(DR.Jd.e(DR.concl(es, fs, d))), hr, kgt.im(es, fs, u, r, H, d, tl, kg), kim_v(es, fs, r, d)),
        kg_of_t(tl, es, fs, k, r, u, H, hr, kgt.tl(es, fs, u, r, H, d, tl, kg))))
