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

# The nodes' sets
# ---------------

def rset.go(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +r: DR.Node) -> ST.St:
  match f:
    case True{}:
      ST.SF{}
    case False{}:
      ST.SH{DC.rhull(es, fs, t, s, r), r}

# a root's set: F's is {y : Im y in K}, another's its hull's combinations
def rset(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +s: DC.Sk, +r: DR.Node) -> ST.St:
  rset.go(DC.node_eq(r, DR.NFrame{}), es, fs, t, s, r)

# a collapsed segment's set
def cset(rep: DC.Rep, +c: Nat) -> ST.St:
  match rep:
    case DC.RFull{}:
      ST.SA{}
    case DC.RFree{+h}:
      ST.SH{h, DR.NSeg{c}}
    case DC.RTied{+u, du, +ts}:
      ST.ST{u, ts}

# what a set needs to hold K squared, beyond its rows
def SOk(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, st: ST.St) -> Data:
  match st:
    case ST.SF{}:
      ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k))
    case ST.SH{+h, +r}:
      ST.KG(es, fs, k, ST.SH{h, r}, KS.ks.ds(k))
    case ST.ST{+u, +ts}:
      SK.Both(ST.RI(DC.crosses(es, fs, u, DC.ts.ds(ts)), DC.ts.rows(ts)), ST.KG(es, fs, k, ST.ST{u, ts}, KS.ks.ds(k)))
    case ST.SA{}:
      Unit

def sok_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, st: ST.St, +h: SOk(es, fs, t, k, st)) -> ST.StOk(es, fs, t, k, st):
  match st:
    case ST.SF{}:
      h
    case ST.SH{+hh, +r}:
      Unit{}
    case ST.ST{+u, +ts}:
      (a, b) = h
      a
    case ST.SA{}:
      Unit{}

# a form with both parts in K is in every node's set
def k2_in(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, st: ST.St, +y: SK.VE, +sok: SOk(es, fs, t, k, st), +kr: ST.RI(KS.kexprs(es, fs, KS.ks.ds(k)), KS.ks.rows(k)),
  hre: {KS.ks.inb(k, SK.VE.x(y)) == True{} : Bool}, him: {KS.ks.inb(k, SK.VE.y(y)) == True{} : Bool}) -> ST.InSt(es, fs, k, st, y):
  match st:
    case ST.SF{}:
      him
    case ST.SH{+hh, +r}:
      ST.st_k2(es, fs, t, k, ST.SH{hh, r}, y, Unit{}, kr, sok, hre, him)
    case ST.ST{+u, +ts}:
      (+a, +b) = sok
      ST.st_k2(es, fs, t, k, ST.ST{u, ts}, y, a, kr, b, hre, him)
    case ST.SA{}:
      Unit{}

def sok_root.go(f: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +r: DR.Node, +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: RP.MsNz(DC.Sk.ms(s)), +hlsn: RP.LsNz(DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> SOk(es, fs, t, DC.Sk.k(s), rset.go(f, es, fs, t, s, r)):
  match f:
    case True{}:
      ST.kri(es, fs, ctx, t, DC.Sk.k(s), hk)
    case False{}:
      kg_of_h(KS.ks.ds(DC.Sk.k(s)), es, fs, ctx, t, DC.Sk.k(s), r, DC.rhull(es, fs, t, s, r),
        ST.hri(es, fs, ctx, r, t, DC.rhull(es, fs, t, s, r), GN.rhull_inv(es, fs, ctx, t, s, r, hk, hms, hls, hz, hb)), ST.hbelow(es, fs, ctx, r, t, DC.rhull(es, fs, t, s, r), GN.rhull_inv(es, fs, ctx, t, s, r, hk, hms, hls, hz, hb)),
        BL.zdir_below(es, t, r, hz),
        kgh_fold(KS.ks.ds(DC.Sk.k(s)), es, fs, t, r, HS.hs0(), DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), ST.hri(es, fs, ctx, r, t, HS.hs0(), IV.hs0_invd(es, fs, ctx, r, t))),
        RP.kgens_of(DC.Sk.k(s), es, fs, ctx, t, r, hk, BL.zdir_below(es, t, r, hz)))

# a root's set holds K squared
def sok_root(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +r: DR.Node, +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: RP.MsNz(DC.Sk.ms(s)), +hlsn: RP.LsNz(DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> SOk(es, fs, t, DC.Sk.k(s), rset(es, fs, t, s, r)):
  sok_root.go(DC.node_eq(r, DR.NFrame{}), es, fs, ctx, t, s, r, hk, hms, hls, hmsn, hlsn, hz, hb)

def sok_coll.t(m: Maybe<&2, DC.LD>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +c: Nat, +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: RP.MsNz(DC.Sk.ms(s)), +hlsn: RP.LsNz(DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> SOk(es, fs, t, DC.Sk.k(s), cset(DC.crep.t(m, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c)):
  match m:
    case None{}:
      kg_of_h(KS.ks.ds(DC.Sk.k(s)), es, fs, ctx, t, DC.Sk.k(s), DR.NSeg{c}, DC.hfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, t, HS.hs0()),
        ST.hri(es, fs, ctx, DR.NSeg{c}, t, DC.hfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, t, HS.hs0()), IV.hfold_inv(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, ctx, DR.NSeg{c}, t, HS.hs0(), IV.hs0_invd(es, fs, ctx, DR.NSeg{c}, t), IV.allpd_cat(es, fs, ctx, DR.NSeg{c}, t, DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c), RP.kgens_of(DC.Sk.k(s), es, fs, ctx, t, DR.NSeg{c}, hk, BL.zdir_below(es, t, DR.NSeg{c}, hz)), RP.cgens_ok(es, fs, ctx, t, s, c, hms, hls, hz, hb)))), ST.hbelow(es, fs, ctx, DR.NSeg{c}, t, DC.hfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, t, HS.hs0()), IV.hfold_inv(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, ctx, DR.NSeg{c}, t, HS.hs0(), IV.hs0_invd(es, fs, ctx, DR.NSeg{c}, t), IV.allpd_cat(es, fs, ctx, DR.NSeg{c}, t, DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c), RP.kgens_of(DC.Sk.k(s), es, fs, ctx, t, DR.NSeg{c}, hk, BL.zdir_below(es, t, DR.NSeg{c}, hz)), RP.cgens_ok(es, fs, ctx, t, s, c, hms, hls, hz, hb)))), BL.zdir_below(es, t, DR.NSeg{c}, hz),
        %Equal.sym(HS.HS, DC.hfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, t, HS.hs0()), DC.hfold(DC.cgens(fs, s, c), es, fs, t, DC.hfold(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), es, fs, t, HS.hs0())), hfold_cat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c), es, fs, t, HS.hs0())) : KGh(es, fs, t, DR.NSeg{c}, _, KS.ks.ds(DC.Sk.k(s)))
        kgh_fold(KS.ks.ds(DC.Sk.k(s)), es, fs, t, DR.NSeg{c}, HS.hs0(), DC.cgens(fs, s, c), ST.hri(es, fs, ctx, DR.NSeg{c}, t, HS.hs0(), IV.hs0_invd(es, fs, ctx, DR.NSeg{c}, t))),
        RP.kgens_of(DC.Sk.k(s), es, fs, ctx, t, DR.NSeg{c}, hk, BL.zdir_below(es, t, DR.NSeg{c}, hz)))
    case Some{DC.LD{+u, du}}:
      (ST.tri(es, fs, ctx, DR.NSeg{c}, t, u, DC.tfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, u, DC.TS{Nil{}, Nil{}}), RP.tfold_inv(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, ctx, DR.NSeg{c}, t, u, DC.TS{Nil{}, Nil{}}, ({==}, ({==}, Unit{})), IV.allpd_cat(es, fs, ctx, DR.NSeg{c}, t, DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c), RP.kgens_of(DC.Sk.k(s), es, fs, ctx, t, DR.NSeg{c}, hk, BL.zdir_below(es, t, DR.NSeg{c}, hz)), RP.cgens_ok(es, fs, ctx, t, s, c, hms, hls, hz, hb)))),
       kg_of_t(KS.ks.ds(DC.Sk.k(s)), es, fs, DC.Sk.k(s), DR.NSeg{c}, u, DC.tfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, u, DC.TS{Nil{}, Nil{}}), ST.tri(es, fs, ctx, DR.NSeg{c}, t, u, DC.tfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, u, DC.TS{Nil{}, Nil{}}), RP.tfold_inv(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, ctx, DR.NSeg{c}, t, u, DC.TS{Nil{}, Nil{}}, ({==}, ({==}, Unit{})), IV.allpd_cat(es, fs, ctx, DR.NSeg{c}, t, DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c), RP.kgens_of(DC.Sk.k(s), es, fs, ctx, t, DR.NSeg{c}, hk, BL.zdir_below(es, t, DR.NSeg{c}, hz)), RP.cgens_ok(es, fs, ctx, t, s, c, hms, hls, hz, hb)))),
         %Equal.sym(DC.TS, DC.tfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, u, DC.TS{Nil{}, Nil{}}), DC.tfold(DC.cgens(fs, s, c), es, fs, u, DC.tfold(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), es, fs, u, DC.TS{Nil{}, Nil{}})), tfold_cat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c), es, fs, u, DC.TS{Nil{}, Nil{}})) : KGt(es, fs, u, DR.NSeg{c}, _, KS.ks.ds(DC.Sk.k(s)))
         kgt_fold(KS.ks.ds(DC.Sk.k(s)), es, fs, u, DR.NSeg{c}, DC.TS{Nil{}, Nil{}}, DC.cgens(fs, s, c), ({==}, {==}))))

def sok_coll.f(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +c: Nat, +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: RP.MsNz(DC.Sk.ms(s)), +hlsn: RP.LsNz(DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> SOk(es, fs, t, DC.Sk.k(s), cset(DC.crep.f(b, es, fs, t, s, c), c)):
  match b:
    case True{}:
      Unit{}
    case False{}:
      sok_coll.t(DC.cties(DC.Sk.ls(s), c, DC.Sk.ms(s)), es, fs, ctx, t, s, c, hk, hms, hls, hmsn, hlsn, hz, hb)

# a collapsed segment's set holds K squared
def sok_coll(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +c: Nat, +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: RP.MsNz(DC.Sk.ms(s)), +hlsn: RP.LsNz(DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> SOk(es, fs, t, DC.Sk.k(s), cset(DC.crep(es, fs, t, s, c), c)):
  sok_coll.f(DC.fullc(es, DC.Sk.k(s), c), es, fs, ctx, t, s, c, hk, hms, hls, hmsn, hlsn, hz, hb)

# Generators
# ----------

def pgen_at(ds: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, +g: DR.Der, n: Nat,
  en: {ST.dat(ds, n) == Some{g} : Maybe<&2, DR.Der>}, ap: IV.AllPD(es, fs, ctx, r, t, ds)) -> IV.PGenD(es, fs, ctx, r, t, g):
  match ds n:
    case Nil{} n:
      absurd(IV.PGenD(es, fs, ctx, r, t, g), ST.dnone_some(g, en))
    case Con{+d0, tl} 0n:
      (a, rt) = ap
      %ST.dsome_inj(d0, g, en) : IV.PGenD(es, fs, ctx, r, t, _)
      a
    case Con{+d0, tl} 1n+m:
      (a, rt) = ap
      pgen_at(tl, es, fs, ctx, r, t, g, m, en, rt)

def gen_root.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +r: DR.Node, +g: DR.Der, +n: Nat, +en: {ST.dat(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), n) == Some{g} : Maybe<&2, DR.Der>}, +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: RP.MsNz(DC.Sk.ms(s)), +hlsn: RP.LsNz(DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> ST.HIn(es, fs, r, DC.rhull(es, fs, t, s, r), DR.Jd.x(DR.concl(es, fs, g))):
  ST.hin_of(es, fs, r, t, DC.rhull(es, fs, t, s, r), DR.Jd.x(DR.concl(es, fs, g)),
    ST.hri(es, fs, ctx, r, t, DC.rhull(es, fs, t, s, r), GN.rhull_inv(es, fs, ctx, t, s, r, hk, hms, hls, hz, hb)), ST.hbelow(es, fs, ctx, r, t, DC.rhull(es, fs, t, s, r), GN.rhull_inv(es, fs, ctx, t, s, r, hk, hms, hls, hz, hb)),
    BL.zdir_below(es, t, r, hz), pgd.below(es, fs, ctx, r, t, g, pgen_at(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, ctx, r, t, g, n, en, GN.rgens_ok(DC.Sk.ms(s), es, fs, ctx, t, r, DC.Sk.ls(s), hz, hb, hms, hls))),
    ST.hs_fold_in(DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s)), es, fs, t, DC.khull(es, fs, t, DC.Sk.k(s), r), g, n, en, ST.hri(es, fs, ctx, r, t, DC.khull(es, fs, t, DC.Sk.k(s), r), GN.khull_inv(es, fs, ctx, t, DC.Sk.k(s), r, hk, BL.zdir_below(es, t, r, hz)))))

# a root's generators are in its hull's set
def gen_root(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +r: DR.Node, +g: DR.Der, hg: ST.InD(g, DC.rgens(fs, r, DC.Sk.ms(s), DC.Sk.ls(s))), +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: RP.MsNz(DC.Sk.ms(s)), +hlsn: RP.LsNz(DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> ST.HIn(es, fs, r, DC.rhull(es, fs, t, s, r), DR.Jd.x(DR.concl(es, fs, g))):
  (+n, +en) = hg
  gen_root.go(es, fs, ctx, t, s, r, g, n, en, hk, hms, hls, hmsn, hlsn, hz, hb)

def gen_coll.t(m: Maybe<&2, DC.LD>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +c: Nat, +g: DR.Der, +n: Nat,
  +en: {ST.dat(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), n) == Some{g} : Maybe<&2, DR.Der>}, +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: RP.MsNz(DC.Sk.ms(s)), +hlsn: RP.LsNz(DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> ST.InSt(es, fs, DC.Sk.k(s), cset(DC.crep.t(m, es, fs, t, DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c))), c), DR.Jd.x(DR.concl(es, fs, g))):
  match m:
    case None{}:
      ST.hin_of(es, fs, DR.NSeg{c}, t, DC.hfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, t, HS.hs0()), DR.Jd.x(DR.concl(es, fs, g)), ST.hri(es, fs, ctx, DR.NSeg{c}, t, DC.hfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, t, HS.hs0()), IV.hfold_inv(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, ctx, DR.NSeg{c}, t, HS.hs0(), IV.hs0_invd(es, fs, ctx, DR.NSeg{c}, t), IV.allpd_cat(es, fs, ctx, DR.NSeg{c}, t, DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c), RP.kgens_of(DC.Sk.k(s), es, fs, ctx, t, DR.NSeg{c}, hk, BL.zdir_below(es, t, DR.NSeg{c}, hz)), RP.cgens_ok(es, fs, ctx, t, s, c, hms, hls, hz, hb)))), ST.hbelow(es, fs, ctx, DR.NSeg{c}, t, DC.hfold(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, t, HS.hs0()), IV.hfold_inv(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, ctx, DR.NSeg{c}, t, HS.hs0(), IV.hs0_invd(es, fs, ctx, DR.NSeg{c}, t), IV.allpd_cat(es, fs, ctx, DR.NSeg{c}, t, DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c), RP.kgens_of(DC.Sk.k(s), es, fs, ctx, t, DR.NSeg{c}, hk, BL.zdir_below(es, t, DR.NSeg{c}, hz)), RP.cgens_ok(es, fs, ctx, t, s, c, hms, hls, hz, hb)))),
        BL.zdir_below(es, t, DR.NSeg{c}, hz), pgd.below(es, fs, ctx, DR.NSeg{c}, t, g, pgen_at(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, ctx, DR.NSeg{c}, t, g, n, en, IV.allpd_cat(es, fs, ctx, DR.NSeg{c}, t, DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c), RP.kgens_of(DC.Sk.k(s), es, fs, ctx, t, DR.NSeg{c}, hk, BL.zdir_below(es, t, DR.NSeg{c}, hz)), RP.cgens_ok(es, fs, ctx, t, s, c, hms, hls, hz, hb)))),
        ST.hs_fold_in(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, t, HS.hs0(), g, n, en, ST.hri(es, fs, ctx, DR.NSeg{c}, t, HS.hs0(), IV.hs0_invd(es, fs, ctx, DR.NSeg{c}, t))))
    case Some{DC.LD{+u, du}}:
      ST.ts_fold_in(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), es, fs, u, DC.TS{Nil{}, Nil{}}, g, n, en, ({==}, {==}))

def gen_coll.f(b: Bool, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +c: Nat, +g: DR.Der, +n: Nat,
  +en: {ST.dat(DC.dcat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c)), n) == Some{g} : Maybe<&2, DR.Der>}, +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: RP.MsNz(DC.Sk.ms(s)), +hlsn: RP.LsNz(DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> ST.InSt(es, fs, DC.Sk.k(s), cset(DC.crep.f(b, es, fs, t, s, c), c), DR.Jd.x(DR.concl(es, fs, g))):
  match b:
    case True{}:
      Unit{}
    case False{}:
      gen_coll.t(DC.cties(DC.Sk.ls(s), c, DC.Sk.ms(s)), es, fs, ctx, t, s, c, g, n, en, hk, hms, hls, hmsn, hlsn, hz, hb)

def gen_coll.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +c: Nat, +g: DR.Der, +n: Nat, +en: {ST.dat(DC.cgens(fs, s, c), n) == Some{g} : Maybe<&2, DR.Der>}, +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: RP.MsNz(DC.Sk.ms(s)), +hlsn: RP.LsNz(DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> ST.InSt(es, fs, DC.Sk.k(s), cset(DC.crep(es, fs, t, s, c), c), DR.Jd.x(DR.concl(es, fs, g))):
  gen_coll.f(DC.fullc(es, DC.Sk.k(s), c), es, fs, ctx, t, s, c, g, Nat.add(DC.dlen(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s)))), n), ST.dlen_cat(DC.kgens(DR.NSeg{c}, KS.ks.ds(DC.Sk.k(s))), DC.cgens(fs, s, c), n, g, en), hk, hms, hls, hmsn, hlsn, hz, hb)

# a collapsed segment's generators are in its set
def gen_coll(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +s: DC.Sk, +c: Nat, +g: DR.Der, hg: ST.InD(g, DC.cgens(fs, s, c)), +hk: IV.KInvD(es, fs, ctx, t, DC.Sk.k(s)), +hms: GN.MsOk(es, fs, ctx, t, DC.Sk.ms(s)), +hls: GN.LsOk(es, fs, ctx, t, DC.Sk.ls(s)), +hmsn: RP.MsNz(DC.Sk.ms(s)), +hlsn: RP.LsNz(DC.Sk.ls(s)), +hz: {DC.zb(es, t) == True{} : Bool}, +hb: {DC.fb(fs, t) == True{} : Bool})
  -> ST.InSt(es, fs, DC.Sk.k(s), cset(DC.crep(es, fs, t, s, c), c), DR.Jd.x(DR.concl(es, fs, g))):
  (+n, +en) = hg
  gen_coll.go(es, fs, ctx, t, s, c, g, n, en, hk, hms, hls, hmsn, hlsn, hz, hb)
