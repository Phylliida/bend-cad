# bend-cad: the start kept across closure calls (PLAN-sk13b B4.8). A pass
# keeps K from the facts R of its kept constraints and the cache of K's
# rows (lib/dclose.bend: MK); a call whose facts extend R starts from
# them.
# - A derivation's conclusion reads only the facts it cites (concl_pre):
#   where fs agrees with R on each fact's e and statement (Pre), a
#   derivation citing only positions of R (DB) concludes the same over
#   both. So ks.add, kinit, lh.add, lfold, the cache's entries and CInv
#   carry from R to fs, K's derivations citing only positions of R
#   (kinit_below).
# - kinit over X ++ ys is kinit over ys after X (kinit_cat), and mext
#   gives ys to K and its cache by ks.add and kc.add (mext_ok, by
#   lib/dfastpf.bend's kc_add_inv).
# - So R's start, extended by ys, is the start of X ++ ys for any X that
#   agrees with R and has its length (mext_reuse); and dclose from a
#   start of fs returns what dclose returns (dclose_m_eq).
# Proofs only.

import Base
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./dclose.bend as DC
import ./lres.bend as LR
import ./nat.bend as LN
import ./karith.bend as KA
import ./kbpf.bend as KB
import ./dfastpf.bend as FP
import ./ownpf.bend as OW

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Facts that agree
# ----------------

def flen(fs: List<&2, DR.Fact>) -> Nat:
  match fs:
    case Nil{}:
      0n
    case Con{f, t}:
      1n+flen(t)

def fds(f: DR.Fact) -> Maybe<&2, DR.DStat>:
  match f:
    case DR.Fact{e, nd, ds}:
      ds

# what a derivation reads of a fact: its e and its statement (not its nd)
def FAg(+f: DR.Fact, +g: DR.Fact) -> Data:
  SK.Both({DR.fact.e(Some{f}) == DR.fact.e(Some{g}) : E.QExpr}, {fds(f) == fds(g) : Maybe<&2, DR.DStat>})

# fs2 agrees with fs1 at every position of fs1
def Pre(fs1: List<&2, DR.Fact>, fs2: List<&2, DR.Fact>) -> Data:
  match fs1:
    case Nil{}:
      Unit
    case Con{f, t1}:
      match fs2:
        case Nil{}:
          Empty
        case Con{g, t2}:
          SK.Both(FAg(f, g), Pre(t1, t2))

# every position d cites is below n
def DB(d: DR.Der, +n: Nat) -> Data:
  match d:
    case DR.DZero{}:
      Unit
    case DR.DPrem{i}:
      {SV.lt(i, n) == True{} : Bool}
    case DR.DKAdd{l, d1, d2}:
      SK.Both(DB(d1, n), DB(d2, n))
    case DR.DBack{d0}:
      DB(d0, n)
    case DR.DLine{d1, d2, re}:
      SK.Both(DB(d1, n), DB(d2, n))
    case DR.DPPrem{i}:
      {SV.lt(i, n) == True{} : Bool}
    case DR.DSelf{a}:
      Unit
    case DR.DPLin{m1, d1, m2, d2}:
      SK.Both(DB(d1, n), DB(d2, n))
    case DR.DKnown{d0, dr, di}:
      SK.Both(DB(d0, n), SK.Both(DB(dr, n), DB(di, n)))
    case DR.DTurn{d0, g, b}:
      DB(d0, n)
    case DR.DThrough{d1, d2, g, b}:
      SK.Both(DB(d1, n), DB(d2, n))
    case DR.DFrame{d0, x}:
      DB(d0, n)
    case DR.DVoid{dr, di, a, x}:
      SK.Both(DB(dr, n), DB(di, n))

def DsB(ds: List<&2, DR.Der>, +n: Nat) -> Data:
  match ds:
    case Nil{}:
      Unit
    case Con{d, t}:
      SK.Both(DB(d, n), DsB(t, n))

def PE(fs1: List<&2, DR.Fact>, fs2: List<&2, DR.Fact>, i: Nat) -> Type:
  {DR.fact.e(DR.fact_at(fs1, i)) == DR.fact.e(DR.fact_at(fs2, i)) : E.QExpr}

def PJ(fs1: List<&2, DR.Fact>, fs2: List<&2, DR.Fact>, i: Nat) -> Type:
  {DR.fact.pj(DR.fact_at(fs1, i)) == DR.fact.pj(DR.fact_at(fs2, i)) : DR.Jd}

def fag_e(+f: DR.Fact, +g: DR.Fact, h: FAg(f, g)) -> {DR.fact.e(Some{f}) == DR.fact.e(Some{g}) : E.QExpr}:
  (a, b) = h
  a

def pj_ds(+e1: E.QExpr, +n1: List<&2, Nat>, +e2: E.QExpr, +n2: List<&2, Nat>, d: Maybe<&2, DR.DStat>) -> {DR.fact.pj(Some{DR.Fact{e1, n1, d}}) == DR.fact.pj(Some{DR.Fact{e2, n2, d}}) : DR.Jd}:
  match d:
    case None{}:
      {==}
    case Some{DR.DStat{+a, +x, +l}}:
      {==}

def fag.ds(+f: DR.Fact, +g: DR.Fact, h: FAg(f, g)) -> {fds(f) == fds(g) : Maybe<&2, DR.DStat>}:
  (a, b) = h
  b

def fag_pj(f: DR.Fact, g: DR.Fact, h: FAg(f, g)) -> {DR.fact.pj(Some{f}) == DR.fact.pj(Some{g}) : DR.Jd}:
  match f g:
    case DR.Fact{+e1, +n1, +d1} DR.Fact{+e2, +n2, +d2}:
      %fag.ds(DR.Fact{e1, n1, d1}, DR.Fact{e2, n2, d2}, h) : {DR.fact.pj(Some{DR.Fact{e1, n1, d1}}) == DR.fact.pj(Some{DR.Fact{e2, n2, _}}) : DR.Jd}
      pj_ds(e1, n1, e2, n2, d1)

def nolt(+i: Nat, h: {SV.lt(i, 0n) == True{} : Bool}) -> Empty:
  KA.tf(Equal.sym(Bool, False{}, True{}, KB.lt_zero(i, h)))

# position i of fs1 agrees
def pre_e(fs1: List<&2, DR.Fact>, fs2: List<&2, DR.Fact>, i: Nat, +h: Pre(fs1, fs2), +hi: {SV.lt(i, flen(fs1)) == True{} : Bool}) -> PE(fs1, fs2, i):
  match fs1 fs2 i:
    case Nil{} Nil{} 0n:
      absurd(PE(Nil{}, Nil{}, 0n), nolt(0n, hi))
    case Nil{} Nil{} 1n+j:
      absurd(PE(Nil{}, Nil{}, 1n+j), nolt(1n+j, hi))
    case Nil{} Con{+g, +t2} 0n:
      absurd(PE(Nil{}, Con{g, t2}, 0n), nolt(0n, hi))
    case Nil{} Con{+g, +t2} 1n+j:
      absurd(PE(Nil{}, Con{g, t2}, 1n+j), nolt(1n+j, hi))
    case Con{+f, +t1} Nil{} 0n:
      absurd(PE(Con{f, t1}, Nil{}, 0n), h)
    case Con{+f, +t1} Nil{} 1n+j:
      absurd(PE(Con{f, t1}, Nil{}, 1n+j), h)
    case Con{+f, +t1} Con{+g, +t2} 0n:
      (a, ht) = h
      fag_e(f, g, a)
    case Con{+f, +t1} Con{+g, +t2} 1n+j:
      (a, ht) = h
      pre_e(t1, t2, j, ht, hi)

def pre_pj(fs1: List<&2, DR.Fact>, fs2: List<&2, DR.Fact>, i: Nat, +h: Pre(fs1, fs2), +hi: {SV.lt(i, flen(fs1)) == True{} : Bool}) -> PJ(fs1, fs2, i):
  match fs1 fs2 i:
    case Nil{} Nil{} 0n:
      absurd(PJ(Nil{}, Nil{}, 0n), nolt(0n, hi))
    case Nil{} Nil{} 1n+j:
      absurd(PJ(Nil{}, Nil{}, 1n+j), nolt(1n+j, hi))
    case Nil{} Con{+g, +t2} 0n:
      absurd(PJ(Nil{}, Con{g, t2}, 0n), nolt(0n, hi))
    case Nil{} Con{+g, +t2} 1n+j:
      absurd(PJ(Nil{}, Con{g, t2}, 1n+j), nolt(1n+j, hi))
    case Con{+f, +t1} Nil{} 0n:
      absurd(PJ(Con{f, t1}, Nil{}, 0n), h)
    case Con{+f, +t1} Nil{} 1n+j:
      absurd(PJ(Con{f, t1}, Nil{}, 1n+j), h)
    case Con{+f, +t1} Con{+g, +t2} 0n:
      (a, ht) = h
      fag_pj(f, g, a)
    case Con{+f, +t1} Con{+g, +t2} 1n+j:
      (a, ht) = h
      pre_pj(t1, t2, j, ht, hi)

# Conclusions
# -----------

def known_pre(+es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +d0: DR.Der, +dr: DR.Der, +di: DR.Der, +n: Nat, bri: SK.Both(DB(dr, n), DB(di, n)),
  e0: {DR.concl(es, fs1, d0) == DR.concl(es, fs2, d0) : DR.Jd},
  ihr: DB(dr, n) -> {DR.concl(es, fs1, dr) == DR.concl(es, fs2, dr) : DR.Jd},
  ihi: DB(di, n) -> {DR.concl(es, fs1, di) == DR.concl(es, fs2, di) : DR.Jd})
  -> {DR.concl(es, fs1, DR.DKnown{d0, dr, di}) == DR.concl(es, fs2, DR.DKnown{d0, dr, di}) : DR.Jd}:
  (br, bi) = bri
  %e0 : {DR.concl(es, fs1, DR.DKnown{d0, dr, di}) == DR.JP{DR.Jd.a(_), SK.VE.add(DR.Jd.x(_), SK.VE{DR.Jd.e(DR.concl(es, fs2, dr)), DR.Jd.e(DR.concl(es, fs2, di))})} : DR.Jd}
  %ihr(br) : {DR.concl(es, fs1, DR.DKnown{d0, dr, di}) == DR.JP{DR.Jd.a(DR.concl(es, fs1, d0)), SK.VE.add(DR.Jd.x(DR.concl(es, fs1, d0)), SK.VE{DR.Jd.e(_), DR.Jd.e(DR.concl(es, fs2, di))})} : DR.Jd}
  %ihi(bi) : {DR.concl(es, fs1, DR.DKnown{d0, dr, di}) == DR.JP{DR.Jd.a(DR.concl(es, fs1, d0)), SK.VE.add(DR.Jd.x(DR.concl(es, fs1, d0)), SK.VE{DR.Jd.e(DR.concl(es, fs1, dr)), DR.Jd.e(_)})} : DR.Jd}
  {==}

# a derivation citing positions of fs1 concludes the same over fs2
def concl_pre(+es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, d: DR.Der, +h: Pre(fs1, fs2), b: DB(d, flen(fs1))) -> {DR.concl(es, fs1, d) == DR.concl(es, fs2, d) : DR.Jd}:
  match d:
    case DR.DZero{}:
      {==}
    case DR.DPrem{+i}:
      %pre_e(fs1, fs2, i, h, b) : {DR.JK{DR.fact.e(DR.fact_at(fs1, i))} == DR.JK{_} : DR.Jd}
      {==}
    case DR.DKAdd{+l, +d1, +d2}:
      (b1, b2) = b
      %concl_pre(es, fs1, fs2, d1, h, b1) : {DR.concl(es, fs1, DR.DKAdd{l, d1, d2}) == DR.JK{E.QAdd{E.QMul{E.QCst{l}, DR.Jd.e(_)}, DR.Jd.e(DR.concl(es, fs2, d2))}} : DR.Jd}
      %concl_pre(es, fs1, fs2, d2, h, b2) : {DR.concl(es, fs1, DR.DKAdd{l, d1, d2}) == DR.JK{E.QAdd{E.QMul{E.QCst{l}, DR.Jd.e(DR.concl(es, fs1, d1))}, DR.Jd.e(_)}} : DR.Jd}
      {==}
    case DR.DBack{+d0}:
      %concl_pre(es, fs1, fs2, d0, h, b) : {DR.concl(es, fs1, DR.DBack{d0}) == DR.JK{SK.VE.y(DR.Jd.x(_))} : DR.Jd}
      {==}
    case DR.DLine{+d1, +d2, +re}:
      (b1, b2) = b
      %concl_pre(es, fs1, fs2, d1, h, b1) : {DR.concl(es, fs1, DR.DLine{d1, d2, re}) == DR.JK{DR.dline.e(re, DR.Jd.x(_))} : DR.Jd}
      {==}
    case DR.DPPrem{+i}:
      pre_pj(fs1, fs2, i, h, b)
    case DR.DSelf{+a}:
      {==}
    case DR.DPLin{+m1, +d1, +m2, +d2}:
      (b1, b2) = b
      %concl_pre(es, fs1, fs2, d1, h, b1) : {DR.concl(es, fs1, DR.DPLin{m1, d1, m2, d2}) == DR.JP{DR.Jd.a(_), DR.vlin(m1, DR.Jd.x(_), m2, DR.Jd.x(DR.concl(es, fs2, d2)))} : DR.Jd}
      %concl_pre(es, fs1, fs2, d2, h, b2) : {DR.concl(es, fs1, DR.DPLin{m1, d1, m2, d2}) == DR.JP{DR.Jd.a(DR.concl(es, fs1, d1)), DR.vlin(m1, DR.Jd.x(DR.concl(es, fs1, d1)), m2, DR.Jd.x(_))} : DR.Jd}
      {==}
    case DR.DKnown{+d0, +dr, +di}:
      (b0, bri) = b
      known_pre(es, fs1, fs2, d0, dr, di, flen(fs1), bri, concl_pre(es, fs1, fs2, d0, h, b0), x => concl_pre(es, fs1, fs2, dr, h, x), x => concl_pre(es, fs1, fs2, di, h, x))
    case DR.DTurn{+d0, +g, +nb}:
      %concl_pre(es, fs1, fs2, d0, h, b) : {DR.concl(es, fs1, DR.DTurn{d0, g, nb}) == DR.JP{nb, DR.gmul(g, DR.zdir(es, DR.Jd.a(_)))} : DR.Jd}
      {==}
    case DR.DThrough{+d1, +d2, +g, +nb}:
      (b1, b2) = b
      %concl_pre(es, fs1, fs2, d1, h, b1) : {DR.concl(es, fs1, DR.DThrough{d1, d2, g, nb}) == DR.JP{DR.Jd.a(_), DR.gmul(DR.Lab.conj(g), DR.Jd.x(DR.concl(es, fs2, d2)))} : DR.Jd}
      %concl_pre(es, fs1, fs2, d2, h, b2) : {DR.concl(es, fs1, DR.DThrough{d1, d2, g, nb}) == DR.JP{DR.Jd.a(DR.concl(es, fs1, d1)), DR.gmul(DR.Lab.conj(g), DR.Jd.x(_))} : DR.Jd}
      {==}
    case DR.DFrame{+d0, +x}:
      {==}
    case DR.DVoid{+dr, +di, +a, +x}:
      {==}

def pre_refl(fs: List<&2, DR.Fact>) -> Pre(fs, fs):
  match fs:
    case Nil{}:
      Unit{}
    case Con{+f, +t}:
      (({==}, {==}), pre_refl(t))

def pre_cat(fs1: List<&2, DR.Fact>, fs2: List<&2, DR.Fact>, +ys: List<&2, DR.Fact>, h: Pre(fs1, fs2)) -> Pre(fs1, SV.fcat(fs2, ys)):
  match fs1 fs2:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} Con{+g, +t2}:
      Unit{}
    case Con{+f, +t1} Nil{}:
      absurd(Pre(Con{f, t1}, SV.fcat(Nil{}, ys)), h)
    case Con{+f, +t1} Con{+g, +t2}:
      (a, ht) = h
      (a, pre_cat(t1, t2, ys, ht))

def flen_cat(xs: List<&2, DR.Fact>, +ys: List<&2, DR.Fact>) -> {flen(SV.fcat(xs, ys)) == Nat.add(flen(xs), flen(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %flen_cat(t, ys) : {1n+flen(SV.fcat(t, ys)) == 1n+_ : Nat}
      {==}

# What reads the facts only through conclusions
# ---------------------------------------------

def ks_add_pre(+es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, k: KS.KS, +d: DR.Der, +h: Pre(fs1, fs2), +b: DB(d, flen(fs1))) -> {KS.ks.add(es, fs1, k, d) == KS.ks.add(es, fs2, k, d) : KS.KS}:
  match k:
    case KS.KS{+rows, +ds}:
      %concl_pre(es, fs1, fs2, d, h, b) : {KS.ks.add(es, fs1, KS.KS{rows, ds}, d) == KS.ks.pick(EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(_)))), rows, ds, EL.resid(rows, DR.Jd.e(_)), d) : KS.KS}
      {==}

def lh_add_pre(+es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +t: Nat, hh: LR.LH, +d: DR.Der, +h: Pre(fs1, fs2), +b: DB(d, flen(fs1))) -> {LR.lh.add(es, fs1, t, hh, d) == LR.lh.add(es, fs2, t, hh, d) : LR.LH}:
  match hh:
    case LR.LH{+rows, +ds}:
      %concl_pre(es, fs1, fs2, d, h, b) : {LR.lh.add(es, fs1, t, LR.LH{rows, ds}, d) == LR.lh.pick(EP.isnil(LR.lresid(rows, HS.enc(DR.Jd.x(_), t))), rows, ds, LR.lresid(rows, HS.enc(DR.Jd.x(_), t)), d) : LR.LH}
      {==}

def lfold_pre(xs: List<&2, DR.Der>, +es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +t: Nat, +hh: LR.LH, +h: Pre(fs1, fs2), b: DsB(xs, flen(fs1))) -> {LR.lfold(xs, es, fs1, t, hh) == LR.lfold(xs, es, fs2, t, hh) : LR.LH}:
  match xs:
    case Nil{}:
      {==}
    case Con{+d, +tl}:
      (bd, bt) = b
      %lh_add_pre(es, fs1, fs2, t, hh, d, h, bd) : {LR.lfold(tl, es, fs1, t, LR.lh.add(es, fs1, t, hh, d)) == LR.lfold(tl, es, fs2, t, _) : LR.LH}
      lfold_pre(tl, es, fs1, fs2, t, LR.lh.add(es, fs1, t, hh, d), h, bt)

def kg.c(+r: DR.Node, +d: DR.Der, +tl: List<&2, DR.Der>, +n: Nat, +bd: DB(d, n), bt: DsB(DC.kgens(r, tl), n)) -> DsB(Con{HS.kre(r, d), Con{HS.kim(r, d), DC.kgens(r, tl)}}, n):
  (((Unit{}, Unit{}), (bd, Unit{})), (((Unit{}, Unit{}), (Unit{}, bd)), bt))

def kgens_dsb(+r: DR.Node, ds: List<&2, DR.Der>, +n: Nat, b: DsB(ds, n)) -> DsB(DC.kgens(r, ds), n):
  match ds:
    case Nil{}:
      Unit{}
    case Con{+d, +tl}:
      (bd, bt) = b
      kg.c(r, d, tl, n, bd, kgens_dsb(r, tl, n, bt))

def lkhull_pre(+es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +r: DR.Node, +h: Pre(fs1, fs2), +b: DsB(KS.ks.ds(k), flen(fs1))) -> {DC.lkhull(es, fs1, t, k, r) == DC.lkhull(es, fs2, t, k, r) : LR.LH}:
  lfold_pre(DC.kgens(r, KS.ks.ds(k)), es, fs1, fs2, t, LR.LH{Nil{}, Nil{}}, h, kgens_dsb(r, KS.ks.ds(k), flen(fs1), b))

# a cache right over fs1 is right over fs2
def cinv_pre(+es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, C: List<&2, DC.KC>, +h: Pre(fs1, fs2), +b: DsB(KS.ks.ds(k), flen(fs1)), inv: FP.CInv(es, fs1, t, k, C)) -> FP.CInv(es, fs2, t, k, C):
  match C:
    case Nil{}:
      Unit{}
    case Con{DC.KC{+n, +hh}, +tl}:
      (hn, it) = inv
      (Equal.trans(LR.LH, hh, DC.lkhull(es, fs1, t, k, n), DC.lkhull(es, fs2, t, k, n), hn, lkhull_pre(es, fs1, fs2, t, k, n, h, b)), cinv_pre(es, fs1, fs2, t, k, tl, h, b, it))

# K from the facts
# ----------------

def lt_add(i: Nat, +m: Nat) -> {SV.lt(i, Nat.add(i, 1n+m)) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      lt_add(j, m)

def lt_of_add(+i: Nat, +m: Nat, +n: Nat, h: {Nat.add(i, 1n+m) == n : Nat}) -> {SV.lt(i, n) == True{} : Bool}:
  %h : {SV.lt(i, _) == True{} : Bool}
  lt_add(i, m)

def dsnoc_dsb(ds: List<&2, DR.Der>, +d: DR.Der, +n: Nat, b: DsB(ds, n), +bd: DB(d, n)) -> DsB(KS.dsnoc(ds, d), n):
  match ds:
    case Nil{}:
      (bd, Unit{})
    case Con{+x, +tl}:
      (bx, bt) = b
      (bx, dsnoc_dsb(tl, d, n, bt, bd))

def ks_pick_dsb(c: Bool, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +r: EL.Res, +d: DR.Der, +n: Nat, b: DsB(ds, n), +bd: DB(d, n)) -> DsB(KS.ks.ds(KS.ks.pick(c, rows, ds, r, d)), n):
  match c:
    case True{}:
      b
    case False{}:
      dsnoc_dsb(ds, d, n, b, bd)

def ks_add_dsb(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, k: KS.KS, +d: DR.Der, +n: Nat, b: DsB(KS.ks.ds(k), n), +bd: DB(d, n)) -> DsB(KS.ks.ds(KS.ks.add(es, fs, k, d)), n):
  match k:
    case KS.KS{+rows, +ds}:
      ks_pick_dsb(EP.isnil(EP.resp(EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))))), rows, ds, EL.resid(rows, DR.Jd.e(DR.concl(es, fs, d))), d, n, b, bd)

# K's derivations cite only positions below n
def kinit_below(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, rest: List<&2, DR.Fact>, +i: Nat, +k: KS.KS, +n: Nat, b: DsB(KS.ks.ds(k), n), +hb: {Nat.add(i, flen(rest)) == n : Nat}) -> DsB(KS.ks.ds(DC.kinit(es, fs, rest, i, k)), n):
  match rest:
    case Nil{}:
      b
    case Con{+f, +tl}:
      kinit_below(es, fs, tl, 1n+i, KS.ks.add(es, fs, k, DR.DPrem{i}), n, ks_add_dsb(es, fs, k, DR.DPrem{i}, n, b, lt_of_add(i, flen(tl), n, hb)), LN.succ_add(i, flen(tl), n, hb))

# K from the facts at the positions of xs, over fs1, is K from those of ys
# (as many) over fs2
def kinit_pre(xs: List<&2, DR.Fact>, ys: List<&2, DR.Fact>, +es: List<&2, SK.Ent>, +fs1: List<&2, DR.Fact>, +fs2: List<&2, DR.Fact>, +i: Nat, +k: KS.KS, +h: Pre(fs1, fs2), +hl: {flen(xs) == flen(ys) : Nat}, +hb: {Nat.add(i, flen(xs)) == flen(fs1) : Nat})
  -> {DC.kinit(es, fs1, xs, i, k) == DC.kinit(es, fs2, ys, i, k) : KS.KS}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+y, +yt}:
      absurd({DC.kinit(es, fs1, Nil{}, i, k) == DC.kinit(es, fs2, Con{y, yt}, i, k) : KS.KS}, OW.zs(flen(yt), hl))
    case Con{+x, +xt} Nil{}:
      absurd({DC.kinit(es, fs1, Con{x, xt}, i, k) == DC.kinit(es, fs2, Nil{}, i, k) : KS.KS}, OW.zs(flen(xt), Equal.sym(Nat, 1n+flen(xt), 0n, hl)))
    case Con{+x, +xt} Con{+y, +yt}:
      %ks_add_pre(es, fs1, fs2, k, DR.DPrem{i}, h, lt_of_add(i, flen(xt), flen(fs1), hb)) : {DC.kinit(es, fs1, xt, 1n+i, KS.ks.add(es, fs1, k, DR.DPrem{i})) == DC.kinit(es, fs2, yt, 1n+i, _) : KS.KS}
      kinit_pre(xt, yt, es, fs1, fs2, 1n+i, KS.ks.add(es, fs1, k, DR.DPrem{i}), h, LN.succ_inj(flen(xt), flen(yt), hl), LN.succ_add(i, flen(xt), flen(fs1), hb))

# K from xs ++ ys is K from ys after K from xs
def kinit_cat(xs: List<&2, DR.Fact>, +ys: List<&2, DR.Fact>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +i: Nat, +k: KS.KS)
  -> {DC.kinit(es, fs, SV.fcat(xs, ys), i, k) == DC.kinit(es, fs, ys, Nat.add(i, flen(xs)), DC.kinit(es, fs, xs, i, k)) : KS.KS}:
  match xs:
    case Nil{}:
      %LN.add_zero(i) : {DC.kinit(es, fs, ys, i, k) == DC.kinit(es, fs, ys, _, k) : KS.KS}
      {==}
    case Con{+x, +xt}:
      %LN.add_succ(i, flen(xt)) : {DC.kinit(es, fs, SV.fcat(xt, ys), 1n+i, KS.ks.add(es, fs, k, DR.DPrem{i})) == DC.kinit(es, fs, ys, _, DC.kinit(es, fs, xt, 1n+i, KS.ks.add(es, fs, k, DR.DPrem{i}))) : KS.KS}
      kinit_cat(xt, ys, es, fs, 1n+i, KS.ks.add(es, fs, k, DR.DPrem{i}))

# The start
# ---------

def mk.n(m: DC.MK) -> Nat:
  match m:
    case DC.MK{n, k, C}:
      n

def mk.k(m: DC.MK) -> KS.KS:
  match m:
    case DC.MK{n, k, C}:
      k

def mk.C(m: DC.MK) -> List<&2, DC.KC>:
  match m:
    case DC.MK{n, k, C}:
      C

# m is the count n, K = k, and a cache right for it
def MOk(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +n: Nat, +k: KS.KS, +m: DC.MK) -> Data:
  SK.Both({mk.n(m) == n : Nat}, SK.Both({mk.k(m) == k : KS.KS}, FP.CInv(es, fs, t, mk.k(m), mk.C(m))))

# m is the start of the facts fs
def MemoOk(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +m: DC.MK) -> Data:
  MOk(es, fs, t, flen(fs), DC.kinit(es, fs, fs, 0n, KS.ks0()), m)

# mext gives K the facts ys and keeps the cache right
def mext_ok(ys: List<&2, DR.Fact>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +n: Nat, +k: KS.KS, +C: List<&2, DC.KC>, inv: FP.CInv(es, fs, t, k, C))
  -> MOk(es, fs, t, Nat.add(n, flen(ys)), DC.kinit(es, fs, ys, n, k), DC.mext(ys, es, fs, t, n, k, C)):
  match ys:
    case Nil{}:
      (LN.add_zero(n), ({==}, inv))
    case Con{+y, +tl}:
      %LN.add_succ(n, flen(tl)) : MOk(es, fs, t, _, DC.kinit(es, fs, tl, 1n+n, KS.ks.add(es, fs, k, DR.DPrem{n})), DC.mext(tl, es, fs, t, 1n+n, KS.ks.add(es, fs, k, DR.DPrem{n}), DC.kc.add(C, DR.DPrem{n}, es, fs, t, k)))
      mext_ok(tl, es, fs, t, 1n+n, KS.ks.add(es, fs, k, DR.DPrem{n}), DC.kc.add(C, DR.DPrem{n}, es, fs, t, k), FP.kc_add_inv(k, C, DR.DPrem{n}, es, fs, t, inv))

def mok.k(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +m: DC.MK, +k: KS.KS, +k2: KS.KS, h: SK.Both({mk.k(m) == k : KS.KS}, FP.CInv(es, fs, t, mk.k(m), mk.C(m))), ek: {k == k2 : KS.KS})
  -> SK.Both({mk.k(m) == k2 : KS.KS}, FP.CInv(es, fs, t, mk.k(m), mk.C(m))):
  (hk, hc) = h
  (Equal.trans(KS.KS, mk.k(m), k, k2, hk, ek), hc)

# the same start, with n and k named otherwise
def mok_eq(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +m: DC.MK, +n: Nat, +n2: Nat, +k: KS.KS, +k2: KS.KS, h: MOk(es, fs, t, n, k, m), en: {n == n2 : Nat}, ek: {k == k2 : KS.KS}) -> MOk(es, fs, t, n2, k2, m):
  (hn, hk) = h
  (Equal.trans(Nat, mk.n(m), n, n2, hn, en), mok.k(es, fs, t, m, k, k2, hk, ek))

def kdsb(+es: List<&2, SK.Ent>, +R: List<&2, DR.Fact>, +k: KS.KS, +hk: {k == DC.kinit(es, R, R, 0n, KS.ks0()) : KS.KS}) -> DsB(KS.ks.ds(k), flen(R)):
  %Equal.sym(KS.KS, k, DC.kinit(es, R, R, 0n, KS.ks0()), hk) : DsB(KS.ks.ds(_), flen(R))
  kinit_below(es, R, R, 0n, KS.ks0(), flen(R), Unit{}, {==})

def mr.n(+R: List<&2, DR.Fact>, +X: List<&2, DR.Fact>, +ys: List<&2, DR.Fact>, +n: Nat, +hn: {n == flen(R) : Nat}, +hl: {flen(X) == flen(R) : Nat}) -> {Nat.add(n, flen(ys)) == flen(SV.fcat(X, ys)) : Nat}:
  %Equal.sym(Nat, n, flen(X), Equal.trans(Nat, n, flen(R), flen(X), hn, Equal.sym(Nat, flen(X), flen(R), hl))) : {Nat.add(_, flen(ys)) == flen(SV.fcat(X, ys)) : Nat}
  Equal.sym(Nat, flen(SV.fcat(X, ys)), Nat.add(flen(X), flen(ys)), flen_cat(X, ys))

def mr.k(+es: List<&2, SK.Ent>, +R: List<&2, DR.Fact>, +X: List<&2, DR.Fact>, +ys: List<&2, DR.Fact>, +n: Nat, +k: KS.KS, +hn: {n == flen(R) : Nat}, +hk: {k == DC.kinit(es, R, R, 0n, KS.ks0()) : KS.KS}, +hpf: Pre(R, SV.fcat(X, ys)), +hl: {flen(X) == flen(R) : Nat})
  -> {DC.kinit(es, SV.fcat(X, ys), ys, n, k) == DC.kinit(es, SV.fcat(X, ys), SV.fcat(X, ys), 0n, KS.ks0()) : KS.KS}:
  %Equal.sym(Nat, n, flen(X), Equal.trans(Nat, n, flen(R), flen(X), hn, Equal.sym(Nat, flen(X), flen(R), hl))) : {DC.kinit(es, SV.fcat(X, ys), ys, _, k) == DC.kinit(es, SV.fcat(X, ys), SV.fcat(X, ys), 0n, KS.ks0()) : KS.KS}
  %Equal.sym(KS.KS, k, DC.kinit(es, SV.fcat(X, ys), X, 0n, KS.ks0()), Equal.trans(KS.KS, k, DC.kinit(es, R, R, 0n, KS.ks0()), DC.kinit(es, SV.fcat(X, ys), X, 0n, KS.ks0()), hk, kinit_pre(R, X, es, R, SV.fcat(X, ys), 0n, KS.ks0(), hpf, Equal.sym(Nat, flen(X), flen(R), hl), {==}))) : {DC.kinit(es, SV.fcat(X, ys), ys, flen(X), _) == DC.kinit(es, SV.fcat(X, ys), SV.fcat(X, ys), 0n, KS.ks0()) : KS.KS}
  Equal.sym(KS.KS, DC.kinit(es, SV.fcat(X, ys), SV.fcat(X, ys), 0n, KS.ks0()), DC.kinit(es, SV.fcat(X, ys), ys, flen(X), DC.kinit(es, SV.fcat(X, ys), X, 0n, KS.ks0())), kinit_cat(X, ys, es, SV.fcat(X, ys), 0n, KS.ks0()))

def reuse.c(+es: List<&2, SK.Ent>, +R: List<&2, DR.Fact>, +X: List<&2, DR.Fact>, +ys: List<&2, DR.Fact>, +t: Nat, +n: Nat, +k: KS.KS, +C: List<&2, DC.KC>, +hn: {n == flen(R) : Nat},
  +hk: {k == DC.kinit(es, R, R, 0n, KS.ks0()) : KS.KS}, hc: FP.CInv(es, R, t, k, C), +hp: Pre(R, X), +hl: {flen(X) == flen(R) : Nat})
  -> MemoOk(es, SV.fcat(X, ys), t, DC.mext(ys, es, SV.fcat(X, ys), t, n, k, C)):
  mok_eq(es, SV.fcat(X, ys), t, DC.mext(ys, es, SV.fcat(X, ys), t, n, k, C), Nat.add(n, flen(ys)), flen(SV.fcat(X, ys)), DC.kinit(es, SV.fcat(X, ys), ys, n, k), DC.kinit(es, SV.fcat(X, ys), SV.fcat(X, ys), 0n, KS.ks0()),
    mext_ok(ys, es, SV.fcat(X, ys), t, n, k, C, cinv_pre(es, R, SV.fcat(X, ys), t, k, C, pre_cat(R, X, ys, hp), kdsb(es, R, k, hk), hc)),
    mr.n(R, X, ys, n, hn, hl), mr.k(es, R, X, ys, n, k, hn, hk, pre_cat(R, X, ys, hp), hl))

def reuse.k(+es: List<&2, SK.Ent>, +R: List<&2, DR.Fact>, +X: List<&2, DR.Fact>, +ys: List<&2, DR.Fact>, +t: Nat, +n: Nat, +k: KS.KS, +C: List<&2, DC.KC>, +hn: {n == flen(R) : Nat},
  hkc: SK.Both({k == DC.kinit(es, R, R, 0n, KS.ks0()) : KS.KS}, FP.CInv(es, R, t, k, C)), +hp: Pre(R, X), +hl: {flen(X) == flen(R) : Nat})
  -> MemoOk(es, SV.fcat(X, ys), t, DC.mext(ys, es, SV.fcat(X, ys), t, n, k, C)):
  (hk, hc) = hkc
  reuse.c(es, R, X, ys, t, n, k, C, hn, hk, hc, hp, hl)

# R's start, given the facts ys, is the start of X ++ ys, for X agreeing
# with R at each of its positions and as long
def mext_reuse(+es: List<&2, SK.Ent>, +R: List<&2, DR.Fact>, +X: List<&2, DR.Fact>, +ys: List<&2, DR.Fact>, +t: Nat, M: DC.MK, hm: MemoOk(es, R, t, M), +hp: Pre(R, X), +hl: {flen(X) == flen(R) : Nat})
  -> MemoOk(es, SV.fcat(X, ys), t, DC.mext.m(ys, es, SV.fcat(X, ys), t, M)):
  match M:
    case DC.MK{+n, +k, +C}:
      (hn, hkc) = hm
      reuse.k(es, R, X, ys, t, n, k, C, hn, hkc, hp, hl)

# Starting a call
# ---------------

def kc_sel_inv(ns: List<&2, DR.Node>, +C: List<&2, DC.KC>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +k: KS.KS, +inv: FP.CInv(es, fs, t, k, C)) -> FP.CInv(es, fs, t, k, DC.kc.sel(ns, C, es, fs, t, k)):
  match ns:
    case Nil{}:
      Unit{}
    case Con{+n, +tl}:
      (FP.kc_get_eq(C, n, es, fs, t, k, inv), kc_sel_inv(tl, C, es, fs, t, k, inv))

def dcm.c(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +fuel: Nat, +n: Nat, +k: KS.KS, +C: List<&2, DC.KC>,
  +hk: {k == DC.kinit(es, fs, fs, 0n, KS.ks0()) : KS.KS}, hc: FP.CInv(es, fs, t, k, C))
  -> {DC.dclose.m(es, fs, ctx, t, fuel, DC.MK{n, k, C}) == DC.dclose(es, fs, ctx, t, fuel) : DC.Out}:
  %Equal.sym(KS.KS, k, DC.kinit(es, fs, fs, 0n, KS.ks0()), hk) : {DC.dclose.m(es, fs, ctx, t, fuel, DC.MK{n, _, C}) == DC.dclose(es, fs, ctx, t, fuel) : DC.Out}
  Equal.trans(DC.Out, DC.dclose.m(es, fs, ctx, t, fuel, DC.MK{n, DC.kinit(es, fs, fs, 0n, KS.ks0()), C}), DC.dclose_ref(es, fs, ctx, t, fuel), DC.dclose(es, fs, ctx, t, fuel),
    FP.frun_eq(fuel, DC.FO{DC.OStep{DC.sk0(es, fs, DC.sp.of(ctx, DC.SP{Nil{}, Nil{}}))}, DC.kc.sel(DC.snodes(DC.oids(DC.segids(es), es, DC.sp.of(ctx, DC.SP{Nil{}, Nil{}}))), C, es, fs, t, DC.kinit(es, fs, fs, 0n, KS.ks0()))}, DC.OStep{DC.sk0(es, fs, DC.sp.of(ctx, DC.SP{Nil{}, Nil{}}))}, es, fs, t, DC.sp.of(ctx, DC.SP{Nil{}, Nil{}}), DC.segids(es),
      ({==}, kc_sel_inv(DC.snodes(DC.oids(DC.segids(es), es, DC.sp.of(ctx, DC.SP{Nil{}, Nil{}}))), C, es, fs, t, DC.kinit(es, fs, fs, 0n, KS.ks0()), (%hk : FP.CInv(es, fs, t, _, C)
        hc)))),
    Equal.sym(DC.Out, DC.dclose(es, fs, ctx, t, fuel), DC.dclose_ref(es, fs, ctx, t, fuel), FP.dclose_eq(es, fs, ctx, t, fuel)))

def dcm.h(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, fuel: Nat, +n: Nat, +k: KS.KS, +C: List<&2, DC.KC>,
  hkc: SK.Both({k == DC.kinit(es, fs, fs, 0n, KS.ks0()) : KS.KS}, FP.CInv(es, fs, t, k, C)))
  -> {DC.dclose.m(es, fs, ctx, t, fuel, DC.MK{n, k, C}) == DC.dclose(es, fs, ctx, t, fuel) : DC.Out}:
  (hk, hc) = hkc
  dcm.c(es, fs, ctx, t, fuel, n, k, C, hk, hc)

# dclose from a start of fs returns what dclose returns
def dclose_m_eq(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, fuel: Nat, m: DC.MK, hm: MemoOk(es, fs, t, m)) -> {DC.dclose.m(es, fs, ctx, t, fuel, m) == DC.dclose(es, fs, ctx, t, fuel) : DC.Out}:
  match m:
    case DC.MK{+n, +k, +C}:
      (hn, hkc) = hm
      dcm.h(es, fs, ctx, t, fuel, n, k, C, hkc)
