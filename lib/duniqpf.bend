# bend-cad: any two classifications honest by the draft Honest agree
# (PLAN-sk13b B6, honest_unique over the extended Honest). Every constraint
# has the same kind in both, and every equation is dropped in both or in
# neither. Proofs only.
#
# As lib/uniqpf.bend: both are read once (lib/dfactpf.bend: hon_rb), then
# walked in order with the same kept constraints and solved equations
# before c in both. At c the two Fates meet (fate_ag2) and every pair of
# classes either has the same kind and drops or is impossible:
# - kept or amber against kept or amber: the same drops, now of both
#   layers (lib/dagreepf.bend: drops_ag2), and an amber's one Implied per
#   side (SV.AllImplied) meets a kept's NotImplied (ka_imp2);
# - a conflict against anything else (conf_nr2): its refutation is of
#   degree 0 (lib/nrconfpf.bend's cn.m) or by directions, and the other
#   has none with all the kept constraints before c, so none with the
#   support (lib/dmappf.bend: nodir_mono);
# - over against kept or amber: lib/overpf.bend, with drops_ag2.
# The rest of the walk reads only the classes, and is uniqpf's.
#
# Generated from tools/drafts/duniqpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/ring.bend as E
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/dir.bend as DR
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as L
import ./kbpf.bend as KB
import ./solvedpf.bend as SP
import ./agreepf.bend as AG
import ./hreadpf.bend as HR
import ./refute.bend as RF
import ./nrconfpf.bend as NC
import ./overpf.bend as OV
import ./uniqpf.bend as UQ
import ./dmappf.bend as DMP
import ./dfactpf.bend as DFC
import ./dagreepf.bend as DAG

def absurd(-A: Type, x: Empty) -> A:
  match x:


# the no-refutation every unconflicted Fate starts with
def nr_k(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +dd: List<&2, SV.Drop>, h: SV.KeptOk(sk, cls, R, D, c, dd)) -> SV.NoRefute2(sk, R, c):
  (nr, r) = h
  nr

def nr_a(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +dd: List<&2, SV.Drop>, h: SV.AmberOk(sk, cls, R, D, c, dd)) -> SV.NoRefute2(sk, R, c):
  (nr, r) = h
  nr

def nr_o(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +j: Nat, +s: List<&2, Nat>, +w: List<&2, Nat>, h: SV.OverOk(sk, cls, R, D, c, j, s, w)) -> SV.NoRefute2(sk, R, c):
  (nr, r) = h
  nr

# Kept and Amber
# --------------

# side i0 + i of c is implied
def ai_go(+sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat, ss: List<&2, SK.Side>, +i0: Nat, i: Nat, h: SV.implied.go(sk, R, c, ss, i0), hi: {SV.lt(i, SV.slen(ss)) == True{} : Bool}) -> SV.Implied(sk, R, c, Nat.add(i, i0)):
  match ss i:
    case Nil{} i:
      absurd(SV.Implied(sk, R, c, Nat.add(i, i0)), KA.ft(KB.lt_zero(i, hi)))
    case Con{s, t} 0n:
      (a, b) = h
      a
    case Con{s, t} 1n++q:
      (a, b) = h
      (%Equal.sym(Nat, 1n+Nat.add(q, i0), Nat.add(q, 1n+i0), LN.add_succ(q, i0)) : SV.Implied(sk, R, c, _)
        ai_go(sk, R, c, t, 1n+i0, q, b, hi))

def ai_at(+sk: SK.Sketch, +R: List<&2, Nat>, +c: Nat, +i: Nat, h: SV.AllImplied(sk, R, c), hi: {SV.lt(i, SV.slen(SV.csides(sk, [c]))) == True{} : Bool}) -> SV.Implied(sk, R, c, i):
  (%Equal.sym(Nat, i, Nat.add(i, 0n), LN.add_zero(i)) : SV.Implied(sk, R, c, _)
    ai_go(sk, R, c, SV.csides(sk, [c]), 0n, i, h, hi))

# not implied in one, implied in the other, over the same kept list
def ka_imp2(+sk: SK.Sketch, +R1: List<&2, Nat>, +R2: List<&2, Nat>, +c: Nat, p: &i: Nat -> ({SV.lt(i, SV.slen(SV.csides(sk, [c]))) == True{} : Bool} & SV.NotImplied(sk, R1, c, i)), fA: SV.AllImplied(sk, R2, c), +hkb: {SV.kept_before(sk, R1, c) == SV.kept_before(sk, R2, c) : List<&2, Nat>}) -> Empty:
  (+i, q) = p
  (+hi, ni) = q
  AG.imp_ni(sk, R2, R1, c, i, Equal.sym(List<&2, Nat>, SV.kept_before(sk, R1, c), SV.kept_before(sk, R2, c), hkb), ai_at(sk, R2, c, i, fA, hi), ni)


def f_kk(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, +dc1: List<&2, SV.Drop>, +dc2: List<&2, SV.Drop>, h1: SV.KeptOk(sk, cls1, SV.reds(cls1), SV.dropped(cls1), c, dc1), h2: SV.KeptOk(sk, cls2, SV.reds(cls2), SV.dropped(cls2), c, dc2)) -> {UQ.GR(sk, c, SV.Kept{dc1}, SV.Kept{dc2}) == True{} : Bool}:
  (nr1, r1) = h1
  (dk1, q1) = r1
  (nr2, r2) = h2
  (dk2, q2) = r2
  L.band_i(True{}, SP.agree(SV.owners(sk), SV.drops(dc1), SV.drops(dc2), c, 0n), {==}, DAG.drops_ag2(sk, cls1, SV.reds(cls1), SV.dropped(cls1), cls2, SV.reds(cls2), SV.dropped(cls2), c, SV.drops(dc1), SV.drops(dc2), hkb, hps, dk1, dk2))

def f_aa(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, +dc1: List<&2, SV.Drop>, +dc2: List<&2, SV.Drop>, +rs1: List<&2, SV.Ref>, +rs2: List<&2, SV.Ref>, h1: SV.AmberOk(sk, cls1, SV.reds(cls1), SV.dropped(cls1), c, dc1), h2: SV.AmberOk(sk, cls2, SV.reds(cls2), SV.dropped(cls2), c, dc2)) -> {UQ.GR(sk, c, SV.Amber{dc1, rs1}, SV.Amber{dc2, rs2}) == True{} : Bool}:
  (nr1, r1) = h1
  (dk1, q1) = r1
  (nr2, r2) = h2
  (dk2, q2) = r2
  L.band_i(True{}, SP.agree(SV.owners(sk), SV.drops(dc1), SV.drops(dc2), c, 0n), {==}, DAG.drops_ag2(sk, cls1, SV.reds(cls1), SV.dropped(cls1), cls2, SV.reds(cls2), SV.dropped(cls2), c, SV.drops(dc1), SV.drops(dc2), hkb, hps, dk1, dk2))

# kept in the first, amber in the second
def f_ka(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, +dc1: List<&2, SV.Drop>, +dc2: List<&2, SV.Drop>, h1: SV.KeptOk(sk, cls1, SV.reds(cls1), SV.dropped(cls1), c, dc1), h2: SV.AmberOk(sk, cls2, SV.reds(cls2), SV.dropped(cls2), c, dc2)) -> Empty:
  (nr1, r1) = h1
  (dk1, q1) = r1
  (dn1, q1b) = q1
  (mt1, fK) = q1b
  (nr2, r2) = h2
  (dk2, q2) = r2
  (dn2, q2b) = q2
  (+ham, fA) = q2b
  +hag = DAG.drops_ag2(sk, cls1, SV.reds(cls1), SV.dropped(cls1), cls2, SV.reds(cls2), SV.dropped(cls2), c, SV.drops(dc1), SV.drops(dc2), hkb, hps, dk1, dk2)
  ka_imp2(sk, SV.reds(cls1), SV.reds(cls2), c, fK(Equal.trans(Bool, SV.is_amberable(sk, c, SV.drops(dc1)), SV.is_amberable(sk, c, SV.drops(dc2)), True{}, AG.amb_cong(sk, c, SV.drops(dc1), SV.drops(dc2), hag), ham)), fA, hkb)

# amber in the first, kept in the second
def f_ak(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, +dc1: List<&2, SV.Drop>, +dc2: List<&2, SV.Drop>, h1: SV.AmberOk(sk, cls1, SV.reds(cls1), SV.dropped(cls1), c, dc1), h2: SV.KeptOk(sk, cls2, SV.reds(cls2), SV.dropped(cls2), c, dc2)) -> Empty:
  (nr1, r1) = h1
  (dk1, q1) = r1
  (dn1, q1b) = q1
  (+ham, fA) = q1b
  (nr2, r2) = h2
  (dk2, q2) = r2
  (dn2, q2b) = q2
  (mt2, fK) = q2b
  +hag = DAG.drops_ag2(sk, cls1, SV.reds(cls1), SV.dropped(cls1), cls2, SV.reds(cls2), SV.dropped(cls2), c, SV.drops(dc1), SV.drops(dc2), hkb, hps, dk1, dk2)
  ka_imp2(sk, SV.reds(cls2), SV.reds(cls1), c, fK(Equal.trans(Bool, SV.is_amberable(sk, c, SV.drops(dc2)), SV.is_amberable(sk, c, SV.drops(dc1)), True{}, Equal.sym(Bool, SV.is_amberable(sk, c, SV.drops(dc1)), SV.is_amberable(sk, c, SV.drops(dc2)), AG.amb_cong(sk, c, SV.drops(dc1), SV.drops(dc2), hag)), ham)), fA, Equal.sym(List<&2, Nat>, SV.kept_before(sk, SV.reds(cls1), c), SV.kept_before(sk, SV.reds(cls2), c), hkb))

# Over
# ----


# over in a, kept in b (a's drops read once for their owners)
def ovk2(+sk: SK.Sketch, +ca: List<&2, SV.Class>, +cb: List<&2, SV.Class>, +c: Nat, +j: Nat, +s: List<&2, Nat>, +w: List<&2, Nat>, +hkb: {SV.kept_before(sk, SV.reds(ca), c) == SV.kept_before(sk, SV.reds(cb), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(ca), SV.dropped(ca), c) == SV.presolved(sk, SV.reds(cb), SV.dropped(cb), c) : List<&2, E.QExpr>}, +dO: List<&2, Nat>, +dK: List<&2, Nat>, +hfa: {HR.hfacts(sk, ca) == True{} : Bool}, +hkd: {SV.kdrops(SV.class_at(ca, c)) == Nil{} : List<&2, Nat>},
  p: ({HR.pk_d(sk, c, dO) == True{} : Bool} & SV.DropsOk(sk, ca, SV.reds(ca), SV.dropped(ca), c, dO)), q: ({SV.band(SV.eq(SV.nth(SV.owners(sk), j), c), SV.band(SV.mem(j, s), SV.clean(SV.owners(sk), SV.reds(ca), SV.dropped(ca), dO, c, s))) == True{} : Bool} & SV.Overdet(SK.Sketch.eqs(sk), s, w)),
  dkK: SV.DropsOk(sk, cb, SV.reds(cb), SV.dropped(cb), c, dK), mt: SV.Matchable(SK.cat(SV.presolved(sk, SV.reds(cb), SV.dropped(cb), c), SV.own_rest(sk, c, dK, SV.neqs(SK.Sketch.eqs(sk)))))) -> Empty:
  (+hp, dkO) = p
  (+hbO, ovd) = q
  +hag = DAG.drops_ag2(sk, ca, SV.reds(ca), SV.dropped(ca), cb, SV.reds(cb), SV.dropped(cb), c, dO, dK, hkb, hps, dkO, dkK)
  OV.over_kept(sk, ca, SV.reds(cb), SV.dropped(cb), c, j, s, w, dO, dK, hbO, ovd, hfa, hkd, L.band_l(KB.allo(SV.owners(sk), dO, c), SV.below(dO, SV.neqs(SK.Sketch.eqs(sk))), hp), hps, hag, mt)

def ovk(+sk: SK.Sketch, +ca: List<&2, SV.Class>, +cb: List<&2, SV.Class>, +c: Nat, +j: Nat, +s: List<&2, Nat>, +w: List<&2, Nat>, +hkb: {SV.kept_before(sk, SV.reds(ca), c) == SV.kept_before(sk, SV.reds(cb), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(ca), SV.dropped(ca), c) == SV.presolved(sk, SV.reds(cb), SV.dropped(cb), c) : List<&2, E.QExpr>}, +ddK: List<&2, SV.Drop>, +hfa: {HR.hfacts(sk, ca) == True{} : Bool}, +hkd: {SV.kdrops(SV.class_at(ca, c)) == Nil{} : List<&2, Nat>},
  ho: SV.OverOk(sk, ca, SV.reds(ca), SV.dropped(ca), c, j, s, w), hk: SV.KeptOk(sk, cb, SV.reds(cb), SV.dropped(cb), c, ddK)) -> Empty:
  (nrO, pO) = ho
  (+dO, qO) = pO
  (dkO, qq) = qO
  (nrK, rK) = hk
  (dkK, qK) = rK
  (dnK, qK2) = qK
  (mt, fK) = qK2
  ovk2(sk, ca, cb, c, j, s, w, hkb, hps, dO, SV.drops(ddK), hfa, hkd, DFC.dok_rb(sk, ca, SV.reds(ca), SV.dropped(ca), c, dO, dkO), qq, dkK, mt)

# over in a, amber in b
def ova(+sk: SK.Sketch, +ca: List<&2, SV.Class>, +cb: List<&2, SV.Class>, +c: Nat, +j: Nat, +s: List<&2, Nat>, +w: List<&2, Nat>, +hkb: {SV.kept_before(sk, SV.reds(ca), c) == SV.kept_before(sk, SV.reds(cb), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(ca), SV.dropped(ca), c) == SV.presolved(sk, SV.reds(cb), SV.dropped(cb), c) : List<&2, E.QExpr>}, +ddA: List<&2, SV.Drop>, ho: SV.OverOk(sk, ca, SV.reds(ca), SV.dropped(ca), c, j, s, w), ha: SV.AmberOk(sk, cb, SV.reds(cb), SV.dropped(cb), c, ddA)) -> Empty:
  (nrO, pO) = ho
  (+dO, qO) = pO
  (dkO, qq) = qO
  (+hbO, ovd) = qq
  (+hov, haw) = ovd
  (nrA, rA) = ha
  (dkA, qA) = rA
  (dnA, qA2) = qA
  (+ham, fA) = qA2
  OV.over_amber(sk, SV.reds(ca), SV.dropped(ca), dO, SV.drops(ddA), c, j, s, hbO, L.band_l(SV.below(s, SV.neqs(SK.Sketch.eqs(sk))), SV.lt(SV.len(w), SV.len(s)), L.band_r(SV.distinct(s), SV.band(SV.below(s, SV.neqs(SK.Sketch.eqs(sk))), SV.lt(SV.len(w), SV.len(s))), hov)),
    DAG.drops_ag2(sk, ca, SV.reds(ca), SV.dropped(ca), cb, SV.reds(cb), SV.dropped(cb), c, dO, SV.drops(ddA), hkb, hps, dkO, dkA), ham)

# Conflict
# --------


def cf_r0(+sk: SK.Sketch, +R1: List<&2, Nat>, +R2: List<&2, Nat>, +c: Nat, +s: List<&2, Nat>, +nd: List<&2, Nat>, +hkb: {SV.kept_before(sk, R1, c) == SV.kept_before(sk, R2, c) : List<&2, Nat>}, +hsub: {SV.sub(s, SV.kept_before(sk, R2, c)) == True{} : Bool}, r0: SV.Ref0(sk, c, s), nr: SV.NoRefute(sk, R2, c)) -> Empty:
  (+ls, r1) = r0
  (+ms, r2) = r1
  (+k, r3) = r2
  NC.cn.m(RF.refute(SK.cat(SV.eqs_of(sk, SV.kept_before(sk, R2, c)), SV.eqs_of(sk, [c])), SK.cats(SK.cats(SV.csides(sk, SV.kept_before(sk, R2, c)), SV.esides(sk)), SV.csides(sk, [c]))), sk, R2, c, s, {==}, hsub, nr, ls, ms, k, r3)

def cf_dq(+sk: SK.Sketch, +R1: List<&2, Nat>, +R2: List<&2, Nat>, +c: Nat, +s: List<&2, Nat>, +nd: List<&2, Nat>, +hkb: {SV.kept_before(sk, R1, c) == SV.kept_before(sk, R2, c) : List<&2, Nat>}, +hsub: {SV.sub(s, SV.kept_before(sk, R2, c)) == True{} : Bool}, +r: DR.DRef, q: SV.RefOk(sk, c, s, SV.ctx(sk, R1, c), r) & ({SV.sub(DR.ref.nd(SV.ents(sk), SV.rfacts(sk, Con{c, s}), r), SV.cat(nd, SV.angle_args(sk, Con{c, s}))) == True{} : Bool} & {SV.sub(nd, DR.ref.nd(SV.ents(sk), SV.rfacts(sk, Con{c, s}), r)) == True{} : Bool}), ndr: SV.NoDirRef(sk, c, SV.kept_before(sk, R2, c), SV.ctx(sk, R2, c))) -> Empty:
  match q:
    case (ro, hn):
      DMP.nodir_mono(sk, c, s, SV.kept_before(sk, R2, c), SV.ctx(sk, R2, c), hsub, ndr, r, (%DAG.cx_ag(sk, R1, R2, c, hkb) : SV.RefOk(sk, c, s, _, r)
        ro))

def cf_dir(+sk: SK.Sketch, +R1: List<&2, Nat>, +R2: List<&2, Nat>, +c: Nat, +s: List<&2, Nat>, +nd: List<&2, Nat>, +hkb: {SV.kept_before(sk, R1, c) == SV.kept_before(sk, R2, c) : List<&2, Nat>}, +hsub: {SV.sub(s, SV.kept_before(sk, R2, c)) == True{} : Bool}, rd: SV.DirRefutes(sk, c, s, SV.ctx(sk, R1, c), nd), ndr: SV.NoDirRef(sk, c, SV.kept_before(sk, R2, c), SV.ctx(sk, R2, c))) -> Empty:
  match rd:
    case (+r, q):
      cf_dq(sk, R1, R2, c, s, nd, hkb, hsub, r, q, ndr)

def cf_or(+sk: SK.Sketch, +R1: List<&2, Nat>, +R2: List<&2, Nat>, +c: Nat, +s: List<&2, Nat>, +nd: List<&2, Nat>, +hkb: {SV.kept_before(sk, R1, c) == SV.kept_before(sk, R2, c) : List<&2, Nat>}, +hsub: {SV.sub(s, SV.kept_before(sk, R2, c)) == True{} : Bool}, h: Or(SV.Ref0(sk, c, s) & {nd == Nil{} : List<&2, Nat>}, SV.DirRefutes(sk, c, s, SV.ctx(sk, R1, c), nd)), nr: SV.NoRefute2(sk, R2, c)) -> Empty:
  match h:
    case Inl{q}:
      (r0, hn) = q
      (nr0, ndr) = nr
      cf_r0(sk, R1, R2, c, s, nd, hkb, hsub, r0, nr0)
    case Inr{rd}:
      (nr0, ndr) = nr
      cf_dir(sk, R1, R2, c, s, nd, hkb, hsub, rd, ndr)

# c a conflict over one red list, without refutation of either kind over
# another, the kept constraints before c the same in both: impossible
def conf_nr2(+sk: SK.Sketch, +R1: List<&2, Nat>, +R2: List<&2, Nat>, +c: Nat, +s: List<&2, Nat>, +nd: List<&2, Nat>, +hkb: {SV.kept_before(sk, R1, c) == SV.kept_before(sk, R2, c) : List<&2, Nat>}, hc: SV.ConflictOk(sk, R1, c, s, nd), nr: SV.NoRefute2(sk, R2, c)) -> Empty:
  (+hb, r) = hc
  (hor, hmin) = r
  +hb2 = L.band_r(SV.distinct(s), SV.band(SV.below(s, c), SV.band(SV.all_driving(sk, s), SV.none_in(s, R1))), hb)
  +hb3 = L.band_r(SV.below(s, c), SV.band(SV.all_driving(sk, s), SV.none_in(s, R1)), hb2)
  cf_or(sk, R1, R2, c, s, nd, hkb, (%hkb : {SV.sub(s, _) == True{} : Bool}
    NC.sub_kb(sk, R1, c, s, L.band_l(SV.below(s, c), SV.band(SV.all_driving(sk, s), SV.none_in(s, R1)), hb2), L.band_l(SV.all_driving(sk, s), SV.none_in(s, R1), hb3), L.band_r(SV.all_driving(sk, s), SV.none_in(s, R1), hb3))), hor, nr)

# The classes at c, driving
# -------------------------

def fv_k(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, +dc1: List<&2, SV.Drop>, k2: SV.Class, +hK2: {SV.class_at(cls2, c) == k2 : SV.Class}, h1: SV.KeptOk(sk, cls1, SV.reds(cls1), SV.dropped(cls1), c, dc1), h2: SV.Fate.driving(sk, cls2, SV.reds(cls2), SV.dropped(cls2), c, k2)) -> {UQ.GR(sk, c, SV.Kept{dc1}, k2) == True{} : Bool}:
  match k2:
    case SV.Kept{+dc2}:
      f_kk(sk, cls1, cls2, c, hkb, hps, hf1, hf2, dc1, dc2, h1, h2)
    case SV.Amber{+dc2, +rs2}:
      absurd({UQ.GR(sk, c, SV.Kept{dc1}, SV.Amber{dc2, rs2}) == True{} : Bool}, f_ka(sk, cls1, cls2, c, hkb, hps, hf1, hf2, dc1, dc2, h1, h2))
    case SV.Over{+j, +s, +w}:
      absurd({UQ.GR(sk, c, SV.Kept{dc1}, SV.Over{j, s, w}) == True{} : Bool}, ovk(sk, cls2, cls1, c, j, s, w, Equal.sym(List<&2, Nat>, SV.kept_before(sk, SV.reds(cls1), c), SV.kept_before(sk, SV.reds(cls2), c), hkb), Equal.sym(List<&2, E.QExpr>, SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c), SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c), hps), dc1, hf2, UQ.kd_over(cls2, c, j, s, w, hK2), h2, h1))
    case SV.Conflict{+s, +cns}:
      absurd({UQ.GR(sk, c, SV.Kept{dc1}, SV.Conflict{s, cns}) == True{} : Bool}, conf_nr2(sk, SV.reds(cls2), SV.reds(cls1), c, s, cns, Equal.sym(List<&2, Nat>, SV.kept_before(sk, SV.reds(cls1), c), SV.kept_before(sk, SV.reds(cls2), c), hkb), h2, nr_k(sk, cls1, SV.reds(cls1), SV.dropped(cls1), c, dc1, h1)))

def fv_a(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, +dc1: List<&2, SV.Drop>, +rs1: List<&2, SV.Ref>, k2: SV.Class, +hK2: {SV.class_at(cls2, c) == k2 : SV.Class}, h1: SV.AmberOk(sk, cls1, SV.reds(cls1), SV.dropped(cls1), c, dc1), h2: SV.Fate.driving(sk, cls2, SV.reds(cls2), SV.dropped(cls2), c, k2)) -> {UQ.GR(sk, c, SV.Amber{dc1, rs1}, k2) == True{} : Bool}:
  match k2:
    case SV.Kept{+dc2}:
      absurd({UQ.GR(sk, c, SV.Amber{dc1, rs1}, SV.Kept{dc2}) == True{} : Bool}, f_ak(sk, cls1, cls2, c, hkb, hps, hf1, hf2, dc1, dc2, h1, h2))
    case SV.Amber{+dc2, +rs2}:
      f_aa(sk, cls1, cls2, c, hkb, hps, hf1, hf2, dc1, dc2, rs1, rs2, h1, h2)
    case SV.Over{+j, +s, +w}:
      absurd({UQ.GR(sk, c, SV.Amber{dc1, rs1}, SV.Over{j, s, w}) == True{} : Bool}, ova(sk, cls2, cls1, c, j, s, w, Equal.sym(List<&2, Nat>, SV.kept_before(sk, SV.reds(cls1), c), SV.kept_before(sk, SV.reds(cls2), c), hkb), Equal.sym(List<&2, E.QExpr>, SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c), SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c), hps), dc1, h2, h1))
    case SV.Conflict{+s, +cns}:
      absurd({UQ.GR(sk, c, SV.Amber{dc1, rs1}, SV.Conflict{s, cns}) == True{} : Bool}, conf_nr2(sk, SV.reds(cls2), SV.reds(cls1), c, s, cns, Equal.sym(List<&2, Nat>, SV.kept_before(sk, SV.reds(cls1), c), SV.kept_before(sk, SV.reds(cls2), c), hkb), h2, nr_a(sk, cls1, SV.reds(cls1), SV.dropped(cls1), c, dc1, h1)))

def fv_o(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, +j: Nat, +s: List<&2, Nat>, +w: List<&2, Nat>, +hK1: {SV.class_at(cls1, c) == SV.Over{j, s, w} : SV.Class}, k2: SV.Class, h1: SV.OverOk(sk, cls1, SV.reds(cls1), SV.dropped(cls1), c, j, s, w), h2: SV.Fate.driving(sk, cls2, SV.reds(cls2), SV.dropped(cls2), c, k2)) -> {UQ.GR(sk, c, SV.Over{j, s, w}, k2) == True{} : Bool}:
  match k2:
    case SV.Kept{+dc2}:
      absurd({UQ.GR(sk, c, SV.Over{j, s, w}, SV.Kept{dc2}) == True{} : Bool}, ovk(sk, cls1, cls2, c, j, s, w, hkb, hps, dc2, hf1, UQ.kd_over(cls1, c, j, s, w, hK1), h1, h2))
    case SV.Amber{+dc2, +rs2}:
      absurd({UQ.GR(sk, c, SV.Over{j, s, w}, SV.Amber{dc2, rs2}) == True{} : Bool}, ova(sk, cls1, cls2, c, j, s, w, hkb, hps, dc2, h1, h2))
    case SV.Over{+j2, +s2, +w2}:
      L.band_i(True{}, SP.agree(SV.owners(sk), Nil{}, Nil{}, c, 0n), {==}, UQ.ag_nil(SV.owners(sk), c, 0n))
    case SV.Conflict{+s2, +cns2}:
      absurd({UQ.GR(sk, c, SV.Over{j, s, w}, SV.Conflict{s2, cns2}) == True{} : Bool}, conf_nr2(sk, SV.reds(cls2), SV.reds(cls1), c, s2, cns2, Equal.sym(List<&2, Nat>, SV.kept_before(sk, SV.reds(cls1), c), SV.kept_before(sk, SV.reds(cls2), c), hkb), h2, nr_o(sk, cls1, SV.reds(cls1), SV.dropped(cls1), c, j, s, w, h1)))

def fv_f(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, +s: List<&2, Nat>, +cns: List<&2, Nat>, k2: SV.Class, h1: SV.ConflictOk(sk, SV.reds(cls1), c, s, cns), h2: SV.Fate.driving(sk, cls2, SV.reds(cls2), SV.dropped(cls2), c, k2)) -> {UQ.GR(sk, c, SV.Conflict{s, cns}, k2) == True{} : Bool}:
  match k2:
    case SV.Kept{+dc2}:
      absurd({UQ.GR(sk, c, SV.Conflict{s, cns}, SV.Kept{dc2}) == True{} : Bool}, conf_nr2(sk, SV.reds(cls1), SV.reds(cls2), c, s, cns, hkb, h1, nr_k(sk, cls2, SV.reds(cls2), SV.dropped(cls2), c, dc2, h2)))
    case SV.Amber{+dc2, +rs2}:
      absurd({UQ.GR(sk, c, SV.Conflict{s, cns}, SV.Amber{dc2, rs2}) == True{} : Bool}, conf_nr2(sk, SV.reds(cls1), SV.reds(cls2), c, s, cns, hkb, h1, nr_a(sk, cls2, SV.reds(cls2), SV.dropped(cls2), c, dc2, h2)))
    case SV.Over{+j2, +s2, +w2}:
      absurd({UQ.GR(sk, c, SV.Conflict{s, cns}, SV.Over{j2, s2, w2}) == True{} : Bool}, conf_nr2(sk, SV.reds(cls1), SV.reds(cls2), c, s, cns, hkb, h1, nr_o(sk, cls2, SV.reds(cls2), SV.dropped(cls2), c, j2, s2, w2, h2)))
    case SV.Conflict{+s2, +cns2}:
      L.band_i(True{}, SP.agree(SV.owners(sk), Nil{}, Nil{}, c, 0n), {==}, UQ.ag_nil(SV.owners(sk), c, 0n))

def fdv(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, k1: SV.Class, k2: SV.Class, +hK1: {SV.class_at(cls1, c) == k1 : SV.Class}, +hK2: {SV.class_at(cls2, c) == k2 : SV.Class}, h1: SV.Fate.driving(sk, cls1, SV.reds(cls1), SV.dropped(cls1), c, k1), h2: SV.Fate.driving(sk, cls2, SV.reds(cls2), SV.dropped(cls2), c, k2)) -> {UQ.GR(sk, c, k1, k2) == True{} : Bool}:
  match k1:
    case SV.Kept{+dc1}:
      fv_k(sk, cls1, cls2, c, hkb, hps, hf1, hf2, dc1, k2, hK2, h1, h2)
    case SV.Amber{+dc1, +rs1}:
      fv_a(sk, cls1, cls2, c, hkb, hps, hf1, hf2, dc1, rs1, k2, hK2, h1, h2)
    case SV.Over{+j, +s, +w}:
      fv_o(sk, cls1, cls2, c, hkb, hps, hf1, hf2, j, s, w, hK1, k2, h1, h2)
    case SV.Conflict{+s, +cns}:
      fv_f(sk, cls1, cls2, c, hkb, hps, hf1, hf2, s, cns, k2, h1, h2)

# The classes at c, driven: both kept, dropping nothing
# -----------------------------------------------------

def fd_k(+sk: SK.Sketch, +c: Nat, +dc1: List<&2, SV.Drop>, k2: SV.Class, h1: {SV.drops(dc1) == Nil{} : List<&2, Nat>}, h2: SV.Fate.driven(k2)) -> {UQ.GR(sk, c, SV.Kept{dc1}, k2) == True{} : Bool}:
  match k2:
    case SV.Kept{+dc2}:
      L.band_i(True{}, SP.agree(SV.owners(sk), SV.drops(dc1), SV.drops(dc2), c, 0n), {==}, (%Equal.sym(List<&2, Nat>, SV.drops(dc1), Nil{}, h1) : {SP.agree(SV.owners(sk), _, SV.drops(dc2), c, 0n) == True{} : Bool}
        (%Equal.sym(List<&2, Nat>, SV.drops(dc2), Nil{}, h2) : {SP.agree(SV.owners(sk), Nil{}, _, c, 0n) == True{} : Bool}
          UQ.ag_nil(SV.owners(sk), c, 0n))))
    case SV.Amber{+dc2, +rs2}:
      absurd({UQ.GR(sk, c, SV.Kept{dc1}, SV.Amber{dc2, rs2}) == True{} : Bool}, h2)
    case SV.Over{+j2, +s2, +w2}:
      absurd({UQ.GR(sk, c, SV.Kept{dc1}, SV.Over{j2, s2, w2}) == True{} : Bool}, h2)
    case SV.Conflict{+s2, +cns2}:
      absurd({UQ.GR(sk, c, SV.Kept{dc1}, SV.Conflict{s2, cns2}) == True{} : Bool}, h2)

def fdr(+sk: SK.Sketch, +c: Nat, k1: SV.Class, +k2: SV.Class, h1: SV.Fate.driven(k1), h2: SV.Fate.driven(k2)) -> {UQ.GR(sk, c, k1, k2) == True{} : Bool}:
  match k1:
    case SV.Kept{+dc1}:
      fd_k(sk, c, dc1, k2, h1, h2)
    case SV.Amber{+dc1, +rs1}:
      absurd({UQ.GR(sk, c, SV.Amber{dc1, rs1}, k2) == True{} : Bool}, h1)
    case SV.Over{+j, +s, +w}:
      absurd({UQ.GR(sk, c, SV.Over{j, s, w}, k2) == True{} : Bool}, h1)
    case SV.Conflict{+s, +cns}:
      absurd({UQ.GR(sk, c, SV.Conflict{s, cns}, k2) == True{} : Bool}, h1)

def fpk(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, b: Bool, +k1: SV.Class, +k2: SV.Class, +hK1: {SV.class_at(cls1, c) == k1 : SV.Class}, +hK2: {SV.class_at(cls2, c) == k2 : SV.Class},
  h1: SV.Fate.pick(sk, cls1, SV.reds(cls1), SV.dropped(cls1), c, b, k1), h2: SV.Fate.pick(sk, cls2, SV.reds(cls2), SV.dropped(cls2), c, b, k2)) -> {UQ.GR(sk, c, k1, k2) == True{} : Bool}:
  match b:
    case True{}:
      fdr(sk, c, k1, k2, h1, h2)
    case False{}:
      fdv(sk, cls1, cls2, c, hkb, hps, hf1, hf2, k1, k2, hK1, hK2, h1, h2)

# the two Fates at c: the same kind, the same drops
def fate_ag2(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, f1: SV.Fate(sk, cls1, c), f2: SV.Fate(sk, cls2, c)) -> {UQ.GR(sk, c, SV.class_at(cls1, c), SV.class_at(cls2, c)) == True{} : Bool}:
  fpk(sk, cls1, cls2, c, hkb, hps, hf1, hf2, SV.driven(sk, c), SV.class_at(cls1, c), SV.class_at(cls2, c), {==}, {==}, f1, f2)

# The walk
# --------

# both Honests from c on, with the same kept list and solved equations
# before c: the same kind and drops at every constraint from c
def mw2(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, n: Nat, +c: Nat, H1: SV.Honest.go(sk, cls1, n, c), H2: SV.Honest.go(sk, cls2, n, c),
  +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool})
  -> {UQ.AA(sk, cls1, cls2, n, c) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      (f1, r1) = H1
      (f2, r2) = H2
      +hc = fate_ag2(sk, cls1, cls2, c, hkb, hps, hf1, hf2, f1, f2)
      UQ.mw.c(sk, cls1, cls2, m, c, hf1, hf2, hc, UQ.mw.next(sk, cls1, cls2, c, hkb, hps, hf1, hf2, hc), k2 => p2 => mw2(sk, cls1, cls2, m, 1n+c, r1, r2, k2, p2, hf1, hf2))

# The law
# -------

def hu_go(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +j: Nat, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, q1: SV.Honest(sk, cls1), q2: SV.Honest(sk, cls2))
  -> M.Both({SV.kind(SV.class_at(cls1, c)) == SV.kind(SV.class_at(cls2, c)) : Nat}, {SV.mem(j, SV.dropped(cls1)) == SV.mem(j, SV.dropped(cls2)) : Bool}):
  (+hn1, g1) = q1
  (+hn2, g2) = q2
  +hA = mw2(sk, cls1, cls2, SV.ncons(sk), 0n, g1, g2, AG.kb_zero(sk, SV.reds(cls1), SV.reds(cls2)), AG.ps_zero(sk, SV.reds(cls1), SV.dropped(cls1), SV.reds(cls2), SV.dropped(cls2)), hf1, hf2)
  (UQ.hu_k(sk, cls1, cls2, c, SV.lt(c, SV.ncons(sk)), {==}, hn1, hn2, hA), UQ.hu_d(sk, cls1, cls2, j, SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))), {==}, hf1, hf2, hA))

def hu_cmb(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +j: Nat, p1: ({HR.hfacts(sk, cls1) == True{} : Bool} & SV.Honest(sk, cls1)), p2: ({HR.hfacts(sk, cls2) == True{} : Bool} & SV.Honest(sk, cls2)))
  -> M.Both({SV.kind(SV.class_at(cls1, c)) == SV.kind(SV.class_at(cls2, c)) : Nat}, {SV.mem(j, SV.dropped(cls1)) == SV.mem(j, SV.dropped(cls2)) : Bool}):
  (+hf1, q1) = p1
  (+hf2, q2) = p2
  hu_go(sk, cls1, cls2, c, j, hf1, hf2, q1, q2)

# THE DRAFT LAW (honest_unique over the extended Honest): honest
# classifications agree. Every constraint gets the same kind, and every
# equation is dropped in both or in neither
def honest_unique2(+sk: SK.Sketch, +c1: List<&2, SV.Class>, h1: SV.Honest(sk, c1), +c2: List<&2, SV.Class>, h2: SV.Honest(sk, c2), +c: Nat, +j: Nat)
  -> M.Both({SV.kind(SV.class_at(c1, c)) == SV.kind(SV.class_at(c2, c)) : Nat}, {SV.mem(j, SV.dropped(c1)) == SV.mem(j, SV.dropped(c2)) : Bool}):
  hu_cmb(sk, c1, c2, c, j, DFC.hon_rb(sk, c1, h1), DFC.hon_rb(sk, c2, h2))
