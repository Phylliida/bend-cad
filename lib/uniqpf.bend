# bend-cad: law 5, honest_unique (PLAN-sk13a S6): any two honest
# classifications of a sketch agree. Every constraint has the same kind in
# both, and every equation is dropped in both or in neither. Proofs only.
#
# Both are read once (lib/hreadpf.bend: hon_rb), so that each class drops
# only its own equations. Then walk the constraints in order with both
# Honests, carrying two list equalities: the kept constraints before c,
# and the solved equations before c, are the same in both. At c the two
# Fates meet (fate_ag): the same driven flag; then every pair of classes
# either has the same kind and the same drops among c's equations, or is
# impossible:
# - kept or amber against kept or amber: the same drops (lib/agreepf.bend:
#   drops_ag), so the same amberability, and Implied against NotImplied
#   cannot meet (ka_imp);
# - a conflict against anything else: lib/nrconfpf.bend;
# - over against kept or amber: lib/overpf.bend.
# With c's kind and drops the same, the two equalities carry to c + 1
# (agreepf: kb_ag, ps_red, ps_kept). The law reads the walk's facts at c
# and at j's owner; past the end both classes are Kept{[]} and nothing is
# dropped.
#
# Generated from tools/drafts/uniqpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/ring.bend as E
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as L
import ./kbpf.bend as KB
import ./ownpf.bend as OW
import ./solvedpf.bend as SP
import ./clslpf.bend as CL
import ./agreepf.bend as AG
import ./hreadpf.bend as HR
import ./nrconfpf.bend as NC
import ./overpf.bend as OV

def absurd(-A: Type, x: Empty) -> A:
  match x:


# c has the same kind, and the same drops among its own equations
def GR(+sk: SK.Sketch, +c: Nat, +k1: SV.Class, +k2: SV.Class) -> Bool:
  SV.band(SV.eq(SV.kind(k1), SV.kind(k2)), SP.agree(SV.owners(sk), SV.kdrops(k1), SV.kdrops(k2), c, 0n))

def ag_nil(own_s: List<&2, Nat>, +c: Nat, +k: Nat) -> {SP.agree(own_s, Nil{}, Nil{}, c, k) == True{} : Bool}:
  match own_s:
    case Nil{}:
      {==}
    case Con{+o, +t}:
      L.band_i(SV.bor(SV.bnot(SV.eq(o, c)), True{}), SP.agree(t, Nil{}, Nil{}, c, 1n+k), L.bor_r(SV.bnot(SV.eq(o, c)), True{}, {==}), ag_nil(t, c, 1n+k))

# the NoRefute every unconflicted Fate starts with
def nr_k(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, h: SV.KeptOk(sk, R, D, c, d)) -> SV.NoRefute(sk, R, c):
  (nr, r) = h
  nr

def nr_a(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +d: List<&2, Nat>, h: SV.AmberOk(sk, R, D, c, d)) -> SV.NoRefute(sk, R, c):
  (nr, r) = h
  nr

def nr_o(+sk: SK.Sketch, +R: List<&2, Nat>, +D: List<&2, Nat>, +c: Nat, +j: Nat, +s: List<&2, Nat>, +w: List<&2, Nat>, h: SV.OverOk(sk, R, D, c, j, s, w)) -> SV.NoRefute(sk, R, c):
  (nr, r) = h
  nr

# Kept and Amber
# --------------

# not implied in one, implied in the other, over the same kept list
def ka_imp(+sk: SK.Sketch, +R1: List<&2, Nat>, +R2: List<&2, Nat>, +c: Nat, p: &i: Nat -> ({SV.lt(i, SV.slen(SV.csides(sk, [c]))) == True{} : Bool} & SV.NotImplied(sk, R1, c, i)),
  fA: @i: Nat -> {SV.lt(i, SV.slen(SV.csides(sk, [c]))) == True{} : Bool} -> SV.Implied(sk, R2, c, i), +hkb: {SV.kept_before(sk, R1, c) == SV.kept_before(sk, R2, c) : List<&2, Nat>}) -> Empty:
  (+i, q) = p
  (+hi, ni) = q
  AG.imp_ni(sk, R2, R1, c, i, Equal.sym(List<&2, Nat>, SV.kept_before(sk, R1, c), SV.kept_before(sk, R2, c), hkb), fA(i, hi), ni)

def f_kk(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, +dc1: List<&2, SV.Drop>, +dc2: List<&2, SV.Drop>, h1: SV.KeptOk(sk, SV.reds(cls1), SV.dropped(cls1), c, SV.drops(dc1)), h2: SV.KeptOk(sk, SV.reds(cls2), SV.dropped(cls2), c, SV.drops(dc2))) -> {GR(sk, c, SV.Kept{dc1}, SV.Kept{dc2}) == True{} : Bool}:
  (nr1, r1) = h1
  (dk1, q1) = r1
  (nr2, r2) = h2
  (dk2, q2) = r2
  L.band_i(True{}, SP.agree(SV.owners(sk), SV.drops(dc1), SV.drops(dc2), c, 0n), {==}, AG.drops_ag(sk, SV.reds(cls1), SV.dropped(cls1), SV.reds(cls2), SV.dropped(cls2), c, SV.drops(dc1), SV.drops(dc2), hps, dk1, dk2))

def f_aa(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, +dc1: List<&2, SV.Drop>, +dc2: List<&2, SV.Drop>, +rs1: List<&2, SV.Ref>, +rs2: List<&2, SV.Ref>, h1: SV.AmberOk(sk, SV.reds(cls1), SV.dropped(cls1), c, SV.drops(dc1)), h2: SV.AmberOk(sk, SV.reds(cls2), SV.dropped(cls2), c, SV.drops(dc2))) -> {GR(sk, c, SV.Amber{dc1, rs1}, SV.Amber{dc2, rs2}) == True{} : Bool}:
  (nr1, r1) = h1
  (dk1, q1) = r1
  (nr2, r2) = h2
  (dk2, q2) = r2
  L.band_i(True{}, SP.agree(SV.owners(sk), SV.drops(dc1), SV.drops(dc2), c, 0n), {==}, AG.drops_ag(sk, SV.reds(cls1), SV.dropped(cls1), SV.reds(cls2), SV.dropped(cls2), c, SV.drops(dc1), SV.drops(dc2), hps, dk1, dk2))

# kept in the first, amber in the second
def f_ka(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, +d1: List<&2, Nat>, +d2: List<&2, Nat>, h1: SV.KeptOk(sk, SV.reds(cls1), SV.dropped(cls1), c, d1), h2: SV.AmberOk(sk, SV.reds(cls2), SV.dropped(cls2), c, d2)) -> Empty:
  (nr1, r1) = h1
  (dk1, q1) = r1
  (mt1, fK) = q1
  (nr2, r2) = h2
  (dk2, q2) = r2
  (+ham, fA) = q2
  +hag = AG.drops_ag(sk, SV.reds(cls1), SV.dropped(cls1), SV.reds(cls2), SV.dropped(cls2), c, d1, d2, hps, dk1, dk2)
  ka_imp(sk, SV.reds(cls1), SV.reds(cls2), c, fK(Equal.trans(Bool, SV.is_amberable(sk, c, d1), SV.is_amberable(sk, c, d2), True{}, AG.amb_cong(sk, c, d1, d2, hag), ham)), fA, hkb)

# amber in the first, kept in the second
def f_ak(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, +d1: List<&2, Nat>, +d2: List<&2, Nat>, h1: SV.AmberOk(sk, SV.reds(cls1), SV.dropped(cls1), c, d1), h2: SV.KeptOk(sk, SV.reds(cls2), SV.dropped(cls2), c, d2)) -> Empty:
  (nr1, r1) = h1
  (dk1, q1) = r1
  (+ham, fA) = q1
  (nr2, r2) = h2
  (dk2, q2) = r2
  (mt2, fK) = q2
  +hag = AG.drops_ag(sk, SV.reds(cls1), SV.dropped(cls1), SV.reds(cls2), SV.dropped(cls2), c, d1, d2, hps, dk1, dk2)
  ka_imp(sk, SV.reds(cls2), SV.reds(cls1), c, fK(Equal.trans(Bool, SV.is_amberable(sk, c, d2), SV.is_amberable(sk, c, d1), True{}, Equal.sym(Bool, SV.is_amberable(sk, c, d1), SV.is_amberable(sk, c, d2), AG.amb_cong(sk, c, d1, d2, hag)), ham)), fA,
    Equal.sym(List<&2, Nat>, SV.kept_before(sk, SV.reds(cls1), c), SV.kept_before(sk, SV.reds(cls2), c), hkb))

# Over
# ----


# over in a, kept in b (a's drops read once for their owners)
def ovk2(+sk: SK.Sketch, +ca: List<&2, SV.Class>, +Rb: List<&2, Nat>, +Db: List<&2, Nat>, +c: Nat, +j: Nat, +s: List<&2, Nat>, +w: List<&2, Nat>, +dO: List<&2, Nat>, +dK: List<&2, Nat>,
  +hps: {SV.presolved(sk, SV.reds(ca), SV.dropped(ca), c) == SV.presolved(sk, Rb, Db, c) : List<&2, E.QExpr>}, +hfa: {HR.hfacts(sk, ca) == True{} : Bool}, +hkd: {SV.kdrops(SV.class_at(ca, c)) == Nil{} : List<&2, Nat>},
  p: ({HR.pk_d(sk, c, dO) == True{} : Bool} & SV.DropsOk(sk, SV.reds(ca), SV.dropped(ca), c, dO)), q: ({SV.band(SV.eq(SV.nth(SV.owners(sk), j), c), SV.band(SV.mem(j, s), SV.clean(SV.owners(sk), SV.reds(ca), SV.dropped(ca), dO, c, s))) == True{} : Bool} & SV.Overdet(SK.Sketch.eqs(sk), s, w)),
  dkK: SV.DropsOk(sk, Rb, Db, c, dK), mt: SV.Matchable(SK.cat(SV.presolved(sk, Rb, Db, c), SV.own_rest(sk, c, dK, SV.neqs(SK.Sketch.eqs(sk)))))) -> Empty:
  (+hp, dkO) = p
  (+hbO, ovd) = q
  +hag = AG.drops_ag(sk, SV.reds(ca), SV.dropped(ca), Rb, Db, c, dO, dK, hps, dkO, dkK)
  OV.over_kept(sk, ca, Rb, Db, c, j, s, w, dO, dK, hbO, ovd, hfa, hkd, L.band_l(KB.allo(SV.owners(sk), dO, c), SV.below(dO, SV.neqs(SK.Sketch.eqs(sk))), hp), hps, hag, mt)

def ovk(+sk: SK.Sketch, +ca: List<&2, SV.Class>, +Rb: List<&2, Nat>, +Db: List<&2, Nat>, +c: Nat, +j: Nat, +s: List<&2, Nat>, +w: List<&2, Nat>, +dK: List<&2, Nat>,
  +hps: {SV.presolved(sk, SV.reds(ca), SV.dropped(ca), c) == SV.presolved(sk, Rb, Db, c) : List<&2, E.QExpr>}, +hfa: {HR.hfacts(sk, ca) == True{} : Bool}, +hkd: {SV.kdrops(SV.class_at(ca, c)) == Nil{} : List<&2, Nat>},
  ho: SV.OverOk(sk, SV.reds(ca), SV.dropped(ca), c, j, s, w), hk: SV.KeptOk(sk, Rb, Db, c, dK)) -> Empty:
  (nrO, pO) = ho
  (+dO, qO) = pO
  (dkO, qq) = qO
  (nrK, rK) = hk
  (dkK, qK) = rK
  (mt, fK) = qK
  ovk2(sk, ca, Rb, Db, c, j, s, w, dO, dK, hps, hfa, hkd, HR.dok_rb(sk, SV.reds(ca), SV.dropped(ca), c, dO, dkO), qq, dkK, mt)

# over in a, amber in b
def ova(+sk: SK.Sketch, +Ra: List<&2, Nat>, +Da: List<&2, Nat>, +Rb: List<&2, Nat>, +Db: List<&2, Nat>, +c: Nat, +j: Nat, +s: List<&2, Nat>, +w: List<&2, Nat>, +dA: List<&2, Nat>,
  +hps: {SV.presolved(sk, Ra, Da, c) == SV.presolved(sk, Rb, Db, c) : List<&2, E.QExpr>}, ho: SV.OverOk(sk, Ra, Da, c, j, s, w), ha: SV.AmberOk(sk, Rb, Db, c, dA)) -> Empty:
  (nrO, pO) = ho
  (+dO, qO) = pO
  (dkO, qq) = qO
  (+hbO, ovd) = qq
  (+hov, haw) = ovd
  (nrA, rA) = ha
  (dkA, qA) = rA
  (+ham, fA) = qA
  OV.over_amber(sk, Ra, Da, dO, dA, c, j, s, hbO, L.band_l(SV.below(s, SV.neqs(SK.Sketch.eqs(sk))), SV.lt(SV.len(w), SV.len(s)), L.band_r(SV.distinct(s), SV.band(SV.below(s, SV.neqs(SK.Sketch.eqs(sk))), SV.lt(SV.len(w), SV.len(s))), hov)),
    AG.drops_ag(sk, Ra, Da, Rb, Db, c, dO, dA, hps, dkO, dkA), ham)

def kd_over(+cls: List<&2, SV.Class>, +c: Nat, +j: Nat, +s: List<&2, Nat>, +w: List<&2, Nat>, +hK: {SV.class_at(cls, c) == SV.Over{j, s, w} : SV.Class}) -> {SV.kdrops(SV.class_at(cls, c)) == Nil{} : List<&2, Nat>}:
  Equal.cong(SV.Class, List<&2, Nat>, x => SV.kdrops(x), SV.class_at(cls, c), SV.Over{j, s, w}, hK)

# The classes at c, driving
# -------------------------


def fv_k(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, +dc1: List<&2, SV.Drop>, k2: SV.Class, +hK2: {SV.class_at(cls2, c) == k2 : SV.Class}, h1: SV.KeptOk(sk, SV.reds(cls1), SV.dropped(cls1), c, SV.drops(dc1)), h2: SV.Fate.driving(sk, SV.reds(cls2), SV.dropped(cls2), c, k2)) -> {GR(sk, c, SV.Kept{dc1}, k2) == True{} : Bool}:
  match k2:
    case SV.Kept{+dc2}:
      f_kk(sk, cls1, cls2, c, hkb, hps, hf1, hf2, dc1, dc2, h1, h2)
    case SV.Amber{+dc2, +rs2}:
      absurd({GR(sk, c, SV.Kept{dc1}, SV.Amber{dc2, rs2}) == True{} : Bool}, f_ka(sk, cls1, cls2, c, hkb, hps, hf1, hf2, SV.drops(dc1), SV.drops(dc2), h1, h2))
    case SV.Over{+j, +s, +w}:
      absurd({GR(sk, c, SV.Kept{dc1}, SV.Over{j, s, w}) == True{} : Bool}, ovk(sk, cls2, SV.reds(cls1), SV.dropped(cls1), c, j, s, w, SV.drops(dc1), Equal.sym(List<&2, E.QExpr>, SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c), SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c), hps), hf2, kd_over(cls2, c, j, s, w, hK2), h2, h1))
    case SV.Conflict{+s}:
      absurd({GR(sk, c, SV.Kept{dc1}, SV.Conflict{s}) == True{} : Bool}, NC.conf_nr(sk, SV.reds(cls2), SV.reds(cls1), c, s, Equal.sym(List<&2, Nat>, SV.kept_before(sk, SV.reds(cls1), c), SV.kept_before(sk, SV.reds(cls2), c), hkb), h2, nr_k(sk, SV.reds(cls1), SV.dropped(cls1), c, SV.drops(dc1), h1)))

def fv_a(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, +dc1: List<&2, SV.Drop>, +rs1: List<&2, SV.Ref>, k2: SV.Class, +hK2: {SV.class_at(cls2, c) == k2 : SV.Class}, h1: SV.AmberOk(sk, SV.reds(cls1), SV.dropped(cls1), c, SV.drops(dc1)), h2: SV.Fate.driving(sk, SV.reds(cls2), SV.dropped(cls2), c, k2)) -> {GR(sk, c, SV.Amber{dc1, rs1}, k2) == True{} : Bool}:
  match k2:
    case SV.Kept{+dc2}:
      absurd({GR(sk, c, SV.Amber{dc1, rs1}, SV.Kept{dc2}) == True{} : Bool}, f_ak(sk, cls1, cls2, c, hkb, hps, hf1, hf2, SV.drops(dc1), SV.drops(dc2), h1, h2))
    case SV.Amber{+dc2, +rs2}:
      f_aa(sk, cls1, cls2, c, hkb, hps, hf1, hf2, dc1, dc2, rs1, rs2, h1, h2)
    case SV.Over{+j, +s, +w}:
      absurd({GR(sk, c, SV.Amber{dc1, rs1}, SV.Over{j, s, w}) == True{} : Bool}, ova(sk, SV.reds(cls2), SV.dropped(cls2), SV.reds(cls1), SV.dropped(cls1), c, j, s, w, SV.drops(dc1), Equal.sym(List<&2, E.QExpr>, SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c), SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c), hps), h2, h1))
    case SV.Conflict{+s}:
      absurd({GR(sk, c, SV.Amber{dc1, rs1}, SV.Conflict{s}) == True{} : Bool}, NC.conf_nr(sk, SV.reds(cls2), SV.reds(cls1), c, s, Equal.sym(List<&2, Nat>, SV.kept_before(sk, SV.reds(cls1), c), SV.kept_before(sk, SV.reds(cls2), c), hkb), h2, nr_a(sk, SV.reds(cls1), SV.dropped(cls1), c, SV.drops(dc1), h1)))

def fv_o(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, +j: Nat, +s: List<&2, Nat>, +w: List<&2, Nat>, +hK1: {SV.class_at(cls1, c) == SV.Over{j, s, w} : SV.Class}, k2: SV.Class, h1: SV.OverOk(sk, SV.reds(cls1), SV.dropped(cls1), c, j, s, w), h2: SV.Fate.driving(sk, SV.reds(cls2), SV.dropped(cls2), c, k2)) -> {GR(sk, c, SV.Over{j, s, w}, k2) == True{} : Bool}:
  match k2:
    case SV.Kept{+dc2}:
      absurd({GR(sk, c, SV.Over{j, s, w}, SV.Kept{dc2}) == True{} : Bool}, ovk(sk, cls1, SV.reds(cls2), SV.dropped(cls2), c, j, s, w, SV.drops(dc2), hps, hf1, kd_over(cls1, c, j, s, w, hK1), h1, h2))
    case SV.Amber{+dc2, +rs2}:
      absurd({GR(sk, c, SV.Over{j, s, w}, SV.Amber{dc2, rs2}) == True{} : Bool}, ova(sk, SV.reds(cls1), SV.dropped(cls1), SV.reds(cls2), SV.dropped(cls2), c, j, s, w, SV.drops(dc2), hps, h1, h2))
    case SV.Over{+j2, +s2, +w2}:
      L.band_i(True{}, SP.agree(SV.owners(sk), Nil{}, Nil{}, c, 0n), {==}, ag_nil(SV.owners(sk), c, 0n))
    case SV.Conflict{+s2}:
      absurd({GR(sk, c, SV.Over{j, s, w}, SV.Conflict{s2}) == True{} : Bool}, NC.conf_nr(sk, SV.reds(cls2), SV.reds(cls1), c, s2, Equal.sym(List<&2, Nat>, SV.kept_before(sk, SV.reds(cls1), c), SV.kept_before(sk, SV.reds(cls2), c), hkb), h2, nr_o(sk, SV.reds(cls1), SV.dropped(cls1), c, j, s, w, h1)))

def fv_f(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, +s: List<&2, Nat>, k2: SV.Class, h1: SV.ConflictOk(sk, SV.reds(cls1), c, s), h2: SV.Fate.driving(sk, SV.reds(cls2), SV.dropped(cls2), c, k2)) -> {GR(sk, c, SV.Conflict{s}, k2) == True{} : Bool}:
  match k2:
    case SV.Kept{+dc2}:
      absurd({GR(sk, c, SV.Conflict{s}, SV.Kept{dc2}) == True{} : Bool}, NC.conf_nr(sk, SV.reds(cls1), SV.reds(cls2), c, s, hkb, h1, nr_k(sk, SV.reds(cls2), SV.dropped(cls2), c, SV.drops(dc2), h2)))
    case SV.Amber{+dc2, +rs2}:
      absurd({GR(sk, c, SV.Conflict{s}, SV.Amber{dc2, rs2}) == True{} : Bool}, NC.conf_nr(sk, SV.reds(cls1), SV.reds(cls2), c, s, hkb, h1, nr_a(sk, SV.reds(cls2), SV.dropped(cls2), c, SV.drops(dc2), h2)))
    case SV.Over{+j2, +s2, +w2}:
      absurd({GR(sk, c, SV.Conflict{s}, SV.Over{j2, s2, w2}) == True{} : Bool}, NC.conf_nr(sk, SV.reds(cls1), SV.reds(cls2), c, s, hkb, h1, nr_o(sk, SV.reds(cls2), SV.dropped(cls2), c, j2, s2, w2, h2)))
    case SV.Conflict{+s2}:
      L.band_i(True{}, SP.agree(SV.owners(sk), Nil{}, Nil{}, c, 0n), {==}, ag_nil(SV.owners(sk), c, 0n))

def fdv(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, k1: SV.Class, k2: SV.Class, +hK1: {SV.class_at(cls1, c) == k1 : SV.Class}, +hK2: {SV.class_at(cls2, c) == k2 : SV.Class}, h1: SV.Fate.driving(sk, SV.reds(cls1), SV.dropped(cls1), c, k1), h2: SV.Fate.driving(sk, SV.reds(cls2), SV.dropped(cls2), c, k2)) -> {GR(sk, c, k1, k2) == True{} : Bool}:
  match k1:
    case SV.Kept{+dc1}:
      fv_k(sk, cls1, cls2, c, hkb, hps, hf1, hf2, dc1, k2, hK2, h1, h2)
    case SV.Amber{+dc1, +rs1}:
      fv_a(sk, cls1, cls2, c, hkb, hps, hf1, hf2, dc1, rs1, k2, hK2, h1, h2)
    case SV.Over{+j, +s, +w}:
      fv_o(sk, cls1, cls2, c, hkb, hps, hf1, hf2, j, s, w, hK1, k2, h1, h2)
    case SV.Conflict{+s}:
      fv_f(sk, cls1, cls2, c, hkb, hps, hf1, hf2, s, k2, h1, h2)

# The classes at c, driven: both kept, dropping nothing
# -----------------------------------------------------

def fd_k(+sk: SK.Sketch, +c: Nat, +dc1: List<&2, SV.Drop>, k2: SV.Class, h1: {SV.drops(dc1) == Nil{} : List<&2, Nat>}, h2: SV.Fate.driven(k2)) -> {GR(sk, c, SV.Kept{dc1}, k2) == True{} : Bool}:
  match k2:
    case SV.Kept{+dc2}:
      L.band_i(True{}, SP.agree(SV.owners(sk), SV.drops(dc1), SV.drops(dc2), c, 0n), {==}, (%Equal.sym(List<&2, Nat>, SV.drops(dc1), Nil{}, h1) : {SP.agree(SV.owners(sk), _, SV.drops(dc2), c, 0n) == True{} : Bool}
        (%Equal.sym(List<&2, Nat>, SV.drops(dc2), Nil{}, h2) : {SP.agree(SV.owners(sk), Nil{}, _, c, 0n) == True{} : Bool}
          ag_nil(SV.owners(sk), c, 0n))))
    case SV.Amber{+dc2, +rs2}:
      absurd({GR(sk, c, SV.Kept{dc1}, SV.Amber{dc2, rs2}) == True{} : Bool}, h2)
    case SV.Over{+j2, +s2, +w2}:
      absurd({GR(sk, c, SV.Kept{dc1}, SV.Over{j2, s2, w2}) == True{} : Bool}, h2)
    case SV.Conflict{+s2}:
      absurd({GR(sk, c, SV.Kept{dc1}, SV.Conflict{s2}) == True{} : Bool}, h2)

def fdr(+sk: SK.Sketch, +c: Nat, k1: SV.Class, +k2: SV.Class, h1: SV.Fate.driven(k1), h2: SV.Fate.driven(k2)) -> {GR(sk, c, k1, k2) == True{} : Bool}:
  match k1:
    case SV.Kept{+dc1}:
      fd_k(sk, c, dc1, k2, h1, h2)
    case SV.Amber{+dc1, +rs1}:
      absurd({GR(sk, c, SV.Amber{dc1, rs1}, k2) == True{} : Bool}, h1)
    case SV.Over{+j, +s, +w}:
      absurd({GR(sk, c, SV.Over{j, s, w}, k2) == True{} : Bool}, h1)
    case SV.Conflict{+s}:
      absurd({GR(sk, c, SV.Conflict{s}, k2) == True{} : Bool}, h1)

def fpk(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, b: Bool, +k1: SV.Class, +k2: SV.Class, +hK1: {SV.class_at(cls1, c) == k1 : SV.Class}, +hK2: {SV.class_at(cls2, c) == k2 : SV.Class},
  h1: SV.Fate.pick(sk, SV.reds(cls1), SV.dropped(cls1), c, b, k1), h2: SV.Fate.pick(sk, SV.reds(cls2), SV.dropped(cls2), c, b, k2)) -> {GR(sk, c, k1, k2) == True{} : Bool}:
  match b:
    case True{}:
      fdr(sk, c, k1, k2, h1, h2)
    case False{}:
      fdv(sk, cls1, cls2, c, hkb, hps, hf1, hf2, k1, k2, hK1, hK2, h1, h2)

# the two Fates at c: the same kind, the same drops
def fate_ag(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, f1: SV.Fate(sk, cls1, c), f2: SV.Fate(sk, cls2, c)) -> {GR(sk, c, SV.class_at(cls1, c), SV.class_at(cls2, c)) == True{} : Bool}:
  fpk(sk, cls1, cls2, c, hkb, hps, hf1, hf2, SV.driven(sk, c), SV.class_at(cls1, c), SV.class_at(cls2, c), {==}, {==}, f1, f2)

# The walk
# --------

def AA(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, n: Nat, +c: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+m:
      SV.band(GR(sk, c, SV.class_at(cls1, c), SV.class_at(cls2, c)), AA(sk, cls1, cls2, m, 1n+c))

def ps_step(b: Bool, +sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +e: {SV.mem(c, SV.reds(cls1)) == b : Bool}, +hm: {SV.mem(c, SV.reds(cls1)) == SV.mem(c, SV.reds(cls2)) : Bool},
  +hD1: {CL.downs(SV.owners(sk), cls1, 0n) == True{} : Bool}, +hD2: {CL.downs(SV.owners(sk), cls2, 0n) == True{} : Bool}, +hag: {SP.agree(SV.owners(sk), SV.kdrops(SV.class_at(cls1, c)), SV.kdrops(SV.class_at(cls2, c)), c, 0n) == True{} : Bool},
  +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}) -> {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), 1n+c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), 1n+c) : List<&2, E.QExpr>}:
  match b:
    case True{}:
      AG.ps_red(sk, SV.reds(cls1), SV.dropped(cls1), SV.reds(cls2), SV.dropped(cls2), c, e, Equal.trans(Bool, SV.mem(c, SV.reds(cls2)), SV.mem(c, SV.reds(cls1)), True{}, Equal.sym(Bool, SV.mem(c, SV.reds(cls1)), SV.mem(c, SV.reds(cls2)), hm), e), hps)
    case False{}:
      AG.ps_kept(sk, cls1, cls2, c, e, Equal.trans(Bool, SV.mem(c, SV.reds(cls2)), SV.mem(c, SV.reds(cls1)), False{}, Equal.sym(Bool, SV.mem(c, SV.reds(cls1)), SV.mem(c, SV.reds(cls2)), hm), e), hD1, hD2, hag, hps)


def mw.next(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>},
  +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, +hc: {GR(sk, c, SV.class_at(cls1, c), SV.class_at(cls2, c)) == True{} : Bool})
  -> ({SV.kept_before(sk, SV.reds(cls1), 1n+c) == SV.kept_before(sk, SV.reds(cls2), 1n+c) : List<&2, Nat>} & {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), 1n+c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), 1n+c) : List<&2, E.QExpr>}):
  +hm = AG.red_ag(cls1, cls2, c, L.eq_ok(SV.kind(SV.class_at(cls1, c)), SV.kind(SV.class_at(cls2, c)), L.band_l(SV.eq(SV.kind(SV.class_at(cls1, c)), SV.kind(SV.class_at(cls2, c))), SP.agree(SV.owners(sk), SV.kdrops(SV.class_at(cls1, c)), SV.kdrops(SV.class_at(cls2, c)), c, 0n), hc)))
  (AG.kb_ag(sk, SV.reds(cls1), SV.reds(cls2), c, hm, hkb), ps_step(SV.mem(c, SV.reds(cls1)), sk, cls1, cls2, c, {==}, hm, L.band_l(CL.downs(SV.owners(sk), cls1, 0n), SV.below(SV.dropped(cls1), SV.neqs(SK.Sketch.eqs(sk))), hf1), L.band_l(CL.downs(SV.owners(sk), cls2, 0n), SV.below(SV.dropped(cls2), SV.neqs(SK.Sketch.eqs(sk))), hf2), L.band_r(SV.eq(SV.kind(SV.class_at(cls1, c)), SV.kind(SV.class_at(cls2, c))), SP.agree(SV.owners(sk), SV.kdrops(SV.class_at(cls1, c)), SV.kdrops(SV.class_at(cls2, c)), c, 0n), hc), hps))

def mw.c(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +m: Nat, +c: Nat, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, +hc: {GR(sk, c, SV.class_at(cls1, c), SV.class_at(cls2, c)) == True{} : Bool},
  p: ({SV.kept_before(sk, SV.reds(cls1), 1n+c) == SV.kept_before(sk, SV.reds(cls2), 1n+c) : List<&2, Nat>} & {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), 1n+c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), 1n+c) : List<&2, E.QExpr>}),
  ih: {SV.kept_before(sk, SV.reds(cls1), 1n+c) == SV.kept_before(sk, SV.reds(cls2), 1n+c) : List<&2, Nat>} -> {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), 1n+c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), 1n+c) : List<&2, E.QExpr>} -> {AA(sk, cls1, cls2, m, 1n+c) == True{} : Bool})
  -> {AA(sk, cls1, cls2, 1n+m, c) == True{} : Bool}:
  (+hkb2, hps2) = p
  L.band_i(GR(sk, c, SV.class_at(cls1, c), SV.class_at(cls2, c)), AA(sk, cls1, cls2, m, 1n+c), hc, ih(hkb2, hps2))

# both Honests from c on, with the same kept list and solved equations
# before c: the same kind and drops at every constraint from c
def mw(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, n: Nat, +c: Nat, H1: SV.Honest.go(sk, cls1, n, c), H2: SV.Honest.go(sk, cls2, n, c),
  +hkb: {SV.kept_before(sk, SV.reds(cls1), c) == SV.kept_before(sk, SV.reds(cls2), c) : List<&2, Nat>}, +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, SV.reds(cls2), SV.dropped(cls2), c) : List<&2, E.QExpr>}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool})
  -> {AA(sk, cls1, cls2, n, c) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++m:
      (f1, r1) = H1
      (f2, r2) = H2
      +hc = fate_ag(sk, cls1, cls2, c, hkb, hps, hf1, hf2, f1, f2)
      mw.c(sk, cls1, cls2, m, c, hf1, hf2, hc, mw.next(sk, cls1, cls2, c, hkb, hps, hf1, hf2, hc), k2 => p2 => mw(sk, cls1, cls2, m, 1n+c, r1, r2, k2, p2, hf1, hf2))

# the fact at constraint i from c0
def aa_at(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, n: Nat, +c0: Nat, i: Nat, +h: {AA(sk, cls1, cls2, n, c0) == True{} : Bool}, hi: {KA.natle(1n+i, n) == True{} : Bool})
  -> {GR(sk, Nat.add(i, c0), SV.class_at(cls1, Nat.add(i, c0)), SV.class_at(cls2, Nat.add(i, c0))) == True{} : Bool}:
  match n i:
    case 0n i:
      absurd({GR(sk, Nat.add(i, c0), SV.class_at(cls1, Nat.add(i, c0)), SV.class_at(cls2, Nat.add(i, c0))) == True{} : Bool}, KA.ft(hi))
    case 1n++m 0n:
      L.band_l(GR(sk, c0, SV.class_at(cls1, c0), SV.class_at(cls2, c0)), AA(sk, cls1, cls2, m, 1n+c0), h)
    case 1n++m 1n++q:
      (%Equal.sym(Nat, 1n+Nat.add(q, c0), Nat.add(q, 1n+c0), LN.add_succ(q, c0)) : {GR(sk, _, SV.class_at(cls1, _), SV.class_at(cls2, _)) == True{} : Bool}
        aa_at(sk, cls1, cls2, m, 1n+c0, q, L.band_r(GR(sk, c0, SV.class_at(cls1, c0), SV.class_at(cls2, c0)), AA(sk, cls1, cls2, m, 1n+c0), h), hi))


# the fact at constraint i
def aa_i(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +i: Nat, +h: {AA(sk, cls1, cls2, SV.ncons(sk), 0n) == True{} : Bool}, +hi: {SV.lt(i, SV.ncons(sk)) == True{} : Bool})
  -> {GR(sk, i, SV.class_at(cls1, i), SV.class_at(cls2, i)) == True{} : Bool}:
  (%Equal.sym(Nat, i, Nat.add(i, 0n), LN.add_zero(i)) : {GR(sk, _, SV.class_at(cls1, _), SV.class_at(cls2, _)) == True{} : Bool}
    aa_at(sk, cls1, cls2, SV.ncons(sk), 0n, i, h, (%L.lt_sv(i, SV.ncons(sk)) : {_ == True{} : Bool}
      hi)))

# The law
# -------

def ca_past(cls: List<&2, SV.Class>, c: Nat, h: {SV.lt(c, SV.clsn(cls)) == False{} : Bool}) -> {SV.class_at(cls, c) == SV.Kept{Nil{}} : SV.Class}:
  match cls c:
    case Nil{} c:
      {==}
    case Con{y, t} 0n:
      absurd({y == SV.Kept{Nil{}} : SV.Class}, KA.tf(h))
    case Con{y, t} 1n+m:
      ca_past(t, m, h)

def ca_past_n(+sk: SK.Sketch, +cls: List<&2, SV.Class>, +c: Nat, +hn: {SV.clsn(cls) == SV.ncons(sk) : Nat}, +h: {SV.lt(c, SV.ncons(sk)) == False{} : Bool}) -> {SV.class_at(cls, c) == SV.Kept{Nil{}} : SV.Class}:
  ca_past(cls, c, (%Equal.sym(Nat, SV.clsn(cls), SV.ncons(sk), hn) : {SV.lt(c, _) == False{} : Bool}
    h))

def hu_k(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, b: Bool, +e: {SV.lt(c, SV.ncons(sk)) == b : Bool}, +hn1: {SV.clsn(cls1) == SV.ncons(sk) : Nat}, +hn2: {SV.clsn(cls2) == SV.ncons(sk) : Nat},
  +hA: {AA(sk, cls1, cls2, SV.ncons(sk), 0n) == True{} : Bool}) -> {SV.kind(SV.class_at(cls1, c)) == SV.kind(SV.class_at(cls2, c)) : Nat}:
  match b:
    case True{}:
      L.eq_ok(SV.kind(SV.class_at(cls1, c)), SV.kind(SV.class_at(cls2, c)), L.band_l(SV.eq(SV.kind(SV.class_at(cls1, c)), SV.kind(SV.class_at(cls2, c))), SP.agree(SV.owners(sk), SV.kdrops(SV.class_at(cls1, c)), SV.kdrops(SV.class_at(cls2, c)), c, 0n), aa_i(sk, cls1, cls2, c, hA, e)))
    case False{}:
      %Equal.sym(SV.Class, SV.class_at(cls1, c), SV.Kept{Nil{}}, ca_past_n(sk, cls1, c, hn1, e)) : {SV.kind(_) == SV.kind(SV.class_at(cls2, c)) : Nat}
      %Equal.sym(SV.Class, SV.class_at(cls2, c), SV.Kept{Nil{}}, ca_past_n(sk, cls2, c, hn2, e)) : {SV.kind(SV.Kept{Nil{}}) == SV.kind(_) : Nat}
      {==}

def nth_below(xs: List<&2, Nat>, j: Nat, +n: Nat, +hb: {SV.below(xs, n) == True{} : Bool}, hj: {SV.lt(j, SV.len(xs)) == True{} : Bool}) -> {SV.lt(SV.nth(xs, j), n) == True{} : Bool}:
  match xs j:
    case Nil{} j:
      absurd({SV.lt(SV.nth(Nil{}, j), n) == True{} : Bool}, KA.ft(KB.lt_zero(j, hj)))
    case Con{+x, +t} 0n:
      L.band_l(SV.lt(x, n), SV.below(t, n), hb)
    case Con{+x, +t} 1n+q:
      nth_below(t, q, n, L.band_r(SV.lt(x, n), SV.below(t, n), hb), hj)


# at j's owner the two drops agree, at j
def hu_jo(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +j: Nat, +hag: {SP.agree(SV.owners(sk), SV.kdrops(SV.class_at(cls1, SV.nth(SV.owners(sk), j))), SV.kdrops(SV.class_at(cls2, SV.nth(SV.owners(sk), j))), SV.nth(SV.owners(sk), j), 0n) == True{} : Bool}, +hjo: {SV.lt(j, SV.len(SV.owners(sk))) == True{} : Bool})
  -> {SV.mem(j, SV.kdrops(SV.class_at(cls1, SV.nth(SV.owners(sk), j)))) == SV.mem(j, SV.kdrops(SV.class_at(cls2, SV.nth(SV.owners(sk), j)))) : Bool}:
  AG.ag_hd(SV.nth(SV.owners(sk), j), SV.nth(SV.owners(sk), j), j, SV.kdrops(SV.class_at(cls1, SV.nth(SV.owners(sk), j))), SV.kdrops(SV.class_at(cls2, SV.nth(SV.owners(sk), j))), (%Equal.sym(Nat, j, Nat.add(j, 0n), LN.add_zero(j)) : {SV.bor(SV.bnot(SV.eq(SV.nth(SV.owners(sk), j), SV.nth(SV.owners(sk), j))), SP.beq(SV.mem(_, SV.kdrops(SV.class_at(cls1, SV.nth(SV.owners(sk), j)))), SV.mem(_, SV.kdrops(SV.class_at(cls2, SV.nth(SV.owners(sk), j)))))) == True{} : Bool}
    OV.ag_at(SV.owners(sk), SV.kdrops(SV.class_at(cls1, SV.nth(SV.owners(sk), j))), SV.kdrops(SV.class_at(cls2, SV.nth(SV.owners(sk), j))), SV.nth(SV.owners(sk), j), 0n, j, hag, hjo)), L.eq_refl(SV.nth(SV.owners(sk), j)))

def hu_d(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +j: Nat, b: Bool, +e: {SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))) == b : Bool}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool},
  +hA: {AA(sk, cls1, cls2, SV.ncons(sk), 0n) == True{} : Bool}) -> {SV.mem(j, SV.dropped(cls1)) == SV.mem(j, SV.dropped(cls2)) : Bool}:
  match b:
    case True{}:
      +hjo = OV.oa_jo(sk, j, e)
      +hag = L.band_r(SV.eq(SV.kind(SV.class_at(cls1, SV.nth(SV.owners(sk), j))), SV.kind(SV.class_at(cls2, SV.nth(SV.owners(sk), j)))), SP.agree(SV.owners(sk), SV.kdrops(SV.class_at(cls1, SV.nth(SV.owners(sk), j))), SV.kdrops(SV.class_at(cls2, SV.nth(SV.owners(sk), j))), SV.nth(SV.owners(sk), j), 0n), aa_i(sk, cls1, cls2, SV.nth(SV.owners(sk), j), hA, nth_below(SV.owners(sk), j, SV.ncons(sk), OW.below_ncons(sk), hjo)))
      Equal.trans(Bool, SV.mem(j, SV.dropped(cls1)), SV.mem(j, SV.kdrops(SV.class_at(cls1, SV.nth(SV.owners(sk), j)))), SV.mem(j, SV.dropped(cls2)), HR.mem_dropped(sk, cls1, j, hf1),
        Equal.trans(Bool, SV.mem(j, SV.kdrops(SV.class_at(cls1, SV.nth(SV.owners(sk), j)))), SV.mem(j, SV.kdrops(SV.class_at(cls2, SV.nth(SV.owners(sk), j)))), SV.mem(j, SV.dropped(cls2)), hu_jo(sk, cls1, cls2, j, hag, hjo), Equal.sym(Bool, SV.mem(j, SV.dropped(cls2)), SV.mem(j, SV.kdrops(SV.class_at(cls2, SV.nth(SV.owners(sk), j)))), HR.mem_dropped(sk, cls2, j, hf2))))
    case False{}:
      Equal.trans(Bool, SV.mem(j, SV.dropped(cls1)), False{}, SV.mem(j, SV.dropped(cls2)), HR.nd_past(sk, cls1, j, hf1, e), Equal.sym(Bool, SV.mem(j, SV.dropped(cls2)), False{}, HR.nd_past(sk, cls2, j, hf2, e)))

def hu_go(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +j: Nat, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hf2: {HR.hfacts(sk, cls2) == True{} : Bool}, q1: SV.Honest(sk, cls1), q2: SV.Honest(sk, cls2))
  -> M.Both({SV.kind(SV.class_at(cls1, c)) == SV.kind(SV.class_at(cls2, c)) : Nat}, {SV.mem(j, SV.dropped(cls1)) == SV.mem(j, SV.dropped(cls2)) : Bool}):
  (+hn1, g1) = q1
  (+hn2, g2) = q2
  +hA = mw(sk, cls1, cls2, SV.ncons(sk), 0n, g1, g2, AG.kb_zero(sk, SV.reds(cls1), SV.reds(cls2)), AG.ps_zero(sk, SV.reds(cls1), SV.dropped(cls1), SV.reds(cls2), SV.dropped(cls2)), hf1, hf2)
  (hu_k(sk, cls1, cls2, c, SV.lt(c, SV.ncons(sk)), {==}, hn1, hn2, hA), hu_d(sk, cls1, cls2, j, SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))), {==}, hf1, hf2, hA))

def hu_cmb(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +cls2: List<&2, SV.Class>, +c: Nat, +j: Nat, p1: ({HR.hfacts(sk, cls1) == True{} : Bool} & SV.Honest(sk, cls1)), p2: ({HR.hfacts(sk, cls2) == True{} : Bool} & SV.Honest(sk, cls2)))
  -> M.Both({SV.kind(SV.class_at(cls1, c)) == SV.kind(SV.class_at(cls2, c)) : Nat}, {SV.mem(j, SV.dropped(cls1)) == SV.mem(j, SV.dropped(cls2)) : Bool}):
  (+hf1, q1) = p1
  (+hf2, q2) = p2
  hu_go(sk, cls1, cls2, c, j, hf1, hf2, q1, q2)

# LAW 5 (ROADMAP honest_unique): honest classifications agree. Every
# constraint gets the same kind, and every equation is dropped in both or
# in neither
def honest_unique(+sk: SK.Sketch, w: SK.Sketch.wf(sk), +c1: List<&2, SV.Class>, h1: SV.Honest(sk, c1), +c2: List<&2, SV.Class>, h2: SV.Honest(sk, c2), +c: Nat, +j: Nat)
  -> M.Both({SV.kind(SV.class_at(c1, c)) == SV.kind(SV.class_at(c2, c)) : Nat}, {SV.mem(j, SV.dropped(c1)) == SV.mem(j, SV.dropped(c2)) : Bool}):
  hu_cmb(sk, c1, c2, c, j, HR.hon_rb(sk, c1, h1), HR.hon_rb(sk, c2, h2))
