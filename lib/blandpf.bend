# bend-cad: Bland's rule (PLAN-sk13a S3): along the run, no basis comes
# back. Suppose the bases at steps a and a + L (L >= 1) are equal, every
# step between pivoting. Let t be the largest variable entering in
# between: it enters at some step k1 and, since the bases agree, leaves at
# some step k2. Let i (< t) be the variable leaving at k1, and Delta the
# difference of the two steps' values (at k2 less at k1), a point of the
# system. Read row i of k1's dictionary at Delta:
# - Delta_i > 0 (i is below its bound at k1 and, being smaller than t, not
#   at k2);
# - but the row's sum is < 0: its basic entries are 0; a variable that
#   never enters keeps its status, so its Delta is 0; a smaller fickle
#   variable has a nonpositive entry and its Delta is >= 0; and t's entry
#   is positive with Delta_t < 0.
# Values are a + b delta, compared lexicographically (lib/lexpf.bend).
#
# Generated from tools/drafts/blandpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./qemb.bend as QE
import ./karith.bend as KA
import ./nat.bend as LN
import ./zring.bend as R
import ./elim.bend as EL
import ./simplex.bend as SX
import ./simppf.bend as SP
import ./lexpf.bend as LX
import ./runpf.bend as RN

def absurd(-A: Type, x: Empty) -> A:
  match x:

def bnot(b: Bool) -> Bool:
  match b:
    case True{}:
      False{}
    case False{}:
      True{}

# p + c, counting c down (c first, for termination)
def plus(c: Nat, p: Nat) -> Nat:
  match c:
    case 0n:
      p
    case 1n+k:
      plus(k, 1n+p)

# Steps and statuses
# ------------------

def I(+lp: SX.LP, +q: Nat) -> Nat:
  RN.lv(lp, RN.tab(lp, q))

def En(+lp: SX.LP, +q: Nat) -> Nat:
  RN.en(lp, RN.tab(lp, q))

def B(+lp: SX.LP, +q: Nat) -> List<&2, Bool>:
  SX.Tab.bas(RN.tab(lp, q))

# x is basic at step q
def St(+lp: SX.LP, +x: Nat, +q: Nat) -> Bool:
  SP.bat(B(lp, q), x)

def go_prev(+lp: SX.LP, +n: Nat, h: {RN.isgo(RN.st(lp, 1n+n)) == True{} : Bool}) -> {RN.isgo(RN.st(lp, n)) == True{} : Bool}:
  RN.go_back(lp, RN.st(lp, n), (%RN.st_succ(lp, n) : {RN.isgo(_) == True{} : Bool}
    h))

# the run is still going at an earlier step
def go_down(+lp: SX.LP, c: Nat, d: Nat, +p: Nat, hd: {KA.natle(d, c) == True{} : Bool}, h: {RN.isgo(RN.st(lp, plus(c, p))) == True{} : Bool}) -> {RN.isgo(RN.st(lp, plus(d, p))) == True{} : Bool}:
  match c d:
    case 0n 0n:
      h
    case 0n 1n+j:
      absurd({RN.isgo(RN.st(lp, plus(1n+j, p))) == True{} : Bool}, KA.ft(hd))
    case 1n+k 0n:
      go_prev(lp, p, go_down(lp, k, 0n, 1n+p, {==}, h))
    case 1n+k 1n+j:
      go_down(lp, k, j, 1n+p, hd, h)

# a pivot at step q: the basis after it
def bas_next(+lp: SX.LP, +q: Nat, h: {RN.isgo(RN.st(lp, 1n+q)) == True{} : Bool}) -> {B(lp, 1n+q) == SX.setb(SX.setb(B(lp, q), I(lp, q), False{}), En(lp, q), True{}) : List<&2, Bool>}:
  %Equal.sym(SX.Tab, RN.tab(lp, 1n+q), SX.pivot(SX.LP.nv(lp), RN.tab(lp, q), I(lp, q), En(lp, q)), RN.tab_piv(lp, q, h)) : {SX.Tab.bas(_) == SX.setb(SX.setb(B(lp, q), I(lp, q), False{}), En(lp, q), True{}) : List<&2, Bool>}
  Equal.sym(List<&2, Bool>, SX.setb(SX.setb(B(lp, q), I(lp, q), False{}), En(lp, q), True{}), SX.Tab.bas(SX.pivot(SX.LP.nv(lp), RN.tab(lp, q), I(lp, q), En(lp, q))), SP.bas_pivot(SX.LP.nv(lp), RN.tab(lp, q), I(lp, q), En(lp, q)))

# setting an entry False makes nothing True
def bat_false_down(bs: List<&2, Bool>, j: Nat, k: Nat, h: {SP.bat(SX.setb(bs, j, False{}), k) == True{} : Bool}) -> {SP.bat(bs, k) == True{} : Bool}:
  match bs j k:
    case Nil{} j k:
      h
    case Con{x, t} 0n 0n:
      absurd({SP.bat(Con{x, t}, 0n) == True{} : Bool}, KA.ft(h))
    case Con{x, t} 0n 1n+m:
      h
    case Con{x, t} 1n+i 0n:
      h
    case Con{x, t} 1n+i 1n+m:
      bat_false_down(t, i, m, h)

# setting an entry True keeps every True
def bat_true_up(bs: List<&2, Bool>, j: Nat, k: Nat, h: {SP.bat(bs, k) == True{} : Bool}) -> {SP.bat(SX.setb(bs, j, True{}), k) == True{} : Bool}:
  match bs j k:
    case Nil{} j k:
      h
    case Con{x, t} 0n 0n:
      {==}
    case Con{x, t} 0n 1n+m:
      h
    case Con{x, t} 1n+i 0n:
      h
    case Con{x, t} 1n+i 1n+m:
      bat_true_up(t, i, m, h)

# basic after a pivot it did not enter at: basic before
def down_noE(+lp: SX.LP, +x: Nat, +q: Nat, h: {RN.isgo(RN.st(lp, 1n+q)) == True{} : Bool}, hxe: {SX.eqn(x, En(lp, q)) == False{} : Bool}, hs: {St(lp, x, 1n+q) == True{} : Bool}) -> {St(lp, x, q) == True{} : Bool}:
  bat_false_down(B(lp, q), I(lp, q), x, SP.bat_unset(SX.setb(B(lp, q), I(lp, q), False{}), En(lp, q), True{}, x, hxe, (%bas_next(lp, q, h) : {SP.bat(_, x) == True{} : Bool}
    hs)))

# basic before a pivot it did not leave at: basic after
def up_noI(+lp: SX.LP, +x: Nat, +q: Nat, h: {RN.isgo(RN.st(lp, 1n+q)) == True{} : Bool}, hxi: {SX.eqn(x, I(lp, q)) == False{} : Bool}, hs: {St(lp, x, q) == True{} : Bool}) -> {St(lp, x, 1n+q) == True{} : Bool}:
  %Equal.sym(List<&2, Bool>, B(lp, 1n+q), SX.setb(SX.setb(B(lp, q), I(lp, q), False{}), En(lp, q), True{}), bas_next(lp, q, h)) : {SP.bat(_, x) == True{} : Bool}
  bat_true_up(SX.setb(B(lp, q), I(lp, q), False{}), En(lp, q), x, (%SP.bat_setb_ne(B(lp, q), I(lp, q), False{}, x, hxi) : {_ == True{} : Bool}
    hs))

def bnot_t(b: Bool, h: {bnot(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.ft(h))
    case False{}:
      {==}

# Ranges of steps: c steps from p
# -------------------------------

# x enters at none of them
def noent(+lp: SX.LP, +x: Nat, c: Nat, +p: Nat) -> Bool:
  match c:
    case 0n:
      True{}
    case 1n+k:
      KA.band(bnot(SX.eqn(x, En(lp, p))), noent(lp, x, k, 1n+p))

# x leaves at none of them
def nolev(+lp: SX.LP, +x: Nat, c: Nat, +p: Nat) -> Bool:
  match c:
    case 0n:
      True{}
    case 1n+k:
      KA.band(bnot(SX.eqn(x, I(lp, p))), nolev(lp, x, k, 1n+p))

# never entering, x can only stop being basic: basic at the end, basic at
# each step d of the range
def lemA(+lp: SX.LP, +x: Nat, c: Nat, d: Nat, +p: Nat, hd: {KA.natle(d, c) == True{} : Bool}, +hg: {RN.isgo(RN.st(lp, plus(c, p))) == True{} : Bool}, hn: {noent(lp, x, c, p) == True{} : Bool}, hs: {St(lp, x, plus(c, p)) == True{} : Bool}) -> {St(lp, x, plus(d, p)) == True{} : Bool}:
  match c d:
    case 0n 0n:
      hs
    case 0n 1n+j:
      absurd({St(lp, x, plus(1n+j, p)) == True{} : Bool}, KA.ft(hd))
    case 1n++k 0n:
      +hn2 = hn
      down_noE(lp, x, p, go_down(lp, k, 0n, 1n+p, {==}, hg), bnot_t(SX.eqn(x, En(lp, p)), KA.band_l(bnot(SX.eqn(x, En(lp, p))), noent(lp, x, k, 1n+p), hn2)),
        lemA(lp, x, k, 0n, 1n+p, {==}, hg, KA.band_r(bnot(SX.eqn(x, En(lp, p))), noent(lp, x, k, 1n+p), hn2), hs))
    case 1n++k 1n+j:
      lemA(lp, x, k, j, 1n+p, hd, hg, KA.band_r(bnot(SX.eqn(x, En(lp, p))), noent(lp, x, k, 1n+p), hn), hs)

# never leaving, x can only become basic: basic at step d, basic at the end
def lemB(+lp: SX.LP, +x: Nat, c: Nat, d: Nat, +p: Nat, hd: {KA.natle(d, c) == True{} : Bool}, +hg: {RN.isgo(RN.st(lp, plus(c, p))) == True{} : Bool}, hn: {nolev(lp, x, c, p) == True{} : Bool}, hs: {St(lp, x, plus(d, p)) == True{} : Bool}) -> {St(lp, x, plus(c, p)) == True{} : Bool}:
  match c d:
    case 0n 0n:
      hs
    case 0n 1n+j:
      absurd({St(lp, x, plus(0n, p)) == True{} : Bool}, KA.ft(hd))
    case 1n++k 0n:
      +hn2 = hn
      lemB(lp, x, k, 0n, 1n+p, {==}, hg, KA.band_r(bnot(SX.eqn(x, I(lp, p))), nolev(lp, x, k, 1n+p), hn2),
        up_noI(lp, x, p, go_down(lp, k, 0n, 1n+p, {==}, hg), bnot_t(SX.eqn(x, I(lp, p)), KA.band_l(bnot(SX.eqn(x, I(lp, p))), nolev(lp, x, k, 1n+p), hn2)), hs))
    case 1n++k 1n+j:
      lemB(lp, x, k, j, 1n+p, hd, hg, KA.band_r(bnot(SX.eqn(x, I(lp, p))), nolev(lp, x, k, 1n+p), hn), hs)

def noent_pre(+lp: SX.LP, +x: Nat, c: Nat, d: Nat, +p: Nat, hd: {KA.natle(d, c) == True{} : Bool}, h: {noent(lp, x, c, p) == True{} : Bool}) -> {noent(lp, x, d, p) == True{} : Bool}:
  match c d:
    case 0n 0n:
      h
    case 0n 1n+j:
      absurd({noent(lp, x, 1n+j, p) == True{} : Bool}, KA.ft(hd))
    case 1n+k 0n:
      {==}
    case 1n++k 1n++j:
      +h2 = h
      KA.band_i(bnot(SX.eqn(x, En(lp, p))), noent(lp, x, j, 1n+p), KA.band_l(bnot(SX.eqn(x, En(lp, p))), noent(lp, x, k, 1n+p), h2), noent_pre(lp, x, k, j, 1n+p, hd, KA.band_r(bnot(SX.eqn(x, En(lp, p))), noent(lp, x, k, 1n+p), h2)))

def nolev_pre(+lp: SX.LP, +x: Nat, c: Nat, d: Nat, +p: Nat, hd: {KA.natle(d, c) == True{} : Bool}, h: {nolev(lp, x, c, p) == True{} : Bool}) -> {nolev(lp, x, d, p) == True{} : Bool}:
  match c d:
    case 0n 0n:
      h
    case 0n 1n+j:
      absurd({nolev(lp, x, 1n+j, p) == True{} : Bool}, KA.ft(hd))
    case 1n+k 0n:
      {==}
    case 1n++k 1n++j:
      +h2 = h
      KA.band_i(bnot(SX.eqn(x, I(lp, p))), nolev(lp, x, j, 1n+p), KA.band_l(bnot(SX.eqn(x, I(lp, p))), nolev(lp, x, k, 1n+p), h2), nolev_pre(lp, x, k, j, 1n+p, hd, KA.band_r(bnot(SX.eqn(x, I(lp, p))), nolev(lp, x, k, 1n+p), h2)))

# Where x enters, or leaves
# -------------------------

def fe.go(b: Bool, +lp: SX.LP, +x: Nat, +k: Nat, +p: Nat, rest: Nat) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      1n+rest

# the offset of the first step of the range where x enters
def fe(+lp: SX.LP, +x: Nat, c: Nat, +p: Nat) -> Nat:
  match c:
    case 0n:
      0n
    case 1n++k:
      fe.go(SX.eqn(x, En(lp, p)), lp, x, k, p, fe(lp, x, k, 1n+p))

def fe_ok.go(b: Bool, +lp: SX.LP, +x: Nat, +k: Nat, +p: Nat, hb: {b == SX.eqn(x, En(lp, p)) : Bool}, h: {KA.band(bnot(b), noent(lp, x, k, 1n+p)) == False{} : Bool}, ih: {noent(lp, x, k, 1n+p) == False{} : Bool} -> M.Both({SX.eqn(x, En(lp, plus(fe(lp, x, k, 1n+p), 1n+p))) == True{} : Bool}, {SX.ltn(fe(lp, x, k, 1n+p), k) == True{} : Bool})) -> M.Both({SX.eqn(x, En(lp, plus(fe.go(b, lp, x, k, p, fe(lp, x, k, 1n+p)), p))) == True{} : Bool}, {SX.ltn(fe.go(b, lp, x, k, p, fe(lp, x, k, 1n+p)), 1n+k) == True{} : Bool}):
  match b:
    case True{}:
      (Equal.sym(Bool, True{}, SX.eqn(x, En(lp, p)), hb), {==})
    case False{}:
      ih(h)

# x enters somewhere in the range: at offset fe, below c
def fe_ok(+lp: SX.LP, +x: Nat, c: Nat, +p: Nat, h: {noent(lp, x, c, p) == False{} : Bool}) -> M.Both({SX.eqn(x, En(lp, plus(fe(lp, x, c, p), p))) == True{} : Bool}, {SX.ltn(fe(lp, x, c, p), c) == True{} : Bool}):
  match c:
    case 0n:
      absurd(M.Both({SX.eqn(x, En(lp, plus(fe(lp, x, 0n, p), p))) == True{} : Bool}, {SX.ltn(fe(lp, x, 0n, p), 0n) == True{} : Bool}), KA.tf(h))
    case 1n++k:
      fe_ok.go(SX.eqn(x, En(lp, p)), lp, x, k, p, {==}, h, hh => fe_ok(lp, x, k, 1n+p, hh))

def fl(+lp: SX.LP, +x: Nat, c: Nat, +p: Nat) -> Nat:
  match c:
    case 0n:
      0n
    case 1n++k:
      fe.go(SX.eqn(x, I(lp, p)), lp, x, k, p, fl(lp, x, k, 1n+p))

def fl_ok.go(b: Bool, +lp: SX.LP, +x: Nat, +k: Nat, +p: Nat, hb: {b == SX.eqn(x, I(lp, p)) : Bool}, h: {KA.band(bnot(b), nolev(lp, x, k, 1n+p)) == False{} : Bool}, ih: {nolev(lp, x, k, 1n+p) == False{} : Bool} -> M.Both({SX.eqn(x, I(lp, plus(fl(lp, x, k, 1n+p), 1n+p))) == True{} : Bool}, {SX.ltn(fl(lp, x, k, 1n+p), k) == True{} : Bool})) -> M.Both({SX.eqn(x, I(lp, plus(fe.go(b, lp, x, k, p, fl(lp, x, k, 1n+p)), p))) == True{} : Bool}, {SX.ltn(fe.go(b, lp, x, k, p, fl(lp, x, k, 1n+p)), 1n+k) == True{} : Bool}):
  match b:
    case True{}:
      (Equal.sym(Bool, True{}, SX.eqn(x, I(lp, p)), hb), {==})
    case False{}:
      ih(h)

# x leaves somewhere in the range: at offset fl, below c
def fl_ok(+lp: SX.LP, +x: Nat, c: Nat, +p: Nat, h: {nolev(lp, x, c, p) == False{} : Bool}) -> M.Both({SX.eqn(x, I(lp, plus(fl(lp, x, c, p), p))) == True{} : Bool}, {SX.ltn(fl(lp, x, c, p), c) == True{} : Bool}):
  match c:
    case 0n:
      absurd(M.Both({SX.eqn(x, I(lp, plus(fl(lp, x, 0n, p), p))) == True{} : Bool}, {SX.ltn(fl(lp, x, 0n, p), 0n) == True{} : Bool}), KA.tf(h))
    case 1n++k:
      fl_ok.go(SX.eqn(x, I(lp, p)), lp, x, k, p, {==}, h, hh => fl_ok(lp, x, k, 1n+p, hh))

# The largest entering variable
# -----------------------------

def nmax.go(b: Bool, a: Nat, m: Nat) -> Nat:
  match b:
    case True{}:
      m
    case False{}:
      a

def nmax(+a: Nat, +m: Nat) -> Nat:
  nmax.go(KA.natle(a, m), a, m)

# the largest variable entering in the c + 1 steps from p
def maxE(+lp: SX.LP, c: Nat, +p: Nat) -> Nat:
  match c:
    case 0n:
      En(lp, p)
    case 1n+k:
      nmax(En(lp, p), maxE(lp, k, 1n+p))

def le_nmax.go(b: Bool, +a: Nat, +m: Nat, hb: {b == KA.natle(a, m) : Bool}) -> M.Both({KA.natle(a, nmax.go(b, a, m)) == True{} : Bool}, {KA.natle(m, nmax.go(b, a, m)) == True{} : Bool}):
  match b:
    case True{}:
      (Equal.sym(Bool, True{}, KA.natle(a, m), hb), KA.natle_refl(m))
    case False{}:
      (KA.natle_refl(a), KA.natle_flip(a, m, Equal.sym(Bool, False{}, KA.natle(a, m), hb)))

def le_nmax(+a: Nat, +m: Nat) -> M.Both({KA.natle(a, nmax(a, m)) == True{} : Bool}, {KA.natle(m, nmax(a, m)) == True{} : Bool}):
  le_nmax.go(KA.natle(a, m), a, m, {==})

def both_l(-A: Data, -B: Data, h: M.Both(A, B)) -> A:
  (a, b) = h
  a

def both_r(-A: Data, -B: Data, h: M.Both(A, B)) -> B:
  (a, b) = h
  b

# every variable entering in the range is at most maxE
def le_maxE(+lp: SX.LP, c: Nat, d: Nat, +p: Nat, hd: {KA.natle(d, c) == True{} : Bool}) -> {KA.natle(En(lp, plus(d, p)), maxE(lp, c, p)) == True{} : Bool}:
  match c d:
    case 0n 0n:
      KA.natle_refl(En(lp, p))
    case 0n 1n++j:
      absurd({KA.natle(En(lp, plus(1n+j, p)), maxE(lp, 0n, p)) == True{} : Bool}, KA.ft(hd))
    case 1n++k 0n:
      both_l({KA.natle(En(lp, p), nmax(En(lp, p), maxE(lp, k, 1n+p))) == True{} : Bool}, {KA.natle(maxE(lp, k, 1n+p), nmax(En(lp, p), maxE(lp, k, 1n+p))) == True{} : Bool}, le_nmax(En(lp, p), maxE(lp, k, 1n+p)))
    case 1n++k 1n++j:
      KA.natle_trans(En(lp, plus(j, 1n+p)), maxE(lp, k, 1n+p), nmax(En(lp, p), maxE(lp, k, 1n+p)), le_maxE(lp, k, j, 1n+p, hd), both_r({KA.natle(En(lp, p), nmax(En(lp, p), maxE(lp, k, 1n+p))) == True{} : Bool}, {KA.natle(maxE(lp, k, 1n+p), nmax(En(lp, p), maxE(lp, k, 1n+p))) == True{} : Bool}, le_nmax(En(lp, p), maxE(lp, k, 1n+p))))

def argE.go(b: Bool, rest: Nat) -> Nat:
  match b:
    case True{}:
      1n+rest
    case False{}:
      0n

# where the largest is entering (its offset)
def argE(+lp: SX.LP, c: Nat, +p: Nat) -> Nat:
  match c:
    case 0n:
      0n
    case 1n++k:
      argE.go(KA.natle(En(lp, p), maxE(lp, k, 1n+p)), argE(lp, k, 1n+p))

def argE_ok.go(b: Bool, +lp: SX.LP, +k: Nat, +p: Nat, hb: {b == KA.natle(En(lp, p), maxE(lp, k, 1n+p)) : Bool}, ih: M.Both({En(lp, plus(argE(lp, k, 1n+p), 1n+p)) == maxE(lp, k, 1n+p) : Nat}, {KA.natle(argE(lp, k, 1n+p), k) == True{} : Bool})) -> M.Both({En(lp, plus(argE.go(b, argE(lp, k, 1n+p)), p)) == nmax.go(b, En(lp, p), maxE(lp, k, 1n+p)) : Nat}, {KA.natle(argE.go(b, argE(lp, k, 1n+p)), 1n+k) == True{} : Bool}):
  match b:
    case True{}:
      ih
    case False{}:
      ({==}, {==})

def argE_ok(+lp: SX.LP, c: Nat, +p: Nat) -> M.Both({En(lp, plus(argE(lp, c, p), p)) == maxE(lp, c, p) : Nat}, {KA.natle(argE(lp, c, p), c) == True{} : Bool}):
  match c:
    case 0n:
      ({==}, {==})
    case 1n++k:
      argE_ok.go(KA.natle(En(lp, p), maxE(lp, k, 1n+p)), lp, k, p, {==}, argE_ok(lp, k, 1n+p))

def plus_succ(d: Nat, +p: Nat) -> {plus(d, 1n+p) == 1n+plus(d, p) : Nat}:
  match d:
    case 0n:
      {==}
    case 1n+k:
      plus_succ(k, 1n+p)

# Entering and leaving change the status
# --------------------------------------

def ent_nb.c(~F: O.OField, +lp: SX.LP, +q: Nat, +hgo: {RN.isgo(SX.step(lp, RN.tab(lp, q))) == True{} : Bool}, +hwf: {SP.lpwf(lp) == True{} : Bool}, h: {St(lp, En(lp, q), q) == True{} : Bool}) -> Empty:
  RN.help_zero(SX.at(RN.rowi(lp, RN.tab(lp, q)), En(lp, q)), Nat.is_le(SX.LP.m(lp), En(lp, q)),
    SP.zcol_at(SX.Tab.rows(RN.tab(lp, q)), En(lp, q), I(lp, q), RN.iz_at(~F, lp, q, hwf)(En(lp, q), h)),
    RN.en_help(lp, RN.tab(lp, q), hgo))

def ent_nb.go(~F: O.OField, b: Bool, +lp: SX.LP, +q: Nat, hb: {b == St(lp, En(lp, q), q) : Bool}, +hgo: {RN.isgo(SX.step(lp, RN.tab(lp, q))) == True{} : Bool}, +hwf: {SP.lpwf(lp) == True{} : Bool}) -> {St(lp, En(lp, q), q) == False{} : Bool}:
  match b:
    case False{}:
      Equal.sym(Bool, False{}, St(lp, En(lp, q), q), hb)
    case True{}:
      absurd({St(lp, En(lp, q), q) == False{} : Bool}, ent_nb.c(~F, lp, q, hgo, hwf, Equal.sym(Bool, True{}, St(lp, En(lp, q), q), hb)))

# the entering variable was nonbasic
def ent_nb(~F: O.OField, +lp: SX.LP, +q: Nat, +hgo: {RN.isgo(SX.step(lp, RN.tab(lp, q))) == True{} : Bool}, +hwf: {SP.lpwf(lp) == True{} : Bool}) -> {St(lp, En(lp, q), q) == False{} : Bool}:
  ent_nb.go(~F, St(lp, En(lp, q), q), lp, q, {==}, hgo, hwf)

# and is basic after the pivot
def after_E(+lp: SX.LP, +q: Nat, +h: {RN.isgo(RN.st(lp, 1n+q)) == True{} : Bool}, +hwf: {SP.lpwf(lp) == True{} : Bool}) -> {St(lp, En(lp, q), 1n+q) == True{} : Bool}:
  %Equal.sym(List<&2, Bool>, B(lp, 1n+q), SX.setb(SX.setb(B(lp, q), I(lp, q), False{}), En(lp, q), True{}), bas_next(lp, q, h)) : {SP.bat(_, En(lp, q)) == True{} : Bool}
  SP.bat_setb_eq(SX.setb(B(lp, q), I(lp, q), False{}), En(lp, q), True{}, (%SP.blen_setb(B(lp, q), I(lp, q), False{}) : {SX.ltn(En(lp, q), _) == True{} : Bool}
    RN.he_at(lp, q, RN.piv_step(lp, q, h), hwf)))

def eqn_sym(a: Nat, b: Nat) -> {SX.eqn(a, b) == SX.eqn(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      {==}
    case 1n+i 1n+j:
      eqn_sym(i, j)

# the leaving variable is not the entering one
def ie_ne(~F: O.OField, +lp: SX.LP, +q: Nat, +hgo: {RN.isgo(SX.step(lp, RN.tab(lp, q))) == True{} : Bool}, +hwf: {SP.lpwf(lp) == True{} : Bool}) -> {SX.eqn(I(lp, q), En(lp, q)) == False{} : Bool}:
  %eqn_sym(En(lp, q), I(lp, q)) : {_ == False{} : Bool}
  RN.ei_ne(~F, lp, q, hgo, hwf, RN.iz_at(~F, lp, q, hwf))

# the leaving variable is nonbasic after the pivot
def after_I(~F: O.OField, +lp: SX.LP, +q: Nat, +h: {RN.isgo(RN.st(lp, 1n+q)) == True{} : Bool}, +hwf: {SP.lpwf(lp) == True{} : Bool}) -> {St(lp, I(lp, q), 1n+q) == False{} : Bool}:
  %Equal.sym(List<&2, Bool>, B(lp, 1n+q), SX.setb(SX.setb(B(lp, q), I(lp, q), False{}), En(lp, q), True{}), bas_next(lp, q, h)) : {SP.bat(_, I(lp, q)) == False{} : Bool}
  %SP.bat_setb_ne(SX.setb(B(lp, q), I(lp, q), False{}), En(lp, q), True{}, I(lp, q), ie_ne(~F, lp, q, RN.piv_step(lp, q, h), hwf)) : {_ == False{} : Bool}
  SP.bat_setb_eq(B(lp, q), I(lp, q), False{}, RN.hil_at(lp, q, RN.piv_step(lp, q, h)))

# The cycle
# ---------
# The setting: steps a .. a + L + 1 all pivot, and the bases at a and at
# a + L + 1 are equal.


def bool_eq(x: Bool, y: Bool, f: {x == True{} : Bool} -> {y == True{} : Bool}, g: {y == True{} : Bool} -> {x == True{} : Bool}) -> {x == y : Bool}:
  match x y:
    case True{} True{}:
      {==}
    case True{} False{}:
      absurd({True{} == False{} : Bool}, KA.ft(f({==})))
    case False{} True{}:
      absurd({False{} == True{} : Bool}, KA.ft(g({==})))
    case False{} False{}:
      {==}

# the statuses at the two ends agree
def ends(+lp: SX.LP, +L: Nat, +a: Nat, +x: Nat, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> {St(lp, x, a) == St(lp, x, plus(1n+L, a)) : Bool}:
  Equal.cong(List<&2, Bool>, Bool, bs => SP.bat(bs, x), B(lp, a), B(lp, plus(1n+L, a)), heq)

def hd1(+lp: SX.LP, +L: Nat, +a: Nat) -> {KA.natle(argE(lp, L, a), L) == True{} : Bool}:
  both_r({En(lp, plus(argE(lp, L, a), a)) == maxE(lp, L, a) : Nat}, {KA.natle(argE(lp, L, a), L) == True{} : Bool}, argE_ok(lp, L, a))

def ek1(+lp: SX.LP, +L: Nat, +a: Nat) -> {En(lp, plus(argE(lp, L, a), a)) == maxE(lp, L, a) : Nat}:
  both_l({En(lp, plus(argE(lp, L, a), a)) == maxE(lp, L, a) : Nat}, {KA.natle(argE(lp, L, a), L) == True{} : Bool}, argE_ok(lp, L, a))

# the run goes on past step a + d, for d <= L
def go_at(+lp: SX.LP, +L: Nat, +a: Nat, +d: Nat, hd: {KA.natle(d, L) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}) -> {RN.isgo(RN.st(lp, 1n+plus(d, a))) == True{} : Bool}:
  %plus_succ(d, a) : {RN.isgo(RN.st(lp, _)) == True{} : Bool}
  go_down(lp, 1n+L, 1n+d, a, hd, hG)

def go_at0(+lp: SX.LP, +L: Nat, +a: Nat, +d: Nat, hd: {KA.natle(d, L) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}) -> {RN.isgo(RN.st(lp, plus(d, a))) == True{} : Bool}:
  go_prev(lp, plus(d, a), go_at(lp, L, a, d, hd, hG))

def le_succ(+d: Nat, +L: Nat, h: {KA.natle(d, L) == True{} : Bool}) -> {KA.natle(d, 1n+L) == True{} : Bool}:
  KA.natle_succ(d, L, h)

# t is nonbasic where it enters, basic just after
def t_nb(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> {St(lp, maxE(lp, L, a), plus(argE(lp, L, a), a)) == False{} : Bool}:
  %ek1(lp, L, a) : {St(lp, _, plus(argE(lp, L, a), a)) == False{} : Bool}
  ent_nb(~F, lp, plus(argE(lp, L, a), a), RN.piv_step(lp, plus(argE(lp, L, a), a), go_at(lp, L, a, argE(lp, L, a), hd1(lp, L, a), hG)), hwf)

def t_b(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> {St(lp, maxE(lp, L, a), plus(1n+argE(lp, L, a), a)) == True{} : Bool}:
  %ek1(lp, L, a) : {St(lp, _, plus(1n+argE(lp, L, a), a)) == True{} : Bool}
  %Equal.sym(Nat, plus(argE(lp, L, a), 1n+a), 1n+plus(argE(lp, L, a), a), plus_succ(argE(lp, L, a), a)) : {St(lp, En(lp, plus(argE(lp, L, a), a)), _) == True{} : Bool}
  after_E(lp, plus(argE(lp, L, a), a), go_at(lp, L, a, argE(lp, L, a), hd1(lp, L, a), hG), hwf)

def tl.start(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, b: Bool, hb: {b == St(lp, maxE(lp, L, a), a) : Bool}, +hn: {nolev(lp, maxE(lp, L, a), 1n+L, a) == True{} : Bool}) -> {St(lp, maxE(lp, L, a), a) == False{} : Bool}:
  match b:
    case False{}:
      Equal.sym(Bool, False{}, St(lp, maxE(lp, L, a), a), hb)
    case True{}:
      absurd({St(lp, maxE(lp, L, a), a) == False{} : Bool}, KA.tf(Equal.trans(Bool, True{}, St(lp, maxE(lp, L, a), plus(argE(lp, L, a), a)), False{},
        Equal.sym(Bool, St(lp, maxE(lp, L, a), plus(argE(lp, L, a), a)), True{}, lemB(lp, maxE(lp, L, a), argE(lp, L, a), 0n, a, {==}, go_at0(lp, L, a, argE(lp, L, a), hd1(lp, L, a), hG), nolev_pre(lp, maxE(lp, L, a), 1n+L, argE(lp, L, a), a, le_succ(argE(lp, L, a), L, hd1(lp, L, a)), hn), Equal.sym(Bool, True{}, St(lp, maxE(lp, L, a), a), hb))),
        t_nb(~F, lp, L, a, hwf, hG, heq))))

def tl.c(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +hn: {nolev(lp, maxE(lp, L, a), 1n+L, a) == True{} : Bool}) -> Empty:
  KA.ft(Equal.trans(Bool, False{}, St(lp, maxE(lp, L, a), a), True{},
    Equal.sym(Bool, St(lp, maxE(lp, L, a), a), False{}, tl.start(~F, lp, L, a, hwf, hG, heq, St(lp, maxE(lp, L, a), a), {==}, hn)),
    Equal.trans(Bool, St(lp, maxE(lp, L, a), a), St(lp, maxE(lp, L, a), plus(1n+L, a)), True{}, ends(lp, L, a, maxE(lp, L, a), heq),
      lemB(lp, maxE(lp, L, a), 1n+L, 1n+argE(lp, L, a), a, hd1(lp, L, a), hG, hn, t_b(~F, lp, L, a, hwf, hG, heq)))))

def tl.go(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, b: Bool, hb: {b == nolev(lp, maxE(lp, L, a), 1n+L, a) : Bool}) -> {nolev(lp, maxE(lp, L, a), 1n+L, a) == False{} : Bool}:
  match b:
    case False{}:
      Equal.sym(Bool, False{}, nolev(lp, maxE(lp, L, a), 1n+L, a), hb)
    case True{}:
      absurd({nolev(lp, maxE(lp, L, a), 1n+L, a) == False{} : Bool}, tl.c(~F, lp, L, a, hwf, hG, heq, Equal.sym(Bool, True{}, nolev(lp, maxE(lp, L, a), 1n+L, a), hb)))

# t leaves somewhere in the range
def t_leaves(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> {nolev(lp, maxE(lp, L, a), 1n+L, a) == False{} : Bool}:
  tl.go(~F, lp, L, a, hwf, hG, heq, nolev(lp, maxE(lp, L, a), 1n+L, a), {==})


def ltn_succ_le(x: Nat, L: Nat, h: {SX.ltn(x, 1n+L) == True{} : Bool}) -> {KA.natle(x, L) == True{} : Bool}:
  match x L:
    case 0n L:
      {==}
    case 1n+i 0n:
      absurd({KA.natle(1n+i, 0n) == True{} : Bool}, KA.ft(SP.ltn0(i, h)))
    case 1n+i 1n+j:
      ltn_succ_le(i, j, h)

def lt_of_le_ne(x: Nat, y: Nat, h1: {KA.natle(x, y) == True{} : Bool}, h2: {SX.eqn(x, y) == False{} : Bool}) -> {SX.ltn(x, y) == True{} : Bool}:
  match x y:
    case 0n 0n:
      absurd({SX.ltn(0n, 0n) == True{} : Bool}, KA.tf(h2))
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      absurd({SX.ltn(1n+i, 0n) == True{} : Bool}, KA.ft(h1))
    case 1n+i 1n+j:
      lt_of_le_ne(i, j, h1, h2)

# t leaves at k2 (offset d2 <= L)
def hd2(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> {KA.natle(fl(lp, maxE(lp, L, a), 1n+L, a), L) == True{} : Bool}:
  ltn_succ_le(fl(lp, maxE(lp, L, a), 1n+L, a), L, both_r({SX.eqn(maxE(lp, L, a), I(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))) == True{} : Bool}, {SX.ltn(fl(lp, maxE(lp, L, a), 1n+L, a), 1n+L) == True{} : Bool}, fl_ok(lp, maxE(lp, L, a), 1n+L, a, t_leaves(~F, lp, L, a, hwf, hG, heq))))

def ik2(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> {I(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a)) == maxE(lp, L, a) : Nat}:
  Equal.sym(Nat, maxE(lp, L, a), I(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a)), SP.eqn_eq(maxE(lp, L, a), I(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a)), both_l({SX.eqn(maxE(lp, L, a), I(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))) == True{} : Bool}, {SX.ltn(fl(lp, maxE(lp, L, a), 1n+L, a), 1n+L) == True{} : Bool}, fl_ok(lp, maxE(lp, L, a), 1n+L, a, t_leaves(~F, lp, L, a, hwf, hG, heq)))))

# the variable leaving at k1 is basic there, nonbasic just after
def is_b(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> {St(lp, I(lp, plus(argE(lp, L, a), a)), plus(argE(lp, L, a), a)) == True{} : Bool}:
  RN.viol_basic(~F, lp, plus(argE(lp, L, a), a), RN.piv_step(lp, plus(argE(lp, L, a), a), go_at(lp, L, a, argE(lp, L, a), hd1(lp, L, a), hG)), hwf)

def is_nb(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> {St(lp, I(lp, plus(argE(lp, L, a), a)), plus(1n+argE(lp, L, a), a)) == False{} : Bool}:
  %Equal.sym(Nat, plus(argE(lp, L, a), 1n+a), 1n+plus(argE(lp, L, a), a), plus_succ(argE(lp, L, a), a)) : {St(lp, I(lp, plus(argE(lp, L, a), a)), _) == False{} : Bool}
  after_I(~F, lp, plus(argE(lp, L, a), a), go_at(lp, L, a, argE(lp, L, a), hd1(lp, L, a), hG), hwf)

def ie.end(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, b: Bool, hb: {b == St(lp, I(lp, plus(argE(lp, L, a), a)), plus(1n+L, a)) : Bool}, +hn: {noent(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a) == True{} : Bool}) -> {St(lp, I(lp, plus(argE(lp, L, a), a)), plus(1n+L, a)) == False{} : Bool}:
  match b:
    case False{}:
      Equal.sym(Bool, False{}, St(lp, I(lp, plus(argE(lp, L, a), a)), plus(1n+L, a)), hb)
    case True{}:
      absurd({St(lp, I(lp, plus(argE(lp, L, a), a)), plus(1n+L, a)) == False{} : Bool}, KA.tf(Equal.trans(Bool, True{}, St(lp, I(lp, plus(argE(lp, L, a), a)), plus(1n+argE(lp, L, a), a)), False{},
        Equal.sym(Bool, St(lp, I(lp, plus(argE(lp, L, a), a)), plus(1n+argE(lp, L, a), a)), True{}, lemA(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, 1n+argE(lp, L, a), a, hd1(lp, L, a), hG, hn, Equal.sym(Bool, True{}, St(lp, I(lp, plus(argE(lp, L, a), a)), plus(1n+L, a)), hb))),
        is_nb(~F, lp, L, a, hwf, hG, heq))))

def ie.c(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +hn: {noent(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a) == True{} : Bool}) -> Empty:
  KA.tf(Equal.trans(Bool, True{}, St(lp, I(lp, plus(argE(lp, L, a), a)), a), False{},
    Equal.sym(Bool, St(lp, I(lp, plus(argE(lp, L, a), a)), a), True{}, lemA(lp, I(lp, plus(argE(lp, L, a), a)), argE(lp, L, a), 0n, a, {==}, go_at0(lp, L, a, argE(lp, L, a), hd1(lp, L, a), hG), noent_pre(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, argE(lp, L, a), a, le_succ(argE(lp, L, a), L, hd1(lp, L, a)), hn), is_b(~F, lp, L, a, hwf, hG, heq))),
    Equal.trans(Bool, St(lp, I(lp, plus(argE(lp, L, a), a)), a), St(lp, I(lp, plus(argE(lp, L, a), a)), plus(1n+L, a)), False{}, ends(lp, L, a, I(lp, plus(argE(lp, L, a), a)), heq), ie.end(~F, lp, L, a, hwf, hG, heq, St(lp, I(lp, plus(argE(lp, L, a), a)), plus(1n+L, a)), {==}, hn))))

def ie.go(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, b: Bool, hb: {b == noent(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a) : Bool}) -> {noent(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a) == False{} : Bool}:
  match b:
    case False{}:
      Equal.sym(Bool, False{}, noent(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a), hb)
    case True{}:
      absurd({noent(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a) == False{} : Bool}, ie.c(~F, lp, L, a, hwf, hG, heq, Equal.sym(Bool, True{}, noent(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a), hb)))

# it enters somewhere in the range
def is_enters(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> {noent(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a) == False{} : Bool}:
  ie.go(~F, lp, L, a, hwf, hG, heq, noent(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a), {==})

def is_le_t(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> {KA.natle(I(lp, plus(argE(lp, L, a), a)), maxE(lp, L, a)) == True{} : Bool}:
  %Equal.sym(Nat, I(lp, plus(argE(lp, L, a), a)), En(lp, plus(fe(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a), a)), SP.eqn_eq(I(lp, plus(argE(lp, L, a), a)), En(lp, plus(fe(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a), a)), both_l({SX.eqn(I(lp, plus(argE(lp, L, a), a)), En(lp, plus(fe(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a), a))) == True{} : Bool}, {SX.ltn(fe(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a), 1n+L) == True{} : Bool}, fe_ok(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a, is_enters(~F, lp, L, a, hwf, hG, heq))))) : {KA.natle(_, maxE(lp, L, a)) == True{} : Bool}
  le_maxE(lp, L, fe(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a), a, ltn_succ_le(fe(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a), L, both_r({SX.eqn(I(lp, plus(argE(lp, L, a), a)), En(lp, plus(fe(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a), a))) == True{} : Bool}, {SX.ltn(fe(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a), 1n+L) == True{} : Bool}, fe_ok(lp, I(lp, plus(argE(lp, L, a), a)), 1n+L, a, is_enters(~F, lp, L, a, hwf, hG, heq)))))

def is_ne.go(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, b: Bool, hb: {b == SX.eqn(I(lp, plus(argE(lp, L, a), a)), maxE(lp, L, a)) : Bool}) -> {SX.eqn(I(lp, plus(argE(lp, L, a), a)), maxE(lp, L, a)) == False{} : Bool}:
  match b:
    case False{}:
      Equal.sym(Bool, False{}, SX.eqn(I(lp, plus(argE(lp, L, a), a)), maxE(lp, L, a)), hb)
    case True{}:
      absurd({SX.eqn(I(lp, plus(argE(lp, L, a), a)), maxE(lp, L, a)) == False{} : Bool}, KA.tf(Equal.trans(Bool, True{}, St(lp, maxE(lp, L, a), plus(argE(lp, L, a), a)), False{},
        (%SP.eqn_eq(I(lp, plus(argE(lp, L, a), a)), maxE(lp, L, a), Equal.sym(Bool, True{}, SX.eqn(I(lp, plus(argE(lp, L, a), a)), maxE(lp, L, a)), hb)) : {True{} == St(lp, _, plus(argE(lp, L, a), a)) : Bool}
         Equal.sym(Bool, St(lp, I(lp, plus(argE(lp, L, a), a)), plus(argE(lp, L, a), a)), True{}, is_b(~F, lp, L, a, hwf, hG, heq))),
        t_nb(~F, lp, L, a, hwf, hG, heq))))

# the variable leaving at k1 is smaller than t
def is_lt_t(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> {SX.ltn(I(lp, plus(argE(lp, L, a), a)), maxE(lp, L, a)) == True{} : Bool}:
  lt_of_le_ne(I(lp, plus(argE(lp, L, a), a)), maxE(lp, L, a), is_le_t(~F, lp, L, a, hwf, hG, heq), is_ne.go(~F, lp, L, a, hwf, hG, heq, SX.eqn(I(lp, plus(argE(lp, L, a), a)), maxE(lp, L, a)), {==}))
