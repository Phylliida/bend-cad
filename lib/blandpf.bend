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


def nl.end(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, b: Bool, hb: {b == St(lp, j, plus(1n+L, a)) : Bool}, +hn: {noent(lp, j, 1n+L, a) == True{} : Bool}, +hjq: {j == I(lp, plus(fl(lp, j, 1n+L, a), a)) : Nat}, +hd: {KA.natle(fl(lp, j, 1n+L, a), L) == True{} : Bool}) -> {St(lp, j, plus(1n+L, a)) == False{} : Bool}:
  match b:
    case False{}:
      Equal.sym(Bool, False{}, St(lp, j, plus(1n+L, a)), hb)
    case True{}:
      absurd({St(lp, j, plus(1n+L, a)) == False{} : Bool}, KA.tf(Equal.trans(Bool, True{}, St(lp, j, plus(1n+fl(lp, j, 1n+L, a), a)), False{},
        Equal.sym(Bool, St(lp, j, plus(1n+fl(lp, j, 1n+L, a), a)), True{}, lemA(lp, j, 1n+L, 1n+fl(lp, j, 1n+L, a), a, hd, hG, hn, Equal.sym(Bool, True{}, St(lp, j, plus(1n+L, a)), hb))),
        (%Equal.sym(Nat, plus(fl(lp, j, 1n+L, a), 1n+a), 1n+plus(fl(lp, j, 1n+L, a), a), plus_succ(fl(lp, j, 1n+L, a), a)) : {St(lp, j, _) == False{} : Bool}
         %Equal.sym(Nat, j, I(lp, plus(fl(lp, j, 1n+L, a), a)), hjq) : {St(lp, _, 1n+plus(fl(lp, j, 1n+L, a), a)) == False{} : Bool}
         after_I(~F, lp, plus(fl(lp, j, 1n+L, a), a), go_at(lp, L, a, fl(lp, j, 1n+L, a), hd, hG), hwf)))))

def nl.c(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, +hn: {noent(lp, j, 1n+L, a) == True{} : Bool}, +hl: {nolev(lp, j, 1n+L, a) == False{} : Bool}) -> Empty:
  +hjq = SP.eqn_eq(j, I(lp, plus(fl(lp, j, 1n+L, a), a)), both_l({SX.eqn(j, I(lp, plus(fl(lp, j, 1n+L, a), a))) == True{} : Bool}, {SX.ltn(fl(lp, j, 1n+L, a), 1n+L) == True{} : Bool}, fl_ok(lp, j, 1n+L, a, hl)))
  +hd = ltn_succ_le(fl(lp, j, 1n+L, a), L, both_r({SX.eqn(j, I(lp, plus(fl(lp, j, 1n+L, a), a))) == True{} : Bool}, {SX.ltn(fl(lp, j, 1n+L, a), 1n+L) == True{} : Bool}, fl_ok(lp, j, 1n+L, a, hl)))
  KA.tf(Equal.trans(Bool, True{}, St(lp, j, a), False{},
    Equal.sym(Bool, St(lp, j, a), True{}, lemA(lp, j, fl(lp, j, 1n+L, a), 0n, a, {==}, go_at0(lp, L, a, fl(lp, j, 1n+L, a), hd, hG), noent_pre(lp, j, 1n+L, fl(lp, j, 1n+L, a), a, le_succ(fl(lp, j, 1n+L, a), L, hd), hn),
      (%Equal.sym(Nat, j, I(lp, plus(fl(lp, j, 1n+L, a), a)), hjq) : {St(lp, _, plus(fl(lp, j, 1n+L, a), a)) == True{} : Bool}
       RN.viol_basic(~F, lp, plus(fl(lp, j, 1n+L, a), a), RN.piv_step(lp, plus(fl(lp, j, 1n+L, a), a), go_at(lp, L, a, fl(lp, j, 1n+L, a), hd, hG)), hwf)))),
    Equal.trans(Bool, St(lp, j, a), St(lp, j, plus(1n+L, a)), False{}, ends(lp, L, a, j, heq), nl.end(~F, lp, L, a, hwf, hG, heq, j, St(lp, j, plus(1n+L, a)), {==}, hn, hjq, hd))))

def nl.go(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, b: Bool, hb: {b == nolev(lp, j, 1n+L, a) : Bool}, +hn: {noent(lp, j, 1n+L, a) == True{} : Bool}) -> {nolev(lp, j, 1n+L, a) == True{} : Bool}:
  match b:
    case True{}:
      Equal.sym(Bool, True{}, nolev(lp, j, 1n+L, a), hb)
    case False{}:
      absurd({nolev(lp, j, 1n+L, a) == True{} : Bool}, nl.c(~F, lp, L, a, hwf, hG, heq, j, hn, Equal.sym(Bool, False{}, nolev(lp, j, 1n+L, a), hb)))

# a variable that never enters never leaves either
def nolev_of(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, +hn: {noent(lp, j, 1n+L, a) == True{} : Bool}) -> {nolev(lp, j, 1n+L, a) == True{} : Bool}:
  nl.go(~F, lp, L, a, hwf, hG, heq, j, nolev(lp, j, 1n+L, a), {==}, hn)

# so its status is the same at every step of the range
def st_const(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, +hn: {noent(lp, j, 1n+L, a) == True{} : Bool}, +d: Nat, +hd: {KA.natle(d, 1n+L) == True{} : Bool}) -> {St(lp, j, plus(d, a)) == St(lp, j, a) : Bool}:
  bool_eq(St(lp, j, plus(d, a)), St(lp, j, a),
    h => lemA(lp, j, d, 0n, a, {==}, go_down(lp, 1n+L, d, a, hd, hG), noent_pre(lp, j, 1n+L, d, a, hd, hn), h),
    h => lemB(lp, j, d, 0n, a, {==}, go_down(lp, 1n+L, d, a, hd, hG), nolev_pre(lp, j, 1n+L, d, a, hd, nolev_of(~F, lp, L, a, hwf, hG, heq, j, hn)), h))

# Differences of points, and sums over columns
# --------------------------------------------

# u - w, entry by entry (missing entries 0)
def fsub(~F: O.OField, u: M.Vec(~F), w: M.Vec(~F)) -> M.Vec(~F):
  match u w:
    case Nil{} Nil{}:
      Nil{}
    case Nil{} Con{y, s}:
      Con{O.sub(~F, O.zero(F), y), fsub(~F, Nil{}, s)}
    case Con{x, t} Nil{}:
      Con{O.sub(~F, x, O.zero(F)), fsub(~F, t, Nil{})}
    case Con{x, t} Con{y, s}:
      Con{O.sub(~F, x, y), fsub(~F, t, s)}

def fat_fsub(~F: O.OField, u: M.Vec(~F), w: M.Vec(~F), j: Nat) -> {SP.fat(~F, fsub(~F, u, w), j) == O.sub(~F, SP.fat(~F, u, j), SP.fat(~F, w, j)) : O.C(F)}:
  match u w j:
    case Nil{} Nil{} j:
      FR.fring_eq(~F, [], E.ZCst{S.Z0{}}, E.ZSub{E.ZCst{S.Z0{}}, E.ZCst{S.Z0{}}}, {==})
    case Nil{} Con{y, s} 0n:
      {==}
    case Nil{} Con{y, s} 1n+k:
      fat_fsub(~F, Nil{}, s, k)
    case Con{x, t} Nil{} 0n:
      {==}
    case Con{x, t} Nil{} 1n+k:
      fat_fsub(~F, t, Nil{}, k)
    case Con{x, t} Con{y, s} 0n:
      {==}
    case Con{x, t} Con{y, s} 1n+k:
      fat_fsub(~F, t, s, k)

# u . w1 - u . w2 = u . (w1 - w2)
def zdot_fsub(~F: O.OField, u: List<&2, S.Z>, w1: M.Vec(~F), w2: M.Vec(~F)) -> {O.sub(~F, SP.zdot(~F, u, w1), SP.zdot(~F, u, w2)) == SP.zdot(~F, u, fsub(~F, w1, w2)) : O.C(F)}:
  match u w1 w2:
    case Nil{} w1 w2:
      FR.fring_eq(~F, [], E.ZSub{E.ZCst{S.Z0{}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})
    case Con{x, t} Nil{} Nil{}:
      FR.fring_eq(~F, [], E.ZSub{E.ZCst{S.Z0{}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})
    case Con{+x, +t} Nil{} Con{+y, +s}:
      %zdot_fsub(~F, t, Nil{}, s) : {O.sub(~F, O.zero(F), O.add(F, O.mul(F, O.ofz(~F, x), y), SP.zdot(~F, t, s))) == O.add(F, O.mul(F, O.ofz(~F, x), O.sub(~F, O.zero(F), y)), _) : O.C(F)}
      %SP.zdot_nil_r(~F, t) : {O.sub(~F, O.zero(F), O.add(F, O.mul(F, O.ofz(~F, x), y), SP.zdot(~F, t, s))) == O.add(F, O.mul(F, O.ofz(~F, x), O.sub(~F, O.zero(F), y)), O.sub(~F, _, SP.zdot(~F, t, s))) : O.C(F)}
      FR.fring_eq(~F, [O.ofz(~F, x), y, SP.zdot(~F, t, s)], E.ZSub{E.ZCst{S.Z0{}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZSub{E.ZCst{S.Z0{}}, E.ZVar{1n}}}, E.ZSub{E.ZCst{S.Z0{}}, E.ZVar{2n}}}, {==})
    case Con{+x, +t} Con{+y, +s} Nil{}:
      %zdot_fsub(~F, t, s, Nil{}) : {O.sub(~F, O.add(F, O.mul(F, O.ofz(~F, x), y), SP.zdot(~F, t, s)), O.zero(F)) == O.add(F, O.mul(F, O.ofz(~F, x), O.sub(~F, y, O.zero(F))), _) : O.C(F)}
      %SP.zdot_nil_r(~F, t) : {O.sub(~F, O.add(F, O.mul(F, O.ofz(~F, x), y), SP.zdot(~F, t, s)), O.zero(F)) == O.add(F, O.mul(F, O.ofz(~F, x), O.sub(~F, y, O.zero(F))), O.sub(~F, SP.zdot(~F, t, s), _)) : O.C(F)}
      FR.fring_eq(~F, [O.ofz(~F, x), y, SP.zdot(~F, t, s)], E.ZSub{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZCst{S.Z0{}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZSub{E.ZVar{1n}, E.ZCst{S.Z0{}}}}, E.ZSub{E.ZVar{2n}, E.ZCst{S.Z0{}}}}, {==})
    case Con{+x, +t} Con{+y, +s} Con{+v, +r}:
      %zdot_fsub(~F, t, s, r) : {O.sub(~F, O.add(F, O.mul(F, O.ofz(~F, x), y), SP.zdot(~F, t, s)), O.add(F, O.mul(F, O.ofz(~F, x), v), SP.zdot(~F, t, r))) == O.add(F, O.mul(F, O.ofz(~F, x), O.sub(~F, y, v)), _) : O.C(F)}
      FR.fring_eq(~F, [O.ofz(~F, x), y, v, SP.zdot(~F, t, s), SP.zdot(~F, t, r)], E.ZSub{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{3n}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{4n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZSub{E.ZVar{1n}, E.ZVar{2n}}}, E.ZSub{E.ZVar{3n}, E.ZVar{4n}}}, {==})

# a row read at a difference is the difference of its readings
def rv_fsub(~F: O.OField, +r: SX.Rw, +w1: M.Vec(~F), +w2: M.Vec(~F)) -> {O.sub(~F, SP.rv(~F, r, w1), SP.rv(~F, r, w2)) == SP.rv(~F, r, fsub(~F, w1, w2)) : O.C(F)}:
  %zdot_fsub(~F, SX.Rw.m(r), w1, w2) : {O.sub(~F, SP.rv(~F, r, w1), SP.rv(~F, r, w2)) == O.mul(F, _, O.inv(F, O.ofp(~F, SX.Rw.d(r)))) : O.C(F)}
  FR.fring_eq(~F, [SP.zdot(~F, SX.Rw.m(r), w1), SP.zdot(~F, SX.Rw.m(r), w2), O.inv(F, O.ofp(~F, SX.Rw.d(r)))], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZMul{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, {==})

# the sum over columns j .. j + c - 1 of u_j w_j
def isum(~F: O.OField, c: Nat, +u: List<&2, S.Z>, +w: M.Vec(~F), +j: Nat) -> O.C(F):
  match c:
    case 0n:
      O.zero(F)
    case 1n+k:
      O.add(F, O.mul(F, O.ofz(~F, SX.at(u, j)), SP.fat(~F, w, j)), isum(~F, k, u, w, 1n+j))

def isum_shift(~F: O.OField, c: Nat, +x: S.Z, +ut: List<&2, S.Z>, +y: O.C(F), +wt: M.Vec(~F), +j: Nat) -> {isum(~F, c, ut, wt, j) == isum(~F, c, Con{x, ut}, Con{y, wt}, 1n+j) : O.C(F)}:
  match c:
    case 0n:
      {==}
    case 1n+k:
      %isum_shift(~F, k, x, ut, y, wt, 1n+j) : {O.add(F, O.mul(F, O.ofz(~F, SX.at(ut, j)), SP.fat(~F, wt, j)), isum(~F, k, ut, wt, 1n+j)) == O.add(F, O.mul(F, O.ofz(~F, SX.at(ut, j)), SP.fat(~F, wt, j)), _) : O.C(F)}
      {==}

def isum_nil_u(~F: O.OField, c: Nat, +w: M.Vec(~F), +j: Nat) -> {O.zero(F) == isum(~F, c, Nil{}, w, j) : O.C(F)}:
  match c:
    case 0n:
      {==}
    case 1n+k:
      %isum_nil_u(~F, k, w, 1n+j) : {O.zero(F) == O.add(F, O.mul(F, O.zero(F), SP.fat(~F, w, j)), _) : O.C(F)}
      FR.fring_eq(~F, [SP.fat(~F, w, j)], E.ZCst{S.Z0{}}, E.ZAdd{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZCst{S.Z0{}}}, {==})

def isum_nil_w(~F: O.OField, c: Nat, +u: List<&2, S.Z>, +j: Nat) -> {O.zero(F) == isum(~F, c, u, Nil{}, j) : O.C(F)}:
  match c:
    case 0n:
      {==}
    case 1n+k:
      %isum_nil_w(~F, k, u, 1n+j) : {O.zero(F) == O.add(F, O.mul(F, O.ofz(~F, SX.at(u, j)), O.zero(F)), _) : O.C(F)}
      FR.fring_eq(~F, [O.ofz(~F, SX.at(u, j))], E.ZCst{S.Z0{}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}}, {==})

# a row's dot product is the sum over its columns (c at least its length)
def zdot_isum(~F: O.OField, c: Nat, u: List<&2, S.Z>, w: M.Vec(~F), hu: {KA.natle(SX.vlen(u), c) == True{} : Bool}) -> {SP.zdot(~F, u, w) == isum(~F, c, u, w, 0n) : O.C(F)}:
  match c u w:
    case c Nil{} w:
      isum_nil_u(~F, c, w, 0n)
    case 0n Con{x, ut} w:
      absurd({SP.zdot(~F, Con{x, ut}, w) == isum(~F, 0n, Con{x, ut}, w, 0n) : O.C(F)}, KA.ft(hu))
    case 1n++k Con{+x, +ut} Nil{}:
      %isum_nil_w(~F, k, Con{x, ut}, 1n) : {O.zero(F) == O.add(F, O.mul(F, O.ofz(~F, x), O.zero(F)), _) : O.C(F)}
      FR.fring_eq(~F, [O.ofz(~F, x)], E.ZCst{S.Z0{}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}}, {==})
    case 1n++k Con{+x, +ut} Con{+y, +wt}:
      %Equal.sym(O.C(F), SP.zdot(~F, ut, wt), isum(~F, k, ut, wt, 0n), zdot_isum(~F, k, ut, wt, hu)) : {O.add(F, O.mul(F, O.ofz(~F, x), y), _) == O.add(F, O.mul(F, O.ofz(~F, x), y), isum(~F, k, Con{x, ut}, Con{y, wt}, 1n)) : O.C(F)}
      %isum_shift(~F, k, x, ut, y, wt, 0n) : {O.add(F, O.mul(F, O.ofz(~F, x), y), isum(~F, k, ut, wt, 0n)) == O.add(F, O.mul(F, O.ofz(~F, x), y), _) : O.C(F)}
      {==}

def bor(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      True{}
    case False{}:
      b

# t is among columns j .. j + c - 1
def inrange(+t: Nat, c: Nat, +j: Nat) -> Bool:
  match c:
    case 0n:
      False{}
    case 1n+k:
      bor(SX.eqn(j, t), inrange(t, k, 1n+j))

def le_lt_absurd(j: Nat, t: Nat, h1: {KA.natle(j, t) == True{} : Bool}, h2: {SX.ltn(t, j) == True{} : Bool}) -> Empty:
  match j t:
    case 0n 0n:
      KA.ft(h2)
    case 0n 1n+b:
      KA.ft(h2)
    case 1n+a 0n:
      KA.ft(h1)
    case 1n+a 1n+b:
      le_lt_absurd(a, b, h1, h2)

def inr.go(b: Bool, +t: Nat, k: Nat, +j: Nat, hb: {b == SX.eqn(j, t) : Bool}, h1: {KA.natle(j, t) == True{} : Bool}, ih: {KA.natle(1n+j, t) == True{} : Bool} -> {inrange(t, k, 1n+j) == True{} : Bool}) -> {bor(b, inrange(t, k, 1n+j)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih(RN.ltn_le(j, t, lt_of_le_ne(j, t, h1, Equal.sym(Bool, False{}, SX.eqn(j, t), hb))))

# j <= t < j + c: t is in the range
def inrange_ok(+t: Nat, c: Nat, +j: Nat, h1: {KA.natle(j, t) == True{} : Bool}, +h2: {SX.ltn(t, plus(c, j)) == True{} : Bool}) -> {inrange(t, c, j) == True{} : Bool}:
  match c:
    case 0n:
      absurd({inrange(t, 0n, j) == True{} : Bool}, le_lt_absurd(j, t, h1, h2))
    case 1n++k:
      inr.go(SX.eqn(j, t), t, k, j, {==}, h1, hh => inrange_ok(t, k, 1n+j, hh, h2))

def lneg_nonpos(~F: O.OField, +x0: O.C(F), +x1: O.C(F), h: LX.LNeg(~F, x0, x1)) -> LX.LNonpos(~F, x0, x1):
  match h:
    case Inl{+p}:
      Inl{p}
    case Inr{+p}:
      Inr{(LX.both_l({x0 == O.zero(F) : O.C(F)}, O.lt(F, x1, O.zero(F)), p), FO.lt_le(~F, x1, O.zero(F), LX.both_r({x0 == O.zero(F) : O.C(F)}, O.lt(F, x1, O.zero(F)), p)))}

# Row i at k1, read at the difference of values
# ---------------------------------------------


def isle_f(m: Nat, t: Nat, h: {SX.ltn(t, m) == True{} : Bool}) -> {Nat.is_le(m, t) == False{} : Bool}:
  match m t:
    case 0n t:
      absurd({Nat.is_le(0n, t) == False{} : Bool}, KA.ft(SP.ltn0(t, h)))
    case 1n+k 0n:
      {==}
    case 1n+k 1n+j:
      isle_f(k, j, h)

def lt_isle(m: Nat, j: Nat, h: {Nat.is_le(m, j) == False{} : Bool}) -> {SX.ltn(j, m) == True{} : Bool}:
  match m j:
    case 0n 0n:
      absurd({SX.ltn(0n, 0n) == True{} : Bool}, KA.tf(h))
    case 0n 1n+i:
      absurd({SX.ltn(1n+i, 0n) == True{} : Bool}, KA.tf(h))
    case 1n+k 0n:
      {==}
    case 1n+k 1n+i:
      lt_isle(k, i, h)

def at_past(u: List<&2, S.Z>, j: Nat, h: {KA.natle(SX.vlen(u), j) == True{} : Bool}) -> {S.Z0{} == SX.at(u, j) : S.Z}:
  match u j:
    case Nil{} j:
      {==}
    case Con{x, t} 0n:
      absurd({S.Z0{} == SX.at(Con{x, t}, 0n) : S.Z}, KA.ft(h))
    case Con{x, t} 1n+k:
      at_past(t, k, h)

def ne_of_lt_le(t: Nat, N: Nat, j: Nat, h1: {SX.ltn(t, N) == True{} : Bool}, h2: {KA.natle(N, j) == True{} : Bool}) -> {SX.eqn(j, t) == False{} : Bool}:
  match t N j:
    case t 0n j:
      absurd({SX.eqn(j, t) == False{} : Bool}, KA.ft(SP.ltn0(t, h1)))
    case 0n 1n+k 0n:
      absurd({SX.eqn(0n, 0n) == False{} : Bool}, KA.ft(h2))
    case 0n 1n+k 1n+i:
      {==}
    case 1n+s 1n+k 0n:
      absurd({SX.eqn(0n, 1n+s) == False{} : Bool}, KA.ft(h2))
    case 1n+s 1n+k 1n+i:
      ne_of_lt_le(s, k, i, h1, h2)

def ne_of_st.go(b: Bool, +lp: SX.LP, +j: Nat, +t: Nat, +q: Nat, hb: {b == SX.eqn(j, t) : Bool}, h1: {St(lp, j, q) == True{} : Bool}, h2: {St(lp, t, q) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      absurd({True{} == False{} : Bool}, KA.tf(Equal.trans(Bool, True{}, St(lp, t, q), False{},
        (%SP.eqn_eq(j, t, Equal.sym(Bool, True{}, SX.eqn(j, t), hb)) : {True{} == St(lp, _, q) : Bool}
         Equal.sym(Bool, St(lp, j, q), True{}, h1)),
        h2)))

def ne_of_st(+lp: SX.LP, +j: Nat, +t: Nat, +q: Nat, h1: {St(lp, j, q) == True{} : Bool}, h2: {St(lp, t, q) == False{} : Bool}) -> {SX.eqn(j, t) == False{} : Bool}:
  ne_of_st.go(SX.eqn(j, t), lp, j, t, q, {==}, h1, h2)

def iszero_z(c: S.Z, h: {SX.iszero(c) == True{} : Bool}) -> {S.Z0{} == c : S.Z}:
  SP.iszero_eq(c, Equal.sym(Bool, SX.iszero(c), True{}, h))

# entry j of the difference: row j at k2 less row j at k1, at v
def dl_at(~F: O.OField, +r2: List<&2, SX.Rw>, +r1: List<&2, SX.Rw>, +v: M.Vec(~F), +j: Nat) -> {SP.fat(~F, fsub(~F, SP.rmap(~F, r2, v), SP.rmap(~F, r1, v)), j) == O.sub(~F, SP.rv(~F, SX.rowat(r2, j), v), SP.rv(~F, SX.rowat(r1, j), v)) : O.C(F)}:
  %Equal.sym(O.C(F), SP.fat(~F, fsub(~F, SP.rmap(~F, r2, v), SP.rmap(~F, r1, v)), j), O.sub(~F, SP.fat(~F, SP.rmap(~F, r2, v), j), SP.fat(~F, SP.rmap(~F, r1, v), j)), fat_fsub(~F, SP.rmap(~F, r2, v), SP.rmap(~F, r1, v), j)) : {_ == O.sub(~F, SP.rv(~F, SX.rowat(r2, j), v), SP.rv(~F, SX.rowat(r1, j), v)) : O.C(F)}
  %SP.fat_rmap(~F, r2, v, j) : {O.sub(~F, _, SP.fat(~F, SP.rmap(~F, r1, v), j)) == O.sub(~F, SP.rv(~F, SX.rowat(r2, j), v), SP.rv(~F, SX.rowat(r1, j), v)) : O.C(F)}
  %SP.fat_rmap(~F, r1, v, j) : {O.sub(~F, SP.rv(~F, SX.rowat(r2, j), v), _) == O.sub(~F, SP.rv(~F, SX.rowat(r2, j), v), SP.rv(~F, SX.rowat(r1, j), v)) : O.C(F)}
  {==}

def le_of_nlt(j: Nat, N: Nat, h: {SX.ltn(j, N) == False{} : Bool}) -> {KA.natle(N, j) == True{} : Bool}:
  match j N:
    case j 0n:
      {==}
    case 0n 1n+k:
      absurd({KA.natle(1n+k, 0n) == True{} : Bool}, KA.tf(h))
    case 1n+i 1n+k:
      le_of_nlt(i, k, h)

def t_ltN(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> {SX.ltn(maxE(lp, L, a), SX.LP.nv(lp)) == True{} : Bool}:
  %ik2(~F, lp, L, a, hwf, hG, heq) : {SX.ltn(_, SX.LP.nv(lp)) == True{} : Bool}
  RN.lv_ltN(lp, RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a)), RN.piv_step(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a), go_at(lp, L, a, fl(lp, maxE(lp, L, a), 1n+L, a), hd2(~F, lp, L, a, hwf, hG, heq), hG)))

def t_ltm(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> {SX.ltn(maxE(lp, L, a), SX.LP.m(lp)) == True{} : Bool}:
  %ik2(~F, lp, L, a, hwf, hG, heq) : {SX.ltn(_, SX.LP.m(lp)) == True{} : Bool}
  RN.lv_lt(lp, RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a)), RN.piv_step(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a), go_at(lp, L, a, fl(lp, maxE(lp, L, a), 1n+L, a), hd2(~F, lp, L, a, hwf, hG, heq), hG)))

# a column past N: row i has no entry there
def col_big(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, +hj: {SX.ltn(j, SX.LP.nv(lp)) == False{} : Bool}) -> Either<&2, &2, LX.LNeg(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))), M.Both({SX.eqn(j, maxE(lp, L, a)) == False{} : Bool}, LX.LNonpos(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))))>:
  Inr{(ne_of_lt_le(maxE(lp, L, a), SX.LP.nv(lp), j, t_ltN(~F, lp, L, a, hwf, hG, heq), le_of_nlt(j, SX.LP.nv(lp), hj)),
    (%at_past(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j, KA.natle_trans(SX.vlen(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a)))), SX.LP.nv(lp), j, SP.rlok_at(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), SX.LP.nv(lp), I(lp, plus(argE(lp, L, a), a)), RN.rl_at(lp, plus(argE(lp, L, a), a), hwf)), le_of_nlt(j, SX.LP.nv(lp), hj))) : LX.LNonpos(~F, O.mul(F, O.ofz(~F, _), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, _), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j)))
     LX.lnonpos_czero(~F, SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))))}

# a column basic at k1: row i is 0 there
def col_basic(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, +hb: {St(lp, j, plus(argE(lp, L, a), a)) == True{} : Bool}) -> Either<&2, &2, LX.LNeg(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))), M.Both({SX.eqn(j, maxE(lp, L, a)) == False{} : Bool}, LX.LNonpos(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))))>:
  Inr{(ne_of_st(lp, j, maxE(lp, L, a), plus(argE(lp, L, a), a), hb, t_nb(~F, lp, L, a, hwf, hG, heq)),
    (%iszero_z(SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j), SP.zcol_at(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), j, I(lp, plus(argE(lp, L, a), a)), RN.iz_at(~F, lp, plus(argE(lp, L, a), a), hwf)(j, hb))) : LX.LNonpos(~F, O.mul(F, O.ofz(~F, _), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, _), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j)))
     LX.lnonpos_czero(~F, SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))))}

def band_f_r(a: Bool, h: {a == a : Bool}) -> {KA.band(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# x enters at step p + d (d < c): it does not never-enter
def noent_at(+lp: SX.LP, +x: Nat, c: Nat, d: Nat, +p: Nat, hd: {SX.ltn(d, c) == True{} : Bool}, h: {SX.eqn(x, En(lp, plus(d, p))) == True{} : Bool}) -> {noent(lp, x, c, p) == False{} : Bool}:
  match c d:
    case 0n d:
      absurd({noent(lp, x, 0n, p) == False{} : Bool}, KA.ft(SP.ltn0(d, hd)))
    case 1n+k 0n:
      %Equal.sym(Bool, SX.eqn(x, En(lp, p)), True{}, h) : {KA.band(bnot(_), noent(lp, x, k, 1n+p)) == False{} : Bool}
      {==}
    case 1n+k 1n+i:
      %Equal.sym(Bool, noent(lp, x, k, 1n+p), False{}, noent_at(lp, x, k, i, 1n+p, hd, h)) : {KA.band(bnot(SX.eqn(x, En(lp, p))), _) == False{} : Bool}
      band_f_r(bnot(SX.eqn(x, En(lp, p))), {==})

def eqn_refl(x: Nat) -> {SX.eqn(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+k:
      eqn_refl(k)

def t_ent(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> {noent(lp, maxE(lp, L, a), 1n+L, a) == False{} : Bool}:
  noent_at(lp, maxE(lp, L, a), 1n+L, argE(lp, L, a), a, SP.ltn_of(argE(lp, L, a), 1n+L, hd1(lp, L, a)), (%ek1(lp, L, a) : {SX.eqn(_, En(lp, plus(argE(lp, L, a), a))) == True{} : Bool}
    eqn_refl(En(lp, plus(argE(lp, L, a), a)))))

def nf_ne.go(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, b: Bool, hb: {b == SX.eqn(j, maxE(lp, L, a)) : Bool}, hn: {noent(lp, j, 1n+L, a) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      absurd({True{} == False{} : Bool}, KA.tf(Equal.trans(Bool, True{}, noent(lp, maxE(lp, L, a), 1n+L, a), False{},
        (%SP.eqn_eq(j, maxE(lp, L, a), Equal.sym(Bool, True{}, SX.eqn(j, maxE(lp, L, a)), hb)) : {True{} == noent(lp, _, 1n+L, a) : Bool}
         Equal.sym(Bool, noent(lp, j, 1n+L, a), True{}, hn)),
        t_ent(~F, lp, L, a, hwf, hG, heq))))

# row j of a dictionary where j is nonbasic, read at v, less v_j, is 0
def nb_zero(~F: O.OField, +lp: SX.LP, +q: Nat, +j: Nat, +v: M.Vec(~F), +hwf: {SP.lpwf(lp) == True{} : Bool}, hb: {St(lp, j, q) == False{} : Bool}, hj: {SX.ltn(j, SX.LP.nv(lp)) == True{} : Bool}) -> {SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, q)), j), v) == SP.fat(~F, v, j) : O.C(F)}:
  RN.iu_at(~F, lp, q, hwf)(j, hb, hj, v)

def dz(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, +v: M.Vec(~F), +hj: {SX.ltn(j, SX.LP.nv(lp)) == True{} : Bool}, +hb: {St(lp, j, plus(argE(lp, L, a), a)) == False{} : Bool}, +hb2: {St(lp, j, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a)) == False{} : Bool}) -> {SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), v), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), v)), j) == O.zero(F) : O.C(F)}:
  %Equal.sym(O.C(F), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), v), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), v)), j), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), j), v), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), j), v)), dl_at(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), v, j)) : {_ == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), j), v), SP.fat(~F, v, j), nb_zero(~F, lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a), j, v, hwf, hb2, hj)) : {O.sub(~F, _, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), j), v)) == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), j), v), SP.fat(~F, v, j), nb_zero(~F, lp, plus(argE(lp, L, a), a), j, v, hwf, hb, hj)) : {O.sub(~F, SP.fat(~F, v, j), _) == O.zero(F) : O.C(F)}
  FR.fring_eq(~F, [SP.fat(~F, v, j)], E.ZSub{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Z0{}}, {==})

# a column that never enters keeps its status, so its difference is 0
def col_nf(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, +hj: {SX.ltn(j, SX.LP.nv(lp)) == True{} : Bool}, +hb: {St(lp, j, plus(argE(lp, L, a), a)) == False{} : Bool}, +hn: {noent(lp, j, 1n+L, a) == True{} : Bool}) -> Either<&2, &2, LX.LNeg(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))), M.Both({SX.eqn(j, maxE(lp, L, a)) == False{} : Bool}, LX.LNonpos(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))))>:
  +hb2 = Equal.trans(Bool, St(lp, j, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a)), St(lp, j, a), False{}, st_const(~F, lp, L, a, hwf, hG, heq, j, hn, fl(lp, maxE(lp, L, a), 1n+L, a), le_succ(fl(lp, maxE(lp, L, a), 1n+L, a), L, hd2(~F, lp, L, a, hwf, hG, heq))), Equal.trans(Bool, St(lp, j, a), St(lp, j, plus(argE(lp, L, a), a)), False{}, Equal.sym(Bool, St(lp, j, plus(argE(lp, L, a), a)), St(lp, j, a), st_const(~F, lp, L, a, hwf, hG, heq, j, hn, argE(lp, L, a), le_succ(argE(lp, L, a), L, hd1(lp, L, a)))), hb))
  Inr{(nf_ne.go(~F, lp, L, a, hwf, hG, heq, j, SX.eqn(j, maxE(lp, L, a)), {==}, hn),
    LX.lnonpos_zero(~F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j), dz(~F, lp, L, a, hwf, hG, heq, j, RN.zv(~F, SX.LP.v0(lp)), hj, hb, hb2), dz(~F, lp, L, a, hwf, hG, heq, j, RN.zv(~F, SX.LP.v1(lp)), hj, hb, hb2)))}

def helpful_pos(~F: O.OField, c: S.Z, h: {SX.helpful(c, False{}) == True{} : Bool}) -> O.lt(F, O.zero(F), O.ofz(~F, c)):
  match c:
    case S.Z0{}:
      absurd(O.lt(F, O.zero(F), O.ofz(~F, S.Z0{})), KA.ft(h))
    case S.Zpos{+p}:
      QE.ofp_pos(~F, p)
    case S.Zneg{p}:
      absurd(O.lt(F, O.zero(F), O.ofz(~F, S.Zneg{p})), KA.ft(h))

# t's entry in row i at k1 is positive (t can raise it, and t is a slack)
def t_pos(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> O.lt(F, O.zero(F), O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), maxE(lp, L, a)))):
  helpful_pos(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), maxE(lp, L, a)), (%isle_f(SX.LP.m(lp), maxE(lp, L, a), t_ltm(~F, lp, L, a, hwf, hG, heq)) : {SX.helpful(SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), maxE(lp, L, a)), _) == True{} : Bool}
    %ek1(lp, L, a) : {SX.helpful(SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), _), Nat.is_le(SX.LP.m(lp), _)) == True{} : Bool}
    RN.en_help(lp, RN.tab(lp, plus(argE(lp, L, a), a)), RN.piv_step(lp, plus(argE(lp, L, a), a), go_at(lp, L, a, argE(lp, L, a), hd1(lp, L, a), hG)))))

# t at k1 is nonbasic: its value is its bound
def t_at_k1(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +v: M.Vec(~F)) -> {SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), maxE(lp, L, a)), v) == SP.fat(~F, v, maxE(lp, L, a)) : O.C(F)}:
  nb_zero(~F, lp, plus(argE(lp, L, a), a), maxE(lp, L, a), v, hwf, t_nb(~F, lp, L, a, hwf, hG, heq), t_ltN(~F, lp, L, a, hwf, hG, heq))

# t at k2 is below its bound
def t_viol(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> LX.LNeg(~F, O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v0(lp))), O.ofz(~F, S.Z.neg(RN.Ineq.b(RN.qat(SX.LP.qs(lp), maxE(lp, L, a)))))), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v1(lp))), O.ofz(~F, SX.ind(RN.Ineq.s(RN.qat(SX.LP.qs(lp), maxE(lp, L, a))))))):
  %ik2(~F, lp, L, a, hwf, hG, heq) : LX.LNeg(~F, O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), _), RN.zv(~F, SX.LP.v0(lp))), O.ofz(~F, S.Z.neg(RN.Ineq.b(RN.qat(SX.LP.qs(lp), _))))), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), _), RN.zv(~F, SX.LP.v1(lp))), O.ofz(~F, SX.ind(RN.Ineq.s(RN.qat(SX.LP.qs(lp), _))))))
  RN.viol_f(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), I(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), SX.LP.v0(lp), SX.LP.v1(lp), RN.qat(SX.LP.qs(lp), I(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.lv_viol(lp, RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a)), RN.piv_step(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a), go_at(lp, L, a, fl(lp, maxE(lp, L, a), 1n+L, a), hd2(~F, lp, L, a, hwf, hG, heq), hG)), RN.hr_at(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))))

# t's difference is negative
def t_dneg(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> LX.LNeg(~F, SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), maxE(lp, L, a)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), maxE(lp, L, a))):
  %Equal.sym(O.C(F), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), maxE(lp, L, a)), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v0(lp))), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v0(lp)))), dl_at(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)), maxE(lp, L, a))) : LX.LNeg(~F, _, SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), maxE(lp, L, a)))
  %Equal.sym(O.C(F), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), maxE(lp, L, a)), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v1(lp))), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v1(lp)))), dl_at(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)), maxE(lp, L, a))) : LX.LNeg(~F, O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v0(lp))), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v0(lp)))), _)
  %Equal.sym(O.C(F), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v0(lp))), SP.fat(~F, RN.zv(~F, SX.LP.v0(lp)), maxE(lp, L, a)), t_at_k1(~F, lp, L, a, hwf, hG, heq, RN.zv(~F, SX.LP.v0(lp)))) : LX.LNeg(~F, O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v0(lp))), _), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v1(lp))), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v1(lp)))))
  %Equal.sym(O.C(F), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v1(lp))), SP.fat(~F, RN.zv(~F, SX.LP.v1(lp)), maxE(lp, L, a)), t_at_k1(~F, lp, L, a, hwf, hG, heq, RN.zv(~F, SX.LP.v1(lp)))) : LX.LNeg(~F, O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v0(lp))), SP.fat(~F, RN.zv(~F, SX.LP.v0(lp)), maxE(lp, L, a))), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v1(lp))), _))
  %Equal.sym(O.C(F), SP.fat(~F, RN.zv(~F, SX.LP.v0(lp)), maxE(lp, L, a)), O.ofz(~F, S.Z.neg(RN.Ineq.b(RN.qat(SX.LP.qs(lp), maxE(lp, L, a))))), RN.bnd_v0(~F, lp, maxE(lp, L, a), t_ltm(~F, lp, L, a, hwf, hG, heq))) : LX.LNeg(~F, O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v0(lp))), _), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v1(lp))), SP.fat(~F, RN.zv(~F, SX.LP.v1(lp)), maxE(lp, L, a))))
  %Equal.sym(O.C(F), SP.fat(~F, RN.zv(~F, SX.LP.v1(lp)), maxE(lp, L, a)), O.ofz(~F, SX.ind(RN.Ineq.s(RN.qat(SX.LP.qs(lp), maxE(lp, L, a))))), RN.bnd_v1(~F, lp, maxE(lp, L, a), t_ltm(~F, lp, L, a, hwf, hG, heq))) : LX.LNeg(~F, O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v0(lp))), O.ofz(~F, S.Z.neg(RN.Ineq.b(RN.qat(SX.LP.qs(lp), maxE(lp, L, a)))))), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), maxE(lp, L, a)), RN.zv(~F, SX.LP.v1(lp))), _))
  t_viol(~F, lp, L, a, hwf, hG, heq)

# t's column: positive entry times negative difference
def col_t(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, hjt: {j == maxE(lp, L, a) : Nat}) -> Either<&2, &2, LX.LNeg(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))), M.Both({SX.eqn(j, maxE(lp, L, a)) == False{} : Bool}, LX.LNonpos(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))))>:
  %Equal.sym(Nat, j, maxE(lp, L, a), hjt) : Either<&2, &2, LX.LNeg(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), _)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), _)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), _)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), _))), M.Both({SX.eqn(_, maxE(lp, L, a)) == False{} : Bool}, LX.LNonpos(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), _)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), _)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), _)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), _))))>
  Inl{LX.lneg_scale(~F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), maxE(lp, L, a))), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), maxE(lp, L, a)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), maxE(lp, L, a)), t_pos(~F, lp, L, a, hwf, hG, heq), t_dneg(~F, lp, L, a, hwf, hG, heq))}

# a slack j < t at k2 is not below its bound: its difference is >= 0
def lt_dnn(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, +hjt: {SX.ltn(j, maxE(lp, L, a)) == True{} : Bool}, +hb: {St(lp, j, plus(argE(lp, L, a), a)) == False{} : Bool}, +hjN: {SX.ltn(j, SX.LP.nv(lp)) == True{} : Bool}, +hjm: {SX.ltn(j, SX.LP.m(lp)) == True{} : Bool}) -> LX.LNonneg(~F, SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j)):
  %Equal.sym(O.C(F), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), j), RN.zv(~F, SX.LP.v0(lp))), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), j), RN.zv(~F, SX.LP.v0(lp)))), dl_at(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)), j)) : LX.LNonneg(~F, _, SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))
  %Equal.sym(O.C(F), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), j), RN.zv(~F, SX.LP.v1(lp))), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), j), RN.zv(~F, SX.LP.v1(lp)))), dl_at(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)), j)) : LX.LNonneg(~F, O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), j), RN.zv(~F, SX.LP.v0(lp))), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), j), RN.zv(~F, SX.LP.v0(lp)))), _)
  %Equal.sym(O.C(F), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), j), RN.zv(~F, SX.LP.v0(lp))), SP.fat(~F, RN.zv(~F, SX.LP.v0(lp)), j), nb_zero(~F, lp, plus(argE(lp, L, a), a), j, RN.zv(~F, SX.LP.v0(lp)), hwf, hb, hjN)) : LX.LNonneg(~F, O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), j), RN.zv(~F, SX.LP.v0(lp))), _), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), j), RN.zv(~F, SX.LP.v1(lp))), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), j), RN.zv(~F, SX.LP.v1(lp)))))
  %Equal.sym(O.C(F), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), j), RN.zv(~F, SX.LP.v1(lp))), SP.fat(~F, RN.zv(~F, SX.LP.v1(lp)), j), nb_zero(~F, lp, plus(argE(lp, L, a), a), j, RN.zv(~F, SX.LP.v1(lp)), hwf, hb, hjN)) : LX.LNonneg(~F, O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), j), RN.zv(~F, SX.LP.v0(lp))), SP.fat(~F, RN.zv(~F, SX.LP.v0(lp)), j)), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), j), RN.zv(~F, SX.LP.v1(lp))), _))
  %Equal.sym(O.C(F), SP.fat(~F, RN.zv(~F, SX.LP.v0(lp)), j), O.ofz(~F, S.Z.neg(RN.Ineq.b(RN.qat(SX.LP.qs(lp), j)))), RN.bnd_v0(~F, lp, j, hjm)) : LX.LNonneg(~F, O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), j), RN.zv(~F, SX.LP.v0(lp))), _), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), j), RN.zv(~F, SX.LP.v1(lp))), SP.fat(~F, RN.zv(~F, SX.LP.v1(lp)), j)))
  %Equal.sym(O.C(F), SP.fat(~F, RN.zv(~F, SX.LP.v1(lp)), j), O.ofz(~F, SX.ind(RN.Ineq.s(RN.qat(SX.LP.qs(lp), j)))), RN.bnd_v1(~F, lp, j, hjm)) : LX.LNonneg(~F, O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), j), RN.zv(~F, SX.LP.v0(lp))), O.ofz(~F, S.Z.neg(RN.Ineq.b(RN.qat(SX.LP.qs(lp), j))))), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), j), RN.zv(~F, SX.LP.v1(lp))), _))
  RN.noviol_f(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), j), SX.LP.v0(lp), SX.LP.v1(lp), RN.qat(SX.LP.qs(lp), j), RN.lv_min(lp, RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a)), RN.piv_step(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a), go_at(lp, L, a, fl(lp, maxE(lp, L, a), 1n+L, a), hd2(~F, lp, L, a, hwf, hG, heq), hG)), RN.hr_at(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a)), j, (%Equal.sym(Nat, I(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a)), maxE(lp, L, a), ik2(~F, lp, L, a, hwf, hG, heq)) : {SX.ltn(j, _) == True{} : Bool}
    hjt)))

def lt.go(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, c: S.Z, +hc: {c == SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j) : S.Z}, +hjt: {SX.ltn(j, maxE(lp, L, a)) == True{} : Bool}, +hb: {St(lp, j, plus(argE(lp, L, a), a)) == False{} : Bool}, +hjN: {SX.ltn(j, SX.LP.nv(lp)) == True{} : Bool}, +hh: {SX.helpful(SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j), Nat.is_le(SX.LP.m(lp), j)) == False{} : Bool}) -> LX.LNonpos(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))):
  match c:
    case S.Z0{}:
      %hc : LX.LNonpos(~F, O.mul(F, O.ofz(~F, _), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, _), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j)))
      LX.lnonpos_czero(~F, SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))
    case S.Zpos{p}:
      absurd(LX.LNonpos(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))), KA.tf((%Equal.sym(S.Z, S.Zpos{p}, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j), hc) : {SX.helpful(_, Nat.is_le(SX.LP.m(lp), j)) == False{} : Bool}
        hh)))
    case S.Zneg{+q}:
      %hc : LX.LNonpos(~F, O.mul(F, O.ofz(~F, _), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, _), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j)))
      LX.lnonpos_scale_neg(~F, O.ofz(~F, S.Zneg{q}), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j), FO.pos_neg(~F, O.ofp(~F, q), QE.ofp_pos(~F, q)),
        lt_dnn(~F, lp, L, a, hwf, hG, heq, j, hjt, hb, hjN, lt_isle(SX.LP.m(lp), j, (%Equal.sym(S.Z, S.Zneg{q}, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j), hc) : {SX.helpful(_, Nat.is_le(SX.LP.m(lp), j)) == False{} : Bool}
          hh))))

# a fickle column j < t: a negative entry is at a slack not below its
# bound at k2, a positive entry would have entered
def col_lt(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, +hjt: {SX.ltn(j, maxE(lp, L, a)) == True{} : Bool}, +hb: {St(lp, j, plus(argE(lp, L, a), a)) == False{} : Bool}, +hjN: {SX.ltn(j, SX.LP.nv(lp)) == True{} : Bool}) -> Either<&2, &2, LX.LNeg(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))), M.Both({SX.eqn(j, maxE(lp, L, a)) == False{} : Bool}, LX.LNonpos(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))))>:
  Inr{(SP.ltn_ne(j, maxE(lp, L, a), hjt), lt.go(~F, lp, L, a, hwf, hG, heq, j, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j), {==}, hjt, hb, hjN, RN.en_min(lp, RN.tab(lp, plus(argE(lp, L, a), a)), RN.piv_step(lp, plus(argE(lp, L, a), a), go_at(lp, L, a, argE(lp, L, a), hd1(lp, L, a), hG)), j, (%Equal.sym(Nat, En(lp, plus(argE(lp, L, a), a)), maxE(lp, L, a), ek1(lp, L, a)) : {SX.ltn(j, _) == True{} : Bool}
    hjt))))}

# a variable entering in the range is at most t
def ent_le_t(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, +hn: {noent(lp, j, 1n+L, a) == False{} : Bool}) -> {KA.natle(j, maxE(lp, L, a)) == True{} : Bool}:
  %Equal.sym(Nat, j, En(lp, plus(fe(lp, j, 1n+L, a), a)), SP.eqn_eq(j, En(lp, plus(fe(lp, j, 1n+L, a), a)), both_l({SX.eqn(j, En(lp, plus(fe(lp, j, 1n+L, a), a))) == True{} : Bool}, {SX.ltn(fe(lp, j, 1n+L, a), 1n+L) == True{} : Bool}, fe_ok(lp, j, 1n+L, a, hn)))) : {KA.natle(_, maxE(lp, L, a)) == True{} : Bool}
  le_maxE(lp, L, fe(lp, j, 1n+L, a), a, ltn_succ_le(fe(lp, j, 1n+L, a), L, both_r({SX.eqn(j, En(lp, plus(fe(lp, j, 1n+L, a), a))) == True{} : Bool}, {SX.ltn(fe(lp, j, 1n+L, a), 1n+L) == True{} : Bool}, fe_ok(lp, j, 1n+L, a, hn))))

def col.f(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, b: Bool, hb_: {b == SX.eqn(j, maxE(lp, L, a)) : Bool}, +hle: {KA.natle(j, maxE(lp, L, a)) == True{} : Bool}, +hjN: {SX.ltn(j, SX.LP.nv(lp)) == True{} : Bool}, +hb: {St(lp, j, plus(argE(lp, L, a), a)) == False{} : Bool}) -> Either<&2, &2, LX.LNeg(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))), M.Both({SX.eqn(j, maxE(lp, L, a)) == False{} : Bool}, LX.LNonpos(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))))>:
  match b:
    case True{}:
      col_t(~F, lp, L, a, hwf, hG, heq, j, SP.eqn_eq(j, maxE(lp, L, a), Equal.sym(Bool, True{}, SX.eqn(j, maxE(lp, L, a)), hb_)))
    case False{}:
      col_lt(~F, lp, L, a, hwf, hG, heq, j, lt_of_le_ne(j, maxE(lp, L, a), hle, Equal.sym(Bool, False{}, SX.eqn(j, maxE(lp, L, a)), hb_)), hb, hjN)

def col.e(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, b: Bool, hb_: {b == noent(lp, j, 1n+L, a) : Bool}, +hjN: {SX.ltn(j, SX.LP.nv(lp)) == True{} : Bool}, +hb: {St(lp, j, plus(argE(lp, L, a), a)) == False{} : Bool}) -> Either<&2, &2, LX.LNeg(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))), M.Both({SX.eqn(j, maxE(lp, L, a)) == False{} : Bool}, LX.LNonpos(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))))>:
  match b:
    case True{}:
      col_nf(~F, lp, L, a, hwf, hG, heq, j, hjN, hb, Equal.sym(Bool, True{}, noent(lp, j, 1n+L, a), hb_))
    case False{}:
      col.f(~F, lp, L, a, hwf, hG, heq, j, SX.eqn(j, maxE(lp, L, a)), {==}, ent_le_t(~F, lp, L, a, hwf, hG, heq, j, Equal.sym(Bool, False{}, noent(lp, j, 1n+L, a), hb_)), hjN, hb)

def col.b(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, b: Bool, hb_: {b == St(lp, j, plus(argE(lp, L, a), a)) : Bool}, +hjN: {SX.ltn(j, SX.LP.nv(lp)) == True{} : Bool}) -> Either<&2, &2, LX.LNeg(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))), M.Both({SX.eqn(j, maxE(lp, L, a)) == False{} : Bool}, LX.LNonpos(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))))>:
  match b:
    case True{}:
      col_basic(~F, lp, L, a, hwf, hG, heq, j, Equal.sym(Bool, True{}, St(lp, j, plus(argE(lp, L, a), a)), hb_))
    case False{}:
      col.e(~F, lp, L, a, hwf, hG, heq, j, noent(lp, j, 1n+L, a), {==}, hjN, Equal.sym(Bool, False{}, St(lp, j, plus(argE(lp, L, a), a)), hb_))

def col.n(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, b: Bool, hb_: {b == SX.ltn(j, SX.LP.nv(lp)) : Bool}) -> Either<&2, &2, LX.LNeg(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))), M.Both({SX.eqn(j, maxE(lp, L, a)) == False{} : Bool}, LX.LNonpos(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))))>:
  match b:
    case True{}:
      col.b(~F, lp, L, a, hwf, hG, heq, j, St(lp, j, plus(argE(lp, L, a), a)), {==}, Equal.sym(Bool, True{}, SX.ltn(j, SX.LP.nv(lp)), hb_))
    case False{}:
      col_big(~F, lp, L, a, hwf, hG, heq, j, Equal.sym(Bool, False{}, SX.ltn(j, SX.LP.nv(lp)), hb_))

# every column's term: t's negative, every other one not positive
def col(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat) -> Either<&2, &2, LX.LNeg(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))), M.Both({SX.eqn(j, maxE(lp, L, a)) == False{} : Bool}, LX.LNonpos(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))))>:
  col.n(~F, lp, L, a, hwf, hG, heq, j, SX.ltn(j, SX.LP.nv(lp)), {==})


def bor_ff(a: Bool, b: Bool, ha: {a == False{} : Bool}, hb: {b == False{} : Bool}) -> {bor(a, b) == False{} : Bool}:
  match a:
    case True{}:
      absurd({bor(True{}, b) == False{} : Bool}, KA.tf(ha))
    case False{}:
      hb

def ss.go(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +j: Nat, +k: Nat, h1: Either<&2, &2, LX.LNeg(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))), M.Both({SX.eqn(j, maxE(lp, L, a)) == False{} : Bool}, LX.LNonpos(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))))>, h2: Either<&2, &2, LX.LNeg(~F, isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), 1n+j), isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), 1n+j)), M.Both({inrange(maxE(lp, L, a), k, 1n+j) == False{} : Bool}, LX.LNonpos(~F, isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), 1n+j), isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), 1n+j)))>) -> Either<&2, &2, LX.LNeg(~F, O.add(F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), 1n+j)), O.add(F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j)), isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), 1n+j))), M.Both({bor(SX.eqn(j, maxE(lp, L, a)), inrange(maxE(lp, L, a), k, 1n+j)) == False{} : Bool}, LX.LNonpos(~F, O.add(F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), 1n+j)), O.add(F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j)), isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), 1n+j))))>:
  match h1 h2:
    case Inl{+u} Inl{+v}:
      Inl{LX.lneg_add_l(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j)), isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), 1n+j), isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), 1n+j), u, lneg_nonpos(~F, isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), 1n+j), isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), 1n+j), v))}
    case Inl{+u} Inr{+v}:
      Inl{LX.lneg_add_l(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j)), isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), 1n+j), isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), 1n+j), u, both_r({inrange(maxE(lp, L, a), k, 1n+j) == False{} : Bool}, LX.LNonpos(~F, isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), 1n+j), isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), 1n+j)), v))}
    case Inr{+u} Inl{+v}:
      Inl{LX.lneg_add_r(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j)), isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), 1n+j), isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), 1n+j), both_r({SX.eqn(j, maxE(lp, L, a)) == False{} : Bool}, LX.LNonpos(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))), u), v)}
    case Inr{+u} Inr{+v}:
      Inr{(bor_ff(SX.eqn(j, maxE(lp, L, a)), inrange(maxE(lp, L, a), k, 1n+j), both_l({SX.eqn(j, maxE(lp, L, a)) == False{} : Bool}, LX.LNonpos(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))), u), both_l({inrange(maxE(lp, L, a), k, 1n+j) == False{} : Bool}, LX.LNonpos(~F, isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), 1n+j), isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), 1n+j)), v)),
        LX.lnonpos_add(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j)), isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), 1n+j), isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), 1n+j), both_r({SX.eqn(j, maxE(lp, L, a)) == False{} : Bool}, LX.LNonpos(~F, O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j)), O.mul(F, O.ofz(~F, SX.at(RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), j)), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j))), u), both_r({inrange(maxE(lp, L, a), k, 1n+j) == False{} : Bool}, LX.LNonpos(~F, isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), 1n+j), isum(~F, k, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), 1n+j)), v)))}

# the sum over columns j .. j + c - 1: negative, or not positive with t
# outside the columns
def sumsign(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, c: Nat, +j: Nat) -> Either<&2, &2, LX.LNeg(~F, isum(~F, c, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j), isum(~F, c, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j)), M.Both({inrange(maxE(lp, L, a), c, j) == False{} : Bool}, LX.LNonpos(~F, isum(~F, c, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j), isum(~F, c, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j)))>:
  match c:
    case 0n:
      Inr{({==}, Inr{({==}, Inr{{==}})})}
    case 1n++k:
      ss.go(~F, lp, L, a, hwf, hG, heq, j, k, col(~F, lp, L, a, hwf, hG, heq, j), sumsign(~F, lp, L, a, hwf, hG, heq, k, 1n+j))


def plus_zero(c: Nat) -> {plus(c, 0n) == c : Nat}:
  match c:
    case 0n:
      {==}
    case 1n++k:
      %Equal.sym(Nat, plus(k, 1n), 1n+plus(k, 0n), plus_succ(k, 0n)) : {_ == 1n+k : Nat}
      %Equal.sym(Nat, plus(k, 0n), k, plus_zero(k)) : {1n+_ == 1n+k : Nat}
      {==}

def lneg_scale_r(~F: O.OField, +x0: O.C(F), +x1: O.C(F), +c: O.C(F), hc: O.lt(F, O.zero(F), c), h: LX.LNeg(~F, x0, x1)) -> LX.LNeg(~F, O.mul(F, x0, c), O.mul(F, x1, c)):
  %O.mul_comm(F)(c, x0) : LX.LNeg(~F, _, O.mul(F, x1, c))
  %O.mul_comm(F)(c, x1) : LX.LNeg(~F, O.mul(F, c, x0), _)
  LX.lneg_scale(~F, c, x0, x1, hc, h)

def rn.go(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +c: Nat, +j: Nat, h: Either<&2, &2, LX.LNeg(~F, isum(~F, c, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j), isum(~F, c, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j)), M.Both({inrange(maxE(lp, L, a), c, j) == False{} : Bool}, LX.LNonpos(~F, isum(~F, c, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j), isum(~F, c, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j)))>, hin: {inrange(maxE(lp, L, a), c, j) == True{} : Bool}) -> LX.LNeg(~F, isum(~F, c, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j), isum(~F, c, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j)):
  match h:
    case Inl{u}:
      u
    case Inr{p}:
      absurd(LX.LNeg(~F, isum(~F, c, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j), isum(~F, c, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j)), KA.tf(Equal.trans(Bool, True{}, inrange(maxE(lp, L, a), c, j), False{}, Equal.sym(Bool, inrange(maxE(lp, L, a), c, j), True{}, hin), both_l({inrange(maxE(lp, L, a), c, j) == False{} : Bool}, LX.LNonpos(~F, isum(~F, c, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), j), isum(~F, c, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), j)), p))))

# row i at k1, read at the difference, is negative
def row_neg(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> LX.LNeg(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp))))), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))))):
  +hv = SP.rlok_at(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), SX.LP.nv(lp), I(lp, plus(argE(lp, L, a), a)), RN.rl_at(lp, plus(argE(lp, L, a), a), hwf))
  lneg_scale_r(~F, SP.zdot(~F, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp))))), SP.zdot(~F, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp))))), O.inv(F, O.ofp(~F, SX.Rw.d(SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a)))))), RN.inv_pos(~F, SX.Rw.d(SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))))),
    (%Equal.sym(O.C(F), SP.zdot(~F, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp))))), isum(~F, SX.LP.nv(lp), RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), 0n), zdot_isum(~F, SX.LP.nv(lp), RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), hv)) : LX.LNeg(~F, _, SP.zdot(~F, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp))))))
     %Equal.sym(O.C(F), SP.zdot(~F, RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp))))), isum(~F, SX.LP.nv(lp), RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), 0n), zdot_isum(~F, SX.LP.nv(lp), RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), hv)) : LX.LNeg(~F, isum(~F, SX.LP.nv(lp), RN.rowi(lp, RN.tab(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), 0n), _)
     rn.go(~F, lp, L, a, hwf, hG, heq, SX.LP.nv(lp), 0n, sumsign(~F, lp, L, a, hwf, hG, heq, SX.LP.nv(lp), 0n), inrange_ok(maxE(lp, L, a), SX.LP.nv(lp), 0n, {==}, (%Equal.sym(Nat, plus(SX.LP.nv(lp), 0n), SX.LP.nv(lp), plus_zero(SX.LP.nv(lp))) : {SX.ltn(maxE(lp, L, a), _) == True{} : Bool}
       t_ltN(~F, lp, L, a, hwf, hG, heq))))))

# the difference at i is row i (at k1) read at the difference
def rowid(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}, +v: M.Vec(~F)) -> {SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), v), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), v)), I(lp, plus(argE(lp, L, a), a))) == SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), v), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), v))) : O.C(F)}:
  +hn = RN.hn_at(lp, plus(argE(lp, L, a), a), RN.piv_step(lp, plus(argE(lp, L, a), a), go_at(lp, L, a, argE(lp, L, a), hd1(lp, L, a), hG)))
  %Equal.sym(O.C(F), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), v), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), v)), I(lp, plus(argE(lp, L, a), a))), O.sub(~F, SP.fat(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), v), I(lp, plus(argE(lp, L, a), a))), SP.fat(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), v), I(lp, plus(argE(lp, L, a), a)))), fat_fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), v), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), v), I(lp, plus(argE(lp, L, a), a)))) : {_ == SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), v), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), v))) : O.C(F)}
  %Equal.sym(O.C(F), SP.fat(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), v), I(lp, plus(argE(lp, L, a), a))), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), v)), SP.agree_at(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), v), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), v), I(lp, plus(argE(lp, L, a), a)), RN.i2_at(~F, lp, plus(argE(lp, L, a), a))(SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), v), RN.i1_at(~F, lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a), hwf)(v)), hn)) : {O.sub(~F, _, SP.fat(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), v), I(lp, plus(argE(lp, L, a), a)))) == SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), v), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), v))) : O.C(F)}
  %Equal.sym(O.C(F), SP.fat(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), v), I(lp, plus(argE(lp, L, a), a))), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), v)), SP.agree_at(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), v), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), v), I(lp, plus(argE(lp, L, a), a)), RN.i2_at(~F, lp, plus(argE(lp, L, a), a))(SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), v), RN.i1_at(~F, lp, plus(argE(lp, L, a), a), hwf)(v)), hn)) : {O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), v)), _) == SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), v), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), v))) : O.C(F)}
  rv_fsub(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), v), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), v))


# the difference at i is positive: i is below its bound at k1, and not at
# k2 (i < t, the smallest slack below its bound there)
def d_pos(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> LX.LPos(~F, SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), I(lp, plus(argE(lp, L, a), a))), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), I(lp, plus(argE(lp, L, a), a)))):
  %Equal.sym(O.C(F), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), I(lp, plus(argE(lp, L, a), a))), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), I(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), dl_at(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)), I(lp, plus(argE(lp, L, a), a)))) : LX.LPos(~F, _, SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), I(lp, plus(argE(lp, L, a), a))))
  %Equal.sym(O.C(F), SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), I(lp, plus(argE(lp, L, a), a))), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), I(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))), dl_at(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)), I(lp, plus(argE(lp, L, a), a)))) : LX.LPos(~F, O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), I(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), _)
  %FR.fring_eq(~F, [SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), I(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp))), O.ofz(~F, S.Z.neg(RN.Ineq.b(RN.qat(SX.LP.qs(lp), I(lp, plus(argE(lp, L, a), a))))))], E.ZSub{E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, E.ZSub{E.ZVar{1n}, E.ZVar{2n}}}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, {==}) : LX.LPos(~F, _, O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), I(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp)))))
  %FR.fring_eq(~F, [SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), I(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp))), O.ofz(~F, SX.ind(RN.Ineq.s(RN.qat(SX.LP.qs(lp), I(lp, plus(argE(lp, L, a), a))))))], E.ZSub{E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, E.ZSub{E.ZVar{1n}, E.ZVar{2n}}}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, {==}) : LX.LPos(~F, O.sub(~F, O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), I(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp))), O.ofz(~F, S.Z.neg(RN.Ineq.b(RN.qat(SX.LP.qs(lp), I(lp, plus(argE(lp, L, a), a))))))), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp))), O.ofz(~F, S.Z.neg(RN.Ineq.b(RN.qat(SX.LP.qs(lp), I(lp, plus(argE(lp, L, a), a)))))))), _)
  LX.lpos_sub(~F, O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), I(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp))), O.ofz(~F, S.Z.neg(RN.Ineq.b(RN.qat(SX.LP.qs(lp), I(lp, plus(argE(lp, L, a), a))))))), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), I(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp))), O.ofz(~F, SX.ind(RN.Ineq.s(RN.qat(SX.LP.qs(lp), I(lp, plus(argE(lp, L, a), a))))))), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp))), O.ofz(~F, S.Z.neg(RN.Ineq.b(RN.qat(SX.LP.qs(lp), I(lp, plus(argE(lp, L, a), a))))))), O.sub(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp))), O.ofz(~F, SX.ind(RN.Ineq.s(RN.qat(SX.LP.qs(lp), I(lp, plus(argE(lp, L, a), a))))))),
    RN.noviol_f(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), I(lp, plus(argE(lp, L, a), a))), SX.LP.v0(lp), SX.LP.v1(lp), RN.qat(SX.LP.qs(lp), I(lp, plus(argE(lp, L, a), a))), RN.lv_min(lp, RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a)), RN.piv_step(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a), go_at(lp, L, a, fl(lp, maxE(lp, L, a), 1n+L, a), hd2(~F, lp, L, a, hwf, hG, heq), hG)), RN.hr_at(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a)), I(lp, plus(argE(lp, L, a), a)), (%Equal.sym(Nat, I(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a)), maxE(lp, L, a), ik2(~F, lp, L, a, hwf, hG, heq)) : {SX.ltn(I(lp, plus(argE(lp, L, a), a)), _) == True{} : Bool}
      is_lt_t(~F, lp, L, a, hwf, hG, heq)))),
    RN.viol_f(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), SX.LP.v0(lp), SX.LP.v1(lp), RN.qat(SX.LP.qs(lp), I(lp, plus(argE(lp, L, a), a))), RN.lv_viol(lp, RN.tab(lp, plus(argE(lp, L, a), a)), RN.piv_step(lp, plus(argE(lp, L, a), a), go_at(lp, L, a, argE(lp, L, a), hd1(lp, L, a), hG)), RN.hr_at(lp, plus(argE(lp, L, a), a)))))

# Bland: the cycle is impossible
def bland_main(~F: O.OField, +lp: SX.LP, +L: Nat, +a: Nat, +hwf: {SP.lpwf(lp) == True{} : Bool}, +hG: {RN.isgo(RN.st(lp, plus(1n+L, a))) == True{} : Bool}, +heq: {B(lp, a) == B(lp, plus(1n+L, a)) : List<&2, Bool>}) -> Empty:
  LX.lpos_lneg(~F, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp))))), SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp))))),
    (%rowid(~F, lp, L, a, hwf, hG, heq, RN.zv(~F, SX.LP.v0(lp))) : LX.LPos(~F, _, SP.rv(~F, SX.rowat(SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), I(lp, plus(argE(lp, L, a), a))), fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v1(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v1(lp))))))
     %rowid(~F, lp, L, a, hwf, hG, heq, RN.zv(~F, SX.LP.v1(lp))) : LX.LPos(~F, SP.fat(~F, fsub(~F, SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(fl(lp, maxE(lp, L, a), 1n+L, a), a))), RN.zv(~F, SX.LP.v0(lp))), SP.rmap(~F, SX.Tab.rows(RN.tab(lp, plus(argE(lp, L, a), a))), RN.zv(~F, SX.LP.v0(lp)))), I(lp, plus(argE(lp, L, a), a))), _)
     d_pos(~F, lp, L, a, hwf, hG, heq)),
    row_neg(~F, lp, L, a, hwf, hG, heq))
