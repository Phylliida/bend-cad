# bend-cad: runtime dyadics with word mantissas (rt/wdyad.bend) are the
# spec's S.D exactly. WD.ofd and WD.tod convert (tod_ofd), and each
# operation on converted inputs is the conversion of S.D's result:
# add_ok, mul_ok, neg_ok, and cmp_ok (KI.dcmp). Every law holds for every
# S.D input and every base 2^(1 + lp): the word results are canonical
# with the right value, so they are the conversion (lib/wintpf.bend:
# ofz_of_val).

# Generated from tools/drafts/wdyadpf.draft by tools/expand.py; edit the
# draft.

import Base
import ./nat.bend as N
import ./natring.bend as NR
import ./natord.bend as O
import ./big.bend as LB
import ./z.bend as LZ
import ./zord.bend as ZO
import ./zring.bend as R
import ./dyadic.bend as LD
import ./kinst.bend as KI
import ./wmagpf.bend as WM
import ./wintpf.bend as WI
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/big.bend as SB
import ../spec/mat.bend as M
import ../rt/big.bend as RB
import ../rt/wmag.bend as RW
import ../rt/wint.bend as RI
import ../rt/wdyad.bend as RD


# Helpers
# -------

def BoolD(b: Bool) -> Type:
  match b:
    case True{}:
      Empty
    case False{}:
      Unit

def ft(e: {False{} == True{} : Bool}) -> Empty:
  %e : BoolD(_)
  Unit{}

def le_t(c: Cmp, +a: Nat, +b: Nat, e: {c == Nat.cmp(a, b) : Cmp}, h: {RD.le.go(c) == True{} : Bool}) -> SB.Le(a, b):
  match c:
    case LT{}:
      O.le_weaken(a, b, O.cmp_lt(a, b, e))
    case EQ{}:
      WM.le_of_eq(a, b, NR.nat_cmp_eq(a, b, e))
    case GT{}:
      WM.absurd(SB.Le(a, b), ft(h))

def le_f(c: Cmp, +a: Nat, +b: Nat, e: {c == Nat.cmp(a, b) : Cmp}, h: {RD.le.go(c) == False{} : Bool}) -> SB.Le(1n+b, a):
  match c:
    case LT{}:
      WM.absurd(SB.Le(1n+b, a), ft(Equal.sym(Bool, True{}, False{}, h)))
    case EQ{}:
      WM.absurd(SB.Le(1n+b, a), ft(Equal.sym(Bool, True{}, False{}, h)))
    case GT{}:
      O.cmp_gt(a, b, e)

# le(a, b) = True gives a <= b
def le_true(+a: Nat, +b: Nat, h: {RD.le(a, b) == True{} : Bool}) -> SB.Le(a, b):
  le_t(Nat.cmp(a, b), a, b, {==}, h)

# le(a, b) = False gives b < a
def le_false(+a: Nat, +b: Nat, h: {RD.le(a, b) == False{} : Bool}) -> SB.Le(1n+b, a):
  le_f(Nat.cmp(a, b), a, b, {==}, h)

# (a + k) - a = k
def sub_add_l(a: Nat, +k: Nat) -> {Nat.sub(Nat.add(a, k), a) == k : Nat}:
  match a:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n+j:
          {==}
    case 1n+i:
      sub_add_l(i, k)

def canon_wf(+bp: Nat, x: SB.Big, cx: WI.Canon(bp, x)) -> SB.Big.wf(bp, x):
  match x:
    case SB.BPos{m}:
      (w, t) = cx
      w
    case SB.BNeg{m}:
      (w, t) = cx
      w

def ofz_wf(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +z: S.Z) -> SB.Big.wf(bp, RI.Big.ofz(lp, z)):
  canon_wf(bp, RI.Big.ofz(lp, z), WI.ofz_canon(bp, lp, hb, z))

# a canonical x with value z is Big.ofz(z)
def is_ofz(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +x: SB.Big, +z: S.Z, cx: WI.Canon(bp, x), e: {SB.Big.val(bp, x) == z : S.Z}) -> {x == RI.Big.ofz(lp, z) : SB.Big}:
  %e : {x == RI.Big.ofz(lp, _) : SB.Big}
  Equal.sym(SB.Big, RI.Big.ofz(lp, SB.Big.val(bp, x)), x, WI.ofz_of_val(bp, lp, hb, x, cx))

# Big.canon(y), for a well-formed y with value z, is Big.ofz(z)
def canon_is(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +y: SB.Big, +z: S.Z, wy: SB.Big.wf(bp, y), e: {SB.Big.val(bp, y) == z : S.Z}) -> {RI.Big.canon(y) == RI.Big.ofz(lp, z) : SB.Big}:
  is_ofz(bp, lp, hb, RI.Big.canon(y), z, WI.canon_ok(bp, y, wy), Equal.trans(S.Z, SB.Big.val(bp, RI.Big.canon(y)), SB.Big.val(bp, y), z, WI.canon_val(bp, y), e))

def wd_eq(-m1: SB.Big, -m2: SB.Big, -e: Nat, h: {m1 == m2 : SB.Big}) -> {RD.WD{m1, e} == RD.WD{m2, e} : RD.WD}:
  %h : {RD.WD{m1, e} == RD.WD{_, e} : RD.WD}
  {==}

def d_eq(-z1: S.Z, -z2: S.Z, -e: Nat, h: {z1 == z2 : S.Z}) -> {S.D{z1, e} == S.D{z2, e} : S.D}:
  %h : {S.D{z1, e} == S.D{_, e} : S.D}
  {==}

# Conversions
# -----------

# WD.tod takes WD.ofd back
def tod_ofd(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, x: S.D) -> {RD.WD.tod(lp, RD.WD.ofd(lp, x)) == x : S.D}:
  match x:
    case S.D{+m, e}:
      %Equal.sym(S.Z, RI.Big.toz(lp, RI.Big.ofz(lp, m)), m, WI.toz_ofz(bp, lp, hb, m)) : {S.D{_, e} == S.D{m, e} : S.D}
      {==}

# Products and negation
# ---------------------


def mul_val(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m1: S.Z, +m2: S.Z) -> {SB.Big.val(bp, RB.Big.mul(bp, RI.Big.ofz(lp, m1), RI.Big.ofz(lp, m2))) == S.Z.mul(m1, m2) : S.Z}:
  %WI.ofz_val(bp, lp, hb, m1) : {SB.Big.val(bp, RB.Big.mul(bp, RI.Big.ofz(lp, m1), RI.Big.ofz(lp, m2))) == S.Z.mul(_, m2) : S.Z}
  %WI.ofz_val(bp, lp, hb, m2) : {SB.Big.val(bp, RB.Big.mul(bp, RI.Big.ofz(lp, m1), RI.Big.ofz(lp, m2))) == S.Z.mul(SB.Big.val(bp, RI.Big.ofz(lp, m1)), _) : S.Z}
  LB.mul_ok(bp, RI.Big.ofz(lp, m1), RI.Big.ofz(lp, m2))

def mul_ok(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, a: S.D, b: S.D) -> {RD.WD.mul(bp, RD.WD.ofd(lp, a), RD.WD.ofd(lp, b)) == RD.WD.ofd(lp, S.D.mul(a, b)) : RD.WD}:
  match a b:
    case S.D{+m1, +e1} S.D{+m2, +e2}:
      wd_eq(RI.Big.canon(RB.Big.mul(bp, RI.Big.ofz(lp, m1), RI.Big.ofz(lp, m2))), RI.Big.ofz(lp, S.Z.mul(m1, m2)), Nat.add(e1, e2),
        canon_is(bp, lp, hb, RB.Big.mul(bp, RI.Big.ofz(lp, m1), RI.Big.ofz(lp, m2)), S.Z.mul(m1, m2), LB.mul_wf(bp, RI.Big.ofz(lp, m1), RI.Big.ofz(lp, m2), WM.bp_pos(bp, lp, hb), ofz_wf(bp, lp, hb, m1), ofz_wf(bp, lp, hb, m2)), mul_val(bp, lp, hb, m1, m2)))

def neg_val(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m1: S.Z) -> {SB.Big.val(bp, RB.Big.neg(RI.Big.ofz(lp, m1))) == S.Z.neg(m1) : S.Z}:
  %WI.ofz_val(bp, lp, hb, m1) : {SB.Big.val(bp, RB.Big.neg(RI.Big.ofz(lp, m1))) == S.Z.neg(_) : S.Z}
  LB.neg_ok(bp, RI.Big.ofz(lp, m1))

def neg_ok(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, a: S.D) -> {RD.WD.neg(RD.WD.ofd(lp, a)) == RD.WD.ofd(lp, S.D.neg(a)) : RD.WD}:
  match a:
    case S.D{+m1, +e1}:
      wd_eq(RI.Big.canon(RB.Big.neg(RI.Big.ofz(lp, m1))), RI.Big.ofz(lp, S.Z.neg(m1)), e1,
        canon_is(bp, lp, hb, RB.Big.neg(RI.Big.ofz(lp, m1)), S.Z.neg(m1), LB.neg_wf(bp, RI.Big.ofz(lp, m1), ofz_wf(bp, lp, hb, m1)), neg_val(bp, lp, hb, m1)))

# Sums
# ----


# S.D.add with the larger exponent second: the first mantissa shifted up
def dadd_le(e1: Nat, +k: Nat, +m1: S.Z, +m2: S.Z) -> {S.D.add.go(e1, Nat.add(e1, k), m1, m2) == S.D{S.Z.add(S.Z.mul(m1, S.Zpos{S.Pos.pow2(k)}), m2), Nat.add(e1, k)} : S.D}:
  match e1:
    case 0n:
      match k:
        case 0n:
          d_eq(S.Z.add(m1, m2), S.Z.add(S.Z.mul(m1, S.Zpos{S.XH{}}), m2), 0n, R.ring_eq([m1, m2], E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{1n}}, {==}))
        case 1n+j:
          {==}
    case 1n++i:
      %Equal.sym(S.D, S.D.add.go(i, Nat.add(i, k), m1, m2), S.D{S.Z.add(S.Z.mul(m1, S.Zpos{S.Pos.pow2(k)}), m2), Nat.add(i, k)}, dadd_le(i, k, m1, m2)) : {S.D.inc(_) == S.D{S.Z.add(S.Z.mul(m1, S.Zpos{S.Pos.pow2(k)}), m2), Nat.add(1n+i, k)} : S.D}
      {==}

# and the larger first: the second shifted up
def dadd_ge(e2: Nat, +k: Nat, +m1: S.Z, +m2: S.Z) -> {S.D.add.go(Nat.add(e2, k), e2, m1, m2) == S.D{S.Z.add(m1, S.Z.mul(m2, S.Zpos{S.Pos.pow2(k)})), Nat.add(e2, k)} : S.D}:
  match e2:
    case 0n:
      match k:
        case 0n:
          d_eq(S.Z.add(m1, m2), S.Z.add(m1, S.Z.mul(m2, S.Zpos{S.XH{}})), 0n, R.ring_eq([m1, m2], E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}))
        case 1n+j:
          {==}
    case 1n++i:
      %Equal.sym(S.D, S.D.add.go(Nat.add(i, k), i, m1, m2), S.D{S.Z.add(m1, S.Z.mul(m2, S.Zpos{S.Pos.pow2(k)})), Nat.add(i, k)}, dadd_ge(i, k, m1, m2)) : {S.D.inc(_) == S.D{S.Z.add(m1, S.Z.mul(m2, S.Zpos{S.Pos.pow2(k)})), Nat.add(1n+i, k)} : S.D}
      {==}


def addl_val(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m1: S.Z, +m2: S.Z, +k: Nat) -> {SB.Big.val(bp, RB.Big.add(bp, RI.Big.shl(bp, lp, RI.Big.ofz(lp, m1), k), RI.Big.ofz(lp, m2))) == S.Z.add(S.Z.mul(m1, S.Zpos{S.Pos.pow2(k)}), m2) : S.Z}:
  %WI.ofz_val(bp, lp, hb, m1) : {SB.Big.val(bp, RB.Big.add(bp, RI.Big.shl(bp, lp, RI.Big.ofz(lp, m1), k), RI.Big.ofz(lp, m2))) == S.Z.add(S.Z.mul(_, S.Zpos{S.Pos.pow2(k)}), m2) : S.Z}
  %WI.ofz_val(bp, lp, hb, m2) : {SB.Big.val(bp, RB.Big.add(bp, RI.Big.shl(bp, lp, RI.Big.ofz(lp, m1), k), RI.Big.ofz(lp, m2))) == S.Z.add(S.Z.mul(SB.Big.val(bp, RI.Big.ofz(lp, m1)), S.Zpos{S.Pos.pow2(k)}), _) : S.Z}
  %WI.shl_zval(bp, lp, hb, RI.Big.ofz(lp, m1), k) : {SB.Big.val(bp, RB.Big.add(bp, RI.Big.shl(bp, lp, RI.Big.ofz(lp, m1), k), RI.Big.ofz(lp, m2))) == S.Z.add(_, SB.Big.val(bp, RI.Big.ofz(lp, m2))) : S.Z}
  LB.add_ok(bp, RI.Big.shl(bp, lp, RI.Big.ofz(lp, m1), k), RI.Big.ofz(lp, m2), WI.shl_wf(bp, lp, hb, RI.Big.ofz(lp, m1), k, ofz_wf(bp, lp, hb, m1)), ofz_wf(bp, lp, hb, m2))

def addg_val(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m1: S.Z, +m2: S.Z, +k: Nat) -> {SB.Big.val(bp, RB.Big.add(bp, RI.Big.ofz(lp, m1), RI.Big.shl(bp, lp, RI.Big.ofz(lp, m2), k))) == S.Z.add(m1, S.Z.mul(m2, S.Zpos{S.Pos.pow2(k)})) : S.Z}:
  %WI.ofz_val(bp, lp, hb, m1) : {SB.Big.val(bp, RB.Big.add(bp, RI.Big.ofz(lp, m1), RI.Big.shl(bp, lp, RI.Big.ofz(lp, m2), k))) == S.Z.add(_, S.Z.mul(m2, S.Zpos{S.Pos.pow2(k)})) : S.Z}
  %WI.ofz_val(bp, lp, hb, m2) : {SB.Big.val(bp, RB.Big.add(bp, RI.Big.ofz(lp, m1), RI.Big.shl(bp, lp, RI.Big.ofz(lp, m2), k))) == S.Z.add(SB.Big.val(bp, RI.Big.ofz(lp, m1)), S.Z.mul(_, S.Zpos{S.Pos.pow2(k)})) : S.Z}
  %WI.shl_zval(bp, lp, hb, RI.Big.ofz(lp, m2), k) : {SB.Big.val(bp, RB.Big.add(bp, RI.Big.ofz(lp, m1), RI.Big.shl(bp, lp, RI.Big.ofz(lp, m2), k))) == S.Z.add(SB.Big.val(bp, RI.Big.ofz(lp, m1)), _) : S.Z}
  LB.add_ok(bp, RI.Big.ofz(lp, m1), RI.Big.shl(bp, lp, RI.Big.ofz(lp, m2), k), ofz_wf(bp, lp, hb, m1), WI.shl_wf(bp, lp, hb, RI.Big.ofz(lp, m2), k, ofz_wf(bp, lp, hb, m2)))


# the exponents e1 <= e2 = e1 + k
def add_le(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m1: S.Z, +e1: Nat, +m2: S.Z, +e2: Nat, +k: Nat, ek: {Nat.add(e1, k) == e2 : Nat}) -> {RD.WD.add.go(True{}, bp, lp, RD.WD{RI.Big.ofz(lp, m1), e1}, RD.WD{RI.Big.ofz(lp, m2), e2}) == RD.WD.ofd(lp, S.D.add.go(e1, e2, m1, m2)) : RD.WD}:
  %ek : {RD.WD.add.go(True{}, bp, lp, RD.WD{RI.Big.ofz(lp, m1), e1}, RD.WD{RI.Big.ofz(lp, m2), _}) == RD.WD.ofd(lp, S.D.add.go(e1, _, m1, m2)) : RD.WD}
  %Equal.sym(S.D, S.D.add.go(e1, Nat.add(e1, k), m1, m2), S.D{S.Z.add(S.Z.mul(m1, S.Zpos{S.Pos.pow2(k)}), m2), Nat.add(e1, k)}, dadd_le(e1, k, m1, m2)) : {RD.WD.add.go(True{}, bp, lp, RD.WD{RI.Big.ofz(lp, m1), e1}, RD.WD{RI.Big.ofz(lp, m2), Nat.add(e1, k)}) == RD.WD.ofd(lp, _) : RD.WD}
  %Equal.sym(Nat, Nat.sub(Nat.add(e1, k), e1), k, sub_add_l(e1, k)) : {RD.WD{RI.Big.canon(RB.Big.add(bp, RI.Big.shl(bp, lp, RI.Big.ofz(lp, m1), _), RI.Big.ofz(lp, m2))), Nat.add(e1, k)} == RD.WD{RI.Big.ofz(lp, S.Z.add(S.Z.mul(m1, S.Zpos{S.Pos.pow2(k)}), m2)), Nat.add(e1, k)} : RD.WD}
  wd_eq(RI.Big.canon(RB.Big.add(bp, RI.Big.shl(bp, lp, RI.Big.ofz(lp, m1), k), RI.Big.ofz(lp, m2))), RI.Big.ofz(lp, S.Z.add(S.Z.mul(m1, S.Zpos{S.Pos.pow2(k)}), m2)), Nat.add(e1, k),
    canon_is(bp, lp, hb, RB.Big.add(bp, RI.Big.shl(bp, lp, RI.Big.ofz(lp, m1), k), RI.Big.ofz(lp, m2)), S.Z.add(S.Z.mul(m1, S.Zpos{S.Pos.pow2(k)}), m2), LB.add_wf(bp, RI.Big.shl(bp, lp, RI.Big.ofz(lp, m1), k), RI.Big.ofz(lp, m2), WM.bp_pos(bp, lp, hb), WI.shl_wf(bp, lp, hb, RI.Big.ofz(lp, m1), k, ofz_wf(bp, lp, hb, m1)), ofz_wf(bp, lp, hb, m2)), addl_val(bp, lp, hb, m1, m2, k)))

# the exponents e1 = e2 + k > e2
def add_ge(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m1: S.Z, +e1: Nat, +m2: S.Z, +e2: Nat, +k: Nat, ek: {Nat.add(e2, k) == e1 : Nat}) -> {RD.WD.add.go(False{}, bp, lp, RD.WD{RI.Big.ofz(lp, m1), e1}, RD.WD{RI.Big.ofz(lp, m2), e2}) == RD.WD.ofd(lp, S.D.add.go(e1, e2, m1, m2)) : RD.WD}:
  %ek : {RD.WD.add.go(False{}, bp, lp, RD.WD{RI.Big.ofz(lp, m1), _}, RD.WD{RI.Big.ofz(lp, m2), e2}) == RD.WD.ofd(lp, S.D.add.go(_, e2, m1, m2)) : RD.WD}
  %Equal.sym(S.D, S.D.add.go(Nat.add(e2, k), e2, m1, m2), S.D{S.Z.add(m1, S.Z.mul(m2, S.Zpos{S.Pos.pow2(k)})), Nat.add(e2, k)}, dadd_ge(e2, k, m1, m2)) : {RD.WD.add.go(False{}, bp, lp, RD.WD{RI.Big.ofz(lp, m1), Nat.add(e2, k)}, RD.WD{RI.Big.ofz(lp, m2), e2}) == RD.WD.ofd(lp, _) : RD.WD}
  %Equal.sym(Nat, Nat.sub(Nat.add(e2, k), e2), k, sub_add_l(e2, k)) : {RD.WD{RI.Big.canon(RB.Big.add(bp, RI.Big.ofz(lp, m1), RI.Big.shl(bp, lp, RI.Big.ofz(lp, m2), _))), Nat.add(e2, k)} == RD.WD{RI.Big.ofz(lp, S.Z.add(m1, S.Z.mul(m2, S.Zpos{S.Pos.pow2(k)}))), Nat.add(e2, k)} : RD.WD}
  wd_eq(RI.Big.canon(RB.Big.add(bp, RI.Big.ofz(lp, m1), RI.Big.shl(bp, lp, RI.Big.ofz(lp, m2), k))), RI.Big.ofz(lp, S.Z.add(m1, S.Z.mul(m2, S.Zpos{S.Pos.pow2(k)}))), Nat.add(e2, k),
    canon_is(bp, lp, hb, RB.Big.add(bp, RI.Big.ofz(lp, m1), RI.Big.shl(bp, lp, RI.Big.ofz(lp, m2), k)), S.Z.add(m1, S.Z.mul(m2, S.Zpos{S.Pos.pow2(k)})), LB.add_wf(bp, RI.Big.ofz(lp, m1), RI.Big.shl(bp, lp, RI.Big.ofz(lp, m2), k), WM.bp_pos(bp, lp, hb), ofz_wf(bp, lp, hb, m1), WI.shl_wf(bp, lp, hb, RI.Big.ofz(lp, m2), k, ofz_wf(bp, lp, hb, m2))), addg_val(bp, lp, hb, m1, m2, k)))

def add_le.c(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m1: S.Z, +e1: Nat, +m2: S.Z, +e2: Nat, h: SB.Le(e1, e2)) -> {RD.WD.add.go(True{}, bp, lp, RD.WD{RI.Big.ofz(lp, m1), e1}, RD.WD{RI.Big.ofz(lp, m2), e2}) == RD.WD.ofd(lp, S.D.add.go(e1, e2, m1, m2)) : RD.WD}:
  (+k, ek) = h
  add_le(bp, lp, hb, m1, e1, m2, e2, k, ek)

def add_ge.c(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m1: S.Z, +e1: Nat, +m2: S.Z, +e2: Nat, h: SB.Le(e2, e1)) -> {RD.WD.add.go(False{}, bp, lp, RD.WD{RI.Big.ofz(lp, m1), e1}, RD.WD{RI.Big.ofz(lp, m2), e2}) == RD.WD.ofd(lp, S.D.add.go(e1, e2, m1, m2)) : RD.WD}:
  (+k, ek) = h
  add_ge(bp, lp, hb, m1, e1, m2, e2, k, ek)

def add_go_ok(c: Bool, +bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m1: S.Z, +e1: Nat, +m2: S.Z, +e2: Nat, hc: {RD.le(e1, e2) == c : Bool}) -> {RD.WD.add.go(c, bp, lp, RD.WD{RI.Big.ofz(lp, m1), e1}, RD.WD{RI.Big.ofz(lp, m2), e2}) == RD.WD.ofd(lp, S.D.add.go(e1, e2, m1, m2)) : RD.WD}:
  match c:
    case True{}:
      add_le.c(bp, lp, hb, m1, e1, m2, e2, le_true(e1, e2, hc))
    case False{}:
      add_ge.c(bp, lp, hb, m1, e1, m2, e2, O.le_weaken(e2, e1, le_false(e1, e2, hc)))

def add_ok(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, a: S.D, b: S.D) -> {RD.WD.add(bp, lp, RD.WD.ofd(lp, a), RD.WD.ofd(lp, b)) == RD.WD.ofd(lp, S.D.add(a, b)) : RD.WD}:
  match a b:
    case S.D{+m1, +e1} S.D{+m2, +e2}:
      add_go_ok(RD.le(e1, e2), bp, lp, hb, m1, e1, m2, e2, {==})

# Comparison
# ----------

# a sign is kept by a positive factor
def zcmp0_scale(s: S.Z, -p: S.Pos) -> {S.Z.cmp(S.Z0{}, S.Z.mul(s, S.Zpos{p})) == S.Z.cmp(S.Z0{}, s) : Cmp}:
  match s:
    case S.Z0{}:
      {==}
    case S.Zpos{q}:
      {==}
    case S.Zneg{q}:
      {==}

# and so is an order
def zcmp_scale(+x: S.Z, +y: S.Z, +p: S.Pos) -> {S.Z.cmp(S.Z.mul(x, S.Zpos{p}), S.Z.mul(y, S.Zpos{p})) == S.Z.cmp(x, y) : Cmp}:
  %Equal.sym(Cmp, S.Z.cmp(S.Z.mul(x, S.Zpos{p}), S.Z.mul(y, S.Zpos{p})), S.Z.cmp(S.Z0{}, S.Z.sub(S.Z.mul(y, S.Zpos{p}), S.Z.mul(x, S.Zpos{p}))), ZO.cmp_sub(S.Z.mul(x, S.Zpos{p}), S.Z.mul(y, S.Zpos{p}))) : {_ == S.Z.cmp(x, y) : Cmp}
  %Equal.sym(Cmp, S.Z.cmp(x, y), S.Z.cmp(S.Z0{}, S.Z.sub(y, x)), ZO.cmp_sub(x, y)) : {S.Z.cmp(S.Z0{}, S.Z.sub(S.Z.mul(y, S.Zpos{p}), S.Z.mul(x, S.Zpos{p}))) == _ : Cmp}
  %R.ring_eq([x, y, S.Zpos{p}], E.ZMul{E.ZSub{E.ZVar{1n}, E.ZVar{0n}}, E.ZVar{2n}}, E.ZSub{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, {==}) : {S.Z.cmp(S.Z0{}, _) == S.Z.cmp(S.Z0{}, S.Z.sub(y, x)) : Cmp}
  zcmp0_scale(S.Z.sub(y, x), p)


def cmpl_val(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m1: S.Z, +m2: S.Z, +k: Nat) -> {RB.Big.cmp(bp, RI.Big.shl(bp, lp, RI.Big.ofz(lp, m1), k), RI.Big.ofz(lp, m2)) == S.Z.cmp(S.Z.mul(m1, S.Zpos{S.Pos.pow2(k)}), m2) : Cmp}:
  %WI.ofz_val(bp, lp, hb, m1) : {RB.Big.cmp(bp, RI.Big.shl(bp, lp, RI.Big.ofz(lp, m1), k), RI.Big.ofz(lp, m2)) == S.Z.cmp(S.Z.mul(_, S.Zpos{S.Pos.pow2(k)}), m2) : Cmp}
  %WI.ofz_val(bp, lp, hb, m2) : {RB.Big.cmp(bp, RI.Big.shl(bp, lp, RI.Big.ofz(lp, m1), k), RI.Big.ofz(lp, m2)) == S.Z.cmp(S.Z.mul(SB.Big.val(bp, RI.Big.ofz(lp, m1)), S.Zpos{S.Pos.pow2(k)}), _) : Cmp}
  %WI.shl_zval(bp, lp, hb, RI.Big.ofz(lp, m1), k) : {RB.Big.cmp(bp, RI.Big.shl(bp, lp, RI.Big.ofz(lp, m1), k), RI.Big.ofz(lp, m2)) == S.Z.cmp(_, SB.Big.val(bp, RI.Big.ofz(lp, m2))) : Cmp}
  LB.cmp_ok(bp, RI.Big.shl(bp, lp, RI.Big.ofz(lp, m1), k), RI.Big.ofz(lp, m2), WM.bp_pos(bp, lp, hb), WI.shl_wf(bp, lp, hb, RI.Big.ofz(lp, m1), k, ofz_wf(bp, lp, hb, m1)), ofz_wf(bp, lp, hb, m2))

def cmpg_val(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m1: S.Z, +m2: S.Z, +k: Nat) -> {RB.Big.cmp(bp, RI.Big.ofz(lp, m1), RI.Big.shl(bp, lp, RI.Big.ofz(lp, m2), k)) == S.Z.cmp(m1, S.Z.mul(m2, S.Zpos{S.Pos.pow2(k)})) : Cmp}:
  %WI.ofz_val(bp, lp, hb, m1) : {RB.Big.cmp(bp, RI.Big.ofz(lp, m1), RI.Big.shl(bp, lp, RI.Big.ofz(lp, m2), k)) == S.Z.cmp(_, S.Z.mul(m2, S.Zpos{S.Pos.pow2(k)})) : Cmp}
  %WI.ofz_val(bp, lp, hb, m2) : {RB.Big.cmp(bp, RI.Big.ofz(lp, m1), RI.Big.shl(bp, lp, RI.Big.ofz(lp, m2), k)) == S.Z.cmp(SB.Big.val(bp, RI.Big.ofz(lp, m1)), S.Z.mul(_, S.Zpos{S.Pos.pow2(k)})) : Cmp}
  %WI.shl_zval(bp, lp, hb, RI.Big.ofz(lp, m2), k) : {RB.Big.cmp(bp, RI.Big.ofz(lp, m1), RI.Big.shl(bp, lp, RI.Big.ofz(lp, m2), k)) == S.Z.cmp(SB.Big.val(bp, RI.Big.ofz(lp, m1)), _) : Cmp}
  LB.cmp_ok(bp, RI.Big.ofz(lp, m1), RI.Big.shl(bp, lp, RI.Big.ofz(lp, m2), k), WM.bp_pos(bp, lp, hb), ofz_wf(bp, lp, hb, m1), WI.shl_wf(bp, lp, hb, RI.Big.ofz(lp, m2), k, ofz_wf(bp, lp, hb, m2)))

# dcmp at e2 = e1 + k: m1 2^e2 against m2 2^e1 is m1 2^k against m2
def dcmp_le(+m1: S.Z, +e1: Nat, +m2: S.Z, +k: Nat) -> {S.Z.cmp(S.Z.mul(m1, S.Zpos{S.Pos.pow2(Nat.add(e1, k))}), S.Z.mul(m2, S.Zpos{S.Pos.pow2(e1)})) == S.Z.cmp(S.Z.mul(m1, S.Zpos{S.Pos.pow2(k)}), m2) : Cmp}:
  %LD.pow2_add(e1, k) : {S.Z.cmp(S.Z.mul(m1, S.Zpos{_}), S.Z.mul(m2, S.Zpos{S.Pos.pow2(e1)})) == S.Z.cmp(S.Z.mul(m1, S.Zpos{S.Pos.pow2(k)}), m2) : Cmp}
  %R.ring_eq([m1, S.Zpos{S.Pos.pow2(e1)}, S.Zpos{S.Pos.pow2(k)}], E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, {==}) : {S.Z.cmp(_, S.Z.mul(m2, S.Zpos{S.Pos.pow2(e1)})) == S.Z.cmp(S.Z.mul(m1, S.Zpos{S.Pos.pow2(k)}), m2) : Cmp}
  zcmp_scale(S.Z.mul(m1, S.Zpos{S.Pos.pow2(k)}), m2, S.Pos.pow2(e1))

def dcmp_ge(+m1: S.Z, +m2: S.Z, +e2: Nat, +k: Nat) -> {S.Z.cmp(S.Z.mul(m1, S.Zpos{S.Pos.pow2(e2)}), S.Z.mul(m2, S.Zpos{S.Pos.pow2(Nat.add(e2, k))})) == S.Z.cmp(m1, S.Z.mul(m2, S.Zpos{S.Pos.pow2(k)})) : Cmp}:
  %LD.pow2_add(e2, k) : {S.Z.cmp(S.Z.mul(m1, S.Zpos{S.Pos.pow2(e2)}), S.Z.mul(m2, S.Zpos{_})) == S.Z.cmp(m1, S.Z.mul(m2, S.Zpos{S.Pos.pow2(k)})) : Cmp}
  %R.ring_eq([m2, S.Zpos{S.Pos.pow2(e2)}, S.Zpos{S.Pos.pow2(k)}], E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, {==}) : {S.Z.cmp(S.Z.mul(m1, S.Zpos{S.Pos.pow2(e2)}), _) == S.Z.cmp(m1, S.Z.mul(m2, S.Zpos{S.Pos.pow2(k)})) : Cmp}
  zcmp_scale(m1, S.Z.mul(m2, S.Zpos{S.Pos.pow2(k)}), S.Pos.pow2(e2))


def cmp_le(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m1: S.Z, +e1: Nat, +m2: S.Z, +e2: Nat, +k: Nat, ek: {Nat.add(e1, k) == e2 : Nat}) -> {RD.WD.cmp.go(True{}, bp, lp, RD.WD{RI.Big.ofz(lp, m1), e1}, RD.WD{RI.Big.ofz(lp, m2), e2}) == KI.dcmp(S.D{m1, e1}, S.D{m2, e2}) : Cmp}:
  %ek : {RD.WD.cmp.go(True{}, bp, lp, RD.WD{RI.Big.ofz(lp, m1), e1}, RD.WD{RI.Big.ofz(lp, m2), _}) == S.Z.cmp(S.Z.mul(m1, S.Zpos{S.Pos.pow2(_)}), S.Z.mul(m2, S.Zpos{S.Pos.pow2(e1)})) : Cmp}
  %Equal.sym(Nat, Nat.sub(Nat.add(e1, k), e1), k, sub_add_l(e1, k)) : {RB.Big.cmp(bp, RI.Big.shl(bp, lp, RI.Big.ofz(lp, m1), _), RI.Big.ofz(lp, m2)) == S.Z.cmp(S.Z.mul(m1, S.Zpos{S.Pos.pow2(Nat.add(e1, k))}), S.Z.mul(m2, S.Zpos{S.Pos.pow2(e1)})) : Cmp}
  %Equal.sym(Cmp, S.Z.cmp(S.Z.mul(m1, S.Zpos{S.Pos.pow2(Nat.add(e1, k))}), S.Z.mul(m2, S.Zpos{S.Pos.pow2(e1)})), S.Z.cmp(S.Z.mul(m1, S.Zpos{S.Pos.pow2(k)}), m2), dcmp_le(m1, e1, m2, k)) : {RB.Big.cmp(bp, RI.Big.shl(bp, lp, RI.Big.ofz(lp, m1), k), RI.Big.ofz(lp, m2)) == _ : Cmp}
  cmpl_val(bp, lp, hb, m1, m2, k)

def cmp_ge(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m1: S.Z, +e1: Nat, +m2: S.Z, +e2: Nat, +k: Nat, ek: {Nat.add(e2, k) == e1 : Nat}) -> {RD.WD.cmp.go(False{}, bp, lp, RD.WD{RI.Big.ofz(lp, m1), e1}, RD.WD{RI.Big.ofz(lp, m2), e2}) == KI.dcmp(S.D{m1, e1}, S.D{m2, e2}) : Cmp}:
  %ek : {RD.WD.cmp.go(False{}, bp, lp, RD.WD{RI.Big.ofz(lp, m1), _}, RD.WD{RI.Big.ofz(lp, m2), e2}) == S.Z.cmp(S.Z.mul(m1, S.Zpos{S.Pos.pow2(e2)}), S.Z.mul(m2, S.Zpos{S.Pos.pow2(_)})) : Cmp}
  %Equal.sym(Nat, Nat.sub(Nat.add(e2, k), e2), k, sub_add_l(e2, k)) : {RB.Big.cmp(bp, RI.Big.ofz(lp, m1), RI.Big.shl(bp, lp, RI.Big.ofz(lp, m2), _)) == S.Z.cmp(S.Z.mul(m1, S.Zpos{S.Pos.pow2(e2)}), S.Z.mul(m2, S.Zpos{S.Pos.pow2(Nat.add(e2, k))})) : Cmp}
  %Equal.sym(Cmp, S.Z.cmp(S.Z.mul(m1, S.Zpos{S.Pos.pow2(e2)}), S.Z.mul(m2, S.Zpos{S.Pos.pow2(Nat.add(e2, k))})), S.Z.cmp(m1, S.Z.mul(m2, S.Zpos{S.Pos.pow2(k)})), dcmp_ge(m1, m2, e2, k)) : {RB.Big.cmp(bp, RI.Big.ofz(lp, m1), RI.Big.shl(bp, lp, RI.Big.ofz(lp, m2), k)) == _ : Cmp}
  cmpg_val(bp, lp, hb, m1, m2, k)

def cmp_le.c(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m1: S.Z, +e1: Nat, +m2: S.Z, +e2: Nat, h: SB.Le(e1, e2)) -> {RD.WD.cmp.go(True{}, bp, lp, RD.WD{RI.Big.ofz(lp, m1), e1}, RD.WD{RI.Big.ofz(lp, m2), e2}) == KI.dcmp(S.D{m1, e1}, S.D{m2, e2}) : Cmp}:
  (+k, ek) = h
  cmp_le(bp, lp, hb, m1, e1, m2, e2, k, ek)

def cmp_ge.c(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m1: S.Z, +e1: Nat, +m2: S.Z, +e2: Nat, h: SB.Le(e2, e1)) -> {RD.WD.cmp.go(False{}, bp, lp, RD.WD{RI.Big.ofz(lp, m1), e1}, RD.WD{RI.Big.ofz(lp, m2), e2}) == KI.dcmp(S.D{m1, e1}, S.D{m2, e2}) : Cmp}:
  (+k, ek) = h
  cmp_ge(bp, lp, hb, m1, e1, m2, e2, k, ek)

def cmp_go_ok(c: Bool, +bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m1: S.Z, +e1: Nat, +m2: S.Z, +e2: Nat, hc: {RD.le(e1, e2) == c : Bool}) -> {RD.WD.cmp.go(c, bp, lp, RD.WD{RI.Big.ofz(lp, m1), e1}, RD.WD{RI.Big.ofz(lp, m2), e2}) == KI.dcmp(S.D{m1, e1}, S.D{m2, e2}) : Cmp}:
  match c:
    case True{}:
      cmp_le.c(bp, lp, hb, m1, e1, m2, e2, le_true(e1, e2, hc))
    case False{}:
      cmp_ge.c(bp, lp, hb, m1, e1, m2, e2, O.le_weaken(e2, e1, le_false(e1, e2, hc)))

# the comparison of converted dyadics is KI.dcmp
def cmp_ok(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, a: S.D, b: S.D) -> {RD.WD.cmp(bp, lp, RD.WD.ofd(lp, a), RD.WD.ofd(lp, b)) == KI.dcmp(a, b) : Cmp}:
  match a b:
    case S.D{+m1, +e1} S.D{+m2, +e2}:
      cmp_go_ok(RD.le(e1, e2), bp, lp, hb, m1, e1, m2, e2, {==})
