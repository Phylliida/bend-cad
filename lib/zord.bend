# Order on the binary integers through signs: x < y exactly when y - x is
# positive (cmp_sub), and positivity is closed under + and * by computation
# (Zpos p + Zpos q is Zpos (p + q)). So an order fact becomes a ring identity
# (one normalizer call) plus a sign.

import Base
import ./nat.bend as N
import ./natring.bend as NR
import ./z.bend as LZ
import ./zlaws.bend as LZL
import ./zring.bend as R
import ../spec/num.bend as S
import ../spec/ring.bend as E

def absurd(-A: Type, x: Empty) -> A:
  match x:

# s is positive
def pos(s: S.Z) -> Data:
  match s:
    case S.Z0{}:
      Empty
    case S.Zpos{p}:
      Unit
    case S.Zneg{p}:
      Empty

# Comparison is the sign of the difference
# ----------------------------------------

# 0 vs a - b is b vs a
def od_cmp(m: Nat, n: Nat) -> {S.Z.cmp(S.Z0{}, S.Z.of_diff(m, n)) == Nat.cmp(n, m) : Cmp}:
  match m n:
    case 0n 0n:
      {==}
    case 1n+k 0n:
      {==}
    case 0n 1n+k:
      {==}
    case 1n+i 1n+j:
      od_cmp(i, j)

# b - a as the difference of parts
def sub_diff(+a: S.Z, b: S.Z) -> {S.Z.of_diff(Nat.add(S.Z.pnat(b), S.Z.nnat(a)), Nat.add(S.Z.nnat(b), S.Z.pnat(a))) == S.Z.sub(b, a) : S.Z}:
  match a:
    case S.Z0{}:
      LZ.add_diff(b, S.Z0{})
    case S.Zpos{p}:
      LZ.add_diff(b, S.Zneg{p})
    case S.Zneg{p}:
      LZ.add_diff(b, S.Zpos{p})

# a vs b is 0 vs b - a
def cmp_sub(+a: S.Z, +b: S.Z) -> {S.Z.cmp(a, b) == S.Z.cmp(S.Z0{}, S.Z.sub(b, a)) : Cmp}:
  %sub_diff(a, b) : {S.Z.cmp(a, b) == S.Z.cmp(S.Z0{}, _) : Cmp}
  %Equal.sym(Cmp, S.Z.cmp(S.Z0{}, S.Z.of_diff(Nat.add(S.Z.pnat(b), S.Z.nnat(a)), Nat.add(S.Z.nnat(b), S.Z.pnat(a)))), Nat.cmp(Nat.add(S.Z.nnat(b), S.Z.pnat(a)), Nat.add(S.Z.pnat(b), S.Z.nnat(a))), od_cmp(Nat.add(S.Z.pnat(b), S.Z.nnat(a)), Nat.add(S.Z.nnat(b), S.Z.pnat(a)))) : {S.Z.cmp(a, b) == _ : Cmp}
  %N.add_comm(S.Z.pnat(a), S.Z.nnat(b)) : {S.Z.cmp(a, b) == Nat.cmp(_, Nat.add(S.Z.pnat(b), S.Z.nnat(a))) : Cmp}
  LZ.cmp_nat(a, b)

# Signs from comparisons with 0
# -----------------------------

def cmp0_pos(s: S.Z, h: {S.Z.cmp(S.Z0{}, s) == LT{} : Cmp}) -> pos(s):
  match s:
    case S.Z0{}:
      %h : NR.CmpD(_, Empty, Unit, Unit)
      Unit{}
    case S.Zpos{p}:
      Unit{}
    case S.Zneg{p}:
      %h : NR.CmpD(_, Empty, Unit, Unit)
      Unit{}

def pos_cmp0(s: S.Z, h: pos(s)) -> {S.Z.cmp(S.Z0{}, s) == LT{} : Cmp}:
  match s:
    case S.Z0{}:
      absurd({S.Z.cmp(S.Z0{}, S.Z0{}) == LT{} : Cmp}, h)
    case S.Zpos{p}:
      {==}
    case S.Zneg{p}:
      absurd({S.Z.cmp(S.Z0{}, S.Zneg{p}) == LT{} : Cmp}, h)

def cmp0_zero(s: S.Z, h: {S.Z.cmp(S.Z0{}, s) == EQ{} : Cmp}) -> {s == S.Z0{} : S.Z}:
  match s:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      %h : NR.CmpD(_, Unit, {S.Zpos{p} == S.Z0{} : S.Z}, Unit)
      Unit{}
    case S.Zneg{p}:
      %h : NR.CmpD(_, Unit, {S.Zneg{p} == S.Z0{} : S.Z}, Unit)
      Unit{}

def cmp0_neg(s: S.Z, h: {S.Z.cmp(S.Z0{}, s) == GT{} : Cmp}) -> pos(S.Z.neg(s)):
  match s:
    case S.Z0{}:
      %h : NR.CmpD(_, Unit, Unit, Empty)
      Unit{}
    case S.Zpos{p}:
      %h : NR.CmpD(_, Unit, Unit, Empty)
      Unit{}
    case S.Zneg{p}:
      Unit{}

# a < b exactly when b - a is positive
def lt_pos(+a: S.Z, +b: S.Z, h: {S.Z.cmp(a, b) == LT{} : Cmp}) -> pos(S.Z.sub(b, a)):
  cmp0_pos(S.Z.sub(b, a), Equal.trans(Cmp, S.Z.cmp(S.Z0{}, S.Z.sub(b, a)), S.Z.cmp(a, b), LT{}, Equal.sym(Cmp, S.Z.cmp(a, b), S.Z.cmp(S.Z0{}, S.Z.sub(b, a)), cmp_sub(a, b)), h))

def pos_lt(+a: S.Z, +b: S.Z, h: pos(S.Z.sub(b, a))) -> {S.Z.cmp(a, b) == LT{} : Cmp}:
  Equal.trans(Cmp, S.Z.cmp(a, b), S.Z.cmp(S.Z0{}, S.Z.sub(b, a)), LT{}, cmp_sub(a, b), pos_cmp0(S.Z.sub(b, a), h))

# a = b when they compare EQ (b - a = 0)
def eq_zero(+a: S.Z, +b: S.Z, h: {S.Z.cmp(a, b) == EQ{} : Cmp}) -> {S.Z.sub(b, a) == S.Z0{} : S.Z}:
  cmp0_zero(S.Z.sub(b, a), Equal.trans(Cmp, S.Z.cmp(S.Z0{}, S.Z.sub(b, a)), S.Z.cmp(a, b), EQ{}, Equal.sym(Cmp, S.Z.cmp(a, b), S.Z.cmp(S.Z0{}, S.Z.sub(b, a)), cmp_sub(a, b)), h))

# b - a = 0 gives a = b
def sub_eq(+a: S.Z, +b: S.Z, h: {S.Z.sub(b, a) == S.Z0{} : S.Z}) -> {a == b : S.Z}:
  %R.ring_eq([a, b], E.ZAdd{E.ZVar{0n}, E.ZSub{E.ZVar{1n}, E.ZVar{0n}}}, E.ZVar{1n}, {==}) : {a == _ : S.Z}
  %Equal.sym(S.Z, S.Z.sub(b, a), S.Z0{}, h) : {a == S.Z.add(a, _) : S.Z}
  LZL.add_zero(a)

# a > b gives a positive -(b - a)
def gt_pos(+a: S.Z, +b: S.Z, h: {S.Z.cmp(a, b) == GT{} : Cmp}) -> pos(S.Z.neg(S.Z.sub(b, a))):
  cmp0_neg(S.Z.sub(b, a), Equal.trans(Cmp, S.Z.cmp(S.Z0{}, S.Z.sub(b, a)), S.Z.cmp(a, b), GT{}, Equal.sym(Cmp, S.Z.cmp(a, b), S.Z.cmp(S.Z0{}, S.Z.sub(b, a)), cmp_sub(a, b)), h))

# Positivity algebra
# ------------------

def pos_add(s: S.Z, t: S.Z, hs: pos(s), ht: pos(t)) -> pos(S.Z.add(s, t)):
  match s t:
    case S.Zpos{p} S.Zpos{q}:
      Unit{}
    case S.Z0{} t:
      absurd(pos(S.Z.add(S.Z0{}, t)), hs)
    case S.Zneg{p} t:
      absurd(pos(S.Z.add(S.Zneg{p}, t)), hs)
    case S.Zpos{p} S.Z0{}:
      absurd(pos(S.Zpos{p}), ht)
    case S.Zpos{p} S.Zneg{q}:
      absurd(pos(S.Z.pos_sub(p, q)), ht)

def pos_mul(s: S.Z, t: S.Z, hs: pos(s), ht: pos(t)) -> pos(S.Z.mul(s, t)):
  match s t:
    case S.Zpos{p} S.Zpos{q}:
      Unit{}
    case S.Z0{} t:
      absurd(pos(S.Z.mul(S.Z0{}, t)), hs)
    case S.Zneg{p} t:
      absurd(pos(S.Z.mul(S.Zneg{p}, t)), hs)
    case S.Zpos{p} S.Z0{}:
      absurd(pos(S.Z0{}), ht)
    case S.Zpos{p} S.Zneg{q}:
      absurd(pos(S.Zneg{S.Pos.mul(p, q)}), ht)

# p s positive, for a positive p, gives s positive
def pos_cancel(-p: S.Pos, s: S.Z, h: pos(S.Z.mul(S.Zpos{p}, s))) -> pos(s):
  match s:
    case S.Z0{}:
      absurd(pos(S.Z0{}), h)
    case S.Zpos{q}:
      Unit{}
    case S.Zneg{q}:
      absurd(pos(S.Zneg{q}), h)

# positivity moves along equalities
def pos_eq(+s: S.Z, +t: S.Z, e: {s == t : S.Z}, h: pos(t)) -> pos(s):
  %Equal.sym(S.Z, s, t, e) : pos(_)
  h

# 0 is not positive
def pos_zero(+s: S.Z, e: {s == S.Z0{} : S.Z}, h: pos(s)) -> Empty:
  pos_eq(S.Z0{}, s, Equal.sym(S.Z, s, S.Z0{}, e), h)
