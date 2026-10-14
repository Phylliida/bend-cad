# Order on Base's Nat, and Euclid's division (Nat.div / Nat.mod) by a base
# 1 + bp. The base stays a variable: a large literal such as 65536n would be
# unfolded to unary by the checker.
#
# SB.Le(a, b) is a <= b, witnessed by the gap k with a + k = b.

import Base
import ./nat.bend as N
import ./natring.bend as NR
import ../spec/big.bend as SB

def le_refl(+a: Nat) -> SB.Le(a, a):
  (0n, Equal.sym(Nat, a, Nat.add(a, 0n), N.add_zero(a)))

# Division
# --------
# Base's Nat.divmod(s, 1 + bp) runs Nat.divmod.go(s, bp, 0, 0): r counts up
# and m counts down, with r + m = bp throughout.

def dm_h0(+r: Nat, -bp: Nat, h: {Nat.add(r, 0n) == bp : Nat}) -> {r == bp : Nat}:
  %h : {r == _ : Nat}
  N.add_zero(r)

def dm_h1(+r: Nat, +mp: Nat, -bp: Nat, h: {Nat.add(r, 1n+mp) == bp : Nat}) -> {1n+Nat.add(r, mp) == bp : Nat}:
  %h : {1n+Nat.add(r, mp) == _ : Nat}
  N.add_succ(r, mp)

def dm_go(n: Nat, m: Nat, +d: Nat, +r: Nat, +bp: Nat, +h: {Nat.add(r, m) == bp : Nat})
  -> {Nat.add(Nat.add(r, Nat.mul(d, 1n+bp)), n) == Nat.add(Nat.mod.fin(Nat.divmod.go(n, m, d, r)), Nat.mul(Nat.div.fin(Nat.divmod.go(n, m, d, r)), 1n+bp)) : Nat}:
  match n:
    case 0n:
      %N.add_zero(Nat.add(r, Nat.mul(d, 1n+bp))) : {_ == Nat.add(r, Nat.mul(d, 1n+bp)) : Nat}
      {==}
    case 1n+np:
      match m:
        case 0n:
          %dm_go(np, r, 1n+d, 0n, bp, dm_h0(r, bp, h)) : {Nat.add(Nat.add(r, Nat.mul(d, 1n+bp)), 1n+np) == _ : Nat}
          %dm_h0(r, bp, h) : {Nat.add(Nat.add(r, Nat.mul(d, 1n+bp)), 1n+np) == 1n+Nat.add(Nat.add(_, Nat.mul(d, 1n+bp)), np) : Nat}
          %N.add_succ(Nat.add(r, Nat.mul(d, 1n+bp)), np) : {_ == 1n+Nat.add(Nat.add(r, Nat.mul(d, 1n+bp)), np) : Nat}
          {==}
        case 1n++mp:
          %dm_go(np, mp, d, 1n+r, bp, dm_h1(r, mp, bp, h)) : {Nat.add(Nat.add(r, Nat.mul(d, 1n+bp)), 1n+np) == _ : Nat}
          %N.add_succ(Nat.add(r, Nat.mul(d, 1n+bp)), np) : {_ == 1n+Nat.add(Nat.add(r, Nat.mul(d, 1n+bp)), np) : Nat}
          {==}

def dm_go_le(n: Nat, m: Nat, -d: Nat, +r: Nat, +bp: Nat, h: {Nat.add(r, m) == bp : Nat}) -> SB.Le(Nat.mod.fin(Nat.divmod.go(n, m, d, r)), bp):
  match n:
    case 0n:
      (m, h)
    case 1n+np:
      match m:
        case 0n:
          dm_go_le(np, r, 1n+d, 0n, bp, dm_h0(r, bp, h))
        case 1n++mp:
          dm_go_le(np, mp, d, 1n+r, bp, dm_h1(r, mp, bp, h))

# s = (s mod B) + (s div B) * B, for B = 1 + bp
def divmod_eq(+s: Nat, +bp: Nat) -> {s == Nat.add(Nat.mod(s, 1n+bp), Nat.mul(Nat.div(s, 1n+bp), 1n+bp)) : Nat}:
  dm_go(s, bp, 0n, 0n, bp, {==})

# s mod B <= bp
def mod_le(+s: Nat, +bp: Nat) -> SB.Le(Nat.mod(s, 1n+bp), bp):
  dm_go_le(s, bp, 0n, 0n, bp, {==})

# Order algebra
# -------------

# a <= a + b
def le_add(-a: Nat, +b: Nat) -> SB.Le(a, Nat.add(a, b)):
  (b, {==})

def le_trans.eq(+a: Nat, -b: Nat, -c: Nat, -k1: Nat, -k2: Nat, e1: {Nat.add(a, k1) == b : Nat}, e2: {Nat.add(b, k2) == c : Nat}) -> {Nat.add(a, Nat.add(k1, k2)) == c : Nat}:
  %e2 : {Nat.add(a, Nat.add(k1, k2)) == _ : Nat}
  %e1 : {Nat.add(a, Nat.add(k1, k2)) == Nat.add(_, k2) : Nat}
  N.add_assoc(a, k1, k2)

def le_trans(+a: Nat, -b: Nat, -c: Nat, h1: SB.Le(a, b), h2: SB.Le(b, c)) -> SB.Le(a, c):
  (k1, e1) = h1
  (k2, e2) = h2
  (Nat.add(k1, k2), le_trans.eq(a, b, c, k1, k2, e1, e2))

# a <= b gives 1 + a <= 1 + b, and back
def le_succ(-a: Nat, -b: Nat, h: SB.Le(a, b)) -> SB.Le(1n+a, 1n+b):
  (k, e) = h
  (k, Equal.cong(Nat, Nat, n => 1n+n, Nat.add(a, k), b, e))

def le_pred(-a: Nat, -b: Nat, h: SB.Le(1n+a, 1n+b)) -> SB.Le(a, b):
  (k, e) = h
  (k, Equal.cong(Nat, Nat, n => N.pred(n), 1n+Nat.add(a, k), 1n+b, e))

# x <= 0 gives x = 0
def le_zero(x: Nat, h: SB.Le(x, 0n)) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      (k, e) = h
      %e : N.NatD(_, {1n+p == 0n : Nat}, Unit)
      Unit{}

# 1 + a + z is never a
def gt_self(a: Nat, -z: Nat, e: {1n+Nat.add(a, z) == a : Nat}) -> Empty:
  match a:
    case 0n:
      %e : N.NatD(_, Empty, Unit)
      Unit{}
    case 1n+p:
      gt_self(p, z, Equal.cong(Nat, Nat, n => N.pred(n), 2n+Nat.add(p, z), 1n+p, e))

# Le(x*B, bp + m*B) gives Le(x, m), for B = 1 + bp
def lmc_wrap0(+bp: Nat, +i: Nat, +k: Nat, e: {Nat.add(Nat.mul(1n+i, 1n+bp), k) == Nat.add(bp, Nat.mul(0n, 1n+bp)) : Nat}) -> {1n+Nat.add(bp, Nat.add(Nat.mul(i, 1n+bp), k)) == Nat.add(bp, 0n) : Nat}:
  %NR.ring_eq([bp, i, k], NR.NAdd{NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NVar{1n}}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}, NR.NVar{2n}}, NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NVar{0n}, NR.NAdd{NR.NMul{NR.NVar{1n}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}, NR.NVar{2n}}}}, {==}) : {_ == Nat.add(bp, 0n) : Nat}
  e

def lmc_wrap(+bp: Nat, +i: Nat, +k: Nat, e: {Nat.add(Nat.mul(1n+i, 1n+bp), k) == Nat.add(bp, Nat.mul(0n, 1n+bp)) : Nat}) -> {1n+Nat.add(bp, Nat.add(Nat.mul(i, 1n+bp), k)) == bp : Nat}:
  Equal.trans(Nat, 1n+Nat.add(bp, Nat.add(Nat.mul(i, 1n+bp), k)), Nat.add(bp, 0n), bp, lmc_wrap0(bp, i, k, e), Equal.sym(Nat, bp, Nat.add(bp, 0n), N.add_zero(bp)))

def lmc_shift(+bp: Nat, +i: Nat, +j: Nat, +k: Nat, e: {Nat.add(Nat.mul(1n+i, 1n+bp), k) == Nat.add(bp, Nat.mul(1n+j, 1n+bp)) : Nat})
  -> {Nat.add(1n+bp, Nat.add(Nat.mul(i, 1n+bp), k)) == Nat.add(1n+bp, Nat.add(bp, Nat.mul(j, 1n+bp))) : Nat}:
  %NR.ring_eq([bp, i, k, j], NR.NAdd{NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NVar{1n}}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}, NR.NVar{2n}}, NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}, NR.NAdd{NR.NMul{NR.NVar{1n}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}, NR.NVar{2n}}}, {==}) : {_ == Nat.add(1n+bp, Nat.add(bp, Nat.mul(j, 1n+bp))) : Nat}
  %NR.ring_eq([bp, i, k, j], NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NVar{3n}}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}}, NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}, NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{3n}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}}}, {==}) : {Nat.add(Nat.mul(1n+i, 1n+bp), k) == _ : Nat}
  e

def le_mul_cancel(x: Nat, m: Nat, +bp: Nat, h: SB.Le(Nat.mul(x, 1n+bp), Nat.add(bp, Nat.mul(m, 1n+bp)))) -> SB.Le(x, m):
  match x m:
    case 0n mm:
      (mm, {==})
    case 1n++i 0n:
      (+k, e) = h
      Empty.absurd(SB.Le(1n+i, 0n), gt_self(bp, Nat.add(Nat.mul(i, 1n+bp), k), lmc_wrap(bp, i, k, e)))
    case 1n++i 1n++j:
      (+k, e) = h
      le_succ(i, j, le_mul_cancel(i, j, bp, (k, N.add_cancel(1n+bp, Nat.add(Nat.mul(i, 1n+bp), k), Nat.add(bp, Nat.mul(j, 1n+bp)), lmc_shift(bp, i, j, k, e)))))

# (s div B) * B <= s
def divb_le(+s: Nat, +bp: Nat) -> SB.Le(Nat.mul(Nat.div(s, 1n+bp), 1n+bp), s):
  (Nat.mod(s, 1n+bp), Equal.trans(Nat, Nat.add(Nat.mul(Nat.div(s, 1n+bp), 1n+bp), Nat.mod(s, 1n+bp)), Nat.add(Nat.mod(s, 1n+bp), Nat.mul(Nat.div(s, 1n+bp), 1n+bp)), s,
    N.add_comm(Nat.mul(Nat.div(s, 1n+bp), 1n+bp), Nat.mod(s, 1n+bp)),
    Equal.sym(Nat, s, Nat.add(Nat.mod(s, 1n+bp), Nat.mul(Nat.div(s, 1n+bp), 1n+bp)), divmod_eq(s, bp))))

# s <= bp + m*B gives s div B <= m
def div_le(+s: Nat, +bp: Nat, +m: Nat, h: SB.Le(s, Nat.add(bp, Nat.mul(m, 1n+bp)))) -> SB.Le(Nat.div(s, 1n+bp), m):
  le_mul_cancel(Nat.div(s, 1n+bp), m, bp, le_trans(Nat.mul(Nat.div(s, 1n+bp), 1n+bp), s, Nat.add(bp, Nat.mul(m, 1n+bp)), divb_le(s, bp), h))

# Comparison and order
# --------------------

def cmp_lt(x: Nat, y: Nat, e: {LT{} == Nat.cmp(x, y) : Cmp}) -> SB.Le(1n+x, y):
  match x y:
    case 0n 0n:
      %e : NR.CmpD(_, Unit, SB.Le(1n, 0n), Unit)
      Unit{}
    case 0n 1n+j:
      (j, {==})
    case 1n+i 0n:
      %e : NR.CmpD(_, Unit, Unit, SB.Le(2n+i, 0n))
      Unit{}
    case 1n+i 1n+j:
      le_succ(1n+i, j, cmp_lt(i, j, e))

def cmp_gt(x: Nat, y: Nat, e: {GT{} == Nat.cmp(x, y) : Cmp}) -> SB.Le(1n+y, x):
  match x y:
    case 0n 0n:
      %e : NR.CmpD(_, Unit, SB.Le(1n, 0n), Unit)
      Unit{}
    case 0n 1n+j:
      %e : NR.CmpD(_, SB.Le(2n+j, 0n), Unit, Unit)
      Unit{}
    case 1n+i 0n:
      (i, {==})
    case 1n+i 1n+j:
      le_succ(1n+j, i, cmp_gt(i, j, e))

def lt_cmp(x: Nat, y: Nat, h: SB.Le(1n+x, y)) -> {LT{} == Nat.cmp(x, y) : Cmp}:
  match x y:
    case 0n 0n:
      (k, e) = h
      %e : N.NatD(_, {LT{} == EQ{} : Cmp}, Unit)
      Unit{}
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      (k, e) = h
      %e : N.NatD(_, {LT{} == GT{} : Cmp}, Unit)
      Unit{}
    case 1n+i 1n+j:
      lt_cmp(i, j, le_pred(1n+i, j, h))

# a <= b and c <= d give a + c <= b + d
def le_add_mono.eq(+a: Nat, -b: Nat, +c: Nat, -d: Nat, +k1: Nat, +k2: Nat, e1: {Nat.add(a, k1) == b : Nat}, e2: {Nat.add(c, k2) == d : Nat}) -> {Nat.add(Nat.add(a, c), Nat.add(k1, k2)) == Nat.add(b, d) : Nat}:
  %e1 : {Nat.add(Nat.add(a, c), Nat.add(k1, k2)) == Nat.add(_, d) : Nat}
  %e2 : {Nat.add(Nat.add(a, c), Nat.add(k1, k2)) == Nat.add(Nat.add(a, k1), _) : Nat}
  NR.ring_eq([a, c, k1, k2], NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}, NR.NAdd{NR.NVar{2n}, NR.NVar{3n}}}, NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NVar{2n}}, NR.NAdd{NR.NVar{1n}, NR.NVar{3n}}}, {==})

def le_add_mono(+a: Nat, -b: Nat, +c: Nat, -d: Nat, h1: SB.Le(a, b), h2: SB.Le(c, d)) -> SB.Le(Nat.add(a, c), Nat.add(b, d)):
  (+k1, e1) = h1
  (+k2, e2) = h2
  (Nat.add(k1, k2), le_add_mono.eq(a, b, c, d, k1, k2, e1, e2))

# a <= b and c <= d give a * c <= b * d
def le_mul_mono.eq(+a: Nat, -b: Nat, +c: Nat, -d: Nat, +k1: Nat, +k2: Nat, e1: {Nat.add(a, k1) == b : Nat}, e2: {Nat.add(c, k2) == d : Nat})
  -> {Nat.add(Nat.mul(a, c), Nat.add(Nat.add(Nat.mul(a, k2), Nat.mul(k1, c)), Nat.mul(k1, k2))) == Nat.mul(b, d) : Nat}:
  %e1 : {Nat.add(Nat.mul(a, c), Nat.add(Nat.add(Nat.mul(a, k2), Nat.mul(k1, c)), Nat.mul(k1, k2))) == Nat.mul(_, d) : Nat}
  %e2 : {Nat.add(Nat.mul(a, c), Nat.add(Nat.add(Nat.mul(a, k2), Nat.mul(k1, c)), Nat.mul(k1, k2))) == Nat.mul(Nat.add(a, k1), _) : Nat}
  NR.ring_eq([a, c, k1, k2], NR.NAdd{NR.NMul{NR.NVar{0n}, NR.NVar{1n}}, NR.NAdd{NR.NAdd{NR.NMul{NR.NVar{0n}, NR.NVar{3n}}, NR.NMul{NR.NVar{2n}, NR.NVar{1n}}}, NR.NMul{NR.NVar{2n}, NR.NVar{3n}}}}, NR.NMul{NR.NAdd{NR.NVar{0n}, NR.NVar{2n}}, NR.NAdd{NR.NVar{1n}, NR.NVar{3n}}}, {==})

def le_mul_mono(+a: Nat, -b: Nat, +c: Nat, -d: Nat, h1: SB.Le(a, b), h2: SB.Le(c, d)) -> SB.Le(Nat.mul(a, c), Nat.mul(b, d)):
  (+k1, e1) = h1
  (+k2, e2) = h2
  (Nat.add(Nat.add(Nat.mul(a, k2), Nat.mul(k1, c)), Nat.mul(k1, k2)), le_mul_mono.eq(a, b, c, d, k1, k2, e1, e2))

def gt_cmp(x: Nat, y: Nat, h: SB.Le(1n+y, x)) -> {GT{} == Nat.cmp(x, y) : Cmp}:
  match x y:
    case 0n 0n:
      (k, e) = h
      %e : N.NatD(_, {GT{} == EQ{} : Cmp}, Unit)
      Unit{}
    case 0n 1n+j:
      (k, e) = h
      %e : N.NatD(_, {GT{} == LT{} : Cmp}, Unit)
      Unit{}
    case 1n+i 0n:
      {==}
    case 1n+i 1n+j:
      gt_cmp(i, j, le_pred(1n+j, i, h))

# adding c to both sides keeps the comparison
def cmp_add_l(c: Nat, -a: Nat, -b: Nat) -> {Nat.cmp(a, b) == Nat.cmp(Nat.add(c, a), Nat.add(c, b)) : Cmp}:
  match c:
    case 0n:
      {==}
    case 1n+k:
      cmp_add_l(k, a, b)

def cmp_add_r(+a: Nat, +b: Nat, +c: Nat) -> {Nat.cmp(a, b) == Nat.cmp(Nat.add(a, c), Nat.add(b, c)) : Cmp}:
  %N.add_comm(c, a) : {Nat.cmp(a, b) == Nat.cmp(_, Nat.add(b, c)) : Cmp}
  %N.add_comm(c, b) : {Nat.cmp(a, b) == Nat.cmp(Nat.add(c, a), _) : Cmp}
  cmp_add_l(c, a, b)

# a low limb ah below the base cannot make up a deficit in the high part:
# 1 + X <= Y gives 1 + (ah + X*B) <= bh + Y*B
def lift_lt.eq(+bp: Nat, +ah: Nat, +bh: Nat, +x: Nat, -y: Nat, +k1: Nat, +k2: Nat, e1: {Nat.add(ah, k1) == bp : Nat}, e2: {Nat.add(1n+x, k2) == y : Nat})
  -> {Nat.add(1n+Nat.add(ah, Nat.mul(x, 1n+bp)), Nat.add(Nat.add(k1, Nat.mul(k2, 1n+bp)), bh)) == Nat.add(bh, Nat.mul(y, 1n+bp)) : Nat}:
  %e2 : {Nat.add(1n+Nat.add(ah, Nat.mul(x, 1n+bp)), Nat.add(Nat.add(k1, Nat.mul(k2, 1n+bp)), bh)) == Nat.add(bh, Nat.mul(_, 1n+bp)) : Nat}
  %NR.ring_eq([ah, k1, x, k2, bh, bp], NR.NAdd{NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}}, NR.NAdd{NR.NMul{NR.NVar{2n}, NR.NAdd{NR.NCst{1n}, NR.NVar{5n}}}, NR.NMul{NR.NVar{3n}, NR.NAdd{NR.NCst{1n}, NR.NVar{5n}}}}}, NR.NVar{4n}}, NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{2n}, NR.NAdd{NR.NCst{1n}, NR.NVar{5n}}}}}, NR.NAdd{NR.NAdd{NR.NVar{1n}, NR.NMul{NR.NVar{3n}, NR.NAdd{NR.NCst{1n}, NR.NVar{5n}}}}, NR.NVar{4n}}}, {==}) : {_ == Nat.add(bh, Nat.mul(Nat.add(1n+x, k2), 1n+bp)) : Nat}
  %Equal.sym(Nat, Nat.add(ah, k1), bp, e1) : {Nat.add(Nat.add(1n+_, Nat.add(Nat.mul(x, 1n+bp), Nat.mul(k2, 1n+bp))), bh) == Nat.add(bh, Nat.mul(Nat.add(1n+x, k2), 1n+bp)) : Nat}
  NR.ring_eq([bp, x, k2, bh], NR.NAdd{NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}, NR.NAdd{NR.NMul{NR.NVar{1n}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}, NR.NMul{NR.NVar{2n}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}}}, NR.NVar{3n}}, NR.NAdd{NR.NVar{3n}, NR.NMul{NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NVar{1n}}, NR.NVar{2n}}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}}, {==})

def lift_lt(+bp: Nat, +ah: Nat, +bh: Nat, +x: Nat, -y: Nat, la: SB.Le(ah, bp), h: SB.Le(1n+x, y)) -> SB.Le(1n+Nat.add(ah, Nat.mul(x, 1n+bp)), Nat.add(bh, Nat.mul(y, 1n+bp))):
  (+k1, e1) = la
  (+k2, e2) = h
  (Nat.add(Nat.add(k1, Nat.mul(k2, 1n+bp)), bh), lift_lt.eq(bp, ah, bh, x, y, k1, k2, e1, e2))

# truncated subtraction is exact when y <= x
def sub_add(x: Nat, y: Nat, h: SB.Le(y, x)) -> {Nat.add(Nat.sub(x, y), y) == x : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      (k, e) = h
      %e : N.NatD(_, {Nat.add(Nat.sub(0n, 1n+j), 1n+j) == 0n : Nat}, Unit)
      Unit{}
    case 1n+i 0n:
      %N.add_zero(i) : {1n+_ == 1n+i : Nat}
      {==}
    case 1n++i 1n++j:
      %N.add_succ(Nat.sub(i, j), j) : {_ == 1n+i : Nat}
      %sub_add(i, j, le_pred(j, i, h)) : {1n+Nat.add(Nat.sub(i, j), j) == 1n+_ : Nat}
      {==}

def le_weaken.eq(+t: Nat, -a: Nat, +k: Nat, e: {1n+Nat.add(t, k) == a : Nat}) -> {Nat.add(t, 1n+k) == a : Nat}:
  %e : {Nat.add(t, 1n+k) == _ : Nat}
  %N.add_succ(t, k) : {_ == 1n+Nat.add(t, k) : Nat}
  {==}

# 1 + t <= a gives t <= a
def le_weaken(+t: Nat, -a: Nat, h: SB.Le(1n+t, a)) -> SB.Le(t, a):
  (+k, e) = h
  (1n+k, le_weaken.eq(t, a, k, e))
