# bend-cad: runtime magnitudes in a base 2^L (rt/wmag.bend) compute what
# they mean. Shifts multiply and divide by powers of two (Floor: the
# quotient, pinned by inequalities), Mag.bits is the bit length (Bits),
# Mag.ofpos and Mag.topos convert with the spec's positives, and a
# magnitude with no high zero limb (Top) is the only one of its value.
# The base is 1 + bp = 2^(1 + lp) for any lp (hb); the CLI's is 2^12
# (lib/fast.bend).

# Generated from tools/drafts/wmagpf.draft by tools/expand.py; edit the
# draft.

import Base
import ./nat.bend as N
import ./natring.bend as NR
import ./natord.bend as O
import ./mag.bend as LM
import ./pos.bend as P
import ./qreduce.bend as QRD
import ../spec/num.bend as S
import ../spec/big.bend as SB
import ../spec/mat.bend as M
import ../rt/mag.bend as RM
import ../rt/wmag.bend as RW


# Powers of two
# -------------

# 2^a 2^b = 2^(a + b)
def pw_add(a: Nat, +b: Nat) -> {Nat.mul(RW.pw(a), RW.pw(b)) == RW.pw(Nat.add(a, b)) : Nat}:
  match a:
    case 0n:
      NR.ring_eq([RW.pw(b)], NR.NMul{NR.NCst{1n}, NR.NVar{0n}}, NR.NVar{0n}, {==})
    case 1n++k:
      %pw_add(k, b) : {Nat.mul(Nat.mul(2n, RW.pw(k)), RW.pw(b)) == Nat.mul(2n, _) : Nat}
      NR.ring_eq([RW.pw(k), RW.pw(b)], NR.NMul{NR.NMul{NR.NCst{2n}, NR.NVar{0n}}, NR.NVar{1n}}, NR.NMul{NR.NCst{2n}, NR.NMul{NR.NVar{0n}, NR.NVar{1n}}}, {==})

def pw_pos.eq(-j: Nat, +d: Nat, e: {Nat.add(1n, d) == RW.pw(j) : Nat}) -> {Nat.add(1n, Nat.add(1n, Nat.mul(2n, d))) == RW.pw(1n+j) : Nat}:
  %e : {Nat.add(1n, Nat.add(1n, Nat.mul(2n, d))) == Nat.mul(2n, _) : Nat}
  NR.ring_eq([d], NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NCst{1n}, NR.NMul{NR.NCst{2n}, NR.NVar{0n}}}}, NR.NMul{NR.NCst{2n}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}, {==})

def pw_pos.c(-j: Nat, h: SB.Le(1n, RW.pw(j))) -> SB.Le(1n, RW.pw(1n+j)):
  (+d, e) = h
  (Nat.add(1n, Nat.mul(2n, d)), pw_pos.eq(j, d, e))

# 1 <= 2^k
def pw_pos(k: Nat) -> SB.Le(1n, RW.pw(k)):
  match k:
    case 0n:
      (0n, {==})
    case 1n++j:
      pw_pos.c(j, pw_pos(j))

# Order
# -----

def absurd(-A: Type, x: Empty) -> A:
  match x:

# no x is below itself
def lt_irrefl(x: Nat, h: SB.Le(1n+x, x)) -> Empty:
  (z, e) = h
  O.gt_self(x, z, e)

def le_of_eq(+a: Nat, -b: Nat, e: {a == b : Nat}) -> SB.Le(a, b):
  %e : SB.Le(a, _)
  O.le_refl(a)

# x <= h + x
def le_addl(+h: Nat, +x: Nat) -> SB.Le(x, Nat.add(h, x)):
  (h, NR.ring_eq([x, h], NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}, NR.NAdd{NR.NVar{1n}, NR.NVar{0n}}, {==}))

# 1 + b c <= (1 + b) c, for c = 1 + k
def le_succ_mul(+b: Nat, +k: Nat) -> SB.Le(1n+Nat.mul(b, 1n+k), Nat.mul(1n+b, 1n+k)):
  (k, NR.ring_eq([Nat.mul(b, 1n+k), k], NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}}, NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NVar{1n}}, NR.NVar{0n}}, {==}))

# a c <= b c gives a <= b, for c = 1 + k
def le_cancel.go(c: Cmp, +a: Nat, +b: Nat, +k: Nat, e: {c == Nat.cmp(a, b) : Cmp}, h: SB.Le(Nat.mul(a, 1n+k), Nat.mul(b, 1n+k))) -> SB.Le(a, b):
  match c:
    case LT{}:
      O.le_weaken(a, b, O.cmp_lt(a, b, e))
    case EQ{}:
      le_of_eq(a, b, NR.nat_cmp_eq(a, b, e))
    case GT{}:
      absurd(SB.Le(a, b), lt_irrefl(Nat.mul(b, 1n+k), O.le_trans(1n+Nat.mul(b, 1n+k), Nat.mul(1n+b, 1n+k), Nat.mul(b, 1n+k), le_succ_mul(b, k),
        O.le_trans(Nat.mul(1n+b, 1n+k), Nat.mul(a, 1n+k), Nat.mul(b, 1n+k), O.le_mul_mono(1n+b, a, 1n+k, 1n+k, O.cmp_gt(a, b, e), O.le_refl(1n+k)), h))))

def le_cancel(+a: Nat, +b: Nat, +k: Nat, h: SB.Le(Nat.mul(a, 1n+k), Nat.mul(b, 1n+k))) -> SB.Le(a, b):
  le_cancel.go(Nat.cmp(a, b), a, b, k, {==}, h)

# 1 + a c <= b c is impossible when b <= a
def lt_cancel.no(+a: Nat, +b: Nat, +k: Nat, hba: SB.Le(b, a), h: SB.Le(1n+Nat.mul(a, 1n+k), Nat.mul(b, 1n+k))) -> Empty:
  lt_irrefl(Nat.mul(a, 1n+k), O.le_trans(1n+Nat.mul(a, 1n+k), Nat.mul(b, 1n+k), Nat.mul(a, 1n+k), h, O.le_mul_mono(b, a, 1n+k, 1n+k, hba, O.le_refl(1n+k))))

# 1 + a c <= b c gives 1 + a <= b, for c = 1 + k
def lt_cancel.go(c: Cmp, +a: Nat, +b: Nat, +k: Nat, e: {c == Nat.cmp(a, b) : Cmp}, h: SB.Le(1n+Nat.mul(a, 1n+k), Nat.mul(b, 1n+k))) -> SB.Le(1n+a, b):
  match c:
    case LT{}:
      O.cmp_lt(a, b, e)
    case EQ{}:
      absurd(SB.Le(1n+a, b), lt_cancel.no(a, b, k, le_of_eq(b, a, Equal.sym(Nat, a, b, NR.nat_cmp_eq(a, b, e))), h))
    case GT{}:
      absurd(SB.Le(1n+a, b), lt_cancel.no(a, b, k, O.le_weaken(b, a, O.cmp_gt(a, b, e)), h))

def lt_cancel(+a: Nat, +b: Nat, +k: Nat, h: SB.Le(1n+Nat.mul(a, 1n+k), Nat.mul(b, 1n+k))) -> SB.Le(1n+a, b):
  lt_cancel.go(Nat.cmp(a, b), a, b, k, {==}, h)

# Quotients
# ---------

# u = floor(v / d): u d <= v < (u + 1) d
def Floor(v: Nat, d: Nat, u: Nat) -> Data:
  M.Both(SB.Le(Nat.mul(u, d), v), SB.Le(1n+v, Nat.mul(1n+u, d)))

def floor_one(+v: Nat) -> Floor(v, 1n, v):
  (le_of_eq(Nat.mul(v, 1n), v, Equal.sym(Nat, v, Nat.mul(v, 1n), N.mul_one(v))), le_of_eq(1n+v, Nat.mul(1n+v, 1n), N.mul_one(1n+v)))

def floor_mul.lo(+v: Nat, +d: Nat, +u: Nat, +h: Nat, +bp: Nat, lo: SB.Le(Nat.mul(u, d), v)) -> SB.Le(Nat.mul(u, Nat.mul(1n+bp, d)), Nat.add(h, Nat.mul(v, 1n+bp))):
  %NR.ring_eq([u, d, 1n+bp], NR.NMul{NR.NMul{NR.NVar{0n}, NR.NVar{1n}}, NR.NVar{2n}}, NR.NMul{NR.NVar{0n}, NR.NMul{NR.NVar{2n}, NR.NVar{1n}}}, {==}) : SB.Le(_, Nat.add(h, Nat.mul(v, 1n+bp)))
  O.le_trans(Nat.mul(Nat.mul(u, d), 1n+bp), Nat.mul(v, 1n+bp), Nat.add(h, Nat.mul(v, 1n+bp)), O.le_mul_mono(Nat.mul(u, d), v, 1n+bp, 1n+bp, lo, O.le_refl(1n+bp)), le_addl(h, Nat.mul(v, 1n+bp)))

def floor_mul.hi(+v: Nat, +d: Nat, +u: Nat, +h: Nat, +bp: Nat, hi: SB.Le(1n+v, Nat.mul(1n+u, d)), lh: SB.Le(h, bp)) -> SB.Le(1n+Nat.add(h, Nat.mul(v, 1n+bp)), Nat.mul(1n+u, Nat.mul(1n+bp, d))):
  %NR.ring_eq([u, d, 1n+bp], NR.NMul{NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}, NR.NVar{1n}}, NR.NVar{2n}}, NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}, NR.NMul{NR.NVar{2n}, NR.NVar{1n}}}, {==}) : SB.Le(1n+Nat.add(h, Nat.mul(v, 1n+bp)), _)
  O.le_trans(1n+Nat.add(h, Nat.mul(v, 1n+bp)), Nat.mul(1n+v, 1n+bp), Nat.mul(Nat.mul(1n+u, d), 1n+bp),
    O.le_add_mono(1n+h, 1n+bp, Nat.mul(v, 1n+bp), Nat.mul(v, 1n+bp), O.le_succ(h, bp, lh), O.le_refl(Nat.mul(v, 1n+bp))),
    O.le_mul_mono(1n+v, Nat.mul(1n+u, d), 1n+bp, 1n+bp, hi, O.le_refl(1n+bp)))

# a digit below: Floor(v, d, u) gives Floor(h + v B, B d, u) for h < B = 1 + bp
def floor_mul(+v: Nat, +d: Nat, +u: Nat, +h: Nat, +bp: Nat, f: Floor(v, d, u), lh: SB.Le(h, bp)) -> Floor(Nat.add(h, Nat.mul(v, 1n+bp)), Nat.mul(1n+bp, d), u):
  (lo, hi) = f
  (floor_mul.lo(v, d, u, h, bp, lo), floor_mul.hi(v, d, u, h, bp, hi, lh))

def floor_cancel.lo(+v: Nat, +d: Nat, +u: Nat, +k: Nat, lo: SB.Le(Nat.mul(u, Nat.mul(d, 1n+k)), Nat.mul(v, 1n+k))) -> SB.Le(Nat.mul(u, d), v):
  le_cancel(Nat.mul(u, d), v, k, (%Equal.sym(Nat, Nat.mul(Nat.mul(u, d), 1n+k), Nat.mul(u, Nat.mul(d, 1n+k)), NR.ring_eq([u, d, 1n+k], NR.NMul{NR.NMul{NR.NVar{0n}, NR.NVar{1n}}, NR.NVar{2n}}, NR.NMul{NR.NVar{0n}, NR.NMul{NR.NVar{1n}, NR.NVar{2n}}}, {==})) : SB.Le(_, Nat.mul(v, 1n+k))
    lo))

def floor_cancel.hi(+v: Nat, +d: Nat, +u: Nat, +k: Nat, hi: SB.Le(1n+Nat.mul(v, 1n+k), Nat.mul(1n+u, Nat.mul(d, 1n+k)))) -> SB.Le(1n+v, Nat.mul(1n+u, d)):
  lt_cancel(v, Nat.mul(1n+u, d), k, (%Equal.sym(Nat, Nat.mul(Nat.mul(1n+u, d), 1n+k), Nat.mul(1n+u, Nat.mul(d, 1n+k)), NR.ring_eq([u, d, 1n+k], NR.NMul{NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}, NR.NVar{1n}}, NR.NVar{2n}}, NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}, NR.NMul{NR.NVar{1n}, NR.NVar{2n}}}, {==})) : SB.Le(1n+Nat.mul(v, 1n+k), _)
    hi))

# Floor(v c, d c, u) gives Floor(v, d, u), for c = 1 + k
def floor_cancel(+v: Nat, +d: Nat, +u: Nat, +k: Nat, f: Floor(Nat.mul(v, 1n+k), Nat.mul(d, 1n+k), u)) -> Floor(v, d, u):
  (lo, hi) = f
  (floor_cancel.lo(v, d, u, k, lo), floor_cancel.hi(v, d, u, k, hi))

def floor_comp.lo(+v: Nat, +p1: Nat, +v1: Nat, +p2: Nat, +u: Nat, lo1: SB.Le(Nat.mul(v1, p1), v), lo2: SB.Le(Nat.mul(u, p2), v1)) -> SB.Le(Nat.mul(u, Nat.mul(p2, p1)), v):
  %NR.ring_eq([u, p1, p2], NR.NMul{NR.NMul{NR.NVar{0n}, NR.NVar{2n}}, NR.NVar{1n}}, NR.NMul{NR.NVar{0n}, NR.NMul{NR.NVar{2n}, NR.NVar{1n}}}, {==}) : SB.Le(_, v)
  O.le_trans(Nat.mul(Nat.mul(u, p2), p1), Nat.mul(v1, p1), v, O.le_mul_mono(Nat.mul(u, p2), v1, p1, p1, lo2, O.le_refl(p1)), lo1)

def floor_comp.hi(+v: Nat, +p1: Nat, +v1: Nat, +p2: Nat, +u: Nat, hi1: SB.Le(1n+v, Nat.mul(1n+v1, p1)), hi2: SB.Le(1n+v1, Nat.mul(1n+u, p2))) -> SB.Le(1n+v, Nat.mul(1n+u, Nat.mul(p2, p1))):
  %NR.ring_eq([u, p1, p2], NR.NMul{NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}, NR.NVar{2n}}, NR.NVar{1n}}, NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}, NR.NMul{NR.NVar{2n}, NR.NVar{1n}}}, {==}) : SB.Le(1n+v, _)
  O.le_trans(1n+v, Nat.mul(1n+v1, p1), Nat.mul(Nat.mul(1n+u, p2), p1), hi1, O.le_mul_mono(1n+v1, Nat.mul(1n+u, p2), p1, p1, hi2, O.le_refl(p1)))

# floor(floor(v / p1) / p2) = floor(v / (p2 p1))
def floor_comp(+v: Nat, +p1: Nat, +v1: Nat, +p2: Nat, +u: Nat, f1: Floor(v, p1, v1), f2: Floor(v1, p2, u)) -> Floor(v, Nat.mul(p2, p1), u):
  (lo1, hi1) = f1
  (lo2, hi2) = f2
  (floor_comp.lo(v, p1, v1, p2, u, lo1, lo2), floor_comp.hi(v, p1, v1, p2, u, hi1, hi2))

def floor_lt(+v: Nat, +d: Nat, +u1: Nat, +u2: Nat, h: SB.Le(1n+u1, u2), f1: Floor(v, d, u1), f2: Floor(v, d, u2)) -> Empty:
  (lo1, hi1) = f1
  (lo2, hi2) = f2
  lt_irrefl(v, O.le_trans(1n+v, Nat.mul(1n+u1, d), v, hi1, O.le_trans(Nat.mul(1n+u1, d), Nat.mul(u2, d), v, O.le_mul_mono(1n+u1, u2, d, d, h, O.le_refl(d)), lo2)))

def floor_uniq.go(c: Cmp, +v: Nat, +d: Nat, +u1: Nat, +u2: Nat, e: {c == Nat.cmp(u1, u2) : Cmp}, f1: Floor(v, d, u1), f2: Floor(v, d, u2)) -> {u1 == u2 : Nat}:
  match c:
    case LT{}:
      absurd({u1 == u2 : Nat}, floor_lt(v, d, u1, u2, O.cmp_lt(u1, u2, e), f1, f2))
    case EQ{}:
      NR.nat_cmp_eq(u1, u2, e)
    case GT{}:
      absurd({u1 == u2 : Nat}, floor_lt(v, d, u2, u1, O.cmp_gt(u1, u2, e), f2, f1))

# the quotient is unique
def floor_uniq(+v: Nat, +d: Nat, +u1: Nat, +u2: Nat, f1: Floor(v, d, u1), f2: Floor(v, d, u2)) -> {u1 == u2 : Nat}:
  floor_uniq.go(Nat.cmp(u1, u2), v, d, u1, u2, {==}, f1, f2)

# transport along equal arguments
def floor_eq(+v: Nat, +x: Nat, +d: Nat, +dd: Nat, +u: Nat, hx: {x == v : Nat}, hd: {dd == d : Nat}, f: Floor(x, dd, u)) -> Floor(v, d, u):
  %hx : Floor(_, d, u)
  %hd : Floor(x, _, u)
  f

def floor_zero.hi(+d: Nat, h: SB.Le(1n, d)) -> SB.Le(1n, Nat.mul(1n, d)):
  %N.add_zero(d) : SB.Le(1n, _)
  h

# 0 = floor(0 / d), for d >= 1
def floor_zero(+d: Nat, h: SB.Le(1n, d)) -> Floor(0n, d, 0n):
  ((0n, {==}), floor_zero.hi(d, h))

# More powers
# -----------

def pw_mono.c(+a: Nat, -b: Nat, h: SB.Le(a, b)) -> SB.Le(RW.pw(a), RW.pw(b)):
  (+d, e) = h
  %e : SB.Le(RW.pw(a), RW.pw(_))
  %pw_add(a, d) : SB.Le(RW.pw(a), _)
  %NR.ring_eq([RW.pw(a)], NR.NMul{NR.NVar{0n}, NR.NCst{1n}}, NR.NVar{0n}, {==}) : SB.Le(_, Nat.mul(RW.pw(a), RW.pw(d)))
  O.le_mul_mono(RW.pw(a), RW.pw(a), 1n, RW.pw(d), O.le_refl(RW.pw(a)), pw_pos(d))

# a <= b gives 2^a <= 2^b
def pw_mono(+a: Nat, -b: Nat, h: SB.Le(a, b)) -> SB.Le(RW.pw(a), RW.pw(b)):
  pw_mono.c(a, b, h)

def pw_lt.eq(+x: Nat, +d: Nat, e: {Nat.add(1n, d) == x : Nat}) -> {Nat.add(1n+x, d) == Nat.mul(2n, x) : Nat}:
  %e : {Nat.add(1n+_, d) == Nat.mul(2n, _) : Nat}
  NR.ring_eq([d], NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}, NR.NVar{0n}}, NR.NMul{NR.NCst{2n}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}, {==})

def pw_lt.c(+x: Nat, h: SB.Le(1n, x)) -> SB.Le(1n+x, Nat.mul(2n, x)):
  (+d, e) = h
  (d, pw_lt.eq(x, d, e))

# 2^lp < 2^(lp + 1) = B, so 2^lp <= bp
def pw_lp_le(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}) -> SB.Le(RW.pw(lp), bp):
  O.le_pred(RW.pw(lp), bp, (%hb : SB.Le(1n+RW.pw(lp), _)
    pw_lt.c(RW.pw(lp), pw_pos(lp))))

# the base is at least 2
def bp_pos(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}) -> SB.Le(1n, bp):
  O.le_trans(1n, RW.pw(lp), bp, pw_pos(lp), pw_lp_le(bp, lp, hb))

# 2^r <= bp for r <= lp
def pw_le_bp(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +r: Nat, hr: SB.Le(r, lp)) -> SB.Le(RW.pw(r), bp):
  O.le_trans(RW.pw(r), RW.pw(lp), bp, pw_mono(r, lp, hr), pw_lp_le(bp, lp, hb))

# Zero limbs and shifts left
# --------------------------

# m B^n
def zl_val(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, n: Nat, +m: List<&2, Nat>) -> {Nat.mul(SB.Mag.val(bp, m), RW.pw(Nat.mul(n, 1n+lp))) == SB.Mag.val(bp, RW.Mag.zl(n, m)) : Nat}:
  match n:
    case 0n:
      NR.ring_eq([SB.Mag.val(bp, m)], NR.NMul{NR.NVar{0n}, NR.NCst{1n}}, NR.NVar{0n}, {==})
    case 1n++j:
      %zl_val(bp, lp, hb, j, m) : {Nat.mul(SB.Mag.val(bp, m), RW.pw(Nat.mul(1n+j, 1n+lp))) == Nat.mul(_, 1n+bp) : Nat}
      %hb : {Nat.mul(SB.Mag.val(bp, m), RW.pw(Nat.mul(1n+j, 1n+lp))) == Nat.mul(Nat.mul(SB.Mag.val(bp, m), RW.pw(Nat.mul(j, 1n+lp))), _) : Nat}
      %pw_add(1n+lp, Nat.mul(j, 1n+lp)) : {Nat.mul(SB.Mag.val(bp, m), _) == Nat.mul(Nat.mul(SB.Mag.val(bp, m), RW.pw(Nat.mul(j, 1n+lp))), RW.pw(1n+lp)) : Nat}
      NR.ring_eq([SB.Mag.val(bp, m), RW.pw(1n+lp), RW.pw(Nat.mul(j, 1n+lp))], NR.NMul{NR.NVar{0n}, NR.NMul{NR.NVar{1n}, NR.NVar{2n}}}, NR.NMul{NR.NMul{NR.NVar{0n}, NR.NVar{2n}}, NR.NVar{1n}}, {==})

def zl_wf(+bp: Nat, n: Nat, m: List<&2, Nat>, wm: SB.Mag.wf(bp, m)) -> SB.Mag.wf(bp, RW.Mag.zl(n, m)):
  match n:
    case 0n:
      wm
    case 1n+j:
      ((bp, {==}), zl_wf(bp, j, m, wm))


# k = r + q L
def pw_divmod(+lp: Nat, +k: Nat) -> {Nat.mul(RW.pw(Nat.mod(k, 1n+lp)), RW.pw(Nat.mul(Nat.div(k, 1n+lp), 1n+lp))) == RW.pw(k) : Nat}:
  %Equal.sym(Nat, k, Nat.add(Nat.mod(k, 1n+lp), Nat.mul(Nat.div(k, 1n+lp), 1n+lp)), O.divmod_eq(k, lp)) : {Nat.mul(RW.pw(Nat.mod(k, 1n+lp)), RW.pw(Nat.mul(Nat.div(k, 1n+lp), 1n+lp))) == RW.pw(_) : Nat}
  pw_add(Nat.mod(k, 1n+lp), Nat.mul(Nat.div(k, 1n+lp), 1n+lp))

# m 2^k
def shl_val(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, m: List<&2, Nat>, +k: Nat) -> {Nat.mul(SB.Mag.val(bp, m), RW.pw(k)) == SB.Mag.val(bp, RW.Mag.shl(bp, lp, m, k)) : Nat}:
  match m:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %zl_val(bp, lp, hb, Nat.div(k, 1n+lp), RM.Mag.mul1(bp, Con{h, t}, RW.pw(Nat.mod(k, 1n+lp)), 0n)) : {Nat.mul(SB.Mag.val(bp, Con{h, t}), RW.pw(k)) == _ : Nat}
      %LM.mul1_val(bp, Con{h, t}, RW.pw(Nat.mod(k, 1n+lp)), 0n) : {Nat.mul(SB.Mag.val(bp, Con{h, t}), RW.pw(k)) == Nat.mul(_, RW.pw(Nat.mul(Nat.div(k, 1n+lp), 1n+lp))) : Nat}
      %pw_divmod(lp, k) : {Nat.mul(SB.Mag.val(bp, Con{h, t}), _) == Nat.mul(Nat.add(Nat.mul(SB.Mag.val(bp, Con{h, t}), RW.pw(Nat.mod(k, 1n+lp))), 0n), RW.pw(Nat.mul(Nat.div(k, 1n+lp), 1n+lp))) : Nat}
      NR.ring_eq([SB.Mag.val(bp, Con{h, t}), RW.pw(Nat.mod(k, 1n+lp)), RW.pw(Nat.mul(Nat.div(k, 1n+lp), 1n+lp))], NR.NMul{NR.NVar{0n}, NR.NMul{NR.NVar{1n}, NR.NVar{2n}}}, NR.NMul{NR.NAdd{NR.NMul{NR.NVar{0n}, NR.NVar{1n}}, NR.NCst{0n}}, NR.NVar{2n}}, {==})

def shl_wf(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, m: List<&2, Nat>, +k: Nat, wm: SB.Mag.wf(bp, m)) -> SB.Mag.wf(bp, RW.Mag.shl(bp, lp, m, k)):
  match m:
    case Nil{}:
      Unit{}
    case Con{+h, +t}:
      zl_wf(bp, Nat.div(k, 1n+lp), RM.Mag.mul1(bp, Con{h, t}, RW.pw(Nat.mod(k, 1n+lp)), 0n),
        LM.mul1_wf(bp, Con{h, t}, RW.pw(Nat.mod(k, 1n+lp)), 0n, pw_le_bp(bp, lp, hb, Nat.mod(k, 1n+lp), O.mod_le(k, lp)), (bp, {==}), wm))

# Low limbs dropped and shifts right
# ----------------------------------


# floor(m / B^n)
def drop_val(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, n: Nat, m: List<&2, Nat>, wm: SB.Mag.wf(bp, m)) -> Floor(SB.Mag.val(bp, m), RW.pw(Nat.mul(n, 1n+lp)), SB.Mag.val(bp, RW.Mag.drop(n, m))):
  match n m:
    case 0n m:
      floor_one(SB.Mag.val(bp, m))
    case 1n++j Nil{}:
      floor_zero(RW.pw(Nat.mul(1n+j, 1n+lp)), pw_pos(Nat.mul(1n+j, 1n+lp)))
    case 1n++j Con{+h, +t}:
      (lh, wt) = wm
      %pw_add(1n+lp, Nat.mul(j, 1n+lp)) : Floor(SB.Mag.val(bp, Con{h, t}), _, SB.Mag.val(bp, RW.Mag.drop(j, t)))
      %Equal.sym(Nat, RW.pw(1n+lp), 1n+bp, hb) : Floor(SB.Mag.val(bp, Con{h, t}), Nat.mul(_, RW.pw(Nat.mul(j, 1n+lp))), SB.Mag.val(bp, RW.Mag.drop(j, t)))
      floor_mul(SB.Mag.val(bp, t), RW.pw(Nat.mul(j, 1n+lp)), SB.Mag.val(bp, RW.Mag.drop(j, t)), h, bp, drop_val(bp, lp, hb, j, t, wt), lh)

def drop_wf(+bp: Nat, n: Nat, m: List<&2, Nat>, wm: SB.Mag.wf(bp, m)) -> SB.Mag.wf(bp, RW.Mag.drop(n, m)):
  match n m:
    case 0n m:
      wm
    case 1n+j Nil{}:
      Unit{}
    case 1n+j Con{h, t}:
      (lh, wt) = wm
      drop_wf(bp, j, t, wt)


# 2^(1 L) = 2^(1 + j) 2^(lp - j), for 1 + j <= lp
def pw_split(+lp: Nat, +j: Nat, hr: SB.Le(1n+j, lp)) -> {RW.pw(Nat.mul(1n, 1n+lp)) == Nat.mul(RW.pw(1n+j), RW.pw(Nat.sub(lp, j))) : Nat}:
  %Equal.sym(Nat, Nat.mul(RW.pw(1n+j), RW.pw(Nat.sub(lp, j))), RW.pw(Nat.add(1n+j, Nat.sub(lp, j))), pw_add(1n+j, Nat.sub(lp, j))) : {RW.pw(Nat.mul(1n, 1n+lp)) == _ : Nat}
  %N.add_zero(1n+lp) : {RW.pw(_) == RW.pw(Nat.add(1n+j, Nat.sub(lp, j))) : Nat}
  %Equal.sym(Nat, Nat.add(j, Nat.sub(lp, j)), lp, Equal.trans(Nat, Nat.add(j, Nat.sub(lp, j)), Nat.add(Nat.sub(lp, j), j), lp, N.add_comm(j, Nat.sub(lp, j)), O.sub_add(lp, j, O.le_weaken(j, lp, hr)))) : {RW.pw(1n+lp) == RW.pw(1n+_) : Nat}
  {==}

def shr_hx(+bp: Nat, +m: List<&2, Nat>, +c: Nat, +k: Nat, e: {Nat.add(1n, k) == c : Nat}) -> {SB.Mag.val(bp, RM.Mag.mul1(bp, m, c, 0n)) == Nat.mul(SB.Mag.val(bp, m), 1n+k) : Nat}:
  %LM.mul1_val(bp, m, c, 0n) : {_ == Nat.mul(SB.Mag.val(bp, m), 1n+k) : Nat}
  %N.add_zero(Nat.mul(SB.Mag.val(bp, m), c)) : {_ == Nat.mul(SB.Mag.val(bp, m), 1n+k) : Nat}
  %e : {Nat.mul(SB.Mag.val(bp, m), _) == Nat.mul(SB.Mag.val(bp, m), 1n+k) : Nat}
  {==}

def shr_hd(+lp: Nat, +j: Nat, +k: Nat, hr: SB.Le(1n+j, lp), e: {Nat.add(1n, k) == RW.pw(Nat.sub(lp, j)) : Nat}) -> {RW.pw(Nat.mul(1n, 1n+lp)) == Nat.mul(RW.pw(1n+j), 1n+k) : Nat}:
  %Equal.sym(Nat, Nat.add(1n, k), RW.pw(Nat.sub(lp, j)), e) : {RW.pw(Nat.mul(1n, 1n+lp)) == Nat.mul(RW.pw(1n+j), _) : Nat}
  pw_split(lp, j, hr)


def shr_r.c(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m: List<&2, Nat>, +j: Nat, +hr: SB.Le(1n+j, lp), wm: SB.Mag.wf(bp, m), hc: SB.Le(1n, RW.pw(Nat.sub(lp, j)))) -> Floor(SB.Mag.val(bp, m), RW.pw(1n+j), SB.Mag.val(bp, RW.Mag.drop(1n, RM.Mag.mul1(bp, m, RW.pw(Nat.sub(lp, j)), 0n)))):
  (+k, +e) = hc
  floor_cancel(SB.Mag.val(bp, m), RW.pw(1n+j), SB.Mag.val(bp, RW.Mag.drop(1n, RM.Mag.mul1(bp, m, RW.pw(Nat.sub(lp, j)), 0n))), k,
    floor_eq(Nat.mul(SB.Mag.val(bp, m), 1n+k), SB.Mag.val(bp, RM.Mag.mul1(bp, m, RW.pw(Nat.sub(lp, j)), 0n)), Nat.mul(RW.pw(1n+j), 1n+k), RW.pw(Nat.mul(1n, 1n+lp)), SB.Mag.val(bp, RW.Mag.drop(1n, RM.Mag.mul1(bp, m, RW.pw(Nat.sub(lp, j)), 0n))),
      shr_hx(bp, m, RW.pw(Nat.sub(lp, j)), k, e), shr_hd(lp, j, k, hr, e),
      drop_val(bp, lp, hb, 1n, RM.Mag.mul1(bp, m, RW.pw(Nat.sub(lp, j)), 0n), LM.mul1_wf(bp, m, RW.pw(Nat.sub(lp, j)), 0n, pw_le_bp(bp, lp, hb, Nat.sub(lp, j), (j, O.sub_add(lp, j, O.le_weaken(j, lp, hr)))), (bp, {==}), wm))))

# floor(m / 2^r), r <= lp
def shr_r_val(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m: List<&2, Nat>, r: Nat, hr: SB.Le(r, lp), wm: SB.Mag.wf(bp, m)) -> Floor(SB.Mag.val(bp, m), RW.pw(r), SB.Mag.val(bp, RW.Mag.shr.r(bp, lp, m, r))):
  match r:
    case 0n:
      floor_one(SB.Mag.val(bp, m))
    case 1n++j:
      shr_r.c(bp, lp, hb, m, j, hr, wm, pw_pos(Nat.sub(lp, j)))

def shr_r_wf(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m: List<&2, Nat>, r: Nat, hr: SB.Le(r, lp), wm: SB.Mag.wf(bp, m)) -> SB.Mag.wf(bp, RW.Mag.shr.r(bp, lp, m, r)):
  match r:
    case 0n:
      wm
    case 1n++j:
      drop_wf(bp, 1n, RM.Mag.mul1(bp, m, RW.pw(Nat.sub(lp, j)), 0n), LM.mul1_wf(bp, m, RW.pw(Nat.sub(lp, j)), 0n, pw_le_bp(bp, lp, hb, Nat.sub(lp, j), (j, O.sub_add(lp, j, O.le_weaken(j, lp, hr)))), (bp, {==}), wm))


# floor(m / 2^k)
def shr_val(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m: List<&2, Nat>, +k: Nat, +wm: SB.Mag.wf(bp, m)) -> Floor(SB.Mag.val(bp, m), RW.pw(k), SB.Mag.val(bp, RW.Mag.shr(bp, lp, m, k))):
  floor_eq(SB.Mag.val(bp, m), SB.Mag.val(bp, m), RW.pw(k), Nat.mul(RW.pw(Nat.mod(k, 1n+lp)), RW.pw(Nat.mul(Nat.div(k, 1n+lp), 1n+lp))), SB.Mag.val(bp, RW.Mag.shr(bp, lp, m, k)), {==}, pw_divmod(lp, k),
    floor_comp(SB.Mag.val(bp, m), RW.pw(Nat.mul(Nat.div(k, 1n+lp), 1n+lp)), SB.Mag.val(bp, RW.Mag.drop(Nat.div(k, 1n+lp), m)), RW.pw(Nat.mod(k, 1n+lp)), SB.Mag.val(bp, RW.Mag.shr(bp, lp, m, k)),
      drop_val(bp, lp, hb, Nat.div(k, 1n+lp), m, wm),
      shr_r_val(bp, lp, hb, RW.Mag.drop(Nat.div(k, 1n+lp), m), Nat.mod(k, 1n+lp), O.mod_le(k, lp), drop_wf(bp, Nat.div(k, 1n+lp), m, wm))))

def shr_wf(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m: List<&2, Nat>, +k: Nat, wm: SB.Mag.wf(bp, m)) -> SB.Mag.wf(bp, RW.Mag.shr(bp, lp, m, k)):
  shr_r_wf(bp, lp, hb, RW.Mag.drop(Nat.div(k, 1n+lp), m), Nat.mod(k, 1n+lp), O.mod_le(k, lp), drop_wf(bp, Nat.div(k, 1n+lp), m, wm))

# Rounding
# --------


def round_hx(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m: List<&2, Nat>, +k: Nat) -> {SB.Mag.val(bp, RM.Mag.add(bp, m, RW.Mag.shl(bp, lp, Con{1n, Nil{}}, Nat.sub(k, 1n)))) == Nat.add(SB.Mag.val(bp, m), RW.pw(Nat.sub(k, 1n))) : Nat}:
  %LM.add_val(bp, m, RW.Mag.shl(bp, lp, Con{1n, Nil{}}, Nat.sub(k, 1n))) : {_ == Nat.add(SB.Mag.val(bp, m), RW.pw(Nat.sub(k, 1n))) : Nat}
  %shl_val(bp, lp, hb, Con{1n, Nil{}}, Nat.sub(k, 1n)) : {Nat.add(SB.Mag.val(bp, m), _) == Nat.add(SB.Mag.val(bp, m), RW.pw(Nat.sub(k, 1n))) : Nat}
  NR.ring_eq([SB.Mag.val(bp, m), RW.pw(Nat.sub(k, 1n)), bp], NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NMul{NR.NCst{0n}, NR.NAdd{NR.NCst{1n}, NR.NVar{2n}}}}, NR.NVar{1n}}}, NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}, {==})

def round_wf.s(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m: List<&2, Nat>, +k: Nat, wm: SB.Mag.wf(bp, m)) -> SB.Mag.wf(bp, RM.Mag.add(bp, m, RW.Mag.shl(bp, lp, Con{1n, Nil{}}, Nat.sub(k, 1n)))):
  LM.add_wf(bp, m, RW.Mag.shl(bp, lp, Con{1n, Nil{}}, Nat.sub(k, 1n)), bp_pos(bp, lp, hb), wm, shl_wf(bp, lp, hb, Con{1n, Nil{}}, Nat.sub(k, 1n), (bp_pos(bp, lp, hb), Unit{})))

# floor((m + 2^(k-1)) / 2^k)
def round_val(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m: List<&2, Nat>, +k: Nat, +wm: SB.Mag.wf(bp, m)) -> Floor(Nat.add(SB.Mag.val(bp, m), RW.pw(Nat.sub(k, 1n))), RW.pw(k), SB.Mag.val(bp, RW.Mag.round(bp, lp, m, k))):
  floor_eq(Nat.add(SB.Mag.val(bp, m), RW.pw(Nat.sub(k, 1n))), SB.Mag.val(bp, RM.Mag.add(bp, m, RW.Mag.shl(bp, lp, Con{1n, Nil{}}, Nat.sub(k, 1n)))), RW.pw(k), RW.pw(k), SB.Mag.val(bp, RW.Mag.round(bp, lp, m, k)), round_hx(bp, lp, hb, m, k), {==},
    shr_val(bp, lp, hb, RM.Mag.add(bp, m, RW.Mag.shl(bp, lp, Con{1n, Nil{}}, Nat.sub(k, 1n))), k, round_wf.s(bp, lp, hb, m, k, wm)))

def round_wf(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m: List<&2, Nat>, +k: Nat, wm: SB.Mag.wf(bp, m)) -> SB.Mag.wf(bp, RW.Mag.round(bp, lp, m, k)):
  shr_wf(bp, lp, hb, RM.Mag.add(bp, m, RW.Mag.shl(bp, lp, Con{1n, Nil{}}, Nat.sub(k, 1n))), k, round_wf.s(bp, lp, hb, m, k, wm))

# Bit length
# ----------

# n is the bit length of x: x < 2^n <= 2 x (so x >= 1)
def Bits(x: Nat, n: Nat) -> Data:
  M.Both(SB.Le(1n+x, RW.pw(n)), SB.Le(RW.pw(n), Nat.add(x, x)))

def bits_one(+x: Nat, +h1: SB.Le(1n, x), h2: SB.Le(x, 1n)) -> Bits(x, 1n):
  (O.le_succ(x, 1n, h2), O.le_add_mono(1n, x, 1n, x, h1, h1))

def bits_dbl.lo(+y: Nat, +b: Nat, +n: Nat, hb: SB.Le(b, 1n), lo: SB.Le(1n+y, RW.pw(n))) -> SB.Le(1n+Nat.add(b, Nat.mul(y, 2n)), Nat.mul(2n, RW.pw(n))):
  O.le_trans(1n+Nat.add(b, Nat.mul(y, 2n)), Nat.mul(2n, 1n+y), Nat.mul(2n, RW.pw(n)),
    (%NR.ring_eq([y], NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NCst{1n}, NR.NMul{NR.NVar{0n}, NR.NCst{2n}}}}, NR.NMul{NR.NCst{2n}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}, {==}) : SB.Le(1n+Nat.add(b, Nat.mul(y, 2n)), _)
      O.le_succ(Nat.add(b, Nat.mul(y, 2n)), Nat.add(1n, Nat.mul(y, 2n)), O.le_add_mono(b, 1n, Nat.mul(y, 2n), Nat.mul(y, 2n), hb, O.le_refl(Nat.mul(y, 2n))))),
    O.le_mul_mono(2n, 2n, 1n+y, RW.pw(n), O.le_refl(2n), lo))

def bits_dbl.hi(+y: Nat, +b: Nat, +n: Nat, hi: SB.Le(RW.pw(n), Nat.add(y, y))) -> SB.Le(Nat.mul(2n, RW.pw(n)), Nat.add(Nat.add(b, Nat.mul(y, 2n)), Nat.add(b, Nat.mul(y, 2n)))):
  O.le_trans(Nat.mul(2n, RW.pw(n)), Nat.add(Nat.mul(y, 2n), Nat.mul(y, 2n)), Nat.add(Nat.add(b, Nat.mul(y, 2n)), Nat.add(b, Nat.mul(y, 2n))),
    (%NR.ring_eq([y], NR.NMul{NR.NCst{2n}, NR.NAdd{NR.NVar{0n}, NR.NVar{0n}}}, NR.NAdd{NR.NMul{NR.NVar{0n}, NR.NCst{2n}}, NR.NMul{NR.NVar{0n}, NR.NCst{2n}}}, {==}) : SB.Le(Nat.mul(2n, RW.pw(n)), _)
      O.le_mul_mono(2n, 2n, RW.pw(n), Nat.add(y, y), O.le_refl(2n), hi)),
    O.le_add_mono(Nat.mul(y, 2n), Nat.add(b, Nat.mul(y, 2n)), Nat.mul(y, 2n), Nat.add(b, Nat.mul(y, 2n)), le_addl(b, Nat.mul(y, 2n)), le_addl(b, Nat.mul(y, 2n))))

# x = b + 2 y for a bit b: one bit longer than y
def bits_dbl(+x: Nat, +y: Nat, +b: Nat, +n: Nat, hb: SB.Le(b, 1n), hx: {Nat.add(b, Nat.mul(y, 2n)) == x : Nat}, hy: Bits(y, n)) -> Bits(x, 1n+n):
  (lo, hi) = hy
  %hx : Bits(_, 1n+n)
  (bits_dbl.lo(y, b, n, hb, lo), bits_dbl.hi(y, b, n, hi))

def bits_lt.lo(+x: Nat, +n1: Nat, lo1: SB.Le(1n+x, RW.pw(n1))) -> SB.Le(1n+Nat.add(x, x), RW.pw(1n+n1)):
  O.le_trans(1n+Nat.add(x, x), Nat.mul(2n, 1n+x), Nat.mul(2n, RW.pw(n1)), (1n, NR.ring_eq([x], NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NVar{0n}, NR.NVar{0n}}}, NR.NCst{1n}}, NR.NMul{NR.NCst{2n}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}, {==})),
    O.le_mul_mono(2n, 2n, 1n+x, RW.pw(n1), O.le_refl(2n), lo1))

def bits_lt(+x: Nat, +n1: Nat, +n2: Nat, h: SB.Le(1n+n1, n2), f1: Bits(x, n1), f2: Bits(x, n2)) -> Empty:
  (lo1, hi1) = f1
  (lo2, hi2) = f2
  lt_irrefl(Nat.add(x, x), O.le_trans(1n+Nat.add(x, x), RW.pw(1n+n1), Nat.add(x, x), bits_lt.lo(x, n1, lo1),
    O.le_trans(RW.pw(1n+n1), RW.pw(n2), Nat.add(x, x), pw_mono(1n+n1, n2, h), hi2)))

def bits_uniq.go(c: Cmp, +x: Nat, +n1: Nat, +n2: Nat, e: {c == Nat.cmp(n1, n2) : Cmp}, f1: Bits(x, n1), f2: Bits(x, n2)) -> {n1 == n2 : Nat}:
  match c:
    case LT{}:
      absurd({n1 == n2 : Nat}, bits_lt(x, n1, n2, O.cmp_lt(n1, n2, e), f1, f2))
    case EQ{}:
      NR.nat_cmp_eq(n1, n2, e)
    case GT{}:
      absurd({n1 == n2 : Nat}, bits_lt(x, n2, n1, O.cmp_gt(n1, n2, e), f2, f1))

# the bit length is unique
def bits_uniq(+x: Nat, +n1: Nat, +n2: Nat, f1: Bits(x, n1), f2: Bits(x, n2)) -> {n1 == n2 : Nat}:
  bits_uniq.go(Nat.cmp(n1, n2), x, n1, n2, {==}, f1, f2)

# the spec's bit length
def size_bits(p: S.Pos) -> Bits(S.Pos.nat(p), QRD.size(p)):
  match p:
    case S.XH{}:
      bits_one(1n, (0n, {==}), (0n, {==}))
    case S.XO{+q}:
      bits_dbl(S.Pos.nat(S.XO{q}), S.Pos.nat(q), 0n, QRD.size(q), (1n, {==}), NR.ring_eq([S.Pos.nat(q)], NR.NAdd{NR.NCst{0n}, NR.NMul{NR.NVar{0n}, NR.NCst{2n}}}, NR.NDbl{NR.NVar{0n}}, {==}), size_bits(q))
    case S.XI{+q}:
      bits_dbl(S.Pos.nat(S.XI{q}), S.Pos.nat(q), 1n, QRD.size(q), (0n, {==}), NR.ring_eq([S.Pos.nat(q)], NR.NAdd{NR.NCst{1n}, NR.NMul{NR.NVar{0n}, NR.NCst{2n}}}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{0n}}}, {==}), size_bits(q))

# a limb's bit length
# ...................

def nb_zero(g: Nat) -> {RW.Mag.nb(g, 0n) == 0n : Nat}:
  match g:
    case 0n:
      {==}
    case 1n+h:
      {==}

# x = (x mod 2) + (x div 2) 2
def half_eq(+x: Nat) -> {Nat.add(Nat.mod(x, 2n), Nat.mul(Nat.div(x, 2n), 2n)) == x : Nat}:
  Equal.sym(Nat, x, Nat.add(Nat.mod(x, 2n), Nat.mul(Nat.div(x, 2n), 2n)), O.divmod_eq(x, 1n))

def nb_c.lo1(+x: Nat, hy: {Nat.div(x, 2n) == 0n : Nat}) -> SB.Le(x, 1n):
  %half_eq(x) : SB.Le(_, 1n)
  %Equal.sym(Nat, Nat.div(x, 2n), 0n, hy) : SB.Le(Nat.add(Nat.mod(x, 2n), Nat.mul(_, 2n)), 1n)
  %N.add_zero(Nat.mod(x, 2n)) : SB.Le(_, 1n)
  O.mod_le(x, 1n)

def nb_c.lo(+x: Nat, +y: Nat, hy: {Nat.div(x, 2n) == y : Nat}) -> {Nat.add(Nat.mod(x, 2n), Nat.mul(y, 2n)) == x : Nat}:
  %hy : {Nat.add(Nat.mod(x, 2n), Nat.mul(_, 2n)) == x : Nat}
  half_eq(x)

# 2 y <= x < 2^(1 + g) gives y < 2^g
def nb_c.hf(+x: Nat, +y: Nat, +g: Nat, hx: {Nat.add(Nat.mod(x, 2n), Nat.mul(y, 2n)) == x : Nat}, hf: SB.Le(1n+x, RW.pw(1n+g))) -> SB.Le(1n+y, RW.pw(g)):
  lt_cancel(y, RW.pw(g), 1n, O.le_trans(1n+Nat.mul(y, 2n), 1n+x, Nat.mul(RW.pw(g), 2n),
    O.le_succ(Nat.mul(y, 2n), x, (%hx : SB.Le(Nat.mul(y, 2n), _)
      le_addl(Nat.mod(x, 2n), Nat.mul(y, 2n)))),
    (%NR.ring_eq([RW.pw(g)], NR.NMul{NR.NCst{2n}, NR.NVar{0n}}, NR.NMul{NR.NVar{0n}, NR.NCst{2n}}, {==}) : SB.Le(1n+x, _)
      hf)))

def nb_bits.c(+g: Nat, +x: Nat, y: Nat, +hy: {Nat.div(x, 2n) == y : Nat}, h1: SB.Le(1n, x), hf: SB.Le(1n+x, RW.pw(1n+g)), ih: @z: Nat -> SB.Le(1n, z) -> SB.Le(1n+z, RW.pw(g)) -> Bits(z, RW.Mag.nb(g, z))) -> Bits(x, 1n+RW.Mag.nb(g, y)):
  match y:
    case 0n:
      %Equal.sym(Nat, RW.Mag.nb(g, 0n), 0n, nb_zero(g)) : Bits(x, 1n+_)
      bits_one(x, h1, nb_c.lo1(x, hy))
    case 1n++z:
      bits_dbl(x, 1n+z, Nat.mod(x, 2n), RW.Mag.nb(g, 1n+z), O.mod_le(x, 1n), nb_c.lo(x, 1n+z, hy),
        ih(1n+z, (z, {==}), nb_c.hf(x, 1n+z, g, nb_c.lo(x, 1n+z, hy), hf)))

# the bit length of a limb x >= 1, given fuel f with x < 2^f
def nb_bits(f: Nat, +x: Nat, h1: SB.Le(1n, x), hf: SB.Le(1n+x, RW.pw(f))) -> Bits(x, RW.Mag.nb(f, x)):
  match f x:
    case 0n x:
      absurd(Bits(x, RW.Mag.nb(0n, x)), lt_irrefl(0n, O.le_trans(1n, x, 0n, h1, O.le_pred(x, 0n, hf))))
    case 1n++g 0n:
      absurd(Bits(0n, RW.Mag.nb(1n+g, 0n)), lt_irrefl(0n, h1))
    case 1n++g 1n++j:
      nb_bits.c(g, 1n+j, Nat.div(1n+j, 2n), {==}, h1, hf, z => a => b => nb_bits(g, z, a, b))

# No high zero limb
# -----------------

def top.c(t: List<&2, Nat>, h: Nat) -> Data:
  match t:
    case Nil{}:
      SB.Le(1n, h)
    case Con{h2, t2}:
      top.c(t2, h2)

# m has no high zero limb
def Top(m: List<&2, Nat>) -> Data:
  match m:
    case Nil{}:
      Unit
    case Con{h, t}:
      top.c(t, h)

# m is not zero and has no high zero limb
def TopC(m: List<&2, Nat>) -> Data:
  match m:
    case Nil{}:
      Empty
    case Con{h, t}:
      top.c(t, h)

def topc_cons(-h: Nat, g: List<&2, Nat>, tg: TopC(g)) -> top.c(g, h):
  match g:
    case Nil{}:
      absurd(top.c(Nil{}, h), tg)
    case Con{a, b}:
      tg

# h < B = 2^(1 + lp)
def limb_lt(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +h: Nat, lh: SB.Le(h, bp)) -> SB.Le(1n+h, RW.pw(1n+lp)):
  %Equal.sym(Nat, RW.pw(1n+lp), 1n+bp, hb) : SB.Le(1n+h, _)
  O.le_succ(h, bp, lh)

# a magnitude's bit length
# ........................

def bits_limb.lo(+h: Nat, +v: Nat, +n: Nat, +bp: Nat, lh: SB.Le(h, bp), lo: SB.Le(1n+v, RW.pw(n))) -> SB.Le(1n+Nat.add(h, Nat.mul(v, 1n+bp)), Nat.mul(1n+bp, RW.pw(n))):
  O.le_trans(1n+Nat.add(h, Nat.mul(v, 1n+bp)), Nat.mul(1n+v, 1n+bp), Nat.mul(1n+bp, RW.pw(n)),
    O.le_add_mono(1n+h, 1n+bp, Nat.mul(v, 1n+bp), Nat.mul(v, 1n+bp), O.le_succ(h, bp, lh), O.le_refl(Nat.mul(v, 1n+bp))),
    (%NR.ring_eq([RW.pw(n), bp], NR.NMul{NR.NVar{0n}, NR.NAdd{NR.NCst{1n}, NR.NVar{1n}}}, NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NVar{1n}}, NR.NVar{0n}}, {==}) : SB.Le(Nat.mul(1n+v, 1n+bp), _)
      O.le_mul_mono(1n+v, RW.pw(n), 1n+bp, 1n+bp, lo, O.le_refl(1n+bp))))

def bits_limb.hi(+h: Nat, +v: Nat, +n: Nat, +bp: Nat, hi: SB.Le(RW.pw(n), Nat.add(v, v))) -> SB.Le(Nat.mul(1n+bp, RW.pw(n)), Nat.add(Nat.add(h, Nat.mul(v, 1n+bp)), Nat.add(h, Nat.mul(v, 1n+bp)))):
  O.le_trans(Nat.mul(1n+bp, RW.pw(n)), Nat.add(Nat.mul(v, 1n+bp), Nat.mul(v, 1n+bp)), Nat.add(Nat.add(h, Nat.mul(v, 1n+bp)), Nat.add(h, Nat.mul(v, 1n+bp))),
    (%NR.ring_eq([v, bp], NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NVar{1n}}, NR.NAdd{NR.NVar{0n}, NR.NVar{0n}}}, NR.NAdd{NR.NMul{NR.NVar{0n}, NR.NAdd{NR.NCst{1n}, NR.NVar{1n}}}, NR.NMul{NR.NVar{0n}, NR.NAdd{NR.NCst{1n}, NR.NVar{1n}}}}, {==}) : SB.Le(Nat.mul(1n+bp, RW.pw(n)), _)
      O.le_mul_mono(1n+bp, 1n+bp, RW.pw(n), Nat.add(v, v), O.le_refl(1n+bp), hi)),
    O.le_add_mono(Nat.mul(v, 1n+bp), Nat.add(h, Nat.mul(v, 1n+bp)), Nat.mul(v, 1n+bp), Nat.add(h, Nat.mul(v, 1n+bp)), le_addl(h, Nat.mul(v, 1n+bp)), le_addl(h, Nat.mul(v, 1n+bp))))


# a limb below: L bits longer
def bits_limb(+h: Nat, +v: Nat, +n: Nat, +bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, lh: SB.Le(h, bp), f: Bits(v, n)) -> Bits(Nat.add(h, Nat.mul(v, 1n+bp)), Nat.add(1n+lp, n)):
  (lo, hi) = f
  %pw_add(1n+lp, n) : M.Both(SB.Le(1n+Nat.add(h, Nat.mul(v, 1n+bp)), _), SB.Le(_, Nat.add(Nat.add(h, Nat.mul(v, 1n+bp)), Nat.add(h, Nat.mul(v, 1n+bp)))))
  %Equal.sym(Nat, RW.pw(1n+lp), 1n+bp, hb) : M.Both(SB.Le(1n+Nat.add(h, Nat.mul(v, 1n+bp)), Nat.mul(_, RW.pw(n))), SB.Le(Nat.mul(_, RW.pw(n)), Nat.add(Nat.add(h, Nat.mul(v, 1n+bp)), Nat.add(h, Nat.mul(v, 1n+bp)))))
  (bits_limb.lo(h, v, n, bp, lh, lo), bits_limb.hi(h, v, n, bp, hi))

def bits_go(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, t: List<&2, Nat>, +h: Nat, w: SB.Mag.wf(bp, Con{h, t}), tc: top.c(t, h)) -> Bits(SB.Mag.val(bp, Con{h, t}), RW.Mag.bits.go(lp, t, h)):
  match t:
    case Nil{}:
      (lh, wt) = w
      %N.add_zero(h) : Bits(_, RW.Mag.nb(2n+lp, h))
      nb_bits(2n+lp, h, tc, O.le_trans(1n+h, RW.pw(1n+lp), RW.pw(2n+lp), limb_lt(bp, lp, hb, h, lh), pw_mono(1n+lp, 2n+lp, O.le_weaken(1n+lp, 2n+lp, O.le_refl(2n+lp)))))
    case Con{+h2, +t2}:
      (lh, wt) = w
      bits_limb(h, SB.Mag.val(bp, Con{h2, t2}), RW.Mag.bits.go(lp, t2, h2), bp, lp, hb, lh, bits_go(bp, lp, hb, t2, h2, wt, tc))

# Mag.bits is the bit length of a nonzero magnitude with no high zero limb
def bits_ok(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, m: List<&2, Nat>, wm: SB.Mag.wf(bp, m), tm: TopC(m)) -> Bits(SB.Mag.val(bp, m), RW.Mag.bits(lp, m)):
  match m:
    case Nil{}:
      absurd(Bits(0n, 0n), tm)
    case Con{+h, +t}:
      bits_go(bp, lp, hb, t, h, wm, tm)

# Positives into limbs
# --------------------


def hw_init(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}) -> {Nat.mul(1n, RW.pw(1n+lp)) == 1n+bp : Nat}:
  %N.add_zero(RW.pw(1n+lp)) : {_ == 1n+bp : Nat}
  hb

def hw_step(+bp: Nat, +w: Nat, +i: Nat, hw: {Nat.mul(w, RW.pw(2n+i)) == 1n+bp : Nat}) -> {Nat.mul(Nat.mul(2n, w), RW.pw(1n+i)) == 1n+bp : Nat}:
  %NR.ring_eq([w, RW.pw(1n+i)], NR.NMul{NR.NVar{0n}, NR.NMul{NR.NCst{2n}, NR.NVar{1n}}}, NR.NMul{NR.NMul{NR.NCst{2n}, NR.NVar{0n}}, NR.NVar{1n}}, {==}) : {_ == 1n+bp : Nat}
  hw

# p's bits placed from w on: cur + w p, given w 2^(c + 1) = B
def ofpos_val(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, p: S.Pos, c: Nat, +cur: Nat, +w: Nat, +hw: {Nat.mul(w, RW.pw(1n+c)) == 1n+bp : Nat}) -> {Nat.add(cur, Nat.mul(w, S.Pos.nat(p))) == SB.Mag.val(bp, RW.Mag.ofpos.go(lp, p, c, cur, w)) : Nat}:
  match p:
    case S.XH{}:
      NR.ring_eq([cur, w, bp], NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{1n}, NR.NCst{1n}}}, NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}, NR.NMul{NR.NCst{0n}, NR.NAdd{NR.NCst{1n}, NR.NVar{2n}}}}, {==})
    case S.XO{+q}:
      match c:
        case 0n:
          %ofpos_val(bp, lp, hb, q, lp, 0n, 1n, hw_init(bp, lp, hb)) : {Nat.add(cur, Nat.mul(w, S.Pos.nat(S.XO{q}))) == Nat.add(cur, Nat.mul(_, 1n+bp)) : Nat}
          %hw : {Nat.add(cur, Nat.mul(w, S.Pos.nat(S.XO{q}))) == Nat.add(cur, Nat.mul(Nat.add(0n, Nat.mul(1n, S.Pos.nat(q))), _)) : Nat}
          NR.ring_eq([cur, w, S.Pos.nat(q)], NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{1n}, NR.NDbl{NR.NVar{2n}}}}, NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NAdd{NR.NCst{0n}, NR.NMul{NR.NCst{1n}, NR.NVar{2n}}}, NR.NMul{NR.NVar{1n}, NR.NCst{2n}}}}, {==})
        case 1n++i:
          %ofpos_val(bp, lp, hb, q, i, cur, Nat.mul(2n, w), hw_step(bp, w, i, hw)) : {Nat.add(cur, Nat.mul(w, S.Pos.nat(S.XO{q}))) == _ : Nat}
          NR.ring_eq([cur, w, S.Pos.nat(q)], NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{1n}, NR.NDbl{NR.NVar{2n}}}}, NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NMul{NR.NCst{2n}, NR.NVar{1n}}, NR.NVar{2n}}}, {==})
    case S.XI{+q}:
      match c:
        case 0n:
          %ofpos_val(bp, lp, hb, q, lp, 0n, 1n, hw_init(bp, lp, hb)) : {Nat.add(cur, Nat.mul(w, S.Pos.nat(S.XI{q}))) == Nat.add(Nat.add(cur, w), Nat.mul(_, 1n+bp)) : Nat}
          %hw : {Nat.add(cur, Nat.mul(w, S.Pos.nat(S.XI{q}))) == Nat.add(Nat.add(cur, w), Nat.mul(Nat.add(0n, Nat.mul(1n, S.Pos.nat(q))), _)) : Nat}
          NR.ring_eq([cur, w, S.Pos.nat(q)], NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{1n}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{2n}}}}}, NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}, NR.NMul{NR.NAdd{NR.NCst{0n}, NR.NMul{NR.NCst{1n}, NR.NVar{2n}}}, NR.NMul{NR.NVar{1n}, NR.NCst{2n}}}}, {==})
        case 1n++i:
          %ofpos_val(bp, lp, hb, q, i, Nat.add(cur, w), Nat.mul(2n, w), hw_step(bp, w, i, hw)) : {Nat.add(cur, Nat.mul(w, S.Pos.nat(S.XI{q}))) == _ : Nat}
          NR.ring_eq([cur, w, S.Pos.nat(q)], NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{1n}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{2n}}}}}, NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}, NR.NMul{NR.NMul{NR.NCst{2n}, NR.NVar{1n}}, NR.NVar{2n}}}, {==})

# 2 w <= w 2^(c + 1) = B
def ww_le(+bp: Nat, +w: Nat, +c: Nat, hw: {Nat.mul(w, RW.pw(1n+c)) == 1n+bp : Nat}) -> SB.Le(Nat.add(w, w), 1n+bp):
  %hw : SB.Le(Nat.add(w, w), _)
  %NR.ring_eq([w], NR.NMul{NR.NVar{0n}, NR.NCst{2n}}, NR.NAdd{NR.NVar{0n}, NR.NVar{0n}}, {==}) : SB.Le(_, Nat.mul(w, RW.pw(1n+c)))
  O.le_mul_mono(w, w, 2n, RW.pw(1n+c), O.le_refl(w), O.le_mul_mono(2n, 2n, 1n, RW.pw(c), O.le_refl(2n), pw_pos(c)))

# cur + w <= bp
def cw_le(+bp: Nat, +cur: Nat, +w: Nat, +c: Nat, hw: {Nat.mul(w, RW.pw(1n+c)) == 1n+bp : Nat}, hc: SB.Le(1n+cur, w)) -> SB.Le(Nat.add(cur, w), bp):
  O.le_pred(Nat.add(cur, w), bp, O.le_trans(1n+Nat.add(cur, w), Nat.add(w, w), 1n+bp,
    O.le_add_mono(1n+cur, w, w, w, hc, O.le_refl(w)), ww_le(bp, w, c, hw)))

# cur <= bp
def c_le(+bp: Nat, +cur: Nat, +w: Nat, +c: Nat, hw: {Nat.mul(w, RW.pw(1n+c)) == 1n+bp : Nat}, hc: SB.Le(1n+cur, w)) -> SB.Le(cur, bp):
  O.le_pred(cur, bp, O.le_trans(1n+cur, Nat.add(w, w), 1n+bp, O.le_trans(1n+cur, w, Nat.add(w, w), hc, le_addl(w, w)), ww_le(bp, w, c, hw)))

def c2w(+cur: Nat, +w: Nat, hc: SB.Le(1n+cur, w)) -> SB.Le(1n+cur, Nat.mul(2n, w)):
  O.le_trans(1n+cur, w, Nat.mul(2n, w), hc, (%NR.ring_eq([w], NR.NAdd{NR.NVar{0n}, NR.NVar{0n}}, NR.NMul{NR.NCst{2n}, NR.NVar{0n}}, {==}) : SB.Le(w, _)
    le_addl(w, w)))

def cw2w(+cur: Nat, +w: Nat, hc: SB.Le(1n+cur, w)) -> SB.Le(1n+Nat.add(cur, w), Nat.mul(2n, w)):
  (%NR.ring_eq([w], NR.NAdd{NR.NVar{0n}, NR.NVar{0n}}, NR.NMul{NR.NCst{2n}, NR.NVar{0n}}, {==}) : SB.Le(1n+Nat.add(cur, w), _)
    O.le_add_mono(1n+cur, w, w, w, hc, O.le_refl(w)))

def cw_pos(+cur: Nat, +w: Nat, hc: SB.Le(1n+cur, w)) -> SB.Le(1n, Nat.add(cur, w)):
  O.le_trans(1n, w, Nat.add(cur, w), O.le_trans(1n, 1n+cur, w, O.le_succ(0n, cur, (cur, {==})), hc), le_addl(cur, w))

def ofpos_ok.con(+bp: Nat, -h: Nat, g: List<&2, Nat>, lh: SB.Le(h, bp), r: M.Both(SB.Mag.wf(bp, g), TopC(g))) -> M.Both(SB.Mag.wf(bp, Con{h, g}), TopC(Con{h, g})):
  (wg, tg) = r
  ((lh, wg), topc_cons(h, g, tg))

# every limb below the base, and the top one not zero
def ofpos_ok(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, p: S.Pos, c: Nat, +cur: Nat, +w: Nat, +hw: {Nat.mul(w, RW.pw(1n+c)) == 1n+bp : Nat}, +hc: SB.Le(1n+cur, w)) -> M.Both(SB.Mag.wf(bp, RW.Mag.ofpos.go(lp, p, c, cur, w)), TopC(RW.Mag.ofpos.go(lp, p, c, cur, w))):
  match p:
    case S.XH{}:
      ((cw_le(bp, cur, w, c, hw, hc), Unit{}), cw_pos(cur, w, hc))
    case S.XO{+q}:
      match c:
        case 0n:
          ofpos_ok.con(bp, cur, RW.Mag.ofpos.go(lp, q, lp, 0n, 1n), c_le(bp, cur, w, 0n, hw, hc), ofpos_ok(bp, lp, hb, q, lp, 0n, 1n, hw_init(bp, lp, hb), (0n, {==})))
        case 1n++i:
          ofpos_ok(bp, lp, hb, q, i, cur, Nat.mul(2n, w), hw_step(bp, w, i, hw), c2w(cur, w, hc))
    case S.XI{+q}:
      match c:
        case 0n:
          ofpos_ok.con(bp, Nat.add(cur, w), RW.Mag.ofpos.go(lp, q, lp, 0n, 1n), cw_le(bp, cur, w, 0n, hw, hc), ofpos_ok(bp, lp, hb, q, lp, 0n, 1n, hw_init(bp, lp, hb), (0n, {==})))
        case 1n++i:
          ofpos_ok(bp, lp, hb, q, i, Nat.add(cur, w), Nat.mul(2n, w), hw_step(bp, w, i, hw), cw2w(cur, w, hc))

def both_l(-A: Data, -B: Data, h: M.Both(A, B)) -> A:
  (a, b) = h
  a

def both_r(-A: Data, -B: Data, h: M.Both(A, B)) -> B:
  (a, b) = h
  b

def topc_top(m: List<&2, Nat>, h: TopC(m)) -> Top(m):
  match m:
    case Nil{}:
      absurd(Unit, h)
    case Con{a, b}:
      h


# Mag.ofpos is p, in limbs: its value, its limbs, its top and its bit length
def ofpos_nat(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +p: S.Pos) -> {S.Pos.nat(p) == SB.Mag.val(bp, RW.Mag.ofpos(lp, p)) : Nat}:
  %NR.ring_eq([S.Pos.nat(p)], NR.NAdd{NR.NCst{0n}, NR.NMul{NR.NCst{1n}, NR.NVar{0n}}}, NR.NVar{0n}, {==}) : {_ == SB.Mag.val(bp, RW.Mag.ofpos(lp, p)) : Nat}
  ofpos_val(bp, lp, hb, p, lp, 0n, 1n, hw_init(bp, lp, hb))

def ofpos_wf(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +p: S.Pos) -> SB.Mag.wf(bp, RW.Mag.ofpos(lp, p)):
  both_l(SB.Mag.wf(bp, RW.Mag.ofpos(lp, p)), TopC(RW.Mag.ofpos(lp, p)), ofpos_ok(bp, lp, hb, p, lp, 0n, 1n, hw_init(bp, lp, hb), (0n, {==})))

def ofpos_topc(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +p: S.Pos) -> TopC(RW.Mag.ofpos(lp, p)):
  both_r(SB.Mag.wf(bp, RW.Mag.ofpos(lp, p)), TopC(RW.Mag.ofpos(lp, p)), ofpos_ok(bp, lp, hb, p, lp, 0n, 1n, hw_init(bp, lp, hb), (0n, {==})))

def ofpos_bits(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +p: S.Pos) -> {RW.Mag.bits(lp, RW.Mag.ofpos(lp, p)) == QRD.size(p) : Nat}:
  bits_uniq(S.Pos.nat(p), RW.Mag.bits(lp, RW.Mag.ofpos(lp, p)), QRD.size(p),
    (%Equal.sym(Nat, S.Pos.nat(p), SB.Mag.val(bp, RW.Mag.ofpos(lp, p)), ofpos_nat(bp, lp, hb, p)) : Bits(_, RW.Mag.bits(lp, RW.Mag.ofpos(lp, p)))
      bits_ok(bp, lp, hb, RW.Mag.ofpos(lp, p), ofpos_wf(bp, lp, hb, p), ofpos_topc(bp, lp, hb, p))),
    size_bits(p))

# Limbs into positives
# --------------------

# a positive's value, zero for None
def mv(r: Maybe<&2, S.Pos>) -> Nat:
  match r:
    case None{}:
      0n
    case Some{p}:
      S.Pos.nat(p)

def one_bit(+j: Nat, hb: SB.Le(1n+j, 1n)) -> {0n == j : Nat}:
  Equal.sym(Nat, j, 0n, O.le_zero(j, O.le_pred(j, 0n, hb)))

def lbbit0(r: Maybe<&2, S.Pos>) -> {Nat.add(0n, Nat.mul(2n, mv(r))) == mv(RW.Mag.lb.bit(0n, r)) : Nat}:
  match r:
    case None{}:
      {==}
    case Some{+q}:
      NR.ring_eq([S.Pos.nat(q)], NR.NAdd{NR.NCst{0n}, NR.NMul{NR.NCst{2n}, NR.NVar{0n}}}, NR.NDbl{NR.NVar{0n}}, {==})

def lbbit1(r: Maybe<&2, S.Pos>) -> {Nat.add(1n, Nat.mul(2n, mv(r))) == mv(RW.Mag.lb.bit(1n, r)) : Nat}:
  match r:
    case None{}:
      {==}
    case Some{+q}:
      NR.ring_eq([S.Pos.nat(q)], NR.NAdd{NR.NCst{1n}, NR.NMul{NR.NCst{2n}, NR.NVar{0n}}}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{0n}}}, {==})

def lbbit_val(b: Nat, r: Maybe<&2, S.Pos>, hb: SB.Le(b, 1n)) -> {Nat.add(b, Nat.mul(2n, mv(r))) == mv(RW.Mag.lb.bit(b, r)) : Nat}:
  match b:
    case 0n:
      lbbit0(r)
    case 1n++j:
      %one_bit(j, hb) : {Nat.add(1n+_, Nat.mul(2n, mv(r))) == mv(RW.Mag.lb.bit(1n+_, r)) : Nat}
      lbbit1(r)

# h + 2^k hi, for h < 2^k
def lb_val(k: Nat, +h: Nat, +hi: Maybe<&2, S.Pos>, hh: SB.Le(1n+h, RW.pw(k))) -> {Nat.add(h, Nat.mul(RW.pw(k), mv(hi))) == mv(RW.Mag.lb(k, h, hi)) : Nat}:
  match k:
    case 0n:
      %Equal.sym(Nat, h, 0n, O.le_zero(h, O.le_pred(h, 0n, hh))) : {Nat.add(_, Nat.mul(1n, mv(hi))) == mv(hi) : Nat}
      NR.ring_eq([mv(hi)], NR.NAdd{NR.NCst{0n}, NR.NMul{NR.NCst{1n}, NR.NVar{0n}}}, NR.NVar{0n}, {==})
    case 1n++j:
      %lbbit_val(Nat.mod(h, 2n), RW.Mag.lb(j, Nat.div(h, 2n), hi), O.mod_le(h, 1n)) : {Nat.add(h, Nat.mul(RW.pw(1n+j), mv(hi))) == _ : Nat}
      %lb_val(j, Nat.div(h, 2n), hi, nb_c.hf(h, Nat.div(h, 2n), j, half_eq(h), hh)) : {Nat.add(h, Nat.mul(RW.pw(1n+j), mv(hi))) == Nat.add(Nat.mod(h, 2n), Nat.mul(2n, _)) : Nat}
      %half_eq(h) : {Nat.add(_, Nat.mul(RW.pw(1n+j), mv(hi))) == Nat.add(Nat.mod(h, 2n), Nat.mul(2n, Nat.add(Nat.div(h, 2n), Nat.mul(RW.pw(j), mv(hi))))) : Nat}
      NR.ring_eq([Nat.mod(h, 2n), Nat.div(h, 2n), RW.pw(j), mv(hi)], NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{1n}, NR.NCst{2n}}}, NR.NMul{NR.NMul{NR.NCst{2n}, NR.NVar{2n}}, NR.NVar{3n}}}, NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NCst{2n}, NR.NAdd{NR.NVar{1n}, NR.NMul{NR.NVar{2n}, NR.NVar{3n}}}}}, {==})

# Mag.topos is m's value
def topos_val(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, m: List<&2, Nat>, wm: SB.Mag.wf(bp, m)) -> {SB.Mag.val(bp, m) == mv(RW.Mag.topos(lp, m)) : Nat}:
  match m:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      (lh, wt) = wm
      %lb_val(1n+lp, h, RW.Mag.topos(lp, t), limb_lt(bp, lp, hb, h, lh)) : {SB.Mag.val(bp, Con{h, t}) == _ : Nat}
      %topos_val(bp, lp, hb, t, wt) : {SB.Mag.val(bp, Con{h, t}) == Nat.add(h, Nat.mul(RW.pw(1n+lp), _)) : Nat}
      %Equal.sym(Nat, RW.pw(1n+lp), 1n+bp, hb) : {SB.Mag.val(bp, Con{h, t}) == Nat.add(h, Nat.mul(_, SB.Mag.val(bp, t))) : Nat}
      NR.ring_eq([h, SB.Mag.val(bp, t), bp], NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{1n}, NR.NAdd{NR.NCst{1n}, NR.NVar{2n}}}}, NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NVar{2n}}, NR.NVar{1n}}}, {==})

def some_eq(-q: S.Pos, -p: S.Pos, e: {q == p : S.Pos}) -> {Some{q} == Some{p} : Maybe<&2, S.Pos>}:
  %e : {Some{q} == Some{_} : Maybe<&2, S.Pos>}
  {==}

def zero_succ(-k: Nat, e: {0n == 1n+k : Nat}) -> Empty:
  %Equal.sym(Nat, 0n, 1n+k, e) : N.NatD(_, Empty, Unit)
  Unit{}

# a positive's value pins it down
def mv_some(r: Maybe<&2, S.Pos>, +p: S.Pos, e: {mv(r) == S.Pos.nat(p) : Nat}) -> {r == Some{p} : Maybe<&2, S.Pos>}:
  match r:
    case None{}:
      absurd({None{} == Some{p} : Maybe<&2, S.Pos>}, zero_succ(P.pm1(p), Equal.trans(Nat, 0n, S.Pos.nat(p), 1n+P.pm1(p), e, P.nat_form(p))))
    case Some{+q}:
      some_eq(q, p, P.nat_inj(q, p, e))

# back from limbs: Mag.topos(Mag.ofpos(p)) = p
def topos_ofpos(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +p: S.Pos) -> {RW.Mag.topos(lp, RW.Mag.ofpos(lp, p)) == Some{p} : Maybe<&2, S.Pos>}:
  mv_some(RW.Mag.topos(lp, RW.Mag.ofpos(lp, p)), p, Equal.sym(Nat, S.Pos.nat(p), mv(RW.Mag.topos(lp, RW.Mag.ofpos(lp, p))), Equal.trans(Nat, S.Pos.nat(p), SB.Mag.val(bp, RW.Mag.ofpos(lp, p)), mv(RW.Mag.topos(lp, RW.Mag.ofpos(lp, p))), ofpos_nat(bp, lp, hb, p), topos_val(bp, lp, hb, RW.Mag.ofpos(lp, p), ofpos_wf(bp, lp, hb, p)))))

# One magnitude per value
# -----------------------

def le_vb(+bp: Nat, +h: Nat, +v: Nat) -> SB.Le(v, Nat.add(h, Nat.mul(v, 1n+bp))):
  O.le_trans(v, Nat.mul(v, 1n+bp), Nat.add(h, Nat.mul(v, 1n+bp)), (Nat.mul(v, bp), NR.ring_eq([v, bp], NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{0n}, NR.NVar{1n}}}, NR.NMul{NR.NVar{0n}, NR.NAdd{NR.NCst{1n}, NR.NVar{1n}}}, {==})), le_addl(h, Nat.mul(v, 1n+bp)))

# a nonzero top limb: 1 <= m
def top_pos(+bp: Nat, t: List<&2, Nat>, +h: Nat, tc: top.c(t, h)) -> SB.Le(1n, SB.Mag.val(bp, Con{h, t})):
  match t:
    case Nil{}:
      %N.add_zero(h) : SB.Le(1n, _)
      tc
    case Con{+h2, +t2}:
      O.le_trans(1n, SB.Mag.val(bp, Con{h2, t2}), SB.Mag.val(bp, Con{h, Con{h2, t2}}), top_pos(bp, t2, h2, tc), le_vb(bp, h, SB.Mag.val(bp, Con{h2, t2})))

def top_tail(t: List<&2, Nat>, -h: Nat, tc: top.c(t, h)) -> Top(t):
  match t:
    case Nil{}:
      Unit{}
    case Con{h2, t2}:
      tc


# h1 + v1 B < h2 + v2 B when v1 < v2
def digit_lt(+bp: Nat, +h1: Nat, +v1: Nat, +h2: Nat, +v2: Nat, lh1: SB.Le(h1, bp), hv: SB.Le(1n+v1, v2)) -> SB.Le(1n+Nat.add(h1, Nat.mul(v1, 1n+bp)), Nat.add(h2, Nat.mul(v2, 1n+bp))):
  O.le_trans(1n+Nat.add(h1, Nat.mul(v1, 1n+bp)), Nat.mul(1n+v1, 1n+bp), Nat.add(h2, Nat.mul(v2, 1n+bp)),
    O.le_add_mono(1n+h1, 1n+bp, Nat.mul(v1, 1n+bp), Nat.mul(v1, 1n+bp), O.le_succ(h1, bp, lh1), O.le_refl(Nat.mul(v1, 1n+bp))),
    O.le_trans(Nat.mul(1n+v1, 1n+bp), Nat.mul(v2, 1n+bp), Nat.add(h2, Nat.mul(v2, 1n+bp)), O.le_mul_mono(1n+v1, v2, 1n+bp, 1n+bp, hv, O.le_refl(1n+bp)), le_addl(h2, Nat.mul(v2, 1n+bp))))

def lt_eq_no(+x: Nat, +y: Nat, h: SB.Le(1n+x, y), e: {x == y : Nat}) -> Empty:
  lt_irrefl(y, (%e : SB.Le(1n+_, y)
    h))

def digit_v.go(c: Cmp, +bp: Nat, +h1: Nat, +v1: Nat, +h2: Nat, +v2: Nat, e0: {c == Nat.cmp(v1, v2) : Cmp}, lh1: SB.Le(h1, bp), lh2: SB.Le(h2, bp), e: {Nat.add(h1, Nat.mul(v1, 1n+bp)) == Nat.add(h2, Nat.mul(v2, 1n+bp)) : Nat}) -> {v1 == v2 : Nat}:
  match c:
    case LT{}:
      absurd({v1 == v2 : Nat}, lt_eq_no(Nat.add(h1, Nat.mul(v1, 1n+bp)), Nat.add(h2, Nat.mul(v2, 1n+bp)), digit_lt(bp, h1, v1, h2, v2, lh1, O.cmp_lt(v1, v2, e0)), e))
    case EQ{}:
      NR.nat_cmp_eq(v1, v2, e0)
    case GT{}:
      absurd({v1 == v2 : Nat}, lt_eq_no(Nat.add(h2, Nat.mul(v2, 1n+bp)), Nat.add(h1, Nat.mul(v1, 1n+bp)), digit_lt(bp, h2, v2, h1, v1, lh2, O.cmp_gt(v1, v2, e0)), Equal.sym(Nat, Nat.add(h1, Nat.mul(v1, 1n+bp)), Nat.add(h2, Nat.mul(v2, 1n+bp)), e)))

# a number's high part in base B is unique
def digit_v(+bp: Nat, +h1: Nat, +v1: Nat, +h2: Nat, +v2: Nat, lh1: SB.Le(h1, bp), lh2: SB.Le(h2, bp), e: {Nat.add(h1, Nat.mul(v1, 1n+bp)) == Nat.add(h2, Nat.mul(v2, 1n+bp)) : Nat}) -> {v1 == v2 : Nat}:
  digit_v.go(Nat.cmp(v1, v2), bp, h1, v1, h2, v2, {==}, lh1, lh2, e)

def digit_h.e(+bp: Nat, +h1: Nat, +v1: Nat, +h2: Nat, +v2: Nat, ev: {v1 == v2 : Nat}, e: {Nat.add(h1, Nat.mul(v1, 1n+bp)) == Nat.add(h2, Nat.mul(v2, 1n+bp)) : Nat}) -> {Nat.add(Nat.mul(v1, 1n+bp), h1) == Nat.add(Nat.mul(v1, 1n+bp), h2) : Nat}:
  %N.add_comm(h1, Nat.mul(v1, 1n+bp)) : {_ == Nat.add(Nat.mul(v1, 1n+bp), h2) : Nat}
  %N.add_comm(h2, Nat.mul(v1, 1n+bp)) : {Nat.add(h1, Nat.mul(v1, 1n+bp)) == _ : Nat}
  %Equal.sym(Nat, v1, v2, ev) : {Nat.add(h1, Nat.mul(v1, 1n+bp)) == Nat.add(h2, Nat.mul(_, 1n+bp)) : Nat}
  e

# and so is its low digit
def digit_h(+bp: Nat, +h1: Nat, +v1: Nat, +h2: Nat, +v2: Nat, ev: {v1 == v2 : Nat}, e: {Nat.add(h1, Nat.mul(v1, 1n+bp)) == Nat.add(h2, Nat.mul(v2, 1n+bp)) : Nat}) -> {h1 == h2 : Nat}:
  N.add_cancel(Nat.mul(v1, 1n+bp), h1, h2, digit_h.e(bp, h1, v1, h2, v2, ev, e))

def cons_eq(-h1: Nat, -t1: List<&2, Nat>, -h2: Nat, -t2: List<&2, Nat>, eh: {h1 == h2 : Nat}, et: {t1 == t2 : List<&2, Nat>}) -> {Con{h1, t1} == Con{h2, t2} : List<&2, Nat>}:
  %eh : {Con{h1, t1} == Con{_, t2} : List<&2, Nat>}
  %et : {Con{h1, t1} == Con{h1, _} : List<&2, Nat>}
  {==}

# well-formed magnitudes with no high zero limb and the same value are equal
def canon_eq(+bp: Nat, m1: List<&2, Nat>, m2: List<&2, Nat>, w1: SB.Mag.wf(bp, m1), w2: SB.Mag.wf(bp, m2), q1: Top(m1), q2: Top(m2), +e: {SB.Mag.val(bp, m1) == SB.Mag.val(bp, m2) : Nat}) -> {m1 == m2 : List<&2, Nat>}:
  match m1 m2:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+h, +t}:
      absurd({Nil{} == Con{h, t} : List<&2, Nat>}, lt_irrefl(0n, (%Equal.sym(Nat, 0n, SB.Mag.val(bp, Con{h, t}), e) : SB.Le(1n, _)
        top_pos(bp, t, h, q2))))
    case Con{+h, +t} Nil{}:
      absurd({Con{h, t} == Nil{} : List<&2, Nat>}, lt_irrefl(0n, (%e : SB.Le(1n, _)
        top_pos(bp, t, h, q1))))
    case Con{+h1, +t1} Con{+h2, +t2}:
      (+lh1, wt1) = w1
      (+lh2, wt2) = w2
      cons_eq(h1, t1, h2, t2, digit_h(bp, h1, SB.Mag.val(bp, t1), h2, SB.Mag.val(bp, t2), digit_v(bp, h1, SB.Mag.val(bp, t1), h2, SB.Mag.val(bp, t2), lh1, lh2, e), e),
        canon_eq(bp, t1, t2, wt1, wt2, top_tail(t1, h1, q1), top_tail(t2, h2, q2), digit_v(bp, h1, SB.Mag.val(bp, t1), h2, SB.Mag.val(bp, t2), lh1, lh2, e)))

# Mag.norm leaves no high zero limb
def limb_top(h: Nat) -> Top(RM.Mag.limb(h)):
  match h:
    case 0n:
      Unit{}
    case 1n+k:
      (k, {==})

def normcon_top(h: Nat, t: List<&2, Nat>, tt: Top(t)) -> Top(RM.Mag.norm.con(h, t)):
  match t:
    case Nil{}:
      limb_top(h)
    case Con{x, y}:
      tt

def norm_top(m: List<&2, Nat>) -> Top(RM.Mag.norm(m)):
  match m:
    case Nil{}:
      Unit{}
    case Con{h, +t}:
      normcon_top(h, RM.Mag.norm(t), norm_top(t))

# The base
# --------

# RW.wbp(lp) is a base for lp: 2^(1 + lp) = 1 + wbp(lp)
def wbp_ok(+lp: Nat) -> {RW.pw(1n+lp) == 1n+RW.wbp(lp) : Nat}:
  %N.add_comm(Nat.sub(RW.pw(1n+lp), 1n), 1n) : {RW.pw(1n+lp) == _ : Nat}
  Equal.sym(Nat, Nat.add(Nat.sub(RW.pw(1n+lp), 1n), 1n), RW.pw(1n+lp), O.sub_add(RW.pw(1n+lp), 1n, pw_pos(1n+lp)))

# Native bounds
# -------------
# Every native operation on limbs (rt/mag.bend, rt/wmag.bend) is a limb
# times a limb plus a limb (mul1), a sum of two limbs and a carry bit, a
# limb against 2^r with r <= lp = L - 1, or a quotient or remainder of
# these. For limbs up to bp = 2^L - 1 each is below 2^(2 L), so a run whose
# base has 2 L <= n never forms a Nat of n bits; the CLI's L = 12 gives
# 2 L = 24 <= 48 (BendRT's immediates; tests/wmag_demo.bend: l12). The exponent stays a variable: a
# closed 2^48 in a type would be unfolded to unary by the checker.

# (1 + bp)^2 = 2^(2 L)
def base_sq(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}) -> {Nat.mul(1n+bp, 1n+bp) == RW.pw(Nat.add(1n+lp, 1n+lp)) : Nat}:
  %hb : {Nat.mul(_, _) == RW.pw(Nat.add(1n+lp, 1n+lp)) : Nat}
  pw_add(1n+lp, 1n+lp)

# h k + c < 2^(2 L) for limbs h, k, c
def mul_bound(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +h: Nat, +k: Nat, +c: Nat, lh: SB.Le(h, bp), lk: SB.Le(k, bp), lc: SB.Le(c, bp)) -> SB.Le(1n+Nat.add(Nat.mul(h, k), c), RW.pw(Nat.add(1n+lp, 1n+lp))):
  %base_sq(bp, lp, hb) : SB.Le(1n+Nat.add(Nat.mul(h, k), c), _)
  O.le_trans(1n+Nat.add(Nat.mul(h, k), c), 1n+Nat.add(Nat.mul(bp, bp), bp), Nat.mul(1n+bp, 1n+bp),
    O.le_succ(Nat.add(Nat.mul(h, k), c), Nat.add(Nat.mul(bp, bp), bp), O.le_add_mono(Nat.mul(h, k), Nat.mul(bp, bp), c, bp, O.le_mul_mono(h, bp, k, bp, lh, lk), lc)),
    (bp, NR.ring_eq([bp], NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NMul{NR.NVar{0n}, NR.NVar{0n}}, NR.NVar{0n}}}, NR.NVar{0n}}, NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}, {==})))

def add_bound.lo(+bp: Nat, +a: Nat, +b: Nat, +c: Nat, la: SB.Le(a, bp), lb: SB.Le(b, bp), lc: SB.Le(c, 1n)) -> SB.Le(1n+Nat.add(Nat.add(a, b), c), Nat.mul(2n, 1n+bp)):
  (%NR.ring_eq([bp], NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NVar{0n}}, NR.NCst{1n}}}, NR.NMul{NR.NCst{2n}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}, {==}) : SB.Le(1n+Nat.add(Nat.add(a, b), c), _)
    O.le_succ(Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(bp, bp), 1n), O.le_add_mono(Nat.add(a, b), Nat.add(bp, bp), c, 1n, O.le_add_mono(a, bp, b, bp, la, lb), lc)))

# a + b + c < 2^(2 L) for limbs a, b and a bit c
def add_bound(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +a: Nat, +b: Nat, +c: Nat, la: SB.Le(a, bp), lb: SB.Le(b, bp), lc: SB.Le(c, 1n)) -> SB.Le(1n+Nat.add(Nat.add(a, b), c), RW.pw(Nat.add(1n+lp, 1n+lp))):
  %base_sq(bp, lp, hb) : SB.Le(1n+Nat.add(Nat.add(a, b), c), _)
  O.le_trans(1n+Nat.add(Nat.add(a, b), c), Nat.mul(2n, 1n+bp), Nat.mul(1n+bp, 1n+bp), add_bound.lo(bp, a, b, c, la, lb, lc),
    O.le_mul_mono(2n, 1n+bp, 1n+bp, 1n+bp, O.le_succ(1n, bp, bp_pos(bp, lp, hb)), O.le_refl(1n+bp)))
