# Runtime magnitudes in a base 2^L, L = 1 + lp (2^12 at run time): shifts,
# bit length, rounding to nearest, and conversions with the spec's binary
# positives. Verified in lib/wmagpf.bend. The rt/mag.bend operations take
# bp = 2^L - 1, so these take bp and lp both.
#
# Every native operation here works on limbs (below 2^L), single-limb
# products and carries, or bit counts.

import Base
import ../spec/num.bend as S
import ./mag.bend as RM

# 2^k
def pw(k: Nat) -> Nat:
  match k:
    case 0n:
      1n
    case 1n+j:
      Nat.mul(2n, pw(j))

# Shifts
# ------

# m B^n: n zero limbs below m
def Mag.zl(n: Nat, m: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      m
    case 1n+j:
      Con{0n, Mag.zl(j, m)}

# m 2^k: with k = q L + r (r < L), q zero limbs below m 2^r
def Mag.shl(+bp: Nat, +lp: Nat, m: List<&2, Nat>, +k: Nat) -> List<&2, Nat>:
  match m:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Mag.zl(Nat.div(k, 1n+lp), RM.Mag.mul1(bp, Con{h, t}, pw(Nat.mod(k, 1n+lp)), 0n))

# floor(m / B^n): m without its n low limbs
def Mag.drop(n: Nat, m: List<&2, Nat>) -> List<&2, Nat>:
  match n m:
    case 0n m:
      m
    case 1n+j Nil{}:
      Nil{}
    case 1n+j Con{h, t}:
      Mag.drop(j, t)

# floor(m / 2^r) for r < L: m 2^(L - r) without its low limb
def Mag.shr.r(+bp: Nat, +lp: Nat, m: List<&2, Nat>, r: Nat) -> List<&2, Nat>:
  match r:
    case 0n:
      m
    case 1n+j:
      Mag.drop(1n, RM.Mag.mul1(bp, m, pw(Nat.sub(lp, j)), 0n))

# floor(m / 2^k)
def Mag.shr(+bp: Nat, +lp: Nat, m: List<&2, Nat>, +k: Nat) -> List<&2, Nat>:
  Mag.shr.r(bp, lp, Mag.drop(Nat.div(k, 1n+lp), m), Nat.mod(k, 1n+lp))

# floor((m + 2^(k-1)) / 2^k): m / 2^k to the nearest, halves up (k >= 1)
def Mag.round(+bp: Nat, +lp: Nat, m: List<&2, Nat>, +k: Nat) -> List<&2, Nat>:
  Mag.shr(bp, lp, RM.Mag.add(bp, m, Mag.shl(bp, lp, Con{1n, Nil{}}, Nat.sub(k, 1n))), k)

# Bit length
# ----------

# the binary digits of x, in at most f steps (f = L + 1 is enough for a limb)
def Mag.nb(f: Nat, x: Nat) -> Nat:
  match f x:
    case 0n x:
      0n
    case 1n+g 0n:
      0n
    case 1n+g 1n+j:
      1n+Mag.nb(g, Nat.div(1n+j, 2n))

def Mag.bits.go(+lp: Nat, t: List<&2, Nat>, h: Nat) -> Nat:
  match t:
    case Nil{}:
      Mag.nb(2n+lp, h)
    case Con{h2, t2}:
      Nat.add(1n+lp, Mag.bits.go(lp, t2, h2))

# the binary digits of m (its top limb not zero)
def Mag.bits(+lp: Nat, m: List<&2, Nat>) -> Nat:
  match m:
    case Nil{}:
      0n
    case Con{h, t}:
      Mag.bits.go(lp, t, h)

# Conversions with the spec's positives
# -------------------------------------

# p's bits into limbs: cur holds the current limb's bits so far, w is the
# place of the next one, and c + 1 places are left in the limb
def Mag.ofpos.go(+lp: Nat, p: S.Pos, c: Nat, cur: Nat, +w: Nat) -> List<&2, Nat>:
  match p:
    case S.XH{}:
      Con{Nat.add(cur, w), Nil{}}
    case S.XO{q}:
      match c:
        case 0n:
          Con{cur, Mag.ofpos.go(lp, q, lp, 0n, 1n)}
        case 1n+i:
          Mag.ofpos.go(lp, q, i, cur, Nat.mul(2n, w))
    case S.XI{q}:
      match c:
        case 0n:
          Con{Nat.add(cur, w), Mag.ofpos.go(lp, q, lp, 0n, 1n)}
        case 1n+i:
          Mag.ofpos.go(lp, q, i, Nat.add(cur, w), Nat.mul(2n, w))

def Mag.ofpos(+lp: Nat, p: S.Pos) -> List<&2, Nat>:
  Mag.ofpos.go(lp, p, lp, 0n, 1n)

def Mag.lb.none(b: Nat) -> Maybe<&2, S.Pos>:
  match b:
    case 0n:
      None{}
    case 1n+j:
      Some{S.XH{}}

def Mag.lb.some(b: Nat, q: S.Pos) -> Maybe<&2, S.Pos>:
  match b:
    case 0n:
      Some{S.XO{q}}
    case 1n+j:
      Some{S.XI{q}}

# b + 2 r, for a bit b
def Mag.lb.bit(b: Nat, r: Maybe<&2, S.Pos>) -> Maybe<&2, S.Pos>:
  match r:
    case None{}:
      Mag.lb.none(b)
    case Some{q}:
      Mag.lb.some(b, q)

# h + 2^k hi, for h < 2^k (None is zero)
def Mag.lb(k: Nat, +h: Nat, hi: Maybe<&2, S.Pos>) -> Maybe<&2, S.Pos>:
  match k:
    case 0n:
      hi
    case 1n+j:
      Mag.lb.bit(Nat.mod(h, 2n), Mag.lb(j, Nat.div(h, 2n), hi))

# m as a positive, None when it is zero
def Mag.topos(+lp: Nat, m: List<&2, Nat>) -> Maybe<&2, S.Pos>:
  match m:
    case Nil{}:
      None{}
    case Con{h, t}:
      Mag.lb(1n+lp, h, Mag.topos(lp, t))

# The base
# --------

# bp for the base 2^(1 + lp), the base the laws are stated at (the CLI's
# instance, lib/fast.bend, writes its bp as a literal)
def wbp(+lp: Nat) -> Nat:
  Nat.sub(pw(1n+lp), 1n)
