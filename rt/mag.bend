# Runtime magnitudes: lists of limbs in base 1 + bp, least significant
# first (spec/big.bend says what they mean). Verified in lib/mag.bend. The
# base is a parameter; the runtime passes bp = 65535n at the top.
#
# Carries: each step computes s, emits s mod B and carries s div B (Bend
# cannot destructure a computed pair, so mod and div are separate calls).

import Base

# the magnitude of a single small value c (no limb when c is zero)
def Mag.limb(c: Nat) -> List<&2, Nat>:
  match c:
    case 0n:
      Nil{}
    case 1n+k:
      Con{1n+k, Nil{}}

# a + c
def Mag.addc(+bp: Nat, a: List<&2, Nat>, c: Nat) -> List<&2, Nat>:
  match a:
    case Nil{}:
      Mag.limb(c)
    case Con{h, t}:
      +s = Nat.add(h, c)
      Con{Nat.mod(s, 1n+bp), Mag.addc(bp, t, Nat.div(s, 1n+bp))}

# a + b + c
def Mag.add.go(+bp: Nat, a: List<&2, Nat>, b: List<&2, Nat>, c: Nat) -> List<&2, Nat>:
  match a b:
    case Nil{} Nil{}:
      Mag.limb(c)
    case Nil{} Con{bh, bt}:
      Mag.addc(bp, Con{bh, bt}, c)
    case Con{ah, at} Nil{}:
      Mag.addc(bp, Con{ah, at}, c)
    case Con{ah, at} Con{bh, bt}:
      +s = Nat.add(Nat.add(ah, bh), c)
      Con{Nat.mod(s, 1n+bp), Mag.add.go(bp, at, bt, Nat.div(s, 1n+bp))}

def Mag.add(+bp: Nat, a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  Mag.add.go(bp, a, b, 0n)

# a * k + c, for a single limb k
def Mag.mul1(+bp: Nat, a: List<&2, Nat>, +k: Nat, c: Nat) -> List<&2, Nat>:
  match a:
    case Nil{}:
      Mag.limb(c)
    case Con{h, t}:
      +s = Nat.add(Nat.mul(h, k), c)
      Con{Nat.mod(s, 1n+bp), Mag.mul1(bp, t, k, Nat.div(s, 1n+bp))}

# a * b, schoolbook
def Mag.mul(+bp: Nat, a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  match a:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Mag.add(bp, Mag.mul1(bp, b, h, 0n), Con{0n, Mag.mul(bp, t, b)})

# h below t, dropping h when it would be a high zero
def Mag.norm.con(h: Nat, t: List<&2, Nat>) -> List<&2, Nat>:
  match t:
    case Nil{}:
      Mag.limb(h)
    case Con{x, y}:
      Con{h, Con{x, y}}

# strips high zero limbs
def Mag.norm(m: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Mag.norm.con(h, Mag.norm(t))

# Comparison
# ----------
# Lists are least significant first, so the tails' verdict decides unless
# it is EQ{}, when the low limbs do.

def Mag.cmp.fin(hi: Cmp, ah: Nat, bh: Nat) -> Cmp:
  match hi:
    case LT{}:
      LT{}
    case EQ{}:
      Nat.cmp(ah, bh)
    case GT{}:
      GT{}

# a compared with zero
def Mag.cmpz(a: List<&2, Nat>) -> Cmp:
  match a:
    case Nil{}:
      EQ{}
    case Con{h, t}:
      Mag.cmp.fin(Mag.cmpz(t), h, 0n)

# zero compared with b
def Mag.zcmp(b: List<&2, Nat>) -> Cmp:
  match b:
    case Nil{}:
      EQ{}
    case Con{h, t}:
      Mag.cmp.fin(Mag.zcmp(t), 0n, h)

def Mag.cmp(a: List<&2, Nat>, b: List<&2, Nat>) -> Cmp:
  match a b:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{bh, bt}:
      Mag.zcmp(Con{bh, bt})
    case Con{ah, at} Nil{}:
      Mag.cmpz(Con{ah, at})
    case Con{ah, at} Con{bh, bt}:
      Mag.cmp.fin(Mag.cmp(at, bt), ah, bh)

# Subtraction
# -----------
# a - (b + w) for a borrow bit w, when b + w <= a. At each limb t = bh + w:
# if ah >= t the limb is ah - t and no borrow; else it is B + ah - t and the
# next limb borrows 1. Both differences are exact.

def Mag.borrow.fin(o: Cmp) -> Nat:
  match o:
    case LT{}:
      1n
    case EQ{}:
      0n
    case GT{}:
      0n

# 1 when ah < t
def Mag.borrow(ah: Nat, t: Nat) -> Nat:
  Mag.borrow.fin(Nat.cmp(ah, t))

# what a borrow adds back to the limb: B for w = 1
def Mag.bval(+bp: Nat, w: Nat) -> Nat:
  match w:
    case 0n:
      0n
    case 1n+k:
      1n+bp

def Mag.sub.go(+bp: Nat, a: List<&2, Nat>, b: List<&2, Nat>, w: Nat) -> List<&2, Nat>:
  match a b:
    case Nil{} bb:
      Nil{}
    case Con{+ah, at} Nil{}:
      +t = Nat.add(0n, w)
      +w2 = Mag.borrow(ah, t)
      Con{Nat.sub(Nat.add(Mag.bval(bp, w2), ah), t), Mag.sub.go(bp, at, Nil{}, w2)}
    case Con{+ah, at} Con{bh, bt}:
      +t = Nat.add(bh, w)
      +w2 = Mag.borrow(ah, t)
      Con{Nat.sub(Nat.add(Mag.bval(bp, w2), ah), t), Mag.sub.go(bp, at, bt, w2)}

# a - b, for b <= a
def Mag.sub(+bp: Nat, a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  Mag.norm(Mag.sub.go(bp, a, b, 0n))
