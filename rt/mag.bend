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
