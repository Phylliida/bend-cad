# Demos of the binary-coefficient Z normalizer (lib/zring.bend): each
# identity is one ring_eq call, its normal forms compared by {==}.

import Base
import ../lib/zring.bend as R
import ../spec/num.bend as S
import ../spec/ring.bend as E

# 2^k as a positive (the checker builds k binary digits)
def p2(k: Nat) -> S.Pos:
  match k:
    case 0n:
      S.XH{}
    case 1n+j:
      S.XO{p2(j)}

def two() -> S.Z:
  S.Zpos{S.XO{S.XH{}}}

# (a + b)^2 = a^2 + 2ab + b^2
def sq(+a: S.Z, +b: S.Z) -> {S.Z.mul(S.Z.add(a, b), S.Z.add(a, b)) == S.Z.add(S.Z.add(S.Z.mul(a, a), S.Z.mul(two(), S.Z.mul(a, b))), S.Z.mul(b, b)) : S.Z}:
  R.ring_eq([a, b],
    E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}},
    E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{0n}}, E.ZMul{E.ZCst{two()}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}, E.ZMul{E.ZVar{1n}, E.ZVar{1n}}},
    {==})

# (a - b)(a + b) = a^2 - b^2
def diff_sq(+a: S.Z, +b: S.Z) -> {S.Z.mul(S.Z.sub(a, b), S.Z.add(a, b)) == S.Z.sub(S.Z.mul(a, a), S.Z.mul(b, b)) : S.Z}:
  R.ring_eq([a, b],
    E.ZMul{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}},
    E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{0n}}, E.ZMul{E.ZVar{1n}, E.ZVar{1n}}},
    {==})

# (2^64 a + b)^2 = 2^128 a^2 + 2^65 ab + b^2: binary constants stay small
def big(+a: S.Z, +b: S.Z) -> {S.Z.mul(S.Z.add(S.Z.mul(S.Zpos{p2(64n)}, a), b), S.Z.add(S.Z.mul(S.Zpos{p2(64n)}, a), b)) == S.Z.add(S.Z.add(S.Z.mul(S.Zpos{p2(128n)}, S.Z.mul(a, a)), S.Z.mul(S.Zpos{p2(65n)}, S.Z.mul(a, b))), S.Z.mul(b, b)) : S.Z}:
  R.ring_eq([a, b],
    E.ZMul{E.ZAdd{E.ZMul{E.ZCst{S.Zpos{p2(64n)}}, E.ZVar{0n}}, E.ZVar{1n}}, E.ZAdd{E.ZMul{E.ZCst{S.Zpos{p2(64n)}}, E.ZVar{0n}}, E.ZVar{1n}}},
    E.ZAdd{E.ZAdd{E.ZMul{E.ZCst{S.Zpos{p2(128n)}}, E.ZMul{E.ZVar{0n}, E.ZVar{0n}}}, E.ZMul{E.ZCst{S.Zpos{p2(65n)}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}}, E.ZMul{E.ZVar{1n}, E.ZVar{1n}}},
    {==})

# Brahmagupta-Fibonacci: (a^2 + b^2)(c^2 + d^2) = (ac - bd)^2 + (ad + bc)^2
def bf(+a: S.Z, +b: S.Z, +c: S.Z, +d: S.Z) -> {S.Z.mul(S.Z.add(S.Z.mul(a, a), S.Z.mul(b, b)), S.Z.add(S.Z.mul(c, c), S.Z.mul(d, d))) == S.Z.add(S.Z.mul(S.Z.sub(S.Z.mul(a, c), S.Z.mul(b, d)), S.Z.sub(S.Z.mul(a, c), S.Z.mul(b, d))), S.Z.mul(S.Z.add(S.Z.mul(a, d), S.Z.mul(b, c)), S.Z.add(S.Z.mul(a, d), S.Z.mul(b, c)))) : S.Z}:
  R.ring_eq([a, b, c, d],
    E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{0n}}, E.ZMul{E.ZVar{1n}, E.ZVar{1n}}}, E.ZAdd{E.ZMul{E.ZVar{2n}, E.ZVar{2n}}, E.ZMul{E.ZVar{3n}, E.ZVar{3n}}}},
    E.ZAdd{E.ZMul{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}},
    {==})

def main() -> Nat:
  0n
