# Dyadic arithmetic computes exactly: closed facts check by {==}.

import Base
import ../spec/num.bend as S

def dy(m: S.Z, e: Nat) -> S.D:
  S.D{m, e}

def three() -> S.Z:
  S.Zpos{S.XI{S.XH{}}}

def five() -> S.Z:
  S.Zpos{S.XI{S.XO{S.XH{}}}}

# 3/4 + 5/8 = 11/8
def add_ok() -> S.Q.eq(S.D.toq(S.D.add(dy(three(), 2n), dy(five(), 3n))), S.Q{S.Zpos{S.XI{S.XI{S.XO{S.XH{}}}}}, S.XO{S.XO{S.XO{S.XH{}}}}}):
  {==}

# (3/4) * (-5/8) = -15/32
def mul_ok() -> S.Q.eq(S.D.toq(S.D.mul(dy(three(), 2n), dy(S.Z.neg(five()), 3n))), S.Q{S.Zneg{S.XI{S.XI{S.XI{S.XH{}}}}}, S.Pos.pow2(5n)}):
  {==}

# 1/2^100 - 1/2^101 = 1/2^101, with 100-digit exponents
def tiny() -> S.Q.eq(S.D.toq(S.D.sub(dy(S.Zpos{S.XH{}}, 100n), dy(S.Zpos{S.XH{}}, 101n))), S.Q{S.Zpos{S.XH{}}, S.Pos.pow2(101n)}):
  {==}

def main() -> Nat:
  0n
