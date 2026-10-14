# Reduction computes: closed facts check by {==}.

import Base
import ../spec/num.bend as S
import ../lib/qreduce.bend as QRD

def twelve() -> S.Pos:
  S.XO{S.XO{S.XI{S.XH{}}}}

def eighteen() -> S.Pos:
  S.XO{S.XI{S.XO{S.XO{S.XH{}}}}}

# 12/18 = 2/3
def red_pos() -> {QRD.reduce(S.Q{S.Zpos{twelve()}, eighteen()}) == S.Q{S.Zpos{S.XO{S.XH{}}}, S.XI{S.XH{}}} : S.Q}:
  {==}

# -12/18 = -2/3
def red_neg() -> {QRD.reduce(S.Q{S.Zneg{twelve()}, eighteen()}) == S.Q{S.Zneg{S.XO{S.XH{}}}, S.XI{S.XH{}}} : S.Q}:
  {==}

# 3 2^40 / 2^41 = 3/2
def red_big() -> {QRD.reduce(S.Q{S.Z.mul(S.Zpos{S.XI{S.XH{}}}, S.Zpos{S.Pos.pow2(40n)}), S.Pos.pow2(41n)}) == S.Q{S.Zpos{S.XI{S.XH{}}}, S.XO{S.XH{}}} : S.Q}:
  {==}

# 0/7 = 0/1
def red_zero() -> {QRD.reduce(S.Q{S.Z0{}, S.XI{S.XI{S.XH{}}}}) == S.Q{S.Z0{}, S.XH{}} : S.Q}:
  {==}

def main() -> Nat:
  0n
