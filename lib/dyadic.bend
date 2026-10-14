# Dyadics mean rationals: D.toq turns D.mul, D.neg and D.add into Q.mul,
# Q.neg and Q.add (up to Q.eq).

import Base
import ./zring.bend as R
import ../spec/num.bend as S
import ../spec/ring.bend as E

# 2^a * 2^b = 2^(a + b)
def pow2_add(a: Nat, -b: Nat) -> {S.Pos.mul(S.Pos.pow2(a), S.Pos.pow2(b)) == S.Pos.pow2(Nat.add(a, b)) : S.Pos}:
  match a:
    case 0n:
      {==}
    case 1n+k:
      %pow2_add(k, b) : {S.XO{S.Pos.mul(S.Pos.pow2(k), S.Pos.pow2(b))} == S.XO{_} : S.Pos}
      {==}

def toq_mul(+x: S.D, +y: S.D) -> S.Q.eq(S.D.toq(S.D.mul(x, y)), S.Q.mul(S.D.toq(x), S.D.toq(y))):
  %pow2_add(S.D.exp(x), S.D.exp(y)) : {S.Z.mul(S.Z.mul(S.D.man(x), S.D.man(y)), S.Zpos{S.Pos.mul(S.Pos.pow2(S.D.exp(x)), S.Pos.pow2(S.D.exp(y)))}) == S.Z.mul(S.Z.mul(S.D.man(x), S.D.man(y)), S.Zpos{_}) : S.Z}
  {==}

def toq_neg(+x: S.D) -> S.Q.eq(S.D.toq(S.D.neg(x)), S.Q.neg(S.D.toq(x))):
  {==}

def add_go_ok(e1: Nat, e2: Nat, +m1: S.Z, +m2: S.Z) -> S.Q.eq(S.D.toq(S.D.add.go(e1, e2, m1, m2)), S.Q.add(S.Q{m1, S.Pos.pow2(e1)}, S.Q{m2, S.Pos.pow2(e2)})):
  match e1 e2:
    case 0n 0n:
      R.ring_eq([m1, m2], E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZMul{E.ZVar{1n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZCst{S.Zpos{S.XH{}}}}, {==})
    case 1n++i 0n:
      R.ring_eq([m1, m2, S.Zpos{S.Pos.pow2(1n+i)}], E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZMul{E.ZVar{2n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZVar{2n}}, {==})
    case 0n 1n++j:
      R.ring_eq([m1, m2, S.Zpos{S.Pos.pow2(1n+j)}], E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{1n}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{2n}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZVar{2n}}, {==})
    case 1n++i 1n++j:
      %R.ring_eq([S.D.man(S.D.add.go(i, j, m1, m2)), m1, m2, S.Zpos{S.Pos.pow2(i)}, S.Zpos{S.Pos.pow2(j)}, S.Zpos{S.Pos.pow2(S.D.exp(S.D.add.go(i, j, m1, m2)))}], E.ZMul{E.ZCst{S.Zpos{S.XO{S.XO{S.XH{}}}}}, E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{3n}, E.ZVar{4n}}}}, E.ZMul{E.ZVar{0n}, E.ZMul{E.ZMul{E.ZCst{S.Zpos{S.XO{S.XH{}}}}, E.ZVar{3n}}, E.ZMul{E.ZCst{S.Zpos{S.XO{S.XH{}}}}, E.ZVar{4n}}}}, {==}) : {_ == E.eval([S.D.man(S.D.add.go(i, j, m1, m2)), m1, m2, S.Zpos{S.Pos.pow2(i)}, S.Zpos{S.Pos.pow2(j)}, S.Zpos{S.Pos.pow2(S.D.exp(S.D.add.go(i, j, m1, m2)))}], E.ZMul{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZMul{E.ZCst{S.Zpos{S.XO{S.XH{}}}}, E.ZVar{4n}}}, E.ZMul{E.ZVar{2n}, E.ZMul{E.ZCst{S.Zpos{S.XO{S.XH{}}}}, E.ZVar{3n}}}}, E.ZMul{E.ZCst{S.Zpos{S.XO{S.XH{}}}}, E.ZVar{5n}}}) : S.Z}
      %R.ring_eq([S.D.man(S.D.add.go(i, j, m1, m2)), m1, m2, S.Zpos{S.Pos.pow2(i)}, S.Zpos{S.Pos.pow2(j)}, S.Zpos{S.Pos.pow2(S.D.exp(S.D.add.go(i, j, m1, m2)))}], E.ZMul{E.ZCst{S.Zpos{S.XO{S.XO{S.XH{}}}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{4n}}, E.ZMul{E.ZVar{2n}, E.ZVar{3n}}}, E.ZVar{5n}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZMul{E.ZCst{S.Zpos{S.XO{S.XH{}}}}, E.ZVar{4n}}}, E.ZMul{E.ZVar{2n}, E.ZMul{E.ZCst{S.Zpos{S.XO{S.XH{}}}}, E.ZVar{3n}}}}, E.ZMul{E.ZCst{S.Zpos{S.XO{S.XH{}}}}, E.ZVar{5n}}}, {==}) : {E.eval([S.D.man(S.D.add.go(i, j, m1, m2)), m1, m2, S.Zpos{S.Pos.pow2(i)}, S.Zpos{S.Pos.pow2(j)}, S.Zpos{S.Pos.pow2(S.D.exp(S.D.add.go(i, j, m1, m2)))}], E.ZMul{E.ZCst{S.Zpos{S.XO{S.XO{S.XH{}}}}}, E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{3n}, E.ZVar{4n}}}}) == _ : S.Z}
      %add_go_ok(i, j, m1, m2) : {E.eval([S.D.man(S.D.add.go(i, j, m1, m2)), m1, m2, S.Zpos{S.Pos.pow2(i)}, S.Zpos{S.Pos.pow2(j)}, S.Zpos{S.Pos.pow2(S.D.exp(S.D.add.go(i, j, m1, m2)))}], E.ZMul{E.ZCst{S.Zpos{S.XO{S.XO{S.XH{}}}}}, E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{3n}, E.ZVar{4n}}}}) == S.Z.mul(S.Zpos{S.XO{S.XO{S.XH{}}}}, _) : S.Z}
      {==}

def toq_add(+x: S.D, +y: S.D) -> S.Q.eq(S.D.toq(S.D.add(x, y)), S.Q.add(S.D.toq(x), S.D.toq(y))):
  add_go_ok(S.D.exp(x), S.D.exp(y), S.D.man(x), S.D.man(y))
