import Base
import ../lib/natring.bend as NR

# (a + b)^2 = a^2 + 2ab + b^2, one normalizer call
def sq(+a: Nat, +b: Nat) -> {Nat.mul(Nat.add(a, b), Nat.add(a, b)) == Nat.add(Nat.add(Nat.mul(a, a), Nat.mul(2n, Nat.mul(a, b))), Nat.mul(b, b)) : Nat}:
  NR.ring_eq([a, b],
    NR.NMul{NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}, NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}},
    NR.NAdd{NR.NAdd{NR.NMul{NR.NVar{0n}, NR.NVar{0n}}, NR.NMul{NR.NCst{2n}, NR.NMul{NR.NVar{0n}, NR.NVar{1n}}}}, NR.NMul{NR.NVar{1n}, NR.NVar{1n}}},
    {==})

# a bigger one: (a + b + c)^3, expanded
def cube(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.add(Nat.add(a, b), c), Nat.mul(Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(a, b), c))) == Nat.mul(Nat.add(c, Nat.add(b, a)), Nat.mul(Nat.add(c, Nat.add(b, a)), Nat.add(c, Nat.add(b, a)))) : Nat}:
  NR.ring_eq([a, b, c],
    NR.NMul{NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}, NR.NVar{2n}}, NR.NMul{NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}, NR.NVar{2n}}, NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}, NR.NVar{2n}}}},
    NR.NMul{NR.NAdd{NR.NVar{2n}, NR.NAdd{NR.NVar{1n}, NR.NVar{0n}}}, NR.NMul{NR.NAdd{NR.NVar{2n}, NR.NAdd{NR.NVar{1n}, NR.NVar{0n}}}, NR.NAdd{NR.NVar{2n}, NR.NAdd{NR.NVar{1n}, NR.NVar{0n}}}}},
    {==})

def main() -> Nat:
  0n
