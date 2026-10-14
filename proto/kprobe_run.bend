# sk-05 probe: native speed of generic code at K = D vs the dyadic copy
import Base
import ../spec/num.bend as S
import ../spec/mat.bend as M
import ./kprobe.bend as KP

def gen(n: Nat, +s: Nat) -> List<&2, S.D>:
  match n:
    case 0n:
      Nil{}
    case 1n++k:
      Con{S.D{S.Zpos{S.Pos.of_succ(Nat.add(k, s))}, 3n}, gen(k, s)}

def cmp_nat(c: Cmp) -> Nat:
  match c:
    case LT{}:
      0n
    case EQ{}:
      1n
    case GT{}:
      2n

def loop_k(n: Nat, +a: List<&2, S.D>, +v: List<&2, S.D>, acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+k:
      loop_k(k, a, v, Nat.add(acc, cmp_nat(KP.dcmp(KP.kdot(~KP.dnum(), a, v), M.d0()))))

def loop_d(n: Nat, +a: List<&2, S.D>, +v: List<&2, S.D>, acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+k:
      loop_d(k, a, v, Nat.add(acc, cmp_nat(KP.dcmp(M.ddot(a, v), M.d0()))))

def main() -> Nat:
  MODE
