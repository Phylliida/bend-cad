# Benchmark (prototype side): 256-bit (16-limb) magnitude products, verified rt/mag.bend vs
# the sk-P1 prototype. Untrusted harness.

import Base
import ../rt/mag.bend as RM
import ./int.bend as PI

# 16 pseudo-random limbs below 2^16
def limbs(n: Nat, +x: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      +y = Nat.mod(Nat.add(Nat.mul(x, 48271n), 11n), 65521n)
      Con{y, limbs(k, y)}

def sum(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.mod(Nat.add(h, sum(t)), 1000000007n)

def run_v(n: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+k:
      run_v(k, a, b, Nat.mod(Nat.add(acc, sum(RM.Mag.mul(65535n, a, b))), 1000000007n))

def run_p(n: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, acc: Nat) -> Nat:
  match n:
    case 0n:
      acc
    case 1n+k:
      run_p(k, a, b, Nat.mod(Nat.add(acc, sum(PI.Mag.mul(a, b))), 1000000007n))

# sk-P1 prototype: the same 20000 products
def main() -> Nat:
  run_p(20000n, limbs(16n, 12345n), limbs(16n, 777n), 0n)
