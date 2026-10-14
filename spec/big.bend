# bend-cad spec: what runtime bigints mean. A magnitude is a list of limbs
# in base 1 + bp, least significant first; a big integer is a signed
# magnitude. The base is a parameter (65536 at runtime): the proofs hold for
# every base, and a large literal would be unfolded to unary by the checker.

import Base
import ./num.bend as S

# a <= b, witnessed by the gap k with a + k = b
def Le(a: Nat, b: Nat) -> Type:
  &k: Nat -> {Nat.add(a, k) == b : Nat}

def Mag.val(+bp: Nat, m: List<&2, Nat>) -> Nat:
  match m:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(h, Nat.mul(Mag.val(bp, t), 1n+bp))

# every limb is below the base
def Mag.wf(+bp: Nat, m: List<&2, Nat>) -> Type:
  match m:
    case Nil{}:
      Unit
    case Con{h, t}:
      Le(h, bp) & Mag.wf(bp, t)

type Big is Data:
  BPos{m: List<&2, Nat>}
  BNeg{m: List<&2, Nat>}

def Big.val(+bp: Nat, x: Big) -> S.Z:
  match x:
    case BPos{m}:
      S.Z.of_diff(Mag.val(bp, m), 0n)
    case BNeg{m}:
      S.Z.of_diff(0n, Mag.val(bp, m))

def Big.wf(+bp: Nat, x: Big) -> Type:
  match x:
    case BPos{m}:
      Mag.wf(bp, m)
    case BNeg{m}:
      Mag.wf(bp, m)
