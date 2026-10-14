# Runtime big integers: the generic laws instantiate at the runtime base,
# and a small base computes concrete examples by {==}.

import Base
import ../spec/num.bend as S
import ../spec/big.bend as SB
import ../rt/big.bend as RB
import ../lib/big.bend as LB

# the runtime base minus one: 65535
def bp16() -> Nat:
  65535n

# the laws at the runtime base
def add16(+a: SB.Big, +b: SB.Big, wa: SB.Big.wf(bp16(), a), wb: SB.Big.wf(bp16(), b)) -> {SB.Big.val(bp16(), RB.Big.add(bp16(), a, b)) == S.Z.add(SB.Big.val(bp16(), a), SB.Big.val(bp16(), b)) : S.Z}:
  LB.add_ok(bp16(), a, b, wa, wb)

def mul16(+a: SB.Big, +b: SB.Big) -> {SB.Big.val(bp16(), RB.Big.mul(bp16(), a, b)) == S.Z.mul(SB.Big.val(bp16(), a), SB.Big.val(bp16(), b)) : S.Z}:
  LB.mul_ok(bp16(), a, b)

# decimal limbs (bp = 9): 321 * (-47) = -15087, and 321 - 456 = -135
def dec_mul() -> {RB.Big.mul(9n, SB.BPos{[1n, 2n, 3n]}, SB.BNeg{[7n, 4n]}) == SB.BNeg{[7n, 8n, 0n, 5n, 1n]} : SB.Big}:
  {==}

def dec_sub() -> {RB.Big.sub(9n, SB.BPos{[1n, 2n, 3n]}, SB.BPos{[6n, 5n, 4n]}) == SB.BNeg{[5n, 3n, 1n]} : SB.Big}:
  {==}

def dec_cmp() -> {RB.Big.cmp(9n, SB.BNeg{[0n, 0n, 1n]}, SB.BNeg{[9n, 9n]}) == LT{} : Cmp}:
  {==}

def main() -> Nat:
  0n
