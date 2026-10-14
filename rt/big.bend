# Runtime big integers: signed magnitudes in base 1 + bp (spec/big.bend
# says what they mean; lib/big.bend proves they refine the spec integers).

import Base
import ../spec/big.bend as SB
import ./mag.bend as RM

def Big.neg(x: SB.Big) -> SB.Big:
  match x:
    case SB.BPos{m}:
      SB.BNeg{m}
    case SB.BNeg{m}:
      SB.BPos{m}

# x - y for magnitudes, given c = Mag.cmp(x, y)
def Big.diff.fin(+bp: Nat, c: Cmp, +x: List<&2, Nat>, +y: List<&2, Nat>) -> SB.Big:
  match c:
    case LT{}:
      SB.BNeg{RM.Mag.sub(bp, y, x)}
    case EQ{}:
      SB.BPos{Nil{}}
    case GT{}:
      SB.BPos{RM.Mag.sub(bp, x, y)}

def Big.diff(+bp: Nat, +x: List<&2, Nat>, +y: List<&2, Nat>) -> SB.Big:
  Big.diff.fin(bp, RM.Mag.cmp(x, y), x, y)

def Big.add(+bp: Nat, a: SB.Big, b: SB.Big) -> SB.Big:
  match a b:
    case SB.BPos{x} SB.BPos{y}:
      SB.BPos{RM.Mag.add(bp, x, y)}
    case SB.BPos{x} SB.BNeg{y}:
      Big.diff(bp, x, y)
    case SB.BNeg{x} SB.BPos{y}:
      Big.diff(bp, y, x)
    case SB.BNeg{x} SB.BNeg{y}:
      SB.BNeg{RM.Mag.add(bp, x, y)}

def Big.sub(+bp: Nat, a: SB.Big, b: SB.Big) -> SB.Big:
  Big.add(bp, a, Big.neg(b))

def Big.mul(+bp: Nat, a: SB.Big, b: SB.Big) -> SB.Big:
  match a b:
    case SB.BPos{x} SB.BPos{y}:
      SB.BPos{RM.Mag.mul(bp, x, y)}
    case SB.BPos{x} SB.BNeg{y}:
      SB.BNeg{RM.Mag.mul(bp, x, y)}
    case SB.BNeg{x} SB.BPos{y}:
      SB.BNeg{RM.Mag.mul(bp, x, y)}
    case SB.BNeg{x} SB.BNeg{y}:
      SB.BPos{RM.Mag.mul(bp, x, y)}

def Big.cmp(+bp: Nat, a: SB.Big, b: SB.Big) -> Cmp:
  match a b:
    case SB.BPos{x} SB.BPos{y}:
      RM.Mag.cmp(x, y)
    case SB.BPos{x} SB.BNeg{y}:
      RM.Mag.cmpz(RM.Mag.add(bp, x, y))
    case SB.BNeg{x} SB.BPos{y}:
      RM.Mag.zcmp(RM.Mag.add(bp, y, x))
    case SB.BNeg{x} SB.BNeg{y}:
      RM.Mag.cmp(y, x)
