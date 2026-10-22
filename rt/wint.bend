# Runtime big integers in a base 2^L (rt/wmag.bend's magnitudes, signed as
# spec/big.bend's Big): the canonical form, shifts and rounding, and
# conversions with the spec's integers. Verified in lib/wintpf.bend.
#
# Canonical: no high zero limb, and zero is BPos{Nil}. The word results the
# solver keeps are canonical, so a word integer is equal to another exactly
# when their values are (lib/wintpf.bend: canon_big_eq).

import Base
import ../spec/num.bend as S
import ../spec/big.bend as SB
import ./mag.bend as RM
import ./wmag.bend as RW

# minus a magnitude, zero as BPos{Nil}
def Big.negm(m: List<&2, Nat>) -> SB.Big:
  match m:
    case Nil{}:
      SB.BPos{Nil{}}
    case Con{h, t}:
      SB.BNeg{Con{h, t}}

# the canonical form
def Big.canon(x: SB.Big) -> SB.Big:
  match x:
    case SB.BPos{m}:
      SB.BPos{RM.Mag.norm(m)}
    case SB.BNeg{m}:
      Big.negm(RM.Mag.norm(m))

# x 2^k
def Big.shl(+bp: Nat, +lp: Nat, x: SB.Big, +k: Nat) -> SB.Big:
  match x:
    case SB.BPos{m}:
      SB.BPos{RW.Mag.shl(bp, lp, m, k)}
    case SB.BNeg{m}:
      SB.BNeg{RW.Mag.shl(bp, lp, m, k)}

# x / 2^k to the nearest, halves away from zero (k >= 1)
def Big.round(+bp: Nat, +lp: Nat, x: SB.Big, +k: Nat) -> SB.Big:
  match x:
    case SB.BPos{m}:
      SB.BPos{RW.Mag.round(bp, lp, m, k)}
    case SB.BNeg{m}:
      SB.BNeg{RW.Mag.round(bp, lp, m, k)}

# |x|
def Big.abs(x: SB.Big) -> SB.Big:
  match x:
    case SB.BPos{m}:
      SB.BPos{m}
    case SB.BNeg{m}:
      SB.BPos{m}

# the magnitude
def Big.mag(x: SB.Big) -> List<&2, Nat>:
  match x:
    case SB.BPos{m}:
      m
    case SB.BNeg{m}:
      m

# Conversions with the spec's integers
# ------------------------------------

def Big.ofz(+lp: Nat, z: S.Z) -> SB.Big:
  match z:
    case S.Z0{}:
      SB.BPos{Nil{}}
    case S.Zpos{p}:
      SB.BPos{RW.Mag.ofpos(lp, p)}
    case S.Zneg{p}:
      SB.BNeg{RW.Mag.ofpos(lp, p)}

def Big.zp(r: Maybe<&2, S.Pos>) -> S.Z:
  match r:
    case None{}:
      S.Z0{}
    case Some{p}:
      S.Zpos{p}

def Big.zn(r: Maybe<&2, S.Pos>) -> S.Z:
  match r:
    case None{}:
      S.Z0{}
    case Some{p}:
      S.Zneg{p}

def Big.toz(+lp: Nat, x: SB.Big) -> S.Z:
  match x:
    case SB.BPos{m}:
      Big.zp(RW.Mag.topos(lp, m))
    case SB.BNeg{m}:
      Big.zn(RW.Mag.topos(lp, m))

# the spec's QRD.size(zpos(z)): the bit length, and 1 for zero
def Big.size.m(+lp: Nat, m: List<&2, Nat>) -> Nat:
  match m:
    case Nil{}:
      1n
    case Con{h, t}:
      RW.Mag.bits(lp, Con{h, t})

def Big.size(+lp: Nat, x: SB.Big) -> Nat:
  Big.size.m(lp, Big.mag(x))
