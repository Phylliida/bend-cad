# Runtime dyadics m 2^-e with a word integer mantissa (rt/wint.bend, base
# 2^(1 + lp)), twins of the spec's S.D: each operation gives exactly the
# S.D result (the same mantissa and the same exponent), in canonical form.
# Verified in lib/wdyadpf.bend. Exponents and bit counts are Nats, as in
# S.D.

import Base
import ../spec/num.bend as S
import ../spec/big.bend as SB
import ./mag.bend as RM
import ./big.bend as RB
import ./wmag.bend as RW
import ./wint.bend as RI

type WD is Data:
  WD{m: SB.Big, e: Nat}

def WD.m(x: WD) -> SB.Big:
  match x:
    case WD{m, e}:
      m

def WD.e(x: WD) -> Nat:
  match x:
    case WD{m, e}:
      e

# Native order on Nat
# -------------------

def le.go(c: Cmp) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

# a <= b, by the native comparison
def le(+a: Nat, +b: Nat) -> Bool:
  le.go(Nat.cmp(a, b))

# Conversions with S.D
# --------------------

def WD.ofd(+lp: Nat, x: S.D) -> WD:
  match x:
    case S.D{m, e}:
      WD{RI.Big.ofz(lp, m), e}

def WD.tod(+lp: Nat, x: WD) -> S.D:
  match x:
    case WD{m, e}:
      S.D{RI.Big.toz(lp, m), e}

# The ring operations
# -------------------

# S.D.add: the larger exponent, the other mantissa shifted up to it
def WD.add.go(l: Bool, +bp: Nat, +lp: Nat, +a: WD, +b: WD) -> WD:
  match l:
    case True{}:
      WD{RI.Big.canon(RB.Big.add(bp, RI.Big.shl(bp, lp, WD.m(a), Nat.sub(WD.e(b), WD.e(a))), WD.m(b))), WD.e(b)}
    case False{}:
      WD{RI.Big.canon(RB.Big.add(bp, WD.m(a), RI.Big.shl(bp, lp, WD.m(b), Nat.sub(WD.e(a), WD.e(b))))), WD.e(a)}

def WD.add(+bp: Nat, +lp: Nat, +a: WD, +b: WD) -> WD:
  WD.add.go(le(WD.e(a), WD.e(b)), bp, lp, a, b)

def WD.mul(+bp: Nat, +a: WD, +b: WD) -> WD:
  WD{RI.Big.canon(RB.Big.mul(bp, WD.m(a), WD.m(b))), Nat.add(WD.e(a), WD.e(b))}

def WD.neg(+a: WD) -> WD:
  WD{RI.Big.canon(RB.Big.neg(WD.m(a))), WD.e(a)}

# the comparison of the values (KI.dcmp)
def WD.cmp.go(l: Bool, +bp: Nat, +lp: Nat, +a: WD, +b: WD) -> Cmp:
  match l:
    case True{}:
      RB.Big.cmp(bp, RI.Big.shl(bp, lp, WD.m(a), Nat.sub(WD.e(b), WD.e(a))), WD.m(b))
    case False{}:
      RB.Big.cmp(bp, WD.m(a), RI.Big.shl(bp, lp, WD.m(b), Nat.sub(WD.e(a), WD.e(b))))

def WD.cmp(+bp: Nat, +lp: Nat, +a: WD, +b: WD) -> Cmp:
  WD.cmp.go(le(WD.e(a), WD.e(b)), bp, lp, a, b)

# Rounding (twins of lib/numer.bend's dznorm, dsig and dround)
# ------------------------------------------------------------

# a zero at exponent 0
def WD.znorm.m(m: List<&2, Nat>, x: WD) -> WD:
  match m:
    case Nil{}:
      WD{SB.BPos{Nil{}}, 0n}
    case Con{h, t}:
      x

def WD.znorm(+x: WD) -> WD:
  WD.znorm.m(RI.Big.mag(WD.m(x)), x)

# m / 2^k to the nearest, canonical
def WD.zround(+bp: Nat, +lp: Nat, m: SB.Big, +k: Nat) -> SB.Big:
  RI.Big.canon(RI.Big.round(bp, lp, m, k))

def WD.sig.sh(l: Bool, +bp: Nat, +lp: Nat, m: SB.Big, +e: Nat, +k: Nat) -> WD:
  match l:
    case True{}:
      WD{WD.zround(bp, lp, m, k), Nat.sub(e, k)}
    case False{}:
      WD{RI.Big.canon(RI.Big.shl(bp, lp, WD.zround(bp, lp, m, k), Nat.sub(k, e))), 0n}

def WD.sig.go(l: Bool, +bp: Nat, +lp: Nat, +x: WD, +k: Nat) -> WD:
  match l:
    case True{}:
      WD.znorm(x)
    case False{}:
      WD.sig.sh(le(k, WD.e(x)), bp, lp, WD.m(x), WD.e(x), k)

def WD.sig.n(+n: Nat, +bp: Nat, +lp: Nat, +x: WD, +b: Nat) -> WD:
  WD.sig.go(le(n, b), bp, lp, x, Nat.sub(n, b))

# x to about b significant bits
def WD.sig(+bp: Nat, +lp: Nat, +x: WD, +b: Nat) -> WD:
  WD.sig.n(RI.Big.size(lp, WD.m(x)), bp, lp, x, b)

def WD.round.go(l: Bool, +bp: Nat, +lp: Nat, +x: WD, +p: Nat) -> WD:
  match l:
    case True{}:
      x
    case False{}:
      WD{WD.zround(bp, lp, WD.m(x), Nat.sub(WD.e(x), p)), p}

# x to a multiple of 2^-p
def WD.round(+bp: Nat, +lp: Nat, +x: WD, +p: Nat) -> WD:
  WD.round.go(le(WD.e(x), p), bp, lp, x, p)
