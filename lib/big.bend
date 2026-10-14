# Runtime big integers refine the spec integers: Big.val of the result of
# add, sub, neg, mul is the Z result; Big.cmp is Z.cmp; and the operations
# keep limbs below the base. Through of_diff's homomorphism laws (lib/z.bend)
# and the magnitude proofs (lib/mag.bend).

import Base
import ./nat.bend as N
import ./natring.bend as NR
import ./natord.bend as O
import ./z.bend as LZ
import ./mag.bend as LM
import ../spec/num.bend as S
import ../spec/big.bend as SB
import ../rt/mag.bend as RM
import ../rt/big.bend as RB

def neg_ok(+bp: Nat, x: SB.Big) -> {SB.Big.val(bp, RB.Big.neg(x)) == S.Z.neg(SB.Big.val(bp, x)) : S.Z}:
  match x:
    case SB.BPos{m}:
      LZ.neg_diff(SB.Mag.val(bp, m), 0n)
    case SB.BNeg{m}:
      LZ.neg_diff(0n, SB.Mag.val(bp, m))

def neg_wf(+bp: Nat, x: SB.Big, wx: SB.Big.wf(bp, x)) -> SB.Big.wf(bp, RB.Big.neg(x)):
  match x:
    case SB.BPos{m}:
      wx
    case SB.BNeg{m}:
      wx

# the difference of magnitudes, given their comparison c
def diff_dec(+bp: Nat, c: Cmp, +x: List<&2, Nat>, +y: List<&2, Nat>, e: {c == Nat.cmp(SB.Mag.val(bp, x), SB.Mag.val(bp, y)) : Cmp}, wx: SB.Mag.wf(bp, x), wy: SB.Mag.wf(bp, y))
  -> {SB.Big.val(bp, RB.Big.diff.fin(bp, c, x, y)) == S.Z.of_diff(SB.Mag.val(bp, x), SB.Mag.val(bp, y)) : S.Z}:
  match c:
    case LT{}:
      LZ.od_eq(0n, SB.Mag.val(bp, RM.Mag.sub(bp, y, x)), SB.Mag.val(bp, x), SB.Mag.val(bp, y),
        Equal.sym(Nat, Nat.add(SB.Mag.val(bp, RM.Mag.sub(bp, y, x)), SB.Mag.val(bp, x)), SB.Mag.val(bp, y), LM.sub_val(bp, y, x, wy, wx, O.le_weaken(SB.Mag.val(bp, x), SB.Mag.val(bp, y), O.cmp_lt(SB.Mag.val(bp, x), SB.Mag.val(bp, y), e)))))
    case EQ{}:
      LZ.od_eq(0n, 0n, SB.Mag.val(bp, x), SB.Mag.val(bp, y), Equal.sym(Nat, SB.Mag.val(bp, x), SB.Mag.val(bp, y), NR.nat_cmp_eq(SB.Mag.val(bp, x), SB.Mag.val(bp, y), e)))
    case GT{}:
      LZ.od_eq(SB.Mag.val(bp, RM.Mag.sub(bp, x, y)), 0n, SB.Mag.val(bp, x), SB.Mag.val(bp, y), LM.sub_val(bp, x, y, wx, wy, O.le_weaken(SB.Mag.val(bp, y), SB.Mag.val(bp, x), O.cmp_gt(SB.Mag.val(bp, x), SB.Mag.val(bp, y), e))))

def diff_ok(+bp: Nat, +x: List<&2, Nat>, +y: List<&2, Nat>, +wx: SB.Mag.wf(bp, x), +wy: SB.Mag.wf(bp, y)) -> {SB.Big.val(bp, RB.Big.diff(bp, x, y)) == S.Z.of_diff(SB.Mag.val(bp, x), SB.Mag.val(bp, y)) : S.Z}:
  diff_dec(bp, RM.Mag.cmp(x, y), x, y, LM.cmp_ok(bp, x, y, wx, wy), wx, wy)

def diff_wf(+bp: Nat, c: Cmp, +x: List<&2, Nat>, +y: List<&2, Nat>, wx: SB.Mag.wf(bp, x), wy: SB.Mag.wf(bp, y)) -> SB.Big.wf(bp, RB.Big.diff.fin(bp, c, x, y)):
  match c:
    case LT{}:
      LM.sub_wf(bp, y, x, wy, wx)
    case EQ{}:
      Unit{}
    case GT{}:
      LM.sub_wf(bp, x, y, wx, wy)

# Addition
# --------

def add_ok(+bp: Nat, a: SB.Big, b: SB.Big, wa: SB.Big.wf(bp, a), wb: SB.Big.wf(bp, b)) -> {SB.Big.val(bp, RB.Big.add(bp, a, b)) == S.Z.add(SB.Big.val(bp, a), SB.Big.val(bp, b)) : S.Z}:
  match a b:
    case SB.BPos{+x} SB.BPos{+y}:
      %LZ.add_hom(SB.Mag.val(bp, x), 0n, SB.Mag.val(bp, y), 0n) : {S.Z.of_diff(SB.Mag.val(bp, RM.Mag.add(bp, x, y)), 0n) == _ : S.Z}
      %LM.add_val(bp, x, y) : {S.Z.of_diff(_, 0n) == S.Z.of_diff(Nat.add(SB.Mag.val(bp, x), SB.Mag.val(bp, y)), 0n) : S.Z}
      {==}
    case SB.BPos{+x} SB.BNeg{+y}:
      %LZ.add_hom(SB.Mag.val(bp, x), 0n, 0n, SB.Mag.val(bp, y)) : {SB.Big.val(bp, RB.Big.diff(bp, x, y)) == _ : S.Z}
      %N.add_zero(SB.Mag.val(bp, x)) : {SB.Big.val(bp, RB.Big.diff(bp, x, y)) == S.Z.of_diff(_, SB.Mag.val(bp, y)) : S.Z}
      diff_ok(bp, x, y, wa, wb)
    case SB.BNeg{+x} SB.BPos{+y}:
      %LZ.add_hom(0n, SB.Mag.val(bp, x), SB.Mag.val(bp, y), 0n) : {SB.Big.val(bp, RB.Big.diff(bp, y, x)) == _ : S.Z}
      %N.add_zero(SB.Mag.val(bp, x)) : {SB.Big.val(bp, RB.Big.diff(bp, y, x)) == S.Z.of_diff(SB.Mag.val(bp, y), _) : S.Z}
      diff_ok(bp, y, x, wb, wa)
    case SB.BNeg{+x} SB.BNeg{+y}:
      %LZ.add_hom(0n, SB.Mag.val(bp, x), 0n, SB.Mag.val(bp, y)) : {S.Z.of_diff(0n, SB.Mag.val(bp, RM.Mag.add(bp, x, y))) == _ : S.Z}
      %LM.add_val(bp, x, y) : {S.Z.of_diff(0n, _) == S.Z.of_diff(0n, Nat.add(SB.Mag.val(bp, x), SB.Mag.val(bp, y))) : S.Z}
      {==}

def add_wf(+bp: Nat, a: SB.Big, b: SB.Big, hb: SB.Le(1n, bp), wa: SB.Big.wf(bp, a), wb: SB.Big.wf(bp, b)) -> SB.Big.wf(bp, RB.Big.add(bp, a, b)):
  match a b:
    case SB.BPos{x} SB.BPos{y}:
      LM.add_wf(bp, x, y, hb, wa, wb)
    case SB.BPos{+x} SB.BNeg{+y}:
      diff_wf(bp, RM.Mag.cmp(x, y), x, y, wa, wb)
    case SB.BNeg{+x} SB.BPos{+y}:
      diff_wf(bp, RM.Mag.cmp(y, x), y, x, wb, wa)
    case SB.BNeg{x} SB.BNeg{y}:
      LM.add_wf(bp, x, y, hb, wa, wb)

def sub_ok(+bp: Nat, +a: SB.Big, +b: SB.Big, wa: SB.Big.wf(bp, a), wb: SB.Big.wf(bp, b)) -> {SB.Big.val(bp, RB.Big.sub(bp, a, b)) == S.Z.sub(SB.Big.val(bp, a), SB.Big.val(bp, b)) : S.Z}:
  %neg_ok(bp, b) : {SB.Big.val(bp, RB.Big.sub(bp, a, b)) == S.Z.add(SB.Big.val(bp, a), _) : S.Z}
  add_ok(bp, a, RB.Big.neg(b), wa, neg_wf(bp, b, wb))

def sub_wf(+bp: Nat, +a: SB.Big, +b: SB.Big, hb: SB.Le(1n, bp), wa: SB.Big.wf(bp, a), wb: SB.Big.wf(bp, b)) -> SB.Big.wf(bp, RB.Big.sub(bp, a, b)):
  add_wf(bp, a, RB.Big.neg(b), hb, wa, neg_wf(bp, b, wb))

# Multiplication
# --------------

def mul_ok(+bp: Nat, a: SB.Big, b: SB.Big) -> {SB.Big.val(bp, RB.Big.mul(bp, a, b)) == S.Z.mul(SB.Big.val(bp, a), SB.Big.val(bp, b)) : S.Z}:
  match a b:
    case SB.BPos{+x} SB.BPos{+y}:
      %LZ.mul_hom(SB.Mag.val(bp, x), 0n, SB.Mag.val(bp, y), 0n) : {S.Z.of_diff(SB.Mag.val(bp, RM.Mag.mul(bp, x, y)), 0n) == _ : S.Z}
      %N.add_zero(Nat.mul(SB.Mag.val(bp, x), SB.Mag.val(bp, y))) : {S.Z.of_diff(SB.Mag.val(bp, RM.Mag.mul(bp, x, y)), 0n) == S.Z.of_diff(_, Nat.add(Nat.mul(SB.Mag.val(bp, x), 0n), 0n)) : S.Z}
      %N.mul_zero(SB.Mag.val(bp, x)) : {S.Z.of_diff(SB.Mag.val(bp, RM.Mag.mul(bp, x, y)), 0n) == S.Z.of_diff(Nat.mul(SB.Mag.val(bp, x), SB.Mag.val(bp, y)), Nat.add(_, 0n)) : S.Z}
      %LM.mul_val(bp, x, y) : {S.Z.of_diff(_, 0n) == S.Z.of_diff(Nat.mul(SB.Mag.val(bp, x), SB.Mag.val(bp, y)), 0n) : S.Z}
      {==}
    case SB.BPos{+x} SB.BNeg{+y}:
      %LZ.mul_hom(SB.Mag.val(bp, x), 0n, 0n, SB.Mag.val(bp, y)) : {S.Z.of_diff(0n, SB.Mag.val(bp, RM.Mag.mul(bp, x, y))) == _ : S.Z}
      %N.mul_zero(SB.Mag.val(bp, x)) : {S.Z.of_diff(0n, SB.Mag.val(bp, RM.Mag.mul(bp, x, y))) == S.Z.of_diff(Nat.add(_, 0n), Nat.add(Nat.mul(SB.Mag.val(bp, x), SB.Mag.val(bp, y)), 0n)) : S.Z}
      %N.add_zero(Nat.mul(SB.Mag.val(bp, x), SB.Mag.val(bp, y))) : {S.Z.of_diff(0n, SB.Mag.val(bp, RM.Mag.mul(bp, x, y))) == S.Z.of_diff(0n, _) : S.Z}
      %LM.mul_val(bp, x, y) : {S.Z.of_diff(0n, _) == S.Z.of_diff(0n, Nat.mul(SB.Mag.val(bp, x), SB.Mag.val(bp, y))) : S.Z}
      {==}
    case SB.BNeg{+x} SB.BPos{+y}:
      %LZ.mul_hom(0n, SB.Mag.val(bp, x), SB.Mag.val(bp, y), 0n) : {S.Z.of_diff(0n, SB.Mag.val(bp, RM.Mag.mul(bp, x, y))) == _ : S.Z}
      %N.mul_zero(SB.Mag.val(bp, x)) : {S.Z.of_diff(0n, SB.Mag.val(bp, RM.Mag.mul(bp, x, y))) == S.Z.of_diff(_, Nat.mul(SB.Mag.val(bp, x), SB.Mag.val(bp, y))) : S.Z}
      %LM.mul_val(bp, x, y) : {S.Z.of_diff(0n, _) == S.Z.of_diff(0n, Nat.mul(SB.Mag.val(bp, x), SB.Mag.val(bp, y))) : S.Z}
      {==}
    case SB.BNeg{+x} SB.BNeg{+y}:
      %LZ.mul_hom(0n, SB.Mag.val(bp, x), 0n, SB.Mag.val(bp, y)) : {S.Z.of_diff(SB.Mag.val(bp, RM.Mag.mul(bp, x, y)), 0n) == _ : S.Z}
      %N.mul_zero(SB.Mag.val(bp, x)) : {S.Z.of_diff(SB.Mag.val(bp, RM.Mag.mul(bp, x, y)), 0n) == S.Z.of_diff(Nat.mul(SB.Mag.val(bp, x), SB.Mag.val(bp, y)), _) : S.Z}
      %LM.mul_val(bp, x, y) : {S.Z.of_diff(_, 0n) == S.Z.of_diff(Nat.mul(SB.Mag.val(bp, x), SB.Mag.val(bp, y)), 0n) : S.Z}
      {==}

def mul_wf(+bp: Nat, a: SB.Big, b: SB.Big, hb: SB.Le(1n, bp), wa: SB.Big.wf(bp, a), wb: SB.Big.wf(bp, b)) -> SB.Big.wf(bp, RB.Big.mul(bp, a, b)):
  match a b:
    case SB.BPos{x} SB.BPos{y}:
      LM.mul_wf(bp, x, y, hb, wa, wb)
    case SB.BPos{x} SB.BNeg{y}:
      LM.mul_wf(bp, x, y, hb, wa, wb)
    case SB.BNeg{x} SB.BPos{y}:
      LM.mul_wf(bp, x, y, hb, wa, wb)
    case SB.BNeg{x} SB.BNeg{y}:
      LM.mul_wf(bp, x, y, hb, wa, wb)

# Comparison
# ----------

# the sign of x + y, for magnitudes
def cmpz_add(+bp: Nat, +x: List<&2, Nat>, +y: List<&2, Nat>, hb: SB.Le(1n, bp), wx: SB.Mag.wf(bp, x), wy: SB.Mag.wf(bp, y))
  -> {RM.Mag.cmpz(RM.Mag.add(bp, x, y)) == Nat.cmp(Nat.add(SB.Mag.val(bp, x), SB.Mag.val(bp, y)), 0n) : Cmp}:
  %Equal.sym(Nat, Nat.add(SB.Mag.val(bp, x), SB.Mag.val(bp, y)), SB.Mag.val(bp, RM.Mag.add(bp, x, y)), LM.add_val(bp, x, y)) : {RM.Mag.cmpz(RM.Mag.add(bp, x, y)) == Nat.cmp(_, 0n) : Cmp}
  LM.cmpz_ok(bp, RM.Mag.add(bp, x, y), LM.add_wf(bp, x, y, hb, wx, wy))

def zcmp_add(+bp: Nat, +x: List<&2, Nat>, +y: List<&2, Nat>, hb: SB.Le(1n, bp), wx: SB.Mag.wf(bp, x), wy: SB.Mag.wf(bp, y))
  -> {RM.Mag.zcmp(RM.Mag.add(bp, x, y)) == Nat.cmp(0n, Nat.add(SB.Mag.val(bp, x), SB.Mag.val(bp, y))) : Cmp}:
  %Equal.sym(Nat, Nat.add(SB.Mag.val(bp, x), SB.Mag.val(bp, y)), SB.Mag.val(bp, RM.Mag.add(bp, x, y)), LM.add_val(bp, x, y)) : {RM.Mag.zcmp(RM.Mag.add(bp, x, y)) == Nat.cmp(0n, _) : Cmp}
  LM.zcmp_ok(bp, RM.Mag.add(bp, x, y), LM.add_wf(bp, x, y, hb, wx, wy))


def cmp_ok(+bp: Nat, a: SB.Big, b: SB.Big, hb: SB.Le(1n, bp), wa: SB.Big.wf(bp, a), wb: SB.Big.wf(bp, b)) -> {RB.Big.cmp(bp, a, b) == S.Z.cmp(SB.Big.val(bp, a), SB.Big.val(bp, b)) : Cmp}:
  match a b:
    case SB.BPos{+x} SB.BPos{+y}:
      Equal.trans(Cmp, RM.Mag.cmp(x, y), Nat.cmp(SB.Mag.val(bp, x), SB.Mag.val(bp, y)), S.Z.cmp(S.Z.of_diff(SB.Mag.val(bp, x), 0n), S.Z.of_diff(SB.Mag.val(bp, y), 0n)), LM.cmp_ok(bp, x, y, wa, wb),
        Equal.trans(Cmp, Nat.cmp(SB.Mag.val(bp, x), SB.Mag.val(bp, y)), Nat.cmp(Nat.add(SB.Mag.val(bp, x), 0n), Nat.add(SB.Mag.val(bp, y), 0n)), S.Z.cmp(S.Z.of_diff(SB.Mag.val(bp, x), 0n), S.Z.of_diff(SB.Mag.val(bp, y), 0n)), O.cmp_add_r(SB.Mag.val(bp, x), SB.Mag.val(bp, y), 0n),
          LZ.cmp_parts(S.Z.of_diff(SB.Mag.val(bp, x), 0n), S.Z.of_diff(SB.Mag.val(bp, y), 0n), SB.Mag.val(bp, x), 0n, SB.Mag.val(bp, y), 0n, LZ.pnat_pos(SB.Mag.val(bp, x)), LZ.nnat_pos(SB.Mag.val(bp, x)), LZ.pnat_pos(SB.Mag.val(bp, y)), LZ.nnat_pos(SB.Mag.val(bp, y)))))
    case SB.BPos{+x} SB.BNeg{+y}:
      Equal.trans(Cmp, RM.Mag.cmpz(RM.Mag.add(bp, x, y)), Nat.cmp(Nat.add(SB.Mag.val(bp, x), SB.Mag.val(bp, y)), 0n), S.Z.cmp(S.Z.of_diff(SB.Mag.val(bp, x), 0n), S.Z.of_diff(0n, SB.Mag.val(bp, y))),
        cmpz_add(bp, x, y, hb, wa, wb),
        LZ.cmp_parts(S.Z.of_diff(SB.Mag.val(bp, x), 0n), S.Z.of_diff(0n, SB.Mag.val(bp, y)), SB.Mag.val(bp, x), 0n, 0n, SB.Mag.val(bp, y), LZ.pnat_pos(SB.Mag.val(bp, x)), LZ.nnat_pos(SB.Mag.val(bp, x)), LZ.pnat_neg(SB.Mag.val(bp, y)), LZ.nnat_neg(SB.Mag.val(bp, y))))
    case SB.BNeg{+x} SB.BPos{+y}:
      Equal.trans(Cmp, RM.Mag.zcmp(RM.Mag.add(bp, y, x)), Nat.cmp(0n, Nat.add(SB.Mag.val(bp, y), SB.Mag.val(bp, x))), S.Z.cmp(S.Z.of_diff(0n, SB.Mag.val(bp, x)), S.Z.of_diff(SB.Mag.val(bp, y), 0n)),
        zcmp_add(bp, y, x, hb, wb, wa),
        LZ.cmp_parts(S.Z.of_diff(0n, SB.Mag.val(bp, x)), S.Z.of_diff(SB.Mag.val(bp, y), 0n), 0n, SB.Mag.val(bp, x), SB.Mag.val(bp, y), 0n, LZ.pnat_neg(SB.Mag.val(bp, x)), LZ.nnat_neg(SB.Mag.val(bp, x)), LZ.pnat_pos(SB.Mag.val(bp, y)), LZ.nnat_pos(SB.Mag.val(bp, y))))
    case SB.BNeg{+x} SB.BNeg{+y}:
      Equal.trans(Cmp, RM.Mag.cmp(y, x), Nat.cmp(SB.Mag.val(bp, y), SB.Mag.val(bp, x)), S.Z.cmp(S.Z.of_diff(0n, SB.Mag.val(bp, x)), S.Z.of_diff(0n, SB.Mag.val(bp, y))), LM.cmp_ok(bp, y, x, wb, wa),
        LZ.cmp_parts(S.Z.of_diff(0n, SB.Mag.val(bp, x)), S.Z.of_diff(0n, SB.Mag.val(bp, y)), 0n, SB.Mag.val(bp, x), 0n, SB.Mag.val(bp, y), LZ.pnat_neg(SB.Mag.val(bp, x)), LZ.nnat_neg(SB.Mag.val(bp, x)), LZ.pnat_neg(SB.Mag.val(bp, y)), LZ.nnat_neg(SB.Mag.val(bp, y))))
