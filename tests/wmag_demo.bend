# Runtime magnitudes in a base 2^L (rt/wmag.bend): lib/wmagpf.bend's laws at
# the base RW.wbp(lp) the solver uses, for every lp (the CLI passes 22: a
# closed 2^23 would be unfolded to unary by the checker), and concrete
# examples computed by {==} in base 4 (lp = 1, bp = 3).

import Base
import ../spec/num.bend as S
import ../spec/big.bend as SB
import ../lib/qreduce.bend as QRD
import ../rt/wmag.bend as RW
import ../rt/wint.bend as RI
import ../lib/wmagpf.bend as WM
import ../lib/wintpf.bend as WI
import ../rt/wdyad.bend as RD
import ../lib/wdyadpf.bend as WDP
import ../lib/kinst.bend as KI
import ../lib/numer.bend as NU
import ../lib/wsigpf.bend as WSG
import ../lib/wnum.bend as WN
import ../lib/wnumpf.bend as WNP
import ../spec/knum.bend as N

# The laws at the solver's base
# -----------------------------

def shl_w(+lp: Nat, m: List<&2, Nat>, +k: Nat) -> {Nat.mul(SB.Mag.val(RW.wbp(lp), m), RW.pw(k)) == SB.Mag.val(RW.wbp(lp), RW.Mag.shl(RW.wbp(lp), lp, m, k)) : Nat}:
  WM.shl_val(RW.wbp(lp), lp, WM.wbp_ok(lp), m, k)

def shr_w(+lp: Nat, +m: List<&2, Nat>, +k: Nat, +wm: SB.Mag.wf(RW.wbp(lp), m)) -> WM.Floor(SB.Mag.val(RW.wbp(lp), m), RW.pw(k), SB.Mag.val(RW.wbp(lp), RW.Mag.shr(RW.wbp(lp), lp, m, k))):
  WM.shr_val(RW.wbp(lp), lp, WM.wbp_ok(lp), m, k, wm)

def round_w(+lp: Nat, +m: List<&2, Nat>, +k: Nat, +wm: SB.Mag.wf(RW.wbp(lp), m)) -> WM.Floor(Nat.add(SB.Mag.val(RW.wbp(lp), m), RW.pw(Nat.sub(k, 1n))), RW.pw(k), SB.Mag.val(RW.wbp(lp), RW.Mag.round(RW.wbp(lp), lp, m, k))):
  WM.round_val(RW.wbp(lp), lp, WM.wbp_ok(lp), m, k, wm)

def ofpos_w(+lp: Nat, +p: S.Pos) -> {S.Pos.nat(p) == SB.Mag.val(RW.wbp(lp), RW.Mag.ofpos(lp, p)) : Nat}:
  WM.ofpos_nat(RW.wbp(lp), lp, WM.wbp_ok(lp), p)

def bits_w(+lp: Nat, +p: S.Pos) -> {RW.Mag.bits(lp, RW.Mag.ofpos(lp, p)) == QRD.size(p) : Nat}:
  WM.ofpos_bits(RW.wbp(lp), lp, WM.wbp_ok(lp), p)

def topos_w(+lp: Nat, +p: S.Pos) -> {RW.Mag.topos(lp, RW.Mag.ofpos(lp, p)) == Some{p} : Maybe<&2, S.Pos>}:
  WM.topos_ofpos(RW.wbp(lp), lp, WM.wbp_ok(lp), p)

def canon_w(+lp: Nat, m1: List<&2, Nat>, m2: List<&2, Nat>, w1: SB.Mag.wf(RW.wbp(lp), m1), w2: SB.Mag.wf(RW.wbp(lp), m2), q1: WM.Top(m1), q2: WM.Top(m2), +e: {SB.Mag.val(RW.wbp(lp), m1) == SB.Mag.val(RW.wbp(lp), m2) : Nat}) -> {m1 == m2 : List<&2, Nat>}:
  WM.canon_eq(RW.wbp(lp), m1, m2, w1, w2, q1, q2, e)

# the word integers (rt/wint.bend): Big.ofz is z, canonical, and Big.toz
# takes it back; a canonical word integer is Big.ofz of its value
def ofz_w(+lp: Nat, z: S.Z) -> {SB.Big.val(RW.wbp(lp), RI.Big.ofz(lp, z)) == z : S.Z}:
  WI.ofz_val(RW.wbp(lp), lp, WM.wbp_ok(lp), z)

def toz_w(+lp: Nat, z: S.Z) -> {RI.Big.toz(lp, RI.Big.ofz(lp, z)) == z : S.Z}:
  WI.toz_ofz(RW.wbp(lp), lp, WM.wbp_ok(lp), z)

def ofval_w(+lp: Nat, +x: SB.Big, cx: WI.Canon(RW.wbp(lp), x)) -> {RI.Big.ofz(lp, SB.Big.val(RW.wbp(lp), x)) == x : SB.Big}:
  WI.ofz_of_val(RW.wbp(lp), lp, WM.wbp_ok(lp), x, cx)

def canonv_w(+lp: Nat, x: SB.Big) -> {SB.Big.val(RW.wbp(lp), RI.Big.canon(x)) == SB.Big.val(RW.wbp(lp), x) : S.Z}:
  WI.canon_val(RW.wbp(lp), x)

def shlz_w(+lp: Nat, x: SB.Big, +k: Nat) -> {SB.Big.val(RW.wbp(lp), RI.Big.shl(RW.wbp(lp), lp, x, k)) == S.Z.mul(SB.Big.val(RW.wbp(lp), x), S.Zpos{S.Pos.pow2(k)}) : S.Z}:
  WI.shl_zval(RW.wbp(lp), lp, WM.wbp_ok(lp), x, k)

# the word dyadics (rt/wdyad.bend) are S.D exactly
def tod_w(+lp: Nat, x: S.D) -> {RD.WD.tod(lp, RD.WD.ofd(lp, x)) == x : S.D}:
  WDP.tod_ofd(RW.wbp(lp), lp, WM.wbp_ok(lp), x)

def add_w(+lp: Nat, a: S.D, b: S.D) -> {RD.WD.add(RW.wbp(lp), lp, RD.WD.ofd(lp, a), RD.WD.ofd(lp, b)) == RD.WD.ofd(lp, S.D.add(a, b)) : RD.WD}:
  WDP.add_ok(RW.wbp(lp), lp, WM.wbp_ok(lp), a, b)

def mul_w(+lp: Nat, a: S.D, b: S.D) -> {RD.WD.mul(RW.wbp(lp), RD.WD.ofd(lp, a), RD.WD.ofd(lp, b)) == RD.WD.ofd(lp, S.D.mul(a, b)) : RD.WD}:
  WDP.mul_ok(RW.wbp(lp), lp, WM.wbp_ok(lp), a, b)

def neg_w(+lp: Nat, a: S.D) -> {RD.WD.neg(RD.WD.ofd(lp, a)) == RD.WD.ofd(lp, S.D.neg(a)) : RD.WD}:
  WDP.neg_ok(RW.wbp(lp), lp, WM.wbp_ok(lp), a)

def cmp_w(+lp: Nat, a: S.D, b: S.D) -> {RD.WD.cmp(RW.wbp(lp), lp, RD.WD.ofd(lp, a), RD.WD.ofd(lp, b)) == KI.dcmp(a, b) : Cmp}:
  WDP.cmp_ok(RW.wbp(lp), lp, WM.wbp_ok(lp), a, b)

# and so is their rounding (lib/numer.bend's dznorm, dsig, dround)
def znorm_w(+lp: Nat, x: S.D) -> {RD.WD.znorm(RD.WD.ofd(lp, x)) == RD.WD.ofd(lp, NU.dznorm(x)) : RD.WD}:
  WSG.znorm_ok(RW.wbp(lp), lp, WM.wbp_ok(lp), x)

def sig_w(+lp: Nat, x: S.D, +b: Nat) -> {RD.WD.sig(RW.wbp(lp), lp, RD.WD.ofd(lp, x), b) == RD.WD.ofd(lp, NU.dsig(x, b)) : RD.WD}:
  WSG.sig_ok(RW.wbp(lp), lp, WM.wbp_ok(lp), x, b)

def dround_w(+lp: Nat, x: S.D, +p: Nat) -> {RD.WD.round(RW.wbp(lp), lp, RD.WD.ofd(lp, x), p) == RD.WD.ofd(lp, NU.dround(x, p)) : RD.WD}:
  WSG.round_ok(RW.wbp(lp), lp, WM.wbp_ok(lp), x, p)

# the checker's numbers at words: WD.ofd commutes with the instance
def wadd_w(+lp: Nat, a: S.D, b: S.D) -> {N.nadd(WN.wnum(RW.wbp(lp), lp), RD.WD.ofd(lp, a), RD.WD.ofd(lp, b)) == RD.WD.ofd(lp, N.nadd(KI.dnum(), a, b)) : RD.WD}:
  WNP.w_add(RW.wbp(lp), lp, WM.wbp_ok(lp), a, b)

def wcmp_w(+lp: Nat, a: S.D, b: S.D) -> {N.ncmp(WN.wnum(RW.wbp(lp), lp), RD.WD.ofd(lp, a), RD.WD.ofd(lp, b)) == N.ncmp(KI.dnum(), a, b) : Cmp}:
  WNP.w_cmp(RW.wbp(lp), lp, WM.wbp_ok(lp), a, b)

# native bounds: limb products and sums are below 2^(2 L), and the run
# time's 2 L = 46 is within BendRT's 48-bit immediates
def mulb_w(+lp: Nat, +h: Nat, +k: Nat, +c: Nat, lh: SB.Le(h, RW.wbp(lp)), lk: SB.Le(k, RW.wbp(lp)), lc: SB.Le(c, RW.wbp(lp))) -> SB.Le(1n+Nat.add(Nat.mul(h, k), c), RW.pw(Nat.add(1n+lp, 1n+lp))):
  WM.mul_bound(RW.wbp(lp), lp, WM.wbp_ok(lp), h, k, c, lh, lk, lc)

def l23() -> SB.Le(Nat.add(1n+22n, 1n+22n), 48n):
  (2n, {==})

# Examples in base 4
# ------------------

# 13 = 1 + 3 * 4
def thirteen() -> S.Pos:
  S.XI{S.XO{S.XI{S.XH{}}}}

def ofpos13() -> {RW.Mag.ofpos(1n, thirteen()) == [1n, 3n] : List<&2, Nat>}:
  {==}

def topos13() -> {RW.Mag.topos(1n, [1n, 3n]) == Some{thirteen()} : Maybe<&2, S.Pos>}:
  {==}

# 13 * 8 = 104 = 0 + 2 * 4 + 2 * 16 + 1 * 64
def shl13() -> {RW.Mag.shl(3n, 1n, [1n, 3n], 3n) == [0n, 2n, 2n, 1n] : List<&2, Nat>}:
  {==}

def shr104() -> {RW.Mag.shr(3n, 1n, [0n, 2n, 2n, 1n], 3n) == [1n, 3n] : List<&2, Nat>}:
  {==}

# 13 / 4 = 3.25 rounds to 3; 14 / 4 = 3.5 rounds up to 4 = [0, 1]
def round13() -> {RW.Mag.round(3n, 1n, [1n, 3n], 2n) == [3n] : List<&2, Nat>}:
  {==}

def round14() -> {RW.Mag.round(3n, 1n, [2n, 3n], 2n) == [0n, 1n] : List<&2, Nat>}:
  {==}

def bits13() -> {RW.Mag.bits(1n, [1n, 3n]) == 4n : Nat}:
  {==}

def wbp1() -> {RW.wbp(1n) == 3n : Nat}:
  {==}

def ofz13() -> {RI.Big.ofz(1n, S.Zneg{thirteen()}) == SB.BNeg{[1n, 3n]} : SB.Big}:
  {==}

def toz13() -> {RI.Big.toz(1n, SB.BNeg{[1n, 3n]}) == S.Zneg{thirteen()} : S.Z}:
  {==}

# a negative zero and a high zero limb, canonical
def canon0() -> {RI.Big.canon(SB.BNeg{[0n, 0n]}) == SB.BPos{[]} : SB.Big}:
  {==}

def canon13() -> {RI.Big.canon(SB.BPos{[1n, 3n, 0n]}) == SB.BPos{[1n, 3n]} : SB.Big}:
  {==}

def shlm13() -> {RI.Big.shl(3n, 1n, SB.BNeg{[1n, 3n]}, 3n) == SB.BNeg{[0n, 2n, 2n, 1n]} : SB.Big}:
  {==}

# 13/4 + (-3)/2 = 7/4: the exponents aligned by a shift
def wadd13() -> {RD.WD.add(3n, 1n, RD.WD{SB.BPos{[1n, 3n]}, 2n}, RD.WD{SB.BNeg{[3n]}, 1n}) == RD.WD{SB.BPos{[3n, 1n]}, 2n} : RD.WD}:
  {==}

def wcmp13() -> {RD.WD.cmp(3n, 1n, RD.WD{SB.BPos{[1n, 3n]}, 2n}, RD.WD{SB.BNeg{[3n]}, 1n}) == GT{} : Cmp}:
  {==}

# 13/4 to 2 significant bits: 3, both ways
def wsig13() -> {RD.WD.sig(3n, 1n, RD.WD{SB.BPos{[1n, 3n]}, 2n}, 2n) == RD.WD{SB.BPos{[3n]}, 0n} : RD.WD}:
  {==}

def dsig13() -> {NU.dsig(S.D{S.Zpos{thirteen()}, 2n}, 2n) == S.D{S.Zpos{S.XI{S.XH{}}}, 0n} : S.D}:
  {==}

def main() -> Nat:
  0n
