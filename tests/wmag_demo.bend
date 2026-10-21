# Runtime magnitudes in a base 2^L (rt/wmag.bend): lib/wmagpf.bend's laws at
# the base RW.wbp(lp) the solver uses, for every lp (the CLI passes 22: a
# closed 2^23 would be unfolded to unary by the checker), and concrete
# examples computed by {==} in base 4 (lp = 1, bp = 3).

import Base
import ../spec/num.bend as S
import ../spec/big.bend as SB
import ../lib/qreduce.bend as QRD
import ../rt/wmag.bend as RW
import ../lib/wmagpf.bend as WM

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

def main() -> Nat:
  0n
