# Runtime magnitudes compute what they mean: Mag.val of the result of add,
# mul1, mul and norm is the unary sum / product (lib/natord.bend supplies
# Euclid's division; the Nat normalizer does the rearranging).

import Base
import ./nat.bend as N
import ./natring.bend as NR
import ./natord.bend as O
import ../spec/big.bend as SB
import ../rt/mag.bend as RM

# one carry step: s + X*B = (s mod B) + (X + s div B)*B
def digit_step(+bp: Nat, +s: Nat, +x: Nat) -> {Nat.add(s, Nat.mul(x, 1n+bp)) == Nat.add(Nat.mod(s, 1n+bp), Nat.mul(Nat.add(x, Nat.div(s, 1n+bp)), 1n+bp)) : Nat}:
  %NR.ring_eq([Nat.mod(s, 1n+bp), Nat.div(s, 1n+bp), x, bp], NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{1n}, NR.NAdd{NR.NCst{1n}, NR.NVar{3n}}}}, NR.NMul{NR.NVar{2n}, NR.NAdd{NR.NCst{1n}, NR.NVar{3n}}}}, NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NAdd{NR.NVar{2n}, NR.NVar{1n}}, NR.NAdd{NR.NCst{1n}, NR.NVar{3n}}}}, {==}) : {Nat.add(s, Nat.mul(x, 1n+bp)) == _ : Nat}
  %O.divmod_eq(s, bp) : {Nat.add(s, Nat.mul(x, 1n+bp)) == Nat.add(_, Nat.mul(x, 1n+bp)) : Nat}
  {==}

def limb_val(+bp: Nat, c: Nat) -> {c == SB.Mag.val(bp, RM.Mag.limb(c)) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+k:
      %N.add_zero(k) : {1n+k == 1n+_ : Nat}
      {==}

def addc_val(+bp: Nat, a: List<&2, Nat>, +c: Nat) -> {Nat.add(SB.Mag.val(bp, a), c) == SB.Mag.val(bp, RM.Mag.addc(bp, a, c)) : Nat}:
  match a:
    case Nil{}:
      limb_val(bp, c)
    case Con{+h, +t}:
      %addc_val(bp, t, Nat.div(Nat.add(h, c), 1n+bp)) : {Nat.add(SB.Mag.val(bp, Con{h, t}), c) == Nat.add(Nat.mod(Nat.add(h, c), 1n+bp), Nat.mul(_, 1n+bp)) : Nat}
      %digit_step(bp, Nat.add(h, c), SB.Mag.val(bp, t)) : {Nat.add(SB.Mag.val(bp, Con{h, t}), c) == _ : Nat}
      NR.ring_eq([h, c, SB.Mag.val(bp, t), bp], NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{2n}, NR.NAdd{NR.NCst{1n}, NR.NVar{3n}}}}, NR.NVar{1n}}, NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}, NR.NMul{NR.NVar{2n}, NR.NAdd{NR.NCst{1n}, NR.NVar{3n}}}}, {==})

def add_go_val(+bp: Nat, a: List<&2, Nat>, b: List<&2, Nat>, +c: Nat) -> {Nat.add(Nat.add(SB.Mag.val(bp, a), SB.Mag.val(bp, b)), c) == SB.Mag.val(bp, RM.Mag.add.go(bp, a, b, c)) : Nat}:
  match a b:
    case Nil{} Nil{}:
      limb_val(bp, c)
    case Nil{} Con{+bh, +bt}:
      addc_val(bp, Con{bh, bt}, c)
    case Con{+ah, +at} Nil{}:
      %N.add_zero(SB.Mag.val(bp, Con{ah, at})) : {Nat.add(_, c) == SB.Mag.val(bp, RM.Mag.addc(bp, Con{ah, at}, c)) : Nat}
      addc_val(bp, Con{ah, at}, c)
    case Con{+ah, +at} Con{+bh, +bt}:
      %add_go_val(bp, at, bt, Nat.div(Nat.add(Nat.add(ah, bh), c), 1n+bp)) : {Nat.add(Nat.add(SB.Mag.val(bp, Con{ah, at}), SB.Mag.val(bp, Con{bh, bt})), c) == Nat.add(Nat.mod(Nat.add(Nat.add(ah, bh), c), 1n+bp), Nat.mul(_, 1n+bp)) : Nat}
      %digit_step(bp, Nat.add(Nat.add(ah, bh), c), Nat.add(SB.Mag.val(bp, at), SB.Mag.val(bp, bt))) : {Nat.add(Nat.add(SB.Mag.val(bp, Con{ah, at}), SB.Mag.val(bp, Con{bh, bt})), c) == _ : Nat}
      NR.ring_eq([ah, bh, c, SB.Mag.val(bp, at), SB.Mag.val(bp, bt), bp], NR.NAdd{NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{3n}, NR.NAdd{NR.NCst{1n}, NR.NVar{5n}}}}, NR.NAdd{NR.NVar{1n}, NR.NMul{NR.NVar{4n}, NR.NAdd{NR.NCst{1n}, NR.NVar{5n}}}}}, NR.NVar{2n}}, NR.NAdd{NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}, NR.NVar{2n}}, NR.NMul{NR.NAdd{NR.NVar{3n}, NR.NVar{4n}}, NR.NAdd{NR.NCst{1n}, NR.NVar{5n}}}}, {==})

def add_val(+bp: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>) -> {Nat.add(SB.Mag.val(bp, a), SB.Mag.val(bp, b)) == SB.Mag.val(bp, RM.Mag.add(bp, a, b)) : Nat}:
  Equal.trans(Nat, Nat.add(SB.Mag.val(bp, a), SB.Mag.val(bp, b)), Nat.add(Nat.add(SB.Mag.val(bp, a), SB.Mag.val(bp, b)), 0n), SB.Mag.val(bp, RM.Mag.add(bp, a, b)),
    N.add_zero(Nat.add(SB.Mag.val(bp, a), SB.Mag.val(bp, b))), add_go_val(bp, a, b, 0n))

def mul1_val(+bp: Nat, a: List<&2, Nat>, +k: Nat, +c: Nat) -> {Nat.add(Nat.mul(SB.Mag.val(bp, a), k), c) == SB.Mag.val(bp, RM.Mag.mul1(bp, a, k, c)) : Nat}:
  match a:
    case Nil{}:
      limb_val(bp, c)
    case Con{+h, +t}:
      %mul1_val(bp, t, k, Nat.div(Nat.add(Nat.mul(h, k), c), 1n+bp)) : {Nat.add(Nat.mul(SB.Mag.val(bp, Con{h, t}), k), c) == Nat.add(Nat.mod(Nat.add(Nat.mul(h, k), c), 1n+bp), Nat.mul(_, 1n+bp)) : Nat}
      %digit_step(bp, Nat.add(Nat.mul(h, k), c), Nat.mul(SB.Mag.val(bp, t), k)) : {Nat.add(Nat.mul(SB.Mag.val(bp, Con{h, t}), k), c) == _ : Nat}
      NR.ring_eq([h, k, c, SB.Mag.val(bp, t), bp], NR.NAdd{NR.NMul{NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{3n}, NR.NAdd{NR.NCst{1n}, NR.NVar{4n}}}}, NR.NVar{1n}}, NR.NVar{2n}}, NR.NAdd{NR.NAdd{NR.NMul{NR.NVar{0n}, NR.NVar{1n}}, NR.NVar{2n}}, NR.NMul{NR.NMul{NR.NVar{3n}, NR.NVar{1n}}, NR.NAdd{NR.NCst{1n}, NR.NVar{4n}}}}, {==})

def mul_val(+bp: Nat, a: List<&2, Nat>, +b: List<&2, Nat>) -> {Nat.mul(SB.Mag.val(bp, a), SB.Mag.val(bp, b)) == SB.Mag.val(bp, RM.Mag.mul(bp, a, b)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %add_val(bp, RM.Mag.mul1(bp, b, h, 0n), Con{0n, RM.Mag.mul(bp, t, b)}) : {Nat.mul(SB.Mag.val(bp, Con{h, t}), SB.Mag.val(bp, b)) == _ : Nat}
      %mul1_val(bp, b, h, 0n) : {Nat.mul(SB.Mag.val(bp, Con{h, t}), SB.Mag.val(bp, b)) == Nat.add(_, SB.Mag.val(bp, Con{0n, RM.Mag.mul(bp, t, b)})) : Nat}
      %mul_val(bp, t, b) : {Nat.mul(SB.Mag.val(bp, Con{h, t}), SB.Mag.val(bp, b)) == Nat.add(Nat.add(Nat.mul(SB.Mag.val(bp, b), h), 0n), Nat.mul(_, 1n+bp)) : Nat}
      NR.ring_eq([h, SB.Mag.val(bp, t), SB.Mag.val(bp, b), bp], NR.NMul{NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{1n}, NR.NAdd{NR.NCst{1n}, NR.NVar{3n}}}}, NR.NVar{2n}}, NR.NAdd{NR.NAdd{NR.NMul{NR.NVar{2n}, NR.NVar{0n}}, NR.NCst{0n}}, NR.NMul{NR.NMul{NR.NVar{1n}, NR.NVar{2n}}, NR.NAdd{NR.NCst{1n}, NR.NVar{3n}}}}, {==})

def normcon_val(+bp: Nat, +h: Nat, t: List<&2, Nat>) -> {Nat.add(h, Nat.mul(SB.Mag.val(bp, t), 1n+bp)) == SB.Mag.val(bp, RM.Mag.norm.con(h, t)) : Nat}:
  match t:
    case Nil{}:
      %N.add_zero(h) : {_ == SB.Mag.val(bp, RM.Mag.limb(h)) : Nat}
      limb_val(bp, h)
    case Con{x, y}:
      {==}

def norm_val(+bp: Nat, m: List<&2, Nat>) -> {SB.Mag.val(bp, m) == SB.Mag.val(bp, RM.Mag.norm(m)) : Nat}:
  match m:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %normcon_val(bp, h, RM.Mag.norm(t)) : {Nat.add(h, Nat.mul(SB.Mag.val(bp, t), 1n+bp)) == _ : Nat}
      %norm_val(bp, t) : {Nat.add(h, Nat.mul(SB.Mag.val(bp, t), 1n+bp)) == Nat.add(h, Nat.mul(_, 1n+bp)) : Nat}
      {==}

# Well-formedness
# ---------------
# Results of well-formed inputs are well-formed (every limb below the base),
# given a base of at least 2. Each carry is bounded through O.div_le.

def limb_wf(+bp: Nat, c: Nat, h: SB.Le(c, bp)) -> SB.Mag.wf(bp, RM.Mag.limb(c)):
  match c:
    case 0n:
      Unit{}
    case 1n+k:
      (h, Unit{})

# bp + 1 <= bp + 1 * B
def le_carry1(+bp: Nat) -> SB.Le(Nat.add(bp, 1n), Nat.add(bp, Nat.mul(1n, 1n+bp))):
  (bp, NR.ring_eq([bp], NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NCst{1n}}, NR.NVar{0n}}, NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NCst{1n}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}}, {==}))

# (bp + bp) + 1 <= bp + 1 * B
def le_carry2(+bp: Nat) -> SB.Le(Nat.add(Nat.add(bp, bp), 1n), Nat.add(bp, Nat.mul(1n, 1n+bp))):
  (0n, NR.ring_eq([bp], NR.NAdd{NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NVar{0n}}, NR.NCst{1n}}, NR.NCst{0n}}, NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NCst{1n}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}}, {==}))

# bp * bp + bp <= bp + bp * B
def le_carryb(+bp: Nat) -> SB.Le(Nat.add(Nat.mul(bp, bp), bp), Nat.add(bp, Nat.mul(bp, 1n+bp))):
  (bp, NR.ring_eq([bp], NR.NAdd{NR.NAdd{NR.NMul{NR.NVar{0n}, NR.NVar{0n}}, NR.NVar{0n}}, NR.NVar{0n}}, NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{0n}, NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}}, {==}))

def addc_wf(+bp: Nat, a: List<&2, Nat>, +c: Nat, +hb: SB.Le(1n, bp), hc: SB.Le(c, 1n), wa: SB.Mag.wf(bp, a)) -> SB.Mag.wf(bp, RM.Mag.addc(bp, a, c)):
  match a:
    case Nil{}:
      limb_wf(bp, c, O.le_trans(c, 1n, bp, hc, hb))
    case Con{+h, t}:
      (lh, wt) = wa
      (O.mod_le(Nat.add(h, c), bp), addc_wf(bp, t, Nat.div(Nat.add(h, c), 1n+bp), hb,
        O.div_le(Nat.add(h, c), bp, 1n, O.le_trans(Nat.add(h, c), Nat.add(bp, 1n), Nat.add(bp, Nat.mul(1n, 1n+bp)), O.le_add_mono(h, bp, c, 1n, lh, hc), le_carry1(bp))),
        wt))

def add_go_wf(+bp: Nat, a: List<&2, Nat>, b: List<&2, Nat>, +c: Nat, +hb: SB.Le(1n, bp), hc: SB.Le(c, 1n), wa: SB.Mag.wf(bp, a), wb: SB.Mag.wf(bp, b)) -> SB.Mag.wf(bp, RM.Mag.add.go(bp, a, b, c)):
  match a b:
    case Nil{} Nil{}:
      limb_wf(bp, c, O.le_trans(c, 1n, bp, hc, hb))
    case Nil{} Con{bh, bt}:
      addc_wf(bp, Con{bh, bt}, c, hb, hc, wb)
    case Con{ah, at} Nil{}:
      addc_wf(bp, Con{ah, at}, c, hb, hc, wa)
    case Con{+ah, at} Con{+bh, bt}:
      (la, wat) = wa
      (lb, wbt) = wb
      (O.mod_le(Nat.add(Nat.add(ah, bh), c), bp), add_go_wf(bp, at, bt, Nat.div(Nat.add(Nat.add(ah, bh), c), 1n+bp), hb,
        O.div_le(Nat.add(Nat.add(ah, bh), c), bp, 1n, O.le_trans(Nat.add(Nat.add(ah, bh), c), Nat.add(Nat.add(bp, bp), 1n), Nat.add(bp, Nat.mul(1n, 1n+bp)),
          O.le_add_mono(Nat.add(ah, bh), Nat.add(bp, bp), c, 1n, O.le_add_mono(ah, bp, bh, bp, la, lb), hc), le_carry2(bp))),
        wat, wbt))

def add_wf(+bp: Nat, a: List<&2, Nat>, b: List<&2, Nat>, +hb: SB.Le(1n, bp), wa: SB.Mag.wf(bp, a), wb: SB.Mag.wf(bp, b)) -> SB.Mag.wf(bp, RM.Mag.add(bp, a, b)):
  add_go_wf(bp, a, b, 0n, hb, (1n, {==}), wa, wb)

def mul1_wf(+bp: Nat, a: List<&2, Nat>, +k: Nat, +c: Nat, +hk: SB.Le(k, bp), hc: SB.Le(c, bp), wa: SB.Mag.wf(bp, a)) -> SB.Mag.wf(bp, RM.Mag.mul1(bp, a, k, c)):
  match a:
    case Nil{}:
      limb_wf(bp, c, hc)
    case Con{+h, t}:
      (lh, wt) = wa
      (O.mod_le(Nat.add(Nat.mul(h, k), c), bp), mul1_wf(bp, t, k, Nat.div(Nat.add(Nat.mul(h, k), c), 1n+bp), hk,
        O.div_le(Nat.add(Nat.mul(h, k), c), bp, bp, O.le_trans(Nat.add(Nat.mul(h, k), c), Nat.add(Nat.mul(bp, bp), bp), Nat.add(bp, Nat.mul(bp, 1n+bp)),
          O.le_add_mono(Nat.mul(h, k), Nat.mul(bp, bp), c, bp, O.le_mul_mono(h, bp, k, bp, lh, hk), hc), le_carryb(bp))),
        wt))

def mul_wf(+bp: Nat, a: List<&2, Nat>, +b: List<&2, Nat>, +hb: SB.Le(1n, bp), wa: SB.Mag.wf(bp, a), +wb: SB.Mag.wf(bp, b)) -> SB.Mag.wf(bp, RM.Mag.mul(bp, a, b)):
  match a:
    case Nil{}:
      Unit{}
    case Con{+h, +t}:
      (lh, wt) = wa
      add_wf(bp, RM.Mag.mul1(bp, b, h, 0n), Con{0n, RM.Mag.mul(bp, t, b)}, hb,
        mul1_wf(bp, b, h, 0n, lh, (bp, {==}), wb),
        ((bp, {==}), mul_wf(bp, t, b, hb, wt, wb)))

def normcon_wf(+bp: Nat, h: Nat, t: List<&2, Nat>, lh: SB.Le(h, bp), wt: SB.Mag.wf(bp, t)) -> SB.Mag.wf(bp, RM.Mag.norm.con(h, t)):
  match t:
    case Nil{}:
      limb_wf(bp, h, lh)
    case Con{x, y}:
      (lh, wt)

def norm_wf(+bp: Nat, m: List<&2, Nat>, wm: SB.Mag.wf(bp, m)) -> SB.Mag.wf(bp, RM.Mag.norm(m)):
  match m:
    case Nil{}:
      Unit{}
    case Con{+h, +t}:
      (lh, wt) = wm
      normcon_wf(bp, h, RM.Mag.norm(t), lh, norm_wf(bp, t, wt))
