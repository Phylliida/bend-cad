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

# Comparison
# ----------

# the high parts' verdict o, refined by limbs below the base, is the verdict
# of the whole numbers
def fin_ok(+bp: Nat, o: Cmp, +ah: Nat, +bh: Nat, +x: Nat, +y: Nat, e: {o == Nat.cmp(x, y) : Cmp}, la: SB.Le(ah, bp), lb: SB.Le(bh, bp))
  -> {RM.Mag.cmp.fin(o, ah, bh) == Nat.cmp(Nat.add(ah, Nat.mul(x, 1n+bp)), Nat.add(bh, Nat.mul(y, 1n+bp))) : Cmp}:
  match o:
    case LT{}:
      O.lt_cmp(Nat.add(ah, Nat.mul(x, 1n+bp)), Nat.add(bh, Nat.mul(y, 1n+bp)), O.lift_lt(bp, ah, bh, x, y, la, O.cmp_lt(x, y, e)))
    case EQ{}:
      %NR.nat_cmp_eq(x, y, e) : {Nat.cmp(ah, bh) == Nat.cmp(Nat.add(ah, Nat.mul(x, 1n+bp)), Nat.add(bh, Nat.mul(_, 1n+bp))) : Cmp}
      O.cmp_add_r(ah, bh, Nat.mul(x, 1n+bp))
    case GT{}:
      O.gt_cmp(Nat.add(ah, Nat.mul(x, 1n+bp)), Nat.add(bh, Nat.mul(y, 1n+bp)), O.lift_lt(bp, bh, ah, y, x, lb, O.cmp_gt(x, y, e)))

def cmpz_ok(+bp: Nat, a: List<&2, Nat>, wa: SB.Mag.wf(bp, a)) -> {RM.Mag.cmpz(a) == Nat.cmp(SB.Mag.val(bp, a), 0n) : Cmp}:
  match a:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      (lh, wt) = wa
      fin_ok(bp, RM.Mag.cmpz(t), h, 0n, SB.Mag.val(bp, t), 0n, cmpz_ok(bp, t, wt), lh, (bp, {==}))

def zcmp_ok(+bp: Nat, b: List<&2, Nat>, wb: SB.Mag.wf(bp, b)) -> {RM.Mag.zcmp(b) == Nat.cmp(0n, SB.Mag.val(bp, b)) : Cmp}:
  match b:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      (lh, wt) = wb
      fin_ok(bp, RM.Mag.zcmp(t), 0n, h, 0n, SB.Mag.val(bp, t), zcmp_ok(bp, t, wt), (bp, {==}), lh)

# Mag.cmp compares the values of well-formed magnitudes
def cmp_ok(+bp: Nat, a: List<&2, Nat>, b: List<&2, Nat>, wa: SB.Mag.wf(bp, a), wb: SB.Mag.wf(bp, b)) -> {RM.Mag.cmp(a, b) == Nat.cmp(SB.Mag.val(bp, a), SB.Mag.val(bp, b)) : Cmp}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{bh, bt}:
      zcmp_ok(bp, Con{bh, bt}, wb)
    case Con{ah, at} Nil{}:
      cmpz_ok(bp, Con{ah, at}, wa)
    case Con{+ah, +at} Con{+bh, +bt}:
      (la, wat) = wa
      (lb, wbt) = wb
      fin_ok(bp, RM.Mag.cmp(at, bt), ah, bh, SB.Mag.val(bp, at), SB.Mag.val(bp, bt), cmp_ok(bp, at, bt, wat, wbt), la, lb)

# Subtraction
# -----------
# Mag.sub.go(a, b, w) with b + w <= a: the precondition passes to the tails
# (pre0 without a borrow, pre1 with one), and each limb is an exact
# difference (O.sub_add).

def pre0.c(+bp: Nat, +ah: Nat, +bh: Nat, +w: Nat, +vat: Nat, +vbt: Nat, +j: Nat, +k: Nat, f: {Nat.add(Nat.add(bh, w), j) == ah : Nat}, e: {Nat.add(Nat.add(Nat.add(bh, Nat.mul(vbt, 1n+bp)), w), k) == Nat.add(ah, Nat.mul(vat, 1n+bp)) : Nat})
  -> {Nat.add(Nat.add(bh, w), Nat.add(Nat.mul(vbt, 1n+bp), k)) == Nat.add(Nat.add(bh, w), Nat.add(j, Nat.mul(vat, 1n+bp))) : Nat}:
  %NR.ring_eq([bh, w, j, k, vbt, vat, bp], NR.NAdd{NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}, NR.NVar{2n}}, NR.NMul{NR.NVar{5n}, NR.NAdd{NR.NCst{1n}, NR.NVar{6n}}}}, NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}, NR.NAdd{NR.NVar{2n}, NR.NMul{NR.NVar{5n}, NR.NAdd{NR.NCst{1n}, NR.NVar{6n}}}}}, {==}) : {Nat.add(Nat.add(bh, w), Nat.add(Nat.mul(vbt, 1n+bp), k)) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(bh, w), j), ah, f) : {Nat.add(Nat.add(bh, w), Nat.add(Nat.mul(vbt, 1n+bp), k)) == Nat.add(_, Nat.mul(vat, 1n+bp)) : Nat}
  %NR.ring_eq([bh, w, j, k, vbt, vat, bp], NR.NAdd{NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{4n}, NR.NAdd{NR.NCst{1n}, NR.NVar{6n}}}}, NR.NVar{1n}}, NR.NVar{3n}}, NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}, NR.NAdd{NR.NMul{NR.NVar{4n}, NR.NAdd{NR.NCst{1n}, NR.NVar{6n}}}, NR.NVar{3n}}}, {==}) : {_ == Nat.add(ah, Nat.mul(vat, 1n+bp)) : Nat}
  e

def pre0.jb.eq(+bp: Nat, -ah: Nat, +t: Nat, +j: Nat, +m0: Nat, f: {Nat.add(t, j) == ah : Nat}, g0: {Nat.add(ah, m0) == bp : Nat}) -> {Nat.add(j, Nat.add(t, m0)) == bp : Nat}:
  %g0 : {Nat.add(j, Nat.add(t, m0)) == _ : Nat}
  %f : {Nat.add(j, Nat.add(t, m0)) == Nat.add(_, m0) : Nat}
  NR.ring_eq([j, t, m0], NR.NAdd{NR.NVar{0n}, NR.NAdd{NR.NVar{1n}, NR.NVar{2n}}}, NR.NAdd{NR.NAdd{NR.NVar{1n}, NR.NVar{0n}}, NR.NVar{2n}}, {==})

def pre0.jb(+bp: Nat, -ah: Nat, +t: Nat, +j: Nat, f: {Nat.add(t, j) == ah : Nat}, la: SB.Le(ah, bp)) -> SB.Le(j, bp):
  (+m0, g0) = la
  (Nat.add(t, m0), pre0.jb.eq(bp, ah, t, j, m0, f, g0))

def pre0.fin.eq(+bp: Nat, +vat: Nat, +vbt: Nat, +j: Nat, +k: Nat, +m: Nat, g: {Nat.add(j, m) == bp : Nat}, c1: {Nat.add(Nat.mul(vbt, 1n+bp), k) == Nat.add(j, Nat.mul(vat, 1n+bp)) : Nat})
  -> {Nat.add(Nat.mul(vbt, 1n+bp), Nat.add(k, m)) == Nat.add(bp, Nat.mul(vat, 1n+bp)) : Nat}:
  %g : {Nat.add(Nat.mul(vbt, 1n+bp), Nat.add(k, m)) == Nat.add(_, Nat.mul(vat, 1n+bp)) : Nat}
  %NR.ring_eq([vbt, vat, j, k, m, bp], NR.NAdd{NR.NAdd{NR.NVar{2n}, NR.NMul{NR.NVar{1n}, NR.NAdd{NR.NCst{1n}, NR.NVar{5n}}}}, NR.NVar{4n}}, NR.NAdd{NR.NAdd{NR.NVar{2n}, NR.NVar{4n}}, NR.NMul{NR.NVar{1n}, NR.NAdd{NR.NCst{1n}, NR.NVar{5n}}}}, {==}) : {Nat.add(Nat.mul(vbt, 1n+bp), Nat.add(k, m)) == _ : Nat}
  %c1 : {Nat.add(Nat.mul(vbt, 1n+bp), Nat.add(k, m)) == Nat.add(_, m) : Nat}
  NR.ring_eq([vbt, k, m, bp], NR.NAdd{NR.NMul{NR.NVar{0n}, NR.NAdd{NR.NCst{1n}, NR.NVar{3n}}}, NR.NAdd{NR.NVar{1n}, NR.NVar{2n}}}, NR.NAdd{NR.NAdd{NR.NMul{NR.NVar{0n}, NR.NAdd{NR.NCst{1n}, NR.NVar{3n}}}, NR.NVar{1n}}, NR.NVar{2n}}, {==})

def pre0.fin(+bp: Nat, +vat: Nat, +vbt: Nat, +j: Nat, +k: Nat, jb: SB.Le(j, bp), c1: {Nat.add(Nat.mul(vbt, 1n+bp), k) == Nat.add(j, Nat.mul(vat, 1n+bp)) : Nat}) -> SB.Le(vbt, vat):
  (+m, g) = jb
  O.le_mul_cancel(vbt, vat, bp, (Nat.add(k, m), pre0.fin.eq(bp, vat, vbt, j, k, m, g, c1)))

# no borrow (t = bh + w <= ah): vbt <= vat
def pre0(+bp: Nat, +ah: Nat, +bh: Nat, +w: Nat, +vat: Nat, +vbt: Nat, la: SB.Le(ah, bp), ht: SB.Le(Nat.add(bh, w), ah),
  hpre: SB.Le(Nat.add(Nat.add(bh, Nat.mul(vbt, 1n+bp)), w), Nat.add(ah, Nat.mul(vat, 1n+bp)))) -> SB.Le(Nat.add(vbt, 0n), vat):
  (+j, +f) = ht
  (+k, e) = hpre
  %N.add_zero(vbt) : SB.Le(_, vat)
  pre0.fin(bp, vat, vbt, j, k, pre0.jb(bp, ah, Nat.add(bh, w), j, f, la),
    N.add_cancel(Nat.add(bh, w), Nat.add(Nat.mul(vbt, 1n+bp), k), Nat.add(j, Nat.mul(vat, 1n+bp)), pre0.c(bp, ah, bh, w, vat, vbt, j, k, f, e)))

def pre1.c(+bp: Nat, +ah: Nat, +bh: Nat, +w: Nat, -vat: Nat, +vbt: Nat, +j: Nat, +k: Nat, f: {Nat.add(1n+ah, j) == Nat.add(bh, w) : Nat}, e: {Nat.add(Nat.add(Nat.add(bh, Nat.mul(vbt, 1n+bp)), w), k) == Nat.add(ah, Nat.mul(vat, 1n+bp)) : Nat})
  -> {Nat.add(ah, Nat.add(1n+j, Nat.add(Nat.mul(vbt, 1n+bp), k))) == Nat.add(ah, Nat.mul(vat, 1n+bp)) : Nat}:
  %NR.ring_eq([ah, j, vbt, k, bh, w, bp], NR.NAdd{NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}, NR.NVar{1n}}, NR.NAdd{NR.NMul{NR.NVar{2n}, NR.NAdd{NR.NCst{1n}, NR.NVar{6n}}}, NR.NVar{3n}}}, NR.NAdd{NR.NVar{0n}, NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NVar{1n}}, NR.NAdd{NR.NMul{NR.NVar{2n}, NR.NAdd{NR.NCst{1n}, NR.NVar{6n}}}, NR.NVar{3n}}}}, {==}) : {_ == Nat.add(ah, Nat.mul(vat, 1n+bp)) : Nat}
  %Equal.sym(Nat, Nat.add(1n+ah, j), Nat.add(bh, w), f) : {Nat.add(_, Nat.add(Nat.mul(vbt, 1n+bp), k)) == Nat.add(ah, Nat.mul(vat, 1n+bp)) : Nat}
  %NR.ring_eq([ah, j, vbt, k, bh, w, bp], NR.NAdd{NR.NAdd{NR.NAdd{NR.NVar{4n}, NR.NMul{NR.NVar{2n}, NR.NAdd{NR.NCst{1n}, NR.NVar{6n}}}}, NR.NVar{5n}}, NR.NVar{3n}}, NR.NAdd{NR.NAdd{NR.NVar{4n}, NR.NVar{5n}}, NR.NAdd{NR.NMul{NR.NVar{2n}, NR.NAdd{NR.NCst{1n}, NR.NVar{6n}}}, NR.NVar{3n}}}, {==}) : {_ == Nat.add(ah, Nat.mul(vat, 1n+bp)) : Nat}
  e

def pre1.fin.eq(+bp: Nat, -vat: Nat, +vbt: Nat, +j: Nat, +k: Nat, c2: {Nat.add(1n+j, Nat.add(Nat.mul(vbt, 1n+bp), k)) == Nat.mul(vat, 1n+bp) : Nat})
  -> {Nat.add(Nat.mul(Nat.add(vbt, 1n), 1n+bp), Nat.add(j, k)) == Nat.add(bp, Nat.mul(vat, 1n+bp)) : Nat}:
  %c2 : {Nat.add(Nat.mul(Nat.add(vbt, 1n), 1n+bp), Nat.add(j, k)) == Nat.add(bp, _) : Nat}
  NR.ring_eq([vbt, j, k, bp], NR.NAdd{NR.NMul{NR.NAdd{NR.NVar{0n}, NR.NCst{1n}}, NR.NAdd{NR.NCst{1n}, NR.NVar{3n}}}, NR.NAdd{NR.NVar{1n}, NR.NVar{2n}}}, NR.NAdd{NR.NVar{3n}, NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NVar{1n}}, NR.NAdd{NR.NMul{NR.NVar{0n}, NR.NAdd{NR.NCst{1n}, NR.NVar{3n}}}, NR.NVar{2n}}}}, {==})

# a borrow (ah < t = bh + w): vbt + 1 <= vat
def pre1(+bp: Nat, +ah: Nat, +bh: Nat, +w: Nat, +vat: Nat, +vbt: Nat, ht: SB.Le(1n+ah, Nat.add(bh, w)),
  hpre: SB.Le(Nat.add(Nat.add(bh, Nat.mul(vbt, 1n+bp)), w), Nat.add(ah, Nat.mul(vat, 1n+bp)))) -> SB.Le(Nat.add(vbt, 1n), vat):
  (+j, f) = ht
  (+k, e) = hpre
  O.le_mul_cancel(Nat.add(vbt, 1n), vat, bp, (Nat.add(j, k), pre1.fin.eq(bp, vat, vbt, j, k,
    N.add_cancel(ah, Nat.add(1n+j, Nat.add(Nat.mul(vbt, 1n+bp), k)), Nat.mul(vat, 1n+bp), pre1.c(bp, ah, bh, w, vat, vbt, j, k, f, e)))))

# no borrow: the limb is ah - t
def zero_case(+bp: Nat, +ah: Nat, +bh: Nat, +w: Nat, +at: List<&2, Nat>, +bt: List<&2, Nat>, +ht0: SB.Le(Nat.add(bh, w), ah), la: SB.Le(ah, bp), hpre: SB.Le(Nat.add(Nat.add(bh, Nat.mul(SB.Mag.val(bp, bt), 1n+bp)), w), Nat.add(ah, Nat.mul(SB.Mag.val(bp, at), 1n+bp))),
  rec0: SB.Le(0n, 1n) -> SB.Le(Nat.add(SB.Mag.val(bp, bt), 0n), SB.Mag.val(bp, at)) -> {Nat.add(SB.Mag.val(bp, RM.Mag.sub.go(bp, at, bt, 0n)), Nat.add(SB.Mag.val(bp, bt), 0n)) == SB.Mag.val(bp, at) : Nat}) -> {Nat.add(Nat.add(Nat.sub(Nat.add(RM.Mag.bval(bp, 0n), ah), Nat.add(bh, w)), Nat.mul(SB.Mag.val(bp, RM.Mag.sub.go(bp, at, bt, 0n)), 1n+bp)), Nat.add(Nat.add(bh, Nat.mul(SB.Mag.val(bp, bt), 1n+bp)), w)) == Nat.add(ah, Nat.mul(SB.Mag.val(bp, at), 1n+bp)) : Nat}:
  %rec0((1n, {==}), pre0(bp, ah, bh, w, SB.Mag.val(bp, at), SB.Mag.val(bp, bt), la, ht0, hpre)) : {Nat.add(Nat.add(Nat.sub(Nat.add(RM.Mag.bval(bp, 0n), ah), Nat.add(bh, w)), Nat.mul(SB.Mag.val(bp, RM.Mag.sub.go(bp, at, bt, 0n)), 1n+bp)), Nat.add(Nat.add(bh, Nat.mul(SB.Mag.val(bp, bt), 1n+bp)), w)) == Nat.add(ah, Nat.mul(_, 1n+bp)) : Nat}
  %O.sub_add(ah, Nat.add(bh, w), ht0) : {Nat.add(Nat.add(Nat.sub(Nat.add(RM.Mag.bval(bp, 0n), ah), Nat.add(bh, w)), Nat.mul(SB.Mag.val(bp, RM.Mag.sub.go(bp, at, bt, 0n)), 1n+bp)), Nat.add(Nat.add(bh, Nat.mul(SB.Mag.val(bp, bt), 1n+bp)), w)) == Nat.add(_, Nat.mul(Nat.add(SB.Mag.val(bp, RM.Mag.sub.go(bp, at, bt, 0n)), Nat.add(SB.Mag.val(bp, bt), 0n)), 1n+bp)) : Nat}
  NR.ring_eq([Nat.sub(ah, Nat.add(bh, w)), SB.Mag.val(bp, RM.Mag.sub.go(bp, at, bt, 0n)), bh, SB.Mag.val(bp, bt), w, bp], NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{1n}, NR.NAdd{NR.NCst{1n}, NR.NVar{5n}}}}, NR.NAdd{NR.NAdd{NR.NVar{2n}, NR.NMul{NR.NVar{3n}, NR.NAdd{NR.NCst{1n}, NR.NVar{5n}}}}, NR.NVar{4n}}}, NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NAdd{NR.NVar{2n}, NR.NVar{4n}}}, NR.NMul{NR.NAdd{NR.NVar{1n}, NR.NAdd{NR.NVar{3n}, NR.NCst{0n}}}, NR.NAdd{NR.NCst{1n}, NR.NVar{5n}}}}, {==})

# bh + w <= B + ah
def t_le(+bp: Nat, +ah: Nat, +bh: Nat, +w: Nat, lb: SB.Le(bh, bp), hw: SB.Le(w, 1n)) -> SB.Le(Nat.add(bh, w), Nat.add(1n+bp, ah)):
  O.le_trans(Nat.add(bh, w), Nat.add(bp, 1n), Nat.add(1n+bp, ah), O.le_add_mono(bh, bp, w, 1n, lb, hw),
    (ah, NR.ring_eq([bp, ah], NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NCst{1n}}, NR.NVar{1n}}, NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}, NR.NVar{1n}}, {==})))

# a borrow: the limb is B + ah - t
def one_case(+bp: Nat, +ah: Nat, +bh: Nat, +w: Nat, +at: List<&2, Nat>, +bt: List<&2, Nat>, ht1: SB.Le(1n+ah, Nat.add(bh, w)), lb: SB.Le(bh, bp), hw: SB.Le(w, 1n), hpre: SB.Le(Nat.add(Nat.add(bh, Nat.mul(SB.Mag.val(bp, bt), 1n+bp)), w), Nat.add(ah, Nat.mul(SB.Mag.val(bp, at), 1n+bp))),
  rec1: SB.Le(1n, 1n) -> SB.Le(Nat.add(SB.Mag.val(bp, bt), 1n), SB.Mag.val(bp, at)) -> {Nat.add(SB.Mag.val(bp, RM.Mag.sub.go(bp, at, bt, 1n)), Nat.add(SB.Mag.val(bp, bt), 1n)) == SB.Mag.val(bp, at) : Nat}) -> {Nat.add(Nat.add(Nat.sub(Nat.add(RM.Mag.bval(bp, 1n), ah), Nat.add(bh, w)), Nat.mul(SB.Mag.val(bp, RM.Mag.sub.go(bp, at, bt, 1n)), 1n+bp)), Nat.add(Nat.add(bh, Nat.mul(SB.Mag.val(bp, bt), 1n+bp)), w)) == Nat.add(ah, Nat.mul(SB.Mag.val(bp, at), 1n+bp)) : Nat}:
  %rec1((0n, {==}), pre1(bp, ah, bh, w, SB.Mag.val(bp, at), SB.Mag.val(bp, bt), ht1, hpre)) : {Nat.add(Nat.add(Nat.sub(Nat.add(RM.Mag.bval(bp, 1n), ah), Nat.add(bh, w)), Nat.mul(SB.Mag.val(bp, RM.Mag.sub.go(bp, at, bt, 1n)), 1n+bp)), Nat.add(Nat.add(bh, Nat.mul(SB.Mag.val(bp, bt), 1n+bp)), w)) == Nat.add(ah, Nat.mul(_, 1n+bp)) : Nat}
  %NR.ring_eq([ah, SB.Mag.val(bp, RM.Mag.sub.go(bp, at, bt, 1n)), SB.Mag.val(bp, bt), bp], NR.NAdd{NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NVar{3n}}, NR.NVar{0n}}, NR.NMul{NR.NAdd{NR.NVar{1n}, NR.NVar{2n}}, NR.NAdd{NR.NCst{1n}, NR.NVar{3n}}}}, NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NAdd{NR.NVar{1n}, NR.NAdd{NR.NVar{2n}, NR.NCst{1n}}}, NR.NAdd{NR.NCst{1n}, NR.NVar{3n}}}}, {==}) : {Nat.add(Nat.add(Nat.sub(Nat.add(RM.Mag.bval(bp, 1n), ah), Nat.add(bh, w)), Nat.mul(SB.Mag.val(bp, RM.Mag.sub.go(bp, at, bt, 1n)), 1n+bp)), Nat.add(Nat.add(bh, Nat.mul(SB.Mag.val(bp, bt), 1n+bp)), w)) == _ : Nat}
  %O.sub_add(Nat.add(1n+bp, ah), Nat.add(bh, w), t_le(bp, ah, bh, w, lb, hw)) : {Nat.add(Nat.add(Nat.sub(Nat.add(RM.Mag.bval(bp, 1n), ah), Nat.add(bh, w)), Nat.mul(SB.Mag.val(bp, RM.Mag.sub.go(bp, at, bt, 1n)), 1n+bp)), Nat.add(Nat.add(bh, Nat.mul(SB.Mag.val(bp, bt), 1n+bp)), w)) == Nat.add(_, Nat.mul(Nat.add(SB.Mag.val(bp, RM.Mag.sub.go(bp, at, bt, 1n)), SB.Mag.val(bp, bt)), 1n+bp)) : Nat}
  NR.ring_eq([Nat.sub(Nat.add(1n+bp, ah), Nat.add(bh, w)), SB.Mag.val(bp, RM.Mag.sub.go(bp, at, bt, 1n)), bh, SB.Mag.val(bp, bt), w, bp], NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NMul{NR.NVar{1n}, NR.NAdd{NR.NCst{1n}, NR.NVar{5n}}}}, NR.NAdd{NR.NAdd{NR.NVar{2n}, NR.NMul{NR.NVar{3n}, NR.NAdd{NR.NCst{1n}, NR.NVar{5n}}}}, NR.NVar{4n}}}, NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NAdd{NR.NVar{2n}, NR.NVar{4n}}}, NR.NMul{NR.NAdd{NR.NVar{1n}, NR.NVar{3n}}, NR.NAdd{NR.NCst{1n}, NR.NVar{5n}}}}, {==})

def le_of_eq.go(+t: Nat, ah: Nat, eq: {ah == t : Nat}) -> {Nat.add(t, 0n) == ah : Nat}:
  %eq : {Nat.add(_, 0n) == ah : Nat}
  Equal.sym(Nat, ah, Nat.add(ah, 0n), N.add_zero(ah))

def le_of_eq(+t: Nat, ah: Nat, eq: {ah == t : Nat}) -> SB.Le(t, ah):
  (0n, le_of_eq.go(t, ah, eq))

def sub_step(+bp: Nat, o: Cmp, +ah: Nat, +bh: Nat, +w: Nat, +at: List<&2, Nat>, +bt: List<&2, Nat>, e: {o == Nat.cmp(ah, Nat.add(bh, w)) : Cmp},
  la: SB.Le(ah, bp), lb: SB.Le(bh, bp), hw: SB.Le(w, 1n), hpre: SB.Le(Nat.add(Nat.add(bh, Nat.mul(SB.Mag.val(bp, bt), 1n+bp)), w), Nat.add(ah, Nat.mul(SB.Mag.val(bp, at), 1n+bp))), rec: SB.Le(RM.Mag.borrow.fin(o), 1n) -> SB.Le(Nat.add(SB.Mag.val(bp, bt), RM.Mag.borrow.fin(o)), SB.Mag.val(bp, at)) -> {Nat.add(SB.Mag.val(bp, RM.Mag.sub.go(bp, at, bt, RM.Mag.borrow.fin(o))), Nat.add(SB.Mag.val(bp, bt), RM.Mag.borrow.fin(o))) == SB.Mag.val(bp, at) : Nat}) -> {Nat.add(Nat.add(Nat.sub(Nat.add(RM.Mag.bval(bp, RM.Mag.borrow.fin(o)), ah), Nat.add(bh, w)), Nat.mul(SB.Mag.val(bp, RM.Mag.sub.go(bp, at, bt, RM.Mag.borrow.fin(o))), 1n+bp)), Nat.add(Nat.add(bh, Nat.mul(SB.Mag.val(bp, bt), 1n+bp)), w)) == Nat.add(ah, Nat.mul(SB.Mag.val(bp, at), 1n+bp)) : Nat}:
  match o:
    case LT{}:
      one_case(bp, ah, bh, w, at, bt, O.cmp_lt(ah, Nat.add(bh, w), e), lb, hw, hpre, rec)
    case EQ{}:
      zero_case(bp, ah, bh, w, at, bt, le_of_eq(Nat.add(bh, w), ah, NR.nat_cmp_eq(ah, Nat.add(bh, w), e)), la, hpre, rec)
    case GT{}:
      zero_case(bp, ah, bh, w, at, bt, O.le_weaken(Nat.add(bh, w), ah, O.cmp_gt(ah, Nat.add(bh, w), e)), la, hpre, rec)

# Mag.sub.go subtracts: for b + w <= a, result + (b + w) = a
def sub_go_val(+bp: Nat, a: List<&2, Nat>, b: List<&2, Nat>, +w: Nat, hw: SB.Le(w, 1n), wa: SB.Mag.wf(bp, a), wb: SB.Mag.wf(bp, b), hpre: SB.Le(Nat.add(SB.Mag.val(bp, b), w), SB.Mag.val(bp, a)))
  -> {Nat.add(SB.Mag.val(bp, RM.Mag.sub.go(bp, a, b, w)), Nat.add(SB.Mag.val(bp, b), w)) == SB.Mag.val(bp, a) : Nat}:
  match a b:
    case Nil{} bb:
      O.le_zero(Nat.add(SB.Mag.val(bp, bb), w), hpre)
    case Con{+ah, +at} Nil{}:
      (la, wat) = wa
      sub_step(bp, Nat.cmp(ah, Nat.add(0n, w)), ah, 0n, w, at, Nil{}, {==}, la, (bp, {==}), hw, hpre,
        h2 => h3 => sub_go_val(bp, at, Nil{}, RM.Mag.borrow(ah, Nat.add(0n, w)), h2, wat, Unit{}, h3))
    case Con{+ah, +at} Con{+bh, +bt}:
      (la, wat) = wa
      (lb, wbt) = wb
      sub_step(bp, Nat.cmp(ah, Nat.add(bh, w)), ah, bh, w, at, bt, {==}, la, lb, hw, hpre,
        h2 => h3 => sub_go_val(bp, at, bt, RM.Mag.borrow(ah, Nat.add(bh, w)), h2, wat, wbt, h3))

def le_add0.go(+x: Nat, -y: Nat, -k: Nat, e: {Nat.add(x, k) == y : Nat}) -> {Nat.add(Nat.add(x, 0n), k) == y : Nat}:
  %N.add_zero(x) : {Nat.add(_, k) == y : Nat}
  e

def le_add0(x: Nat, -y: Nat, h: SB.Le(x, y)) -> SB.Le(Nat.add(x, 0n), y):
  (+k, e) = h
  (k, le_add0.go(x, y, k, e))

# Mag.sub subtracts: for b <= a, (a - b) + b = a
def sub_val(+bp: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, wa: SB.Mag.wf(bp, a), wb: SB.Mag.wf(bp, b), h: SB.Le(SB.Mag.val(bp, b), SB.Mag.val(bp, a)))
  -> {Nat.add(SB.Mag.val(bp, RM.Mag.sub(bp, a, b)), SB.Mag.val(bp, b)) == SB.Mag.val(bp, a) : Nat}:
  %norm_val(bp, RM.Mag.sub.go(bp, a, b, 0n)) : {Nat.add(_, SB.Mag.val(bp, b)) == SB.Mag.val(bp, a) : Nat}
  Equal.trans(Nat, Nat.add(SB.Mag.val(bp, RM.Mag.sub.go(bp, a, b, 0n)), SB.Mag.val(bp, b)), Nat.add(SB.Mag.val(bp, RM.Mag.sub.go(bp, a, b, 0n)), Nat.add(SB.Mag.val(bp, b), 0n)), SB.Mag.val(bp, a),
    Equal.cong(Nat, Nat, n => Nat.add(SB.Mag.val(bp, RM.Mag.sub.go(bp, a, b, 0n)), n), SB.Mag.val(bp, b), Nat.add(SB.Mag.val(bp, b), 0n), N.add_zero(SB.Mag.val(bp, b))),
    sub_go_val(bp, a, b, 0n, (1n, {==}), wa, wb, le_add0(SB.Mag.val(bp, b), SB.Mag.val(bp, a), h)))

def borrow_le(o: Cmp) -> SB.Le(RM.Mag.borrow.fin(o), 1n):
  match o:
    case LT{}:
      (0n, {==})
    case EQ{}:
      (1n, {==})
    case GT{}:
      (1n, {==})

def lw1.eq(+bp: Nat, +ah: Nat, +bh: Nat, +w: Nat, +j: Nat, f: {Nat.add(1n+ah, j) == Nat.add(bh, w) : Nat}, sa: {Nat.add(Nat.sub(Nat.add(1n+bp, ah), Nat.add(bh, w)), Nat.add(bh, w)) == Nat.add(1n+bp, ah) : Nat})
  -> {Nat.add(1n+ah, Nat.add(Nat.sub(Nat.add(1n+bp, ah), Nat.add(bh, w)), j)) == Nat.add(1n+ah, bp) : Nat}:
  %NR.ring_eq([ah, bp], NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NVar{1n}}, NR.NVar{0n}}, NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}, NR.NVar{1n}}, {==}) : {Nat.add(1n+ah, Nat.add(Nat.sub(Nat.add(1n+bp, ah), Nat.add(bh, w)), j)) == _ : Nat}
  %sa : {Nat.add(1n+ah, Nat.add(Nat.sub(Nat.add(1n+bp, ah), Nat.add(bh, w)), j)) == _ : Nat}
  %f : {Nat.add(1n+ah, Nat.add(Nat.sub(Nat.add(1n+bp, ah), Nat.add(bh, w)), j)) == Nat.add(Nat.sub(Nat.add(1n+bp, ah), Nat.add(bh, w)), _) : Nat}
  NR.ring_eq([ah, Nat.sub(Nat.add(1n+bp, ah), Nat.add(bh, w)), j], NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}, NR.NAdd{NR.NVar{1n}, NR.NVar{2n}}}, NR.NAdd{NR.NVar{1n}, NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}, NR.NVar{2n}}}, {==})

def lw1(+bp: Nat, +ah: Nat, +bh: Nat, +w: Nat, ht1: SB.Le(1n+ah, Nat.add(bh, w)), lb: SB.Le(bh, bp), hw: SB.Le(w, 1n)) -> SB.Le(Nat.sub(Nat.add(1n+bp, ah), Nat.add(bh, w)), bp):
  (+j, f) = ht1
  (j, N.add_cancel(1n+ah, Nat.add(Nat.sub(Nat.add(1n+bp, ah), Nat.add(bh, w)), j), bp, lw1.eq(bp, ah, bh, w, j, f, O.sub_add(Nat.add(1n+bp, ah), Nat.add(bh, w), t_le(bp, ah, bh, w, lb, hw)))))

def lw0(+bp: Nat, +ah: Nat, +t: Nat, +ht0: SB.Le(t, ah), la: SB.Le(ah, bp)) -> SB.Le(Nat.sub(ah, t), bp):
  O.le_trans(Nat.sub(ah, t), ah, bp, (t, O.sub_add(ah, t, ht0)), la)

# each limb of a subtraction is below the base
def limb_le(+bp: Nat, o: Cmp, +ah: Nat, +bh: Nat, +w: Nat, e: {o == Nat.cmp(ah, Nat.add(bh, w)) : Cmp}, la: SB.Le(ah, bp), lb: SB.Le(bh, bp), hw: SB.Le(w, 1n))
  -> SB.Le(Nat.sub(Nat.add(RM.Mag.bval(bp, RM.Mag.borrow.fin(o)), ah), Nat.add(bh, w)), bp):
  match o:
    case LT{}:
      lw1(bp, ah, bh, w, O.cmp_lt(ah, Nat.add(bh, w), e), lb, hw)
    case EQ{}:
      lw0(bp, ah, Nat.add(bh, w), le_of_eq(Nat.add(bh, w), ah, NR.nat_cmp_eq(ah, Nat.add(bh, w), e)), la)
    case GT{}:
      lw0(bp, ah, Nat.add(bh, w), O.le_weaken(Nat.add(bh, w), ah, O.cmp_gt(ah, Nat.add(bh, w), e)), la)

def sub_go_wf(+bp: Nat, a: List<&2, Nat>, b: List<&2, Nat>, +w: Nat, hw: SB.Le(w, 1n), wa: SB.Mag.wf(bp, a), wb: SB.Mag.wf(bp, b)) -> SB.Mag.wf(bp, RM.Mag.sub.go(bp, a, b, w)):
  match a b:
    case Nil{} bb:
      Unit{}
    case Con{+ah, at} Nil{}:
      (la, wat) = wa
      (limb_le(bp, Nat.cmp(ah, Nat.add(0n, w)), ah, 0n, w, {==}, la, (bp, {==}), hw),
        sub_go_wf(bp, at, Nil{}, RM.Mag.borrow(ah, Nat.add(0n, w)), borrow_le(Nat.cmp(ah, Nat.add(0n, w))), wat, Unit{}))
    case Con{+ah, at} Con{+bh, bt}:
      (la, wat) = wa
      (lb, wbt) = wb
      (limb_le(bp, Nat.cmp(ah, Nat.add(bh, w)), ah, bh, w, {==}, la, lb, hw),
        sub_go_wf(bp, at, bt, RM.Mag.borrow(ah, Nat.add(bh, w)), borrow_le(Nat.cmp(ah, Nat.add(bh, w))), wat, wbt))

def sub_wf(+bp: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, wa: SB.Mag.wf(bp, a), wb: SB.Mag.wf(bp, b)) -> SB.Mag.wf(bp, RM.Mag.sub(bp, a, b)):
  norm_wf(bp, RM.Mag.sub.go(bp, a, b, 0n), sub_go_wf(bp, a, b, 0n, (1n, {==}), wa, wb))
