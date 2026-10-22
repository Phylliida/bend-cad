# bend-cad: the word dyadics' rounding (rt/wdyad.bend: WD.znorm, WD.sig,
# WD.round) is lib/numer.bend's (dznorm, dsig, dround) exactly: on a
# converted dyadic each gives the conversion of numer's result, for every
# S.D input and every base. Through numer's pshr as a quotient (Floor),
# the word rounding's quotient (lib/wmagpf.bend: round_val) and its
# uniqueness.

# Generated from tools/drafts/wsigpf.draft by tools/expand.py; edit the
# draft.

import Base
import ./nat.bend as N
import ./natring.bend as NR
import ./natord.bend as O
import ./pos.bend as P
import ./z.bend as LZ
import ./zring.bend as R
import ./karith.bend as KA
import ./qreduce.bend as QRD
import ./numer.bend as NU
import ./wmagpf.bend as WM
import ./wintpf.bend as WI
import ./wdyadpf.bend as WDP
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/big.bend as SB
import ../rt/wmag.bend as RW
import ../rt/wint.bend as RI
import ../rt/wdyad.bend as RD


# Orders
# ------

# the native comparison is karith's natle
def le_natle(a: Nat, b: Nat) -> {RD.le(a, b) == KA.natle(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      {==}
    case 1n+i 1n+j:
      le_natle(i, j)

def natle_false(+a: Nat, +b: Nat, h: {KA.natle(a, b) == False{} : Bool}) -> SB.Le(1n+b, a):
  WDP.le_false(a, b, Equal.trans(Bool, RD.le(a, b), KA.natle(a, b), False{}, le_natle(a, b), h))

def sub_pos.c(+a: Nat, +b: Nat, +d: Nat, e: {Nat.add(1n+b, d) == a : Nat}) -> SB.Le(1n, Nat.sub(a, b)):
  %e : SB.Le(1n, Nat.sub(_, b))
  %NR.ring_eq([b, d], NR.NAdd{NR.NVar{0n}, NR.NAdd{NR.NCst{1n}, NR.NVar{1n}}}, NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}, NR.NVar{1n}}, {==}) : SB.Le(1n, Nat.sub(_, b))
  %Equal.sym(Nat, Nat.sub(Nat.add(b, 1n+d), b), 1n+d, WDP.sub_add_l(b, 1n+d)) : SB.Le(1n, _)
  (d, {==})

# b < a gives a - b >= 1
def sub_pos(+a: Nat, +b: Nat, h: SB.Le(1n+b, a)) -> SB.Le(1n, Nat.sub(a, b)):
  (+d, e) = h
  sub_pos.c(a, b, d, e)

# numer's pshr as a quotient
# --------------------------

def floor_two(+j: Nat) -> WM.Floor(1n, RW.pw(1n+j), 0n):
  ((1n, {==}), (%N.add_zero(RW.pw(1n+j)) : SB.Le(2n, _)
    O.le_mul_mono(2n, 2n, 1n, RW.pw(j), O.le_refl(2n), WM.pw_pos(j))))

# pshr(p, k) = floor(p / 2^k)
def pshr_floor(p: S.Pos, k: Nat) -> WM.Floor(S.Pos.nat(p), RW.pw(k), S.Z.pnat(NU.pshr(p, k))):
  match p k:
    case S.XH{} 0n:
      WM.floor_one(1n)
    case S.XH{} 1n++j:
      floor_two(j)
    case S.XO{+q} 0n:
      WM.floor_one(S.Pos.nat(S.XO{q}))
    case S.XO{+q} 1n++j:
      WM.floor_eq(Nat.double(S.Pos.nat(q)), Nat.add(0n, Nat.mul(S.Pos.nat(q), 1n+1n)), RW.pw(1n+j), Nat.mul(1n+1n, RW.pw(j)), S.Z.pnat(NU.pshr(q, j)),
        NR.ring_eq([S.Pos.nat(q)], NR.NAdd{NR.NCst{0n}, NR.NMul{NR.NVar{0n}, NR.NCst{2n}}}, NR.NDbl{NR.NVar{0n}}, {==}), {==}, WM.floor_mul(S.Pos.nat(q), RW.pw(j), S.Z.pnat(NU.pshr(q, j)), 0n, 1n, pshr_floor(q, j), (1n, {==})))
    case S.XI{+q} 0n:
      WM.floor_one(S.Pos.nat(S.XI{q}))
    case S.XI{+q} 1n++j:
      WM.floor_eq(1n+Nat.double(S.Pos.nat(q)), Nat.add(1n, Nat.mul(S.Pos.nat(q), 1n+1n)), RW.pw(1n+j), Nat.mul(1n+1n, RW.pw(j)), S.Z.pnat(NU.pshr(q, j)),
        NR.ring_eq([S.Pos.nat(q)], NR.NAdd{NR.NCst{1n}, NR.NMul{NR.NVar{0n}, NR.NCst{2n}}}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{0n}}}, {==}), {==}, WM.floor_mul(S.Pos.nat(q), RW.pw(j), S.Z.pnat(NU.pshr(q, j)), 1n, 1n, pshr_floor(q, j), (0n, {==})))

# pshr never gives a negative
def pshr_nn(p: S.Pos, k: Nat) -> {S.Z.nnat(NU.pshr(p, k)) == 0n : Nat}:
  match p k:
    case S.XH{} 0n:
      {==}
    case S.XH{} 1n+j:
      {==}
    case S.XO{q} 0n:
      {==}
    case S.XO{q} 1n+j:
      pshr_nn(q, j)
    case S.XI{q} 0n:
      {==}
    case S.XI{q} 1n+j:
      pshr_nn(q, j)

def pshr_diff(+p: S.Pos, +k: Nat) -> {S.Z.of_diff(S.Z.pnat(NU.pshr(p, k)), 0n) == NU.pshr(p, k) : S.Z}:
  %pshr_nn(p, k) : {S.Z.of_diff(S.Z.pnat(NU.pshr(p, k)), _) == NU.pshr(p, k) : S.Z}
  LZ.diff_parts(NU.pshr(p, k))


def pr_hx(+p: S.Pos, +k: Nat) -> {S.Pos.nat(S.Pos.add(p, S.Pos.pow2(Nat.sub(k, 1n)))) == Nat.add(S.Pos.nat(p), RW.pw(Nat.sub(k, 1n))) : Nat}:
  %WI.pow2_nat(Nat.sub(k, 1n)) : {S.Pos.nat(S.Pos.add(p, S.Pos.pow2(Nat.sub(k, 1n)))) == Nat.add(S.Pos.nat(p), _) : Nat}
  Equal.sym(Nat, Nat.add(S.Pos.nat(p), S.Pos.nat(S.Pos.pow2(Nat.sub(k, 1n)))), S.Pos.nat(S.Pos.add(p, S.Pos.pow2(Nat.sub(k, 1n)))), P.add_nat(p, S.Pos.pow2(Nat.sub(k, 1n))))

# pshr_round(p, k) = floor((p + 2^(k-1)) / 2^k)
def pround_floor(+p: S.Pos, +k: Nat) -> WM.Floor(Nat.add(S.Pos.nat(p), RW.pw(Nat.sub(k, 1n))), RW.pw(k), S.Z.pnat(NU.pshr_round(p, k))):
  WM.floor_eq(Nat.add(S.Pos.nat(p), RW.pw(Nat.sub(k, 1n))), S.Pos.nat(S.Pos.add(p, S.Pos.pow2(Nat.sub(k, 1n)))), RW.pw(k), RW.pw(k), S.Z.pnat(NU.pshr_round(p, k)), pr_hx(p, k), {==}, pshr_floor(S.Pos.add(p, S.Pos.pow2(Nat.sub(k, 1n))), k))

# The word rounding is numer's
# ----------------------------


def mround_pos(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +p: S.Pos, +k: Nat) -> {SB.Mag.val(bp, RW.Mag.round(bp, lp, RW.Mag.ofpos(lp, p), k)) == S.Z.pnat(NU.pshr_round(p, k)) : Nat}:
  WM.floor_uniq(Nat.add(S.Pos.nat(p), RW.pw(Nat.sub(k, 1n))), RW.pw(k), SB.Mag.val(bp, RW.Mag.round(bp, lp, RW.Mag.ofpos(lp, p), k)), S.Z.pnat(NU.pshr_round(p, k)),
    WM.floor_eq(Nat.add(S.Pos.nat(p), RW.pw(Nat.sub(k, 1n))), Nat.add(SB.Mag.val(bp, RW.Mag.ofpos(lp, p)), RW.pw(Nat.sub(k, 1n))), RW.pw(k), RW.pw(k), SB.Mag.val(bp, RW.Mag.round(bp, lp, RW.Mag.ofpos(lp, p), k)),
      (%WM.ofpos_nat(bp, lp, hb, p) : {Nat.add(_, RW.pw(Nat.sub(k, 1n))) == Nat.add(S.Pos.nat(p), RW.pw(Nat.sub(k, 1n))) : Nat}
        {==}), {==},
      WM.round_val(bp, lp, hb, RW.Mag.ofpos(lp, p), k, WM.ofpos_wf(bp, lp, hb, p))),
    pround_floor(p, k))

def floor_half(+j: Nat) -> WM.Floor(RW.pw(j), RW.pw(1n+j), 0n):
  ((RW.pw(j), {==}), (%N.add_zero(RW.pw(1n+j)) : SB.Le(1n+RW.pw(j), _)
    WM.pw_lt.c(RW.pw(j), WM.pw_pos(j))))

def pw_sub0(+j: Nat) -> {RW.pw(Nat.sub(j, 0n)) == RW.pw(j) : Nat}:
  %Equal.sym(Nat, Nat.sub(j, 0n), j, LZ.sub_zero(j)) : {RW.pw(_) == RW.pw(j) : Nat}
  {==}

# zero rounds to zero (k >= 1)
def mround_nil(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, k: Nat, hk: SB.Le(1n, k)) -> {SB.Mag.val(bp, RW.Mag.round(bp, lp, Nil{}, k)) == 0n : Nat}:
  match k:
    case 0n:
      WM.absurd({SB.Mag.val(bp, RW.Mag.round(bp, lp, Nil{}, 0n)) == 0n : Nat}, WM.lt_irrefl(0n, hk))
    case 1n++j:
      WM.floor_uniq(RW.pw(j), RW.pw(1n+j), SB.Mag.val(bp, RW.Mag.round(bp, lp, Nil{}, 1n+j)), 0n,
        WM.floor_eq(RW.pw(j), RW.pw(Nat.sub(j, 0n)), RW.pw(1n+j), RW.pw(1n+j), SB.Mag.val(bp, RW.Mag.round(bp, lp, Nil{}, 1n+j)), pw_sub0(j), {==},
          WM.round_val(bp, lp, hb, Nil{}, 1n+j, Unit{})), floor_half(j))


def zr_zero(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +k: Nat, hk: SB.Le(1n, k)) -> {SB.Big.val(bp, RI.Big.round(bp, lp, SB.BPos{Nil{}}, k)) == S.Z0{} : S.Z}:
  %Equal.sym(Nat, SB.Mag.val(bp, RW.Mag.round(bp, lp, Nil{}, k)), 0n, mround_nil(bp, lp, hb, k, hk)) : {S.Z.of_diff(_, 0n) == S.Z0{} : S.Z}
  {==}

def zr_pos(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +p: S.Pos, +k: Nat) -> {SB.Big.val(bp, RI.Big.round(bp, lp, SB.BPos{RW.Mag.ofpos(lp, p)}, k)) == NU.pshr_round(p, k) : S.Z}:
  %Equal.sym(Nat, SB.Mag.val(bp, RW.Mag.round(bp, lp, RW.Mag.ofpos(lp, p), k)), S.Z.pnat(NU.pshr_round(p, k)), mround_pos(bp, lp, hb, p, k)) : {S.Z.of_diff(_, 0n) == NU.pshr_round(p, k) : S.Z}
  pshr_diff(S.Pos.add(p, S.Pos.pow2(Nat.sub(k, 1n))), k)

def zr_neg(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +p: S.Pos, +k: Nat) -> {SB.Big.val(bp, RI.Big.round(bp, lp, SB.BNeg{RW.Mag.ofpos(lp, p)}, k)) == S.Z.neg(NU.pshr_round(p, k)) : S.Z}:
  %Equal.sym(Nat, SB.Mag.val(bp, RW.Mag.round(bp, lp, RW.Mag.ofpos(lp, p), k)), S.Z.pnat(NU.pshr_round(p, k)), mround_pos(bp, lp, hb, p, k)) : {S.Z.of_diff(0n, _) == S.Z.neg(NU.pshr_round(p, k)) : S.Z}
  %pshr_diff(S.Pos.add(p, S.Pos.pow2(Nat.sub(k, 1n))), k) : {S.Z.of_diff(0n, S.Z.pnat(NU.pshr_round(p, k))) == S.Z.neg(_) : S.Z}
  LZ.neg_diff(S.Z.pnat(NU.pshr_round(p, k)), 0n)

def round_wf(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, x: SB.Big, +k: Nat, wx: SB.Big.wf(bp, x)) -> SB.Big.wf(bp, RI.Big.round(bp, lp, x, k)):
  match x:
    case SB.BPos{+m}:
      WM.round_wf(bp, lp, hb, m, k, wx)
    case SB.BNeg{+m}:
      WM.round_wf(bp, lp, hb, m, k, wx)

# the canonical word rounding of m by 2^k is numer's zshr_round (k >= 1)
def zround_ok(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, m: S.Z, +k: Nat, hk: SB.Le(1n, k)) -> {RD.WD.zround(bp, lp, RI.Big.ofz(lp, m), k) == RI.Big.ofz(lp, NU.zshr_round(m, k)) : SB.Big}:
  match m:
    case S.Z0{}:
      WDP.canon_is(bp, lp, hb, RI.Big.round(bp, lp, SB.BPos{Nil{}}, k), S.Z0{}, round_wf(bp, lp, hb, SB.BPos{Nil{}}, k, Unit{}), zr_zero(bp, lp, hb, k, hk))
    case S.Zpos{+p}:
      WDP.canon_is(bp, lp, hb, RI.Big.round(bp, lp, SB.BPos{RW.Mag.ofpos(lp, p)}, k), NU.pshr_round(p, k), round_wf(bp, lp, hb, SB.BPos{RW.Mag.ofpos(lp, p)}, k, WM.ofpos_wf(bp, lp, hb, p)), zr_pos(bp, lp, hb, p, k))
    case S.Zneg{+p}:
      WDP.canon_is(bp, lp, hb, RI.Big.round(bp, lp, SB.BNeg{RW.Mag.ofpos(lp, p)}, k), S.Z.neg(NU.pshr_round(p, k)), round_wf(bp, lp, hb, SB.BNeg{RW.Mag.ofpos(lp, p)}, k, WM.ofpos_wf(bp, lp, hb, p)), zr_neg(bp, lp, hb, p, k))

# Sizes
# -----

def sizem_bits(+lp: Nat, m: List<&2, Nat>, tm: WM.TopC(m)) -> {RI.Big.size.m(lp, m) == RW.Mag.bits(lp, m) : Nat}:
  match m:
    case Nil{}:
      WM.absurd({1n == 0n : Nat}, tm)
    case Con{h, t}:
      {==}

def size_pos(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +p: S.Pos) -> {RI.Big.size.m(lp, RW.Mag.ofpos(lp, p)) == QRD.size(p) : Nat}:
  Equal.trans(Nat, RI.Big.size.m(lp, RW.Mag.ofpos(lp, p)), RW.Mag.bits(lp, RW.Mag.ofpos(lp, p)), QRD.size(p), sizem_bits(lp, RW.Mag.ofpos(lp, p), WM.ofpos_topc(bp, lp, hb, p)), WM.ofpos_bits(bp, lp, hb, p))

# the word size is QRD.size(zpos(m))
def size_ok(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, m: S.Z) -> {RI.Big.size(lp, RI.Big.ofz(lp, m)) == QRD.size(NU.zpos(m)) : Nat}:
  match m:
    case S.Z0{}:
      {==}
    case S.Zpos{+p}:
      size_pos(bp, lp, hb, p)
    case S.Zneg{+p}:
      size_pos(bp, lp, hb, p)

# The rounding twins
# ------------------

def znorm_con(m: List<&2, Nat>, +x: RD.WD, tm: WM.TopC(m)) -> {RD.WD.znorm.m(m, x) == x : RD.WD}:
  match m:
    case Nil{}:
      WM.absurd({RD.WD{SB.BPos{Nil{}}, 0n} == x : RD.WD}, tm)
    case Con{h, t}:
      {==}

def znorm_m(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, m: S.Z, +e: Nat) -> {RD.WD.znorm(RD.WD.ofd(lp, S.D{m, e})) == RD.WD.ofd(lp, NU.dznorm(S.D{m, e})) : RD.WD}:
  match m:
    case S.Z0{}:
      {==}
    case S.Zpos{+p}:
      znorm_con(RW.Mag.ofpos(lp, p), RD.WD{SB.BPos{RW.Mag.ofpos(lp, p)}, e}, WM.ofpos_topc(bp, lp, hb, p))
    case S.Zneg{+p}:
      znorm_con(RW.Mag.ofpos(lp, p), RD.WD{SB.BNeg{RW.Mag.ofpos(lp, p)}, e}, WM.ofpos_topc(bp, lp, hb, p))

# WD.znorm is numer's dznorm
def znorm_ok(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, x: S.D) -> {RD.WD.znorm(RD.WD.ofd(lp, x)) == RD.WD.ofd(lp, NU.dznorm(x)) : RD.WD}:
  match x:
    case S.D{m, +e}:
      znorm_m(bp, lp, hb, m, e)


def shz_val(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +z: S.Z, +d: Nat) -> {SB.Big.val(bp, RI.Big.shl(bp, lp, RI.Big.ofz(lp, z), d)) == S.Z.mul(z, S.Zpos{S.Pos.pow2(d)}) : S.Z}:
  %WI.ofz_val(bp, lp, hb, z) : {SB.Big.val(bp, RI.Big.shl(bp, lp, RI.Big.ofz(lp, z), d)) == S.Z.mul(_, S.Zpos{S.Pos.pow2(d)}) : S.Z}
  WI.shl_zval(bp, lp, hb, RI.Big.ofz(lp, z), d)

def sh_ok(c: Bool, +bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m: S.Z, +e: Nat, +k: Nat, hc: {KA.natle(k, e) == c : Bool}, hk: SB.Le(1n, k)) -> {RD.WD.sig.sh(c, bp, lp, RI.Big.ofz(lp, m), e, k) == RD.WD.ofd(lp, NU.dsig.sh(c, m, e, k)) : RD.WD}:
  match c:
    case True{}:
      WDP.wd_eq(RD.WD.zround(bp, lp, RI.Big.ofz(lp, m), k), RI.Big.ofz(lp, NU.zshr_round(m, k)), Nat.sub(e, k), zround_ok(bp, lp, hb, m, k, hk))
    case False{}:
      %Equal.sym(SB.Big, RD.WD.zround(bp, lp, RI.Big.ofz(lp, m), k), RI.Big.ofz(lp, NU.zshr_round(m, k)), zround_ok(bp, lp, hb, m, k, hk)) : {RD.WD{RI.Big.canon(RI.Big.shl(bp, lp, _, Nat.sub(k, e))), 0n} == RD.WD.ofd(lp, NU.dsig.sh(False{}, m, e, k)) : RD.WD}
      WDP.wd_eq(RI.Big.canon(RI.Big.shl(bp, lp, RI.Big.ofz(lp, NU.zshr_round(m, k)), Nat.sub(k, e))), RI.Big.ofz(lp, S.Z.mul(NU.zshr_round(m, k), S.Zpos{S.Pos.pow2(Nat.sub(k, e))})), 0n,
        WDP.canon_is(bp, lp, hb, RI.Big.shl(bp, lp, RI.Big.ofz(lp, NU.zshr_round(m, k)), Nat.sub(k, e)), S.Z.mul(NU.zshr_round(m, k), S.Zpos{S.Pos.pow2(Nat.sub(k, e))}), WI.shl_wf(bp, lp, hb, RI.Big.ofz(lp, NU.zshr_round(m, k)), Nat.sub(k, e), WDP.ofz_wf(bp, lp, hb, NU.zshr_round(m, k))), shz_val(bp, lp, hb, NU.zshr_round(m, k), Nat.sub(k, e))))


def sig_go(c: Bool, +bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m: S.Z, +e: Nat, +b: Nat, hc: {KA.natle(QRD.size(NU.zpos(m)), b) == c : Bool}) -> {RD.WD.sig.go(c, bp, lp, RD.WD.ofd(lp, S.D{m, e}), Nat.sub(QRD.size(NU.zpos(m)), b)) == RD.WD.ofd(lp, NU.dsig.go(c, S.D{m, e}, Nat.sub(QRD.size(NU.zpos(m)), b))) : RD.WD}:
  match c:
    case True{}:
      znorm_ok(bp, lp, hb, S.D{m, e})
    case False{}:
      %Equal.sym(Bool, RD.le(Nat.sub(QRD.size(NU.zpos(m)), b), e), KA.natle(Nat.sub(QRD.size(NU.zpos(m)), b), e), le_natle(Nat.sub(QRD.size(NU.zpos(m)), b), e)) : {RD.WD.sig.sh(_, bp, lp, RI.Big.ofz(lp, m), e, Nat.sub(QRD.size(NU.zpos(m)), b)) == RD.WD.ofd(lp, NU.dsig.sh(KA.natle(Nat.sub(QRD.size(NU.zpos(m)), b), e), m, e, Nat.sub(QRD.size(NU.zpos(m)), b))) : RD.WD}
      sh_ok(KA.natle(Nat.sub(QRD.size(NU.zpos(m)), b), e), bp, lp, hb, m, e, Nat.sub(QRD.size(NU.zpos(m)), b), {==}, sub_pos(QRD.size(NU.zpos(m)), b, natle_false(QRD.size(NU.zpos(m)), b, hc)))

# WD.sig is numer's dsig
def sig_ok(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, x: S.D, +b: Nat) -> {RD.WD.sig(bp, lp, RD.WD.ofd(lp, x), b) == RD.WD.ofd(lp, NU.dsig(x, b)) : RD.WD}:
  match x:
    case S.D{+m, +e}:
      %Equal.sym(Nat, RI.Big.size(lp, RI.Big.ofz(lp, m)), QRD.size(NU.zpos(m)), size_ok(bp, lp, hb, m)) : {RD.WD.sig.go(RD.le(_, b), bp, lp, RD.WD.ofd(lp, S.D{m, e}), Nat.sub(_, b)) == RD.WD.ofd(lp, NU.dsig(S.D{m, e}, b)) : RD.WD}
      %Equal.sym(Bool, RD.le(QRD.size(NU.zpos(m)), b), KA.natle(QRD.size(NU.zpos(m)), b), le_natle(QRD.size(NU.zpos(m)), b)) : {RD.WD.sig.go(_, bp, lp, RD.WD.ofd(lp, S.D{m, e}), Nat.sub(QRD.size(NU.zpos(m)), b)) == RD.WD.ofd(lp, NU.dsig(S.D{m, e}, b)) : RD.WD}
      sig_go(KA.natle(QRD.size(NU.zpos(m)), b), bp, lp, hb, m, e, b, {==})

def round_go(c: Bool, +bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, +m: S.Z, +e: Nat, +p: Nat, hc: {KA.natle(e, p) == c : Bool}) -> {RD.WD.round.go(c, bp, lp, RD.WD.ofd(lp, S.D{m, e}), p) == RD.WD.ofd(lp, NU.dround.go(c, S.D{m, e}, p)) : RD.WD}:
  match c:
    case True{}:
      {==}
    case False{}:
      WDP.wd_eq(RD.WD.zround(bp, lp, RI.Big.ofz(lp, m), Nat.sub(e, p)), RI.Big.ofz(lp, NU.zshr_round(m, Nat.sub(e, p))), p,
        zround_ok(bp, lp, hb, m, Nat.sub(e, p), sub_pos(e, p, natle_false(e, p, hc))))

# WD.round is numer's dround
def round_ok(+bp: Nat, +lp: Nat, +hb: {RW.pw(1n+lp) == 1n+bp : Nat}, x: S.D, +p: Nat) -> {RD.WD.round(bp, lp, RD.WD.ofd(lp, x), p) == RD.WD.ofd(lp, NU.dround(x, p)) : RD.WD}:
  match x:
    case S.D{+m, +e}:
      %Equal.sym(Bool, RD.le(e, p), KA.natle(e, p), le_natle(e, p)) : {RD.WD.round.go(_, bp, lp, RD.WD.ofd(lp, S.D{m, e}), p) == RD.WD.ofd(lp, NU.dround(S.D{m, e}, p)) : RD.WD}
      round_go(KA.natle(e, p), bp, lp, hb, m, e, p, {==})
