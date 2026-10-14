# Proofs about the binary integers of spec/num.bend, through their unary
# meaning: of_diff(a, b) is the integer a - b. Every integer is of_diff of
# its parts (diff_parts), and of_diff turns sums and products of pairs into
# Z.add and Z.mul (add_hom, mul_hom). lib/zpair.bend builds a tactic on top.

import Base
import ./nat.bend as N
import ./natring.bend as NR
import ./pos.bend as P
import ../spec/num.bend as S

# Every integer is the difference of its parts
# --------------------------------------------

def zpos_diff(+p: S.Pos) -> {S.Z.of_diff(S.Pos.nat(p), 0n) == S.Zpos{p} : S.Z}:
  %P.form_nat(p) : {S.Z.of_diff(_, 0n) == S.Zpos{p} : S.Z}
  %P.retract(p) : {S.Z.of_diff(1n+P.pm1(p), 0n) == S.Zpos{_} : S.Z}
  {==}

def zneg_diff(+p: S.Pos) -> {S.Z.of_diff(0n, S.Pos.nat(p)) == S.Zneg{p} : S.Z}:
  %P.form_nat(p) : {S.Z.of_diff(0n, _) == S.Zneg{p} : S.Z}
  %P.retract(p) : {S.Z.of_diff(0n, 1n+P.pm1(p)) == S.Zneg{_} : S.Z}
  {==}

def diff_parts(x: S.Z) -> {S.Z.of_diff(S.Z.pnat(x), S.Z.nnat(x)) == x : S.Z}:
  match x:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      zpos_diff(p)
    case S.Zneg{p}:
      zneg_diff(p)

# Doubling
# --------

def double_diff(a: Nat, b: Nat) -> {S.Z.of_diff(Nat.double(a), Nat.double(b)) == S.Z.double(S.Z.of_diff(a, b)) : S.Z}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+i 0n:
      %P.os_odd(i) : {S.Zpos{_} == S.Zpos{S.XO{S.Pos.of_succ(i)}} : S.Z}
      {==}
    case 0n 1n+j:
      %P.os_odd(j) : {S.Zneg{_} == S.Zneg{S.XO{S.Pos.of_succ(j)}} : S.Z}
      {==}
    case 1n+i 1n+j:
      double_diff(i, j)

def sd_diff(a: Nat, b: Nat) -> {S.Z.of_diff(1n+Nat.double(a), Nat.double(b)) == S.Z.succ_double(S.Z.of_diff(a, b)) : S.Z}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+i 0n:
      %P.os_even(i) : {S.Zpos{_} == S.Zpos{S.XI{S.Pos.of_succ(i)}} : S.Z}
      {==}
    case 0n 1n+j:
      %P.pd_os(j) : {S.Zneg{_} == S.Zneg{S.Pos.pred_double(S.Pos.of_succ(j))} : S.Z}
      {==}
    case 1n+i 1n+j:
      sd_diff(i, j)

def pd_diff(a: Nat, b: Nat) -> {S.Z.of_diff(Nat.double(a), 1n+Nat.double(b)) == S.Z.pred_double(S.Z.of_diff(a, b)) : S.Z}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+i 0n:
      %P.pd_os(i) : {S.Zpos{_} == S.Zpos{S.Pos.pred_double(S.Pos.of_succ(i))} : S.Z}
      {==}
    case 0n 1n+j:
      %P.os_even(j) : {S.Zneg{_} == S.Zneg{S.XI{S.Pos.of_succ(j)}} : S.Z}
      {==}
    case 1n+i 1n+j:
      pd_diff(i, j)

# pos_sub is subtraction
# ----------------------

def pos_sub_diff(a: S.Pos, b: S.Pos) -> {S.Z.of_diff(S.Pos.nat(a), S.Pos.nat(b)) == S.Z.pos_sub(a, b) : S.Z}:
  match a b:
    case S.XI{+p} S.XI{+q}:
      %pos_sub_diff(p, q) : {S.Z.of_diff(Nat.double(S.Pos.nat(p)), Nat.double(S.Pos.nat(q))) == S.Z.double(_) : S.Z}
      double_diff(S.Pos.nat(p), S.Pos.nat(q))
    case S.XI{+p} S.XO{+q}:
      %pos_sub_diff(p, q) : {S.Z.of_diff(1n+Nat.double(S.Pos.nat(p)), Nat.double(S.Pos.nat(q))) == S.Z.succ_double(_) : S.Z}
      sd_diff(S.Pos.nat(p), S.Pos.nat(q))
    case S.XI{+p} S.XH{}:
      %zpos_diff(p) : {S.Z.of_diff(Nat.double(S.Pos.nat(p)), 0n) == S.Z.double(_) : S.Z}
      double_diff(S.Pos.nat(p), 0n)
    case S.XO{+p} S.XI{+q}:
      %pos_sub_diff(p, q) : {S.Z.of_diff(Nat.double(S.Pos.nat(p)), 1n+Nat.double(S.Pos.nat(q))) == S.Z.pred_double(_) : S.Z}
      pd_diff(S.Pos.nat(p), S.Pos.nat(q))
    case S.XO{+p} S.XO{+q}:
      %pos_sub_diff(p, q) : {S.Z.of_diff(Nat.double(S.Pos.nat(p)), Nat.double(S.Pos.nat(q))) == S.Z.double(_) : S.Z}
      double_diff(S.Pos.nat(p), S.Pos.nat(q))
    case S.XO{+p} S.XH{}:
      %zpos_diff(p) : {S.Z.of_diff(Nat.double(S.Pos.nat(p)), 1n) == S.Z.pred_double(_) : S.Z}
      pd_diff(S.Pos.nat(p), 0n)
    case S.XH{} S.XI{+q}:
      %zneg_diff(q) : {S.Z.of_diff(0n, Nat.double(S.Pos.nat(q))) == S.Z.double(_) : S.Z}
      double_diff(0n, S.Pos.nat(q))
    case S.XH{} S.XO{+q}:
      %zneg_diff(q) : {S.Z.of_diff(1n, Nat.double(S.Pos.nat(q))) == S.Z.succ_double(_) : S.Z}
      sd_diff(0n, S.Pos.nat(q))
    case S.XH{} S.XH{}:
      {==}

# Z.add and Z.mul on the parts
# ----------------------------

def add_diff(x: S.Z, y: S.Z) -> {S.Z.of_diff(Nat.add(S.Z.pnat(x), S.Z.pnat(y)), Nat.add(S.Z.nnat(x), S.Z.nnat(y))) == S.Z.add(x, y) : S.Z}:
  match x:
    case S.Z0{}:
      diff_parts(y)
    case S.Zpos{+p}:
      match y:
        case S.Z0{}:
          %N.add_zero(S.Pos.nat(p)) : {S.Z.of_diff(_, 0n) == S.Zpos{p} : S.Z}
          zpos_diff(p)
        case S.Zpos{+q}:
          %zpos_diff(S.Pos.add(p, q)) : {S.Z.of_diff(Nat.add(S.Pos.nat(p), S.Pos.nat(q)), 0n) == _ : S.Z}
          %P.add_nat(p, q) : {S.Z.of_diff(Nat.add(S.Pos.nat(p), S.Pos.nat(q)), 0n) == S.Z.of_diff(_, 0n) : S.Z}
          {==}
        case S.Zneg{+q}:
          %N.add_zero(S.Pos.nat(p)) : {S.Z.of_diff(_, S.Pos.nat(q)) == S.Z.pos_sub(p, q) : S.Z}
          pos_sub_diff(p, q)
    case S.Zneg{+p}:
      match y:
        case S.Z0{}:
          %N.add_zero(S.Pos.nat(p)) : {S.Z.of_diff(0n, _) == S.Zneg{p} : S.Z}
          zneg_diff(p)
        case S.Zpos{+q}:
          %N.add_zero(S.Pos.nat(p)) : {S.Z.of_diff(S.Pos.nat(q), _) == S.Z.pos_sub(q, p) : S.Z}
          pos_sub_diff(q, p)
        case S.Zneg{+q}:
          %zneg_diff(S.Pos.add(p, q)) : {S.Z.of_diff(0n, Nat.add(S.Pos.nat(p), S.Pos.nat(q))) == _ : S.Z}
          %P.add_nat(p, q) : {S.Z.of_diff(0n, Nat.add(S.Pos.nat(p), S.Pos.nat(q))) == S.Z.of_diff(0n, _) : S.Z}
          {==}

def mul_diff(x: S.Z, y: S.Z) -> {S.Z.of_diff(Nat.add(Nat.mul(S.Z.pnat(x), S.Z.pnat(y)), Nat.mul(S.Z.nnat(x), S.Z.nnat(y))), Nat.add(Nat.mul(S.Z.pnat(x), S.Z.nnat(y)), Nat.mul(S.Z.nnat(x), S.Z.pnat(y)))) == S.Z.mul(x, y) : S.Z}:
  match x:
    case S.Z0{}:
      {==}
    case S.Zpos{+p}:
      match y:
        case S.Z0{}:
          %N.mul_zero(S.Pos.nat(p)) : {S.Z.of_diff(Nat.add(_, 0n), Nat.add(_, 0n)) == S.Z0{} : S.Z}
          {==}
        case S.Zpos{+q}:
          %N.mul_zero(S.Pos.nat(p)) : {S.Z.of_diff(Nat.add(Nat.mul(S.Pos.nat(p), S.Pos.nat(q)), 0n), Nat.add(_, 0n)) == S.Zpos{S.Pos.mul(p, q)} : S.Z}
          %N.add_zero(Nat.mul(S.Pos.nat(p), S.Pos.nat(q))) : {S.Z.of_diff(_, 0n) == S.Zpos{S.Pos.mul(p, q)} : S.Z}
          %zpos_diff(S.Pos.mul(p, q)) : {S.Z.of_diff(Nat.mul(S.Pos.nat(p), S.Pos.nat(q)), 0n) == _ : S.Z}
          %P.mul_nat(p, q) : {S.Z.of_diff(Nat.mul(S.Pos.nat(p), S.Pos.nat(q)), 0n) == S.Z.of_diff(_, 0n) : S.Z}
          {==}
        case S.Zneg{+q}:
          %N.mul_zero(S.Pos.nat(p)) : {S.Z.of_diff(Nat.add(_, 0n), Nat.add(Nat.mul(S.Pos.nat(p), S.Pos.nat(q)), 0n)) == S.Zneg{S.Pos.mul(p, q)} : S.Z}
          %N.add_zero(Nat.mul(S.Pos.nat(p), S.Pos.nat(q))) : {S.Z.of_diff(0n, _) == S.Zneg{S.Pos.mul(p, q)} : S.Z}
          %zneg_diff(S.Pos.mul(p, q)) : {S.Z.of_diff(0n, Nat.mul(S.Pos.nat(p), S.Pos.nat(q))) == _ : S.Z}
          %P.mul_nat(p, q) : {S.Z.of_diff(0n, Nat.mul(S.Pos.nat(p), S.Pos.nat(q))) == S.Z.of_diff(0n, _) : S.Z}
          {==}
    case S.Zneg{+p}:
      match y:
        case S.Z0{}:
          %N.mul_zero(S.Pos.nat(p)) : {S.Z.of_diff(_, _) == S.Z0{} : S.Z}
          {==}
        case S.Zpos{+q}:
          %N.mul_zero(S.Pos.nat(p)) : {S.Z.of_diff(_, Nat.mul(S.Pos.nat(p), S.Pos.nat(q))) == S.Zneg{S.Pos.mul(p, q)} : S.Z}
          %zneg_diff(S.Pos.mul(p, q)) : {S.Z.of_diff(0n, Nat.mul(S.Pos.nat(p), S.Pos.nat(q))) == _ : S.Z}
          %P.mul_nat(p, q) : {S.Z.of_diff(0n, Nat.mul(S.Pos.nat(p), S.Pos.nat(q))) == S.Z.of_diff(0n, _) : S.Z}
          {==}
        case S.Zneg{+q}:
          %N.mul_zero(S.Pos.nat(p)) : {S.Z.of_diff(Nat.mul(S.Pos.nat(p), S.Pos.nat(q)), _) == S.Zpos{S.Pos.mul(p, q)} : S.Z}
          %zpos_diff(S.Pos.mul(p, q)) : {S.Z.of_diff(Nat.mul(S.Pos.nat(p), S.Pos.nat(q)), 0n) == _ : S.Z}
          %P.mul_nat(p, q) : {S.Z.of_diff(Nat.mul(S.Pos.nat(p), S.Pos.nat(q)), 0n) == S.Z.of_diff(_, 0n) : S.Z}
          {==}

# The parts of a difference
# -------------------------

def sub_pnat(a: Nat, b: Nat) -> {Nat.sub(a, b) == S.Z.pnat(S.Z.of_diff(a, b)) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+i 0n:
      P.nat_os(i)
    case 0n 1n+j:
      {==}
    case 1n+i 1n+j:
      sub_pnat(i, j)

def sub_nnat(a: Nat, b: Nat) -> {Nat.sub(b, a) == S.Z.nnat(S.Z.of_diff(a, b)) : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+i 0n:
      {==}
    case 0n 1n+j:
      P.nat_os(j)
    case 1n+i 1n+j:
      sub_nnat(i, j)

# of_diff only sees a - b
# -----------------------

def shift(k: Nat, -x: Nat, -y: Nat) -> {S.Z.of_diff(x, y) == S.Z.of_diff(Nat.add(k, x), Nat.add(k, y)) : S.Z}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      shift(j, x, y)

def absorb(a: Nat, b: Nat, -x: Nat, -y: Nat) -> {S.Z.of_diff(Nat.add(a, x), Nat.add(b, y)) == S.Z.of_diff(Nat.add(Nat.sub(a, b), x), Nat.add(Nat.sub(b, a), y)) : S.Z}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+i 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+i 1n+j:
      absorb(i, j, x, y)

def mabsorb(a: Nat, b: Nat, +u: Nat, +v: Nat) -> {S.Z.of_diff(Nat.add(Nat.mul(a, u), Nat.mul(b, v)), Nat.add(Nat.mul(a, v), Nat.mul(b, u))) == S.Z.of_diff(Nat.add(Nat.mul(Nat.sub(a, b), u), Nat.mul(Nat.sub(b, a), v)), Nat.add(Nat.mul(Nat.sub(a, b), v), Nat.mul(Nat.sub(b, a), u))) : S.Z}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+i 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n++i 1n++j:
      # (u + iu) + (v + jv) is (u + v) + (iu + jv), and likewise below
      %NR.ring_eq([u, v, i, j],
        NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}, NR.NAdd{NR.NMul{NR.NVar{2n}, NR.NVar{0n}}, NR.NMul{NR.NVar{3n}, NR.NVar{1n}}}},
        NR.NAdd{NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NVar{2n}}, NR.NVar{0n}}, NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NVar{3n}}, NR.NVar{1n}}},
        {==}) : {S.Z.of_diff(_, Nat.add(Nat.mul(1n+i, v), Nat.mul(1n+j, u))) == S.Z.of_diff(Nat.add(Nat.mul(Nat.sub(i, j), u), Nat.mul(Nat.sub(j, i), v)), Nat.add(Nat.mul(Nat.sub(i, j), v), Nat.mul(Nat.sub(j, i), u))) : S.Z}
      %NR.ring_eq([u, v, i, j],
        NR.NAdd{NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}, NR.NAdd{NR.NMul{NR.NVar{2n}, NR.NVar{1n}}, NR.NMul{NR.NVar{3n}, NR.NVar{0n}}}},
        NR.NAdd{NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NVar{2n}}, NR.NVar{1n}}, NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NVar{3n}}, NR.NVar{0n}}},
        {==}) : {S.Z.of_diff(Nat.add(Nat.add(u, v), Nat.add(Nat.mul(i, u), Nat.mul(j, v))), _) == S.Z.of_diff(Nat.add(Nat.mul(Nat.sub(i, j), u), Nat.mul(Nat.sub(j, i), v)), Nat.add(Nat.mul(Nat.sub(i, j), v), Nat.mul(Nat.sub(j, i), u))) : S.Z}
      %shift(Nat.add(u, v), Nat.add(Nat.mul(i, u), Nat.mul(j, v)), Nat.add(Nat.mul(i, v), Nat.mul(j, u))) : {_ == S.Z.of_diff(Nat.add(Nat.mul(Nat.sub(i, j), u), Nat.mul(Nat.sub(j, i), v)), Nat.add(Nat.mul(Nat.sub(i, j), v), Nat.mul(Nat.sub(j, i), u))) : S.Z}
      mabsorb(i, j, u, v)

def neg_diff(a: Nat, b: Nat) -> {S.Z.of_diff(b, a) == S.Z.neg(S.Z.of_diff(a, b)) : S.Z}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+i 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+i 1n+j:
      neg_diff(i, j)

# of_diff is a ring homomorphism
# ------------------------------

def add_hom(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {S.Z.of_diff(Nat.add(a, c), Nat.add(b, d)) == S.Z.add(S.Z.of_diff(a, b), S.Z.of_diff(c, d)) : S.Z}:
  %add_diff(S.Z.of_diff(a, b), S.Z.of_diff(c, d)) : {S.Z.of_diff(Nat.add(a, c), Nat.add(b, d)) == _ : S.Z}
  %sub_pnat(a, b) : {S.Z.of_diff(Nat.add(a, c), Nat.add(b, d)) == S.Z.of_diff(Nat.add(_, S.Z.pnat(S.Z.of_diff(c, d))), Nat.add(S.Z.nnat(S.Z.of_diff(a, b)), S.Z.nnat(S.Z.of_diff(c, d)))) : S.Z}
  %sub_nnat(a, b) : {S.Z.of_diff(Nat.add(a, c), Nat.add(b, d)) == S.Z.of_diff(Nat.add(Nat.sub(a, b), S.Z.pnat(S.Z.of_diff(c, d))), Nat.add(_, S.Z.nnat(S.Z.of_diff(c, d)))) : S.Z}
  %sub_pnat(c, d) : {S.Z.of_diff(Nat.add(a, c), Nat.add(b, d)) == S.Z.of_diff(Nat.add(Nat.sub(a, b), _), Nat.add(Nat.sub(b, a), S.Z.nnat(S.Z.of_diff(c, d)))) : S.Z}
  %sub_nnat(c, d) : {S.Z.of_diff(Nat.add(a, c), Nat.add(b, d)) == S.Z.of_diff(Nat.add(Nat.sub(a, b), Nat.sub(c, d)), Nat.add(Nat.sub(b, a), _)) : S.Z}
  %absorb(a, b, Nat.sub(c, d), Nat.sub(d, c)) : {S.Z.of_diff(Nat.add(a, c), Nat.add(b, d)) == _ : S.Z}
  %N.add_comm(Nat.sub(c, d), a) : {S.Z.of_diff(Nat.add(a, c), Nat.add(b, d)) == S.Z.of_diff(_, Nat.add(b, Nat.sub(d, c))) : S.Z}
  %N.add_comm(Nat.sub(d, c), b) : {S.Z.of_diff(Nat.add(a, c), Nat.add(b, d)) == S.Z.of_diff(Nat.add(Nat.sub(c, d), a), _) : S.Z}
  %absorb(c, d, a, b) : {S.Z.of_diff(Nat.add(a, c), Nat.add(b, d)) == _ : S.Z}
  %N.add_comm(a, c) : {S.Z.of_diff(Nat.add(a, c), Nat.add(b, d)) == S.Z.of_diff(_, Nat.add(d, b)) : S.Z}
  %N.add_comm(b, d) : {S.Z.of_diff(Nat.add(a, c), Nat.add(b, d)) == S.Z.of_diff(Nat.add(a, c), _) : S.Z}
  {==}

def mul_hom(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {S.Z.of_diff(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), Nat.add(Nat.mul(a, d), Nat.mul(b, c))) == S.Z.mul(S.Z.of_diff(a, b), S.Z.of_diff(c, d)) : S.Z}:
  %mul_diff(S.Z.of_diff(a, b), S.Z.of_diff(c, d)) : {S.Z.of_diff(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), Nat.add(Nat.mul(a, d), Nat.mul(b, c))) == _ : S.Z}
  %sub_pnat(a, b) : {S.Z.of_diff(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), Nat.add(Nat.mul(a, d), Nat.mul(b, c))) == S.Z.of_diff(Nat.add(Nat.mul(_, S.Z.pnat(S.Z.of_diff(c, d))), Nat.mul(S.Z.nnat(S.Z.of_diff(a, b)), S.Z.nnat(S.Z.of_diff(c, d)))), Nat.add(Nat.mul(_, S.Z.nnat(S.Z.of_diff(c, d))), Nat.mul(S.Z.nnat(S.Z.of_diff(a, b)), S.Z.pnat(S.Z.of_diff(c, d))))) : S.Z}
  %sub_nnat(a, b) : {S.Z.of_diff(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), Nat.add(Nat.mul(a, d), Nat.mul(b, c))) == S.Z.of_diff(Nat.add(Nat.mul(Nat.sub(a, b), S.Z.pnat(S.Z.of_diff(c, d))), Nat.mul(_, S.Z.nnat(S.Z.of_diff(c, d)))), Nat.add(Nat.mul(Nat.sub(a, b), S.Z.nnat(S.Z.of_diff(c, d))), Nat.mul(_, S.Z.pnat(S.Z.of_diff(c, d))))) : S.Z}
  %sub_pnat(c, d) : {S.Z.of_diff(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), Nat.add(Nat.mul(a, d), Nat.mul(b, c))) == S.Z.of_diff(Nat.add(Nat.mul(Nat.sub(a, b), _), Nat.mul(Nat.sub(b, a), S.Z.nnat(S.Z.of_diff(c, d)))), Nat.add(Nat.mul(Nat.sub(a, b), S.Z.nnat(S.Z.of_diff(c, d))), Nat.mul(Nat.sub(b, a), _))) : S.Z}
  %sub_nnat(c, d) : {S.Z.of_diff(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), Nat.add(Nat.mul(a, d), Nat.mul(b, c))) == S.Z.of_diff(Nat.add(Nat.mul(Nat.sub(a, b), Nat.sub(c, d)), Nat.mul(Nat.sub(b, a), _)), Nat.add(Nat.mul(Nat.sub(a, b), _), Nat.mul(Nat.sub(b, a), Nat.sub(c, d)))) : S.Z}
  %mabsorb(a, b, Nat.sub(c, d), Nat.sub(d, c)) : {S.Z.of_diff(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), Nat.add(Nat.mul(a, d), Nat.mul(b, c))) == _ : S.Z}
  %NR.ring_eq([a, b, Nat.sub(c, d), Nat.sub(d, c)],
    NR.NAdd{NR.NMul{NR.NVar{2n}, NR.NVar{0n}}, NR.NMul{NR.NVar{3n}, NR.NVar{1n}}},
    NR.NAdd{NR.NMul{NR.NVar{0n}, NR.NVar{2n}}, NR.NMul{NR.NVar{1n}, NR.NVar{3n}}},
    {==}) : {S.Z.of_diff(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), Nat.add(Nat.mul(a, d), Nat.mul(b, c))) == S.Z.of_diff(_, Nat.add(Nat.mul(a, Nat.sub(d, c)), Nat.mul(b, Nat.sub(c, d)))) : S.Z}
  %NR.ring_eq([a, b, Nat.sub(c, d), Nat.sub(d, c)],
    NR.NAdd{NR.NMul{NR.NVar{2n}, NR.NVar{1n}}, NR.NMul{NR.NVar{3n}, NR.NVar{0n}}},
    NR.NAdd{NR.NMul{NR.NVar{0n}, NR.NVar{3n}}, NR.NMul{NR.NVar{1n}, NR.NVar{2n}}},
    {==}) : {S.Z.of_diff(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), Nat.add(Nat.mul(a, d), Nat.mul(b, c))) == S.Z.of_diff(Nat.add(Nat.mul(Nat.sub(c, d), a), Nat.mul(Nat.sub(d, c), b)), _) : S.Z}
  %mabsorb(c, d, a, b) : {S.Z.of_diff(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), Nat.add(Nat.mul(a, d), Nat.mul(b, c))) == _ : S.Z}
  %NR.ring_eq([a, b, c, d],
    NR.NAdd{NR.NMul{NR.NVar{0n}, NR.NVar{2n}}, NR.NMul{NR.NVar{1n}, NR.NVar{3n}}},
    NR.NAdd{NR.NMul{NR.NVar{2n}, NR.NVar{0n}}, NR.NMul{NR.NVar{3n}, NR.NVar{1n}}},
    {==}) : {S.Z.of_diff(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), Nat.add(Nat.mul(a, d), Nat.mul(b, c))) == S.Z.of_diff(_, Nat.add(Nat.mul(c, b), Nat.mul(d, a))) : S.Z}
  %NR.ring_eq([a, b, c, d],
    NR.NAdd{NR.NMul{NR.NVar{0n}, NR.NVar{3n}}, NR.NMul{NR.NVar{1n}, NR.NVar{2n}}},
    NR.NAdd{NR.NMul{NR.NVar{2n}, NR.NVar{1n}}, NR.NMul{NR.NVar{3n}, NR.NVar{0n}}},
    {==}) : {S.Z.of_diff(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), Nat.add(Nat.mul(a, d), Nat.mul(b, c))) == S.Z.of_diff(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), _) : S.Z}
  {==}

# Comparison
# ----------

# x vs y is pnat x + nnat y vs pnat y + nnat x
def cmp_nat(x: S.Z, y: S.Z) -> {S.Z.cmp(x, y) == Nat.cmp(Nat.add(S.Z.pnat(x), S.Z.nnat(y)), Nat.add(S.Z.pnat(y), S.Z.nnat(x))) : Cmp}:
  match x:
    case S.Z0{}:
      match y:
        case S.Z0{}:
          {==}
        case S.Zpos{+q}:
          %N.add_zero(S.Pos.nat(q)) : {LT{} == Nat.cmp(0n, _) : Cmp}
          %P.form_nat(q) : {LT{} == Nat.cmp(0n, _) : Cmp}
          {==}
        case S.Zneg{+q}:
          %P.form_nat(q) : {GT{} == Nat.cmp(_, 0n) : Cmp}
          {==}
    case S.Zpos{+p}:
      match y:
        case S.Z0{}:
          %N.add_zero(S.Pos.nat(p)) : {GT{} == Nat.cmp(_, 0n) : Cmp}
          %P.form_nat(p) : {GT{} == Nat.cmp(_, 0n) : Cmp}
          {==}
        case S.Zpos{+q}:
          %N.add_zero(S.Pos.nat(p)) : {S.Pos.cmp(p, q) == Nat.cmp(_, Nat.add(S.Pos.nat(q), 0n)) : Cmp}
          %N.add_zero(S.Pos.nat(q)) : {S.Pos.cmp(p, q) == Nat.cmp(S.Pos.nat(p), _) : Cmp}
          P.cmp_nat(p, q)
        case S.Zneg{+q}:
          %P.form_nat(p) : {GT{} == Nat.cmp(Nat.add(_, S.Pos.nat(q)), 0n) : Cmp}
          {==}
    case S.Zneg{+p}:
      match y:
        case S.Z0{}:
          %P.form_nat(p) : {LT{} == Nat.cmp(0n, _) : Cmp}
          {==}
        case S.Zpos{+q}:
          %P.form_nat(q) : {LT{} == Nat.cmp(0n, Nat.add(_, S.Pos.nat(p))) : Cmp}
          {==}
        case S.Zneg{+q}:
          P.cmp_nat(q, p)
