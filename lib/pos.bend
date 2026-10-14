# Proofs about the binary positives of spec/num.bend: Pos.nat is injective
# and turns succ, addc and mul into their unary counterparts. The case
# arithmetic is discharged by the Nat normalizer (lib/natring.bend).

import Base
import ./nat.bend as N
import ./natring.bend as NR
import ../spec/num.bend as S

def bit(c: Bool) -> Nat:
  match c:
    case False{}:
      0n
    case True{}:
      1n

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+k:
      k

# Homomorphism
# ------------

def succ_nat(p: S.Pos) -> {1n+S.Pos.nat(p) == S.Pos.nat(S.Pos.succ(p)) : Nat}:
  match p:
    case S.XH{}:
      {==}
    case S.XO{q}:
      {==}
    case S.XI{q}:
      %succ_nat(q) : {2n+Nat.double(S.Pos.nat(q)) == Nat.double(_) : Nat}
      {==}

def addc_nat(a: S.Pos, b: S.Pos, c: Bool) -> {Nat.add(bit(c), Nat.add(S.Pos.nat(a), S.Pos.nat(b))) == S.Pos.nat(S.Pos.addc(a, b, c)) : Nat}:
  match a b c:
    case S.XH{} S.XH{} False{}:
      {==}
    case S.XH{} S.XH{} True{}:
      {==}
    case S.XH{} S.XO{+q} False{}:
      NR.ring_eq([S.Pos.nat(q)], NR.NAdd{NR.NCst{0n}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{0n}}}}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{0n}}}, {==})
    case S.XH{} S.XO{+q} True{}:
      %succ_nat(q) : {Nat.add(bit(True{}), Nat.add(1n, S.Pos.nat(S.XO{q}))) == Nat.double(_) : Nat}
      NR.ring_eq([S.Pos.nat(q)], NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{0n}}}}, NR.NDbl{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}, {==})
    case S.XH{} S.XI{+q} False{}:
      %succ_nat(q) : {Nat.add(bit(False{}), Nat.add(1n, S.Pos.nat(S.XI{q}))) == Nat.double(_) : Nat}
      NR.ring_eq([S.Pos.nat(q)], NR.NAdd{NR.NCst{0n}, NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{0n}}}}}, NR.NDbl{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}, {==})
    case S.XH{} S.XI{+q} True{}:
      %succ_nat(q) : {Nat.add(bit(True{}), Nat.add(1n, S.Pos.nat(S.XI{q}))) == 1n+Nat.double(_) : Nat}
      NR.ring_eq([S.Pos.nat(q)], NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{0n}}}}}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}}, {==})
    case S.XO{+p} S.XH{} False{}:
      NR.ring_eq([S.Pos.nat(p)], NR.NAdd{NR.NCst{0n}, NR.NAdd{NR.NDbl{NR.NVar{0n}}, NR.NCst{1n}}}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{0n}}}, {==})
    case S.XO{+p} S.XH{} True{}:
      %succ_nat(p) : {Nat.add(bit(True{}), Nat.add(S.Pos.nat(S.XO{p}), 1n)) == Nat.double(_) : Nat}
      NR.ring_eq([S.Pos.nat(p)], NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NDbl{NR.NVar{0n}}, NR.NCst{1n}}}, NR.NDbl{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}, {==})
    case S.XI{+p} S.XH{} False{}:
      %succ_nat(p) : {Nat.add(bit(False{}), Nat.add(S.Pos.nat(S.XI{p}), 1n)) == Nat.double(_) : Nat}
      NR.ring_eq([S.Pos.nat(p)], NR.NAdd{NR.NCst{0n}, NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{0n}}}, NR.NCst{1n}}}, NR.NDbl{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}, {==})
    case S.XI{+p} S.XH{} True{}:
      %succ_nat(p) : {Nat.add(bit(True{}), Nat.add(S.Pos.nat(S.XI{p}), 1n)) == 1n+Nat.double(_) : Nat}
      NR.ring_eq([S.Pos.nat(p)], NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{0n}}}, NR.NCst{1n}}}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NAdd{NR.NCst{1n}, NR.NVar{0n}}}}, {==})
    case S.XO{+p} S.XO{+q} False{}:
      %addc_nat(p, q, False{}) : {Nat.add(bit(False{}), Nat.add(S.Pos.nat(S.XO{p}), S.Pos.nat(S.XO{q}))) == Nat.double(_) : Nat}
      NR.ring_eq([S.Pos.nat(p), S.Pos.nat(q)], NR.NAdd{NR.NCst{0n}, NR.NAdd{NR.NDbl{NR.NVar{0n}}, NR.NDbl{NR.NVar{1n}}}}, NR.NDbl{NR.NAdd{NR.NCst{0n}, NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}}}, {==})
    case S.XO{+p} S.XO{+q} True{}:
      %addc_nat(p, q, False{}) : {Nat.add(bit(True{}), Nat.add(S.Pos.nat(S.XO{p}), S.Pos.nat(S.XO{q}))) == 1n+Nat.double(_) : Nat}
      NR.ring_eq([S.Pos.nat(p), S.Pos.nat(q)], NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NDbl{NR.NVar{0n}}, NR.NDbl{NR.NVar{1n}}}}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NAdd{NR.NCst{0n}, NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}}}}, {==})
    case S.XO{+p} S.XI{+q} False{}:
      %addc_nat(p, q, False{}) : {Nat.add(bit(False{}), Nat.add(S.Pos.nat(S.XO{p}), S.Pos.nat(S.XI{q}))) == 1n+Nat.double(_) : Nat}
      NR.ring_eq([S.Pos.nat(p), S.Pos.nat(q)], NR.NAdd{NR.NCst{0n}, NR.NAdd{NR.NDbl{NR.NVar{0n}}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{1n}}}}}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NAdd{NR.NCst{0n}, NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}}}}, {==})
    case S.XO{+p} S.XI{+q} True{}:
      %addc_nat(p, q, True{}) : {Nat.add(bit(True{}), Nat.add(S.Pos.nat(S.XO{p}), S.Pos.nat(S.XI{q}))) == Nat.double(_) : Nat}
      NR.ring_eq([S.Pos.nat(p), S.Pos.nat(q)], NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NDbl{NR.NVar{0n}}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{1n}}}}}, NR.NDbl{NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}}}, {==})
    case S.XI{+p} S.XO{+q} False{}:
      %addc_nat(p, q, False{}) : {Nat.add(bit(False{}), Nat.add(S.Pos.nat(S.XI{p}), S.Pos.nat(S.XO{q}))) == 1n+Nat.double(_) : Nat}
      NR.ring_eq([S.Pos.nat(p), S.Pos.nat(q)], NR.NAdd{NR.NCst{0n}, NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{0n}}}, NR.NDbl{NR.NVar{1n}}}}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NAdd{NR.NCst{0n}, NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}}}}, {==})
    case S.XI{+p} S.XO{+q} True{}:
      %addc_nat(p, q, True{}) : {Nat.add(bit(True{}), Nat.add(S.Pos.nat(S.XI{p}), S.Pos.nat(S.XO{q}))) == Nat.double(_) : Nat}
      NR.ring_eq([S.Pos.nat(p), S.Pos.nat(q)], NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{0n}}}, NR.NDbl{NR.NVar{1n}}}}, NR.NDbl{NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}}}, {==})
    case S.XI{+p} S.XI{+q} False{}:
      %addc_nat(p, q, True{}) : {Nat.add(bit(False{}), Nat.add(S.Pos.nat(S.XI{p}), S.Pos.nat(S.XI{q}))) == Nat.double(_) : Nat}
      NR.ring_eq([S.Pos.nat(p), S.Pos.nat(q)], NR.NAdd{NR.NCst{0n}, NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{0n}}}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{1n}}}}}, NR.NDbl{NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}}}, {==})
    case S.XI{+p} S.XI{+q} True{}:
      %addc_nat(p, q, True{}) : {Nat.add(bit(True{}), Nat.add(S.Pos.nat(S.XI{p}), S.Pos.nat(S.XI{q}))) == 1n+Nat.double(_) : Nat}
      NR.ring_eq([S.Pos.nat(p), S.Pos.nat(q)], NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{0n}}}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{1n}}}}}, NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NAdd{NR.NCst{1n}, NR.NAdd{NR.NVar{0n}, NR.NVar{1n}}}}}, {==})

def add_nat(+a: S.Pos, +b: S.Pos) -> {Nat.add(S.Pos.nat(a), S.Pos.nat(b)) == S.Pos.nat(S.Pos.add(a, b)) : Nat}:
  addc_nat(a, b, False{})

def mul_nat(a: S.Pos, +b: S.Pos) -> {Nat.mul(S.Pos.nat(a), S.Pos.nat(b)) == S.Pos.nat(S.Pos.mul(a, b)) : Nat}:
  match a:
    case S.XH{}:
      %N.add_zero(S.Pos.nat(b)) : {_ == S.Pos.nat(b) : Nat}
      {==}
    case S.XO{+p}:
      %mul_nat(p, b) : {Nat.mul(Nat.double(S.Pos.nat(p)), S.Pos.nat(b)) == Nat.double(_) : Nat}
      NR.ring_eq([S.Pos.nat(p), S.Pos.nat(b)], NR.NMul{NR.NDbl{NR.NVar{0n}}, NR.NVar{1n}}, NR.NDbl{NR.NMul{NR.NVar{0n}, NR.NVar{1n}}}, {==})
    case S.XI{+p}:
      %addc_nat(S.XO{S.Pos.mul(p, b)}, b, False{}) : {Nat.mul(1n+Nat.double(S.Pos.nat(p)), S.Pos.nat(b)) == _ : Nat}
      %mul_nat(p, b) : {Nat.mul(1n+Nat.double(S.Pos.nat(p)), S.Pos.nat(b)) == Nat.add(Nat.double(_), S.Pos.nat(b)) : Nat}
      NR.ring_eq([S.Pos.nat(p), S.Pos.nat(b)], NR.NMul{NR.NAdd{NR.NCst{1n}, NR.NDbl{NR.NVar{0n}}}, NR.NVar{1n}}, NR.NAdd{NR.NDbl{NR.NMul{NR.NVar{0n}, NR.NVar{1n}}}, NR.NVar{1n}}, {==})

# Injectivity
# -----------
# pm1(p) is nat(p) - 1, and of_succ(pm1(p)) rebuilds p, so nat forgets nothing.

def pm1(p: S.Pos) -> Nat:
  match p:
    case S.XH{}:
      0n
    case S.XO{q}:
      1n+Nat.double(pm1(q))
    case S.XI{q}:
      2n+Nat.double(pm1(q))

def nat_form(p: S.Pos) -> {S.Pos.nat(p) == 1n+pm1(p) : Nat}:
  match p:
    case S.XH{}:
      {==}
    case S.XO{+q}:
      %nat_form(q) : {Nat.double(S.Pos.nat(q)) == Nat.double(_) : Nat}
      {==}
    case S.XI{+q}:
      %nat_form(q) : {1n+Nat.double(S.Pos.nat(q)) == 1n+Nat.double(_) : Nat}
      {==}

def os_odd(k: Nat) -> {S.XO{S.Pos.of_succ(k)} == S.Pos.of_succ(1n+Nat.double(k)) : S.Pos}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %os_odd(j) : {S.XO{S.Pos.succ(S.Pos.of_succ(j))} == S.Pos.succ(S.Pos.succ(_)) : S.Pos}
      {==}

def os_even(k: Nat) -> {S.XI{S.Pos.of_succ(k)} == S.Pos.of_succ(2n+Nat.double(k)) : S.Pos}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %os_even(j) : {S.XI{S.Pos.succ(S.Pos.of_succ(j))} == S.Pos.succ(S.Pos.succ(_)) : S.Pos}
      {==}

def retract(p: S.Pos) -> {S.Pos.of_succ(pm1(p)) == p : S.Pos}:
  match p:
    case S.XH{}:
      {==}
    case S.XO{+q}:
      %os_odd(pm1(q)) : {_ == S.XO{q} : S.Pos}
      %retract(q) : {S.XO{S.Pos.of_succ(pm1(q))} == S.XO{_} : S.Pos}
      {==}
    case S.XI{+q}:
      %os_even(pm1(q)) : {_ == S.XI{q} : S.Pos}
      %retract(q) : {S.XI{S.Pos.of_succ(pm1(q))} == S.XI{_} : S.Pos}
      {==}

def nat_inj(+p: S.Pos, +q: S.Pos, e: {S.Pos.nat(p) == S.Pos.nat(q) : Nat}) -> {p == q : S.Pos}:
  %retract(p) : {_ == q : S.Pos}
  %retract(q) : {S.Pos.of_succ(pm1(p)) == _ : S.Pos}
  %nat_form(p) : {S.Pos.of_succ(pred(_)) == S.Pos.of_succ(pm1(q)) : S.Pos}
  %nat_form(q) : {S.Pos.of_succ(pred(S.Pos.nat(p))) == S.Pos.of_succ(pred(_)) : S.Pos}
  %e : {S.Pos.of_succ(pred(S.Pos.nat(p))) == S.Pos.of_succ(pred(_)) : S.Pos}
  {==}

# nat(of_succ(k)) is 1 + k
def nat_os(k: Nat) -> {1n+k == S.Pos.nat(S.Pos.of_succ(k)) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n++j:
      %succ_nat(S.Pos.of_succ(j)) : {2n+j == _ : Nat}
      %nat_os(j) : {2n+j == 1n+_ : Nat}
      {==}

# Doubling lemmas
# ---------------

# succ(pred_double(q)) is 2q
def succ_pd(q: S.Pos) -> {S.XO{q} == S.Pos.succ(S.Pos.pred_double(q)) : S.Pos}:
  match q:
    case S.XH{}:
      {==}
    case S.XO{+r}:
      %succ_pd(r) : {S.XO{S.XO{r}} == S.XO{_} : S.Pos}
      {==}
    case S.XI{r}:
      {==}

# pred_double(succ(q)) is 2q + 1
def pd_succ(q: S.Pos) -> {S.XI{q} == S.Pos.pred_double(S.Pos.succ(q)) : S.Pos}:
  match q:
    case S.XH{}:
      {==}
    case S.XO{r}:
      {==}
    case S.XI{+r}:
      %pd_succ(r) : {S.XI{S.XI{r}} == S.XI{_} : S.Pos}
      {==}

# pred_double(of_succ(j)) is of_succ(2j)
def pd_os(j: Nat) -> {S.Pos.pred_double(S.Pos.of_succ(j)) == S.Pos.of_succ(Nat.double(j)) : S.Pos}:
  match j:
    case 0n:
      {==}
    case 1n++k:
      %pd_os(k) : {S.Pos.pred_double(S.Pos.succ(S.Pos.of_succ(k))) == S.Pos.succ(S.Pos.succ(_)) : S.Pos}
      %pd_succ(S.Pos.of_succ(k)) : {_ == S.Pos.succ(S.Pos.succ(S.Pos.pred_double(S.Pos.of_succ(k)))) : S.Pos}
      %succ_pd(S.Pos.of_succ(k)) : {S.XI{S.Pos.of_succ(k)} == S.Pos.succ(_) : S.Pos}
      {==}

def form_nat(+p: S.Pos) -> {1n+pm1(p) == S.Pos.nat(p) : Nat}:
  Equal.sym(Nat, S.Pos.nat(p), 1n+pm1(p), nat_form(p))
