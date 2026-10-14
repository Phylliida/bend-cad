# The ring normalizer of lib/zring.bend, proven sound in every ordered field:
# two integer-coefficient expressions with equal normal forms are equal for
# every assignment of field values to their variables. The normalizer
# (R.norm) is the same untrusted code; only the soundness proof is new, a
# line-for-line port of lib/zring.bend's with the laws of lib/flaws.bend.
# The coefficients enter the field through O.ofz, which respects integer
# addition, multiplication and negation (proven here through unary
# naturals, as lib/z.bend relates binary integers to differences).
#
# Use: fring_eq(~F, env, e1, e2, {==}) proves
# {zeval(~F, env, e1) == zeval(~F, env, e2)} when e1, e2 normalize alike.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ./flaws.bend as FL
import ./pos.bend as P
import ./z.bend as LZ
import ./natring.bend as NR
import ./zring.bend as R

# Integer expressions evaluated in F
def zeval(~F: O.OField, +env: List<&2, O.C(F)>, e: E.ZExpr) -> O.C(F):
  match e:
    case E.ZVar{i}:
      O.lookup(~F, env, i)
    case E.ZCst{c}:
      O.ofz(~F, c)
    case E.ZAdd{a, b}:
      O.add(F, zeval(~F, env, a), zeval(~F, env, b))
    case E.ZSub{a, b}:
      O.sub(~F, zeval(~F, env, a), zeval(~F, env, b))
    case E.ZMul{a, b}:
      O.mul(F, zeval(~F, env, a), zeval(~F, env, b))
    case E.ZNeg{a}:
      O.neg(F, zeval(~F, env, a))

# The integers in F
# -----------------

# n as 1 + 1 + ... + 1 in F
def ofn(~F: O.OField, n: Nat) -> O.C(F):
  match n:
    case 0n:
      O.zero(F)
    case 1n+k:
      O.add(F, O.one(F), ofn(~F, k))

def ofn_add(~F: O.OField, a: Nat, +b: Nat) -> {O.add(F, ofn(~F, a), ofn(~F, b)) == ofn(~F, Nat.add(a, b)) : O.C(F)}:
  match a:
    case 0n:
      FL.zero_add(~F, ofn(~F, b))
    case 1n++p:
      %ofn_add(~F, p, b) : {O.add(F, O.add(F, O.one(F), ofn(~F, p)), ofn(~F, b)) == O.add(F, O.one(F), _) : O.C(F)}
      O.add_assoc(F)(O.one(F), ofn(~F, p), ofn(~F, b))

def ofn_mul(~F: O.OField, a: Nat, +b: Nat) -> {O.mul(F, ofn(~F, a), ofn(~F, b)) == ofn(~F, Nat.mul(a, b)) : O.C(F)}:
  match a:
    case 0n:
      FL.zero_mul(~F, ofn(~F, b))
    case 1n++p:
      %ofn_add(~F, b, Nat.mul(p, b)) : {O.mul(F, O.add(F, O.one(F), ofn(~F, p)), ofn(~F, b)) == _ : O.C(F)}
      %ofn_mul(~F, p, b) : {O.mul(F, O.add(F, O.one(F), ofn(~F, p)), ofn(~F, b)) == O.add(F, ofn(~F, b), _) : O.C(F)}
      %FL.mul_add_r(~F, O.one(F), ofn(~F, p), ofn(~F, b)) : {_ == O.add(F, ofn(~F, b), O.mul(F, ofn(~F, p), ofn(~F, b))) : O.C(F)}
      %FL.one_mul(~F, ofn(~F, b)) : {O.add(F, _, O.mul(F, ofn(~F, p), ofn(~F, b))) == O.add(F, ofn(~F, b), O.mul(F, ofn(~F, p), ofn(~F, b))) : O.C(F)}
      {==}

def ofn_double(~F: O.OField, n: Nat) -> {ofn(~F, Nat.double(n)) == O.add(F, ofn(~F, n), ofn(~F, n)) : O.C(F)}:
  match n:
    case 0n:
      FL.add_zero(~F, O.zero(F))
    case 1n++p:
      %Equal.sym(O.C(F), ofn(~F, Nat.double(p)), O.add(F, ofn(~F, p), ofn(~F, p)), ofn_double(~F, p)) : {O.add(F, O.one(F), O.add(F, O.one(F), _)) == O.add(F, O.add(F, O.one(F), ofn(~F, p)), O.add(F, O.one(F), ofn(~F, p))) : O.C(F)}
      %FL.add_assoc(~F, O.one(F), ofn(~F, p), O.add(F, O.one(F), ofn(~F, p))) : {O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, ofn(~F, p), ofn(~F, p)))) == _ : O.C(F)}
      %FL.add_swap(~F, O.one(F), ofn(~F, p), ofn(~F, p)) : {O.add(F, O.one(F), O.add(F, O.one(F), O.add(F, ofn(~F, p), ofn(~F, p)))) == O.add(F, O.one(F), _) : O.C(F)}
      {==}

# a binary positive is its unary meaning
def ofp_nat(~F: O.OField, p: S.Pos) -> {ofn(~F, S.Pos.nat(p)) == O.ofp(~F, p) : O.C(F)}:
  match p:
    case S.XH{}:
      O.add_zero(F)(O.one(F))
    case S.XO{+q}:
      %ofp_nat(~F, q) : {ofn(~F, Nat.double(S.Pos.nat(q))) == O.add(F, _, _) : O.C(F)}
      ofn_double(~F, S.Pos.nat(q))
    case S.XI{+q}:
      %ofp_nat(~F, q) : {ofn(~F, 1n+Nat.double(S.Pos.nat(q))) == O.add(F, O.add(F, _, _), O.one(F)) : O.C(F)}
      %Equal.sym(O.C(F), ofn(~F, Nat.double(S.Pos.nat(q))), O.add(F, ofn(~F, S.Pos.nat(q)), ofn(~F, S.Pos.nat(q))), ofn_double(~F, S.Pos.nat(q))) : {O.add(F, O.one(F), _) == O.add(F, O.add(F, ofn(~F, S.Pos.nat(q)), ofn(~F, S.Pos.nat(q))), O.one(F)) : O.C(F)}
      FL.add_comm(~F, O.one(F), O.add(F, ofn(~F, S.Pos.nat(q)), ofn(~F, S.Pos.nat(q))))

# of_diff(a, b) is a - b in F
def ofz_diff(~F: O.OField, a: Nat, b: Nat) -> {O.sub(~F, ofn(~F, a), ofn(~F, b)) == O.ofz(~F, S.Z.of_diff(a, b)) : O.C(F)}:
  match a b:
    case 0n 0n:
      O.add_neg(F)(O.zero(F))
    case 1n++k 0n:
      %ofp_nat(~F, S.Pos.of_succ(k)) : {O.add(F, ofn(~F, 1n+k), O.neg(F, O.zero(F))) == _ : O.C(F)}
      %P.nat_os(k) : {O.add(F, ofn(~F, 1n+k), O.neg(F, O.zero(F))) == ofn(~F, _) : O.C(F)}
      FL.sub_zero(~F, ofn(~F, 1n+k))
    case 0n 1n++k:
      %ofp_nat(~F, S.Pos.of_succ(k)) : {O.add(F, O.zero(F), O.neg(F, ofn(~F, 1n+k))) == O.neg(F, _) : O.C(F)}
      %P.nat_os(k) : {O.add(F, O.zero(F), O.neg(F, ofn(~F, 1n+k))) == O.neg(F, ofn(~F, _)) : O.C(F)}
      FL.zero_add(~F, O.neg(F, ofn(~F, 1n+k)))
    case 1n++i 1n++j:
      %ofz_diff(~F, i, j) : {O.sub(~F, ofn(~F, 1n+i), ofn(~F, 1n+j)) == _ : O.C(F)}
      FL.sub_succ(~F, ofn(~F, i), ofn(~F, j))

def ofz_add(~F: O.OField, +x: S.Z, +y: S.Z) -> {O.add(F, O.ofz(~F, x), O.ofz(~F, y)) == O.ofz(~F, S.Z.add(x, y)) : O.C(F)}:
  %LZ.add_diff(x, y) : {O.add(F, O.ofz(~F, x), O.ofz(~F, y)) == O.ofz(~F, _) : O.C(F)}
  %ofz_diff(~F, Nat.add(S.Z.pnat(x), S.Z.pnat(y)), Nat.add(S.Z.nnat(x), S.Z.nnat(y))) : {O.add(F, O.ofz(~F, x), O.ofz(~F, y)) == _ : O.C(F)}
  %ofn_add(~F, S.Z.pnat(x), S.Z.pnat(y)) : {O.add(F, O.ofz(~F, x), O.ofz(~F, y)) == O.sub(~F, _, ofn(~F, Nat.add(S.Z.nnat(x), S.Z.nnat(y)))) : O.C(F)}
  %ofn_add(~F, S.Z.nnat(x), S.Z.nnat(y)) : {O.add(F, O.ofz(~F, x), O.ofz(~F, y)) == O.sub(~F, O.add(F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.pnat(y))), _) : O.C(F)}
  %LZ.diff_parts(x) : {O.add(F, O.ofz(~F, _), O.ofz(~F, y)) == O.sub(~F, O.add(F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.pnat(y))), O.add(F, ofn(~F, S.Z.nnat(x)), ofn(~F, S.Z.nnat(y)))) : O.C(F)}
  %ofz_diff(~F, S.Z.pnat(x), S.Z.nnat(x)) : {O.add(F, _, O.ofz(~F, y)) == O.sub(~F, O.add(F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.pnat(y))), O.add(F, ofn(~F, S.Z.nnat(x)), ofn(~F, S.Z.nnat(y)))) : O.C(F)}
  %LZ.diff_parts(y) : {O.add(F, O.sub(~F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.nnat(x))), O.ofz(~F, _)) == O.sub(~F, O.add(F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.pnat(y))), O.add(F, ofn(~F, S.Z.nnat(x)), ofn(~F, S.Z.nnat(y)))) : O.C(F)}
  %ofz_diff(~F, S.Z.pnat(y), S.Z.nnat(y)) : {O.add(F, O.sub(~F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.nnat(x))), _) == O.sub(~F, O.add(F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.pnat(y))), O.add(F, ofn(~F, S.Z.nnat(x)), ofn(~F, S.Z.nnat(y)))) : O.C(F)}
  %FL.neg_add(~F, ofn(~F, S.Z.nnat(x)), ofn(~F, S.Z.nnat(y))) : {O.add(F, O.sub(~F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.nnat(x))), O.sub(~F, ofn(~F, S.Z.pnat(y)), ofn(~F, S.Z.nnat(y)))) == O.add(F, O.add(F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.pnat(y))), _) : O.C(F)}
  FL.add_shuffle(~F, ofn(~F, S.Z.pnat(x)), O.neg(F, ofn(~F, S.Z.nnat(x))), ofn(~F, S.Z.pnat(y)), O.neg(F, ofn(~F, S.Z.nnat(y))))

def ofz_mul(~F: O.OField, +x: S.Z, +y: S.Z) -> {O.mul(F, O.ofz(~F, x), O.ofz(~F, y)) == O.ofz(~F, S.Z.mul(x, y)) : O.C(F)}:
  %LZ.mul_diff(x, y) : {O.mul(F, O.ofz(~F, x), O.ofz(~F, y)) == O.ofz(~F, _) : O.C(F)}
  %ofz_diff(~F, Nat.add(Nat.mul(S.Z.pnat(x), S.Z.pnat(y)), Nat.mul(S.Z.nnat(x), S.Z.nnat(y))), Nat.add(Nat.mul(S.Z.pnat(x), S.Z.nnat(y)), Nat.mul(S.Z.nnat(x), S.Z.pnat(y)))) : {O.mul(F, O.ofz(~F, x), O.ofz(~F, y)) == _ : O.C(F)}
  %ofn_add(~F, Nat.mul(S.Z.pnat(x), S.Z.pnat(y)), Nat.mul(S.Z.nnat(x), S.Z.nnat(y))) : {O.mul(F, O.ofz(~F, x), O.ofz(~F, y)) == O.sub(~F, _, ofn(~F, Nat.add(Nat.mul(S.Z.pnat(x), S.Z.nnat(y)), Nat.mul(S.Z.nnat(x), S.Z.pnat(y))))) : O.C(F)}
  %ofn_add(~F, Nat.mul(S.Z.pnat(x), S.Z.nnat(y)), Nat.mul(S.Z.nnat(x), S.Z.pnat(y))) : {O.mul(F, O.ofz(~F, x), O.ofz(~F, y)) == O.sub(~F, O.add(F, ofn(~F, Nat.mul(S.Z.pnat(x), S.Z.pnat(y))), ofn(~F, Nat.mul(S.Z.nnat(x), S.Z.nnat(y)))), _) : O.C(F)}
  %ofn_mul(~F, S.Z.pnat(x), S.Z.pnat(y)) : {O.mul(F, O.ofz(~F, x), O.ofz(~F, y)) == O.sub(~F, O.add(F, _, ofn(~F, Nat.mul(S.Z.nnat(x), S.Z.nnat(y)))), O.add(F, ofn(~F, Nat.mul(S.Z.pnat(x), S.Z.nnat(y))), ofn(~F, Nat.mul(S.Z.nnat(x), S.Z.pnat(y))))) : O.C(F)}
  %ofn_mul(~F, S.Z.nnat(x), S.Z.nnat(y)) : {O.mul(F, O.ofz(~F, x), O.ofz(~F, y)) == O.sub(~F, O.add(F, O.mul(F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.pnat(y))), _), O.add(F, ofn(~F, Nat.mul(S.Z.pnat(x), S.Z.nnat(y))), ofn(~F, Nat.mul(S.Z.nnat(x), S.Z.pnat(y))))) : O.C(F)}
  %ofn_mul(~F, S.Z.pnat(x), S.Z.nnat(y)) : {O.mul(F, O.ofz(~F, x), O.ofz(~F, y)) == O.sub(~F, O.add(F, O.mul(F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.pnat(y))), O.mul(F, ofn(~F, S.Z.nnat(x)), ofn(~F, S.Z.nnat(y)))), O.add(F, _, ofn(~F, Nat.mul(S.Z.nnat(x), S.Z.pnat(y))))) : O.C(F)}
  %ofn_mul(~F, S.Z.nnat(x), S.Z.pnat(y)) : {O.mul(F, O.ofz(~F, x), O.ofz(~F, y)) == O.sub(~F, O.add(F, O.mul(F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.pnat(y))), O.mul(F, ofn(~F, S.Z.nnat(x)), ofn(~F, S.Z.nnat(y)))), O.add(F, O.mul(F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.nnat(y))), _)) : O.C(F)}
  %LZ.diff_parts(x) : {O.mul(F, O.ofz(~F, _), O.ofz(~F, y)) == O.sub(~F, O.add(F, O.mul(F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.pnat(y))), O.mul(F, ofn(~F, S.Z.nnat(x)), ofn(~F, S.Z.nnat(y)))), O.add(F, O.mul(F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.nnat(y))), O.mul(F, ofn(~F, S.Z.nnat(x)), ofn(~F, S.Z.pnat(y))))) : O.C(F)}
  %ofz_diff(~F, S.Z.pnat(x), S.Z.nnat(x)) : {O.mul(F, _, O.ofz(~F, y)) == O.sub(~F, O.add(F, O.mul(F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.pnat(y))), O.mul(F, ofn(~F, S.Z.nnat(x)), ofn(~F, S.Z.nnat(y)))), O.add(F, O.mul(F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.nnat(y))), O.mul(F, ofn(~F, S.Z.nnat(x)), ofn(~F, S.Z.pnat(y))))) : O.C(F)}
  %LZ.diff_parts(y) : {O.mul(F, O.sub(~F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.nnat(x))), O.ofz(~F, _)) == O.sub(~F, O.add(F, O.mul(F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.pnat(y))), O.mul(F, ofn(~F, S.Z.nnat(x)), ofn(~F, S.Z.nnat(y)))), O.add(F, O.mul(F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.nnat(y))), O.mul(F, ofn(~F, S.Z.nnat(x)), ofn(~F, S.Z.pnat(y))))) : O.C(F)}
  %ofz_diff(~F, S.Z.pnat(y), S.Z.nnat(y)) : {O.mul(F, O.sub(~F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.nnat(x))), _) == O.sub(~F, O.add(F, O.mul(F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.pnat(y))), O.mul(F, ofn(~F, S.Z.nnat(x)), ofn(~F, S.Z.nnat(y)))), O.add(F, O.mul(F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.nnat(y))), O.mul(F, ofn(~F, S.Z.nnat(x)), ofn(~F, S.Z.pnat(y))))) : O.C(F)}
  FL.mul_sub(~F, ofn(~F, S.Z.pnat(x)), ofn(~F, S.Z.nnat(x)), ofn(~F, S.Z.pnat(y)), ofn(~F, S.Z.nnat(y)))

def ofz_neg(~F: O.OField, x: S.Z) -> {O.neg(F, O.ofz(~F, x)) == O.ofz(~F, S.Z.neg(x)) : O.C(F)}:
  match x:
    case S.Z0{}:
      Equal.sym(O.C(F), O.zero(F), O.neg(F, O.zero(F)), FL.neg_zero(~F))
    case S.Zpos{p}:
      {==}
    case S.Zneg{+p}:
      FL.neg_neg(~F, O.ofp(~F, p))

# Polynomials evaluated in F
# --------------------------

def femono(~F: O.OField, +env: List<&2, O.C(F)>, m: List<&2, Nat>) -> O.C(F):
  match m:
    case Nil{}:
      O.one(F)
    case Con{v, vs}:
      O.mul(F, O.lookup(~F, env, v), femono(~F, env, vs))

def fepoly(~F: O.OField, +env: List<&2, O.C(F)>, p: List<&2, R.ZTerm>) -> O.C(F):
  match p:
    case Nil{}:
      O.zero(F)
    case Con{R.ZTerm{c, m}, rest}:
      O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, rest))

# Soundness (lib/zring.bend's, in F)
# ----------------------------------

def minsert_ok.dec(~F: O.OField, +env: List<&2, O.C(F)>, b: Bool, +x: Nat, +h: Nat, +t: List<&2, Nat>,
  rec: {O.mul(F, O.lookup(~F, env, x), femono(~F, env, t)) == femono(~F, env, NR.minsert(x, t)) : O.C(F)})
  -> {O.mul(F, O.lookup(~F, env, x), O.mul(F, O.lookup(~F, env, h), femono(~F, env, t))) == femono(~F, env, NR.minsert.dec(b, x, h, t, NR.minsert(x, t))) : O.C(F)}:
  match b:
    case True{}:
      {==}
    case False{}:
      %rec : {O.mul(F, O.lookup(~F, env, x), O.mul(F, O.lookup(~F, env, h), femono(~F, env, t))) == O.mul(F, O.lookup(~F, env, h), _) : O.C(F)}
      FL.mul_swap(~F, O.lookup(~F, env, x), O.lookup(~F, env, h), femono(~F, env, t))

def minsert_ok(~F: O.OField, +env: List<&2, O.C(F)>, +x: Nat, m: List<&2, Nat>) -> {O.mul(F, O.lookup(~F, env, x), femono(~F, env, m)) == femono(~F, env, NR.minsert(x, m)) : O.C(F)}:
  match m:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      minsert_ok.dec(~F, env, Nat.is_le(x, h), x, h, t, minsert_ok(~F, env, x, t))

def mmul_ok(~F: O.OField, +env: List<&2, O.C(F)>, m1: List<&2, Nat>, +m2: List<&2, Nat>) -> {O.mul(F, femono(~F, env, m1), femono(~F, env, m2)) == femono(~F, env, NR.mmul(m1, m2)) : O.C(F)}:
  match m1:
    case Nil{}:
      %FL.one_mul(~F, femono(~F, env, m2)) : {_ == femono(~F, env, m2) : O.C(F)}
      {==}
    case Con{+v, +vs}:
      %minsert_ok(~F, env, v, NR.mmul(vs, m2)) : {O.mul(F, O.mul(F, O.lookup(~F, env, v), femono(~F, env, vs)), femono(~F, env, m2)) == _ : O.C(F)}
      %mmul_ok(~F, env, vs, m2) : {O.mul(F, O.mul(F, O.lookup(~F, env, v), femono(~F, env, vs)), femono(~F, env, m2)) == O.mul(F, O.lookup(~F, env, v), _) : O.C(F)}
      %FL.mul_assoc(~F, O.lookup(~F, env, v), femono(~F, env, vs), femono(~F, env, m2)) : {_ == O.mul(F, O.lookup(~F, env, v), O.mul(F, femono(~F, env, vs), femono(~F, env, m2))) : O.C(F)}
      {==}

def pcoef_ok(~F: O.OField, +env: List<&2, O.C(F)>, s: S.Z, +n: List<&2, Nat>, +rest: List<&2, R.ZTerm>) -> {O.add(F, O.mul(F, O.ofz(~F, s), femono(~F, env, n)), fepoly(~F, env, rest)) == fepoly(~F, env, R.pcoef(s, n, rest)) : O.C(F)}:
  match s:
    case S.Z0{}:
      %Equal.sym(O.C(F), O.mul(F, O.zero(F), femono(~F, env, n)), O.zero(F), FL.zero_mul(~F, femono(~F, env, n))) : {O.add(F, _, fepoly(~F, env, rest)) == fepoly(~F, env, rest) : O.C(F)}
      FL.zero_add(~F, fepoly(~F, env, rest))
    case S.Zpos{p}:
      {==}
    case S.Zneg{p}:
      {==}

def pins_ok.dec(~F: O.OField, +env: List<&2, O.C(F)>, o: Cmp, +c: S.Z, +m: List<&2, Nat>, +d: S.Z, +n: List<&2, Nat>, +rest: List<&2, R.ZTerm>,
  e: {o == NR.mcmp(m, n) : Cmp},
  rec: {O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, rest)) == fepoly(~F, env, R.pins(c, m, rest)) : O.C(F)})
  -> {O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), O.add(F, O.mul(F, O.ofz(~F, d), femono(~F, env, n)), fepoly(~F, env, rest))) == fepoly(~F, env, R.pins.dec(o, c, m, d, n, rest, R.pins(c, m, rest))) : O.C(F)}:
  match o:
    case LT{}:
      {==}
    case EQ{}:
      %pcoef_ok(~F, env, S.Z.add(c, d), n, rest) : {O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), O.add(F, O.mul(F, O.ofz(~F, d), femono(~F, env, n)), fepoly(~F, env, rest))) == _ : O.C(F)}
      %ofz_add(~F, c, d) : {O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), O.add(F, O.mul(F, O.ofz(~F, d), femono(~F, env, n)), fepoly(~F, env, rest))) == O.add(F, O.mul(F, _, femono(~F, env, n)), fepoly(~F, env, rest)) : O.C(F)}
      %FL.mul_add_r(~F, O.ofz(~F, c), O.ofz(~F, d), femono(~F, env, n)) : {O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), O.add(F, O.mul(F, O.ofz(~F, d), femono(~F, env, n)), fepoly(~F, env, rest))) == O.add(F, _, fepoly(~F, env, rest)) : O.C(F)}
      %FL.add_assoc(~F, O.mul(F, O.ofz(~F, c), femono(~F, env, n)), O.mul(F, O.ofz(~F, d), femono(~F, env, n)), fepoly(~F, env, rest)) : {O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), O.add(F, O.mul(F, O.ofz(~F, d), femono(~F, env, n)), fepoly(~F, env, rest))) == _ : O.C(F)}
      %NR.mcmp_eq(m, n, e) : {O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), O.add(F, O.mul(F, O.ofz(~F, d), femono(~F, env, n)), fepoly(~F, env, rest))) == O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, _)), O.add(F, O.mul(F, O.ofz(~F, d), femono(~F, env, n)), fepoly(~F, env, rest))) : O.C(F)}
      {==}
    case GT{}:
      %rec : {O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), O.add(F, O.mul(F, O.ofz(~F, d), femono(~F, env, n)), fepoly(~F, env, rest))) == O.add(F, O.mul(F, O.ofz(~F, d), femono(~F, env, n)), _) : O.C(F)}
      FL.add_swap(~F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), O.mul(F, O.ofz(~F, d), femono(~F, env, n)), fepoly(~F, env, rest))

def pins_ok(~F: O.OField, +env: List<&2, O.C(F)>, +c: S.Z, +m: List<&2, Nat>, p: List<&2, R.ZTerm>) -> {O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, p)) == fepoly(~F, env, R.pins(c, m, p)) : O.C(F)}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{+d, +n}, +rest}:
      pins_ok.dec(~F, env, NR.mcmp(m, n), c, m, d, n, rest, {==}, pins_ok(~F, env, c, m, rest))

def pinsert_ok(~F: O.OField, +env: List<&2, O.C(F)>, c: S.Z, +m: List<&2, Nat>, +p: List<&2, R.ZTerm>) -> {O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, p)) == fepoly(~F, env, R.pinsert(c, m, p)) : O.C(F)}:
  match c:
    case S.Z0{}:
      %Equal.sym(O.C(F), O.mul(F, O.zero(F), femono(~F, env, m)), O.zero(F), FL.zero_mul(~F, femono(~F, env, m))) : {O.add(F, _, fepoly(~F, env, p)) == fepoly(~F, env, p) : O.C(F)}
      FL.zero_add(~F, fepoly(~F, env, p))
    case S.Zpos{q}:
      pins_ok(~F, env, S.Zpos{q}, m, p)
    case S.Zneg{q}:
      pins_ok(~F, env, S.Zneg{q}, m, p)

def padd_ok(~F: O.OField, +env: List<&2, O.C(F)>, p: List<&2, R.ZTerm>, +q: List<&2, R.ZTerm>) -> {O.add(F, fepoly(~F, env, p), fepoly(~F, env, q)) == fepoly(~F, env, R.padd(p, q)) : O.C(F)}:
  match p:
    case Nil{}:
      FL.zero_add(~F, fepoly(~F, env, q))
    case Con{R.ZTerm{+c, +m}, +rest}:
      %pinsert_ok(~F, env, c, m, R.padd(rest, q)) : {O.add(F, O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, rest)), fepoly(~F, env, q)) == _ : O.C(F)}
      %padd_ok(~F, env, rest, q) : {O.add(F, O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, rest)), fepoly(~F, env, q)) == O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), _) : O.C(F)}
      %FL.add_assoc(~F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, rest), fepoly(~F, env, q)) : {_ == O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), O.add(F, fepoly(~F, env, rest), fepoly(~F, env, q))) : O.C(F)}
      {==}

def pscale_ok(~F: O.OField, +env: List<&2, O.C(F)>, +c: S.Z, +m: List<&2, Nat>, q: List<&2, R.ZTerm>) -> {O.mul(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, q)) == fepoly(~F, env, R.pscale(c, m, q)) : O.C(F)}:
  match q:
    case Nil{}:
      %FL.mul_zero(~F, O.mul(F, O.ofz(~F, c), femono(~F, env, m))) : {_ == O.zero(F) : O.C(F)}
      {==}
    case Con{R.ZTerm{+d, +n}, +rest}:
      %pinsert_ok(~F, env, S.Z.mul(c, d), NR.mmul(m, n), R.pscale(c, m, rest)) : {O.mul(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), O.add(F, O.mul(F, O.ofz(~F, d), femono(~F, env, n)), fepoly(~F, env, rest))) == _ : O.C(F)}
      %pscale_ok(~F, env, c, m, rest) : {O.mul(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), O.add(F, O.mul(F, O.ofz(~F, d), femono(~F, env, n)), fepoly(~F, env, rest))) == O.add(F, O.mul(F, O.ofz(~F, S.Z.mul(c, d)), femono(~F, env, NR.mmul(m, n))), _) : O.C(F)}
      %mmul_ok(~F, env, m, n) : {O.mul(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), O.add(F, O.mul(F, O.ofz(~F, d), femono(~F, env, n)), fepoly(~F, env, rest))) == O.add(F, O.mul(F, O.ofz(~F, S.Z.mul(c, d)), _), O.mul(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, rest))) : O.C(F)}
      %ofz_mul(~F, c, d) : {O.mul(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), O.add(F, O.mul(F, O.ofz(~F, d), femono(~F, env, n)), fepoly(~F, env, rest))) == O.add(F, O.mul(F, _, O.mul(F, femono(~F, env, m), femono(~F, env, n))), O.mul(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, rest))) : O.C(F)}
      %FL.mul_shuffle(~F, O.ofz(~F, c), O.ofz(~F, d), femono(~F, env, m), femono(~F, env, n)) : {O.mul(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), O.add(F, O.mul(F, O.ofz(~F, d), femono(~F, env, n)), fepoly(~F, env, rest))) == O.add(F, _, O.mul(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, rest))) : O.C(F)}
      %FL.mul_add_l(~F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), O.mul(F, O.ofz(~F, d), femono(~F, env, n)), fepoly(~F, env, rest)) : {_ == O.add(F, O.mul(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), O.mul(F, O.ofz(~F, d), femono(~F, env, n))), O.mul(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, rest))) : O.C(F)}
      {==}

def pmul_ok(~F: O.OField, +env: List<&2, O.C(F)>, p: List<&2, R.ZTerm>, +q: List<&2, R.ZTerm>) -> {O.mul(F, fepoly(~F, env, p), fepoly(~F, env, q)) == fepoly(~F, env, R.pmul(p, q)) : O.C(F)}:
  match p:
    case Nil{}:
      FL.zero_mul(~F, fepoly(~F, env, q))
    case Con{R.ZTerm{+c, +m}, +rest}:
      %padd_ok(~F, env, R.pscale(c, m, q), R.pmul(rest, q)) : {O.mul(F, O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, rest)), fepoly(~F, env, q)) == _ : O.C(F)}
      %pscale_ok(~F, env, c, m, q) : {O.mul(F, O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, rest)), fepoly(~F, env, q)) == O.add(F, _, fepoly(~F, env, R.pmul(rest, q))) : O.C(F)}
      %pmul_ok(~F, env, rest, q) : {O.mul(F, O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, rest)), fepoly(~F, env, q)) == O.add(F, O.mul(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, q)), _) : O.C(F)}
      %FL.mul_add_r(~F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, rest), fepoly(~F, env, q)) : {_ == O.add(F, O.mul(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, q)), O.mul(F, fepoly(~F, env, rest), fepoly(~F, env, q))) : O.C(F)}
      {==}

def pneg_ok(~F: O.OField, +env: List<&2, O.C(F)>, p: List<&2, R.ZTerm>) -> {O.neg(F, fepoly(~F, env, p)) == fepoly(~F, env, R.pneg(p)) : O.C(F)}:
  match p:
    case Nil{}:
      Equal.sym(O.C(F), O.zero(F), O.neg(F, O.zero(F)), FL.neg_zero(~F))
    case Con{R.ZTerm{+c, +m}, +rest}:
      %pneg_ok(~F, env, rest) : {O.neg(F, O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, rest))) == O.add(F, O.mul(F, O.ofz(~F, S.Z.neg(c)), femono(~F, env, m)), _) : O.C(F)}
      %ofz_neg(~F, c) : {O.neg(F, O.add(F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, rest))) == O.add(F, O.mul(F, _, femono(~F, env, m)), O.neg(F, fepoly(~F, env, rest))) : O.C(F)}
      %FL.neg_add(~F, O.mul(F, O.ofz(~F, c), femono(~F, env, m)), fepoly(~F, env, rest)) : {_ == O.add(F, O.mul(F, O.neg(F, O.ofz(~F, c)), femono(~F, env, m)), O.neg(F, fepoly(~F, env, rest))) : O.C(F)}
      %FL.neg_mul(~F, O.ofz(~F, c), femono(~F, env, m)) : {O.add(F, _, O.neg(F, fepoly(~F, env, rest))) == O.add(F, O.mul(F, O.neg(F, O.ofz(~F, c)), femono(~F, env, m)), O.neg(F, fepoly(~F, env, rest))) : O.C(F)}
      {==}

def pconst_ok(~F: O.OField, +env: List<&2, O.C(F)>, c: S.Z) -> {fepoly(~F, env, R.pconst(c)) == O.ofz(~F, c) : O.C(F)}:
  match c:
    case S.Z0{}:
      {==}
    case S.Zpos{+q}:
      %FL.add_zero(~F, O.mul(F, O.ofp(~F, q), O.one(F))) : {_ == O.ofp(~F, q) : O.C(F)}
      %FL.mul_one(~F, O.ofp(~F, q)) : {_ == O.ofp(~F, q) : O.C(F)}
      {==}
    case S.Zneg{+q}:
      %FL.add_zero(~F, O.mul(F, O.neg(F, O.ofp(~F, q)), O.one(F))) : {_ == O.neg(F, O.ofp(~F, q)) : O.C(F)}
      %FL.mul_one(~F, O.neg(F, O.ofp(~F, q))) : {_ == O.neg(F, O.ofp(~F, q)) : O.C(F)}
      {==}

def norm_ok(~F: O.OField, +env: List<&2, O.C(F)>, e: E.ZExpr) -> {fepoly(~F, env, R.norm(e)) == zeval(~F, env, e) : O.C(F)}:
  match e:
    case E.ZVar{+i}:
      %FL.add_zero(~F, O.mul(F, O.one(F), O.mul(F, O.lookup(~F, env, i), O.one(F)))) : {_ == O.lookup(~F, env, i) : O.C(F)}
      %FL.one_mul(~F, O.mul(F, O.lookup(~F, env, i), O.one(F))) : {_ == O.lookup(~F, env, i) : O.C(F)}
      %FL.mul_one(~F, O.lookup(~F, env, i)) : {_ == O.lookup(~F, env, i) : O.C(F)}
      {==}
    case E.ZCst{c}:
      pconst_ok(~F, env, c)
    case E.ZAdd{+a, +b}:
      %norm_ok(~F, env, a) : {fepoly(~F, env, R.padd(R.norm(a), R.norm(b))) == O.add(F, _, zeval(~F, env, b)) : O.C(F)}
      %norm_ok(~F, env, b) : {fepoly(~F, env, R.padd(R.norm(a), R.norm(b))) == O.add(F, fepoly(~F, env, R.norm(a)), _) : O.C(F)}
      %padd_ok(~F, env, R.norm(a), R.norm(b)) : {_ == O.add(F, fepoly(~F, env, R.norm(a)), fepoly(~F, env, R.norm(b))) : O.C(F)}
      {==}
    case E.ZSub{+a, +b}:
      %norm_ok(~F, env, a) : {fepoly(~F, env, R.padd(R.norm(a), R.pneg(R.norm(b)))) == O.add(F, _, O.neg(F, zeval(~F, env, b))) : O.C(F)}
      %norm_ok(~F, env, b) : {fepoly(~F, env, R.padd(R.norm(a), R.pneg(R.norm(b)))) == O.add(F, fepoly(~F, env, R.norm(a)), O.neg(F, _)) : O.C(F)}
      %padd_ok(~F, env, R.norm(a), R.pneg(R.norm(b))) : {_ == O.add(F, fepoly(~F, env, R.norm(a)), O.neg(F, fepoly(~F, env, R.norm(b)))) : O.C(F)}
      %pneg_ok(~F, env, R.norm(b)) : {O.add(F, fepoly(~F, env, R.norm(a)), _) == O.add(F, fepoly(~F, env, R.norm(a)), O.neg(F, fepoly(~F, env, R.norm(b)))) : O.C(F)}
      {==}
    case E.ZMul{+a, +b}:
      %norm_ok(~F, env, a) : {fepoly(~F, env, R.pmul(R.norm(a), R.norm(b))) == O.mul(F, _, zeval(~F, env, b)) : O.C(F)}
      %norm_ok(~F, env, b) : {fepoly(~F, env, R.pmul(R.norm(a), R.norm(b))) == O.mul(F, fepoly(~F, env, R.norm(a)), _) : O.C(F)}
      %pmul_ok(~F, env, R.norm(a), R.norm(b)) : {_ == O.mul(F, fepoly(~F, env, R.norm(a)), fepoly(~F, env, R.norm(b))) : O.C(F)}
      {==}
    case E.ZNeg{+a}:
      %norm_ok(~F, env, a) : {fepoly(~F, env, R.pneg(R.norm(a))) == O.neg(F, _) : O.C(F)}
      %pneg_ok(~F, env, R.norm(a)) : {_ == O.neg(F, fepoly(~F, env, R.norm(a))) : O.C(F)}
      {==}

# The normalizer's use: two expressions with equal normal forms are equal in
# every ordered field. The hypothesis is checked by computation, {==}.
def fring_eq(~F: O.OField, +env: List<&2, O.C(F)>, +e1: E.ZExpr, +e2: E.ZExpr, h: {R.norm(e1) == R.norm(e2) : List<&2, R.ZTerm>}) -> {zeval(~F, env, e1) == zeval(~F, env, e2) : O.C(F)}:
  %norm_ok(~F, env, e1) : {_ == zeval(~F, env, e2) : O.C(F)}
  %norm_ok(~F, env, e2) : {fepoly(~F, env, R.norm(e1)) == _ : O.C(F)}
  %h : {fepoly(~F, env, R.norm(e1)) == fepoly(~F, env, _) : O.C(F)}
  {==}
