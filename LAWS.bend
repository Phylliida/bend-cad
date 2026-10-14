# bend-cad: the laws. Human-owned: this file states what "correct" means.
# PROOF.bend proves every law stated here; laws that are not proven yet live
# in ROADMAP.bend. See DESIGN.md for the plan.
#
# sk-01 (spec numbers and the ring normalizer). Trusted definitions:
# spec/num.bend (binary positives and integers, and their unary meaning) and
# spec/ring.bend (integer ring expressions and their meaning).

import Base
import ./spec/num.bend as S
import ./spec/ring.bend as E
import ./lib/zring.bend as R

# Positives
# ---------
# A binary positive means a unary natural: Pos.nat is one-to-one, reaches
# every n + 1, and turns the binary operations into Base's.

# LAW: binary addition is addition
law pos_add:
  for +a: S.Pos
  for +b: S.Pos
  {S.Pos.nat(S.Pos.add(a, b)) == Nat.add(S.Pos.nat(a), S.Pos.nat(b)) : Nat}

# LAW: binary multiplication is multiplication
law pos_mul:
  for +a: S.Pos
  for +b: S.Pos
  {S.Pos.nat(S.Pos.mul(a, b)) == Nat.mul(S.Pos.nat(a), S.Pos.nat(b)) : Nat}

# LAW: positives with the same meaning are the same
law pos_inj:
  for +a: S.Pos
  for +b: S.Pos
  for  e: {S.Pos.nat(a) == S.Pos.nat(b) : Nat}
  {a == b : S.Pos}

# LAW: of_succ(n) means n + 1, so every positive natural is reached
law pos_of_succ:
  for +n: Nat
  {S.Pos.nat(S.Pos.of_succ(n)) == 1n+n : Nat}

# Integers
# --------
# An integer means a difference of naturals: of_diff(a, b) is a - b, whose
# parts pnat and nnat (one of them zero) are a - b truncated each way. Every
# integer is the difference of its parts, and the operations act on
# differences as integer arithmetic does.

# LAW: every integer is the difference of its parts
law z_parts:
  for +x: S.Z
  {S.Z.of_diff(S.Z.pnat(x), S.Z.nnat(x)) == x : S.Z}

# LAW: the positive part of a - b is a - b, truncated at zero
law z_pnat:
  for +a: Nat
  for +b: Nat
  {S.Z.pnat(S.Z.of_diff(a, b)) == Nat.sub(a, b) : Nat}

# LAW: the negative part of a - b is b - a, truncated at zero
law z_nnat:
  for +a: Nat
  for +b: Nat
  {S.Z.nnat(S.Z.of_diff(a, b)) == Nat.sub(b, a) : Nat}

# LAW: (a - b) + (c - d) = (a + c) - (b + d)
law z_add:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {S.Z.add(S.Z.of_diff(a, b), S.Z.of_diff(c, d)) == S.Z.of_diff(Nat.add(a, c), Nat.add(b, d)) : S.Z}

# LAW: (a - b) * (c - d) = (ac + bd) - (ad + bc)
law z_mul:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  {S.Z.mul(S.Z.of_diff(a, b), S.Z.of_diff(c, d)) == S.Z.of_diff(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), Nat.add(Nat.mul(a, d), Nat.mul(b, c))) : S.Z}

# LAW: -(a - b) = b - a
law z_neg:
  for +a: Nat
  for +b: Nat
  {S.Z.neg(S.Z.of_diff(a, b)) == S.Z.of_diff(b, a) : S.Z}

# The integers are a commutative ring
# -----------------------------------
# (Consequences of the laws above, stated for reference.)

# LAW: x + y = y + x
law z_add_comm:
  for +x: S.Z
  for +y: S.Z
  {S.Z.add(x, y) == S.Z.add(y, x) : S.Z}

# LAW: (x + y) + z = x + (y + z)
law z_add_assoc:
  for +x: S.Z
  for +y: S.Z
  for +z: S.Z
  {S.Z.add(S.Z.add(x, y), z) == S.Z.add(x, S.Z.add(y, z)) : S.Z}

# LAW: x + 0 = x
law z_add_zero:
  for +x: S.Z
  {S.Z.add(x, S.Z0{}) == x : S.Z}

# LAW: x + (-x) = 0
law z_add_neg:
  for +x: S.Z
  {S.Z.add(x, S.Z.neg(x)) == S.Z0{} : S.Z}

# LAW: x * y = y * x
law z_mul_comm:
  for +x: S.Z
  for +y: S.Z
  {S.Z.mul(x, y) == S.Z.mul(y, x) : S.Z}

# LAW: (x * y) * z = x * (y * z)
law z_mul_assoc:
  for +x: S.Z
  for +y: S.Z
  for +z: S.Z
  {S.Z.mul(S.Z.mul(x, y), z) == S.Z.mul(x, S.Z.mul(y, z)) : S.Z}

# LAW: x * 1 = x
law z_mul_one:
  for +x: S.Z
  {S.Z.mul(x, S.Zpos{S.XH{}}) == x : S.Z}

# LAW: x * (y + z) = x * y + x * z
law z_mul_add:
  for +x: S.Z
  for +y: S.Z
  for +z: S.Z
  {S.Z.mul(x, S.Z.add(y, z)) == S.Z.add(S.Z.mul(x, y), S.Z.mul(x, z)) : S.Z}

# Ring identities
# ---------------

# LAW: the ring normalizer is sound: two integer expressions whose normal
# forms agree are equal under every environment. The normal forms are
# compared by computation ({==}), so this proves an identity in one step;
# R.norm itself is untrusted, only this law about it matters.
law ring_eq:
  for +env: List<&2, S.Z>
  for +e1: E.ZExpr
  for +e2: E.ZExpr
  for  h: {R.norm(e1) == R.norm(e2) : List<&2, R.ZTerm>}
  {E.eval(env, e1) == E.eval(env, e2) : S.Z}
