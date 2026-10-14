# bend-cad: the laws. Human-owned: this file states what "correct" means.
# PROOF.bend proves every law stated here; laws that are not proven yet live
# in ROADMAP.bend. See DESIGN.md for the plan.
#
# sk-01 (spec numbers and the ring normalizers). Trusted definitions:
# spec/num.bend (binary positives, integers, rationals and dyadics, and their
# meaning) and spec/ring.bend (ring expressions and their meaning).

import Base
import ./spec/num.bend as S
import ./spec/ring.bend as E
import ./lib/zring.bend as R
import ./lib/qring.bend as QR

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

# LAW: binary comparison is comparison
law pos_cmp:
  for +a: S.Pos
  for +b: S.Pos
  {S.Pos.cmp(a, b) == Nat.cmp(S.Pos.nat(a), S.Pos.nat(b)) : Cmp}

# LAW: x compares with y as pnat x + nnat y with pnat y + nnat x
law z_cmp:
  for +x: S.Z
  for +y: S.Z
  {S.Z.cmp(x, y) == Nat.cmp(Nat.add(S.Z.pnat(x), S.Z.nnat(y)), Nat.add(S.Z.pnat(y), S.Z.nnat(x))) : Cmp}

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

# Rationals
# ---------
# A rational is an integer over a positive, unreduced; Q.eq (cross-
# multiplication) is its equality. It is an equivalence, the operations
# respect it, and the rationals are a field under it.

# LAW: Q.eq is reflexive
law q_refl:
  for +x: S.Q
  S.Q.eq(x, x)

# LAW: Q.eq is symmetric
law q_sym:
  for +x: S.Q
  for +y: S.Q
  for  h: S.Q.eq(x, y)
  S.Q.eq(y, x)

# LAW: Q.eq is transitive
law q_trans:
  for +x: S.Q
  for +y: S.Q
  for +z: S.Q
  for  h1: S.Q.eq(x, y)
  for  h2: S.Q.eq(y, z)
  S.Q.eq(x, z)

# LAW: addition respects Q.eq
law q_add_cong:
  for +x: S.Q
  for +x2: S.Q
  for +y: S.Q
  for +y2: S.Q
  for  h1: S.Q.eq(x, x2)
  for  h2: S.Q.eq(y, y2)
  S.Q.eq(S.Q.add(x, y), S.Q.add(x2, y2))

# LAW: multiplication respects Q.eq
law q_mul_cong:
  for +x: S.Q
  for +x2: S.Q
  for +y: S.Q
  for +y2: S.Q
  for  h1: S.Q.eq(x, x2)
  for  h2: S.Q.eq(y, y2)
  S.Q.eq(S.Q.mul(x, y), S.Q.mul(x2, y2))

# LAW: negation respects Q.eq
law q_neg_cong:
  for +x: S.Q
  for +x2: S.Q
  for  h: S.Q.eq(x, x2)
  S.Q.eq(S.Q.neg(x), S.Q.neg(x2))

# LAW: x + y = y + x
law q_add_comm:
  for +x: S.Q
  for +y: S.Q
  S.Q.eq(S.Q.add(x, y), S.Q.add(y, x))

# LAW: (x + y) + z = x + (y + z)
law q_add_assoc:
  for +x: S.Q
  for +y: S.Q
  for +z: S.Q
  S.Q.eq(S.Q.add(S.Q.add(x, y), z), S.Q.add(x, S.Q.add(y, z)))

# LAW: x + 0 = x
law q_add_zero:
  for +x: S.Q
  S.Q.eq(S.Q.add(x, S.Q{S.Z0{}, S.XH{}}), x)

# LAW: x + (-x) = 0
law q_add_neg:
  for +x: S.Q
  S.Q.eq(S.Q.add(x, S.Q.neg(x)), S.Q{S.Z0{}, S.XH{}})

# LAW: x * y = y * x
law q_mul_comm:
  for +x: S.Q
  for +y: S.Q
  S.Q.eq(S.Q.mul(x, y), S.Q.mul(y, x))

# LAW: (x * y) * z = x * (y * z)
law q_mul_assoc:
  for +x: S.Q
  for +y: S.Q
  for +z: S.Q
  S.Q.eq(S.Q.mul(S.Q.mul(x, y), z), S.Q.mul(x, S.Q.mul(y, z)))

# LAW: x * 1 = x
law q_mul_one:
  for +x: S.Q
  S.Q.eq(S.Q.mul(x, S.Q{S.Zpos{S.XH{}}, S.XH{}}), x)

# LAW: x * (y + z) = x * y + x * z
law q_mul_add:
  for +x: S.Q
  for +y: S.Q
  for +z: S.Q
  S.Q.eq(S.Q.mul(x, S.Q.add(y, z)), S.Q.add(S.Q.mul(x, y), S.Q.mul(x, z)))

# LAW: x * (1/x) = 1 for x other than 0
law q_mul_inv:
  for x: S.Q
  for h: S.Q.eq(x, S.Q{S.Z0{}, S.XH{}}) -> Empty
  S.Q.eq(S.Q.mul(x, S.Q.inv(x)), S.Q{S.Zpos{S.XH{}}, S.XH{}})

# LAW: the rational normalizer is sound: two rational expressions whose
# cross-multiplied integer forms normalize alike are the same rational under
# every environment. QR.trn and QR.trd (numerator and denominator) are
# untrusted, like R.norm.
law qring_eq:
  for +env: List<&2, S.Q>
  for +e1: E.QExpr
  for +e2: E.QExpr
  for  h: {R.norm(E.ZMul{QR.trn(e1), QR.trd(e2)}) == R.norm(E.ZMul{QR.trn(e2), QR.trd(e1)}) : List<&2, R.ZTerm>}
  S.Q.eq(E.qeval(env, e1), E.qeval(env, e2))

# Dyadics
# -------
# A dyadic m/2^e means the rational D.toq; its operations are the rational
# ones.

# LAW: dyadic addition is rational addition
law d_add:
  for +x: S.D
  for +y: S.D
  S.Q.eq(S.D.toq(S.D.add(x, y)), S.Q.add(S.D.toq(x), S.D.toq(y)))

# LAW: dyadic multiplication is rational multiplication
law d_mul:
  for +x: S.D
  for +y: S.D
  S.Q.eq(S.D.toq(S.D.mul(x, y)), S.Q.mul(S.D.toq(x), S.D.toq(y)))

# LAW: dyadic negation is rational negation
law d_neg:
  for +x: S.D
  S.Q.eq(S.D.toq(S.D.neg(x)), S.Q.neg(S.D.toq(x)))
