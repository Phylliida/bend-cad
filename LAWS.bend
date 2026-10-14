# bend-cad: the laws. Human-owned: this file states what "correct" means.
# PROOF.bend proves every law stated here; laws that are not proven yet live
# in ROADMAP.bend. See DESIGN.md for the plan.
#
# sk-01 (spec numbers and the ring normalizers). Trusted definitions:
# spec/num.bend (binary positives, integers, rationals and dyadics, and their
# meaning) and spec/ring.bend (ring expressions and their meaning). sk-03 and
# sk-07 (the typed sketch and what it means): spec/field.bend (ordered
# fields), spec/geom.bend (plane geometry) and spec/sketch.bend (the IR,
# exact equation forms and meanings).

import Base
import ./spec/num.bend as S
import ./spec/ring.bend as E
import ./lib/zring.bend as R
import ./lib/qring.bend as QR
import ./spec/big.bend as SB
import ./rt/big.bend as RB
import ./spec/field.bend as O
import ./spec/sketch.bend as K

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

# The order of the rationals
# --------------------------
# Q.lt (Q.cmp says LT) is a strict total order up to Q.eq; Q.eq respects
# it, and so do adding a rational and multiplying positives. With the field
# laws above: the rationals are an ordered field under Q.eq.

# LAW: x < x never holds
law q_lt_irrefl:
  for +x: S.Q
  for  h: S.Q.lt(x, x)
  Empty

# LAW: x < y and y < z give x < z
law q_lt_trans:
  for +x: S.Q
  for +y: S.Q
  for +z: S.Q
  for  h1: S.Q.lt(x, y)
  for  h2: S.Q.lt(y, z)
  S.Q.lt(x, z)

# LAW: x < y, x = y or y < x
law q_lt_total:
  for +x: S.Q
  for +y: S.Q
  Or(S.Q.lt(x, y), Or(S.Q.eq(x, y), S.Q.lt(y, x)))

# LAW: the order respects Q.eq
law q_lt_cong:
  for +x: S.Q
  for +x2: S.Q
  for +y: S.Q
  for +y2: S.Q
  for  h1: S.Q.eq(x, x2)
  for  h2: S.Q.eq(y, y2)
  for  h: S.Q.lt(x, y)
  S.Q.lt(x2, y2)

# LAW: x < y gives x + z < y + z
law q_lt_add:
  for +x: S.Q
  for +y: S.Q
  for +z: S.Q
  for  h: S.Q.lt(x, y)
  S.Q.lt(S.Q.add(x, z), S.Q.add(y, z))

# LAW: 0 < x and 0 < y give 0 < x * y
law q_lt_mul:
  for +x: S.Q
  for +y: S.Q
  for  hx: S.Q.lt(S.Q{S.Z0{}, S.XH{}}, x)
  for  hy: S.Q.lt(S.Q{S.Z0{}, S.XH{}}, y)
  S.Q.lt(S.Q{S.Z0{}, S.XH{}}, S.Q.mul(x, y))

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

# The rationals in every ordered field
# ------------------------------------
# O.ofq (spec/field.bend) sends n/d to n * (1/d) in an ordered field F. It
# is an embedding of ordered fields: it respects Q.eq and the operations,
# and it preserves and reflects the order. So an identity or inequality
# between rationals, decided by computation, holds in every ordered field,
# where the exact solution lives.

# LAW: equal rationals land on the same element
law ofq_eq:
  for ~F: O.OField
  for +x: S.Q
  for +y: S.Q
  for  h: S.Q.eq(x, y)
  {O.ofq(~F, x) == O.ofq(~F, y) : O.C(F)}

# LAW: ofq(x + y) = ofq x + ofq y
law ofq_add:
  for ~F: O.OField
  for +x: S.Q
  for +y: S.Q
  {O.ofq(~F, S.Q.add(x, y)) == O.add(F, O.ofq(~F, x), O.ofq(~F, y)) : O.C(F)}

# LAW: ofq(x * y) = ofq x * ofq y
law ofq_mul:
  for ~F: O.OField
  for +x: S.Q
  for +y: S.Q
  {O.ofq(~F, S.Q.mul(x, y)) == O.mul(F, O.ofq(~F, x), O.ofq(~F, y)) : O.C(F)}

# LAW: ofq(-x) = -ofq x
law ofq_neg:
  for ~F: O.OField
  for +x: S.Q
  {O.ofq(~F, S.Q.neg(x)) == O.neg(F, O.ofq(~F, x)) : O.C(F)}

# LAW: ofq 0 = 0
law ofq_zero:
  for ~F: O.OField
  {O.ofq(~F, S.Q{S.Z0{}, S.XH{}}) == O.zero(F) : O.C(F)}

# LAW: ofq 1 = 1
law ofq_one:
  for ~F: O.OField
  {O.ofq(~F, S.Q{S.Zpos{S.XH{}}, S.XH{}}) == O.one(F) : O.C(F)}

# LAW: x < y gives ofq x < ofq y
law ofq_lt:
  for ~F: O.OField
  for +x: S.Q
  for +y: S.Q
  for  h: S.Q.lt(x, y)
  O.lt(F, O.ofq(~F, x), O.ofq(~F, y))

# LAW: ofq x < ofq y gives x < y
law ofq_lt_rev:
  for ~F: O.OField
  for +x: S.Q
  for +y: S.Q
  for +h: O.lt(F, O.ofq(~F, x), O.ofq(~F, y))
  S.Q.lt(x, y)

# LAW: ofq x = ofq y gives x = y
law ofq_eq_rev:
  for ~F: O.OField
  for +x: S.Q
  for +y: S.Q
  for +e: {O.ofq(~F, x) == O.ofq(~F, y) : O.C(F)}
  S.Q.eq(x, y)

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

# Big integers (sk-02)
# --------------------
# A runtime big integer is a signed list of limbs in base 1 + bp (65536 at
# runtime), least significant first; SB.Big.val is the integer it means, and
# SB.Big.wf says every limb is below the base. The laws hold for every base
# (the checker would unfold a literal 65536n to unary). With well-formed
# inputs every intermediate stays below B * B + B, far under the runtime's
# 2^48 Nat cap.

# LAW: runtime addition is integer addition
law big_add:
  for +bp: Nat
  for +a: SB.Big
  for +b: SB.Big
  for  wa: SB.Big.wf(bp, a)
  for  wb: SB.Big.wf(bp, b)
  {SB.Big.val(bp, RB.Big.add(bp, a, b)) == S.Z.add(SB.Big.val(bp, a), SB.Big.val(bp, b)) : S.Z}

# LAW: runtime subtraction is integer subtraction
law big_sub:
  for +bp: Nat
  for +a: SB.Big
  for +b: SB.Big
  for  wa: SB.Big.wf(bp, a)
  for  wb: SB.Big.wf(bp, b)
  {SB.Big.val(bp, RB.Big.sub(bp, a, b)) == S.Z.sub(SB.Big.val(bp, a), SB.Big.val(bp, b)) : S.Z}

# LAW: runtime negation is integer negation
law big_neg:
  for +bp: Nat
  for +a: SB.Big
  {SB.Big.val(bp, RB.Big.neg(a)) == S.Z.neg(SB.Big.val(bp, a)) : S.Z}

# LAW: runtime multiplication is integer multiplication
law big_mul:
  for +bp: Nat
  for +a: SB.Big
  for +b: SB.Big
  {SB.Big.val(bp, RB.Big.mul(bp, a, b)) == S.Z.mul(SB.Big.val(bp, a), SB.Big.val(bp, b)) : S.Z}

# LAW: runtime comparison is integer comparison (base at least 2)
law big_cmp:
  for +bp: Nat
  for +a: SB.Big
  for +b: SB.Big
  for  hb: SB.Le(1n, bp)
  for  wa: SB.Big.wf(bp, a)
  for  wb: SB.Big.wf(bp, b)
  {RB.Big.cmp(bp, a, b) == S.Z.cmp(SB.Big.val(bp, a), SB.Big.val(bp, b)) : Cmp}

# LAW: sums of well-formed big integers are well-formed (base at least 2)
law big_add_wf:
  for +bp: Nat
  for +a: SB.Big
  for +b: SB.Big
  for  hb: SB.Le(1n, bp)
  for  wa: SB.Big.wf(bp, a)
  for  wb: SB.Big.wf(bp, b)
  SB.Big.wf(bp, RB.Big.add(bp, a, b))

# LAW: differences of well-formed big integers are well-formed
law big_sub_wf:
  for +bp: Nat
  for +a: SB.Big
  for +b: SB.Big
  for  hb: SB.Le(1n, bp)
  for  wa: SB.Big.wf(bp, a)
  for  wb: SB.Big.wf(bp, b)
  SB.Big.wf(bp, RB.Big.sub(bp, a, b))

# LAW: negations of well-formed big integers are well-formed
law big_neg_wf:
  for +bp: Nat
  for +a: SB.Big
  for  wa: SB.Big.wf(bp, a)
  SB.Big.wf(bp, RB.Big.neg(a))

# LAW: products of well-formed big integers are well-formed
law big_mul_wf:
  for +bp: Nat
  for +a: SB.Big
  for +b: SB.Big
  for  hb: SB.Le(1n, bp)
  for  wa: SB.Big.wf(bp, a)
  for  wb: SB.Big.wf(bp, b)
  SB.Big.wf(bp, RB.Big.mul(bp, a, b))

# Meaning lemmas (stated in sk-03, proven in sk-07; DESIGN §5.5)
# --------------------------------------------------------------
# In every ordered field F (so in the reals, where a sketch's exact solution
# lives), for every assignment env of values to the variables: a
# constraint's exact equations vanish and its side conditions are positive
# exactly when it means what it says (K.Constraint.means, one case per kind,
# in the vocabulary of spec/geom.bend). Merge kinds need their variable
# sharing (wf). F is a template parameter: the proofs see its operations
# only through the ordered-field axioms (spec/field.bend).

# LAW: the exact form implies the meaning
law means_sound:
  for ~F: O.OField
  for +env: List<&2, O.C(F)>
  for +es: List<&2, K.Ent>
  for +k: K.Constraint
  for  w: K.Constraint.wf(es, k)
  for  h: K.Constraint.holds(~F, env, es, k)
  K.Constraint.means(~F, env, es, k)

# LAW: the meaning implies the exact form (the form asks for nothing more)
law means_complete:
  for ~F: O.OField
  for +env: List<&2, O.C(F)>
  for +es: List<&2, K.Ent>
  for +k: K.Constraint
  for  h: K.Constraint.means(~F, env, es, k)
  K.Constraint.holds(~F, env, es, k)

# LAW: an entity's side conditions hold exactly when it is proper
law ent_sound:
  for ~F: O.OField
  for +env: List<&2, O.C(F)>
  for +e: K.Ent
  for  h: K.Ent.holds(~F, env, e)
  K.Ent.means(~F, env, e)

# LAW: a proper entity satisfies its side conditions
law ent_complete:
  for ~F: O.OField
  for +env: List<&2, O.C(F)>
  for +e: K.Ent
  for  h: K.Ent.means(~F, env, e)
  K.Ent.holds(~F, env, e)

# LAW: a solution of a well-formed sketch's exact system (F = 0, every side
# condition positive) is a sketch where every circle and arc is proper and
# every driving constraint means what it says
law sketch_sound:
  for ~F: O.OField
  for +env: List<&2, O.C(F)>
  for +sk: K.Sketch
  for  w: K.Sketch.wf(sk)
  for  h: K.Sketch.holds(~F, env, sk)
  K.Sketch.means(~F, env, sk)

# LAW: and conversely
law sketch_complete:
  for ~F: O.OField
  for +env: List<&2, O.C(F)>
  for +sk: K.Sketch
  for  h: K.Sketch.means(~F, env, sk)
  K.Sketch.holds(~F, env, sk)
