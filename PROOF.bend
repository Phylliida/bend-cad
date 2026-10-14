# bend-cad: the proofs of every law in LAWS.bend. Each delegates to the
# library (lib/), where the proofs live; the ring laws are one call each to
# the normalizer they are stated beside.

import Base
import ./LAWS.bend as Laws
import ./spec/num.bend as S
import ./spec/ring.bend as E
import ./lib/pos.bend as P
import ./lib/z.bend as LZ
import ./lib/zring.bend as R

# Positives
# ---------

def Laws.pos_add(a, b):
  Equal.sym(Nat, Nat.add(S.Pos.nat(a), S.Pos.nat(b)), S.Pos.nat(S.Pos.add(a, b)), P.add_nat(a, b))

def Laws.pos_mul(a, b):
  Equal.sym(Nat, Nat.mul(S.Pos.nat(a), S.Pos.nat(b)), S.Pos.nat(S.Pos.mul(a, b)), P.mul_nat(a, b))

def Laws.pos_inj(a, b, e):
  P.nat_inj(a, b, e)

def Laws.pos_of_succ(n):
  Equal.sym(Nat, 1n+n, S.Pos.nat(S.Pos.of_succ(n)), P.nat_os(n))

# Integers
# --------

def Laws.z_parts(x):
  LZ.diff_parts(x)

def Laws.z_pnat(a, b):
  Equal.sym(Nat, Nat.sub(a, b), S.Z.pnat(S.Z.of_diff(a, b)), LZ.sub_pnat(a, b))

def Laws.z_nnat(a, b):
  Equal.sym(Nat, Nat.sub(b, a), S.Z.nnat(S.Z.of_diff(a, b)), LZ.sub_nnat(a, b))

def Laws.z_add(a, b, c, d):
  Equal.sym(S.Z, S.Z.of_diff(Nat.add(a, c), Nat.add(b, d)), S.Z.add(S.Z.of_diff(a, b), S.Z.of_diff(c, d)), LZ.add_hom(a, b, c, d))

def Laws.z_mul(a, b, c, d):
  Equal.sym(S.Z, S.Z.of_diff(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), Nat.add(Nat.mul(a, d), Nat.mul(b, c))), S.Z.mul(S.Z.of_diff(a, b), S.Z.of_diff(c, d)), LZ.mul_hom(a, b, c, d))

def Laws.z_neg(a, b):
  Equal.sym(S.Z, S.Z.of_diff(b, a), S.Z.neg(S.Z.of_diff(a, b)), LZ.neg_diff(a, b))

# Ring identities
# ---------------

def Laws.ring_eq(env, e1, e2, h):
  R.ring_eq(env, e1, e2, h)

# The commutative ring laws, each one normalizer call.

def Laws.z_add_comm(x, y):
  Laws.ring_eq([x, y], E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZAdd{E.ZVar{1n}, E.ZVar{0n}}, {==})

def Laws.z_add_assoc(x, y, z):
  Laws.ring_eq([x, y, z], E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZAdd{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}, {==})

def Laws.z_add_zero(x):
  Laws.ring_eq([x], E.ZAdd{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZVar{0n}, {==})

def Laws.z_add_neg(x):
  Laws.ring_eq([x], E.ZAdd{E.ZVar{0n}, E.ZNeg{E.ZVar{0n}}}, E.ZCst{S.Z0{}}, {==})

def Laws.z_mul_comm(x, y):
  Laws.ring_eq([x, y], E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{1n}, E.ZVar{0n}}, {==})

def Laws.z_mul_assoc(x, y, z):
  Laws.ring_eq([x, y, z], E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, {==})

def Laws.z_mul_one(x):
  Laws.ring_eq([x], E.ZMul{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{0n}, {==})

def Laws.z_mul_add(x, y, z):
  Laws.ring_eq([x, y, z], E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, {==})
