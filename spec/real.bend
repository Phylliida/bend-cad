# bend-cad spec: complete ordered fields (DESIGN §8.4, Q18). Trusted.
#
# A complete ordered field is an ordered field that is Archimedean (every
# element lies below some natural number) and in which every Cauchy
# sequence with a modulus converges. Up to isomorphism it is ℝ. Cauchy
# completeness alone is not enough: some non-Archimedean fields have it.
#
# Both properties are stated in Skolem form, as operations with laws, the
# way OField states inverses: arch(x) is a natural number above x, and
# lim(s, m) is the limit of a sequence s that is Cauchy with modulus m (its
# value for any other sequence is unspecified).
#
# s is Cauchy with modulus m: |s_i - s_j| <= 1/(k+1) whenever i, j >= m(k),
# written i = m(k) + a, j = m(k) + b. It then converges to its limit L with
# the same modulus: |s_i - L| <= 1/(k+1) for i >= m(k).
#
# No complete ordered field can be built in Bend (ℝ has no decidable
# order), so these axioms are checked against mathlib's ℝ in Lean
# (lean/BendCad/Axioms.lean transcribes this file and spec/field.bend and
# proves every axiom for ℝ).

import Base
import ./field.bend as O
import ./mat.bend as M

# n as 0 + 1 + ... + 1 in F
def nat(~F: O.OField, n: Nat) -> O.C(F):
  match n:
    case 0n:
      O.zero(F)
    case 1n+k:
      O.add(F, nat(~F, k), O.one(F))

# 1/(k+1)
def eps(~F: O.OField, k: Nat) -> O.C(F):
  O.inv(F, nat(~F, 1n+k))

# s is Cauchy with modulus m
def cauchy(~F: O.OField, s: Nat -> O.C(F), m: Nat -> Nat) -> Type:
  @k: Nat -> @a: Nat -> @b: Nat -> M.bnd(~F, O.sub(~F, s(Nat.add(m(k), a)), s(Nat.add(m(k), b))), eps(~F, k))

type Complete<-F: O.OField> is Type:
  Complete{arch: O.C(F) -> Nat,
    arch_ok: @x: O.C(F) -> O.lt(F, x, nat(~F, arch(x))),
    lim: (Nat -> O.C(F)) -> (Nat -> Nat) -> O.C(F),
    lim_ok: @s: (Nat -> O.C(F)) -> @m: (Nat -> Nat) -> cauchy(~F, s, m) -> @k: Nat -> @a: Nat -> M.bnd(~F, O.sub(~F, s(Nat.add(m(k), a)), lim(s, m)), eps(~F, k))}

# Accessors
# ---------

# a natural number above x
def arch(-F: O.OField, R: Complete<F>) -> O.C(F) -> Nat:
  match R:
    case Complete{arch, arch_ok, lim, lim_ok}:
      arch

def arch_ok(-F: O.OField, R: Complete<F>) -> @x: O.C(F) -> O.lt(F, x, nat(~F, arch(F, R, x))):
  match R:
    case Complete{arch, arch_ok, lim, lim_ok}:
      arch_ok

# the limit of s, Cauchy with modulus m
def lim(-F: O.OField, R: Complete<F>) -> (Nat -> O.C(F)) -> (Nat -> Nat) -> O.C(F):
  match R:
    case Complete{arch, arch_ok, lim, lim_ok}:
      lim

def lim_ok(-F: O.OField, R: Complete<F>) -> @s: (Nat -> O.C(F)) -> @m: (Nat -> Nat) -> cauchy(~F, s, m) -> @k: Nat -> @a: Nat -> M.bnd(~F, O.sub(~F, s(Nat.add(m(k), a)), lim(F, R, s, m)), eps(~F, k)):
  match R:
    case Complete{arch, arch_ok, lim, lim_ok}:
      lim_ok
