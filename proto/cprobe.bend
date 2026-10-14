# sk-05b probe (untrusted, not gated): completeness as an operation plus
# its law (lim/lim_ok, the way OField states inv) type-checks, and the law
# can be used twice on a constant sequence when its Cauchy proof comes from
# a def (lambda binders are single-use, so the per-index proof goes
# through a helper). A Sigma-valued limit failed: its body was a Type.

import Base
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../lib/ford.bend as FO
import ../lib/fvec.bend as FV

def nat(~F: O.OField, n: Nat) -> O.C(F):
  match n:
    case 0n:
      O.zero(F)
    case 1n+k:
      O.add(F, nat(~F, k), O.one(F))

def cauchy(~F: O.OField, s: Nat -> O.C(F), m: Nat -> Nat) -> Type:
  @k: Nat -> @a: Nat -> @b: Nat -> M.bnd(~F, O.sub(~F, s(Nat.add(m(k), a)), s(Nat.add(m(k), b))), O.inv(F, nat(~F, 1n+k)))

type Complete<-F: O.OField> is Type:
  Complete{arch: O.C(F) -> Nat,
    arch_ok: @x: O.C(F) -> O.lt(F, x, nat(~F, arch(x))),
    lim: (Nat -> O.C(F)) -> (Nat -> Nat) -> O.C(F),
    lim_ok: @s: (Nat -> O.C(F)) -> @m: (Nat -> Nat) -> cauchy(~F, s, m) -> @k: Nat -> @a: Nat -> M.bnd(~F, O.sub(~F, s(Nat.add(m(k), a)), lim(s, m)), O.inv(F, nat(~F, 1n+k)))}

def lim(-F: O.OField, R: Complete<F>) -> (Nat -> O.C(F)) -> (Nat -> Nat) -> O.C(F):
  match R:
    case Complete{arch, arch_ok, lim, lim_ok}:
      lim

def lim_ok(-F: O.OField, R: Complete<F>) -> @s: (Nat -> O.C(F)) -> @m: (Nat -> Nat) -> cauchy(~F, s, m) -> @k: Nat -> @a: Nat -> M.bnd(~F, O.sub(~F, s(Nat.add(m(k), a)), lim(F, R, s, m)), O.inv(F, nat(~F, 1n+k))):
  match R:
    case Complete{arch, arch_ok, lim, lim_ok}:
      lim_ok

# a test sequence: constant x
def cseq(~F: O.OField, +x: O.C(F)) -> Nat -> O.C(F):
  k => x

def zmod() -> Nat -> Nat:
  k => 0n

def nat_nn(~F: O.OField, n: Nat) -> O.le(~F, O.zero(F), nat(~F, n)):
  match n:
    case 0n:
      FO.le_refl(~F, O.zero(F))
    case 1n++k:
      FO.lt_le(~F, O.zero(F), nat(~F, 1n+k), FO.pos_add_r(~F, nat(~F, k), O.one(F), nat_nn(~F, k), O.zero_lt_one(F)))

def nat_pos(~F: O.OField, +k: Nat) -> O.lt(F, O.zero(F), nat(~F, 1n+k)):
  FO.pos_add_r(~F, nat(~F, k), O.one(F), nat_nn(~F, k), O.zero_lt_one(F))

def eps_nn(~F: O.OField, +k: Nat) -> O.le(~F, O.zero(F), O.inv(F, nat(~F, 1n+k))):
  FO.lt_le(~F, O.zero(F), O.inv(F, nat(~F, 1n+k)), FO.inv_pos(~F, nat(~F, 1n+k), nat_pos(~F, k)))

def ccauchy.k(~F: O.OField, +x: O.C(F), +k: Nat, a: Nat, b: Nat) -> M.bnd(~F, O.sub(~F, x, x), O.inv(F, nat(~F, 1n+k))):
  FV.bnd_sself(~F, x, O.inv(F, nat(~F, 1n+k)), eps_nn(~F, k))

def ccauchy(~F: O.OField, +x: O.C(F)) -> cauchy(~F, cseq(~F, x), zmod()):
  k => a => b => ccauchy.k(~F, x, k, a, b)

def use2(~F: O.OField, ~R: Complete<F>, +x: O.C(F)) -> M.Both(M.bnd(~F, O.sub(~F, x, lim(F, R, cseq(~F, x), zmod())), O.inv(F, nat(~F, 1n))), M.bnd(~F, O.sub(~F, x, lim(F, R, cseq(~F, x), zmod())), O.inv(F, nat(~F, 2n)))):
  (lim_ok(F, R)(cseq(~F, x), zmod(), ccauchy(~F, x), 0n, 0n), lim_ok(F, R)(cseq(~F, x), zmod(), ccauchy(~F, x), 1n, 5n))
