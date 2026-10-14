# Analysis in a complete ordered field (spec/real.bend): powers of a
# factor below 1 fall under every 1/(k+1) (Bernoulli's inequality and the
# Archimedean property), and a limit keeps every closed bound its sequence
# keeps. Untrusted: proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/real.bend as CR
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./fmat.bend as FM
import ./dmat.bend as DM
import ./qemb.bend as QE
import ./fvec.bend as FV
import ./nat.bend as LN

# Order helpers
# -------------

def nat_nn(~F: O.OField, n: Nat) -> O.le(~F, O.zero(F), CR.nat(~F, n)):
  match n:
    case 0n:
      FO.le_refl(~F, O.zero(F))
    case 1n++k:
      FO.lt_le(~F, O.zero(F), CR.nat(~F, 1n+k), FO.pos_add_r(~F, CR.nat(~F, k), O.one(F), nat_nn(~F, k), O.zero_lt_one(F)))

# 0 < k + 1
def nat_pos(~F: O.OField, +k: Nat) -> O.lt(F, O.zero(F), CR.nat(~F, 1n+k)):
  FO.pos_add_r(~F, CR.nat(~F, k), O.one(F), nat_nn(~F, k), O.zero_lt_one(F))

def eps_pos(~F: O.OField, +k: Nat) -> O.lt(F, O.zero(F), CR.eps(~F, k)):
  FO.inv_pos(~F, CR.nat(~F, 1n+k), nat_pos(~F, k))

# a < b gives 0 < b - a
def sub_pos(~F: O.OField, +a: O.C(F), +b: O.C(F), h: O.lt(F, a, b)) -> O.lt(F, O.zero(F), O.sub(~F, b, a)):
  FO.lt_subst_l(~F, O.add(F, a, O.neg(F, a)), O.zero(F), O.add(F, b, O.neg(F, a)), O.add_neg(F)(a), O.lt_add(F)(a, b, O.neg(F, a), h))

# a c < b c, for a < b and 0 < c
def lt_mul_r(~F: O.OField, +a: O.C(F), +b: O.C(F), +c: O.C(F), h: O.lt(F, a, b), hc: O.lt(F, O.zero(F), c)) -> O.lt(F, O.mul(F, a, c), O.mul(F, b, c)):
  QE.lt_of_sub(~F, O.mul(F, a, c), O.mul(F, b, c), FO.lt_subst_r(~F, O.mul(F, c, O.sub(~F, b, a)), O.sub(~F, O.mul(F, b, c), O.mul(F, a, c)), O.zero(F), FR.fring_eq(~F, [a, b, c], E.ZMul{E.ZVar{2n}, E.ZSub{E.ZVar{1n}, E.ZVar{0n}}}, E.ZSub{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, {==}), O.lt_mul(F)(c, O.sub(~F, b, a), hc, sub_pos(~F, a, b, h))))

def le_rw_l(~F: O.OField, +a: O.C(F), +a2: O.C(F), +b: O.C(F), e: {a == a2 : O.C(F)}, h: O.le(~F, a, b)) -> O.le(~F, a2, b):
  %e : O.le(~F, _, b)
  h

def lt_rw_l(~F: O.OField, +a: O.C(F), +a2: O.C(F), +b: O.C(F), e: {a == a2 : O.C(F)}, h: O.lt(F, a, b)) -> O.lt(F, a2, b):
  %e : O.lt(F, _, b)
  h

def lt_rw_r(~F: O.OField, +a: O.C(F), +b: O.C(F), +b2: O.C(F), e: {b == b2 : O.C(F)}, h: O.lt(F, a, b)) -> O.lt(F, a, b2):
  %e : O.lt(F, a, _)
  h

# a ≤ b from b - a = s and 0 ≤ s
def le_by(~F: O.OField, +a: O.C(F), +b: O.C(F), +s: O.C(F), e: {s == O.sub(~F, b, a) : O.C(F)}, h: O.le(~F, O.zero(F), s)) -> O.le(~F, a, b):
  FV.le_of_sub(~F, a, b, FM.nn_eq(~F, O.sub(~F, b, a), s, e, h))

def nn_by.go(~F: O.OField, +t: O.C(F), contra: O.lt(F, t, O.zero(F)) -> Empty, u: Or(O.lt(F, t, O.zero(F)), Or({t == O.zero(F) : O.C(F)}, O.lt(F, O.zero(F), t)))) -> O.le(~F, O.zero(F), t):
  match u:
    case Inl{l}:
      FO.absurd(O.le(~F, O.zero(F), t), contra(l))
    case Inr{Inl{e}}:
      Inr{Equal.sym(O.C(F), t, O.zero(F), e)}
    case Inr{Inr{g}}:
      Inl{g}

# 0 ≤ t, since t < 0 is absurd
def nn_by(~F: O.OField, +t: O.C(F), contra: O.lt(F, t, O.zero(F)) -> Empty) -> O.le(~F, O.zero(F), t):
  nn_by.go(~F, t, contra, O.lt_total(F)(t, O.zero(F)))

# d ≤ δ and δ < d are absurd
def le_lt_absurd(~F: O.OField, +d: O.C(F), +dl: O.C(F), h1: O.le(~F, d, dl), h2: O.lt(F, dl, d)) -> Empty:
  O.lt_irrefl(F)(d, FO.le_lt_trans(~F, d, dl, d, h1, h2))

# Powers
# ------

# q^k
def pw(~F: O.OField, +q: O.C(F), k: Nat) -> O.C(F):
  match k:
    case 0n:
      O.one(F)
    case 1n+j:
      O.mul(F, pw(~F, q, j), q)

def pw_nn(~F: O.OField, +q: O.C(F), +hq: O.le(~F, O.zero(F), q), k: Nat) -> O.le(~F, O.zero(F), pw(~F, q, k)):
  match k:
    case 0n:
      FO.lt_le(~F, O.zero(F), O.one(F), O.zero_lt_one(F))
    case 1n++j:
      FO.mul_nonneg(~F, pw(~F, q, j), q, pw_nn(~F, q, hq, j), hq)

# Bernoulli: q^k (1 + k (1 - q)) ≤ 1, for 0 ≤ q
def bern(~F: O.OField, +q: O.C(F), +hq: O.le(~F, O.zero(F), q), k: Nat) -> O.le(~F, O.mul(F, pw(~F, q, k), O.add(F, O.one(F), O.mul(F, CR.nat(~F, k), O.sub(~F, O.one(F), q)))), O.one(F)):
  match k:
    case 0n:
      Inr{FR.fring_eq(~F, [q], E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZCst{S.Z0{}}, E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}}}}, E.ZCst{S.Zpos{S.XH{}}}, {==})}
    case 1n++j:
      +p = pw(~F, q, j)
      +n = CR.nat(~F, j)
      +u = O.sub(~F, O.one(F), q)
      +x = O.mul(F, p, O.add(F, O.one(F), O.mul(F, n, u)))
      +y = O.mul(F, O.mul(F, p, q), O.add(F, O.one(F), O.mul(F, O.add(F, n, O.one(F)), u)))
      +sl = O.mul(F, O.mul(F, p, O.mul(F, u, u)), O.add(F, n, O.one(F)))
      +eu = {E.ZSub{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{1n}} : E.ZExpr}
      DM.le_trans(~F, y, x, O.one(F),
        le_by(~F, y, x, sl, FR.fring_eq(~F, [p, q, n], E.ZMul{E.ZMul{E.ZVar{0n}, E.ZMul{eu, eu}}, E.ZAdd{E.ZVar{2n}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZVar{2n}, eu}}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZAdd{E.ZVar{2n}, E.ZCst{S.Zpos{S.XH{}}}}, eu}}}}, {==}),
          FO.mul_nonneg(~F, O.mul(F, p, O.mul(F, u, u)), O.add(F, n, O.one(F)), FO.mul_nonneg(~F, p, O.mul(F, u, u), pw_nn(~F, q, hq, j), FO.sq_nonneg(~F, u)), nat_nn(~F, 1n+j))),
        bern(~F, q, hq, j))

# Small powers
# ------------

# 1/(k+1) < d, for 0 < d and k above 1/d
def eps_lt(~F: O.OField, ~R: CR.Complete<F>, +d: O.C(F), +hd: O.lt(F, O.zero(F), d)) -> O.lt(F, CR.eps(~F, CR.arch(F, R, O.inv(F, d))), d):
  +kk = CR.arch(F, R, O.inv(F, d))
  +nk = CR.nat(~F, 1n+kk)
  +h1 = CR.arch_ok(F, R)(O.inv(F, d))
  +hk = QE.lt_of_sub(~F, CR.nat(~F, kk), nk, FO.lt_subst_r(~F, O.one(F), O.sub(~F, nk, CR.nat(~F, kk)), O.zero(F), FR.fring_eq(~F, [CR.nat(~F, kk)], E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{0n}}, {==}), O.zero_lt_one(F)))
  +h2 = O.lt_trans(F)(O.inv(F, d), CR.nat(~F, kk), nk, h1, hk)
  +e1 = Equal.trans(O.C(F), O.mul(F, O.inv(F, d), d), O.mul(F, d, O.inv(F, d)), O.one(F), O.mul_comm(F)(O.inv(F, d), d), O.mul_inv(F)(d, FO.ne_of_gt(~F, d, O.zero(F), hd)))
  +h3 = lt_rw_l(~F, O.mul(F, O.inv(F, d), d), O.one(F), O.mul(F, nk, d), e1, lt_mul_r(~F, O.inv(F, d), nk, d, h2, hd))
  +h4 = lt_mul_r(~F, O.one(F), O.mul(F, nk, d), O.inv(F, nk), h3, FO.inv_pos(~F, nk, nat_pos(~F, kk)))
  +e2 = FR.fring_eq(~F, [O.inv(F, nk)], E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, E.ZVar{0n}, {==})
  +e3 = Equal.trans(O.C(F), O.mul(F, O.mul(F, nk, d), O.inv(F, nk)), O.mul(F, O.mul(F, d, O.inv(F, nk)), nk), d, FR.fring_eq(~F, [nk, d, O.inv(F, nk)], E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZMul{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{0n}}, {==}), FV.inv_cancel(~F, d, nk, nat_pos(~F, kk)))
  lt_rw_r(~F, O.inv(F, nk), O.mul(F, O.mul(F, nk, d), O.inv(F, nk)), d, e3, lt_rw_l(~F, O.mul(F, O.one(F), O.inv(F, nk)), O.inv(F, nk), O.mul(F, O.mul(F, nk, d), O.inv(F, nk)), e2, h4))

# how far to go so that q^m c ≤ 1/(k+1)
def mk(~F: O.OField, ~R: CR.Complete<F>, +q: O.C(F), +c: O.C(F), +k: Nat) -> Nat:
  CR.arch(F, R, O.mul(F, O.mul(F, c, CR.nat(~F, 1n+k)), O.inv(F, O.sub(~F, O.one(F), q))))

# q^m c ≤ 1/(k+1) for m = mk(q, c, k), when 0 ≤ q < 1 and 0 ≤ c
def small(~F: O.OField, ~R: CR.Complete<F>, +q: O.C(F), +hq0: O.le(~F, O.zero(F), q), +hq1: O.lt(F, q, O.one(F)), +c: O.C(F), +hc: O.le(~F, O.zero(F), c), +k: Nat) -> O.le(~F, O.mul(F, pw(~F, q, mk(~F, ~R, q, c, k)), c), CR.eps(~F, k)):
  +m = mk(~F, ~R, q, c, k)
  +nn = CR.nat(~F, 1n+k)
  +u = O.sub(~F, O.one(F), q)
  +a = O.mul(F, O.mul(F, c, nn), O.inv(F, u))
  +p = pw(~F, q, m)
  +nm = CR.nat(~F, m)
  +cn = O.mul(F, c, nn)
  +hu = sub_pos(~F, q, O.one(F), hq1)
  +h3 = lt_rw_l(~F, O.mul(F, a, u), cn, O.mul(F, nm, u), FV.inv_cancel(~F, cn, u, hu), lt_mul_r(~F, a, nm, u, CR.arch_ok(F, R)(a), hu))
  +h4 = le_by(~F, O.mul(F, p, O.mul(F, nm, u)), O.mul(F, p, O.add(F, O.one(F), O.mul(F, nm, u))), p, FR.fring_eq(~F, [p, nm, u], E.ZVar{0n}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}, {==}), pw_nn(~F, q, hq0, m))
  +h5 = FV.mul_le(~F, p, cn, O.mul(F, nm, u), pw_nn(~F, q, hq0, m), FO.lt_le(~F, cn, O.mul(F, nm, u), h3))
  +h6 = DM.le_trans(~F, O.mul(F, p, cn), O.mul(F, p, O.mul(F, nm, u)), O.one(F), h5, DM.le_trans(~F, O.mul(F, p, O.mul(F, nm, u)), O.mul(F, p, O.add(F, O.one(F), O.mul(F, nm, u))), O.one(F), h4, bern(~F, q, hq0, m)))
  +h7 = FV.mul_le_r(~F, O.mul(F, p, cn), O.one(F), O.inv(F, nn), FO.lt_le(~F, O.zero(F), O.inv(F, nn), FO.inv_pos(~F, nn, nat_pos(~F, k))), h6)
  +e1 = Equal.trans(O.C(F), O.mul(F, O.mul(F, p, cn), O.inv(F, nn)), O.mul(F, O.mul(F, O.mul(F, p, c), O.inv(F, nn)), nn), O.mul(F, p, c), FR.fring_eq(~F, [p, c, nn, O.inv(F, nn)], E.ZMul{E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZVar{3n}}, E.ZMul{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{3n}}, E.ZVar{2n}}, {==}), FV.inv_cancel(~F, O.mul(F, p, c), nn, nat_pos(~F, k)))
  +e2 = FR.fring_eq(~F, [O.inv(F, nn)], E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, E.ZVar{0n}, {==})
  FV.le_rw_r(~F, O.mul(F, p, c), O.mul(F, O.one(F), O.inv(F, nn)), O.inv(F, nn), e2, le_rw_l(~F, O.mul(F, O.mul(F, p, cn), O.inv(F, nn)), O.mul(F, p, c), O.mul(F, O.one(F), O.inv(F, nn)), e1, h7))

# Closed bounds pass to the limit
# -------------------------------

def swap_ix(~F: O.OField, ~s: Nat -> O.C(F), +k: Nat, +mk0: Nat, +x: O.C(F), +e: O.C(F), h: M.bnd(~F, O.sub(~F, s(Nat.add(k, mk0)), x), e)) -> M.bnd(~F, O.sub(~F, s(Nat.add(mk0, k)), x), e):
  %LN.add_comm(k, mk0) : M.bnd(~F, O.sub(~F, s(_), x), e)
  h

# upper half: from |s_t - L| ≤ δ and |s_t - x| ≤ e, L - x ≤ e + δ, against δ < e's excess d
def close1.fin(~F: O.OField, +dl: O.C(F), +l: O.C(F), +x: O.C(F), +e: O.C(F), +st: O.C(F), hc: M.bnd(~F, O.sub(~F, st, l), dl), hxx: M.bnd(~F, O.sub(~F, st, x), e), hlt: O.lt(F, dl, O.neg(F, O.sub(~F, e, O.sub(~F, l, x))))) -> Empty:
  (hc1, hc2) = hc
  (hx1, hx2) = hxx
  +d = O.neg(F, O.sub(~F, e, O.sub(~F, l, x)))
  le_lt_absurd(~F, d, dl, le_by(~F, d, dl, O.add(F, O.add(F, dl, O.sub(~F, st, l)), O.sub(~F, e, O.sub(~F, st, x))), FR.fring_eq(~F, [dl, l, x, e, st], E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZSub{E.ZVar{4n}, E.ZVar{1n}}}, E.ZSub{E.ZVar{3n}, E.ZSub{E.ZVar{4n}, E.ZVar{2n}}}}, E.ZSub{E.ZVar{0n}, E.ZNeg{E.ZSub{E.ZVar{3n}, E.ZSub{E.ZVar{1n}, E.ZVar{2n}}}}}, {==}), FO.nonneg_add(~F, O.add(F, dl, O.sub(~F, st, l)), O.sub(~F, e, O.sub(~F, st, x)), hc2, hx1)), hlt)

# lower half: x - L ≤ e + δ, against δ < e's excess d
def close2.fin(~F: O.OField, +dl: O.C(F), +l: O.C(F), +x: O.C(F), +e: O.C(F), +st: O.C(F), hc: M.bnd(~F, O.sub(~F, st, l), dl), hxx: M.bnd(~F, O.sub(~F, st, x), e), hlt: O.lt(F, dl, O.neg(F, O.add(F, e, O.sub(~F, l, x))))) -> Empty:
  (hc1, hc2) = hc
  (hx1, hx2) = hxx
  +d = O.neg(F, O.add(F, e, O.sub(~F, l, x)))
  le_lt_absurd(~F, d, dl, le_by(~F, d, dl, O.add(F, O.sub(~F, dl, O.sub(~F, st, l)), O.add(F, e, O.sub(~F, st, x))), FR.fring_eq(~F, [dl, l, x, e, st], E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZSub{E.ZVar{4n}, E.ZVar{1n}}}, E.ZAdd{E.ZVar{3n}, E.ZSub{E.ZVar{4n}, E.ZVar{2n}}}}, E.ZSub{E.ZVar{0n}, E.ZNeg{E.ZAdd{E.ZVar{3n}, E.ZSub{E.ZVar{1n}, E.ZVar{2n}}}}}, {==}), FO.nonneg_add(~F, O.sub(~F, dl, O.sub(~F, st, l)), O.add(F, e, O.sub(~F, st, x)), hc1, hx2)), hlt)

def close1(~F: O.OField, ~R: CR.Complete<F>, ~s: Nat -> O.C(F), ~m: Nat -> Nat, ~h: CR.cauchy(~F, s, m), ~k: Nat, ~x: O.C(F), ~e: O.C(F), ~hx: @j: Nat -> M.bnd(~F, O.sub(~F, s(Nat.add(k, j)), x), e), l: O.lt(F, O.sub(~F, e, O.sub(~F, CR.lim(F, R, s, m), x)), O.zero(F))) -> Empty:
  +lm = CR.lim(F, R, s, m)
  +d = O.neg(F, O.sub(~F, e, O.sub(~F, lm, x)))
  +hd = FO.neg_pos(~F, O.sub(~F, e, O.sub(~F, lm, x)), l)
  +kk = CR.arch(F, R, O.inv(F, d))
  +mk0 = m(kk)
  close1.fin(~F, CR.eps(~F, kk), lm, x, e, s(Nat.add(mk0, k)), CR.lim_ok(F, R)(s, m, h, kk, k), swap_ix(~F, ~s, k, mk0, x, e, hx(mk0)), eps_lt(~F, ~R, d, hd))

def close2(~F: O.OField, ~R: CR.Complete<F>, ~s: Nat -> O.C(F), ~m: Nat -> Nat, ~h: CR.cauchy(~F, s, m), ~k: Nat, ~x: O.C(F), ~e: O.C(F), ~hx: @j: Nat -> M.bnd(~F, O.sub(~F, s(Nat.add(k, j)), x), e), l: O.lt(F, O.add(F, e, O.sub(~F, CR.lim(F, R, s, m), x)), O.zero(F))) -> Empty:
  +lm = CR.lim(F, R, s, m)
  +d = O.neg(F, O.add(F, e, O.sub(~F, lm, x)))
  +hd = FO.neg_pos(~F, O.add(F, e, O.sub(~F, lm, x)), l)
  +kk = CR.arch(F, R, O.inv(F, d))
  +mk0 = m(kk)
  close2.fin(~F, CR.eps(~F, kk), lm, x, e, s(Nat.add(mk0, k)), CR.lim_ok(F, R)(s, m, h, kk, k), swap_ix(~F, ~s, k, mk0, x, e, hx(mk0)), eps_lt(~F, ~R, d, hd))

# |s_(k+j) - x| ≤ e for every j gives |lim s - x| ≤ e
def close(~F: O.OField, ~R: CR.Complete<F>, ~s: Nat -> O.C(F), ~m: Nat -> Nat, ~h: CR.cauchy(~F, s, m), ~k: Nat, ~x: O.C(F), ~e: O.C(F), ~hx: @j: Nat -> M.bnd(~F, O.sub(~F, s(Nat.add(k, j)), x), e)) -> M.bnd(~F, O.sub(~F, CR.lim(F, R, s, m), x), e):
  (nn_by(~F, O.sub(~F, e, O.sub(~F, CR.lim(F, R, s, m), x)), l => close1(~F, ~R, ~s, ~m, ~h, ~k, ~x, ~e, ~hx, l)),
   nn_by(~F, O.add(F, e, O.sub(~F, CR.lim(F, R, s, m), x)), l => close2(~F, ~R, ~s, ~m, ~h, ~k, ~x, ~e, ~hx, l)))

# Below every power
# -----------------

def pz1.fin(~F: O.OField, +x: O.C(F), +p: O.C(F), +dl: O.C(F), hxj: M.bnd(~F, x, p), hs: O.le(~F, p, dl), hlt: O.lt(F, dl, O.neg(F, O.sub(~F, O.zero(F), x)))) -> Empty:
  (h1, h2) = hxj
  +d = O.neg(F, O.sub(~F, O.zero(F), x))
  le_lt_absurd(~F, d, dl, DM.le_trans(~F, d, p, dl, le_by(~F, d, p, O.sub(~F, p, x), FR.fring_eq(~F, [p, x], E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZVar{0n}, E.ZNeg{E.ZSub{E.ZCst{S.Z0{}}, E.ZVar{1n}}}}, {==}), h1), hs), hlt)

def pz2.fin(~F: O.OField, +x: O.C(F), +p: O.C(F), +dl: O.C(F), hxj: M.bnd(~F, x, p), hs: O.le(~F, p, dl), hlt: O.lt(F, dl, O.neg(F, O.add(F, O.zero(F), x)))) -> Empty:
  (h1, h2) = hxj
  +d = O.neg(F, O.add(F, O.zero(F), x))
  le_lt_absurd(~F, d, dl, DM.le_trans(~F, d, p, dl, le_by(~F, d, p, O.add(F, p, x), FR.fring_eq(~F, [p, x], E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZVar{0n}, E.ZNeg{E.ZAdd{E.ZCst{S.Z0{}}, E.ZVar{1n}}}}, {==}), h2), hs), hlt)

def pz1(~F: O.OField, ~R: CR.Complete<F>, ~q: O.C(F), ~hq0: O.le(~F, O.zero(F), q), ~hq1: O.lt(F, q, O.one(F)), ~c: O.C(F), ~hc: O.le(~F, O.zero(F), c), ~x: O.C(F), ~hx: @j: Nat -> M.bnd(~F, x, O.mul(F, pw(~F, q, j), c)), l: O.lt(F, O.sub(~F, O.zero(F), x), O.zero(F))) -> Empty:
  +d = O.neg(F, O.sub(~F, O.zero(F), x))
  +kk = CR.arch(F, R, O.inv(F, d))
  +j = mk(~F, ~R, q, c, kk)
  pz1.fin(~F, x, O.mul(F, pw(~F, q, j), c), CR.eps(~F, kk), hx(j), small(~F, ~R, q, hq0, hq1, c, hc, kk), eps_lt(~F, ~R, d, FO.neg_pos(~F, O.sub(~F, O.zero(F), x), l)))

def pz2(~F: O.OField, ~R: CR.Complete<F>, ~q: O.C(F), ~hq0: O.le(~F, O.zero(F), q), ~hq1: O.lt(F, q, O.one(F)), ~c: O.C(F), ~hc: O.le(~F, O.zero(F), c), ~x: O.C(F), ~hx: @j: Nat -> M.bnd(~F, x, O.mul(F, pw(~F, q, j), c)), l: O.lt(F, O.add(F, O.zero(F), x), O.zero(F))) -> Empty:
  +d = O.neg(F, O.add(F, O.zero(F), x))
  +kk = CR.arch(F, R, O.inv(F, d))
  +j = mk(~F, ~R, q, c, kk)
  pz2.fin(~F, x, O.mul(F, pw(~F, q, j), c), CR.eps(~F, kk), hx(j), small(~F, ~R, q, hq0, hq1, c, hc, kk), eps_lt(~F, ~R, d, FO.neg_pos(~F, O.add(F, O.zero(F), x), l)))

# |x| ≤ q^j c for every j gives |x| ≤ 0, for 0 ≤ q < 1 and 0 ≤ c
def pw_zero(~F: O.OField, ~R: CR.Complete<F>, ~q: O.C(F), ~hq0: O.le(~F, O.zero(F), q), ~hq1: O.lt(F, q, O.one(F)), ~c: O.C(F), ~hc: O.le(~F, O.zero(F), c), ~x: O.C(F), ~hx: @j: Nat -> M.bnd(~F, x, O.mul(F, pw(~F, q, j), c))) -> M.bnd(~F, x, O.zero(F)):
  (nn_by(~F, O.sub(~F, O.zero(F), x), l => pz1(~F, ~R, ~q, ~hq0, ~hq1, ~c, ~hc, ~x, ~hx, l)),
   nn_by(~F, O.add(F, O.zero(F), x), l => pz2(~F, ~R, ~q, ~hq0, ~hq1, ~c, ~hc, ~x, ~hx, l)))
