# bend-cad: what the simplex's Unsat says (PLAN-sk13a S3). At Unsat{t, i}
# the leaving slack i's row D x_i = M . x has no entering variable: every
# slack entry is <= 0 and every y entry is 0. The multipliers mu
# (lib/refute.bend's mults: D - M_i at i, -M_k at the other slacks) then
# - are all >= 0 (unsat_nn),
# - cancel every y column, sum_k mu_k a_k = 0 (unsat_cols),
# - and leave sum_k mu_k b_k < 0, or 0 with sum_k mu_k [s_k strict] > 0
#   (unsat_lex),
# a Motzkin certificate for the inequalities a_k . y + b_k > 0 (>= 0).
# Proofs only.
#
# Generated from tools/drafts/unsatpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ./karith.bend as KA
import ./nat.bend as LN
import ./zring.bend as R
import ./zlaws.bend as ZL
import ./zord.bend as ZO
import ./fring.bend as FR
import ./ford.bend as FO
import ./qemb.bend as QE
import ./qfield.bend as QF
import ./elim.bend as EL
import ./simplex.bend as SX
import ./simppf.bend as SP
import ./runpf.bend as RN
import ./lexpf.bend as LX
import ./blandpf.bend as BL
import ./termpf.bend as TP
import ./pigeon.bend as PH
import ./refute.bend as RF

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Small facts about Nat
# ---------------------

def isle_refl(j: Nat) -> {Nat.is_le(j, j) == True{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+k:
      isle_refl(k)

def isle_succ(m: Nat, j: Nat, h: {Nat.is_le(m, j) == True{} : Bool}) -> {Nat.is_le(m, 1n+j) == True{} : Bool}:
  match m j:
    case 0n j:
      {==}
    case 1n+a 0n:
      absurd({Nat.is_le(1n+a, 1n) == True{} : Bool}, KA.ft(h))
    case 1n+a 1n+b:
      isle_succ(a, b, h)

# k < m: m is not <= k
def isle_ltn(k: Nat, m: Nat, h: {SX.ltn(k, m) == True{} : Bool}) -> {Nat.is_le(m, k) == False{} : Bool}:
  match k m:
    case 0n 0n:
      absurd({Nat.is_le(0n, 0n) == False{} : Bool}, KA.ft(h))
    case 0n 1n+b:
      {==}
    case 1n+a 0n:
      absurd({Nat.is_le(0n, 1n+a) == False{} : Bool}, KA.ft(h))
    case 1n+a 1n+b:
      isle_ltn(a, b, h)

def ltn_eqn(t: Nat, j: Nat, h: {SX.ltn(t, j) == True{} : Bool}) -> {SX.eqn(j, t) == False{} : Bool}:
  match t j:
    case 0n 0n:
      absurd({SX.eqn(0n, 0n) == False{} : Bool}, KA.ft(h))
    case 0n 1n+b:
      {==}
    case 1n+a 0n:
      {==}
    case 1n+a 1n+b:
      ltn_eqn(a, b, h)

def ltn_succ(t: Nat, j: Nat, h: {SX.ltn(t, j) == True{} : Bool}) -> {SX.ltn(t, 1n+j) == True{} : Bool}:
  match t j:
    case 0n 0n:
      absurd({SX.ltn(0n, 1n) == True{} : Bool}, KA.ft(h))
    case 0n 1n+b:
      {==}
    case 1n+a 0n:
      absurd({SX.ltn(1n+a, 1n) == True{} : Bool}, KA.ft(h))
    case 1n+a 1n+b:
      ltn_succ(a, b, h)

def eqn_ltn(k: Nat, i: Nat, h: {SX.eqn(k, i) == True{} : Bool}) -> {SX.ltn(i, 1n+k) == True{} : Bool}:
  match k i:
    case 0n 0n:
      {==}
    case 0n 1n+b:
      absurd({SX.ltn(1n+b, 1n) == True{} : Bool}, KA.ft(h))
    case 1n+a 0n:
      absurd({SX.ltn(0n, 2n+a) == True{} : Bool}, KA.ft(h))
    case 1n+a 1n+b:
      eqn_ltn(a, b, h)

# t < j: t is not in [j, j + c)
def inrange_lt(+t: Nat, c: Nat, +j: Nat, +h: {SX.ltn(t, j) == True{} : Bool}) -> {BL.inrange(t, c, j) == False{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(Bool, SX.eqn(j, t), False{}, ltn_eqn(t, j, h)) : {BL.bor(_, BL.inrange(t, k, 1n+j)) == False{} : Bool}
      inrange_lt(t, k, 1n+j, ltn_succ(t, j, h))

# Integer vectors from an index on
# --------------------------------

def zdrop(k: Nat, u: List<&2, S.Z>) -> List<&2, S.Z>:
  match k u:
    case 0n u:
      u
    case 1n+j Nil{}:
      Nil{}
    case 1n+j Con{x, t}:
      zdrop(j, t)

# u . w from entry k on
def rdot(k: Nat, u: List<&2, S.Z>, w: List<&2, S.Z>) -> S.Z:
  match k u w:
    case 0n u w:
      SX.dot(u, w)
    case 1n+j Nil{} w:
      S.Z0{}
    case 1n+j Con{x, t} Nil{}:
      S.Z0{}
    case 1n+j Con{x, t} Con{y, s}:
      rdot(j, t, s)

def dot_nil_l(w: List<&2, S.Z>) -> {S.Z0{} == SX.dot(Nil{}, w) : S.Z}:
  match w:
    case Nil{}:
      {==}
    case Con{y, s}:
      {==}

def dot_nil_r(u: List<&2, S.Z>) -> {S.Z0{} == SX.dot(u, Nil{}) : S.Z}:
  match u:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

def mz0(+x: S.Z, +ut: List<&2, S.Z>) -> {S.Z.add(S.Z.mul(x, S.Z0{}), SX.dot(ut, Nil{})) == S.Z0{} : S.Z}:
  %dot_nil_r(ut) : {S.Z.add(S.Z.mul(x, S.Z0{}), _) == S.Z0{} : S.Z}
  R.ring_eq([x], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})

# u0 x_k + ut . (x from k + 1) = (u0 : ut) . (x from k)
def dot_zdrop(+u0: S.Z, +ut: List<&2, S.Z>, k: Nat, X: List<&2, S.Z>) -> {S.Z.add(S.Z.mul(u0, SX.at(X, k)), SX.dot(ut, zdrop(1n+k, X))) == SX.dot(Con{u0, ut}, zdrop(k, X)) : S.Z}:
  match k X:
    case 0n Nil{}:
      mz0(u0, ut)
    case 0n Con{y, s}:
      {==}
    case 1n+j Nil{}:
      mz0(u0, ut)
    case 1n+j Con{y, s}:
      dot_zdrop(u0, ut, j, s)

def rdot_step(k: Nat, u: List<&2, S.Z>, w: List<&2, S.Z>) -> {S.Z.add(S.Z.mul(SX.at(u, k), SX.at(w, k)), rdot(1n+k, u, w)) == rdot(k, u, w) : S.Z}:
  match k u w:
    case 0n Nil{} w:
      dot_nil_l(w)
    case 0n Con{x, t} Nil{}:
      R.ring_eq([x], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})
    case 0n Con{x, t} Con{y, s}:
      {==}
    case 1n+j Nil{} w:
      {==}
    case 1n++j Con{x, t} Nil{}:
      R.ring_eq([SX.at(t, j)], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})
    case 1n+j Con{x, t} Con{y, s}:
      rdot_step(j, t, s)

# The multipliers against a vector
# --------------------------------


def alg_t(+mk: S.Z, +xk: S.Z, +a: S.Z, +r1: S.Z, +d: S.Pos, +xi: S.Z, +re: S.Z, hk: {xk == xi : S.Z}, ih: {S.Z.add(a, r1) == re : S.Z})
  -> {S.Z.add(S.Z.add(S.Z.mul(S.Z.add(S.Z.neg(mk), S.Zpos{d}), xk), a), S.Z.add(S.Z.mul(mk, xk), r1)) == S.Z.add(S.Z.mul(S.Zpos{d}, xi), re) : S.Z}:
  %hk : {S.Z.add(S.Z.add(S.Z.mul(S.Z.add(S.Z.neg(mk), S.Zpos{d}), xk), a), S.Z.add(S.Z.mul(mk, xk), r1)) == S.Z.add(S.Z.mul(S.Zpos{d}, _), re) : S.Z}
  %ih : {S.Z.add(S.Z.add(S.Z.mul(S.Z.add(S.Z.neg(mk), S.Zpos{d}), xk), a), S.Z.add(S.Z.mul(mk, xk), r1)) == S.Z.add(S.Z.mul(S.Zpos{d}, xk), _) : S.Z}
  R.ring_eq([mk, xk, a, r1, S.Zpos{d}], E.ZAdd{E.ZAdd{E.ZMul{E.ZAdd{E.ZNeg{E.ZVar{0n}}, E.ZVar{4n}}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{3n}}}, E.ZAdd{E.ZMul{E.ZVar{4n}, E.ZVar{1n}}, E.ZAdd{E.ZVar{2n}, E.ZVar{3n}}}, {==})

def alg_f(+mk: S.Z, +xk: S.Z, +a: S.Z, +r1: S.Z, +rhs: S.Z, ih: {S.Z.add(a, r1) == rhs : S.Z})
  -> {S.Z.add(S.Z.add(S.Z.mul(S.Z.add(S.Z.neg(mk), S.Z0{}), xk), a), S.Z.add(S.Z.mul(mk, xk), r1)) == rhs : S.Z}:
  %ih : {S.Z.add(S.Z.add(S.Z.mul(S.Z.add(S.Z.neg(mk), S.Z0{}), xk), a), S.Z.add(S.Z.mul(mk, xk), r1)) == _ : S.Z}
  R.ring_eq([mk, xk, a, r1], E.ZAdd{E.ZAdd{E.ZMul{E.ZAdd{E.ZNeg{E.ZVar{0n}}, E.ZCst{S.Z0{}}}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{3n}}}, E.ZAdd{E.ZVar{2n}, E.ZVar{3n}}, {==})

def mults_dot.c(b: Bool, +M: List<&2, S.Z>, +i: Nat, +d: S.Pos, +j: Nat, +k: Nat, +X: List<&2, S.Z>, +hb: {b == SX.eqn(k, i) : Bool},
  ih: {S.Z.add(SX.dot(RF.mults(M, i, d, j, 1n+k), zdrop(1n+k, X)), rdot(1n+k, M, X)) == S.Z.add(EL.ifz(BL.inrange(i, j, 1n+k), S.Z.mul(S.Zpos{d}, SX.at(X, i))), rdot(BL.plus(j, 1n+k), M, X)) : S.Z})
  -> {S.Z.add(S.Z.add(S.Z.mul(S.Z.add(S.Z.neg(SX.at(M, k)), EL.ifz(SX.eqn(k, i), S.Zpos{d})), SX.at(X, k)), SX.dot(RF.mults(M, i, d, j, 1n+k), zdrop(1n+k, X))), S.Z.add(S.Z.mul(SX.at(M, k), SX.at(X, k)), rdot(1n+k, M, X))) == S.Z.add(EL.ifz(BL.bor(SX.eqn(k, i), BL.inrange(i, j, 1n+k)), S.Z.mul(S.Zpos{d}, SX.at(X, i))), rdot(BL.plus(j, 1n+k), M, X)) : S.Z}:
  match b:
    case True{}:
      %hb : {S.Z.add(S.Z.add(S.Z.mul(S.Z.add(S.Z.neg(SX.at(M, k)), EL.ifz(_, S.Zpos{d})), SX.at(X, k)), SX.dot(RF.mults(M, i, d, j, 1n+k), zdrop(1n+k, X))), S.Z.add(S.Z.mul(SX.at(M, k), SX.at(X, k)), rdot(1n+k, M, X))) == S.Z.add(EL.ifz(BL.bor(_, BL.inrange(i, j, 1n+k)), S.Z.mul(S.Zpos{d}, SX.at(X, i))), rdot(BL.plus(j, 1n+k), M, X)) : S.Z}
      alg_t(SX.at(M, k), SX.at(X, k), SX.dot(RF.mults(M, i, d, j, 1n+k), zdrop(1n+k, X)), rdot(1n+k, M, X), d, SX.at(X, i), rdot(BL.plus(j, 1n+k), M, X),
        (%SP.eqn_eq(k, i, Equal.sym(Bool, True{}, SX.eqn(k, i), hb)) : {SX.at(X, k) == SX.at(X, _) : S.Z}
          {==}),
        (%inrange_lt(i, j, 1n+k, eqn_ltn(k, i, Equal.sym(Bool, True{}, SX.eqn(k, i), hb))) : {S.Z.add(SX.dot(RF.mults(M, i, d, j, 1n+k), zdrop(1n+k, X)), rdot(1n+k, M, X)) == S.Z.add(EL.ifz(_, S.Z.mul(S.Zpos{d}, SX.at(X, i))), rdot(BL.plus(j, 1n+k), M, X)) : S.Z}
          ih))
    case False{}:
      %hb : {S.Z.add(S.Z.add(S.Z.mul(S.Z.add(S.Z.neg(SX.at(M, k)), EL.ifz(_, S.Zpos{d})), SX.at(X, k)), SX.dot(RF.mults(M, i, d, j, 1n+k), zdrop(1n+k, X))), S.Z.add(S.Z.mul(SX.at(M, k), SX.at(X, k)), rdot(1n+k, M, X))) == S.Z.add(EL.ifz(BL.bor(_, BL.inrange(i, j, 1n+k)), S.Z.mul(S.Zpos{d}, SX.at(X, i))), rdot(BL.plus(j, 1n+k), M, X)) : S.Z}
      alg_f(SX.at(M, k), SX.at(X, k), SX.dot(RF.mults(M, i, d, j, 1n+k), zdrop(1n+k, X)), rdot(1n+k, M, X), S.Z.add(EL.ifz(BL.inrange(i, j, 1n+k), S.Z.mul(S.Zpos{d}, SX.at(X, i))), rdot(BL.plus(j, 1n+k), M, X)), ih)

def mults_dot.go(+M: List<&2, S.Z>, +i: Nat, +d: S.Pos, +j: Nat, +k: Nat, +X: List<&2, S.Z>,
  ih: {S.Z.add(SX.dot(RF.mults(M, i, d, j, 1n+k), zdrop(1n+k, X)), rdot(1n+k, M, X)) == S.Z.add(EL.ifz(BL.inrange(i, j, 1n+k), S.Z.mul(S.Zpos{d}, SX.at(X, i))), rdot(BL.plus(j, 1n+k), M, X)) : S.Z})
  -> {S.Z.add(SX.dot(RF.mults(M, i, d, 1n+j, k), zdrop(k, X)), rdot(k, M, X)) == S.Z.add(EL.ifz(BL.inrange(i, 1n+j, k), S.Z.mul(S.Zpos{d}, SX.at(X, i))), rdot(BL.plus(1n+j, k), M, X)) : S.Z}:
  %dot_zdrop(S.Z.add(S.Z.neg(SX.at(M, k)), EL.ifz(SX.eqn(k, i), S.Zpos{d})), RF.mults(M, i, d, j, 1n+k), k, X) : {S.Z.add(_, rdot(k, M, X)) == S.Z.add(EL.ifz(BL.inrange(i, 1n+j, k), S.Z.mul(S.Zpos{d}, SX.at(X, i))), rdot(BL.plus(j, 1n+k), M, X)) : S.Z}
  %rdot_step(k, M, X) : {S.Z.add(S.Z.add(S.Z.mul(S.Z.add(S.Z.neg(SX.at(M, k)), EL.ifz(SX.eqn(k, i), S.Zpos{d})), SX.at(X, k)), SX.dot(RF.mults(M, i, d, j, 1n+k), zdrop(1n+k, X))), _) == S.Z.add(EL.ifz(BL.inrange(i, 1n+j, k), S.Z.mul(S.Zpos{d}, SX.at(X, i))), rdot(BL.plus(j, 1n+k), M, X)) : S.Z}
  mults_dot.c(SX.eqn(k, i), M, i, d, j, k, X, {==}, ih)

# mu . (X from k) + (M . X from k) = [i in [k, k + c)] D X_i + (M . X from k + c)
def mults_dot(+M: List<&2, S.Z>, +i: Nat, +d: S.Pos, c: Nat, +k: Nat, +X: List<&2, S.Z>)
  -> {S.Z.add(SX.dot(RF.mults(M, i, d, c, k), zdrop(k, X)), rdot(k, M, X)) == S.Z.add(EL.ifz(BL.inrange(i, c, k), S.Z.mul(S.Zpos{d}, SX.at(X, i))), rdot(BL.plus(c, k), M, X)) : S.Z}:
  match c:
    case 0n:
      %dot_nil_l(zdrop(k, X)) : {S.Z.add(_, rdot(k, M, X)) == rdot(k, M, X) : S.Z}
      {==}
    case 1n++j:
      mults_dot.go(M, i, d, j, k, X, mults_dot(M, i, d, j, 1n+k, X))

# No entering variable
# --------------------

def allz(u: List<&2, S.Z>) -> Bool:
  match u:
    case Nil{}:
      True{}
    case Con{x, t}:
      KA.band(SX.iszero(x), allz(t))

def dot_allz(u: List<&2, S.Z>, w: List<&2, S.Z>, +h: {allz(u) == True{} : Bool}) -> {SX.dot(u, w) == S.Z0{} : S.Z}:
  match u w:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, s}:
      {==}
    case Con{x, t} Nil{}:
      {==}
    case Con{+x, +t} Con{y, s}:
      %SP.iszero_eq(x, Equal.sym(Bool, SX.iszero(x), True{}, KA.band_l(SX.iszero(x), allz(t), h))) : {S.Z.add(S.Z.mul(_, y), SX.dot(t, s)) == S.Z0{} : S.Z}
      dot_allz(t, s, KA.band_r(SX.iszero(x), allz(t), h))

def rdot_allz(k: Nat, u: List<&2, S.Z>, w: List<&2, S.Z>, h: {allz(zdrop(k, u)) == True{} : Bool}) -> {rdot(k, u, w) == S.Z0{} : S.Z}:
  match k u w:
    case 0n u w:
      dot_allz(u, w, h)
    case 1n+j Nil{} w:
      {==}
    case 1n+j Con{x, t} Nil{}:
      {==}
    case 1n+j Con{x, t} Con{y, s}:
      rdot_allz(j, t, s, h)

def pick_none_l(b: Bool, +j: Nat, +r: Maybe<&2, Nat>, h: {SX.pick(b, j, r) == None{} : Maybe<&2, Nat>}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, RN.none_some(j, Equal.sym(Maybe<&2, Nat>, Some{j}, None{}, h)))
    case False{}:
      {==}

def pick_none_r(b: Bool, +j: Nat, +r: Maybe<&2, Nat>, h: {SX.pick(b, j, r) == None{} : Maybe<&2, Nat>}) -> {r == None{} : Maybe<&2, Nat>}:
  match b:
    case True{}:
      absurd({r == None{} : Maybe<&2, Nat>}, RN.none_some(j, Equal.sym(Maybe<&2, Nat>, Some{j}, None{}, h)))
    case False{}:
      h

# a free variable that cannot raise the row has entry 0
def help_free(c: S.Z, h: {SX.helpful(c, True{}) == False{} : Bool}) -> {SX.iszero(c) == True{} : Bool}:
  match c:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      absurd({SX.iszero(S.Zpos{p}) == True{} : Bool}, KA.tf(h))
    case S.Zneg{p}:
      absurd({SX.iszero(S.Zneg{p}) == True{} : Bool}, KA.tf(h))

# from an index m <= j on, every entry is 0
def nohelp_allz(r: List<&2, S.Z>, +m: Nat, +j: Nat, +h: {SX.enter.go(r, m, j) == None{} : Maybe<&2, Nat>}, +hm: {Nat.is_le(m, j) == True{} : Bool}) -> {allz(r) == True{} : Bool}:
  match r:
    case Nil{}:
      {==}
    case Con{+c, +t}:
      KA.band_i(SX.iszero(c), allz(t),
        help_free(c, (%hm : {SX.helpful(c, _) == False{} : Bool}
          pick_none_l(SX.helpful(c, Nat.is_le(m, j)), j, SX.enter.go(t, m, 1n+j), h))),
        nohelp_allz(t, m, 1n+j, pick_none_r(SX.helpful(c, Nat.is_le(m, j)), j, SX.enter.go(t, m, 1n+j), h), isle_succ(m, j, hm)))

# with nothing to enter, the row is 0 past the slacks
def nohelp_tail(c: Nat, r: List<&2, S.Z>, +j: Nat, h: {SX.enter.go(r, BL.plus(c, j), j) == None{} : Maybe<&2, Nat>}) -> {allz(zdrop(c, r)) == True{} : Bool}:
  match c r:
    case 0n r:
      nohelp_allz(r, j, j, h, isle_refl(j))
    case 1n+k Nil{}:
      {==}
    case 1n++k Con{+x, +t}:
      nohelp_tail(k, t, 1n+j, pick_none_r(SX.helpful(x, Nat.is_le(BL.plus(k, 1n+j), j)), j, SX.enter.go(t, BL.plus(k, 1n+j), 1n+j), h))

# mu . X + M . X = D X_i
def mdot(+M: List<&2, S.Z>, +i: Nat, +d: S.Pos, +m: Nat, +X: List<&2, S.Z>, hi: {SX.ltn(i, m) == True{} : Bool}, hn: {SX.enter.go(M, m, 0n) == None{} : Maybe<&2, Nat>})
  -> {S.Z.add(SX.dot(RF.mults(M, i, d, m, 0n), X), SX.dot(M, X)) == S.Z.mul(S.Zpos{d}, SX.at(X, i)) : S.Z}:
  %Equal.sym(S.Z, S.Z.mul(S.Zpos{d}, SX.at(X, i)), S.Z.add(S.Z.mul(S.Zpos{d}, SX.at(X, i)), S.Z0{}), ZL.add_zero(S.Z.mul(S.Zpos{d}, SX.at(X, i)))) : {S.Z.add(SX.dot(RF.mults(M, i, d, m, 0n), X), SX.dot(M, X)) == _ : S.Z}
  %rdot_allz(BL.plus(m, 0n), M, X, (%Equal.sym(Nat, BL.plus(m, 0n), m, TP.plus0(m)) : {allz(zdrop(_, M)) == True{} : Bool}
      nohelp_tail(m, M, 0n, (%Equal.sym(Nat, BL.plus(m, 0n), m, TP.plus0(m)) : {SX.enter.go(M, _, 0n) == None{} : Maybe<&2, Nat>}
        hn)))) : {S.Z.add(SX.dot(RF.mults(M, i, d, m, 0n), X), SX.dot(M, X)) == S.Z.add(S.Z.mul(S.Zpos{d}, SX.at(X, i)), _) : S.Z}
  %BL.inrange_ok(i, m, 0n, {==}, (%Equal.sym(Nat, BL.plus(m, 0n), m, TP.plus0(m)) : {SX.ltn(i, _) == True{} : Bool}
      hi)) : {S.Z.add(SX.dot(RF.mults(M, i, d, m, 0n), X), SX.dot(M, X)) == S.Z.add(EL.ifz(_, S.Z.mul(S.Zpos{d}, SX.at(X, i))), rdot(BL.plus(m, 0n), M, X)) : S.Z}
  mults_dot(M, i, d, m, 0n, X)

# The multipliers are >= 0
# ------------------------

def nn(x: S.Z) -> Bool:
  match x:
    case S.Z0{}:
      True{}
    case S.Zpos{p}:
      True{}
    case S.Zneg{p}:
      False{}

def znn(u: List<&2, S.Z>) -> Bool:
  match u:
    case Nil{}:
      True{}
    case Con{x, t}:
      KA.band(nn(x), znn(t))

# a slack that cannot raise the row has entry <= 0
def nn_neg_slack(c: S.Z, h: {SX.helpful(c, False{}) == False{} : Bool}) -> {nn(S.Z.neg(c)) == True{} : Bool}:
  match c:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      absurd({nn(S.Zneg{p}) == True{} : Bool}, KA.tf(h))
    case S.Zneg{p}:
      {==}

def nn_add(x: S.Z, y: S.Z, hx: {nn(x) == True{} : Bool}, hy: {nn(y) == True{} : Bool}) -> {nn(S.Z.add(x, y)) == True{} : Bool}:
  match x y:
    case S.Z0{} y:
      hy
    case S.Zpos{p} S.Z0{}:
      {==}
    case S.Zpos{p} S.Zpos{q}:
      {==}
    case S.Zpos{p} S.Zneg{q}:
      absurd({nn(S.Z.add(S.Zpos{p}, S.Zneg{q})) == True{} : Bool}, KA.ft(hy))
    case S.Zneg{p} y:
      absurd({nn(S.Z.add(S.Zneg{p}, y)) == True{} : Bool}, KA.ft(hx))

def nn_ifz(b: Bool, +d: S.Pos) -> {nn(EL.ifz(b, S.Zpos{d})) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def le_succ(p: Nat) -> {KA.natle(p, 1n+p) == True{} : Bool}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      le_succ(q)

def le_plus(c: Nat, +p: Nat) -> {KA.natle(p, BL.plus(c, p)) == True{} : Bool}:
  match c:
    case 0n:
      KA.natle_refl(p)
    case 1n++k:
      KA.natle_trans(p, 1n+p, BL.plus(k, 1n+p), le_succ(p), le_plus(k, 1n+p))

# slack k's entry in the row is <= 0
def slack_nohelp(+M: List<&2, S.Z>, +m: Nat, +k: Nat, hn: {SX.enter.go(M, m, 0n) == None{} : Maybe<&2, Nat>}, hk: {SX.ltn(k, m) == True{} : Bool}) -> {SX.helpful(SX.at(M, k), False{}) == False{} : Bool}:
  %isle_ltn(k, m, hk) : {SX.helpful(SX.at(M, k), _) == False{} : Bool}
  %RN.bat_helps0(M, m, k) : {_ == False{} : Bool}
  RN.first_none(RN.helps(M, m, 0n), (%RN.enter_eq(M, m, 0n) : {_ == None{} : Maybe<&2, Nat>}
    hn), k)

def mults_nn(+M: List<&2, S.Z>, +i: Nat, +d: S.Pos, c: Nat, +k: Nat, +m: Nat, +hn: {SX.enter.go(M, m, 0n) == None{} : Maybe<&2, Nat>}, +hc: {KA.natle(BL.plus(c, k), m) == True{} : Bool}) -> {znn(RF.mults(M, i, d, c, k)) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n++j:
      KA.band_i(nn(S.Z.add(S.Z.neg(SX.at(M, k)), EL.ifz(SX.eqn(k, i), S.Zpos{d}))), znn(RF.mults(M, i, d, j, 1n+k)),
        nn_add(S.Z.neg(SX.at(M, k)), EL.ifz(SX.eqn(k, i), S.Zpos{d}),
          nn_neg_slack(SX.at(M, k), slack_nohelp(M, m, k, hn, SP.ltn_of(k, m, KA.natle_trans(1n+k, BL.plus(j, 1n+k), m, le_plus(j, 1n+k), hc)))),
          nn_ifz(SX.eqn(k, i), d)),
        mults_nn(M, i, d, j, 1n+k, m, hn, hc))

def vlen_mults(+M: List<&2, S.Z>, +i: Nat, +d: S.Pos, c: Nat, +k: Nat) -> {SX.vlen(RF.mults(M, i, d, c, k)) == c : Nat}:
  match c:
    case 0n:
      {==}
    case 1n++j:
      %vlen_mults(M, i, d, j, 1n+k) : {1n+SX.vlen(RF.mults(M, i, d, j, 1n+k)) == 1n+_ : Nat}
      {==}

# The run's Unsat
# ---------------

def meq(ml: Maybe<&2, Nat>, +j: Nat) -> Bool:
  match ml:
    case None{}:
      False{}
    case Some{x}:
      SX.eqn(x, j)

def isnone(me: Maybe<&2, Nat>) -> Bool:
  match me:
    case None{}:
      True{}
    case Some{e}:
      False{}

def meq_some(ml: Maybe<&2, Nat>, +j: Nat, h: {meq(ml, j) == True{} : Bool}) -> {ml == Some{j} : Maybe<&2, Nat>}:
  match ml:
    case None{}:
      absurd({None{} == Some{j} : Maybe<&2, Nat>}, KA.ft(h))
    case Some{+x}:
      %SP.eqn_eq(x, j, h) : {Some{x} == Some{_} : Maybe<&2, Nat>}
      {==}

def isnone_none(me: Maybe<&2, Nat>, h: {isnone(me) == True{} : Bool}) -> {me == None{} : Maybe<&2, Nat>}:
  match me:
    case None{}:
      {==}
    case Some{e}:
      absurd({Some{e} == None{} : Maybe<&2, Nat>}, KA.ft(h))


# slack i leaves t, and nothing can enter
def uok(+lp: SX.LP, +t: SX.Tab, +i: Nat) -> Bool:
  KA.band(meq(SX.leave(lp, t), i), isnone(SX.enter.go(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n)))

def ucheck(+lp: SX.LP, r: SX.Run) -> Bool:
  match r:
    case SX.Go{t}:
      True{}
    case SX.Sat{t}:
      True{}
    case SX.Unsat{+t, +i}:
      uok(lp, t, i)

def uc.e(+lp: SX.LP, +t: SX.Tab, +i: Nat, me: Maybe<&2, Nat>, hme: {me == SX.enter.go(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n) : Maybe<&2, Nat>}, hl: {SX.leave(lp, t) == Some{i} : Maybe<&2, Nat>}) -> {ucheck(lp, SX.step.e(lp, t, i, me)) == True{} : Bool}:
  match me:
    case None{}:
      %Equal.sym(Maybe<&2, Nat>, SX.leave(lp, t), Some{i}, hl) : {KA.band(meq(_, i), isnone(SX.enter.go(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n))) == True{} : Bool}
      %hme : {KA.band(SX.eqn(i, i), isnone(_)) == True{} : Bool}
      KA.band_i(SX.eqn(i, i), True{}, BL.eqn_refl(i), {==})
    case Some{e}:
      {==}

def uc.l(+lp: SX.LP, +t: SX.Tab, ml: Maybe<&2, Nat>, hml: {ml == SX.leave(lp, t) : Maybe<&2, Nat>}) -> {ucheck(lp, SX.step.l(lp, t, ml)) == True{} : Bool}:
  match ml:
    case None{}:
      {==}
    case Some{+i}:
      uc.e(lp, t, i, SX.enter.go(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n), {==}, Equal.sym(Maybe<&2, Nat>, Some{i}, SX.leave(lp, t), hml))

def uc.adv(+lp: SX.LP, r: SX.Run, h: {ucheck(lp, r) == True{} : Bool}) -> {ucheck(lp, SX.adv(lp, r)) == True{} : Bool}:
  match r:
    case SX.Go{+t}:
      uc.l(lp, t, SX.leave(lp, t), {==})
    case SX.Sat{t}:
      {==}
    case SX.Unsat{t, i}:
      h

# every Unsat the run reaches comes from such a step
def ucheck_all(+lp: SX.LP, n: Nat) -> {ucheck(lp, RN.st(lp, n)) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++k:
      %Equal.sym(SX.Run, RN.st(lp, 1n+k), SX.adv(lp, RN.st(lp, k)), RN.st_succ(lp, k)) : {ucheck(lp, _) == True{} : Bool}
      uc.adv(lp, RN.st(lp, k), ucheck_all(lp, k))


def u_st(+lp: SX.LP, +t: SX.Tab, +i: Nat, +h: {SX.solve(lp) == SX.Unsat{t, i} : SX.Run}) -> {RN.st(lp, PH.pow2(SX.LP.nv(lp))) == SX.Unsat{t, i} : SX.Run}:
  Equal.trans(SX.Run, RN.st(lp, PH.pow2(SX.LP.nv(lp))), SX.solve(lp), SX.Unsat{t, i}, Equal.sym(SX.Run, SX.solve(lp), RN.st(lp, PH.pow2(SX.LP.nv(lp))), TP.solve_st(lp)), h)

# t is the run's dictionary at step 2^N
def u_tab(+lp: SX.LP, +t: SX.Tab, +i: Nat, +h: {SX.solve(lp) == SX.Unsat{t, i} : SX.Run}) -> {RN.tab(lp, PH.pow2(SX.LP.nv(lp))) == t : SX.Tab}:
  %Equal.sym(SX.Run, RN.st(lp, PH.pow2(SX.LP.nv(lp))), SX.Unsat{t, i}, u_st(lp, t, i, h)) : {RN.rtab(_) == t : SX.Tab}
  {==}

def u_ok(+lp: SX.LP, +t: SX.Tab, +i: Nat, +h: {SX.solve(lp) == SX.Unsat{t, i} : SX.Run}) -> {uok(lp, t, i) == True{} : Bool}:
  %u_st(lp, t, i, h) : {ucheck(lp, _) == True{} : Bool}
  ucheck_all(lp, PH.pow2(SX.LP.nv(lp)))

def u_leave(+lp: SX.LP, +t: SX.Tab, +i: Nat, +h: {SX.solve(lp) == SX.Unsat{t, i} : SX.Run}) -> {SX.leave(lp, t) == Some{i} : Maybe<&2, Nat>}:
  meq_some(SX.leave(lp, t), i, KA.band_l(meq(SX.leave(lp, t), i), isnone(SX.enter.go(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n)), u_ok(lp, t, i, h)))

def u_enter(+lp: SX.LP, +t: SX.Tab, +i: Nat, +h: {SX.solve(lp) == SX.Unsat{t, i} : SX.Run}) -> {SX.enter.go(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n) == None{} : Maybe<&2, Nat>}:
  isnone_none(SX.enter.go(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n), KA.band_r(meq(SX.leave(lp, t), i), isnone(SX.enter.go(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n)), u_ok(lp, t, i, h)))

def u_first(+lp: SX.LP, +t: SX.Tab, +i: Nat, +h: {SX.solve(lp) == SX.Unsat{t, i} : SX.Run}) -> {RN.firstfrom(RN.viols(SX.LP.qs(lp), SX.Tab.rows(t), SX.LP.v0(lp), SX.LP.v1(lp)), 0n) == Some{i} : Maybe<&2, Nat>}:
  %RN.leave_eq(SX.LP.qs(lp), SX.Tab.rows(t), SX.LP.v0(lp), SX.LP.v1(lp), 0n) : {_ == Some{i} : Maybe<&2, Nat>}
  u_leave(lp, t, i, h)

# i is a slack
def u_lt(+lp: SX.LP, +t: SX.Tab, +i: Nat, +h: {SX.solve(lp) == SX.Unsat{t, i} : SX.Run}) -> {SX.ltn(i, SX.LP.m(lp)) == True{} : Bool}:
  RN.ltn_le_trans(i, SP.blen(RN.viols(SX.LP.qs(lp), SX.Tab.rows(t), SX.LP.v0(lp), SX.LP.v1(lp))), SX.LP.m(lp), RN.first_lt(RN.viols(SX.LP.qs(lp), SX.Tab.rows(t), SX.LP.v0(lp), SX.LP.v1(lp)), i, u_first(lp, t, i, h)), RN.blen_viols(SX.LP.qs(lp), SX.Tab.rows(t), SX.LP.v0(lp), SX.LP.v1(lp)))

def u_hr(+lp: SX.LP, +t: SX.Tab, +i: Nat, +h: {SX.solve(lp) == SX.Unsat{t, i} : SX.Run}) -> {KA.natle(SX.LP.m(lp), SP.nrows(SX.Tab.rows(t))) == True{} : Bool}:
  %u_tab(lp, t, i, h) : {KA.natle(SX.LP.m(lp), SP.nrows(SX.Tab.rows(_))) == True{} : Bool}
  RN.hr_at(lp, PH.pow2(SX.LP.nv(lp)))

# below its bound
def u_viol(+lp: SX.LP, +t: SX.Tab, +i: Nat, +h: {SX.solve(lp) == SX.Unsat{t, i} : SX.Run}) -> {SX.viol(SX.rowat(SX.Tab.rows(t), i), SX.LP.v0(lp), SX.LP.v1(lp), RN.qat(SX.LP.qs(lp), i)) == True{} : Bool}:
  %RN.bat_viols(SX.LP.qs(lp), SX.Tab.rows(t), SX.LP.v0(lp), SX.LP.v1(lp), i, u_lt(lp, t, i, h), u_hr(lp, t, i, h)) : {_ == True{} : Bool}
  RN.first_some(RN.viols(SX.LP.qs(lp), SX.Tab.rows(t), SX.LP.v0(lp), SX.LP.v1(lp)), i, u_first(lp, t, i, h))

def u_i2(~F: O.OField, +lp: SX.LP, +t: SX.Tab, +i: Nat, +h: {SX.solve(lp) == SX.Unsat{t, i} : SX.Run}) -> SP.I2(~F, lp, SX.Tab.rows(t)):
  %u_tab(lp, t, i, h) : SP.I2(~F, lp, SX.Tab.rows(_))
  RN.i2_at(~F, lp, PH.pow2(SX.LP.nv(lp)))

def u_nr(+lp: SX.LP, +t: SX.Tab, +i: Nat, +h: {SX.solve(lp) == SX.Unsat{t, i} : SX.Run}) -> {SP.nrows(SX.Tab.rows(t)) == SX.LP.nv(lp) : Nat}:
  %u_tab(lp, t, i, h) : {SP.nrows(SX.Tab.rows(_)) == SX.LP.nv(lp) : Nat}
  RN.nr_at(lp, PH.pow2(SX.LP.nv(lp)))

# Integers through a field
# ------------------------

def zinj.go(~F: O.OField, o: Cmp, +a: S.Z, +b: S.Z, ho: {S.Z.cmp(a, b) == o : Cmp}, +h: {O.ofz(~F, a) == O.ofz(~F, b) : O.C(F)}) -> {a == b : S.Z}:
  match o:
    case LT{}:
      absurd({a == b : S.Z}, O.lt_irrefl(F)(O.ofz(~F, b))((%h : O.lt(F, _, O.ofz(~F, b))
        LX.zlt_f(~F, a, b, ho))))
    case EQ{}:
      ZO.sub_eq(a, b, ZO.eq_zero(a, b, ho))
    case GT{}:
      absurd({a == b : S.Z}, O.lt_irrefl(F)(O.ofz(~F, b))((%h : O.lt(F, O.ofz(~F, b), _)
        LX.zgt_f(~F, a, b, ho))))

def zinj(~F: O.OField, +a: S.Z, +b: S.Z, h: {O.ofz(~F, a) == O.ofz(~F, b) : O.C(F)}) -> {a == b : S.Z}:
  zinj.go(~F, S.Z.cmp(a, b), a, b, {==}, h)

def ofz_cong(~F: O.OField, +a: S.Z, +b: S.Z, e: {a == b : S.Z}) -> {O.ofz(~F, a) == O.ofz(~F, b) : O.C(F)}:
  %e : {O.ofz(~F, a) == O.ofz(~F, _) : O.C(F)}
  {==}

# x = (y / d) in a field, so d x = y
def rv_mul(~F: O.OField, +d: S.Pos, +x: S.Z, +y: S.Z, h: {O.ofz(~F, x) == O.mul(F, O.ofz(~F, y), O.inv(F, O.ofp(~F, d))) : O.C(F)}) -> {S.Z.mul(S.Zpos{d}, x) == y : S.Z}:
  zinj(~F, S.Z.mul(S.Zpos{d}, x), y,
    (%FR.ofz_mul(~F, S.Zpos{d}, x) : {_ == O.ofz(~F, y) : O.C(F)}
      FO.eq_of_sub(~F, O.mul(F, O.ofp(~F, d), O.ofz(~F, x)), O.ofz(~F, y), FO.cert2(~F, O.sub(~F, O.mul(F, O.ofp(~F, d), O.ofz(~F, x)), O.ofz(~F, y)), O.ofp(~F, d), O.sub(~F, O.ofz(~F, x), O.mul(F, O.ofz(~F, y), O.inv(F, O.ofp(~F, d)))), O.ofz(~F, y), O.sub(~F, O.mul(F, O.ofp(~F, d), O.inv(F, O.ofp(~F, d))), O.one(F)), FR.fring_eq(~F, [O.ofp(~F, d), O.ofz(~F, x), O.ofz(~F, y), O.inv(F, O.ofp(~F, d))], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZSub{E.ZVar{1n}, E.ZMul{E.ZVar{2n}, E.ZVar{3n}}}}, E.ZMul{E.ZVar{2n}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), FO.sub_of_eq(~F, O.ofz(~F, x), O.mul(F, O.ofz(~F, y), O.inv(F, O.ofp(~F, d))), h), QE.ofp_rel(~F, d)))))

# The y columns cancel
# --------------------

# entry l of every a_k
def acol(qs: List<&2, SX.Ineq>, +l: Nat) -> List<&2, S.Z>:
  match qs:
    case Nil{}:
      Nil{}
    case Con{SX.Ineq{a, b, s}, t}:
      Con{SX.at(a, l), acol(t, l)}

def vlen_acol(qs: List<&2, SX.Ineq>, +l: Nat) -> {SX.vlen(acol(qs, l)) == SX.qlen(qs) : Nat}:
  match qs:
    case Nil{}:
      {==}
    case Con{SX.Ineq{a, b, s}, +t}:
      %vlen_acol(t, l) : {1n+SX.vlen(acol(t, l)) == 1n+_ : Nat}
      {==}

def dot_zeros_r(u: List<&2, S.Z>, j: Nat) -> {S.Z0{} == SX.dot(u, EL.zeros(j)) : S.Z}:
  match u j:
    case Nil{} j:
      dot_nil_l(EL.zeros(j))
    case Con{x, t} 0n:
      {==}
    case Con{+x, t} 1n+k:
      %dot_zeros_r(t, k) : {S.Z0{} == S.Z.add(S.Z.mul(x, S.Z0{}), _) : S.Z}
      R.ring_eq([x], E.ZCst{S.Z0{}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}}, {==})

def dot_unit(a: List<&2, S.Z>, n: Nat, l: Nat, h: {SX.ltn(l, n) == True{} : Bool}) -> {SX.dot(a, SX.unit(n, l)) == SX.at(a, l) : S.Z}:
  match a n l:
    case Nil{} n l:
      Equal.sym(S.Z, S.Z0{}, SX.dot(Nil{}, SX.unit(n, l)), dot_nil_l(SX.unit(n, l)))
    case Con{x, t} 0n l:
      absurd({SX.dot(Con{x, t}, SX.unit(0n, l)) == SX.at(Con{x, t}, l) : S.Z}, KA.ft(SP.ltn0(l, h)))
    case Con{+x, +t} 1n+j 0n:
      %dot_zeros_r(t, j) : {S.Z.add(S.Z.mul(x, S.Zpos{S.XH{}}), _) == x : S.Z}
      R.ring_eq([x], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZCst{S.Z0{}}}, E.ZVar{0n}, {==})
    case Con{+x, +t} 1n+j 1n++g:
      %Equal.sym(S.Z, SX.dot(t, SX.unit(j, g)), SX.at(t, g), dot_unit(t, j, g, h)) : {S.Z.add(S.Z.mul(x, S.Z0{}), _) == SX.at(t, g) : S.Z}
      R.ring_eq([x, SX.at(t, g)], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZVar{1n}}, E.ZVar{1n}, {==})

def dot_cat_zeros(m: Nat, +a: List<&2, S.Z>, A: List<&2, S.Z>, +U: List<&2, S.Z>, h: {KA.nateq(SX.vlen(A), m) == True{} : Bool}) -> {SX.dot(SX.cat(EL.zeros(m), a), SX.cat(A, U)) == SX.dot(a, U) : S.Z}:
  match m A:
    case 0n Nil{}:
      {==}
    case 0n Con{y, s}:
      absurd({SX.dot(a, SX.cat(Con{y, s}, U)) == SX.dot(a, U) : S.Z}, KA.ft(h))
    case 1n+k Nil{}:
      absurd({SX.dot(SX.cat(EL.zeros(1n+k), a), U) == SX.dot(a, U) : S.Z}, KA.ft(h))
    case 1n+k Con{y, s}:
      dot_cat_zeros(k, a, s, U, h)

def dot_cat_short(u: List<&2, S.Z>, A: List<&2, S.Z>, +U: List<&2, S.Z>, h: {KA.natle(SX.vlen(u), SX.vlen(A)) == True{} : Bool}) -> {SX.dot(u, SX.cat(A, U)) == SX.dot(u, A) : S.Z}:
  match u A:
    case Nil{} Nil{}:
      Equal.sym(S.Z, S.Z0{}, SX.dot(Nil{}, U), dot_nil_l(U))
    case Nil{} Con{y, s}:
      {==}
    case Con{x, t} Nil{}:
      absurd({SX.dot(Con{x, t}, U) == S.Z0{} : S.Z}, KA.ft(h))
    case Con{+x, t} Con{+y, s}:
      %dot_cat_short(t, s, U, h) : {S.Z.add(S.Z.mul(x, y), SX.dot(t, SX.cat(s, U))) == S.Z.add(S.Z.mul(x, y), _) : S.Z}
      {==}

# the point with y = e_l is in V: slack k is a_k . e_l = (a_k)_l
def pt_entry(~F: O.OField, +m: Nat, +n: Nat, +l: Nat, +a: List<&2, S.Z>, +A: List<&2, S.Z>, hA: {KA.nateq(SX.vlen(A), m) == True{} : Bool}, hl: {SX.ltn(l, n) == True{} : Bool})
  -> {O.ofz(~F, SX.at(a, l)) == SP.zdot(~F, SX.cat(EL.zeros(m), a), RN.zv(~F, SX.cat(A, SX.unit(n, l)))) : O.C(F)}:
  Equal.trans(O.C(F), O.ofz(~F, SX.at(a, l)), O.ofz(~F, SX.dot(SX.cat(EL.zeros(m), a), SX.cat(A, SX.unit(n, l)))), SP.zdot(~F, SX.cat(EL.zeros(m), a), RN.zv(~F, SX.cat(A, SX.unit(n, l)))),
    ofz_cong(~F, SX.at(a, l), SX.dot(SX.cat(EL.zeros(m), a), SX.cat(A, SX.unit(n, l))),
      Equal.trans(S.Z, SX.at(a, l), SX.dot(a, SX.unit(n, l)), SX.dot(SX.cat(EL.zeros(m), a), SX.cat(A, SX.unit(n, l))),
        Equal.sym(S.Z, SX.dot(a, SX.unit(n, l)), SX.at(a, l), dot_unit(a, n, l, hl)),
        Equal.sym(S.Z, SX.dot(SX.cat(EL.zeros(m), a), SX.cat(A, SX.unit(n, l))), SX.dot(a, SX.unit(n, l)), dot_cat_zeros(m, a, A, SX.unit(n, l), hA)))),
    RN.zdot_zv(~F, SX.cat(EL.zeros(m), a), SX.cat(A, SX.unit(n, l))))

def inv_pt(~F: O.OField, qs: List<&2, SX.Ineq>, +m: Nat, +n: Nat, +l: Nat, +A: List<&2, S.Z>, +hA: {KA.nateq(SX.vlen(A), m) == True{} : Bool}, +hl: {SX.ltn(l, n) == True{} : Bool})
  -> SP.invg(~F, qs, m, RN.zv(~F, SX.cat(A, SX.unit(n, l))), RN.zv(~F, SX.cat(acol(qs, l), SX.unit(n, l)))):
  match qs:
    case Nil{}:
      Unit{}
    case Con{SX.Ineq{+a, b, s}, +qt}:
      (pt_entry(~F, m, n, l, a, A, hA, hl), inv_pt(~F, qt, m, n, l, A, hA, hl))


def u_inv(~F: O.OField, +lp: SX.LP, +l: Nat, hl: {SX.ltn(l, SX.LP.n(lp)) == True{} : Bool}) -> SP.InV(~F, lp, RN.zv(~F, SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l)))):
  inv_pt(~F, SX.LP.qs(lp), SX.LP.m(lp), SX.LP.n(lp), l, acol(SX.LP.qs(lp), l), KA.nateq_of(SX.vlen(acol(SX.LP.qs(lp), l)), SX.qlen(SX.LP.qs(lp)), vlen_acol(SX.LP.qs(lp), l)), hl)

# row i read at that point
def u_row(~F: O.OField, +lp: SX.LP, +t: SX.Tab, +i: Nat, +h: {SX.solve(lp) == SX.Unsat{t, i} : SX.Run}, +l: Nat, hl: {SX.ltn(l, SX.LP.n(lp)) == True{} : Bool}) -> {O.ofz(~F, SX.at(SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l)), i)) == SP.rv(~F, SX.rowat(SX.Tab.rows(t), i), RN.zv(~F, SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l)))) : O.C(F)}:
  %Equal.sym(O.C(F), O.ofz(~F, SX.at(SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l)), i)), SP.fat(~F, RN.zv(~F, SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l))), i), RN.fat_zv(~F, SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l)), i)) : {_ == SP.rv(~F, SX.rowat(SX.Tab.rows(t), i), RN.zv(~F, SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l)))) : O.C(F)}
  SP.agree_at(~F, SX.Tab.rows(t), RN.zv(~F, SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l))), RN.zv(~F, SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l))), i, u_i2(~F, lp, t, i, h)(RN.zv(~F, SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l))), u_inv(~F, lp, l, hl)),
    RN.ltn_le_trans(i, SX.LP.m(lp), SP.nrows(SX.Tab.rows(t)), u_lt(lp, t, i, h), u_hr(lp, t, i, h)))

def u_rowz(~F: O.OField, +lp: SX.LP, +t: SX.Tab, +i: Nat, +h: {SX.solve(lp) == SX.Unsat{t, i} : SX.Run}, +l: Nat, hl: {SX.ltn(l, SX.LP.n(lp)) == True{} : Bool}) -> {S.Z.mul(S.Zpos{SX.Rw.d(SX.rowat(SX.Tab.rows(t), i))}, SX.at(SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l)), i)) == SX.dot(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l))) : S.Z}:
  rv_mul(~F, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.at(SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l)), i), SX.dot(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l))),
    (%Equal.sym(O.C(F), O.ofz(~F, SX.dot(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l)))), SP.zdot(~F, SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), RN.zv(~F, SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l)))), RN.zdot_zv(~F, SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l)))) : {O.ofz(~F, SX.at(SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l)), i)) == O.mul(F, _, O.inv(F, O.ofp(~F, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i))))) : O.C(F)}
      u_row(~F, lp, t, i, h, l, hl)))

def cancel_r(+a: S.Z, +b: S.Z, h: {S.Z.add(a, b) == b : S.Z}) -> {a == S.Z0{} : S.Z}:
  Equal.trans(S.Z, a, S.Z.sub(S.Z.add(a, b), b), S.Z0{}, R.ring_eq([a, b], E.ZVar{0n}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{1n}}, {==}),
    (%Equal.sym(S.Z, S.Z.add(a, b), b, h) : {S.Z.sub(_, b) == S.Z0{} : S.Z}
      R.ring_eq([b], E.ZSub{E.ZVar{0n}, E.ZVar{0n}}, E.ZCst{S.Z0{}}, {==})))

# sum_k mu_k (a_k)_l = 0 for every y column l
def unsat_cols(~F: O.OField, +lp: SX.LP, +t: SX.Tab, +i: Nat, +h: {SX.solve(lp) == SX.Unsat{t, i} : SX.Run}, +l: Nat, +hl: {SX.ltn(l, SX.LP.n(lp)) == True{} : Bool}) -> {SX.dot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n), acol(SX.LP.qs(lp), l)) == S.Z0{} : S.Z}:
  Equal.trans(S.Z, SX.dot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n), acol(SX.LP.qs(lp), l)), SX.dot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n), SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l))), S.Z0{},
    Equal.sym(S.Z, SX.dot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n), SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l))), SX.dot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n), acol(SX.LP.qs(lp), l)), dot_cat_short(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n), acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l),
      (%Equal.sym(Nat, SX.vlen(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n)), SX.LP.m(lp), vlen_mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n)) : {KA.natle(_, SX.vlen(acol(SX.LP.qs(lp), l))) == True{} : Bool}
       %Equal.sym(Nat, SX.vlen(acol(SX.LP.qs(lp), l)), SX.qlen(SX.LP.qs(lp)), vlen_acol(SX.LP.qs(lp), l)) : {KA.natle(SX.LP.m(lp), _) == True{} : Bool}
       KA.natle_refl(SX.LP.m(lp))))),
    cancel_r(SX.dot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n), SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l))), SX.dot(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l))),
      Equal.trans(S.Z, S.Z.add(SX.dot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n), SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l))), SX.dot(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l)))), S.Z.mul(S.Zpos{SX.Rw.d(SX.rowat(SX.Tab.rows(t), i))}, SX.at(SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l)), i)), SX.dot(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l))),
        mdot(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), SX.cat(acol(SX.LP.qs(lp), l), SX.unit(SX.LP.n(lp), l)), u_lt(lp, t, i, h), u_enter(lp, t, i, h)), u_rowz(~F, lp, t, i, h, l, hl))))

# the multipliers are >= 0
def unsat_nn(+lp: SX.LP, +t: SX.Tab, +i: Nat, +h: {SX.solve(lp) == SX.Unsat{t, i} : SX.Run}) -> {znn(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n)) == True{} : Bool}:
  mults_nn(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n, SX.LP.m(lp), u_enter(lp, t, i, h),
    (%Equal.sym(Nat, BL.plus(SX.LP.m(lp), 0n), SX.LP.m(lp), TP.plus0(SX.LP.m(lp))) : {KA.natle(_, SX.LP.m(lp)) == True{} : Bool}
      KA.natle_refl(SX.LP.m(lp))))

# The constant's sign
# -------------------

def bcol(qs: List<&2, SX.Ineq>) -> List<&2, S.Z>:
  match qs:
    case Nil{}:
      Nil{}
    case Con{SX.Ineq{a, b, s}, t}:
      Con{b, bcol(t)}

def scol(qs: List<&2, SX.Ineq>) -> List<&2, S.Z>:
  match qs:
    case Nil{}:
      Nil{}
    case Con{SX.Ineq{a, b, s}, t}:
      Con{SX.ind(s), scol(t)}

def dot_bnd0(u: List<&2, S.Z>, qs: List<&2, SX.Ineq>, +n: Nat) -> {SX.dot(u, SX.bnd0(qs, n)) == S.Z.neg(SX.dot(u, bcol(qs))) : S.Z}:
  match u qs:
    case Nil{} Nil{}:
      Equal.sym(S.Z, S.Z0{}, SX.dot(Nil{}, EL.zeros(n)), dot_nil_l(EL.zeros(n)))
    case Nil{} Con{SX.Ineq{a, b, s}, qt}:
      {==}
    case Con{x, t} Nil{}:
      Equal.sym(S.Z, S.Z0{}, SX.dot(Con{x, t}, EL.zeros(n)), dot_zeros_r(Con{x, t}, n))
    case Con{+x, +t} Con{SX.Ineq{a, +b, s}, +qt}:
      %Equal.sym(S.Z, SX.dot(t, SX.bnd0(qt, n)), S.Z.neg(SX.dot(t, bcol(qt))), dot_bnd0(t, qt, n)) : {S.Z.add(S.Z.mul(x, S.Z.neg(b)), _) == S.Z.neg(S.Z.add(S.Z.mul(x, b), SX.dot(t, bcol(qt)))) : S.Z}
      R.ring_eq([x, b, SX.dot(t, bcol(qt))], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZNeg{E.ZVar{1n}}}, E.ZNeg{E.ZVar{2n}}}, E.ZNeg{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}, {==})

def dot_bnd1(u: List<&2, S.Z>, qs: List<&2, SX.Ineq>, +n: Nat) -> {SX.dot(u, SX.bnd1(qs, n)) == SX.dot(u, scol(qs)) : S.Z}:
  match u qs:
    case Nil{} Nil{}:
      Equal.sym(S.Z, S.Z0{}, SX.dot(Nil{}, EL.zeros(n)), dot_nil_l(EL.zeros(n)))
    case Nil{} Con{SX.Ineq{a, b, s}, qt}:
      {==}
    case Con{x, t} Nil{}:
      Equal.sym(S.Z, S.Z0{}, SX.dot(Con{x, t}, EL.zeros(n)), dot_zeros_r(Con{x, t}, n))
    case Con{+x, +t} Con{SX.Ineq{a, b, +s}, +qt}:
      %dot_bnd1(t, qt, n) : {S.Z.add(S.Z.mul(x, SX.ind(s)), SX.dot(t, SX.bnd1(qt, n))) == S.Z.add(S.Z.mul(x, SX.ind(s)), _) : S.Z}
      {==}

def lexgo_cong(o: Cmp, +b1: S.Z, +b2: S.Z, +c1: S.Z, +c2: S.Z, e: {S.Z.cmp(b1, b2) == S.Z.cmp(c1, c2) : Cmp}) -> {SX.lexlt.go(o, b1, b2) == SX.lexlt.go(o, c1, c2) : Bool}:
  match o:
    case LT{}:
      {==}
    case EQ{}:
      %e : {SX.islt(S.Z.cmp(b1, b2)) == SX.islt(_) : Bool}
      {==}
    case GT{}:
      {==}

def lexlt_cong(+a1: S.Z, +b1: S.Z, +a2: S.Z, +b2: S.Z, +c1: S.Z, +d1: S.Z, +c2: S.Z, +d2: S.Z, e1: {S.Z.cmp(a1, a2) == S.Z.cmp(c1, c2) : Cmp}, e2: {S.Z.cmp(b1, b2) == S.Z.cmp(d1, d2) : Cmp}) -> {SX.lexlt(a1, b1, a2, b2) == SX.lexlt(c1, d1, c2, d2) : Bool}:
  %e1 : {SX.lexlt.go(S.Z.cmp(a1, a2), b1, b2) == SX.lexlt.go(_, d1, d2) : Bool}
  lexgo_cong(S.Z.cmp(a1, a2), b1, b2, d1, d2, e2)

def sub_of_add(+k: S.Z, +a: S.Z, +c: S.Z, h: {S.Z.add(k, a) == c : S.Z}) -> {S.Z.sub(c, a) == k : S.Z}:
  %h : {S.Z.sub(_, a) == k : S.Z}
  R.ring_eq([k, a], E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{1n}}, E.ZVar{0n}, {==})

# k + a = c: a against c compares as 0 against k
def cmp_shift(+a: S.Z, +c: S.Z, +k: S.Z, h: {S.Z.add(k, a) == c : S.Z}) -> {S.Z.cmp(a, c) == S.Z.cmp(S.Z0{}, k) : Cmp}:
  Equal.trans(Cmp, S.Z.cmp(a, c), S.Z.cmp(S.Z0{}, S.Z.sub(c, a)), S.Z.cmp(S.Z0{}, k), ZO.cmp_sub(a, c),
    (%sub_of_add(k, a, c, h) : {S.Z.cmp(S.Z0{}, S.Z.sub(c, a)) == S.Z.cmp(S.Z0{}, _) : Cmp}
      {==}))

# below its bound, as K = sum mu_k b_k and S = sum mu_k [s_k strict]:
# K < 0, or K = 0 and S > 0
def lex_of(r: SX.Rw, q: SX.Ineq, +v0: List<&2, S.Z>, +v1: List<&2, S.Z>, +K: S.Z, +T: S.Z, hv: {SX.viol(r, v0, v1, q) == True{} : Bool},
  h0: {S.Z.add(S.Z.neg(K), SX.dot(SX.Rw.m(r), v0)) == S.Z.mul(S.Zpos{SX.Rw.d(r)}, S.Z.neg(RN.Ineq.b(q))) : S.Z},
  h1: {S.Z.add(T, SX.dot(SX.Rw.m(r), v1)) == S.Z.mul(S.Zpos{SX.Rw.d(r)}, SX.ind(RN.Ineq.s(q))) : S.Z})
  -> {SX.lexlt(K, S.Z0{}, S.Z0{}, T) == True{} : Bool}:
  match r q:
    case SX.Rw{+d, +mm} SX.Ineq{a, +b, +s}:
      %Equal.sym(Bool, SX.lexlt(K, S.Z0{}, S.Z0{}, T), SX.lexlt(SX.dot(mm, v0), SX.dot(mm, v1), S.Z.mul(S.Zpos{d}, S.Z.neg(b)), S.Z.mul(S.Zpos{d}, SX.ind(s))),
          lexlt_cong(K, S.Z0{}, S.Z0{}, T, SX.dot(mm, v0), SX.dot(mm, v1), S.Z.mul(S.Zpos{d}, S.Z.neg(b)), S.Z.mul(S.Zpos{d}, SX.ind(s)),
            Equal.trans(Cmp, S.Z.cmp(K, S.Z0{}), S.Z.cmp(S.Z0{}, S.Z.neg(K)), S.Z.cmp(SX.dot(mm, v0), S.Z.mul(S.Zpos{d}, S.Z.neg(b))), ZO.cmp_sub(K, S.Z0{}),
              Equal.sym(Cmp, S.Z.cmp(SX.dot(mm, v0), S.Z.mul(S.Zpos{d}, S.Z.neg(b))), S.Z.cmp(S.Z0{}, S.Z.neg(K)), cmp_shift(SX.dot(mm, v0), S.Z.mul(S.Zpos{d}, S.Z.neg(b)), S.Z.neg(K), h0))),
            Equal.sym(Cmp, S.Z.cmp(SX.dot(mm, v1), S.Z.mul(S.Zpos{d}, SX.ind(s))), S.Z.cmp(S.Z0{}, T), cmp_shift(SX.dot(mm, v1), S.Z.mul(S.Zpos{d}, SX.ind(s)), T, h1))))
        : {_ == True{} : Bool}
      hv


def unsat_lex(+lp: SX.LP, +t: SX.Tab, +i: Nat, +h: {SX.solve(lp) == SX.Unsat{t, i} : SX.Run}) -> {SX.lexlt(SX.dot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n), bcol(SX.LP.qs(lp))), S.Z0{}, S.Z0{}, SX.dot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n), scol(SX.LP.qs(lp)))) == True{} : Bool}:
  lex_of(SX.rowat(SX.Tab.rows(t), i), RN.qat(SX.LP.qs(lp), i), SX.LP.v0(lp), SX.LP.v1(lp), SX.dot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n), bcol(SX.LP.qs(lp))), SX.dot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n), scol(SX.LP.qs(lp))), u_viol(lp, t, i, h),
    (%dot_bnd0(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n), SX.LP.qs(lp), SX.LP.n(lp)) : {S.Z.add(_, SX.dot(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.LP.v0(lp))) == S.Z.mul(S.Zpos{SX.Rw.d(SX.rowat(SX.Tab.rows(t), i))}, S.Z.neg(RN.Ineq.b(RN.qat(SX.LP.qs(lp), i)))) : S.Z}
     %RN.at_bnd0(SX.LP.qs(lp), SX.LP.n(lp), i, u_lt(lp, t, i, h)) : {S.Z.add(SX.dot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n), SX.LP.v0(lp)), SX.dot(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.LP.v0(lp))) == S.Z.mul(S.Zpos{SX.Rw.d(SX.rowat(SX.Tab.rows(t), i))}, _) : S.Z}
     mdot(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), SX.LP.v0(lp), u_lt(lp, t, i, h), u_enter(lp, t, i, h))),
    (%dot_bnd1(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n), SX.LP.qs(lp), SX.LP.n(lp)) : {S.Z.add(_, SX.dot(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.LP.v1(lp))) == S.Z.mul(S.Zpos{SX.Rw.d(SX.rowat(SX.Tab.rows(t), i))}, SX.ind(RN.Ineq.s(RN.qat(SX.LP.qs(lp), i)))) : S.Z}
     %RN.at_bnd1(SX.LP.qs(lp), SX.LP.n(lp), i, u_lt(lp, t, i, h)) : {S.Z.add(SX.dot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), 0n), SX.LP.v1(lp)), SX.dot(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), SX.LP.v1(lp))) == S.Z.mul(S.Zpos{SX.Rw.d(SX.rowat(SX.Tab.rows(t), i))}, _) : S.Z}
     mdot(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.LP.m(lp), SX.LP.v1(lp), u_lt(lp, t, i, h), u_enter(lp, t, i, h))))
