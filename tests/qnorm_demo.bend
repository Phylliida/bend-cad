# Demo: lib/qnorm.bend deciding rational identities, the shape of sk-13's
# certificates (h g = Σ q g_i + k, DESIGN §8.11). The checker computes each
# qzero; qzero_ok then gives the identity in every ordered field.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../lib/qnorm.bend as QN

def v(i: Nat) -> E.QExpr:
  E.QVar{i}

def add(a: E.QExpr, b: E.QExpr) -> E.QExpr:
  E.QAdd{a, b}

def sub(a: E.QExpr, b: E.QExpr) -> E.QExpr:
  E.QSub{a, b}

def mul(a: E.QExpr, b: E.QExpr) -> E.QExpr:
  E.QMul{a, b}

# n/d
def q(n: S.Z, d: S.Pos) -> E.QExpr:
  E.QCst{S.Q{n, d}}

def three() -> S.Pos:
  S.XI{S.XH{}}

def four() -> S.Pos:
  S.XO{S.XO{S.XH{}}}

def seven() -> S.Pos:
  S.XI{S.XI{S.XH{}}}

def eight() -> S.Pos:
  S.XO{S.XO{S.XO{S.XH{}}}}

# HDistance a-b 3, b-c 4, a-c d: g1 = x1 - x0 - 3, g2 = x2 - x1 - 4,
# g3 = x2 - x0 - d
def g1() -> E.QExpr:
  sub(sub(v(1n), v(0n)), q(S.Zpos{three()}, S.XH{}))

def g2() -> E.QExpr:
  sub(sub(v(2n), v(1n)), q(S.Zpos{four()}, S.XH{}))

def g3(d: S.Pos) -> E.QExpr:
  sub(sub(v(2n), v(0n)), q(S.Zpos{d}, S.XH{}))

# d = 7: g3 = g1 + g2, an implied equation (k = 0)
def implied() -> {QN.qzero(sub(g3(seven()), add(g1(), g2()))) == True{} : Bool}:
  {==}

# d = 8: g3 - (g1 + g2) = -1, a conflict, so not identically 0
def conflict() -> {QN.qzero(sub(g3(eight()), add(g1(), g2()))) == False{} : Bool}:
  {==}

# the conflict's certificate, with k = -1 moved over: identically 0
def conflict_k() -> {QN.qzero(add(sub(g3(eight()), add(g1(), g2())), q(S.Zpos{S.XH{}}, S.XH{}))) == True{} : Bool}:
  {==}

# half multipliers and unreduced constants: (1/2)(x0 + x0) - (2/2) x0 -
# (0/3) x1 = 0
def halves() -> {QN.qzero(sub(sub(mul(q(S.Zpos{S.XH{}}, S.XO{S.XH{}}), add(v(0n), v(0n))), mul(q(S.Zpos{S.XO{S.XH{}}}, S.XO{S.XH{}}), v(0n))), mul(q(S.Z0{}, three()), v(1n)))) == True{} : Bool}:
  {==}

# and a near miss: (1/2)(x0 + x0) - (2/4) x0 is x0 / 2, not 0
def near_miss() -> {QN.qzero(sub(mul(q(S.Zpos{S.XH{}}, S.XO{S.XH{}}), add(v(0n), v(0n))), mul(q(S.Zpos{S.XO{S.XH{}}}, four()), v(0n)))) == False{} : Bool}:
  {==}

# a product identity: (x0 + x1)(x0 - x1) - (x0² - x1²) = 0
def squares() -> {QN.qzero(sub(mul(add(v(0n), v(1n)), sub(v(0n), v(1n))), sub(mul(v(0n), v(0n)), mul(v(1n), v(1n))))) == True{} : Bool}:
  {==}

# and its use: the implied equation holds in every ordered field wherever
# the other two do
def implied_ok(~F: O.OField, +env: List<&2, O.C(F)>) -> {O.eval(~F, env, sub(g3(seven()), add(g1(), g2()))) == O.zero(F) : O.C(F)}:
  QN.qzero_ok(~F, env, sub(g3(seven()), add(g1(), g2())), implied())
