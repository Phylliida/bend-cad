# Demo: the ring normalizer proving identities in every ordered field, one
# call each. Lagrange's identity |u|²|v|² = dot(u, v)² + cross(u, v)², and
# the reflection matrix squaring to |w|⁴ times the identity (one entry).

import Base
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../lib/fring.bend as FR

def v(i: Nat) -> E.ZExpr:
  E.ZVar{i}

def add(a: E.ZExpr, b: E.ZExpr) -> E.ZExpr:
  E.ZAdd{a, b}

def sub(a: E.ZExpr, b: E.ZExpr) -> E.ZExpr:
  E.ZSub{a, b}

def mul(a: E.ZExpr, b: E.ZExpr) -> E.ZExpr:
  E.ZMul{a, b}

def sq(+a: E.ZExpr) -> E.ZExpr:
  E.ZMul{a, a}

# (a² + b²)(c² + d²) = (ac + bd)² + (ad - bc)²
def lagrange(~F: O.OField, +a: O.C(F), +b: O.C(F), +c: O.C(F), +d: O.C(F)) -> {O.mul(F, O.add(F, O.mul(F, a, a), O.mul(F, b, b)), O.add(F, O.mul(F, c, c), O.mul(F, d, d))) == O.add(F, O.mul(F, O.add(F, O.mul(F, a, c), O.mul(F, b, d)), O.add(F, O.mul(F, a, c), O.mul(F, b, d))), O.mul(F, O.sub(~F, O.mul(F, a, d), O.mul(F, b, c)), O.sub(~F, O.mul(F, a, d), O.mul(F, b, c)))) : O.C(F)}:
  FR.fring_eq(~F, [a, b, c, d],
    mul(add(sq(v(0n)), sq(v(1n))), add(sq(v(2n)), sq(v(3n)))),
    add(sq(add(mul(v(0n), v(2n)), mul(v(1n), v(3n)))), sq(sub(mul(v(0n), v(3n)), mul(v(1n), v(2n))))),
    {==})

# with R̂ = [[x² - y², 2xy], [2xy, y² - x²]], (R̂²)₁₁ = (x² + y²)²
def reflect(~F: O.OField, +x: O.C(F), +y: O.C(F)) -> {O.add(F, O.mul(F, O.sub(~F, O.mul(F, x, x), O.mul(F, y, y)), O.sub(~F, O.mul(F, x, x), O.mul(F, y, y))), O.mul(F, O.add(F, O.mul(F, x, y), O.mul(F, x, y)), O.add(F, O.mul(F, x, y), O.mul(F, x, y)))) == O.mul(F, O.add(F, O.mul(F, x, x), O.mul(F, y, y)), O.add(F, O.mul(F, x, x), O.mul(F, y, y))) : O.C(F)}:
  FR.fring_eq(~F, [x, y],
    add(sq(sub(sq(v(0n)), sq(v(1n)))), sq(add(mul(v(0n), v(1n)), mul(v(0n), v(1n))))),
    sq(add(sq(v(0n)), sq(v(1n)))),
    {==})
