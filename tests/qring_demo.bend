# Demos of the rational tactic (lib/qring.bend): identities up to Q.eq, each
# one qring_eq call.

import Base
import ../lib/qring.bend as QR
import ../spec/num.bend as S
import ../spec/ring.bend as E

def third() -> S.Q:
  S.Q{S.Zpos{S.XH{}}, S.XI{S.XH{}}}

def two_thirds() -> S.Q:
  S.Q{S.Zpos{S.XO{S.XH{}}}, S.XI{S.XH{}}}

def one() -> S.Q:
  S.Q{S.Zpos{S.XH{}}, S.XH{}}

# x/3 + 2x/3 = x
def thirds(+x: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(x, third()), S.Q.mul(x, two_thirds())), x):
  QR.qring_eq([x], E.QAdd{E.QMul{E.QVar{0n}, E.QCst{third()}}, E.QMul{E.QVar{0n}, E.QCst{two_thirds()}}}, E.QVar{0n}, {==})

# (x + y)^2 - (x - y)^2 = 4xy
def polar(+x: S.Q, +y: S.Q) -> S.Q.eq(S.Q.sub(S.Q.mul(S.Q.add(x, y), S.Q.add(x, y)), S.Q.mul(S.Q.sub(x, y), S.Q.sub(x, y))), S.Q.mul(S.Q{S.Zpos{S.XO{S.XO{S.XH{}}}}, S.XH{}}, S.Q.mul(x, y))):
  QR.qring_eq([x, y],
    E.QSub{E.QMul{E.QAdd{E.QVar{0n}, E.QVar{1n}}, E.QAdd{E.QVar{0n}, E.QVar{1n}}}, E.QMul{E.QSub{E.QVar{0n}, E.QVar{1n}}, E.QSub{E.QVar{0n}, E.QVar{1n}}}},
    E.QMul{E.QCst{S.Q{S.Zpos{S.XO{S.XO{S.XH{}}}}, S.XH{}}}, E.QMul{E.QVar{0n}, E.QVar{1n}}},
    {==})

# x - x = 0
def sub_self(+x: S.Q) -> S.Q.eq(S.Q.sub(x, x), S.Q{S.Z0{}, S.XH{}}):
  QR.qring_eq([x], E.QSub{E.QVar{0n}, E.QVar{0n}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}, {==})

# midpoint: (a + b)/2 - a = (b - a)/2
def mid(+a: S.Q, +b: S.Q) -> S.Q.eq(S.Q.sub(S.Q.mul(S.Q.add(a, b), S.Q{S.Zpos{S.XH{}}, S.XO{S.XH{}}}), a), S.Q.mul(S.Q.sub(b, a), S.Q{S.Zpos{S.XH{}}, S.XO{S.XH{}}})):
  QR.qring_eq([a, b],
    E.QSub{E.QMul{E.QAdd{E.QVar{0n}, E.QVar{1n}}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XO{S.XH{}}}}}, E.QVar{0n}},
    E.QMul{E.QSub{E.QVar{1n}, E.QVar{0n}}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XO{S.XH{}}}}},
    {==})

def main() -> Nat:
  0n
