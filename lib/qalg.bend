# bend-cad: small rational identities, each proven once by the normalizer
# on few atoms (lib/qring.bend), for chaining. The normalizer cross-
# multiplies every atom's denominator, so its cost climbs steeply with the
# atoms and the degree; a long identity is cheaper as a chain of these
# with congruences (lib/q.bend). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ./q.bend as LQ
import ./qring.bend as QR

# (a + b) + (c + d) = (a + c) + (b + d)
def m4(+a: S.Q, +b: S.Q, +c: S.Q, +d: S.Q) -> S.Q.eq(S.Q.add(S.Q.add(a, b), S.Q.add(c, d)), S.Q.add(S.Q.add(a, c), S.Q.add(b, d))):
  QR.qring_eq([a, b, c, d], E.QAdd{E.QAdd{E.QVar{0n}, E.QVar{1n}}, E.QAdd{E.QVar{2n}, E.QVar{3n}}}, E.QAdd{E.QAdd{E.QVar{0n}, E.QVar{2n}}, E.QAdd{E.QVar{1n}, E.QVar{3n}}}, {==})

# (x + y) z = x z + y z
def rdist(+x: S.Q, +y: S.Q, +z: S.Q) -> S.Q.eq(S.Q.mul(S.Q.add(x, y), z), S.Q.add(S.Q.mul(x, z), S.Q.mul(y, z))):
  QR.qring_eq([x, y, z], E.QMul{E.QAdd{E.QVar{0n}, E.QVar{1n}}, E.QVar{2n}}, E.QAdd{E.QMul{E.QVar{0n}, E.QVar{2n}}, E.QMul{E.QVar{1n}, E.QVar{2n}}}, {==})

# x (y + z) = x y + x z
def ldist(+x: S.Q, +y: S.Q, +z: S.Q) -> S.Q.eq(S.Q.mul(x, S.Q.add(y, z)), S.Q.add(S.Q.mul(x, y), S.Q.mul(x, z))):
  QR.qring_eq([x, y, z], E.QMul{E.QVar{0n}, E.QAdd{E.QVar{1n}, E.QVar{2n}}}, E.QAdd{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QMul{E.QVar{0n}, E.QVar{2n}}}, {==})

# (x y) z = x (y z)
def massoc(+x: S.Q, +y: S.Q, +z: S.Q) -> S.Q.eq(S.Q.mul(S.Q.mul(x, y), z), S.Q.mul(x, S.Q.mul(y, z))):
  QR.qring_eq([x, y, z], E.QMul{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QVar{2n}}, E.QMul{E.QVar{0n}, E.QMul{E.QVar{1n}, E.QVar{2n}}}, {==})

# x (y z) = y (x z)
def mswap(+x: S.Q, +y: S.Q, +z: S.Q) -> S.Q.eq(S.Q.mul(x, S.Q.mul(y, z)), S.Q.mul(y, S.Q.mul(x, z))):
  QR.qring_eq([x, y, z], E.QMul{E.QVar{0n}, E.QMul{E.QVar{1n}, E.QVar{2n}}}, E.QMul{E.QVar{1n}, E.QMul{E.QVar{0n}, E.QVar{2n}}}, {==})

# 1 x = x
def one_mul(+x: S.Q) -> S.Q.eq(S.Q.mul(S.Q{S.Zpos{S.XH{}}, S.XH{}}, x), x):
  QR.qring_eq([x], E.QMul{E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}, E.QVar{0n}}, E.QVar{0n}, {==})

# congruence of a sum in both places
def add_cong(+a: S.Q, +a2: S.Q, +b: S.Q, +b2: S.Q, ha: S.Q.eq(a, a2), hb: S.Q.eq(b, b2)) -> S.Q.eq(S.Q.add(a, b), S.Q.add(a2, b2)):
  LQ.q_trans(S.Q.add(a, b), S.Q.add(a2, b), S.Q.add(a2, b2), LQ.q_add_cong_l(a, a2, b, ha), LQ.q_add_cong_r(a2, b, b2, hb))
