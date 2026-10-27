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

# x (-y) = -(x y)
def mneg(+x: S.Q, +y: S.Q) -> S.Q.eq(S.Q.mul(x, S.Q.neg(y)), S.Q.neg(S.Q.mul(x, y))):
  QR.qring_eq([x, y], E.QMul{E.QVar{0n}, E.QNeg{E.QVar{1n}}}, E.QNeg{E.QMul{E.QVar{0n}, E.QVar{1n}}}, {==})

# x (y - z) = x y - x z
def ldsub(+x: S.Q, +y: S.Q, +z: S.Q) -> S.Q.eq(S.Q.mul(x, S.Q.sub(y, z)), S.Q.sub(S.Q.mul(x, y), S.Q.mul(x, z))):
  QR.qring_eq([x, y, z], E.QMul{E.QVar{0n}, E.QSub{E.QVar{1n}, E.QVar{2n}}}, E.QSub{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QMul{E.QVar{0n}, E.QVar{2n}}}, {==})

# (x - y) z = x z - y z
def rdsub(+x: S.Q, +y: S.Q, +z: S.Q) -> S.Q.eq(S.Q.mul(S.Q.sub(x, y), z), S.Q.sub(S.Q.mul(x, z), S.Q.mul(y, z))):
  QR.qring_eq([x, y, z], E.QMul{E.QSub{E.QVar{0n}, E.QVar{1n}}, E.QVar{2n}}, E.QSub{E.QMul{E.QVar{0n}, E.QVar{2n}}, E.QMul{E.QVar{1n}, E.QVar{2n}}}, {==})

# (a - b) - (c + d) = (a - c) - (b + d)
def r4a(+a: S.Q, +b: S.Q, +c: S.Q, +d: S.Q) -> S.Q.eq(S.Q.sub(S.Q.sub(a, b), S.Q.add(c, d)), S.Q.sub(S.Q.sub(a, c), S.Q.add(b, d))):
  QR.qring_eq([a, b, c, d], E.QSub{E.QSub{E.QVar{0n}, E.QVar{1n}}, E.QAdd{E.QVar{2n}, E.QVar{3n}}}, E.QSub{E.QSub{E.QVar{0n}, E.QVar{2n}}, E.QAdd{E.QVar{1n}, E.QVar{3n}}}, {==})

# (a - b) + (c + d) = (c + a) + (d - b)
def r4b(+a: S.Q, +b: S.Q, +c: S.Q, +d: S.Q) -> S.Q.eq(S.Q.add(S.Q.sub(a, b), S.Q.add(c, d)), S.Q.add(S.Q.add(c, a), S.Q.sub(d, b))):
  QR.qring_eq([a, b, c, d], E.QAdd{E.QSub{E.QVar{0n}, E.QVar{1n}}, E.QAdd{E.QVar{2n}, E.QVar{3n}}}, E.QAdd{E.QAdd{E.QVar{2n}, E.QVar{0n}}, E.QSub{E.QVar{3n}, E.QVar{1n}}}, {==})

# congruence of a difference in both places
def sub_cong(+a: S.Q, +a2: S.Q, +b: S.Q, +b2: S.Q, ha: S.Q.eq(a, a2), hb: S.Q.eq(b, b2)) -> S.Q.eq(S.Q.sub(a, b), S.Q.sub(a2, b2)):
  add_cong(a, a2, S.Q.neg(b), S.Q.neg(b2), ha, LQ.q_neg_cong(b, b2, hb))

# x (y z) = (x y) z
def ma(+x: S.Q, +y: S.Q, +z: S.Q) -> S.Q.eq(S.Q.mul(x, S.Q.mul(y, z)), S.Q.mul(S.Q.mul(x, y), z)):
  LQ.q_sym(S.Q.mul(S.Q.mul(x, y), z), S.Q.mul(x, S.Q.mul(y, z)), massoc(x, y, z))

# chains of three and four steps
def ch3(+a: S.Q, +b: S.Q, +c: S.Q, +d: S.Q, h1: S.Q.eq(a, b), h2: S.Q.eq(b, c), h3: S.Q.eq(c, d)) -> S.Q.eq(a, d):
  LQ.q_trans(a, c, d, LQ.q_trans(a, b, c, h1, h2), h3)

def ch4(+a: S.Q, +b: S.Q, +c: S.Q, +d: S.Q, +e: S.Q, h1: S.Q.eq(a, b), h2: S.Q.eq(b, c), h3: S.Q.eq(c, d), h4: S.Q.eq(d, e)) -> S.Q.eq(a, e):
  LQ.q_trans(a, d, e, ch3(a, b, c, d, h1, h2, h3), h4)

# -(a + b) = -a + -b
def negadd(+a: S.Q, +b: S.Q) -> S.Q.eq(S.Q.neg(S.Q.add(a, b)), S.Q.add(S.Q.neg(a), S.Q.neg(b))):
  QR.qring_eq([a, b], E.QNeg{E.QAdd{E.QVar{0n}, E.QVar{1n}}}, E.QAdd{E.QNeg{E.QVar{0n}}, E.QNeg{E.QVar{1n}}}, {==})

# (a + b) - (c + d) = (a - c) + (b - d)
def r4c(+a: S.Q, +b: S.Q, +c: S.Q, +d: S.Q) -> S.Q.eq(S.Q.sub(S.Q.add(a, b), S.Q.add(c, d)), S.Q.add(S.Q.sub(a, c), S.Q.sub(b, d))):
  QR.qring_eq([a, b, c, d], E.QSub{E.QAdd{E.QVar{0n}, E.QVar{1n}}, E.QAdd{E.QVar{2n}, E.QVar{3n}}}, E.QAdd{E.QSub{E.QVar{0n}, E.QVar{2n}}, E.QSub{E.QVar{1n}, E.QVar{3n}}}, {==})

# (a - b) - (d - e) = (a - d) - (b - e)
def r4d(+a: S.Q, +b: S.Q, +d: S.Q, +e: S.Q) -> S.Q.eq(S.Q.sub(S.Q.sub(a, b), S.Q.sub(d, e)), S.Q.sub(S.Q.sub(a, d), S.Q.sub(b, e))):
  QR.qring_eq([a, b, d, e], E.QSub{E.QSub{E.QVar{0n}, E.QVar{1n}}, E.QSub{E.QVar{2n}, E.QVar{3n}}}, E.QSub{E.QSub{E.QVar{0n}, E.QVar{2n}}, E.QSub{E.QVar{1n}, E.QVar{3n}}}, {==})
