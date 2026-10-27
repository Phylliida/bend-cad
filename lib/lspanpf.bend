# bend-cad: spans of labels for the closure theorem (PLAN-sk13b B3). The
# link checks compare a basis of {w : w z in a set} with the stored links'
# labels through qspan; here, what those answers mean:
# - LSp(u0, u1, v): v is a real combination of u0 and u1 (Data);
# - qspan is sound: one stored label u0 and lpar(u0, w) give w a real
#   multiple of u0; two, independent (the pair invariant), give w by
#   Cramer;
# - the bases are complete: every v with v z in the set is a real
#   combination of the basis ([w, i w], [w], or none, then v = 0);
# - a label test finding nothing means only v = 0 has v z in the set.
# Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./q.bend as LQ
import ./qring.bend as QR
import ./qalg.bend as QA
import ./identpf.bend as ID
import ./lab.bend as LB
import ./labpf.bend as LP
import ./labnzpf.bend as NZ
import ./labalgpf.bend as LA
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./indsetpf.bend as IP
import ./dcgenpf.bend as GN
import ./dcmergepf.bend as MG

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Rational identities
# -------------------

# x + 0 0 = x
def q.a00(+x: S.Q) -> S.Q.eq(S.Q.add(x, S.Q.mul(DR.qz(), DR.qz())), x):
  QR.qring_eq([x], E.QAdd{E.QVar{0n}, E.QMul{E.QCst{DR.qz()}, E.QCst{DR.qz()}}}, E.QVar{0n}, {==})

# (A I) x + (B I) y = I (A x + B y)
def q.fac(+A: S.Q, +B: S.Q, +I: S.Q, +x: S.Q, +y: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(S.Q.mul(A, I), x), S.Q.mul(S.Q.mul(B, I), y)), S.Q.mul(I, S.Q.add(S.Q.mul(A, x), S.Q.mul(B, y)))):
  QR.qring_eq([A, B, I, x, y], E.QAdd{E.QMul{E.QMul{E.QVar{0n}, E.QVar{2n}}, E.QVar{3n}}, E.QMul{E.QMul{E.QVar{1n}, E.QVar{2n}}, E.QVar{4n}}}, E.QMul{E.QVar{2n}, E.QAdd{E.QMul{E.QVar{0n}, E.QVar{3n}}, E.QMul{E.QVar{1n}, E.QVar{4n}}}}, {==})

# (A I) x = I (A x)
def q.fac1(+A: S.Q, +I: S.Q, +x: S.Q) -> S.Q.eq(S.Q.mul(S.Q.mul(A, I), x), S.Q.mul(I, S.Q.mul(A, x))):
  QR.qring_eq([A, I, x], E.QMul{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QVar{2n}}, E.QMul{E.QVar{1n}, E.QMul{E.QVar{0n}, E.QVar{2n}}}, {==})

# I (c N) = c (N I)
def q.icn(+I: S.Q, +c: S.Q, +N: S.Q) -> S.Q.eq(S.Q.mul(I, S.Q.mul(c, N)), S.Q.mul(c, S.Q.mul(N, I))):
  QR.qring_eq([I, c, N], E.QMul{E.QVar{0n}, E.QMul{E.QVar{1n}, E.QVar{2n}}}, E.QMul{E.QVar{1n}, E.QMul{E.QVar{2n}, E.QVar{0n}}}, {==})

# c 1 = c
def q.m1(+c: S.Q) -> S.Q.eq(S.Q.mul(c, DR.qo()), c):
  QR.qring_eq([c], E.QMul{E.QVar{0n}, E.QCst{DR.qo()}}, E.QVar{0n}, {==})

# c N + s0 0 = c N
def q.cz(+c: S.Q, +N: S.Q, +s0: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(c, N), S.Q.mul(s0, DR.qz())), S.Q.mul(c, N)):
  QR.qring_eq([c, N, s0], E.QAdd{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QMul{E.QVar{2n}, E.QCst{DR.qz()}}}, E.QMul{E.QVar{0n}, E.QVar{1n}}, {==})

# s N - c0 0 = s N
def q.sz(+s: S.Q, +N: S.Q, +c0: S.Q) -> S.Q.eq(S.Q.sub(S.Q.mul(s, N), S.Q.mul(c0, DR.qz())), S.Q.mul(s, N)):
  QR.qring_eq([s, N, c0], E.QSub{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QMul{E.QVar{2n}, E.QCst{DR.qz()}}}, E.QMul{E.QVar{0n}, E.QVar{1n}}, {==})

def q.p2a(+x: S.Q, +y: S.Q) -> S.Q.eq(S.Q.mul(S.Q.mul(x, y), x), S.Q.mul(y, S.Q.mul(x, x))):
  QR.qring_eq([x, y], E.QMul{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QVar{0n}}, E.QMul{E.QVar{1n}, E.QMul{E.QVar{0n}, E.QVar{0n}}}, {==})

def q.p2b(+x: S.Q, +y: S.Q) -> S.Q.eq(S.Q.mul(x, S.Q.mul(y, y)), S.Q.mul(y, S.Q.mul(y, x))):
  QR.qring_eq([x, y], E.QMul{E.QVar{0n}, E.QMul{E.QVar{1n}, E.QVar{1n}}}, E.QMul{E.QVar{1n}, E.QMul{E.QVar{1n}, E.QVar{0n}}}, {==})

def q.p3a(+x: S.Q, +y: S.Q, +z: S.Q) -> S.Q.eq(S.Q.mul(S.Q.mul(x, y), z), S.Q.mul(x, S.Q.mul(z, y))):
  QR.qring_eq([x, y, z], E.QMul{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QVar{2n}}, E.QMul{E.QVar{0n}, E.QMul{E.QVar{2n}, E.QVar{1n}}}, {==})

# (A + X) + (B - X) = A + B, backwards
def q.c3(+A: S.Q, +X: S.Q, +B: S.Q) -> S.Q.eq(S.Q.add(A, B), S.Q.add(S.Q.add(A, X), S.Q.sub(B, X))):
  QR.qring_eq([A, X, B], E.QAdd{E.QVar{0n}, E.QVar{2n}}, E.QAdd{E.QAdd{E.QVar{0n}, E.QVar{1n}}, E.QSub{E.QVar{2n}, E.QVar{1n}}}, {==})

# C + B = (A + B) - (A - C)
def q.c4(+A: S.Q, +B: S.Q, +C: S.Q) -> S.Q.eq(S.Q.add(C, B), S.Q.sub(S.Q.add(A, B), S.Q.sub(A, C))):
  QR.qring_eq([A, B, C], E.QAdd{E.QVar{2n}, E.QVar{1n}}, E.QSub{E.QAdd{E.QVar{0n}, E.QVar{1n}}, E.QSub{E.QVar{0n}, E.QVar{2n}}}, {==})

def q.par.c(+c: S.Q, +s: S.Q, +c0: S.Q, +s0: S.Q) -> S.Q.eq(S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), c0), S.Q.add(S.Q.mul(c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(s0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c))))):
  LQ.q_trans(S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), c0), S.Q.add(S.Q.mul(c, S.Q.mul(c0, c0)), S.Q.mul(s0, S.Q.mul(c0, s))), S.Q.add(S.Q.mul(c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(s0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)))),
    LQ.q_trans(S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), c0), S.Q.add(S.Q.mul(S.Q.mul(c0, c), c0), S.Q.mul(S.Q.mul(s0, s), c0)), S.Q.add(S.Q.mul(c, S.Q.mul(c0, c0)), S.Q.mul(s0, S.Q.mul(c0, s))),
      QA.rdist(S.Q.mul(c0, c), S.Q.mul(s0, s), c0),
      QA.add_cong(S.Q.mul(S.Q.mul(c0, c), c0), S.Q.mul(c, S.Q.mul(c0, c0)), S.Q.mul(S.Q.mul(s0, s), c0), S.Q.mul(s0, S.Q.mul(c0, s)), q.p2a(c0, c), q.p3a(s0, s, c0))),
    QA.ch3(S.Q.add(S.Q.mul(c, S.Q.mul(c0, c0)), S.Q.mul(s0, S.Q.mul(c0, s))), S.Q.add(S.Q.add(S.Q.mul(c, S.Q.mul(c0, c0)), S.Q.mul(c, S.Q.mul(s0, s0))), S.Q.sub(S.Q.mul(s0, S.Q.mul(c0, s)), S.Q.mul(c, S.Q.mul(s0, s0)))), S.Q.add(S.Q.add(S.Q.mul(c, S.Q.mul(c0, c0)), S.Q.mul(c, S.Q.mul(s0, s0))), S.Q.sub(S.Q.mul(s0, S.Q.mul(c0, s)), S.Q.mul(s0, S.Q.mul(s0, c)))), S.Q.add(S.Q.mul(c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(s0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)))),
      q.c3(S.Q.mul(c, S.Q.mul(c0, c0)), S.Q.mul(c, S.Q.mul(s0, s0)), S.Q.mul(s0, S.Q.mul(c0, s))),
      LQ.q_add_cong_r(S.Q.add(S.Q.mul(c, S.Q.mul(c0, c0)), S.Q.mul(c, S.Q.mul(s0, s0))), S.Q.sub(S.Q.mul(s0, S.Q.mul(c0, s)), S.Q.mul(c, S.Q.mul(s0, s0))), S.Q.sub(S.Q.mul(s0, S.Q.mul(c0, s)), S.Q.mul(s0, S.Q.mul(s0, c))), QA.sub_cong(S.Q.mul(s0, S.Q.mul(c0, s)), S.Q.mul(s0, S.Q.mul(c0, s)), S.Q.mul(c, S.Q.mul(s0, s0)), S.Q.mul(s0, S.Q.mul(s0, c)), LQ.q_refl(S.Q.mul(s0, S.Q.mul(c0, s))), q.p2b(c, s0))),
      QA.add_cong(S.Q.add(S.Q.mul(c, S.Q.mul(c0, c0)), S.Q.mul(c, S.Q.mul(s0, s0))), S.Q.mul(c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.sub(S.Q.mul(s0, S.Q.mul(c0, s)), S.Q.mul(s0, S.Q.mul(s0, c))), S.Q.mul(s0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c))),
        LQ.q_sym(S.Q.mul(c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.add(S.Q.mul(c, S.Q.mul(c0, c0)), S.Q.mul(c, S.Q.mul(s0, s0))), QA.ldist(c, S.Q.mul(c0, c0), S.Q.mul(s0, s0))),
        LQ.q_sym(S.Q.mul(s0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c))), S.Q.sub(S.Q.mul(s0, S.Q.mul(c0, s)), S.Q.mul(s0, S.Q.mul(s0, c))), QA.ldsub(s0, S.Q.mul(c0, s), S.Q.mul(s0, c))))))

def q.p2c(+x: S.Q, +y: S.Q) -> S.Q.eq(S.Q.mul(x, S.Q.mul(y, y)), S.Q.mul(y, S.Q.mul(y, x))):
  QR.qring_eq([x, y], E.QMul{E.QVar{0n}, E.QMul{E.QVar{1n}, E.QVar{1n}}}, E.QMul{E.QVar{1n}, E.QMul{E.QVar{1n}, E.QVar{0n}}}, {==})

def q.par.s(+c: S.Q, +s: S.Q, +c0: S.Q, +s0: S.Q) -> S.Q.eq(S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), s0), S.Q.sub(S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(c0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c))))):
  QA.ch4(S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), s0), S.Q.add(S.Q.mul(S.Q.mul(c0, c), s0), S.Q.mul(S.Q.mul(s0, s), s0)), S.Q.add(S.Q.mul(c0, S.Q.mul(s0, c)), S.Q.mul(s, S.Q.mul(s0, s0))), S.Q.sub(S.Q.add(S.Q.mul(s, S.Q.mul(c0, c0)), S.Q.mul(s, S.Q.mul(s0, s0))), S.Q.sub(S.Q.mul(s, S.Q.mul(c0, c0)), S.Q.mul(c0, S.Q.mul(s0, c)))),
    S.Q.sub(S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(c0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)))),
    QA.rdist(S.Q.mul(c0, c), S.Q.mul(s0, s), s0),
    QA.add_cong(S.Q.mul(S.Q.mul(c0, c), s0), S.Q.mul(c0, S.Q.mul(s0, c)), S.Q.mul(S.Q.mul(s0, s), s0), S.Q.mul(s, S.Q.mul(s0, s0)), q.p3a(c0, c, s0), q.p2a(s0, s)),
    q.c4(S.Q.mul(s, S.Q.mul(c0, c0)), S.Q.mul(s, S.Q.mul(s0, s0)), S.Q.mul(c0, S.Q.mul(s0, c))),
    LQ.q_trans(S.Q.sub(S.Q.add(S.Q.mul(s, S.Q.mul(c0, c0)), S.Q.mul(s, S.Q.mul(s0, s0))), S.Q.sub(S.Q.mul(s, S.Q.mul(c0, c0)), S.Q.mul(c0, S.Q.mul(s0, c)))), S.Q.sub(S.Q.add(S.Q.mul(s, S.Q.mul(c0, c0)), S.Q.mul(s, S.Q.mul(s0, s0))), S.Q.sub(S.Q.mul(c0, S.Q.mul(c0, s)), S.Q.mul(c0, S.Q.mul(s0, c)))), S.Q.sub(S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(c0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)))),
      QA.sub_cong(S.Q.add(S.Q.mul(s, S.Q.mul(c0, c0)), S.Q.mul(s, S.Q.mul(s0, s0))), S.Q.add(S.Q.mul(s, S.Q.mul(c0, c0)), S.Q.mul(s, S.Q.mul(s0, s0))), S.Q.sub(S.Q.mul(s, S.Q.mul(c0, c0)), S.Q.mul(c0, S.Q.mul(s0, c))), S.Q.sub(S.Q.mul(c0, S.Q.mul(c0, s)), S.Q.mul(c0, S.Q.mul(s0, c))), LQ.q_refl(S.Q.add(S.Q.mul(s, S.Q.mul(c0, c0)), S.Q.mul(s, S.Q.mul(s0, s0)))), QA.sub_cong(S.Q.mul(s, S.Q.mul(c0, c0)), S.Q.mul(c0, S.Q.mul(c0, s)), S.Q.mul(c0, S.Q.mul(s0, c)), S.Q.mul(c0, S.Q.mul(s0, c)), q.p2c(s, c0), LQ.q_refl(S.Q.mul(c0, S.Q.mul(s0, c))))),
      QA.sub_cong(S.Q.add(S.Q.mul(s, S.Q.mul(c0, c0)), S.Q.mul(s, S.Q.mul(s0, s0))), S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.sub(S.Q.mul(c0, S.Q.mul(c0, s)), S.Q.mul(c0, S.Q.mul(s0, c))), S.Q.mul(c0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c))),
        LQ.q_sym(S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.add(S.Q.mul(s, S.Q.mul(c0, c0)), S.Q.mul(s, S.Q.mul(s0, s0))), QA.ldist(s, S.Q.mul(c0, c0), S.Q.mul(s0, s0))),
        LQ.q_sym(S.Q.mul(c0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c))), S.Q.sub(S.Q.mul(c0, S.Q.mul(c0, s)), S.Q.mul(c0, S.Q.mul(s0, c))), QA.ldsub(c0, S.Q.mul(c0, s), S.Q.mul(s0, c))))))

def q.cr3a(+x: S.Q, +y: S.Q, +z: S.Q) -> S.Q.eq(S.Q.mul(S.Q.mul(x, y), z), S.Q.mul(x, S.Q.mul(z, y))):
  QR.qring_eq([x, y, z], E.QMul{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QVar{2n}}, E.QMul{E.QVar{0n}, E.QMul{E.QVar{2n}, E.QVar{1n}}}, {==})

def q.cr3b(+x: S.Q, +y: S.Q, +z: S.Q) -> S.Q.eq(S.Q.mul(S.Q.mul(x, y), z), S.Q.mul(S.Q.mul(z, x), y)):
  QR.qring_eq([x, y, z], E.QMul{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QVar{2n}}, E.QMul{E.QMul{E.QVar{2n}, E.QVar{0n}}, E.QVar{1n}}, {==})

def q.cr3c(+x: S.Q, +y: S.Q, +z: S.Q) -> S.Q.eq(S.Q.mul(S.Q.mul(x, y), z), S.Q.mul(y, S.Q.mul(x, z))):
  QR.qring_eq([x, y, z], E.QMul{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QVar{2n}}, E.QMul{E.QVar{1n}, E.QMul{E.QVar{0n}, E.QVar{2n}}}, {==})

# (A - X) + (X - B) = A - B
def q.cancel(+A: S.Q, +X: S.Q, +B: S.Q) -> S.Q.eq(S.Q.add(S.Q.sub(A, X), S.Q.sub(X, B)), S.Q.sub(A, B)):
  QR.qring_eq([A, X, B], E.QAdd{E.QSub{E.QVar{0n}, E.QVar{1n}}, E.QSub{E.QVar{1n}, E.QVar{2n}}}, E.QSub{E.QVar{0n}, E.QVar{2n}}, {==})

def q.cr.c(+c: S.Q, +s: S.Q, +c0: S.Q, +s0: S.Q, +c1: S.Q, +s1: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), c0), S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), c1)), S.Q.mul(c, S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))):
  QA.ch4(S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), c0), S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), c1)),
    S.Q.add(S.Q.sub(S.Q.mul(S.Q.mul(c, s1), c0), S.Q.mul(S.Q.mul(s, c1), c0)), S.Q.sub(S.Q.mul(S.Q.mul(c0, s), c1), S.Q.mul(S.Q.mul(s0, c), c1))),
    S.Q.add(S.Q.sub(S.Q.mul(c, S.Q.mul(c0, s1)), S.Q.mul(S.Q.mul(c0, s), c1)), S.Q.sub(S.Q.mul(S.Q.mul(c0, s), c1), S.Q.mul(c, S.Q.mul(s0, c1)))),
    S.Q.sub(S.Q.mul(c, S.Q.mul(c0, s1)), S.Q.mul(c, S.Q.mul(s0, c1))),
    S.Q.mul(c, S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))),
    QA.add_cong(S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), c0), S.Q.sub(S.Q.mul(S.Q.mul(c, s1), c0), S.Q.mul(S.Q.mul(s, c1), c0)), S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), c1), S.Q.sub(S.Q.mul(S.Q.mul(c0, s), c1), S.Q.mul(S.Q.mul(s0, c), c1)),
      QA.rdsub(S.Q.mul(c, s1), S.Q.mul(s, c1), c0), QA.rdsub(S.Q.mul(c0, s), S.Q.mul(s0, c), c1)),
    QA.add_cong(S.Q.sub(S.Q.mul(S.Q.mul(c, s1), c0), S.Q.mul(S.Q.mul(s, c1), c0)), S.Q.sub(S.Q.mul(c, S.Q.mul(c0, s1)), S.Q.mul(S.Q.mul(c0, s), c1)), S.Q.sub(S.Q.mul(S.Q.mul(c0, s), c1), S.Q.mul(S.Q.mul(s0, c), c1)), S.Q.sub(S.Q.mul(S.Q.mul(c0, s), c1), S.Q.mul(c, S.Q.mul(s0, c1))),
      QA.sub_cong(S.Q.mul(S.Q.mul(c, s1), c0), S.Q.mul(c, S.Q.mul(c0, s1)), S.Q.mul(S.Q.mul(s, c1), c0), S.Q.mul(S.Q.mul(c0, s), c1), q.cr3a(c, s1, c0), q.cr3b(s, c1, c0)),
      QA.sub_cong(S.Q.mul(S.Q.mul(c0, s), c1), S.Q.mul(S.Q.mul(c0, s), c1), S.Q.mul(S.Q.mul(s0, c), c1), S.Q.mul(c, S.Q.mul(s0, c1)), LQ.q_refl(S.Q.mul(S.Q.mul(c0, s), c1)), q.cr3c(s0, c, c1))),
    q.cancel(S.Q.mul(c, S.Q.mul(c0, s1)), S.Q.mul(S.Q.mul(c0, s), c1), S.Q.mul(c, S.Q.mul(s0, c1))),
    LQ.q_sym(S.Q.mul(c, S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), S.Q.sub(S.Q.mul(c, S.Q.mul(c0, s1)), S.Q.mul(c, S.Q.mul(s0, c1))), QA.ldsub(c, S.Q.mul(c0, s1), S.Q.mul(s0, c1))))

def q.cr3d(+x: S.Q, +y: S.Q, +z: S.Q) -> S.Q.eq(S.Q.mul(S.Q.mul(x, y), z), S.Q.mul(S.Q.mul(y, z), x)):
  QR.qring_eq([x, y, z], E.QMul{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QVar{2n}}, E.QMul{E.QMul{E.QVar{1n}, E.QVar{2n}}, E.QVar{0n}}, {==})

# (P - X) + (Y - P) = Y - X
def q.cancel2(+P: S.Q, +X: S.Q, +Y: S.Q) -> S.Q.eq(S.Q.add(S.Q.sub(P, X), S.Q.sub(Y, P)), S.Q.sub(Y, X)):
  QR.qring_eq([P, X, Y], E.QAdd{E.QSub{E.QVar{0n}, E.QVar{1n}}, E.QSub{E.QVar{2n}, E.QVar{0n}}}, E.QSub{E.QVar{2n}, E.QVar{1n}}, {==})

# (c s1 - s c1) s0 + (c0 s - s0 c) s1 = s (c0 s1 - s0 c1)
def q.cr.s(+c: S.Q, +s: S.Q, +c0: S.Q, +s0: S.Q, +c1: S.Q, +s1: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), s0), S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), s1)), S.Q.mul(s, S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))):
  QA.ch4(S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), s0), S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), s1)),
    S.Q.add(S.Q.sub(S.Q.mul(S.Q.mul(c, s1), s0), S.Q.mul(S.Q.mul(s, c1), s0)), S.Q.sub(S.Q.mul(S.Q.mul(c0, s), s1), S.Q.mul(S.Q.mul(s0, c), s1))),
    S.Q.add(S.Q.sub(S.Q.mul(S.Q.mul(c, s1), s0), S.Q.mul(s, S.Q.mul(s0, c1))), S.Q.sub(S.Q.mul(s, S.Q.mul(c0, s1)), S.Q.mul(S.Q.mul(c, s1), s0))),
    S.Q.sub(S.Q.mul(s, S.Q.mul(c0, s1)), S.Q.mul(s, S.Q.mul(s0, c1))),
    S.Q.mul(s, S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))),
    QA.add_cong(S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), s0), S.Q.sub(S.Q.mul(S.Q.mul(c, s1), s0), S.Q.mul(S.Q.mul(s, c1), s0)), S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), s1), S.Q.sub(S.Q.mul(S.Q.mul(c0, s), s1), S.Q.mul(S.Q.mul(s0, c), s1)),
      QA.rdsub(S.Q.mul(c, s1), S.Q.mul(s, c1), s0), QA.rdsub(S.Q.mul(c0, s), S.Q.mul(s0, c), s1)),
    QA.add_cong(S.Q.sub(S.Q.mul(S.Q.mul(c, s1), s0), S.Q.mul(S.Q.mul(s, c1), s0)), S.Q.sub(S.Q.mul(S.Q.mul(c, s1), s0), S.Q.mul(s, S.Q.mul(s0, c1))), S.Q.sub(S.Q.mul(S.Q.mul(c0, s), s1), S.Q.mul(S.Q.mul(s0, c), s1)), S.Q.sub(S.Q.mul(s, S.Q.mul(c0, s1)), S.Q.mul(S.Q.mul(c, s1), s0)),
      QA.sub_cong(S.Q.mul(S.Q.mul(c, s1), s0), S.Q.mul(S.Q.mul(c, s1), s0), S.Q.mul(S.Q.mul(s, c1), s0), S.Q.mul(s, S.Q.mul(s0, c1)), LQ.q_refl(S.Q.mul(S.Q.mul(c, s1), s0)), q.cr3a(s, c1, s0)),
      QA.sub_cong(S.Q.mul(S.Q.mul(c0, s), s1), S.Q.mul(s, S.Q.mul(c0, s1)), S.Q.mul(S.Q.mul(s0, c), s1), S.Q.mul(S.Q.mul(c, s1), s0), q.cr3c(c0, s, s1), q.cr3d(s0, c, s1))),
    q.cancel2(S.Q.mul(S.Q.mul(c, s1), s0), S.Q.mul(s, S.Q.mul(s0, c1)), S.Q.mul(s, S.Q.mul(c0, s1))),
    LQ.q_sym(S.Q.mul(s, S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), S.Q.sub(S.Q.mul(s, S.Q.mul(c0, s1)), S.Q.mul(s, S.Q.mul(s0, c1))), QA.ldsub(s, S.Q.mul(c0, s1), S.Q.mul(s0, c1))))

# Spans of labels
# ---------------

def lab0() -> DR.Lab:
  DR.Lab{DR.qz(), DR.qz()}

def lat0(ws: List<&2, DR.Lab>) -> DR.Lab:
  match ws:
    case Con{w, t}:
      w
    case Nil{}:
      lab0()

def lat1(ws: List<&2, DR.Lab>) -> DR.Lab:
  match ws:
    case Con{w0, Con{w1, t}}:
      w1
    case _:
      lab0()

# the first two stored labels are independent
def pairok(ws: List<&2, DR.Lab>) -> Bool:
  match ws:
    case Con{w0, Con{w1, t}}:
      SV.bnot(DC.lpar(w0, w1))
    case _:
      True{}

# v is a real combination of u0 and u1
def LSp(+u0: DR.Lab, +u1: DR.Lab, +v: DR.Lab) -> Data:
  Sigma<&2, &2, DR.Lab, p => LA.LE(v, LA.lcomb(LA.lab.c(p), u0, LA.lab.s(p), u1))>

def lsp.p(+u0: DR.Lab, +u1: DR.Lab, +v: DR.Lab, h: LSp(u0, u1, v)) -> DR.Lab:
  (p, e) = h
  p

def lsp.e(+u0: DR.Lab, +u1: DR.Lab, +v: DR.Lab, h: LSp(u0, u1, v)) -> LA.LE(v, LA.lcomb(LA.lab.c(lsp.p(u0, u1, v, h)), u0, LA.lab.s(lsp.p(u0, u1, v, h)), u1)):
  (p, e) = h
  e

def bnot_f(b: Bool, h: {SV.bnot(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.sym(Bool, True{}, False{}, h)

# one stored label: w parallel to w0 is a real multiple of it
def qs1(+c0: S.Q, +s0: S.Q, +c: S.Q, +s: S.Q, +hd: LA.QE(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), DR.qz()), +hn: NZ.Nz(DR.Lab{c0, s0})) -> LSp(DR.Lab{c0, s0}, lab0(), DR.Lab{c, s}):
  (DR.Lab{S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), DR.qz()}, LA.le_of(c, s, S.Q.add(S.Q.mul(S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), c0), S.Q.mul(DR.qz(), DR.qz())), S.Q.add(S.Q.mul(S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), s0), S.Q.mul(DR.qz(), DR.qz())), LQ.q_sym(S.Q.add(S.Q.mul(S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), c0), S.Q.mul(DR.qz(), DR.qz())), c, LQ.q_trans(S.Q.add(S.Q.mul(S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), c0), S.Q.mul(DR.qz(), DR.qz())), S.Q.mul(S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), c0), c, q.a00(S.Q.mul(S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), c0)), LQ.q_trans(S.Q.mul(S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), c0), S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), c0)), c, q.fac1(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), c0), LQ.q_trans(S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), c0)), S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.add(S.Q.mul(c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(s0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c))))), c, LQ.q_mul_cong_r(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), c0), S.Q.add(S.Q.mul(c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(s0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)))), q.par.c(c, s, c0, s0)), LQ.q_trans(S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.add(S.Q.mul(c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(s0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c))))), S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.add(S.Q.mul(c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(s0, DR.qz()))), c, LQ.q_mul_cong_r(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.add(S.Q.mul(c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(s0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)))), S.Q.add(S.Q.mul(c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(s0, DR.qz())), LQ.q_add_cong_r(S.Q.mul(c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(s0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c))), S.Q.mul(s0, DR.qz()), LQ.q_mul_cong_r(s0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), DR.qz(), LA.qe_ok(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), DR.qz(), hd)))), LQ.q_trans(S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.add(S.Q.mul(c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(s0, DR.qz()))), S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), c, LQ.q_mul_cong_r(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.add(S.Q.mul(c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(s0, DR.qz())), S.Q.mul(c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), q.cz(c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)), s0)), LQ.q_trans(S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), S.Q.mul(c, S.Q.mul(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))))), c, q.icn(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), c, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), LQ.q_trans(S.Q.mul(c, S.Q.mul(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))))), S.Q.mul(c, DR.qo()), c, LQ.q_mul_cong_r(c, S.Q.mul(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), DR.qo(), LQ.q_mul_inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)), e => LP.qnz_t(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)), hn, e))), q.m1(c))))))))), LQ.q_sym(S.Q.add(S.Q.mul(S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), s0), S.Q.mul(DR.qz(), DR.qz())), s, LQ.q_trans(S.Q.add(S.Q.mul(S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), s0), S.Q.mul(DR.qz(), DR.qz())), S.Q.mul(S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), s0), s, q.a00(S.Q.mul(S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), s0)), LQ.q_trans(S.Q.mul(S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), s0), S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), s0)), s, q.fac1(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), s0), LQ.q_trans(S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), s0)), S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.sub(S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(c0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c))))), s, LQ.q_mul_cong_r(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(S.Q.add(S.Q.mul(c0, c), S.Q.mul(s0, s)), s0), S.Q.sub(S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(c0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)))), q.par.s(c, s, c0, s0)), LQ.q_trans(S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.sub(S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(c0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c))))), S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.sub(S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(c0, DR.qz()))), s, LQ.q_mul_cong_r(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.sub(S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(c0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)))), S.Q.sub(S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(c0, DR.qz())), QA.sub_cong(S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(c0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c))), S.Q.mul(c0, DR.qz()), LQ.q_refl(S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), LQ.q_mul_cong_r(c0, S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), DR.qz(), LA.qe_ok(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), DR.qz(), hd)))), LQ.q_trans(S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.sub(S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(c0, DR.qz()))), S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), s, LQ.q_mul_cong_r(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.sub(S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(c0, DR.qz())), S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), q.sz(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)), c0)), LQ.q_trans(S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), S.Q.mul(s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), S.Q.mul(s, S.Q.mul(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))))), s, q.icn(S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), s, S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))), LQ.q_trans(S.Q.mul(s, S.Q.mul(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0))))), S.Q.mul(s, DR.qo()), s, LQ.q_mul_cong_r(s, S.Q.mul(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)), S.Q.inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)))), DR.qo(), LQ.q_mul_inv(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)), e => LP.qnz_t(S.Q.add(S.Q.mul(c0, c0), S.Q.mul(s0, s0)), hn, e))), q.m1(s)))))))))))

def qs1.go(w0: DR.Lab, w: DR.Lab, h: {DC.lpar(w0, w) == True{} : Bool}, +hn: NZ.Nz(w0)) -> LSp(w0, lab0(), w):
  match w0 w:
    case DR.Lab{+c0, +s0} DR.Lab{+c, +s}:
      qs1(c0, s0, c, s, LA.qe_of(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), DR.qz(), LP.qnz_f(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), IP.bnot_t(DR.qnz(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c))), h))), hn)

# two stored labels, independent: Cramer
def qs2(+c0: S.Q, +s0: S.Q, +c1: S.Q, +s1: S.Q, +c: S.Q, +s: S.Q, +hd: {DR.qnz(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))) == True{} : Bool}) -> LSp(DR.Lab{c0, s0}, DR.Lab{c1, s1}, DR.Lab{c, s}):
  (DR.Lab{S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))))}, LA.le_of(c, s, S.Q.add(S.Q.mul(S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), c0), S.Q.mul(S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), c1)), S.Q.add(S.Q.mul(S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), s0), S.Q.mul(S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), s1)), LQ.q_sym(S.Q.add(S.Q.mul(S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), c0), S.Q.mul(S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), c1)), c, LQ.q_trans(S.Q.add(S.Q.mul(S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), c0), S.Q.mul(S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), c1)), S.Q.mul(S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), c0), S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), c1))), c, q.fac(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), c0, c1), LQ.q_trans(S.Q.mul(S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), c0), S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), c1))), S.Q.mul(S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), S.Q.mul(c, S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), c, LQ.q_mul_cong_r(S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), c0), S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), c1)), S.Q.mul(c, S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), q.cr.c(c, s, c0, s0, c1, s1)), LQ.q_trans(S.Q.mul(S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), S.Q.mul(c, S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), S.Q.mul(c, S.Q.mul(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))))), c, q.icn(S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), c, S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), LQ.q_trans(S.Q.mul(c, S.Q.mul(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))))), S.Q.mul(c, DR.qo()), c, LQ.q_mul_cong_r(c, S.Q.mul(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), DR.qo(), LQ.q_mul_inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)), e => LP.qnz_t(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)), hd, e))), q.m1(c)))))), LQ.q_sym(S.Q.add(S.Q.mul(S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), s0), S.Q.mul(S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), s1)), s, LQ.q_trans(S.Q.add(S.Q.mul(S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), s0), S.Q.mul(S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), s1)), S.Q.mul(S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), s0), S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), s1))), s, q.fac(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), s0, s1), LQ.q_trans(S.Q.mul(S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), s0), S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), s1))), S.Q.mul(S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), S.Q.mul(s, S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), s, LQ.q_mul_cong_r(S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, s1), S.Q.mul(s, c1)), s0), S.Q.mul(S.Q.sub(S.Q.mul(c0, s), S.Q.mul(s0, c)), s1)), S.Q.mul(s, S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), q.cr.s(c, s, c0, s0, c1, s1)), LQ.q_trans(S.Q.mul(S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), S.Q.mul(s, S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), S.Q.mul(s, S.Q.mul(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))))), s, q.icn(S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), s, S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), LQ.q_trans(S.Q.mul(s, S.Q.mul(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))))), S.Q.mul(s, DR.qo()), s, LQ.q_mul_cong_r(s, S.Q.mul(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)), S.Q.inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)))), DR.qo(), LQ.q_mul_inv(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)), e => LP.qnz_t(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1)), hd, e))), q.m1(s))))))))

def qs2.go(w0: DR.Lab, w1: DR.Lab, w: DR.Lab, h: {DC.lpar(w0, w1) == False{} : Bool}) -> LSp(w0, w1, w):
  match w0 w1 w:
    case DR.Lab{+c0, +s0} DR.Lab{+c1, +s1} DR.Lab{+c, +s}:
      qs2(c0, s0, c1, s1, c, s, bnot_f(DR.qnz(S.Q.sub(S.Q.mul(c0, s1), S.Q.mul(s0, c1))), h))

# qspan is sound
def qspan_ok(ws: List<&2, DR.Lab>, +w: DR.Lab, hq: {DC.qspan(ws, w) == True{} : Bool}, hp: {pairok(ws) == True{} : Bool}, +nz: NZ.Nz(lat0(ws))) -> LSp(lat0(ws), lat1(ws), w):
  match ws:
    case Nil{}:
      absurd(LSp(lab0(), lab0(), w), LP.tf(Equal.sym(Bool, False{}, True{}, hq)))
    case Con{+w0, Nil{}}:
      qs1.go(w0, w, hq, nz)
    case Con{+w0, Con{+w1, t}}:
      qs2.go(w0, w1, w, IP.bnot_t(DC.lpar(w0, w1), hp))

# Using spans
# -----------

# a span read on forms
def lsp_form(+u0: DR.Lab, +u1: DR.Lab, +v: DR.Lab, +h: LSp(u0, u1, v), +y: SK.VE)
  -> VD.SameVD(DR.gmul(v, y), DR.vlin(LA.lab.c(lsp.p(u0, u1, v, h)), DR.gmul(u0, y), LA.lab.s(lsp.p(u0, u1, v, h)), DR.gmul(u1, y))):
  GN.samevd_tr(DR.gmul(v, y), DR.gmul(LA.lcomb(LA.lab.c(lsp.p(u0, u1, v, h)), u0, LA.lab.s(lsp.p(u0, u1, v, h)), u1), y), DR.vlin(LA.lab.c(lsp.p(u0, u1, v, h)), DR.gmul(u0, y), LA.lab.s(lsp.p(u0, u1, v, h)), DR.gmul(u1, y)),
    LA.gle(v, LA.lcomb(LA.lab.c(lsp.p(u0, u1, v, h)), u0, LA.lab.s(lsp.p(u0, u1, v, h)), u1), y, lsp.e(u0, u1, v, h)),
    LA.gmul_lin(LA.lab.c(lsp.p(u0, u1, v, h)), u0, LA.lab.s(lsp.p(u0, u1, v, h)), u1, y))

# v is 0 in both parts
def LZ(+v: DR.Lab) -> Data:
  SK.Both({DR.qnz(LA.lab.c(v)) == False{} : Bool}, {DR.qnz(LA.lab.s(v)) == False{} : Bool})

def z2.q(+a: S.Q, +b: S.Q) -> S.Q.eq(DR.qz(), S.Q.add(S.Q.mul(DR.qz(), a), S.Q.mul(DR.qz(), b))):
  QR.qring_eq([a, b], E.QCst{DR.qz()}, E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}}, {==})

def lsp_zero.go(+vc: S.Q, +vs: S.Q, +a0: S.Q, +b0: S.Q, +a1: S.Q, +b1: S.Q, +zc: {DR.qnz(vc) == False{} : Bool}, zs: {DR.qnz(vs) == False{} : Bool})
  -> LSp(DR.Lab{a0, b0}, DR.Lab{a1, b1}, DR.Lab{vc, vs}):
  (lab0(), LA.le_of(vc, vs, S.Q.add(S.Q.mul(DR.qz(), a0), S.Q.mul(DR.qz(), a1)), S.Q.add(S.Q.mul(DR.qz(), b0), S.Q.mul(DR.qz(), b1)),
    LQ.q_trans(vc, DR.qz(), S.Q.add(S.Q.mul(DR.qz(), a0), S.Q.mul(DR.qz(), a1)), LP.qnz_f(vc, zc), z2.q(a0, a1)),
    LQ.q_trans(vs, DR.qz(), S.Q.add(S.Q.mul(DR.qz(), b0), S.Q.mul(DR.qz(), b1)), LP.qnz_f(vs, zs), z2.q(b0, b1))))

# 0 is in every span
def lsp_zero(v: DR.Lab, u0: DR.Lab, u1: DR.Lab, hz: LZ(v)) -> LSp(u0, u1, v):
  match v u0 u1:
    case DR.Lab{+vc, +vs} DR.Lab{+a0, +b0} DR.Lab{+a1, +b1}:
      (+zc, zs) = hz
      lsp_zero.go(vc, vs, a0, b0, a1, b1, zc, zs)

def le.c(+g: DR.Lab, +h: DR.Lab, e: LA.LE(g, h)) -> LA.QE(LA.lab.c(g), LA.lab.c(h)):
  (a, b) = e
  a

def le.s(+g: DR.Lab, +h: DR.Lab, e: LA.LE(g, h)) -> LA.QE(LA.lab.s(g), LA.lab.s(h)):
  (a, b) = e
  b

def tr.q(+l0: S.Q, +l1: S.Q, +m0: S.Q, +m1: S.Q, +n0: S.Q, +n1: S.Q, +U0: S.Q, +U1: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(l0, S.Q.add(S.Q.mul(m0, U0), S.Q.mul(m1, U1))), S.Q.mul(l1, S.Q.add(S.Q.mul(n0, U0), S.Q.mul(n1, U1)))), S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(l0, m0), S.Q.mul(l1, n0)), U0), S.Q.mul(S.Q.add(S.Q.mul(l0, m1), S.Q.mul(l1, n1)), U1))):
  LQ.q_trans(S.Q.add(S.Q.mul(l0, S.Q.add(S.Q.mul(m0, U0), S.Q.mul(m1, U1))), S.Q.mul(l1, S.Q.add(S.Q.mul(n0, U0), S.Q.mul(n1, U1)))), S.Q.add(S.Q.add(S.Q.mul(l0, S.Q.mul(m0, U0)), S.Q.mul(l0, S.Q.mul(m1, U1))), S.Q.add(S.Q.mul(l1, S.Q.mul(n0, U0)), S.Q.mul(l1, S.Q.mul(n1, U1)))), S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(l0, m0), S.Q.mul(l1, n0)), U0), S.Q.mul(S.Q.add(S.Q.mul(l0, m1), S.Q.mul(l1, n1)), U1)), QA.add_cong(S.Q.mul(l0, S.Q.add(S.Q.mul(m0, U0), S.Q.mul(m1, U1))), S.Q.add(S.Q.mul(l0, S.Q.mul(m0, U0)), S.Q.mul(l0, S.Q.mul(m1, U1))), S.Q.mul(l1, S.Q.add(S.Q.mul(n0, U0), S.Q.mul(n1, U1))), S.Q.add(S.Q.mul(l1, S.Q.mul(n0, U0)), S.Q.mul(l1, S.Q.mul(n1, U1))), QA.ldist(l0, S.Q.mul(m0, U0), S.Q.mul(m1, U1)), QA.ldist(l1, S.Q.mul(n0, U0), S.Q.mul(n1, U1))), LQ.q_trans(S.Q.add(S.Q.add(S.Q.mul(l0, S.Q.mul(m0, U0)), S.Q.mul(l0, S.Q.mul(m1, U1))), S.Q.add(S.Q.mul(l1, S.Q.mul(n0, U0)), S.Q.mul(l1, S.Q.mul(n1, U1)))), S.Q.add(S.Q.add(S.Q.mul(l0, S.Q.mul(m0, U0)), S.Q.mul(l1, S.Q.mul(n0, U0))), S.Q.add(S.Q.mul(l0, S.Q.mul(m1, U1)), S.Q.mul(l1, S.Q.mul(n1, U1)))), S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(l0, m0), S.Q.mul(l1, n0)), U0), S.Q.mul(S.Q.add(S.Q.mul(l0, m1), S.Q.mul(l1, n1)), U1)), QA.m4(S.Q.mul(l0, S.Q.mul(m0, U0)), S.Q.mul(l0, S.Q.mul(m1, U1)), S.Q.mul(l1, S.Q.mul(n0, U0)), S.Q.mul(l1, S.Q.mul(n1, U1))), LQ.q_trans(S.Q.add(S.Q.add(S.Q.mul(l0, S.Q.mul(m0, U0)), S.Q.mul(l1, S.Q.mul(n0, U0))), S.Q.add(S.Q.mul(l0, S.Q.mul(m1, U1)), S.Q.mul(l1, S.Q.mul(n1, U1)))), S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(l0, m0), U0), S.Q.mul(S.Q.mul(l1, n0), U0)), S.Q.add(S.Q.mul(S.Q.mul(l0, m1), U1), S.Q.mul(S.Q.mul(l1, n1), U1))), S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(l0, m0), S.Q.mul(l1, n0)), U0), S.Q.mul(S.Q.add(S.Q.mul(l0, m1), S.Q.mul(l1, n1)), U1)), QA.add_cong(S.Q.add(S.Q.mul(l0, S.Q.mul(m0, U0)), S.Q.mul(l1, S.Q.mul(n0, U0))), S.Q.add(S.Q.mul(S.Q.mul(l0, m0), U0), S.Q.mul(S.Q.mul(l1, n0), U0)), S.Q.add(S.Q.mul(l0, S.Q.mul(m1, U1)), S.Q.mul(l1, S.Q.mul(n1, U1))), S.Q.add(S.Q.mul(S.Q.mul(l0, m1), U1), S.Q.mul(S.Q.mul(l1, n1), U1)), QA.add_cong(S.Q.mul(l0, S.Q.mul(m0, U0)), S.Q.mul(S.Q.mul(l0, m0), U0), S.Q.mul(l1, S.Q.mul(n0, U0)), S.Q.mul(S.Q.mul(l1, n0), U0), QA.ma(l0, m0, U0), QA.ma(l1, n0, U0)), QA.add_cong(S.Q.mul(l0, S.Q.mul(m1, U1)), S.Q.mul(S.Q.mul(l0, m1), U1), S.Q.mul(l1, S.Q.mul(n1, U1)), S.Q.mul(S.Q.mul(l1, n1), U1), QA.ma(l0, m1, U1), QA.ma(l1, n1, U1))), QA.add_cong(S.Q.add(S.Q.mul(S.Q.mul(l0, m0), U0), S.Q.mul(S.Q.mul(l1, n0), U0)), S.Q.mul(S.Q.add(S.Q.mul(l0, m0), S.Q.mul(l1, n0)), U0), S.Q.add(S.Q.mul(S.Q.mul(l0, m1), U1), S.Q.mul(S.Q.mul(l1, n1), U1)), S.Q.mul(S.Q.add(S.Q.mul(l0, m1), S.Q.mul(l1, n1)), U1), LQ.q_sym(S.Q.mul(S.Q.add(S.Q.mul(l0, m0), S.Q.mul(l1, n0)), U0), S.Q.add(S.Q.mul(S.Q.mul(l0, m0), U0), S.Q.mul(S.Q.mul(l1, n0), U0)), QA.rdist(S.Q.mul(l0, m0), S.Q.mul(l1, n0), U0)), LQ.q_sym(S.Q.mul(S.Q.add(S.Q.mul(l0, m1), S.Q.mul(l1, n1)), U1), S.Q.add(S.Q.mul(S.Q.mul(l0, m1), U1), S.Q.mul(S.Q.mul(l1, n1), U1)), QA.rdist(S.Q.mul(l0, m1), S.Q.mul(l1, n1), U1))))))

def lsp_trans.go(+vc: S.Q, +vs: S.Q, +b0c: S.Q, +b0s: S.Q, +b1c: S.Q, +b1s: S.Q, +u0c: S.Q, +u0s: S.Q, +u1c: S.Q, +u1s: S.Q, +l0: S.Q, +l1: S.Q, +m0: S.Q, +m1: S.Q, +n0: S.Q, +n1: S.Q,
  +he: LA.LE(DR.Lab{vc, vs}, LA.lcomb(l0, DR.Lab{b0c, b0s}, l1, DR.Lab{b1c, b1s})), +h0: LA.LE(DR.Lab{b0c, b0s}, LA.lcomb(m0, DR.Lab{u0c, u0s}, m1, DR.Lab{u1c, u1s})),
  +h1: LA.LE(DR.Lab{b1c, b1s}, LA.lcomb(n0, DR.Lab{u0c, u0s}, n1, DR.Lab{u1c, u1s})))
  -> LSp(DR.Lab{u0c, u0s}, DR.Lab{u1c, u1s}, DR.Lab{vc, vs}):
  (DR.Lab{S.Q.add(S.Q.mul(l0, m0), S.Q.mul(l1, n0)), S.Q.add(S.Q.mul(l0, m1), S.Q.mul(l1, n1))},
   LA.le_of(vc, vs, S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(l0, m0), S.Q.mul(l1, n0)), u0c), S.Q.mul(S.Q.add(S.Q.mul(l0, m1), S.Q.mul(l1, n1)), u1c)), S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(l0, m0), S.Q.mul(l1, n0)), u0s), S.Q.mul(S.Q.add(S.Q.mul(l0, m1), S.Q.mul(l1, n1)), u1s)),
     LQ.q_trans(vc, S.Q.add(S.Q.mul(l0, b0c), S.Q.mul(l1, b1c)), S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(l0, m0), S.Q.mul(l1, n0)), u0c), S.Q.mul(S.Q.add(S.Q.mul(l0, m1), S.Q.mul(l1, n1)), u1c)), LA.qe_ok(vc, S.Q.add(S.Q.mul(l0, b0c), S.Q.mul(l1, b1c)), le.c(DR.Lab{vc, vs}, LA.lcomb(l0, DR.Lab{b0c, b0s}, l1, DR.Lab{b1c, b1s}), he)), LQ.q_trans(S.Q.add(S.Q.mul(l0, b0c), S.Q.mul(l1, b1c)), S.Q.add(S.Q.mul(l0, S.Q.add(S.Q.mul(m0, u0c), S.Q.mul(m1, u1c))), S.Q.mul(l1, S.Q.add(S.Q.mul(n0, u0c), S.Q.mul(n1, u1c)))), S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(l0, m0), S.Q.mul(l1, n0)), u0c), S.Q.mul(S.Q.add(S.Q.mul(l0, m1), S.Q.mul(l1, n1)), u1c)), QA.add_cong(S.Q.mul(l0, b0c), S.Q.mul(l0, S.Q.add(S.Q.mul(m0, u0c), S.Q.mul(m1, u1c))), S.Q.mul(l1, b1c), S.Q.mul(l1, S.Q.add(S.Q.mul(n0, u0c), S.Q.mul(n1, u1c))), LQ.q_mul_cong_r(l0, b0c, S.Q.add(S.Q.mul(m0, u0c), S.Q.mul(m1, u1c)), LA.qe_ok(b0c, S.Q.add(S.Q.mul(m0, u0c), S.Q.mul(m1, u1c)), le.c(DR.Lab{b0c, b0s}, LA.lcomb(m0, DR.Lab{u0c, u0s}, m1, DR.Lab{u1c, u1s}), h0))), LQ.q_mul_cong_r(l1, b1c, S.Q.add(S.Q.mul(n0, u0c), S.Q.mul(n1, u1c)), LA.qe_ok(b1c, S.Q.add(S.Q.mul(n0, u0c), S.Q.mul(n1, u1c)), le.c(DR.Lab{b1c, b1s}, LA.lcomb(n0, DR.Lab{u0c, u0s}, n1, DR.Lab{u1c, u1s}), h1)))), tr.q(l0, l1, m0, m1, n0, n1, u0c, u1c))), LQ.q_trans(vs, S.Q.add(S.Q.mul(l0, b0s), S.Q.mul(l1, b1s)), S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(l0, m0), S.Q.mul(l1, n0)), u0s), S.Q.mul(S.Q.add(S.Q.mul(l0, m1), S.Q.mul(l1, n1)), u1s)), LA.qe_ok(vs, S.Q.add(S.Q.mul(l0, b0s), S.Q.mul(l1, b1s)), le.s(DR.Lab{vc, vs}, LA.lcomb(l0, DR.Lab{b0c, b0s}, l1, DR.Lab{b1c, b1s}), he)), LQ.q_trans(S.Q.add(S.Q.mul(l0, b0s), S.Q.mul(l1, b1s)), S.Q.add(S.Q.mul(l0, S.Q.add(S.Q.mul(m0, u0s), S.Q.mul(m1, u1s))), S.Q.mul(l1, S.Q.add(S.Q.mul(n0, u0s), S.Q.mul(n1, u1s)))), S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(l0, m0), S.Q.mul(l1, n0)), u0s), S.Q.mul(S.Q.add(S.Q.mul(l0, m1), S.Q.mul(l1, n1)), u1s)), QA.add_cong(S.Q.mul(l0, b0s), S.Q.mul(l0, S.Q.add(S.Q.mul(m0, u0s), S.Q.mul(m1, u1s))), S.Q.mul(l1, b1s), S.Q.mul(l1, S.Q.add(S.Q.mul(n0, u0s), S.Q.mul(n1, u1s))), LQ.q_mul_cong_r(l0, b0s, S.Q.add(S.Q.mul(m0, u0s), S.Q.mul(m1, u1s)), LA.qe_ok(b0s, S.Q.add(S.Q.mul(m0, u0s), S.Q.mul(m1, u1s)), le.s(DR.Lab{b0c, b0s}, LA.lcomb(m0, DR.Lab{u0c, u0s}, m1, DR.Lab{u1c, u1s}), h0))), LQ.q_mul_cong_r(l1, b1s, S.Q.add(S.Q.mul(n0, u0s), S.Q.mul(n1, u1s)), LA.qe_ok(b1s, S.Q.add(S.Q.mul(n0, u0s), S.Q.mul(n1, u1s)), le.s(DR.Lab{b1c, b1s}, LA.lcomb(n0, DR.Lab{u0c, u0s}, n1, DR.Lab{u1c, u1s}), h1)))), tr.q(l0, l1, m0, m1, n0, n1, u0s, u1s)))))

# spans compose
def lsp_trans(v: DR.Lab, b0: DR.Lab, b1: DR.Lab, u0: DR.Lab, u1: DR.Lab, +h: LSp(b0, b1, v), +h0: LSp(u0, u1, b0), +h1: LSp(u0, u1, b1)) -> LSp(u0, u1, v):
  match v b0 b1 u0 u1:
    case DR.Lab{+vc, +vs} DR.Lab{+b0c, +b0s} DR.Lab{+b1c, +b1s} DR.Lab{+u0c, +u0s} DR.Lab{+u1c, +u1s}:
      lsp_trans.go(vc, vs, b0c, b0s, b1c, b1s, u0c, u0s, u1c, u1s,
        LA.lab.c(lsp.p(DR.Lab{b0c, b0s}, DR.Lab{b1c, b1s}, DR.Lab{vc, vs}, h)), LA.lab.s(lsp.p(DR.Lab{b0c, b0s}, DR.Lab{b1c, b1s}, DR.Lab{vc, vs}, h)),
        LA.lab.c(lsp.p(DR.Lab{u0c, u0s}, DR.Lab{u1c, u1s}, DR.Lab{b0c, b0s}, h0)), LA.lab.s(lsp.p(DR.Lab{u0c, u0s}, DR.Lab{u1c, u1s}, DR.Lab{b0c, b0s}, h0)),
        LA.lab.c(lsp.p(DR.Lab{u0c, u0s}, DR.Lab{u1c, u1s}, DR.Lab{b1c, b1s}, h1)), LA.lab.s(lsp.p(DR.Lab{u0c, u0s}, DR.Lab{u1c, u1s}, DR.Lab{b1c, b1s}, h1)),
        lsp.e(DR.Lab{b0c, b0s}, DR.Lab{b1c, b1s}, DR.Lab{vc, vs}, h), lsp.e(DR.Lab{u0c, u0s}, DR.Lab{u1c, u1s}, DR.Lab{b0c, b0s}, h0), lsp.e(DR.Lab{u0c, u0s}, DR.Lab{u1c, u1s}, DR.Lab{b1c, b1s}, h1))

def cj.s(+vs: S.Q, +l0: S.Q, +b0s: S.Q, +l1: S.Q, +b1s: S.Q, +h: LA.QE(vs, S.Q.add(S.Q.mul(l0, b0s), S.Q.mul(l1, b1s)))) -> S.Q.eq(S.Q.neg(vs), S.Q.add(S.Q.mul(l0, S.Q.neg(b0s)), S.Q.mul(l1, S.Q.neg(b1s)))):
  QA.ch3(S.Q.neg(vs), S.Q.neg(S.Q.add(S.Q.mul(l0, b0s), S.Q.mul(l1, b1s))), S.Q.add(S.Q.neg(S.Q.mul(l0, b0s)), S.Q.neg(S.Q.mul(l1, b1s))), S.Q.add(S.Q.mul(l0, S.Q.neg(b0s)), S.Q.mul(l1, S.Q.neg(b1s))),
    LQ.q_neg_cong(vs, S.Q.add(S.Q.mul(l0, b0s), S.Q.mul(l1, b1s)), LA.qe_ok(vs, S.Q.add(S.Q.mul(l0, b0s), S.Q.mul(l1, b1s)), h)),
    QA.negadd(S.Q.mul(l0, b0s), S.Q.mul(l1, b1s)),
    QA.add_cong(S.Q.neg(S.Q.mul(l0, b0s)), S.Q.mul(l0, S.Q.neg(b0s)), S.Q.neg(S.Q.mul(l1, b1s)), S.Q.mul(l1, S.Q.neg(b1s)),
      LQ.q_sym(S.Q.mul(l0, S.Q.neg(b0s)), S.Q.neg(S.Q.mul(l0, b0s)), QA.mneg(l0, b0s)), LQ.q_sym(S.Q.mul(l1, S.Q.neg(b1s)), S.Q.neg(S.Q.mul(l1, b1s)), QA.mneg(l1, b1s))))

def lsp_conj.go(+vc: S.Q, +vs: S.Q, +b0c: S.Q, +b0s: S.Q, +b1c: S.Q, +b1s: S.Q, +l0: S.Q, +l1: S.Q, +he: LA.LE(DR.Lab{vc, vs}, LA.lcomb(l0, DR.Lab{b0c, b0s}, l1, DR.Lab{b1c, b1s})))
  -> LSp(DR.Lab{b0c, S.Q.neg(b0s)}, DR.Lab{b1c, S.Q.neg(b1s)}, DR.Lab{vc, S.Q.neg(vs)}):
  (DR.Lab{l0, l1}, (le.c(DR.Lab{vc, vs}, LA.lcomb(l0, DR.Lab{b0c, b0s}, l1, DR.Lab{b1c, b1s}), he),
    LA.qe_of(S.Q.neg(vs), S.Q.add(S.Q.mul(l0, S.Q.neg(b0s)), S.Q.mul(l1, S.Q.neg(b1s))), cj.s(vs, l0, b0s, l1, b1s, le.s(DR.Lab{vc, vs}, LA.lcomb(l0, DR.Lab{b0c, b0s}, l1, DR.Lab{b1c, b1s}), he)))))

# conjugating a span: the same real coefficients
def lsp_conj(v: DR.Lab, b0: DR.Lab, b1: DR.Lab, +h: LSp(b0, b1, v)) -> LSp(DR.Lab.conj(b0), DR.Lab.conj(b1), DR.Lab.conj(v)):
  match v b0 b1:
    case DR.Lab{+vc, +vs} DR.Lab{+b0c, +b0s} DR.Lab{+b1c, +b1s}:
      lsp_conj.go(vc, vs, b0c, b0s, b1c, b1s, LA.lab.c(lsp.p(DR.Lab{b0c, b0s}, DR.Lab{b1c, b1s}, DR.Lab{vc, vs}, h)), LA.lab.s(lsp.p(DR.Lab{b0c, b0s}, DR.Lab{b1c, b1s}, DR.Lab{vc, vs}, h)),
        lsp.e(DR.Lab{b0c, b0s}, DR.Lab{b1c, b1s}, DR.Lab{vc, vs}, h))
