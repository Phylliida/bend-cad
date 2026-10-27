# bend-cad: a tied set's derivation is right (PLAN-sk13b B3). For y in the
# tied set of c (cross(u, y) in the span of cross(u, the generators)),
# lib/dclose.bend's tied.der derives par(c, y'), y' = (the generators'
# combination) + p u with p = dot(u, y - combination) / |u|^2. Since
# cross(u, y - combination) = 0 and u is nonzero, y' = y (tied_ok).
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
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./drvpf.bend as DV
import ./identpf.bend as ID
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./hspacepf.bend as HP
import ./seppf.bend as SP
import ./labpf.bend as LP
import ./labnzpf.bend as NZ
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcinvpf.bend as IV
import ./dcbelowpf.bend as BL
import ./dcgenpf.bend as GN
import ./dcderpf.bend as DD
import ./dcreppf.bend as RP

# Rational cores
# --------------

# c (W2) = s (W1) from c W2 - s W1 = 0
def tc.eq(+c: S.Q, +s: S.Q, +w1: S.Q, +w2: S.Q, h: S.Q.eq(S.Q.sub(S.Q.mul(c, w2), S.Q.mul(s, w1)), DR.qz())) -> S.Q.eq(S.Q.mul(c, w2), S.Q.mul(s, w1)):
  LQ.q_trans(S.Q.mul(c, w2), S.Q.add(S.Q.sub(S.Q.mul(c, w2), S.Q.mul(s, w1)), S.Q.mul(s, w1)), S.Q.mul(s, w1),
    QR.qring_eq([S.Q.mul(c, w2), S.Q.mul(s, w1)], E.QVar{0n}, E.QAdd{E.QSub{E.QVar{0n}, E.QVar{1n}}, E.QVar{1n}}, {==}),
    LQ.q_trans(S.Q.add(S.Q.sub(S.Q.mul(c, w2), S.Q.mul(s, w1)), S.Q.mul(s, w1)), S.Q.add(DR.qz(), S.Q.mul(s, w1)), S.Q.mul(s, w1),
      LQ.q_add_cong_l(S.Q.sub(S.Q.mul(c, w2), S.Q.mul(s, w1)), DR.qz(), S.Q.mul(s, w1), h),
      QR.qring_eq([S.Q.mul(s, w1)], E.QAdd{E.QCst{DR.qz()}, E.QVar{0n}}, E.QVar{0n}, {==})))

# x (i (x a + y b)) = i (x x a + y (x b))
def tc.dist(+x: S.Q, +i: S.Q, +y: S.Q, +a: S.Q, +b: S.Q) -> S.Q.eq(S.Q.mul(x, S.Q.mul(i, S.Q.add(S.Q.mul(x, a), S.Q.mul(y, b)))), S.Q.mul(i, S.Q.add(S.Q.mul(S.Q.mul(x, x), a), S.Q.mul(y, S.Q.mul(x, b))))):
  LQ.q_trans(S.Q.mul(x, S.Q.mul(i, S.Q.add(S.Q.mul(x, a), S.Q.mul(y, b)))), S.Q.mul(i, S.Q.mul(x, S.Q.add(S.Q.mul(x, a), S.Q.mul(y, b)))), S.Q.mul(i, S.Q.add(S.Q.mul(S.Q.mul(x, x), a), S.Q.mul(y, S.Q.mul(x, b)))),
    QA.mswap(x, i, S.Q.add(S.Q.mul(x, a), S.Q.mul(y, b))),
    LQ.q_mul_cong_r(i, S.Q.mul(x, S.Q.add(S.Q.mul(x, a), S.Q.mul(y, b))), S.Q.add(S.Q.mul(S.Q.mul(x, x), a), S.Q.mul(y, S.Q.mul(x, b))),
      LQ.q_trans(S.Q.mul(x, S.Q.add(S.Q.mul(x, a), S.Q.mul(y, b))), S.Q.add(S.Q.mul(x, S.Q.mul(x, a)), S.Q.mul(x, S.Q.mul(y, b))), S.Q.add(S.Q.mul(S.Q.mul(x, x), a), S.Q.mul(y, S.Q.mul(x, b))),
        QA.ldist(x, S.Q.mul(x, a), S.Q.mul(y, b)),
        QA.add_cong(S.Q.mul(x, S.Q.mul(x, a)), S.Q.mul(S.Q.mul(x, x), a), S.Q.mul(x, S.Q.mul(y, b)), S.Q.mul(y, S.Q.mul(x, b)), QA.ma(x, x, a), QA.mswap(x, y, b)))))

# i (x x a + y (y a)) = (i (x x + y y)) a
def tc.fold(+i: S.Q, +x: S.Q, +y: S.Q, +a: S.Q) -> S.Q.eq(S.Q.mul(i, S.Q.add(S.Q.mul(S.Q.mul(x, x), a), S.Q.mul(y, S.Q.mul(y, a)))), S.Q.mul(S.Q.mul(i, S.Q.add(S.Q.mul(x, x), S.Q.mul(y, y))), a)):
  LQ.q_trans(S.Q.mul(i, S.Q.add(S.Q.mul(S.Q.mul(x, x), a), S.Q.mul(y, S.Q.mul(y, a)))), S.Q.mul(i, S.Q.mul(S.Q.add(S.Q.mul(x, x), S.Q.mul(y, y)), a)), S.Q.mul(S.Q.mul(i, S.Q.add(S.Q.mul(x, x), S.Q.mul(y, y))), a),
    LQ.q_mul_cong_r(i, S.Q.add(S.Q.mul(S.Q.mul(x, x), a), S.Q.mul(y, S.Q.mul(y, a))), S.Q.mul(S.Q.add(S.Q.mul(x, x), S.Q.mul(y, y)), a),
      LQ.q_trans(S.Q.add(S.Q.mul(S.Q.mul(x, x), a), S.Q.mul(y, S.Q.mul(y, a))), S.Q.add(S.Q.mul(S.Q.mul(x, x), a), S.Q.mul(S.Q.mul(y, y), a)), S.Q.mul(S.Q.add(S.Q.mul(x, x), S.Q.mul(y, y)), a),
        LQ.q_add_cong_r(S.Q.mul(S.Q.mul(x, x), a), S.Q.mul(y, S.Q.mul(y, a)), S.Q.mul(S.Q.mul(y, y), a), QA.ma(y, y, a)),
        LQ.q_sym(S.Q.mul(S.Q.add(S.Q.mul(x, x), S.Q.mul(y, y)), a), S.Q.add(S.Q.mul(S.Q.mul(x, x), a), S.Q.mul(S.Q.mul(y, y), a)), QA.rdist(S.Q.mul(x, x), S.Q.mul(y, y), a)))),
    LQ.q_sym(S.Q.mul(S.Q.mul(i, S.Q.add(S.Q.mul(x, x), S.Q.mul(y, y))), a), S.Q.mul(i, S.Q.mul(S.Q.add(S.Q.mul(x, x), S.Q.mul(y, y)), a)), QA.massoc(i, S.Q.add(S.Q.mul(x, x), S.Q.mul(y, y)), a)))

# (1/n n) a = a for n not 0
def tc.cancel(+n: S.Q, +a: S.Q, hn: S.Q.eq(n, DR.qz()) -> Empty) -> S.Q.eq(S.Q.mul(S.Q.mul(S.Q.inv(n), n), a), a):
  LQ.q_trans(S.Q.mul(S.Q.mul(S.Q.inv(n), n), a), S.Q.mul(DR.qo(), a), a,
    LQ.q_mul_cong_l(S.Q.mul(S.Q.inv(n), n), DR.qo(), a, LQ.q_trans(S.Q.mul(S.Q.inv(n), n), S.Q.mul(n, S.Q.inv(n)), DR.qo(), LQ.q_mul_comm(S.Q.inv(n), n), LQ.q_mul_inv(n, hn))),
    QA.one_mul(a))

# with c W2 = s W1 and n = c c + s s not 0: c ((1/n) (c W1 + s W2)) = W1
def tc.x(+c: S.Q, +s: S.Q, +w1: S.Q, +w2: S.Q, h: S.Q.eq(S.Q.mul(c, w2), S.Q.mul(s, w1)), hn: S.Q.eq(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s)), DR.qz()) -> Empty)
  -> S.Q.eq(S.Q.mul(c, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(c, w1), S.Q.mul(s, w2)))), w1):
  QA.ch4(S.Q.mul(c, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(c, w1), S.Q.mul(s, w2)))),
    S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.mul(c, c), w1), S.Q.mul(s, S.Q.mul(c, w2)))),
    S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.mul(c, c), w1), S.Q.mul(s, S.Q.mul(s, w1)))),
    S.Q.mul(S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), w1),
    w1,
    tc.dist(c, S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), s, w1, w2),
    LQ.q_mul_cong_r(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.mul(c, c), w1), S.Q.mul(s, S.Q.mul(c, w2))), S.Q.add(S.Q.mul(S.Q.mul(c, c), w1), S.Q.mul(s, S.Q.mul(s, w1))),
      LQ.q_add_cong_r(S.Q.mul(S.Q.mul(c, c), w1), S.Q.mul(s, S.Q.mul(c, w2)), S.Q.mul(s, S.Q.mul(s, w1)), LQ.q_mul_cong_r(s, S.Q.mul(c, w2), S.Q.mul(s, w1), h))),
    tc.fold(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), c, s, w1),
    tc.cancel(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s)), w1, hn))

# and s ((1/n) (c W1 + s W2)) = W2
def tc.y2(+c: S.Q, +s: S.Q, +w2: S.Q, hn: S.Q.eq(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s)), DR.qz()) -> Empty)
  -> S.Q.eq(S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.mul(s, s), w2), S.Q.mul(c, S.Q.mul(c, w2)))), w2):
  LQ.q_trans(S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.mul(s, s), w2), S.Q.mul(c, S.Q.mul(c, w2)))),
    S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.mul(c, c), w2), S.Q.mul(s, S.Q.mul(s, w2)))), w2,
    LQ.q_mul_cong_r(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.mul(s, s), w2), S.Q.mul(c, S.Q.mul(c, w2))), S.Q.add(S.Q.mul(S.Q.mul(c, c), w2), S.Q.mul(s, S.Q.mul(s, w2))),
      LQ.q_trans(S.Q.add(S.Q.mul(S.Q.mul(s, s), w2), S.Q.mul(c, S.Q.mul(c, w2))), S.Q.add(S.Q.mul(S.Q.mul(s, s), w2), S.Q.mul(S.Q.mul(c, c), w2)), S.Q.add(S.Q.mul(S.Q.mul(c, c), w2), S.Q.mul(s, S.Q.mul(s, w2))),
        LQ.q_add_cong_r(S.Q.mul(S.Q.mul(s, s), w2), S.Q.mul(c, S.Q.mul(c, w2)), S.Q.mul(S.Q.mul(c, c), w2), QA.ma(c, c, w2)),
        LQ.q_trans(S.Q.add(S.Q.mul(S.Q.mul(s, s), w2), S.Q.mul(S.Q.mul(c, c), w2)), S.Q.add(S.Q.mul(S.Q.mul(c, c), w2), S.Q.mul(S.Q.mul(s, s), w2)), S.Q.add(S.Q.mul(S.Q.mul(c, c), w2), S.Q.mul(s, S.Q.mul(s, w2))),
          LQ.q_add_comm(S.Q.mul(S.Q.mul(s, s), w2), S.Q.mul(S.Q.mul(c, c), w2)),
          LQ.q_add_cong_r(S.Q.mul(S.Q.mul(c, c), w2), S.Q.mul(S.Q.mul(s, s), w2), S.Q.mul(s, S.Q.mul(s, w2)), LQ.q_sym(S.Q.mul(s, S.Q.mul(s, w2)), S.Q.mul(S.Q.mul(s, s), w2), QA.ma(s, s, w2)))))),
    LQ.q_trans(S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.mul(c, c), w2), S.Q.mul(s, S.Q.mul(s, w2)))),
      S.Q.mul(S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), w2), w2,
      tc.fold(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), c, s, w2), tc.cancel(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s)), w2, hn)))

def tc.y(+c: S.Q, +s: S.Q, +w1: S.Q, +w2: S.Q, h: S.Q.eq(S.Q.mul(c, w2), S.Q.mul(s, w1)), hn: S.Q.eq(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s)), DR.qz()) -> Empty)
  -> S.Q.eq(S.Q.mul(s, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(c, w1), S.Q.mul(s, w2)))), w2):
  QA.ch4(S.Q.mul(s, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(c, w1), S.Q.mul(s, w2)))),
    S.Q.mul(s, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(s, w2), S.Q.mul(c, w1)))),
    S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.mul(s, s), w2), S.Q.mul(c, S.Q.mul(s, w1)))),
    S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.mul(s, s), w2), S.Q.mul(c, S.Q.mul(c, w2)))),
    w2,
    LQ.q_mul_cong_r(s, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(c, w1), S.Q.mul(s, w2))), S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(s, w2), S.Q.mul(c, w1))),
      LQ.q_mul_cong_r(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(c, w1), S.Q.mul(s, w2)), S.Q.add(S.Q.mul(s, w2), S.Q.mul(c, w1)), LQ.q_add_comm(S.Q.mul(c, w1), S.Q.mul(s, w2)))),
    tc.dist(s, S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), c, w2, w1),
    LQ.q_mul_cong_r(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.mul(s, s), w2), S.Q.mul(c, S.Q.mul(s, w1))), S.Q.add(S.Q.mul(S.Q.mul(s, s), w2), S.Q.mul(c, S.Q.mul(c, w2))),
      LQ.q_add_cong_r(S.Q.mul(S.Q.mul(s, s), w2), S.Q.mul(c, S.Q.mul(s, w1)), S.Q.mul(c, S.Q.mul(c, w2)), LQ.q_mul_cong_r(c, S.Q.mul(s, w1), S.Q.mul(c, w2), LQ.q_sym(S.Q.mul(c, w2), S.Q.mul(s, w1), h)))),
    tc.y2(c, s, w2, hn))


# cross linearity: ua (m1 y1 + m2 y2) - ub (m1 x1 + m2 x2) = m1 (ua y1 - ub x1) + m2 (ua y2 - ub x2)
def crossl(+ua: S.Q, +ub: S.Q, +m1: S.Q, +m2: S.Q, +x1: S.Q, +y1: S.Q, +x2: S.Q, +y2: S.Q) -> S.Q.eq(S.Q.sub(S.Q.mul(ua, S.Q.add(S.Q.mul(m1, y1), S.Q.mul(m2, y2))), S.Q.mul(ub, S.Q.add(S.Q.mul(m1, x1), S.Q.mul(m2, x2)))), S.Q.add(S.Q.mul(m1, S.Q.sub(S.Q.mul(ua, y1), S.Q.mul(ub, x1))), S.Q.mul(m2, S.Q.sub(S.Q.mul(ua, y2), S.Q.mul(ub, x2))))):
  QA.ch4(S.Q.sub(S.Q.mul(ua, S.Q.add(S.Q.mul(m1, y1), S.Q.mul(m2, y2))), S.Q.mul(ub, S.Q.add(S.Q.mul(m1, x1), S.Q.mul(m2, x2)))), S.Q.sub(S.Q.add(S.Q.mul(ua, S.Q.mul(m1, y1)), S.Q.mul(ua, S.Q.mul(m2, y2))), S.Q.add(S.Q.mul(ub, S.Q.mul(m1, x1)), S.Q.mul(ub, S.Q.mul(m2, x2)))), S.Q.add(S.Q.sub(S.Q.mul(ua, S.Q.mul(m1, y1)), S.Q.mul(ub, S.Q.mul(m1, x1))), S.Q.sub(S.Q.mul(ua, S.Q.mul(m2, y2)), S.Q.mul(ub, S.Q.mul(m2, x2)))), S.Q.add(S.Q.sub(S.Q.mul(m1, S.Q.mul(ua, y1)), S.Q.mul(m1, S.Q.mul(ub, x1))), S.Q.sub(S.Q.mul(m2, S.Q.mul(ua, y2)), S.Q.mul(m2, S.Q.mul(ub, x2)))), S.Q.add(S.Q.mul(m1, S.Q.sub(S.Q.mul(ua, y1), S.Q.mul(ub, x1))), S.Q.mul(m2, S.Q.sub(S.Q.mul(ua, y2), S.Q.mul(ub, x2)))),
    QA.sub_cong(S.Q.mul(ua, S.Q.add(S.Q.mul(m1, y1), S.Q.mul(m2, y2))), S.Q.add(S.Q.mul(ua, S.Q.mul(m1, y1)), S.Q.mul(ua, S.Q.mul(m2, y2))), S.Q.mul(ub, S.Q.add(S.Q.mul(m1, x1), S.Q.mul(m2, x2))), S.Q.add(S.Q.mul(ub, S.Q.mul(m1, x1)), S.Q.mul(ub, S.Q.mul(m2, x2))), QA.ldist(ua, S.Q.mul(m1, y1), S.Q.mul(m2, y2)), QA.ldist(ub, S.Q.mul(m1, x1), S.Q.mul(m2, x2))),
    QA.r4c(S.Q.mul(ua, S.Q.mul(m1, y1)), S.Q.mul(ua, S.Q.mul(m2, y2)), S.Q.mul(ub, S.Q.mul(m1, x1)), S.Q.mul(ub, S.Q.mul(m2, x2))),
    QA.add_cong(S.Q.sub(S.Q.mul(ua, S.Q.mul(m1, y1)), S.Q.mul(ub, S.Q.mul(m1, x1))), S.Q.sub(S.Q.mul(m1, S.Q.mul(ua, y1)), S.Q.mul(m1, S.Q.mul(ub, x1))), S.Q.sub(S.Q.mul(ua, S.Q.mul(m2, y2)), S.Q.mul(ub, S.Q.mul(m2, x2))), S.Q.sub(S.Q.mul(m2, S.Q.mul(ua, y2)), S.Q.mul(m2, S.Q.mul(ub, x2))), QA.sub_cong(S.Q.mul(ua, S.Q.mul(m1, y1)), S.Q.mul(m1, S.Q.mul(ua, y1)), S.Q.mul(ub, S.Q.mul(m1, x1)), S.Q.mul(m1, S.Q.mul(ub, x1)), QA.mswap(ua, m1, y1), QA.mswap(ub, m1, x1)), QA.sub_cong(S.Q.mul(ua, S.Q.mul(m2, y2)), S.Q.mul(m2, S.Q.mul(ua, y2)), S.Q.mul(ub, S.Q.mul(m2, x2)), S.Q.mul(m2, S.Q.mul(ub, x2)), QA.mswap(ua, m2, y2), QA.mswap(ub, m2, x2))),
    QA.add_cong(S.Q.sub(S.Q.mul(m1, S.Q.mul(ua, y1)), S.Q.mul(m1, S.Q.mul(ub, x1))), S.Q.mul(m1, S.Q.sub(S.Q.mul(ua, y1), S.Q.mul(ub, x1))), S.Q.sub(S.Q.mul(m2, S.Q.mul(ua, y2)), S.Q.mul(m2, S.Q.mul(ub, x2))), S.Q.mul(m2, S.Q.sub(S.Q.mul(ua, y2), S.Q.mul(ub, x2))), LQ.q_sym(S.Q.mul(m1, S.Q.sub(S.Q.mul(ua, y1), S.Q.mul(ub, x1))), S.Q.sub(S.Q.mul(m1, S.Q.mul(ua, y1)), S.Q.mul(m1, S.Q.mul(ub, x1))), QA.ldsub(m1, S.Q.mul(ua, y1), S.Q.mul(ub, x1))), LQ.q_sym(S.Q.mul(m2, S.Q.sub(S.Q.mul(ua, y2), S.Q.mul(ub, x2))), S.Q.sub(S.Q.mul(m2, S.Q.mul(ua, y2)), S.Q.mul(m2, S.Q.mul(ub, x2))), QA.ldsub(m2, S.Q.mul(ua, y2), S.Q.mul(ub, x2)))))

# cross(u, y) = 0 for y = y - combination
def u1c(+c: S.Q, +s: S.Q) -> S.Q.eq(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), c):
  QR.qring_eq([c, s], E.QSub{E.QMul{E.QVar{0n}, E.QCst{DR.qo()}}, E.QMul{E.QVar{1n}, E.QCst{DR.qz()}}}, E.QVar{0n}, {==})

def u2s(+c: S.Q, +s: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), s):
  QR.qring_eq([c, s], E.QAdd{E.QMul{E.QVar{1n}, E.QCst{DR.qo()}}, E.QMul{E.QVar{0n}, E.QCst{DR.qz()}}}, E.QVar{1n}, {==})

def xcs(+c: S.Q, +s: S.Q, +a: S.Q, +b: S.Q) -> S.Q.eq(S.Q.sub(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), a), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), b)), S.Q.sub(S.Q.mul(c, a), S.Q.mul(s, b))):
  QA.sub_cong(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), a), S.Q.mul(c, a), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), b), S.Q.mul(s, b),
    LQ.q_mul_cong_l(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), c, a, u1c(c, s)), LQ.q_mul_cong_l(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), s, b, u2s(c, s)))

def tcross(+c: S.Q, +s: S.Q, +y1: S.Q, +y2: S.Q, +c1: S.Q, +c2: S.Q,
  h0: S.Q.eq(S.Q.sub(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), y2), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), y1)),
    S.Q.sub(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), c2), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), c1))))
  -> S.Q.eq(S.Q.sub(S.Q.mul(c, S.Q.sub(y2, c2)), S.Q.mul(s, S.Q.sub(y1, c1))), DR.qz()):
  QA.ch4(S.Q.sub(S.Q.mul(c, S.Q.sub(y2, c2)), S.Q.mul(s, S.Q.sub(y1, c1))),
    S.Q.sub(S.Q.sub(S.Q.mul(c, y2), S.Q.mul(c, c2)), S.Q.sub(S.Q.mul(s, y1), S.Q.mul(s, c1))),
    S.Q.sub(S.Q.sub(S.Q.mul(c, y2), S.Q.mul(s, y1)), S.Q.sub(S.Q.mul(c, c2), S.Q.mul(s, c1))),
    S.Q.sub(S.Q.sub(S.Q.mul(c, c2), S.Q.mul(s, c1)), S.Q.sub(S.Q.mul(c, c2), S.Q.mul(s, c1))),
    DR.qz(),
    QA.sub_cong(S.Q.mul(c, S.Q.sub(y2, c2)), S.Q.sub(S.Q.mul(c, y2), S.Q.mul(c, c2)), S.Q.mul(s, S.Q.sub(y1, c1)), S.Q.sub(S.Q.mul(s, y1), S.Q.mul(s, c1)), QA.ldsub(c, y2, c2), QA.ldsub(s, y1, c1)),
    QA.r4d(S.Q.mul(c, y2), S.Q.mul(c, c2), S.Q.mul(s, y1), S.Q.mul(s, c1)),
    QA.sub_cong(S.Q.sub(S.Q.mul(c, y2), S.Q.mul(s, y1)), S.Q.sub(S.Q.mul(c, c2), S.Q.mul(s, c1)), S.Q.sub(S.Q.mul(c, c2), S.Q.mul(s, c1)), S.Q.sub(S.Q.mul(c, c2), S.Q.mul(s, c1)),
      QA.ch3(S.Q.sub(S.Q.mul(c, y2), S.Q.mul(s, y1)), S.Q.sub(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), y2), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), y1)),
        S.Q.sub(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), c2), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), c1)), S.Q.sub(S.Q.mul(c, c2), S.Q.mul(s, c1)),
        LQ.q_sym(S.Q.sub(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), y2), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), y1)), S.Q.sub(S.Q.mul(c, y2), S.Q.mul(s, y1)), xcs(c, s, y2, y1)),
        h0, xcs(c, s, c2, c1)),
      LQ.q_refl(S.Q.sub(S.Q.mul(c, c2), S.Q.mul(s, c1)))),
    QR.qring_eq([S.Q.sub(S.Q.mul(c, c2), S.Q.mul(s, c1))], E.QSub{E.QVar{0n}, E.QVar{0n}}, E.QCst{DR.qz()}, {==}))

# The components
# --------------

def onez(+a: S.Q, +x: S.Q, +n0: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(DR.qo(), a), S.Q.mul(DR.qo(), S.Q.sub(x, S.Q.mul(n0, DR.qz())))), S.Q.add(a, x)):
  QR.qring_eq([a, x, n0], E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qo()}, E.QSub{E.QVar{1n}, E.QMul{E.QVar{2n}, E.QCst{DR.qz()}}}}}, E.QAdd{E.QVar{0n}, E.QVar{1n}}, {==})

def onez2(+a: S.Q, +x: S.Q, +n0: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(DR.qo(), a), S.Q.mul(DR.qo(), S.Q.add(x, S.Q.mul(n0, DR.qz())))), S.Q.add(a, x)):
  QR.qring_eq([a, x, n0], E.QAdd{E.QMul{E.QCst{DR.qo()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qo()}, E.QAdd{E.QVar{1n}, E.QMul{E.QVar{2n}, E.QCst{DR.qz()}}}}}, E.QAdd{E.QVar{0n}, E.QVar{1n}}, {==})

def back(+a: S.Q, +y: S.Q) -> S.Q.eq(S.Q.add(a, S.Q.sub(y, a)), y):
  QR.qring_eq([a, y], E.QAdd{E.QVar{0n}, E.QSub{E.QVar{1n}, E.QVar{0n}}}, E.QVar{1n}, {==})

def pcong(+c: S.Q, +s: S.Q, +i: S.Q, +w1: S.Q, +w2: S.Q)
  -> S.Q.eq(S.Q.mul(i, S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), w1), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), w2))), S.Q.mul(i, S.Q.add(S.Q.mul(c, w1), S.Q.mul(s, w2)))):
  LQ.q_mul_cong_r(i, S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), w1), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), w2)), S.Q.add(S.Q.mul(c, w1), S.Q.mul(s, w2)),
    QA.add_cong(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), w1), S.Q.mul(c, w1), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), w2), S.Q.mul(s, w2),
      LQ.q_mul_cong_l(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), c, w1, u1c(c, s)), LQ.q_mul_cong_l(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), s, w2, u2s(c, s))))

def compx(+c: S.Q, +s: S.Q, +nns: S.Q, +y1: S.Q, +y2: S.Q, +c1: S.Q, +c2: S.Q, hcz: S.Q.eq(S.Q.sub(S.Q.mul(c, S.Q.sub(y2, c2)), S.Q.mul(s, S.Q.sub(y1, c1))), DR.qz()),
  hn: S.Q.eq(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s)), DR.qz()) -> Empty)
  -> S.Q.eq(S.Q.add(S.Q.mul(DR.qo(), c1), S.Q.mul(DR.qo(), S.Q.sub(S.Q.mul(c, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), S.Q.sub(y1, c1)), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), S.Q.sub(y2, c2))))), S.Q.mul(nns, DR.qz())))), y1):
  QA.ch4(S.Q.add(S.Q.mul(DR.qo(), c1), S.Q.mul(DR.qo(), S.Q.sub(S.Q.mul(c, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), S.Q.sub(y1, c1)), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), S.Q.sub(y2, c2))))), S.Q.mul(nns, DR.qz())))),
    S.Q.add(c1, S.Q.mul(c, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), S.Q.sub(y1, c1)), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), S.Q.sub(y2, c2)))))),
    S.Q.add(c1, S.Q.mul(c, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(c, S.Q.sub(y1, c1)), S.Q.mul(s, S.Q.sub(y2, c2)))))),
    S.Q.add(c1, S.Q.sub(y1, c1)), y1,
    onez(c1, S.Q.mul(c, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), S.Q.sub(y1, c1)), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), S.Q.sub(y2, c2))))), nns),
    LQ.q_add_cong_r(c1, S.Q.mul(c, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), S.Q.sub(y1, c1)), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), S.Q.sub(y2, c2))))),
      S.Q.mul(c, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(c, S.Q.sub(y1, c1)), S.Q.mul(s, S.Q.sub(y2, c2))))),
      LQ.q_mul_cong_r(c, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), S.Q.sub(y1, c1)), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), S.Q.sub(y2, c2)))),
        S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(c, S.Q.sub(y1, c1)), S.Q.mul(s, S.Q.sub(y2, c2)))), pcong(c, s, S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.sub(y1, c1), S.Q.sub(y2, c2)))),
    LQ.q_add_cong_r(c1, S.Q.mul(c, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(c, S.Q.sub(y1, c1)), S.Q.mul(s, S.Q.sub(y2, c2))))), S.Q.sub(y1, c1),
      tc.x(c, s, S.Q.sub(y1, c1), S.Q.sub(y2, c2), tc.eq(c, s, S.Q.sub(y1, c1), S.Q.sub(y2, c2), hcz), hn)),
    back(c1, y1))

def compy(+c: S.Q, +s: S.Q, +y1: S.Q, +y2: S.Q, +c1: S.Q, +c2: S.Q, hcz: S.Q.eq(S.Q.sub(S.Q.mul(c, S.Q.sub(y2, c2)), S.Q.mul(s, S.Q.sub(y1, c1))), DR.qz()),
  hn: S.Q.eq(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s)), DR.qz()) -> Empty)
  -> S.Q.eq(S.Q.add(S.Q.mul(DR.qo(), c2), S.Q.mul(DR.qo(), S.Q.add(S.Q.mul(S.Q.neg(S.Q.neg(s)), S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), S.Q.sub(y1, c1)), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), S.Q.sub(y2, c2))))), S.Q.mul(c, DR.qz())))), y2):
  QA.ch4(S.Q.add(S.Q.mul(DR.qo(), c2), S.Q.mul(DR.qo(), S.Q.add(S.Q.mul(S.Q.neg(S.Q.neg(s)), S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), S.Q.sub(y1, c1)), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), S.Q.sub(y2, c2))))), S.Q.mul(c, DR.qz())))),
    S.Q.add(c2, S.Q.mul(S.Q.neg(S.Q.neg(s)), S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), S.Q.sub(y1, c1)), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), S.Q.sub(y2, c2)))))),
    S.Q.add(c2, S.Q.mul(s, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(c, S.Q.sub(y1, c1)), S.Q.mul(s, S.Q.sub(y2, c2)))))),
    S.Q.add(c2, S.Q.sub(y2, c2)), y2,
    onez2(c2, S.Q.mul(S.Q.neg(S.Q.neg(s)), S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), S.Q.sub(y1, c1)), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), S.Q.sub(y2, c2))))), c),
    LQ.q_add_cong_r(c2, S.Q.mul(S.Q.neg(S.Q.neg(s)), S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), S.Q.sub(y1, c1)), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), S.Q.sub(y2, c2))))),
      S.Q.mul(s, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(c, S.Q.sub(y1, c1)), S.Q.mul(s, S.Q.sub(y2, c2))))),
      LQ.q_trans(S.Q.mul(S.Q.neg(S.Q.neg(s)), S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), S.Q.sub(y1, c1)), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), S.Q.sub(y2, c2))))),
        S.Q.mul(s, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), S.Q.sub(y1, c1)), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), S.Q.sub(y2, c2))))),
        S.Q.mul(s, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(c, S.Q.sub(y1, c1)), S.Q.mul(s, S.Q.sub(y2, c2))))),
        LQ.q_mul_cong_l(S.Q.neg(S.Q.neg(s)), s, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), S.Q.sub(y1, c1)), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), S.Q.sub(y2, c2)))), LQ.q_sym(s, S.Q.neg(S.Q.neg(s)), GN.negneg(s))),
        LQ.q_mul_cong_r(s, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c, DR.qo()), S.Q.mul(s, DR.qz())), S.Q.sub(y1, c1)), S.Q.mul(S.Q.add(S.Q.mul(s, DR.qo()), S.Q.mul(c, DR.qz())), S.Q.sub(y2, c2)))),
          S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(c, S.Q.sub(y1, c1)), S.Q.mul(s, S.Q.sub(y2, c2)))), pcong(c, s, S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.sub(y1, c1), S.Q.sub(y2, c2))))),
    LQ.q_add_cong_r(c2, S.Q.mul(s, S.Q.mul(S.Q.inv(S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))), S.Q.add(S.Q.mul(c, S.Q.sub(y1, c1)), S.Q.mul(s, S.Q.sub(y2, c2))))), S.Q.sub(y2, c2),
      tc.y(c, s, S.Q.sub(y1, c1), S.Q.sub(y2, c2), tc.eq(c, s, S.Q.sub(y1, c1), S.Q.sub(y2, c2), hcz), hn)),
    back(c2, y2))

# Forms
# -----

def crs(+u: SK.VE, xs: List<&2, SK.VE>) -> List<&2, E.QExpr>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, tl}:
      Con{SK.VE.cross(u, x), crs(u, tl)}

def crosses_crs(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, ds: List<&2, DR.Der>) -> {DC.crosses(es, fs, u, ds) == crs(DC.lform(u), HS.hxs(es, fs, ds)) : List<&2, E.QExpr>}:
  match ds:
    case Nil{}:
      {==}
    case Con{+d, +tl}:
      %Equal.sym(List<&2, E.QExpr>, DC.crosses(es, fs, u, tl), crs(DC.lform(u), HS.hxs(es, fs, tl)), crosses_crs(es, fs, u, tl)) : {Con{SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, d))), _} == crs(DC.lform(u), HS.hxs(es, fs, Con{d, tl})) : List<&2, E.QExpr>}
      {==}

def cross_vlin.at(+p: List<&2, S.Q>, +uu: SK.VE, +m1: S.Q, +x1: SK.VE, +m2: S.Q, +x2: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.cross(uu, DR.vlin(m1, x1, m2, x2))), S.Q.add(S.Q.mul(m1, E.qeval(p, SK.VE.cross(uu, x1))), S.Q.mul(m2, E.qeval(p, SK.VE.cross(uu, x2))))):
  crossl(E.qeval(p, SK.VE.x(uu)), E.qeval(p, SK.VE.y(uu)), m1, m2, E.qeval(p, SK.VE.x(x1)), E.qeval(p, SK.VE.y(x1)), E.qeval(p, SK.VE.x(x2)), E.qeval(p, SK.VE.y(x2)))

def cross_clin.base(+p: List<&2, S.Q>, +uu: SK.VE, +z: SK.VE) -> S.Q.eq(E.qeval(p, SK.VE.cross(uu, DR.vlin(DR.qz(), z, DR.qz(), z))), DR.qz()):
  LQ.q_trans(E.qeval(p, SK.VE.cross(uu, DR.vlin(DR.qz(), z, DR.qz(), z))), S.Q.add(S.Q.mul(DR.qz(), E.qeval(p, SK.VE.cross(uu, z))), S.Q.mul(DR.qz(), E.qeval(p, SK.VE.cross(uu, z)))), DR.qz(),
    cross_vlin.at(p, uu, DR.qz(), z, DR.qz(), z),
    QR.qring_eq([E.qeval(p, SK.VE.cross(uu, z))], E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}}, E.QCst{DR.qz()}, {==}))

# cross(u, a combination of forms) is the combination of their crosses
def cross_clin.at(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +r: DR.Node, +uu: SK.VE, ls: List<&2, S.Q>, xs: List<&2, SK.VE>)
  -> S.Q.eq(E.qeval(p, SK.VE.cross(uu, HS.clin(es, r, ls, xs))), E.qeval(p, SV.lin(ls, crs(uu, xs)))):
  match ls xs:
    case Con{+l, +lt} Con{+x, +xt}:
      QA.ch3(E.qeval(p, SK.VE.cross(uu, HS.clin(es, r, Con{l, lt}, Con{x, xt}))),
        S.Q.add(S.Q.mul(l, E.qeval(p, SK.VE.cross(uu, x))), S.Q.mul(DR.qo(), E.qeval(p, SK.VE.cross(uu, HS.clin(es, r, lt, xt))))),
        S.Q.add(S.Q.mul(l, E.qeval(p, SK.VE.cross(uu, x))), E.qeval(p, SK.VE.cross(uu, HS.clin(es, r, lt, xt)))),
        S.Q.add(S.Q.mul(l, E.qeval(p, SK.VE.cross(uu, x))), E.qeval(p, SV.lin(lt, crs(uu, xt)))),
        cross_vlin.at(p, uu, l, x, DR.qo(), HS.clin(es, r, lt, xt)),
        LQ.q_add_cong_r(S.Q.mul(l, E.qeval(p, SK.VE.cross(uu, x))), S.Q.mul(DR.qo(), E.qeval(p, SK.VE.cross(uu, HS.clin(es, r, lt, xt)))), E.qeval(p, SK.VE.cross(uu, HS.clin(es, r, lt, xt))), QA.one_mul(E.qeval(p, SK.VE.cross(uu, HS.clin(es, r, lt, xt))))),
        LQ.q_add_cong_r(S.Q.mul(l, E.qeval(p, SK.VE.cross(uu, x))), E.qeval(p, SK.VE.cross(uu, HS.clin(es, r, lt, xt))), E.qeval(p, SV.lin(lt, crs(uu, xt))), cross_clin.at(p, es, r, uu, lt, xt)))
    case Nil{} xs:
      cross_clin.base(p, uu, DR.zdir(es, r))
    case Con{+l, +lt} Nil{}:
      cross_clin.base(p, uu, DR.zdir(es, r))

def crs_move(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +lam: List<&2, S.Q>, +ds: List<&2, DR.Der>)
  -> S.Q.eq(E.qeval(p, SV.lin(lam, DC.crosses(es, fs, u, ds))), E.qeval(p, SV.lin(lam, crs(DC.lform(u), HS.hxs(es, fs, ds))))):
  %Equal.sym(List<&2, E.QExpr>, DC.crosses(es, fs, u, ds), crs(DC.lform(u), HS.hxs(es, fs, ds)), crosses_crs(es, fs, u, ds)) : S.Q.eq(E.qeval(p, SV.lin(lam, _)), E.qeval(p, SV.lin(lam, crs(DC.lform(u), HS.hxs(es, fs, ds)))))
  LQ.q_refl(E.qeval(p, SV.lin(lam, crs(DC.lform(u), HS.hxs(es, fs, ds)))))

def xch_move(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +c: Nat, +u: DR.Lab, +lam: List<&2, S.Q>, +ds: List<&2, DR.Der>)
  -> S.Q.eq(E.qeval(p, SK.VE.cross(DC.lform(u), HS.clin(es, DR.NSeg{c}, lam, HS.hxs(es, fs, ds)))), E.qeval(p, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, HS.pchain(DR.NSeg{c}, lam, ds)))))):
  %Equal.sym(SK.VE, DR.Jd.x(DR.concl(es, fs, HS.pchain(DR.NSeg{c}, lam, ds))), HS.clin(es, DR.NSeg{c}, lam, HS.hxs(es, fs, ds)), HP.pchain_x(es, fs, DR.NSeg{c}, lam, ds))
    : S.Q.eq(E.qeval(p, SK.VE.cross(DC.lform(u), HS.clin(es, DR.NSeg{c}, lam, HS.hxs(es, fs, ds)))), E.qeval(p, SK.VE.cross(DC.lform(u), _)))
  LQ.q_refl(E.qeval(p, SK.VE.cross(DC.lform(u), HS.clin(es, DR.NSeg{c}, lam, HS.hxs(es, fs, ds)))))

# at each point, cross(u, y) = cross(u, the combination's form)
def tied_h0(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +c: Nat, +u: DR.Lab, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +y: SK.VE,
  +hr: {EP.rinv(DC.crosses(es, fs, u, ds), rows, 0n) == True{} : Bool}, +hin: {EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(u), y)))) == True{} : Bool})
  -> S.Q.eq(E.qeval(p, SK.VE.cross(DC.lform(u), y)), E.qeval(p, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, HS.pchain(DR.NSeg{c}, DV.dropls(DV.rescb(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), DV.resbt(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), SK.VE.cross(DC.lform(u), y), DC.crosses(es, fs, u, ds)), ds)))))):
  QA.ch4(E.qeval(p, SK.VE.cross(DC.lform(u), y)),
    E.qeval(p, SV.lin(DV.dropls(DV.rescb(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), DV.resbt(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), SK.VE.cross(DC.lform(u), y), DC.crosses(es, fs, u, ds)), DC.crosses(es, fs, u, ds))),
    E.qeval(p, SV.lin(DV.dropls(DV.rescb(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), DV.resbt(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), SK.VE.cross(DC.lform(u), y), DC.crosses(es, fs, u, ds)), crs(DC.lform(u), HS.hxs(es, fs, ds)))),
    E.qeval(p, SK.VE.cross(DC.lform(u), HS.clin(es, DR.NSeg{c}, DV.dropls(DV.rescb(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), DV.resbt(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), SK.VE.cross(DC.lform(u), y), DC.crosses(es, fs, u, ds)), HS.hxs(es, fs, ds)))),
    E.qeval(p, SK.VE.cross(DC.lform(u), DR.Jd.x(DR.concl(es, fs, HS.pchain(DR.NSeg{c}, DV.dropls(DV.rescb(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), DV.resbt(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), SK.VE.cross(DC.lform(u), y), DC.crosses(es, fs, u, ds)), ds))))),
    DV.derivable(DC.crosses(es, fs, u, ds), rows, SK.VE.cross(DC.lform(u), y), hr, hin)(p),
    crs_move(p, es, fs, u, DV.dropls(DV.rescb(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), DV.resbt(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), SK.VE.cross(DC.lform(u), y), DC.crosses(es, fs, u, ds)), ds),
    LQ.q_sym(E.qeval(p, SK.VE.cross(DC.lform(u), HS.clin(es, DR.NSeg{c}, DV.dropls(DV.rescb(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), DV.resbt(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), SK.VE.cross(DC.lform(u), y), DC.crosses(es, fs, u, ds)), HS.hxs(es, fs, ds)))),
      E.qeval(p, SV.lin(DV.dropls(DV.rescb(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), DV.resbt(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), SK.VE.cross(DC.lform(u), y), DC.crosses(es, fs, u, ds)), crs(DC.lform(u), HS.hxs(es, fs, ds)))),
      cross_clin.at(p, es, DR.NSeg{c}, DC.lform(u), DV.dropls(DV.rescb(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), DV.resbt(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), SK.VE.cross(DC.lform(u), y), DC.crosses(es, fs, u, ds)), HS.hxs(es, fs, ds))),
    xch_move(p, es, fs, c, u, DV.dropls(DV.rescb(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), DV.resbt(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), SK.VE.cross(DC.lform(u), y), DC.crosses(es, fs, u, ds)), ds))

# The tied derivation's form is y
# -------------------------------

def tdp(+u: DR.Lab, +y: SK.VE, +chx: SK.VE) -> E.QExpr:
  E.QMul{E.QCst{S.Q.inv(DC.lnorm(u))}, SK.VE.dot(DC.lform(u), SK.VE.sub(y, chx))}

def tdform(+u: DR.Lab, +y: SK.VE, +chx: SK.VE) -> SK.VE:
  DR.vlin(DR.qo(), chx, DR.qo(), DR.gmul(DR.Lab.conj(DR.Lab.conj(u)), SK.VE{tdp(u, y, chx), DR.cst(DR.qz())}))

def tdx.gen(+p: List<&2, S.Q>, +cu: S.Q, +su: S.Q, +y: SK.VE, +chx: SK.VE,
  h0: S.Q.eq(E.qeval(p, SK.VE.cross(DC.lform(DR.Lab{cu, su}), y)), E.qeval(p, SK.VE.cross(DC.lform(DR.Lab{cu, su}), chx))), hn: S.Q.eq(DC.lnorm(DR.Lab{cu, su}), DR.qz()) -> Empty)
  -> S.Q.eq(E.qeval(p, SK.VE.x(tdform(DR.Lab{cu, su}, y, chx))), E.qeval(p, SK.VE.x(y))):
  compx(cu, su, S.Q.neg(S.Q.neg(su)), E.qeval(p, SK.VE.x(y)), E.qeval(p, SK.VE.y(y)), E.qeval(p, SK.VE.x(chx)), E.qeval(p, SK.VE.y(chx)),
    tcross(cu, su, E.qeval(p, SK.VE.x(y)), E.qeval(p, SK.VE.y(y)), E.qeval(p, SK.VE.x(chx)), E.qeval(p, SK.VE.y(chx)), h0), hn)

def tdy.gen(+p: List<&2, S.Q>, +cu: S.Q, +su: S.Q, +y: SK.VE, +chx: SK.VE,
  h0: S.Q.eq(E.qeval(p, SK.VE.cross(DC.lform(DR.Lab{cu, su}), y)), E.qeval(p, SK.VE.cross(DC.lform(DR.Lab{cu, su}), chx))), hn: S.Q.eq(DC.lnorm(DR.Lab{cu, su}), DR.qz()) -> Empty)
  -> S.Q.eq(E.qeval(p, SK.VE.y(tdform(DR.Lab{cu, su}, y, chx))), E.qeval(p, SK.VE.y(y))):
  compy(cu, su, E.qeval(p, SK.VE.x(y)), E.qeval(p, SK.VE.y(y)), E.qeval(p, SK.VE.x(chx)), E.qeval(p, SK.VE.y(chx)),
    tcross(cu, su, E.qeval(p, SK.VE.x(y)), E.qeval(p, SK.VE.y(y)), E.qeval(p, SK.VE.x(chx)), E.qeval(p, SK.VE.y(chx)), h0), hn)

def tdlam(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +y: SK.VE) -> List<&2, S.Q>:
  DV.dropls(DV.rescb(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), DV.resbt(EL.resid(rows, SK.VE.cross(DC.lform(u), y))), SK.VE.cross(DC.lform(u), y), DC.crosses(es, fs, u, ds))

def tdx.at(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +c: Nat, +cu: S.Q, +su: S.Q, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +y: SK.VE,
  +hr: {EP.rinv(DC.crosses(es, fs, DR.Lab{cu, su}, ds), rows, 0n) == True{} : Bool}, +hin: {EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(DR.Lab{cu, su}), y)))) == True{} : Bool}, +hnz: NZ.Nz(DR.Lab{cu, su}))
  -> S.Q.eq(E.qeval(p, SK.VE.x(tdform(DR.Lab{cu, su}, y, DR.Jd.x(DR.concl(es, fs, HS.pchain(DR.NSeg{c}, tdlam(es, fs, DR.Lab{cu, su}, rows, ds, y), ds)))))), E.qeval(p, SK.VE.x(y))):
  tdx.gen(p, cu, su, y, DR.Jd.x(DR.concl(es, fs, HS.pchain(DR.NSeg{c}, tdlam(es, fs, DR.Lab{cu, su}, rows, ds, y), ds))),
    tied_h0(p, es, fs, c, DR.Lab{cu, su}, rows, ds, y, hr, hin), e => LP.qnz_t(DC.lnorm(DR.Lab{cu, su}), hnz, e))

def tdy.at(+p: List<&2, S.Q>, +es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +c: Nat, +cu: S.Q, +su: S.Q, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +y: SK.VE,
  +hr: {EP.rinv(DC.crosses(es, fs, DR.Lab{cu, su}, ds), rows, 0n) == True{} : Bool}, +hin: {EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(DR.Lab{cu, su}), y)))) == True{} : Bool}, +hnz: NZ.Nz(DR.Lab{cu, su}))
  -> S.Q.eq(E.qeval(p, SK.VE.y(tdform(DR.Lab{cu, su}, y, DR.Jd.x(DR.concl(es, fs, HS.pchain(DR.NSeg{c}, tdlam(es, fs, DR.Lab{cu, su}, rows, ds, y), ds)))))), E.qeval(p, SK.VE.y(y))):
  tdy.gen(p, cu, su, y, DR.Jd.x(DR.concl(es, fs, HS.pchain(DR.NSeg{c}, tdlam(es, fs, DR.Lab{cu, su}, rows, ds, y), ds))),
    tied_h0(p, es, fs, c, DR.Lab{cu, su}, rows, ds, y, hr, hin), e => LP.qnz_t(DC.lnorm(DR.Lab{cu, su}), hnz, e))

# the tied derivation's form is the same as y
def td_same(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +c: Nat, +cu: S.Q, +su: S.Q, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +y: SK.VE,
  +hr: {EP.rinv(DC.crosses(es, fs, DR.Lab{cu, su}, ds), rows, 0n) == True{} : Bool}, +hin: {EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(DR.Lab{cu, su}), y)))) == True{} : Bool}, +hnz: NZ.Nz(DR.Lab{cu, su}))
  -> VD.SameVD(tdform(DR.Lab{cu, su}, y, DR.Jd.x(DR.concl(es, fs, HS.pchain(DR.NSeg{c}, tdlam(es, fs, DR.Lab{cu, su}, rows, ds, y), ds)))), y):
  (ID.qzero_ident(SK.VE.x(tdform(DR.Lab{cu, su}, y, DR.Jd.x(DR.concl(es, fs, HS.pchain(DR.NSeg{c}, tdlam(es, fs, DR.Lab{cu, su}, rows, ds, y), ds))))), SK.VE.x(y),
     p => tdx.at(p, es, fs, c, cu, su, rows, ds, y, hr, hin, hnz)),
   ID.qzero_ident(SK.VE.y(tdform(DR.Lab{cu, su}, y, DR.Jd.x(DR.concl(es, fs, HS.pchain(DR.NSeg{c}, tdlam(es, fs, DR.Lab{cu, su}, rows, ds, y), ds))))), SK.VE.y(y),
     p => tdy.at(p, es, fs, c, cu, su, rows, ds, y, hr, hin, hnz)))

# The tied derivation is valid
# ----------------------------

def vb_p(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +u: DR.Lab, +y: SK.VE, +chx: SK.VE, +t: Nat, hy: HP.VBelow(y, t), hc: HP.VBelow(chx, t)) -> {SP.vbelow(tdp(u, y, chx), t) == True{} : Bool}:
  match u:
    case DR.Lab{c, s}:
      (+y1, +y2) = hy
      (+c1, +c2) = hc
      HP.band_tt(SV.band(SP.vbelow(SK.VE.x(y), t), SP.vbelow(SK.VE.x(chx), t)), SV.band(SP.vbelow(SK.VE.y(y), t), SP.vbelow(SK.VE.y(chx), t)),
        HP.band_tt(SP.vbelow(SK.VE.x(y), t), SP.vbelow(SK.VE.x(chx), t), y1, c1), HP.band_tt(SP.vbelow(SK.VE.y(y), t), SP.vbelow(SK.VE.y(chx), t), y2, c2))

def tied.vd(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, +u: DR.Lab, +du: DR.Der, +ch: DR.Der, +y: SK.VE,
  +vch: VD.VD(es, fs, ctx, ch), +pch: VD.Isp(DR.concl(es, fs, ch)), +ach: {DR.Jd.a(DR.concl(es, fs, ch)) == DR.NSeg{c} : DR.Node}, htie: RP.TieOk(es, fs, ctx, t, c, u, du))
  -> SK.Both(VD.VD(es, fs, ctx, DR.DPLin{DR.qo(), ch, DR.qo(), DR.DThrough{du, DR.DFrame{DR.DZero{}, SK.VE{tdp(u, y, DR.Jd.x(DR.concl(es, fs, ch))), DR.cst(DR.qz())}}, DR.Lab.conj(u), DR.NFrame{}}}),
       SK.Both(VD.Isp(DR.concl(es, fs, DR.DPLin{DR.qo(), ch, DR.qo(), DR.DThrough{du, DR.DFrame{DR.DZero{}, SK.VE{tdp(u, y, DR.Jd.x(DR.concl(es, fs, ch))), DR.cst(DR.qz())}}, DR.Lab.conj(u), DR.NFrame{}}})),
         {DR.Jd.a(DR.concl(es, fs, DR.DPLin{DR.qo(), ch, DR.qo(), DR.DThrough{du, DR.DFrame{DR.DZero{}, SK.VE{tdp(u, y, DR.Jd.x(DR.concl(es, fs, ch))), DR.cst(DR.qz())}}, DR.Lab.conj(u), DR.NFrame{}}})) == DR.NSeg{c} : DR.Node})):
  (pg, s1) = htie
  (vdu, q1) = pg
  (pdu, q2) = q1
  (adu, bdu) = q2
  (svdu, nz) = s1
  ((vch, ((vdu, ((Unit{}, ({==}, {==})), (pdu, ({==}, (GN.samevd_tr(DR.Jd.x(DR.concl(es, fs, du)), DC.lform(u), DR.gmul(DR.Lab.conj(DR.Lab.conj(u)), DR.zdir(es, DR.NFrame{})), svdu, GN.cc(u, DR.zdir(es, DR.NFrame{}))), ({==}, {==})))))),
     (pch, ({==}, Equal.trans(DR.Node, DR.Jd.a(DR.concl(es, fs, ch)), DR.NSeg{c}, DR.Jd.a(DR.concl(es, fs, du)), ach, Equal.sym(DR.Node, DR.Jd.a(DR.concl(es, fs, du)), DR.NSeg{c}, adu)))))),
   ({==}, ach))

def tied.vd0(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, +u: DR.Lab, +du: DR.Der, +ch: DR.Der, +y: SK.VE,
  pk: SK.Both(VD.VD(es, fs, ctx, ch), SK.Both(VD.Isp(DR.concl(es, fs, ch)), {DR.Jd.a(DR.concl(es, fs, ch)) == DR.NSeg{c} : DR.Node})), htie: RP.TieOk(es, fs, ctx, t, c, u, du))
  -> SK.Both(VD.VD(es, fs, ctx, DR.DPLin{DR.qo(), ch, DR.qo(), DR.DThrough{du, DR.DFrame{DR.DZero{}, SK.VE{tdp(u, y, DR.Jd.x(DR.concl(es, fs, ch))), DR.cst(DR.qz())}}, DR.Lab.conj(u), DR.NFrame{}}}),
       SK.Both(VD.Isp(DR.concl(es, fs, DR.DPLin{DR.qo(), ch, DR.qo(), DR.DThrough{du, DR.DFrame{DR.DZero{}, SK.VE{tdp(u, y, DR.Jd.x(DR.concl(es, fs, ch))), DR.cst(DR.qz())}}, DR.Lab.conj(u), DR.NFrame{}}})),
         {DR.Jd.a(DR.concl(es, fs, DR.DPLin{DR.qo(), ch, DR.qo(), DR.DThrough{du, DR.DFrame{DR.DZero{}, SK.VE{tdp(u, y, DR.Jd.x(DR.concl(es, fs, ch))), DR.cst(DR.qz())}}, DR.Lab.conj(u), DR.NFrame{}}})) == DR.NSeg{c} : DR.Node})):
  (vch, r1) = pk
  (pch, ach) = r1
  tied.vd(es, fs, ctx, t, c, u, du, ch, y, vch, pch, ach, htie)

def tied.bch(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, +u: DR.Lab, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +y: SK.VE,
  +ha: IV.AllPD(es, fs, ctx, DR.NSeg{c}, t, ds), +hz: {DC.zb(es, t) == True{} : Bool}) -> HP.VBelow(DR.Jd.x(DR.concl(es, fs, HS.pchain(DR.NSeg{c}, tdlam(es, fs, u, rows, ds, y), ds))), t):
  DD.hs_der.below(es, fs, DR.NSeg{c}, t, tdlam(es, fs, u, rows, ds, y), ds,
    HP.clin_below(es, DR.NSeg{c}, t, tdlam(es, fs, u, rows, ds, y), HS.hxs(es, fs, ds), DD.allpd_below(ds, es, fs, ctx, DR.NSeg{c}, t, ha), BL.zdir_below(es, t, DR.NSeg{c}, hz)))

def tied_ok.go(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, +cu: S.Q, +su: S.Q, +du: DR.Der, +rows: List<&2, EL.Row>, +ds: List<&2, DR.Der>, +y: SK.VE,
  +hr: {EP.rinv(DC.crosses(es, fs, DR.Lab{cu, su}, ds), rows, 0n) == True{} : Bool}, +ha: IV.AllPD(es, fs, ctx, DR.NSeg{c}, t, ds), +htie: RP.TieOk(es, fs, ctx, t, c, DR.Lab{cu, su}, du),
  +hz: {DC.zb(es, t) == True{} : Bool}, +hin: {EP.isnil(EP.resp(EL.resid(rows, SK.VE.cross(DC.lform(DR.Lab{cu, su}), y)))) == True{} : Bool}, +hy: HP.VBelow(y, t))
  -> SK.Both(SK.Both(SK.Both(VD.VD(es, fs, ctx, DC.tied.der(es, fs, c, DR.Lab{cu, su}, du, DC.TS{rows, ds}, y)), SK.Both(VD.Isp(DR.concl(es, fs, DC.tied.der(es, fs, c, DR.Lab{cu, su}, du, DC.TS{rows, ds}, y))), {DR.Jd.a(DR.concl(es, fs, DC.tied.der(es, fs, c, DR.Lab{cu, su}, du, DC.TS{rows, ds}, y))) == DR.NSeg{c} : DR.Node})),
       HP.VBelow(DR.Jd.x(DR.concl(es, fs, DC.tied.der(es, fs, c, DR.Lab{cu, su}, du, DC.TS{rows, ds}, y))), t)), VD.SameVD(DR.Jd.x(DR.concl(es, fs, DC.tied.der(es, fs, c, DR.Lab{cu, su}, du, DC.TS{rows, ds}, y))), y)):
  (pg, s1) = htie
  (svdu, nz) = s1
  ((tied.vd0(es, fs, ctx, t, c, DR.Lab{cu, su}, du, HS.pchain(DR.NSeg{c}, tdlam(es, fs, DR.Lab{cu, su}, rows, ds, y), ds), y, DD.pchain_okd(tdlam(es, fs, DR.Lab{cu, su}, rows, ds, y), ds, es, fs, ctx, DR.NSeg{c}, t, ha), htie),
    HP.vlin_below(DR.qo(), DR.Jd.x(DR.concl(es, fs, HS.pchain(DR.NSeg{c}, tdlam(es, fs, DR.Lab{cu, su}, rows, ds, y), ds))), DR.qo(),
      DR.gmul(DR.Lab.conj(DR.Lab.conj(DR.Lab{cu, su})), SK.VE{tdp(DR.Lab{cu, su}, y, DR.Jd.x(DR.concl(es, fs, HS.pchain(DR.NSeg{c}, tdlam(es, fs, DR.Lab{cu, su}, rows, ds, y), ds)))), DR.cst(DR.qz())}), t,
      tied.bch(es, fs, ctx, t, c, DR.Lab{cu, su}, rows, ds, y, ha, hz),
      BL.vb_gmul(DR.Lab.conj(DR.Lab.conj(DR.Lab{cu, su})), SK.VE{tdp(DR.Lab{cu, su}, y, DR.Jd.x(DR.concl(es, fs, HS.pchain(DR.NSeg{c}, tdlam(es, fs, DR.Lab{cu, su}, rows, ds, y), ds)))), DR.cst(DR.qz())}, t,
        (vb_p(es, fs, DR.Lab{cu, su}, y, DR.Jd.x(DR.concl(es, fs, HS.pchain(DR.NSeg{c}, tdlam(es, fs, DR.Lab{cu, su}, rows, ds, y), ds))), t, hy, tied.bch(es, fs, ctx, t, c, DR.Lab{cu, su}, rows, ds, y, ha, hz)), {==})))),
   td_same(es, fs, c, cu, su, rows, ds, y, hr, hin, nz))

# y in a tied set: its derivation is VD, at c, below t, the same as y
def tied_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +t: Nat, +c: Nat, u: DR.Lab, +du: DR.Der, s: DC.TS, +y: SK.VE,
  hti: RP.TInvD(es, fs, ctx, DR.NSeg{c}, t, u, s), +htie: RP.TieOk(es, fs, ctx, t, c, u, du), +hz: {DC.zb(es, t) == True{} : Bool}, +hin: {DC.ts.inb(s, u, y) == True{} : Bool}, +hy: HP.VBelow(y, t))
  -> SK.Both(SK.Both(SK.Both(VD.VD(es, fs, ctx, DC.tied.der(es, fs, c, u, du, s, y)), SK.Both(VD.Isp(DR.concl(es, fs, DC.tied.der(es, fs, c, u, du, s, y))), {DR.Jd.a(DR.concl(es, fs, DC.tied.der(es, fs, c, u, du, s, y))) == DR.NSeg{c} : DR.Node})),
       HP.VBelow(DR.Jd.x(DR.concl(es, fs, DC.tied.der(es, fs, c, u, du, s, y))), t)), VD.SameVD(DR.Jd.x(DR.concl(es, fs, DC.tied.der(es, fs, c, u, du, s, y))), y)):
  match u s:
    case DR.Lab{+cu, +su} DC.TS{+rows, +ds}:
      (hr, r1) = hti
      (hl, ha) = r1
      tied_ok.go(es, fs, ctx, t, c, cu, su, du, rows, ds, y, hr, ha, htie, hz, hin, hy)
