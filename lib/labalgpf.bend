# bend-cad: label algebra for the closure theorem (PLAN-sk13b B3), as
# identities of forms in reusable Data form (lib/dcvd.bend's SameVD):
# - a real label acts as a scalar (gmul_real);
# - gmul is linear in the label (gmul_lin);
# - w conj(w) = |w|^2, real (lmul_conj);
# - for a label u not real, i y = (1/s)(u y) - (c/s) y (gmul_i);
# - equal labels act alike (gle), rotations commute (gswap), conj of a
#   product (gconj_mul), zero labels (gmul_zero), g = 2 Re(g) - conj(g)
#   (g2re), and gmul is linear in the form (gmul_vlin).
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
import ./dclose.bend as DC
import ./dcvd.bend as VD
import ./dcgenpf.bend as GN
import ./dcmergepf.bend as MG

# Q(c, 0) y = c y (as vlin(c, y, 0, y))
def gr.ax(+p: List<&2, S.Q>, +c: S.Q, +y: SK.VE) -> S.Q.eq(E.qeval(p, SK.VE.x(DR.gmul(DR.Lab{c, DR.qz()}, y))), E.qeval(p, SK.VE.x(DR.vlin(c, y, DR.qz(), y)))):
  QR.qring_eq([c, E.qeval(p, SK.VE.x(y)), E.qeval(p, SK.VE.y(y))],
    E.QSub{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{2n}}}, E.QAdd{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}}, {==})

def gr.ay(+p: List<&2, S.Q>, +c: S.Q, +y: SK.VE) -> S.Q.eq(E.qeval(p, SK.VE.y(DR.gmul(DR.Lab{c, DR.qz()}, y))), E.qeval(p, SK.VE.y(DR.vlin(c, y, DR.qz(), y)))):
  QR.qring_eq([c, E.qeval(p, SK.VE.x(y)), E.qeval(p, SK.VE.y(y))],
    E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}, E.QMul{E.QVar{0n}, E.QVar{2n}}}, E.QAdd{E.QMul{E.QVar{0n}, E.QVar{2n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{2n}}}, {==})

# a real label is a scalar
def gmul_real(+c: S.Q, +y: SK.VE) -> VD.SameVD(DR.gmul(DR.Lab{c, DR.qz()}, y), DR.vlin(c, y, DR.qz(), y)):
  (ID.qzero_ident(SK.VE.x(DR.gmul(DR.Lab{c, DR.qz()}, y)), SK.VE.x(DR.vlin(c, y, DR.qz(), y)), p => gr.ax(p, c, y)),
   ID.qzero_ident(SK.VE.y(DR.gmul(DR.Lab{c, DR.qz()}, y)), SK.VE.y(DR.vlin(c, y, DR.qz(), y)), p => gr.ay(p, c, y)))

def lcomb.go(+a: S.Q, +c1: S.Q, +s1: S.Q, +b: S.Q, u2: DR.Lab) -> DR.Lab:
  match u2:
    case DR.Lab{+c2, +s2}:
      DR.Lab{S.Q.add(S.Q.mul(a, c1), S.Q.mul(b, c2)), S.Q.add(S.Q.mul(a, s1), S.Q.mul(b, s2))}

# the label (a c1 + b c2, a s1 + b s2)
def lcomb(+a: S.Q, u1: DR.Lab, +b: S.Q, +u2: DR.Lab) -> DR.Lab:
  match u1:
    case DR.Lab{+c1, +s1}:
      lcomb.go(a, c1, s1, b, u2)


# Linearity in the label
# ----------------------

def glin_x(+a: S.Q, +b: S.Q, +c1: S.Q, +s1: S.Q, +c2: S.Q, +s2: S.Q, +y1: S.Q, +y2: S.Q) -> S.Q.eq(S.Q.sub(S.Q.mul(S.Q.add(S.Q.mul(a, c1), S.Q.mul(b, c2)), y1), S.Q.mul(S.Q.add(S.Q.mul(a, s1), S.Q.mul(b, s2)), y2)), S.Q.add(S.Q.mul(a, S.Q.sub(S.Q.mul(c1, y1), S.Q.mul(s1, y2))), S.Q.mul(b, S.Q.sub(S.Q.mul(c2, y1), S.Q.mul(s2, y2))))):
  QA.ch4(S.Q.sub(S.Q.mul(S.Q.add(S.Q.mul(a, c1), S.Q.mul(b, c2)), y1), S.Q.mul(S.Q.add(S.Q.mul(a, s1), S.Q.mul(b, s2)), y2)), S.Q.sub(S.Q.add(S.Q.mul(S.Q.mul(a, c1), y1), S.Q.mul(S.Q.mul(b, c2), y1)), S.Q.add(S.Q.mul(S.Q.mul(a, s1), y2), S.Q.mul(S.Q.mul(b, s2), y2))), S.Q.add(S.Q.sub(S.Q.mul(S.Q.mul(a, c1), y1), S.Q.mul(S.Q.mul(a, s1), y2)), S.Q.sub(S.Q.mul(S.Q.mul(b, c2), y1), S.Q.mul(S.Q.mul(b, s2), y2))), S.Q.add(S.Q.sub(S.Q.mul(a, S.Q.mul(c1, y1)), S.Q.mul(a, S.Q.mul(s1, y2))), S.Q.sub(S.Q.mul(b, S.Q.mul(c2, y1)), S.Q.mul(b, S.Q.mul(s2, y2)))), S.Q.add(S.Q.mul(a, S.Q.sub(S.Q.mul(c1, y1), S.Q.mul(s1, y2))), S.Q.mul(b, S.Q.sub(S.Q.mul(c2, y1), S.Q.mul(s2, y2)))),
    QA.sub_cong(S.Q.mul(S.Q.add(S.Q.mul(a, c1), S.Q.mul(b, c2)), y1), S.Q.add(S.Q.mul(S.Q.mul(a, c1), y1), S.Q.mul(S.Q.mul(b, c2), y1)), S.Q.mul(S.Q.add(S.Q.mul(a, s1), S.Q.mul(b, s2)), y2), S.Q.add(S.Q.mul(S.Q.mul(a, s1), y2), S.Q.mul(S.Q.mul(b, s2), y2)), QA.rdist(S.Q.mul(a, c1), S.Q.mul(b, c2), y1), QA.rdist(S.Q.mul(a, s1), S.Q.mul(b, s2), y2)),
    QA.r4c(S.Q.mul(S.Q.mul(a, c1), y1), S.Q.mul(S.Q.mul(b, c2), y1), S.Q.mul(S.Q.mul(a, s1), y2), S.Q.mul(S.Q.mul(b, s2), y2)),
    QA.add_cong(S.Q.sub(S.Q.mul(S.Q.mul(a, c1), y1), S.Q.mul(S.Q.mul(a, s1), y2)), S.Q.sub(S.Q.mul(a, S.Q.mul(c1, y1)), S.Q.mul(a, S.Q.mul(s1, y2))), S.Q.sub(S.Q.mul(S.Q.mul(b, c2), y1), S.Q.mul(S.Q.mul(b, s2), y2)), S.Q.sub(S.Q.mul(b, S.Q.mul(c2, y1)), S.Q.mul(b, S.Q.mul(s2, y2))), QA.sub_cong(S.Q.mul(S.Q.mul(a, c1), y1), S.Q.mul(a, S.Q.mul(c1, y1)), S.Q.mul(S.Q.mul(a, s1), y2), S.Q.mul(a, S.Q.mul(s1, y2)), QA.massoc(a, c1, y1), QA.massoc(a, s1, y2)), QA.sub_cong(S.Q.mul(S.Q.mul(b, c2), y1), S.Q.mul(b, S.Q.mul(c2, y1)), S.Q.mul(S.Q.mul(b, s2), y2), S.Q.mul(b, S.Q.mul(s2, y2)), QA.massoc(b, c2, y1), QA.massoc(b, s2, y2))),
    QA.add_cong(S.Q.sub(S.Q.mul(a, S.Q.mul(c1, y1)), S.Q.mul(a, S.Q.mul(s1, y2))), S.Q.mul(a, S.Q.sub(S.Q.mul(c1, y1), S.Q.mul(s1, y2))), S.Q.sub(S.Q.mul(b, S.Q.mul(c2, y1)), S.Q.mul(b, S.Q.mul(s2, y2))), S.Q.mul(b, S.Q.sub(S.Q.mul(c2, y1), S.Q.mul(s2, y2))), LQ.q_sym(S.Q.mul(a, S.Q.sub(S.Q.mul(c1, y1), S.Q.mul(s1, y2))), S.Q.sub(S.Q.mul(a, S.Q.mul(c1, y1)), S.Q.mul(a, S.Q.mul(s1, y2))), QA.ldsub(a, S.Q.mul(c1, y1), S.Q.mul(s1, y2))), LQ.q_sym(S.Q.mul(b, S.Q.sub(S.Q.mul(c2, y1), S.Q.mul(s2, y2))), S.Q.sub(S.Q.mul(b, S.Q.mul(c2, y1)), S.Q.mul(b, S.Q.mul(s2, y2))), QA.ldsub(b, S.Q.mul(c2, y1), S.Q.mul(s2, y2)))))

def glin_y(+a: S.Q, +b: S.Q, +c1: S.Q, +s1: S.Q, +c2: S.Q, +s2: S.Q, +y1: S.Q, +y2: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(a, s1), S.Q.mul(b, s2)), y1), S.Q.mul(S.Q.add(S.Q.mul(a, c1), S.Q.mul(b, c2)), y2)), S.Q.add(S.Q.mul(a, S.Q.add(S.Q.mul(s1, y1), S.Q.mul(c1, y2))), S.Q.mul(b, S.Q.add(S.Q.mul(s2, y1), S.Q.mul(c2, y2))))):
  QA.ch4(S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(a, s1), S.Q.mul(b, s2)), y1), S.Q.mul(S.Q.add(S.Q.mul(a, c1), S.Q.mul(b, c2)), y2)), S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(a, s1), y1), S.Q.mul(S.Q.mul(b, s2), y1)), S.Q.add(S.Q.mul(S.Q.mul(a, c1), y2), S.Q.mul(S.Q.mul(b, c2), y2))), S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(a, s1), y1), S.Q.mul(S.Q.mul(a, c1), y2)), S.Q.add(S.Q.mul(S.Q.mul(b, s2), y1), S.Q.mul(S.Q.mul(b, c2), y2))), S.Q.add(S.Q.add(S.Q.mul(a, S.Q.mul(s1, y1)), S.Q.mul(a, S.Q.mul(c1, y2))), S.Q.add(S.Q.mul(b, S.Q.mul(s2, y1)), S.Q.mul(b, S.Q.mul(c2, y2)))), S.Q.add(S.Q.mul(a, S.Q.add(S.Q.mul(s1, y1), S.Q.mul(c1, y2))), S.Q.mul(b, S.Q.add(S.Q.mul(s2, y1), S.Q.mul(c2, y2)))),
    QA.add_cong(S.Q.mul(S.Q.add(S.Q.mul(a, s1), S.Q.mul(b, s2)), y1), S.Q.add(S.Q.mul(S.Q.mul(a, s1), y1), S.Q.mul(S.Q.mul(b, s2), y1)), S.Q.mul(S.Q.add(S.Q.mul(a, c1), S.Q.mul(b, c2)), y2), S.Q.add(S.Q.mul(S.Q.mul(a, c1), y2), S.Q.mul(S.Q.mul(b, c2), y2)), QA.rdist(S.Q.mul(a, s1), S.Q.mul(b, s2), y1), QA.rdist(S.Q.mul(a, c1), S.Q.mul(b, c2), y2)),
    QA.m4(S.Q.mul(S.Q.mul(a, s1), y1), S.Q.mul(S.Q.mul(b, s2), y1), S.Q.mul(S.Q.mul(a, c1), y2), S.Q.mul(S.Q.mul(b, c2), y2)),
    QA.add_cong(S.Q.add(S.Q.mul(S.Q.mul(a, s1), y1), S.Q.mul(S.Q.mul(a, c1), y2)), S.Q.add(S.Q.mul(a, S.Q.mul(s1, y1)), S.Q.mul(a, S.Q.mul(c1, y2))), S.Q.add(S.Q.mul(S.Q.mul(b, s2), y1), S.Q.mul(S.Q.mul(b, c2), y2)), S.Q.add(S.Q.mul(b, S.Q.mul(s2, y1)), S.Q.mul(b, S.Q.mul(c2, y2))), QA.add_cong(S.Q.mul(S.Q.mul(a, s1), y1), S.Q.mul(a, S.Q.mul(s1, y1)), S.Q.mul(S.Q.mul(a, c1), y2), S.Q.mul(a, S.Q.mul(c1, y2)), QA.massoc(a, s1, y1), QA.massoc(a, c1, y2)), QA.add_cong(S.Q.mul(S.Q.mul(b, s2), y1), S.Q.mul(b, S.Q.mul(s2, y1)), S.Q.mul(S.Q.mul(b, c2), y2), S.Q.mul(b, S.Q.mul(c2, y2)), QA.massoc(b, s2, y1), QA.massoc(b, c2, y2))),
    QA.add_cong(S.Q.add(S.Q.mul(a, S.Q.mul(s1, y1)), S.Q.mul(a, S.Q.mul(c1, y2))), S.Q.mul(a, S.Q.add(S.Q.mul(s1, y1), S.Q.mul(c1, y2))), S.Q.add(S.Q.mul(b, S.Q.mul(s2, y1)), S.Q.mul(b, S.Q.mul(c2, y2))), S.Q.mul(b, S.Q.add(S.Q.mul(s2, y1), S.Q.mul(c2, y2))), LQ.q_sym(S.Q.mul(a, S.Q.add(S.Q.mul(s1, y1), S.Q.mul(c1, y2))), S.Q.add(S.Q.mul(a, S.Q.mul(s1, y1)), S.Q.mul(a, S.Q.mul(c1, y2))), QA.ldist(a, S.Q.mul(s1, y1), S.Q.mul(c1, y2))), LQ.q_sym(S.Q.mul(b, S.Q.add(S.Q.mul(s2, y1), S.Q.mul(c2, y2))), S.Q.add(S.Q.mul(b, S.Q.mul(s2, y1)), S.Q.mul(b, S.Q.mul(c2, y2))), QA.ldist(b, S.Q.mul(s2, y1), S.Q.mul(c2, y2)))))

def glin.ax(+p: List<&2, S.Q>, +a: S.Q, +c1: S.Q, +s1: S.Q, +b: S.Q, +c2: S.Q, +s2: S.Q, +y: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.x(DR.gmul(lcomb(a, DR.Lab{c1, s1}, b, DR.Lab{c2, s2}), y))), E.qeval(p, SK.VE.x(DR.vlin(a, DR.gmul(DR.Lab{c1, s1}, y), b, DR.gmul(DR.Lab{c2, s2}, y))))):
  glin_x(a, b, c1, s1, c2, s2, E.qeval(p, SK.VE.x(y)), E.qeval(p, SK.VE.y(y)))

def glin.ay(+p: List<&2, S.Q>, +a: S.Q, +c1: S.Q, +s1: S.Q, +b: S.Q, +c2: S.Q, +s2: S.Q, +y: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.y(DR.gmul(lcomb(a, DR.Lab{c1, s1}, b, DR.Lab{c2, s2}), y))), E.qeval(p, SK.VE.y(DR.vlin(a, DR.gmul(DR.Lab{c1, s1}, y), b, DR.gmul(DR.Lab{c2, s2}, y))))):
  glin_y(a, b, c1, s1, c2, s2, E.qeval(p, SK.VE.x(y)), E.qeval(p, SK.VE.y(y)))

# (a u1 + b u2) y = a (u1 y) + b (u2 y)
def gmul_lin(+a: S.Q, u1: DR.Lab, +b: S.Q, u2: DR.Lab, +y: SK.VE) -> VD.SameVD(DR.gmul(lcomb(a, u1, b, u2), y), DR.vlin(a, DR.gmul(u1, y), b, DR.gmul(u2, y))):
  match u1 u2:
    case DR.Lab{+c1, +s1} DR.Lab{+c2, +s2}:
      (ID.qzero_ident(SK.VE.x(DR.gmul(lcomb(a, DR.Lab{c1, s1}, b, DR.Lab{c2, s2}), y)), SK.VE.x(DR.vlin(a, DR.gmul(DR.Lab{c1, s1}, y), b, DR.gmul(DR.Lab{c2, s2}, y))), p => glin.ax(p, a, c1, s1, b, c2, s2, y)),
       ID.qzero_ident(SK.VE.y(DR.gmul(lcomb(a, DR.Lab{c1, s1}, b, DR.Lab{c2, s2}), y)), SK.VE.y(DR.vlin(a, DR.gmul(DR.Lab{c1, s1}, y), b, DR.gmul(DR.Lab{c2, s2}, y))), p => glin.ay(p, a, c1, s1, b, c2, s2, y)))


# Rationals and labels equal, as reusable Data
# --------------------------------------------

# a = b in the normalizer's form on constants
def QE(+a: S.Q, +b: S.Q) -> Data:
  VD.SameD(DR.cst(a), DR.cst(b))

def qe_of(+a: S.Q, +b: S.Q, h: S.Q.eq(a, b)) -> QE(a, b):
  ID.qzero_ident(DR.cst(a), DR.cst(b), p => h)

def qe_ok(+a: S.Q, +b: S.Q, +h: QE(a, b)) -> S.Q.eq(a, b):
  ID.ident_ok(DR.cst(a), DR.cst(b), h)(Nil{})

def lab.c(g: DR.Lab) -> S.Q:
  match g:
    case DR.Lab{c, s}:
      c

def lab.s(g: DR.Lab) -> S.Q:
  match g:
    case DR.Lab{c, s}:
      s

# g = h, part by part
def LE(+g: DR.Lab, +h: DR.Lab) -> Data:
  SK.Both(QE(lab.c(g), lab.c(h)), QE(lab.s(g), lab.s(h)))

def le_of(+c1: S.Q, +s1: S.Q, +c2: S.Q, +s2: S.Q, hc: S.Q.eq(c1, c2), hs: S.Q.eq(s1, s2)) -> LE(DR.Lab{c1, s1}, DR.Lab{c2, s2}):
  (qe_of(c1, c2, hc), qe_of(s1, s2, hs))

def lcong.ax(+p: List<&2, S.Q>, +c1: S.Q, +s1: S.Q, +c2: S.Q, +s2: S.Q, +x: SK.VE, +hc: QE(c1, c2), +hs: QE(s1, s2))
  -> S.Q.eq(E.qeval(p, SK.VE.x(DR.gmul(DR.Lab{c1, s1}, x))), E.qeval(p, SK.VE.x(DR.gmul(DR.Lab{c2, s2}, x)))):
  QA.sub_cong(S.Q.mul(c1, E.qeval(p, SK.VE.x(x))), S.Q.mul(c2, E.qeval(p, SK.VE.x(x))), S.Q.mul(s1, E.qeval(p, SK.VE.y(x))), S.Q.mul(s2, E.qeval(p, SK.VE.y(x))), LQ.q_mul_cong_l(c1, c2, E.qeval(p, SK.VE.x(x)), qe_ok(c1, c2, hc)), LQ.q_mul_cong_l(s1, s2, E.qeval(p, SK.VE.y(x)), qe_ok(s1, s2, hs)))

def lcong.ay(+p: List<&2, S.Q>, +c1: S.Q, +s1: S.Q, +c2: S.Q, +s2: S.Q, +x: SK.VE, +hc: QE(c1, c2), +hs: QE(s1, s2))
  -> S.Q.eq(E.qeval(p, SK.VE.y(DR.gmul(DR.Lab{c1, s1}, x))), E.qeval(p, SK.VE.y(DR.gmul(DR.Lab{c2, s2}, x)))):
  QA.add_cong(S.Q.mul(s1, E.qeval(p, SK.VE.x(x))), S.Q.mul(s2, E.qeval(p, SK.VE.x(x))), S.Q.mul(c1, E.qeval(p, SK.VE.y(x))), S.Q.mul(c2, E.qeval(p, SK.VE.y(x))), LQ.q_mul_cong_l(s1, s2, E.qeval(p, SK.VE.x(x)), qe_ok(s1, s2, hs)), LQ.q_mul_cong_l(c1, c2, E.qeval(p, SK.VE.y(x)), qe_ok(c1, c2, hc)))

def lcong.go(+c1: S.Q, +s1: S.Q, +c2: S.Q, +s2: S.Q, +x: SK.VE, h: SK.Both(QE(c1, c2), QE(s1, s2))) -> VD.SameVD(DR.gmul(DR.Lab{c1, s1}, x), DR.gmul(DR.Lab{c2, s2}, x)):
  (+hc, +hs) = h
  (ID.qzero_ident(SK.VE.x(DR.gmul(DR.Lab{c1, s1}, x)), SK.VE.x(DR.gmul(DR.Lab{c2, s2}, x)), p => lcong.ax(p, c1, s1, c2, s2, x, hc, hs)),
   ID.qzero_ident(SK.VE.y(DR.gmul(DR.Lab{c1, s1}, x)), SK.VE.y(DR.gmul(DR.Lab{c2, s2}, x)), p => lcong.ay(p, c1, s1, c2, s2, x, hc, hs)))

# equal labels act alike
def gle(g: DR.Lab, h: DR.Lab, +x: SK.VE, e: LE(g, h)) -> VD.SameVD(DR.gmul(g, x), DR.gmul(h, x)):
  match g h:
    case DR.Lab{+c1, +s1} DR.Lab{+c2, +s2}:
      lcong.go(c1, s1, c2, s2, x, e)

def cw.c(+c: S.Q, +s: S.Q) -> S.Q.eq(S.Q.sub(S.Q.mul(c, c), S.Q.mul(S.Q.neg(s), s)), S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))):
  QR.qring_eq([c, s], E.QSub{E.QMul{E.QVar{0n}, E.QVar{0n}}, E.QMul{E.QNeg{E.QVar{1n}}, E.QVar{1n}}}, E.QAdd{E.QMul{E.QVar{0n}, E.QVar{0n}}, E.QMul{E.QVar{1n}, E.QVar{1n}}}, {==})

def cw.s(+c: S.Q, +s: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(c, s), S.Q.mul(S.Q.neg(s), c)), DR.qz()):
  QR.qring_eq([c, s], E.QAdd{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QMul{E.QNeg{E.QVar{1n}}, E.QVar{0n}}}, E.QCst{DR.qz()}, {==})

def wc.c(+c: S.Q, +s: S.Q) -> S.Q.eq(S.Q.sub(S.Q.mul(c, c), S.Q.mul(s, S.Q.neg(s))), S.Q.add(S.Q.mul(c, c), S.Q.mul(s, s))):
  QR.qring_eq([c, s], E.QSub{E.QMul{E.QVar{0n}, E.QVar{0n}}, E.QMul{E.QVar{1n}, E.QNeg{E.QVar{1n}}}}, E.QAdd{E.QMul{E.QVar{0n}, E.QVar{0n}}, E.QMul{E.QVar{1n}, E.QVar{1n}}}, {==})

def wc.s(+c: S.Q, +s: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(c, S.Q.neg(s)), S.Q.mul(s, c)), DR.qz()):
  QR.qring_eq([c, s], E.QAdd{E.QMul{E.QVar{0n}, E.QNeg{E.QVar{1n}}}, E.QMul{E.QVar{1n}, E.QVar{0n}}}, E.QCst{DR.qz()}, {==})

# conj(w) (w y) = |w|^2 y
def conj_w(w: DR.Lab, +y: SK.VE) -> VD.SameVD(DR.gmul(DR.Lab.conj(w), DR.gmul(w, y)), DR.vlin(DC.lnorm(w), y, DR.qz(), y)):
  match w:
    case DR.Lab{+c, +s}:
      GN.samevd_tr(DR.gmul(DR.Lab.conj(DR.Lab{c, s}), DR.gmul(DR.Lab{c, s}, y)), DR.gmul(DR.Lab{DC.lnorm(DR.Lab{c, s}), DR.qz()}, y), DR.vlin(DC.lnorm(DR.Lab{c, s}), y, DR.qz(), y),
        GN.samevd_tr(DR.gmul(DR.Lab.conj(DR.Lab{c, s}), DR.gmul(DR.Lab{c, s}, y)), DR.gmul(LB.lmul(DR.Lab.conj(DR.Lab{c, s}), DR.Lab{c, s}), y), DR.gmul(DR.Lab{DC.lnorm(DR.Lab{c, s}), DR.qz()}, y),
          MG.compd(DR.Lab.conj(DR.Lab{c, s}), DR.Lab{c, s}, y),
          gle(LB.lmul(DR.Lab.conj(DR.Lab{c, s}), DR.Lab{c, s}), DR.Lab{DC.lnorm(DR.Lab{c, s}), DR.qz()}, y, le_of(S.Q.sub(S.Q.mul(c, c), S.Q.mul(S.Q.neg(s), s)), S.Q.add(S.Q.mul(c, s), S.Q.mul(S.Q.neg(s), c)), DC.lnorm(DR.Lab{c, s}), DR.qz(), cw.c(c, s), cw.s(c, s)))),
        gmul_real(DC.lnorm(DR.Lab{c, s}), y))

# w (conj(w) y) = |w|^2 y
def w_conj(w: DR.Lab, +y: SK.VE) -> VD.SameVD(DR.gmul(w, DR.gmul(DR.Lab.conj(w), y)), DR.vlin(DC.lnorm(w), y, DR.qz(), y)):
  match w:
    case DR.Lab{+c, +s}:
      GN.samevd_tr(DR.gmul(DR.Lab{c, s}, DR.gmul(DR.Lab.conj(DR.Lab{c, s}), y)), DR.gmul(DR.Lab{DC.lnorm(DR.Lab{c, s}), DR.qz()}, y), DR.vlin(DC.lnorm(DR.Lab{c, s}), y, DR.qz(), y),
        GN.samevd_tr(DR.gmul(DR.Lab{c, s}, DR.gmul(DR.Lab.conj(DR.Lab{c, s}), y)), DR.gmul(LB.lmul(DR.Lab{c, s}, DR.Lab.conj(DR.Lab{c, s})), y), DR.gmul(DR.Lab{DC.lnorm(DR.Lab{c, s}), DR.qz()}, y),
          MG.compd(DR.Lab{c, s}, DR.Lab.conj(DR.Lab{c, s}), y),
          gle(LB.lmul(DR.Lab{c, s}, DR.Lab.conj(DR.Lab{c, s})), DR.Lab{DC.lnorm(DR.Lab{c, s}), DR.qz()}, y, le_of(S.Q.sub(S.Q.mul(c, c), S.Q.mul(s, S.Q.neg(s))), S.Q.add(S.Q.mul(c, S.Q.neg(s)), S.Q.mul(s, c)), DC.lnorm(DR.Lab{c, s}), DR.qz(), wc.c(c, s), wc.s(c, s)))),
        gmul_real(DC.lnorm(DR.Lab{c, s}), y))


# Products of labels
# ------------------

def sw.s(+c1: S.Q, +s1: S.Q, +c2: S.Q, +s2: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), S.Q.add(S.Q.mul(c2, s1), S.Q.mul(s2, c1))):
  LQ.q_trans(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), S.Q.add(S.Q.mul(s1, c2), S.Q.mul(c1, s2)), S.Q.add(S.Q.mul(c2, s1), S.Q.mul(s2, c1)),
    LQ.q_add_comm(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), QA.add_cong(S.Q.mul(s1, c2), S.Q.mul(c2, s1), S.Q.mul(c1, s2), S.Q.mul(s2, c1), LQ.q_mul_comm(s1, c2), LQ.q_mul_comm(c1, s2)))

# g h = h g
def lswap(+c1: S.Q, +s1: S.Q, +c2: S.Q, +s2: S.Q) -> LE(LB.lmul(DR.Lab{c1, s1}, DR.Lab{c2, s2}), LB.lmul(DR.Lab{c2, s2}, DR.Lab{c1, s1})):
  le_of(S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), S.Q.sub(S.Q.mul(c2, c1), S.Q.mul(s2, s1)), S.Q.add(S.Q.mul(c2, s1), S.Q.mul(s2, c1)),
    QA.sub_cong(S.Q.mul(c1, c2), S.Q.mul(c2, c1), S.Q.mul(s1, s2), S.Q.mul(s2, s1), LQ.q_mul_comm(c1, c2), LQ.q_mul_comm(s1, s2)), sw.s(c1, s1, c2, s2))

# g (h x) = h (g x)
def gswap(g: DR.Lab, h: DR.Lab, +x: SK.VE) -> VD.SameVD(DR.gmul(g, DR.gmul(h, x)), DR.gmul(h, DR.gmul(g, x))):
  match g h:
    case DR.Lab{+c1, +s1} DR.Lab{+c2, +s2}:
      GN.samevd_tr(DR.gmul(DR.Lab{c1, s1}, DR.gmul(DR.Lab{c2, s2}, x)), DR.gmul(LB.lmul(DR.Lab{c1, s1}, DR.Lab{c2, s2}), x), DR.gmul(DR.Lab{c2, s2}, DR.gmul(DR.Lab{c1, s1}, x)),
        MG.compd(DR.Lab{c1, s1}, DR.Lab{c2, s2}, x),
        GN.samevd_tr(DR.gmul(LB.lmul(DR.Lab{c1, s1}, DR.Lab{c2, s2}), x), DR.gmul(LB.lmul(DR.Lab{c2, s2}, DR.Lab{c1, s1}), x), DR.gmul(DR.Lab{c2, s2}, DR.gmul(DR.Lab{c1, s1}, x)),
          gle(LB.lmul(DR.Lab{c1, s1}, DR.Lab{c2, s2}), LB.lmul(DR.Lab{c2, s2}, DR.Lab{c1, s1}), x, lswap(c1, s1, c2, s2)),
          MG.samevd_sym(DR.gmul(DR.Lab{c2, s2}, DR.gmul(DR.Lab{c1, s1}, x)), DR.gmul(LB.lmul(DR.Lab{c2, s2}, DR.Lab{c1, s1}), x), MG.compd(DR.Lab{c2, s2}, DR.Lab{c1, s1}, x))))

def nn(+x: S.Q, +y: S.Q) -> S.Q.eq(S.Q.mul(x, y), S.Q.mul(S.Q.neg(x), S.Q.neg(y))):
  QR.qring_eq([x, y], E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QMul{E.QNeg{E.QVar{0n}}, E.QNeg{E.QVar{1n}}}, {==})

def nm(+x: S.Q, +y: S.Q) -> S.Q.eq(S.Q.neg(S.Q.mul(x, y)), S.Q.mul(S.Q.neg(x), y)):
  QR.qring_eq([x, y], E.QNeg{E.QMul{E.QVar{0n}, E.QVar{1n}}}, E.QMul{E.QNeg{E.QVar{0n}}, E.QVar{1n}}, {==})

def cm.s(+c1: S.Q, +s1: S.Q, +c2: S.Q, +s2: S.Q) -> S.Q.eq(S.Q.neg(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2))), S.Q.add(S.Q.mul(c1, S.Q.neg(s2)), S.Q.mul(S.Q.neg(s1), c2))):
  LQ.q_trans(S.Q.neg(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2))), S.Q.add(S.Q.neg(S.Q.mul(c1, s2)), S.Q.neg(S.Q.mul(s1, c2))), S.Q.add(S.Q.mul(c1, S.Q.neg(s2)), S.Q.mul(S.Q.neg(s1), c2)),
    QA.negadd(S.Q.mul(c1, s2), S.Q.mul(s1, c2)),
    QA.add_cong(S.Q.neg(S.Q.mul(c1, s2)), S.Q.mul(c1, S.Q.neg(s2)), S.Q.neg(S.Q.mul(s1, c2)), S.Q.mul(S.Q.neg(s1), c2), LQ.q_sym(S.Q.mul(c1, S.Q.neg(s2)), S.Q.neg(S.Q.mul(c1, s2)), QA.mneg(c1, s2)), nm(s1, c2)))

# conj(g h) = conj(g) conj(h)
def lconj_mul(+c1: S.Q, +s1: S.Q, +c2: S.Q, +s2: S.Q) -> LE(DR.Lab.conj(LB.lmul(DR.Lab{c1, s1}, DR.Lab{c2, s2})), LB.lmul(DR.Lab.conj(DR.Lab{c1, s1}), DR.Lab.conj(DR.Lab{c2, s2}))):
  le_of(S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), S.Q.neg(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2))), S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(S.Q.neg(s1), S.Q.neg(s2))), S.Q.add(S.Q.mul(c1, S.Q.neg(s2)), S.Q.mul(S.Q.neg(s1), c2)),
    QA.sub_cong(S.Q.mul(c1, c2), S.Q.mul(c1, c2), S.Q.mul(s1, s2), S.Q.mul(S.Q.neg(s1), S.Q.neg(s2)), LQ.q_refl(S.Q.mul(c1, c2)), nn(s1, s2)), cm.s(c1, s1, c2, s2))

# conj(g h) x = conj(g) (conj(h) x)
def gconj_mul(g: DR.Lab, h: DR.Lab, +x: SK.VE) -> VD.SameVD(DR.gmul(DR.Lab.conj(LB.lmul(g, h)), x), DR.gmul(DR.Lab.conj(g), DR.gmul(DR.Lab.conj(h), x))):
  match g h:
    case DR.Lab{+c1, +s1} DR.Lab{+c2, +s2}:
      GN.samevd_tr(DR.gmul(DR.Lab.conj(LB.lmul(DR.Lab{c1, s1}, DR.Lab{c2, s2})), x), DR.gmul(LB.lmul(DR.Lab.conj(DR.Lab{c1, s1}), DR.Lab.conj(DR.Lab{c2, s2})), x), DR.gmul(DR.Lab.conj(DR.Lab{c1, s1}), DR.gmul(DR.Lab.conj(DR.Lab{c2, s2}), x)),
        gle(DR.Lab.conj(LB.lmul(DR.Lab{c1, s1}, DR.Lab{c2, s2})), LB.lmul(DR.Lab.conj(DR.Lab{c1, s1}), DR.Lab.conj(DR.Lab{c2, s2})), x, lconj_mul(c1, s1, c2, s2)),
        MG.samevd_sym(DR.gmul(DR.Lab.conj(DR.Lab{c1, s1}), DR.gmul(DR.Lab.conj(DR.Lab{c2, s2}), x)), DR.gmul(LB.lmul(DR.Lab.conj(DR.Lab{c1, s1}), DR.Lab.conj(DR.Lab{c2, s2})), x), MG.compd(DR.Lab.conj(DR.Lab{c1, s1}), DR.Lab.conj(DR.Lab{c2, s2}), x)))


# Real, zero and non-real labels
# ------------------------------

# a label whose imaginary part is 0 acts as its real part
def gmul_realq(+c: S.Q, +s: S.Q, +y: SK.VE, h: {DR.qnz(s) == False{} : Bool}) -> VD.SameVD(DR.gmul(DR.Lab{c, s}, y), DR.vlin(c, y, DR.qz(), y)):
  GN.samevd_tr(DR.gmul(DR.Lab{c, s}, y), DR.gmul(DR.Lab{c, DR.qz()}, y), DR.vlin(c, y, DR.qz(), y),
    gle(DR.Lab{c, s}, DR.Lab{c, DR.qz()}, y, le_of(c, s, c, DR.qz(), LQ.q_refl(c), LP.qnz_f(s, h))), gmul_real(c, y))

def gz.ax(+p: List<&2, S.Q>, +x: SK.VE) -> S.Q.eq(E.qeval(p, SK.VE.x(DR.gmul(DR.Lab{DR.qz(), DR.qz()}, x))), DR.qz()):
  QR.qring_eq([E.qeval(p, SK.VE.x(x)), E.qeval(p, SK.VE.y(x))], E.QSub{E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}}, E.QCst{DR.qz()}, {==})

def gz.ay(+p: List<&2, S.Q>, +x: SK.VE) -> S.Q.eq(E.qeval(p, SK.VE.y(DR.gmul(DR.Lab{DR.qz(), DR.qz()}, x))), DR.qz()):
  QR.qring_eq([E.qeval(p, SK.VE.x(x)), E.qeval(p, SK.VE.y(x))], E.QAdd{E.QMul{E.QCst{DR.qz()}, E.QVar{0n}}, E.QMul{E.QCst{DR.qz()}, E.QVar{1n}}}, E.QCst{DR.qz()}, {==})

# a label 0 in both parts sends every form to 0
def gmul_zero(+c: S.Q, +s: S.Q, +y: SK.VE, hc: {DR.qnz(c) == False{} : Bool}, hs: {DR.qnz(s) == False{} : Bool}) -> VD.SameVD(DR.gmul(DR.Lab{c, s}, y), DR.zerov()):
  GN.samevd_tr(DR.gmul(DR.Lab{c, s}, y), DR.gmul(DR.Lab{DR.qz(), DR.qz()}, y), DR.zerov(),
    gle(DR.Lab{c, s}, DR.Lab{DR.qz(), DR.qz()}, y, le_of(c, s, DR.qz(), DR.qz(), LP.qnz_f(c, hc), LP.qnz_f(s, hs))),
    (ID.qzero_ident(SK.VE.x(DR.gmul(DR.Lab{DR.qz(), DR.qz()}, y)), DR.zeroe(), p => gz.ax(p, y)), ID.qzero_ident(SK.VE.y(DR.gmul(DR.Lab{DR.qz(), DR.qz()}, y)), DR.zeroe(), p => gz.ay(p, y))))

def gi.rx(+c: S.Q, +s: S.Q, +X: S.Q, +Y: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(S.Q.inv(s), S.Q.sub(S.Q.mul(c, X), S.Q.mul(s, Y))), S.Q.mul(S.Q.neg(S.Q.mul(c, S.Q.inv(s))), X)), S.Q.neg(S.Q.mul(S.Q.mul(s, S.Q.inv(s)), Y))):
  QR.qring_eq([c, s, S.Q.inv(s), X, Y], E.QAdd{E.QMul{E.QVar{2n}, E.QSub{E.QMul{E.QVar{0n}, E.QVar{3n}}, E.QMul{E.QVar{1n}, E.QVar{4n}}}}, E.QMul{E.QNeg{E.QMul{E.QVar{0n}, E.QVar{2n}}}, E.QVar{3n}}}, E.QNeg{E.QMul{E.QMul{E.QVar{1n}, E.QVar{2n}}, E.QVar{4n}}}, {==})

def gi.ry(+c: S.Q, +s: S.Q, +X: S.Q, +Y: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(S.Q.inv(s), S.Q.add(S.Q.mul(s, X), S.Q.mul(c, Y))), S.Q.mul(S.Q.neg(S.Q.mul(c, S.Q.inv(s))), Y)), S.Q.mul(S.Q.mul(s, S.Q.inv(s)), X)):
  QR.qring_eq([c, s, S.Q.inv(s), X, Y], E.QAdd{E.QMul{E.QVar{2n}, E.QAdd{E.QMul{E.QVar{1n}, E.QVar{3n}}, E.QMul{E.QVar{0n}, E.QVar{4n}}}}, E.QMul{E.QNeg{E.QMul{E.QVar{0n}, E.QVar{2n}}}, E.QVar{4n}}}, E.QMul{E.QMul{E.QVar{1n}, E.QVar{2n}}, E.QVar{3n}}, {==})

def gi.nz(+s: S.Q, +h: {DR.qnz(s) == True{} : Bool}) -> S.Q.eq(S.Q.mul(s, S.Q.inv(s)), DR.qo()):
  LQ.q_mul_inv(s, e => LP.qnz_t(s, h, e))

def gi.ax(+p: List<&2, S.Q>, +c: S.Q, +s: S.Q, +y: SK.VE, +h: {DR.qnz(s) == True{} : Bool})
  -> S.Q.eq(E.qeval(p, SK.VE.x(DR.imul(y))), E.qeval(p, SK.VE.x(DR.vlin(S.Q.inv(s), DR.gmul(DR.Lab{c, s}, y), S.Q.neg(S.Q.mul(c, S.Q.inv(s))), y)))):
  QA.ch3(S.Q.neg(E.qeval(p, SK.VE.y(y))), S.Q.neg(S.Q.mul(DR.qo(), E.qeval(p, SK.VE.y(y)))), S.Q.neg(S.Q.mul(S.Q.mul(s, S.Q.inv(s)), E.qeval(p, SK.VE.y(y)))), S.Q.add(S.Q.mul(S.Q.inv(s), S.Q.sub(S.Q.mul(c, E.qeval(p, SK.VE.x(y))), S.Q.mul(s, E.qeval(p, SK.VE.y(y))))), S.Q.mul(S.Q.neg(S.Q.mul(c, S.Q.inv(s))), E.qeval(p, SK.VE.x(y)))),
    LQ.q_neg_cong(E.qeval(p, SK.VE.y(y)), S.Q.mul(DR.qo(), E.qeval(p, SK.VE.y(y))), LQ.q_sym(S.Q.mul(DR.qo(), E.qeval(p, SK.VE.y(y))), E.qeval(p, SK.VE.y(y)), QA.one_mul(E.qeval(p, SK.VE.y(y))))),
    LQ.q_neg_cong(S.Q.mul(DR.qo(), E.qeval(p, SK.VE.y(y))), S.Q.mul(S.Q.mul(s, S.Q.inv(s)), E.qeval(p, SK.VE.y(y))), LQ.q_mul_cong_l(DR.qo(), S.Q.mul(s, S.Q.inv(s)), E.qeval(p, SK.VE.y(y)), LQ.q_sym(S.Q.mul(s, S.Q.inv(s)), DR.qo(), gi.nz(s, h)))),
    LQ.q_sym(S.Q.add(S.Q.mul(S.Q.inv(s), S.Q.sub(S.Q.mul(c, E.qeval(p, SK.VE.x(y))), S.Q.mul(s, E.qeval(p, SK.VE.y(y))))), S.Q.mul(S.Q.neg(S.Q.mul(c, S.Q.inv(s))), E.qeval(p, SK.VE.x(y)))), S.Q.neg(S.Q.mul(S.Q.mul(s, S.Q.inv(s)), E.qeval(p, SK.VE.y(y)))), gi.rx(c, s, E.qeval(p, SK.VE.x(y)), E.qeval(p, SK.VE.y(y)))))

def gi.ay(+p: List<&2, S.Q>, +c: S.Q, +s: S.Q, +y: SK.VE, +h: {DR.qnz(s) == True{} : Bool})
  -> S.Q.eq(E.qeval(p, SK.VE.y(DR.imul(y))), E.qeval(p, SK.VE.y(DR.vlin(S.Q.inv(s), DR.gmul(DR.Lab{c, s}, y), S.Q.neg(S.Q.mul(c, S.Q.inv(s))), y)))):
  QA.ch3(E.qeval(p, SK.VE.x(y)), S.Q.mul(DR.qo(), E.qeval(p, SK.VE.x(y))), S.Q.mul(S.Q.mul(s, S.Q.inv(s)), E.qeval(p, SK.VE.x(y))), S.Q.add(S.Q.mul(S.Q.inv(s), S.Q.add(S.Q.mul(s, E.qeval(p, SK.VE.x(y))), S.Q.mul(c, E.qeval(p, SK.VE.y(y))))), S.Q.mul(S.Q.neg(S.Q.mul(c, S.Q.inv(s))), E.qeval(p, SK.VE.y(y)))),
    LQ.q_sym(S.Q.mul(DR.qo(), E.qeval(p, SK.VE.x(y))), E.qeval(p, SK.VE.x(y)), QA.one_mul(E.qeval(p, SK.VE.x(y)))),
    LQ.q_mul_cong_l(DR.qo(), S.Q.mul(s, S.Q.inv(s)), E.qeval(p, SK.VE.x(y)), LQ.q_sym(S.Q.mul(s, S.Q.inv(s)), DR.qo(), gi.nz(s, h))),
    LQ.q_sym(S.Q.add(S.Q.mul(S.Q.inv(s), S.Q.add(S.Q.mul(s, E.qeval(p, SK.VE.x(y))), S.Q.mul(c, E.qeval(p, SK.VE.y(y))))), S.Q.mul(S.Q.neg(S.Q.mul(c, S.Q.inv(s))), E.qeval(p, SK.VE.y(y)))), S.Q.mul(S.Q.mul(s, S.Q.inv(s)), E.qeval(p, SK.VE.x(y))), gi.ry(c, s, E.qeval(p, SK.VE.x(y)), E.qeval(p, SK.VE.y(y)))))

# a label c + i s with s not 0: i y = (1/s)(u y) - (c/s) y
def gmul_i(+c: S.Q, +s: S.Q, +y: SK.VE, +h: {DR.qnz(s) == True{} : Bool}) -> VD.SameVD(DR.imul(y), DR.vlin(S.Q.inv(s), DR.gmul(DR.Lab{c, s}, y), S.Q.neg(S.Q.mul(c, S.Q.inv(s))), y)):
  (ID.qzero_ident(SK.VE.x(DR.imul(y)), SK.VE.x(DR.vlin(S.Q.inv(s), DR.gmul(DR.Lab{c, s}, y), S.Q.neg(S.Q.mul(c, S.Q.inv(s))), y)), p => gi.ax(p, c, s, y, h)),
   ID.qzero_ident(SK.VE.y(DR.imul(y)), SK.VE.y(DR.vlin(S.Q.inv(s), DR.gmul(DR.Lab{c, s}, y), S.Q.neg(S.Q.mul(c, S.Q.inv(s))), y)), p => gi.ay(p, c, s, y, h)))

def g2.ax(+p: List<&2, S.Q>, +c: S.Q, +s: S.Q, +y: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.x(DR.gmul(DR.Lab{c, s}, y))), E.qeval(p, SK.VE.x(DR.vlin(S.Q.add(c, c), y, S.Q.neg(DR.qo()), DR.gmul(DR.Lab.conj(DR.Lab{c, s}), y))))):
  QR.qring_eq([c, s, E.qeval(p, SK.VE.x(y)), E.qeval(p, SK.VE.y(y))], E.QSub{E.QMul{E.QVar{0n}, E.QVar{2n}}, E.QMul{E.QVar{1n}, E.QVar{3n}}}, E.QAdd{E.QMul{E.QAdd{E.QVar{0n}, E.QVar{0n}}, E.QVar{2n}}, E.QMul{E.QNeg{E.QCst{DR.qo()}}, E.QSub{E.QMul{E.QVar{0n}, E.QVar{2n}}, E.QMul{E.QNeg{E.QVar{1n}}, E.QVar{3n}}}}}, {==})

def g2.ay(+p: List<&2, S.Q>, +c: S.Q, +s: S.Q, +y: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.y(DR.gmul(DR.Lab{c, s}, y))), E.qeval(p, SK.VE.y(DR.vlin(S.Q.add(c, c), y, S.Q.neg(DR.qo()), DR.gmul(DR.Lab.conj(DR.Lab{c, s}), y))))):
  QR.qring_eq([c, s, E.qeval(p, SK.VE.x(y)), E.qeval(p, SK.VE.y(y))], E.QAdd{E.QMul{E.QVar{1n}, E.QVar{2n}}, E.QMul{E.QVar{0n}, E.QVar{3n}}}, E.QAdd{E.QMul{E.QAdd{E.QVar{0n}, E.QVar{0n}}, E.QVar{3n}}, E.QMul{E.QNeg{E.QCst{DR.qo()}}, E.QAdd{E.QMul{E.QNeg{E.QVar{1n}}, E.QVar{2n}}, E.QMul{E.QVar{0n}, E.QVar{3n}}}}}, {==})

# g y = 2 Re(g) y - conj(g) y
def g2re(g: DR.Lab, +y: SK.VE) -> VD.SameVD(DR.gmul(g, y), DR.vlin(S.Q.add(lab.c(g), lab.c(g)), y, S.Q.neg(DR.qo()), DR.gmul(DR.Lab.conj(g), y))):
  match g:
    case DR.Lab{+c, +s}:
      (ID.qzero_ident(SK.VE.x(DR.gmul(DR.Lab{c, s}, y)), SK.VE.x(DR.vlin(S.Q.add(c, c), y, S.Q.neg(DR.qo()), DR.gmul(DR.Lab.conj(DR.Lab{c, s}), y))), p => g2.ax(p, c, s, y)),
       ID.qzero_ident(SK.VE.y(DR.gmul(DR.Lab{c, s}, y)), SK.VE.y(DR.vlin(S.Q.add(c, c), y, S.Q.neg(DR.qo()), DR.gmul(DR.Lab.conj(DR.Lab{c, s}), y))), p => g2.ay(p, c, s, y)))

def qnz_neg.n(n: S.Z, +d: S.Pos) -> {DR.qnz(S.Q.neg(S.Q{n, d})) == DR.qnz(S.Q{n, d}) : Bool}:
  match n:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      {==}
    case S.Zneg{p}:
      {==}

# -q is 0 exactly when q is
def qnz_neg(q: S.Q) -> {DR.qnz(S.Q.neg(q)) == DR.qnz(q) : Bool}:
  match q:
    case S.Q{n, d}:
      qnz_neg.n(n, d)

def gv.x(+c: S.Q, +s: S.Q, +m1: S.Q, +m2: S.Q, +X1: S.Q, +Y1: S.Q, +X2: S.Q, +Y2: S.Q)
  -> S.Q.eq(S.Q.sub(S.Q.mul(c, S.Q.add(S.Q.mul(m1, X1), S.Q.mul(m2, X2))), S.Q.mul(s, S.Q.add(S.Q.mul(m1, Y1), S.Q.mul(m2, Y2)))), S.Q.add(S.Q.mul(m1, S.Q.sub(S.Q.mul(c, X1), S.Q.mul(s, Y1))), S.Q.mul(m2, S.Q.sub(S.Q.mul(c, X2), S.Q.mul(s, Y2))))):
  QA.ch4(S.Q.sub(S.Q.mul(c, S.Q.add(S.Q.mul(m1, X1), S.Q.mul(m2, X2))), S.Q.mul(s, S.Q.add(S.Q.mul(m1, Y1), S.Q.mul(m2, Y2)))),
    S.Q.sub(S.Q.add(S.Q.mul(c, S.Q.mul(m1, X1)), S.Q.mul(c, S.Q.mul(m2, X2))), S.Q.add(S.Q.mul(s, S.Q.mul(m1, Y1)), S.Q.mul(s, S.Q.mul(m2, Y2)))),
    S.Q.add(S.Q.sub(S.Q.mul(c, S.Q.mul(m1, X1)), S.Q.mul(s, S.Q.mul(m1, Y1))), S.Q.sub(S.Q.mul(c, S.Q.mul(m2, X2)), S.Q.mul(s, S.Q.mul(m2, Y2)))),
    S.Q.add(S.Q.sub(S.Q.mul(m1, S.Q.mul(c, X1)), S.Q.mul(m1, S.Q.mul(s, Y1))), S.Q.sub(S.Q.mul(m2, S.Q.mul(c, X2)), S.Q.mul(m2, S.Q.mul(s, Y2)))),
    S.Q.add(S.Q.mul(m1, S.Q.sub(S.Q.mul(c, X1), S.Q.mul(s, Y1))), S.Q.mul(m2, S.Q.sub(S.Q.mul(c, X2), S.Q.mul(s, Y2)))),
    QA.sub_cong(S.Q.mul(c, S.Q.add(S.Q.mul(m1, X1), S.Q.mul(m2, X2))), S.Q.add(S.Q.mul(c, S.Q.mul(m1, X1)), S.Q.mul(c, S.Q.mul(m2, X2))), S.Q.mul(s, S.Q.add(S.Q.mul(m1, Y1), S.Q.mul(m2, Y2))), S.Q.add(S.Q.mul(s, S.Q.mul(m1, Y1)), S.Q.mul(s, S.Q.mul(m2, Y2))),
      QA.ldist(c, S.Q.mul(m1, X1), S.Q.mul(m2, X2)), QA.ldist(s, S.Q.mul(m1, Y1), S.Q.mul(m2, Y2))),
    QA.r4c(S.Q.mul(c, S.Q.mul(m1, X1)), S.Q.mul(c, S.Q.mul(m2, X2)), S.Q.mul(s, S.Q.mul(m1, Y1)), S.Q.mul(s, S.Q.mul(m2, Y2))),
    QA.add_cong(S.Q.sub(S.Q.mul(c, S.Q.mul(m1, X1)), S.Q.mul(s, S.Q.mul(m1, Y1))), S.Q.sub(S.Q.mul(m1, S.Q.mul(c, X1)), S.Q.mul(m1, S.Q.mul(s, Y1))), S.Q.sub(S.Q.mul(c, S.Q.mul(m2, X2)), S.Q.mul(s, S.Q.mul(m2, Y2))), S.Q.sub(S.Q.mul(m2, S.Q.mul(c, X2)), S.Q.mul(m2, S.Q.mul(s, Y2))),
      QA.sub_cong(S.Q.mul(c, S.Q.mul(m1, X1)), S.Q.mul(m1, S.Q.mul(c, X1)), S.Q.mul(s, S.Q.mul(m1, Y1)), S.Q.mul(m1, S.Q.mul(s, Y1)), QA.mswap(c, m1, X1), QA.mswap(s, m1, Y1)),
      QA.sub_cong(S.Q.mul(c, S.Q.mul(m2, X2)), S.Q.mul(m2, S.Q.mul(c, X2)), S.Q.mul(s, S.Q.mul(m2, Y2)), S.Q.mul(m2, S.Q.mul(s, Y2)), QA.mswap(c, m2, X2), QA.mswap(s, m2, Y2))),
    QA.add_cong(S.Q.sub(S.Q.mul(m1, S.Q.mul(c, X1)), S.Q.mul(m1, S.Q.mul(s, Y1))), S.Q.mul(m1, S.Q.sub(S.Q.mul(c, X1), S.Q.mul(s, Y1))), S.Q.sub(S.Q.mul(m2, S.Q.mul(c, X2)), S.Q.mul(m2, S.Q.mul(s, Y2))), S.Q.mul(m2, S.Q.sub(S.Q.mul(c, X2), S.Q.mul(s, Y2))),
      LQ.q_sym(S.Q.mul(m1, S.Q.sub(S.Q.mul(c, X1), S.Q.mul(s, Y1))), S.Q.sub(S.Q.mul(m1, S.Q.mul(c, X1)), S.Q.mul(m1, S.Q.mul(s, Y1))), QA.ldsub(m1, S.Q.mul(c, X1), S.Q.mul(s, Y1))),
      LQ.q_sym(S.Q.mul(m2, S.Q.sub(S.Q.mul(c, X2), S.Q.mul(s, Y2))), S.Q.sub(S.Q.mul(m2, S.Q.mul(c, X2)), S.Q.mul(m2, S.Q.mul(s, Y2))), QA.ldsub(m2, S.Q.mul(c, X2), S.Q.mul(s, Y2)))))

def gv.y(+c: S.Q, +s: S.Q, +m1: S.Q, +m2: S.Q, +X1: S.Q, +Y1: S.Q, +X2: S.Q, +Y2: S.Q)
  -> S.Q.eq(S.Q.add(S.Q.mul(s, S.Q.add(S.Q.mul(m1, X1), S.Q.mul(m2, X2))), S.Q.mul(c, S.Q.add(S.Q.mul(m1, Y1), S.Q.mul(m2, Y2)))), S.Q.add(S.Q.mul(m1, S.Q.add(S.Q.mul(s, X1), S.Q.mul(c, Y1))), S.Q.mul(m2, S.Q.add(S.Q.mul(s, X2), S.Q.mul(c, Y2))))):
  QA.ch4(S.Q.add(S.Q.mul(s, S.Q.add(S.Q.mul(m1, X1), S.Q.mul(m2, X2))), S.Q.mul(c, S.Q.add(S.Q.mul(m1, Y1), S.Q.mul(m2, Y2)))),
    S.Q.add(S.Q.add(S.Q.mul(s, S.Q.mul(m1, X1)), S.Q.mul(s, S.Q.mul(m2, X2))), S.Q.add(S.Q.mul(c, S.Q.mul(m1, Y1)), S.Q.mul(c, S.Q.mul(m2, Y2)))),
    S.Q.add(S.Q.add(S.Q.mul(s, S.Q.mul(m1, X1)), S.Q.mul(c, S.Q.mul(m1, Y1))), S.Q.add(S.Q.mul(s, S.Q.mul(m2, X2)), S.Q.mul(c, S.Q.mul(m2, Y2)))),
    S.Q.add(S.Q.add(S.Q.mul(m1, S.Q.mul(s, X1)), S.Q.mul(m1, S.Q.mul(c, Y1))), S.Q.add(S.Q.mul(m2, S.Q.mul(s, X2)), S.Q.mul(m2, S.Q.mul(c, Y2)))),
    S.Q.add(S.Q.mul(m1, S.Q.add(S.Q.mul(s, X1), S.Q.mul(c, Y1))), S.Q.mul(m2, S.Q.add(S.Q.mul(s, X2), S.Q.mul(c, Y2)))),
    QA.add_cong(S.Q.mul(s, S.Q.add(S.Q.mul(m1, X1), S.Q.mul(m2, X2))), S.Q.add(S.Q.mul(s, S.Q.mul(m1, X1)), S.Q.mul(s, S.Q.mul(m2, X2))), S.Q.mul(c, S.Q.add(S.Q.mul(m1, Y1), S.Q.mul(m2, Y2))), S.Q.add(S.Q.mul(c, S.Q.mul(m1, Y1)), S.Q.mul(c, S.Q.mul(m2, Y2))),
      QA.ldist(s, S.Q.mul(m1, X1), S.Q.mul(m2, X2)), QA.ldist(c, S.Q.mul(m1, Y1), S.Q.mul(m2, Y2))),
    QA.m4(S.Q.mul(s, S.Q.mul(m1, X1)), S.Q.mul(s, S.Q.mul(m2, X2)), S.Q.mul(c, S.Q.mul(m1, Y1)), S.Q.mul(c, S.Q.mul(m2, Y2))),
    QA.add_cong(S.Q.add(S.Q.mul(s, S.Q.mul(m1, X1)), S.Q.mul(c, S.Q.mul(m1, Y1))), S.Q.add(S.Q.mul(m1, S.Q.mul(s, X1)), S.Q.mul(m1, S.Q.mul(c, Y1))), S.Q.add(S.Q.mul(s, S.Q.mul(m2, X2)), S.Q.mul(c, S.Q.mul(m2, Y2))), S.Q.add(S.Q.mul(m2, S.Q.mul(s, X2)), S.Q.mul(m2, S.Q.mul(c, Y2))),
      QA.add_cong(S.Q.mul(s, S.Q.mul(m1, X1)), S.Q.mul(m1, S.Q.mul(s, X1)), S.Q.mul(c, S.Q.mul(m1, Y1)), S.Q.mul(m1, S.Q.mul(c, Y1)), QA.mswap(s, m1, X1), QA.mswap(c, m1, Y1)),
      QA.add_cong(S.Q.mul(s, S.Q.mul(m2, X2)), S.Q.mul(m2, S.Q.mul(s, X2)), S.Q.mul(c, S.Q.mul(m2, Y2)), S.Q.mul(m2, S.Q.mul(c, Y2)), QA.mswap(s, m2, X2), QA.mswap(c, m2, Y2))),
    QA.add_cong(S.Q.add(S.Q.mul(m1, S.Q.mul(s, X1)), S.Q.mul(m1, S.Q.mul(c, Y1))), S.Q.mul(m1, S.Q.add(S.Q.mul(s, X1), S.Q.mul(c, Y1))), S.Q.add(S.Q.mul(m2, S.Q.mul(s, X2)), S.Q.mul(m2, S.Q.mul(c, Y2))), S.Q.mul(m2, S.Q.add(S.Q.mul(s, X2), S.Q.mul(c, Y2))),
      LQ.q_sym(S.Q.mul(m1, S.Q.add(S.Q.mul(s, X1), S.Q.mul(c, Y1))), S.Q.add(S.Q.mul(m1, S.Q.mul(s, X1)), S.Q.mul(m1, S.Q.mul(c, Y1))), QA.ldist(m1, S.Q.mul(s, X1), S.Q.mul(c, Y1))),
      LQ.q_sym(S.Q.mul(m2, S.Q.add(S.Q.mul(s, X2), S.Q.mul(c, Y2))), S.Q.add(S.Q.mul(m2, S.Q.mul(s, X2)), S.Q.mul(m2, S.Q.mul(c, Y2))), QA.ldist(m2, S.Q.mul(s, X2), S.Q.mul(c, Y2)))))

def gv.ax(+p: List<&2, S.Q>, +c: S.Q, +s: S.Q, +m1: S.Q, +x1: SK.VE, +m2: S.Q, +x2: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.x(DR.gmul(DR.Lab{c, s}, DR.vlin(m1, x1, m2, x2)))), E.qeval(p, SK.VE.x(DR.vlin(m1, DR.gmul(DR.Lab{c, s}, x1), m2, DR.gmul(DR.Lab{c, s}, x2))))):
  gv.x(c, s, m1, m2, E.qeval(p, SK.VE.x(x1)), E.qeval(p, SK.VE.y(x1)), E.qeval(p, SK.VE.x(x2)), E.qeval(p, SK.VE.y(x2)))

def gv.ay(+p: List<&2, S.Q>, +c: S.Q, +s: S.Q, +m1: S.Q, +x1: SK.VE, +m2: S.Q, +x2: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.y(DR.gmul(DR.Lab{c, s}, DR.vlin(m1, x1, m2, x2)))), E.qeval(p, SK.VE.y(DR.vlin(m1, DR.gmul(DR.Lab{c, s}, x1), m2, DR.gmul(DR.Lab{c, s}, x2))))):
  gv.y(c, s, m1, m2, E.qeval(p, SK.VE.x(x1)), E.qeval(p, SK.VE.y(x1)), E.qeval(p, SK.VE.x(x2)), E.qeval(p, SK.VE.y(x2)))

# g (m1 x1 + m2 x2) = m1 (g x1) + m2 (g x2)
def gmul_vlin(g: DR.Lab, +m1: S.Q, +x1: SK.VE, +m2: S.Q, +x2: SK.VE) -> VD.SameVD(DR.gmul(g, DR.vlin(m1, x1, m2, x2)), DR.vlin(m1, DR.gmul(g, x1), m2, DR.gmul(g, x2))):
  match g:
    case DR.Lab{+c, +s}:
      (ID.qzero_ident(SK.VE.x(DR.gmul(DR.Lab{c, s}, DR.vlin(m1, x1, m2, x2))), SK.VE.x(DR.vlin(m1, DR.gmul(DR.Lab{c, s}, x1), m2, DR.gmul(DR.Lab{c, s}, x2))), p => gv.ax(p, c, s, m1, x1, m2, x2)),
       ID.qzero_ident(SK.VE.y(DR.gmul(DR.Lab{c, s}, DR.vlin(m1, x1, m2, x2))), SK.VE.y(DR.vlin(m1, DR.gmul(DR.Lab{c, s}, x1), m2, DR.gmul(DR.Lab{c, s}, x2))), p => gv.ay(p, c, s, m1, x1, m2, x2)))
