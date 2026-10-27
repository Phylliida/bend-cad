# bend-cad: label algebra for the closure theorem (PLAN-sk13b B3), as
# identities of forms in reusable Data form (lib/dcvd.bend's SameVD):
# - a real label acts as a scalar (gmul_real);
# - gmul is linear in the label (gmul_lin);
# - w conj(w) = |w|^2, real (lmul_conj);
# - for a label u not real, i y = (1/s)(u y) - (c/s) y (gmul_i).
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
import ./dclose.bend as DC
import ./dcvd.bend as VD

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
