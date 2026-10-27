# bend-cad: the closure's labels are nonzero (PLAN-sk13b B3). Nz(g) says
# |g|^2 = c^2 + s^2 is nonzero. It holds for 1 and i, is kept by products
# (|g h|^2 = |g|^2 |h|^2, a product of nonzero rationals being nonzero) and
# by conjugates, and holds for every label the pair test finds: (1, 0), or
# (-c, 1) with c^2 + 1 > 0 (ptest_nz, hs_lab_nz, ks_lab_nz). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./qring.bend as QR
import ./qalg.bend as QA
import ./q.bend as LQ
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./drvpf.bend as DV
import ./kspace.bend as KS
import ./hspace.bend as HS
import ./pair.bend as PT
import ./pairpf.bend as PP
import ./lab.bend as LB
import ./labpf.bend as LP
import ./dclose.bend as DC

def absurd(-A: Type, x: Empty) -> A:
  match x:

def Nz(+g: DR.Lab) -> Data:
  {DR.qnz(DC.lnorm(g)) == True{} : Bool}

def nz_one() -> Nz(DC.lone()):
  {==}

def nz_i() -> Nz(DC.li()):
  {==}

# Nonzero rationals
# -----------------

def qnz_mul.n(na: S.Z, nb: S.Z, +da: S.Pos, +db: S.Pos) -> {DR.qnz(S.Q.mul(S.Q{na, da}, S.Q{nb, db})) == SV.band(DR.qnz(S.Q{na, da}), DR.qnz(S.Q{nb, db})) : Bool}:
  match na nb:
    case S.Z0{} nb:
      {==}
    case S.Zpos{p} S.Z0{}:
      {==}
    case S.Zpos{p} S.Zpos{q}:
      {==}
    case S.Zpos{p} S.Zneg{q}:
      {==}
    case S.Zneg{p} S.Z0{}:
      {==}
    case S.Zneg{p} S.Zpos{q}:
      {==}
    case S.Zneg{p} S.Zneg{q}:
      {==}

# a product is nonzero iff both are
def qnz_mul(a: S.Q, b: S.Q) -> {DR.qnz(S.Q.mul(a, b)) == SV.band(DR.qnz(a), DR.qnz(b)) : Bool}:
  match a b:
    case S.Q{na, da} S.Q{nb, db}:
      qnz_mul.n(na, nb, da, db)

def qnz_eq.n(na: S.Z, nb: S.Z, +da: S.Pos, +db: S.Pos, h: S.Q.eq(S.Q{na, da}, S.Q{nb, db})) -> {DR.qnz(S.Q{na, da}) == DR.qnz(S.Q{nb, db}) : Bool}:
  match na nb:
    case S.Z0{} S.Z0{}:
      {==}
    case S.Z0{} S.Zpos{q}:
      absurd({False{} == True{} : Bool}, LP.zpos_z0(S.Pos.mul(q, da), Equal.sym(S.Z, S.Z0{}, S.Zpos{S.Pos.mul(q, da)}, h)))
    case S.Z0{} S.Zneg{q}:
      absurd({False{} == True{} : Bool}, LP.zneg_z0(S.Pos.mul(q, da), Equal.sym(S.Z, S.Z0{}, S.Zneg{S.Pos.mul(q, da)}, h)))
    case S.Zpos{p} S.Z0{}:
      absurd({True{} == False{} : Bool}, LP.zpos_z0(S.Pos.mul(p, db), h))
    case S.Zpos{p} S.Zpos{q}:
      {==}
    case S.Zpos{p} S.Zneg{q}:
      {==}
    case S.Zneg{p} S.Z0{}:
      absurd({True{} == False{} : Bool}, LP.zneg_z0(S.Pos.mul(p, db), h))
    case S.Zneg{p} S.Zpos{q}:
      {==}
    case S.Zneg{p} S.Zneg{q}:
      {==}

# equal rationals are both zero or both not
def qnz_eq(a: S.Q, b: S.Q, h: S.Q.eq(a, b)) -> {DR.qnz(a) == DR.qnz(b) : Bool}:
  match a b:
    case S.Q{na, da} S.Q{nb, db}:
      qnz_eq.n(na, nb, da, db, h)

# Norms
# -----

def nrm.sa(+a: S.Q, +b: S.Q) -> S.Q.eq(S.Q.mul(S.Q.sub(a, b), S.Q.sub(a, b)), S.Q.add(S.Q.add(S.Q.mul(a, a), S.Q.mul(b, b)), S.Q.mul(S.Q{S.Zneg{S.XO{S.XH{}}}, S.XH{}}, S.Q.mul(a, b)))):
  QR.qring_eq([a, b], E.QMul{E.QSub{E.QVar{0n}, E.QVar{1n}}, E.QSub{E.QVar{0n}, E.QVar{1n}}}, E.QAdd{E.QAdd{E.QMul{E.QVar{0n}, E.QVar{0n}}, E.QMul{E.QVar{1n}, E.QVar{1n}}}, E.QMul{E.QCst{S.Q{S.Zneg{S.XO{S.XH{}}}, S.XH{}}}, E.QMul{E.QVar{0n}, E.QVar{1n}}}}, {==})

def nrm.sb(+c: S.Q, +d: S.Q) -> S.Q.eq(S.Q.mul(S.Q.add(c, d), S.Q.add(c, d)), S.Q.add(S.Q.add(S.Q.mul(c, c), S.Q.mul(d, d)), S.Q.mul(S.Q{S.Zpos{S.XO{S.XH{}}}, S.XH{}}, S.Q.mul(c, d)))):
  QR.qring_eq([c, d], E.QMul{E.QAdd{E.QVar{0n}, E.QVar{1n}}, E.QAdd{E.QVar{0n}, E.QVar{1n}}}, E.QAdd{E.QAdd{E.QMul{E.QVar{0n}, E.QVar{0n}}, E.QMul{E.QVar{1n}, E.QVar{1n}}}, E.QMul{E.QCst{S.Q{S.Zpos{S.XO{S.XH{}}}, S.XH{}}}, E.QMul{E.QVar{0n}, E.QVar{1n}}}}, {==})

def nrm.r4(+x1: S.Q, +y1: S.Q, +x2: S.Q, +y2: S.Q) -> S.Q.eq(S.Q.add(S.Q.add(x1, y1), S.Q.add(x2, y2)), S.Q.add(S.Q.add(x1, x2), S.Q.add(y2, y1))):
  QR.qring_eq([x1, y1, x2, y2], E.QAdd{E.QAdd{E.QVar{0n}, E.QVar{1n}}, E.QAdd{E.QVar{2n}, E.QVar{3n}}}, E.QAdd{E.QAdd{E.QVar{0n}, E.QVar{2n}}, E.QAdd{E.QVar{3n}, E.QVar{1n}}}, {==})

def nrm.sqm(+x: S.Q, +y: S.Q) -> S.Q.eq(S.Q.mul(S.Q.mul(x, y), S.Q.mul(x, y)), S.Q.mul(S.Q.mul(x, x), S.Q.mul(y, y))):
  QR.qring_eq([x, y], E.QMul{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QMul{E.QVar{0n}, E.QVar{1n}}}, E.QMul{E.QMul{E.QVar{0n}, E.QVar{0n}}, E.QMul{E.QVar{1n}, E.QVar{1n}}}, {==})

def nrm.cd(+c1: S.Q, +s1: S.Q, +c2: S.Q, +s2: S.Q) -> S.Q.eq(S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(s1, s2))):
  QR.qring_eq([c1, s1, c2, s2], E.QMul{E.QMul{E.QVar{0n}, E.QVar{3n}}, E.QMul{E.QVar{1n}, E.QVar{2n}}}, E.QMul{E.QMul{E.QVar{0n}, E.QVar{2n}}, E.QMul{E.QVar{1n}, E.QVar{3n}}}, {==})

def nrm.ex(+p: S.Q, +q: S.Q, +r: S.Q, +t: S.Q) -> S.Q.eq(S.Q.mul(S.Q.add(p, q), S.Q.add(r, t)), S.Q.add(S.Q.add(S.Q.mul(p, r), S.Q.mul(p, t)), S.Q.add(S.Q.mul(q, r), S.Q.mul(q, t)))):
  QR.qring_eq([p, q, r, t], E.QMul{E.QAdd{E.QVar{0n}, E.QVar{1n}}, E.QAdd{E.QVar{2n}, E.QVar{3n}}}, E.QAdd{E.QAdd{E.QMul{E.QVar{0n}, E.QVar{2n}}, E.QMul{E.QVar{0n}, E.QVar{3n}}}, E.QAdd{E.QMul{E.QVar{1n}, E.QVar{2n}}, E.QMul{E.QVar{1n}, E.QVar{3n}}}}, {==})

def nrm.z2(+x: S.Q, +y: S.Q, h: S.Q.eq(x, y)) -> S.Q.eq(S.Q.add(S.Q.mul(S.Q{S.Zpos{S.XO{S.XH{}}}, S.XH{}}, x), S.Q.mul(S.Q{S.Zneg{S.XO{S.XH{}}}, S.XH{}}, y)), DR.qz()):
  LQ.q_trans(S.Q.add(S.Q.mul(S.Q{S.Zpos{S.XO{S.XH{}}}, S.XH{}}, x), S.Q.mul(S.Q{S.Zneg{S.XO{S.XH{}}}, S.XH{}}, y)), S.Q.add(S.Q.mul(S.Q{S.Zpos{S.XO{S.XH{}}}, S.XH{}}, y), S.Q.mul(S.Q{S.Zneg{S.XO{S.XH{}}}, S.XH{}}, y)), DR.qz(),
    LQ.q_add_cong_l(S.Q.mul(S.Q{S.Zpos{S.XO{S.XH{}}}, S.XH{}}, x), S.Q.mul(S.Q{S.Zpos{S.XO{S.XH{}}}, S.XH{}}, y), S.Q.mul(S.Q{S.Zneg{S.XO{S.XH{}}}, S.XH{}}, y), LQ.q_mul_cong_r(S.Q{S.Zpos{S.XO{S.XH{}}}, S.XH{}}, x, y, h)),
    QR.qring_eq([y], E.QAdd{E.QMul{E.QCst{S.Q{S.Zpos{S.XO{S.XH{}}}, S.XH{}}}, E.QVar{0n}}, E.QMul{E.QCst{S.Q{S.Zneg{S.XO{S.XH{}}}, S.XH{}}}, E.QVar{0n}}}, E.QCst{DR.qz()}, {==}))

def nrm.az(+x: S.Q) -> S.Q.eq(S.Q.add(x, DR.qz()), x):
  QR.qring_eq([x], E.QAdd{E.QVar{0n}, E.QCst{DR.qz()}}, E.QVar{0n}, {==})

def lnorm_mul.q(+c1: S.Q, +s1: S.Q, +c2: S.Q, +s2: S.Q) -> S.Q.eq(DC.lnorm(LB.lmul(DR.Lab{c1, s1}, DR.Lab{c2, s2})), S.Q.mul(DC.lnorm(DR.Lab{c1, s1}), DC.lnorm(DR.Lab{c2, s2}))):
  LQ.q_trans(S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2))), S.Q.mul(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)))), S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(c2, c2)), S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(s2, s2))), S.Q.add(S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(c2, c2)), S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(s2, s2)))), S.Q.mul(S.Q.add(S.Q.mul(c1, c1), S.Q.mul(s1, s1)), S.Q.add(S.Q.mul(c2, c2), S.Q.mul(s2, s2))), LQ.q_trans(S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2))), S.Q.mul(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)))), S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(c2, c2)), S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(s2, s2))), S.Q.add(S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(s2, s2)), S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(c2, c2)))), S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(c2, c2)), S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(s2, s2))), S.Q.add(S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(c2, c2)), S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(s2, s2)))), LQ.q_trans(S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2))), S.Q.mul(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)))), S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(c2, c2)), S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(s2, s2))), S.Q.add(S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(s2, s2)), S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(c2, c2)))), S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(c2, c2)), S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(s2, s2))), S.Q.add(S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(s2, s2)), S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(c2, c2)))), LQ.q_trans(S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2))), S.Q.mul(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)))), S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(c1, c2)), S.Q.mul(S.Q.mul(s1, s2), S.Q.mul(s1, s2))), S.Q.add(S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(c1, s2)), S.Q.mul(S.Q.mul(s1, c2), S.Q.mul(s1, c2)))), S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(c2, c2)), S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(s2, s2))), S.Q.add(S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(s2, s2)), S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(c2, c2)))), LQ.q_trans(S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2))), S.Q.mul(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)))), S.Q.add(S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(c1, c2)), S.Q.mul(S.Q.mul(s1, s2), S.Q.mul(s1, s2))), S.Q.add(S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(c1, s2)), S.Q.mul(S.Q.mul(s1, c2), S.Q.mul(s1, c2)))), DR.qz()), S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(c1, c2)), S.Q.mul(S.Q.mul(s1, s2), S.Q.mul(s1, s2))), S.Q.add(S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(c1, s2)), S.Q.mul(S.Q.mul(s1, c2), S.Q.mul(s1, c2)))), LQ.q_trans(S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2))), S.Q.mul(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)))), S.Q.add(S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(c1, c2)), S.Q.mul(S.Q.mul(s1, s2), S.Q.mul(s1, s2))), S.Q.add(S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(c1, s2)), S.Q.mul(S.Q.mul(s1, c2), S.Q.mul(s1, c2)))), S.Q.add(S.Q.mul(S.Q{S.Zpos{S.XO{S.XH{}}}, S.XH{}}, S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(s1, c2))), S.Q.mul(S.Q{S.Zneg{S.XO{S.XH{}}}, S.XH{}}, S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(s1, s2))))), S.Q.add(S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(c1, c2)), S.Q.mul(S.Q.mul(s1, s2), S.Q.mul(s1, s2))), S.Q.add(S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(c1, s2)), S.Q.mul(S.Q.mul(s1, c2), S.Q.mul(s1, c2)))), DR.qz()), LQ.q_trans(S.Q.add(S.Q.mul(S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2))), S.Q.mul(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)))), S.Q.add(S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(c1, c2)), S.Q.mul(S.Q.mul(s1, s2), S.Q.mul(s1, s2))), S.Q.mul(S.Q{S.Zneg{S.XO{S.XH{}}}, S.XH{}}, S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(s1, s2)))), S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(c1, s2)), S.Q.mul(S.Q.mul(s1, c2), S.Q.mul(s1, c2))), S.Q.mul(S.Q{S.Zpos{S.XO{S.XH{}}}, S.XH{}}, S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(s1, c2))))), S.Q.add(S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(c1, c2)), S.Q.mul(S.Q.mul(s1, s2), S.Q.mul(s1, s2))), S.Q.add(S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(c1, s2)), S.Q.mul(S.Q.mul(s1, c2), S.Q.mul(s1, c2)))), S.Q.add(S.Q.mul(S.Q{S.Zpos{S.XO{S.XH{}}}, S.XH{}}, S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(s1, c2))), S.Q.mul(S.Q{S.Zneg{S.XO{S.XH{}}}, S.XH{}}, S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(s1, s2))))), QA.add_cong(S.Q.mul(S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2))), S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(c1, c2)), S.Q.mul(S.Q.mul(s1, s2), S.Q.mul(s1, s2))), S.Q.mul(S.Q{S.Zneg{S.XO{S.XH{}}}, S.XH{}}, S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(s1, s2)))), S.Q.mul(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2))), S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(c1, s2)), S.Q.mul(S.Q.mul(s1, c2), S.Q.mul(s1, c2))), S.Q.mul(S.Q{S.Zpos{S.XO{S.XH{}}}, S.XH{}}, S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(s1, c2)))), nrm.sa(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), nrm.sb(S.Q.mul(c1, s2), S.Q.mul(s1, c2))), nrm.r4(S.Q.add(S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(c1, c2)), S.Q.mul(S.Q.mul(s1, s2), S.Q.mul(s1, s2))), S.Q.mul(S.Q{S.Zneg{S.XO{S.XH{}}}, S.XH{}}, S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(s1, s2))), S.Q.add(S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(c1, s2)), S.Q.mul(S.Q.mul(s1, c2), S.Q.mul(s1, c2))), S.Q.mul(S.Q{S.Zpos{S.XO{S.XH{}}}, S.XH{}}, S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(s1, c2))))), QA.add_cong(S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(c1, c2)), S.Q.mul(S.Q.mul(s1, s2), S.Q.mul(s1, s2))), S.Q.add(S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(c1, s2)), S.Q.mul(S.Q.mul(s1, c2), S.Q.mul(s1, c2)))), S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(c1, c2)), S.Q.mul(S.Q.mul(s1, s2), S.Q.mul(s1, s2))), S.Q.add(S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(c1, s2)), S.Q.mul(S.Q.mul(s1, c2), S.Q.mul(s1, c2)))), S.Q.add(S.Q.mul(S.Q{S.Zpos{S.XO{S.XH{}}}, S.XH{}}, S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(s1, c2))), S.Q.mul(S.Q{S.Zneg{S.XO{S.XH{}}}, S.XH{}}, S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(s1, s2)))), DR.qz(), LQ.q_refl(S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(c1, c2)), S.Q.mul(S.Q.mul(s1, s2), S.Q.mul(s1, s2))), S.Q.add(S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(c1, s2)), S.Q.mul(S.Q.mul(s1, c2), S.Q.mul(s1, c2))))), nrm.z2(S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), nrm.cd(c1, s1, c2, s2)))), nrm.az(S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(c1, c2)), S.Q.mul(S.Q.mul(s1, s2), S.Q.mul(s1, s2))), S.Q.add(S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(c1, s2)), S.Q.mul(S.Q.mul(s1, c2), S.Q.mul(s1, c2)))))), QA.add_cong(S.Q.add(S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(c1, c2)), S.Q.mul(S.Q.mul(s1, s2), S.Q.mul(s1, s2))), S.Q.add(S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(c2, c2)), S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(s2, s2))), S.Q.add(S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(c1, s2)), S.Q.mul(S.Q.mul(s1, c2), S.Q.mul(s1, c2))), S.Q.add(S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(s2, s2)), S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(c2, c2))), QA.add_cong(S.Q.mul(S.Q.mul(c1, c2), S.Q.mul(c1, c2)), S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(c2, c2)), S.Q.mul(S.Q.mul(s1, s2), S.Q.mul(s1, s2)), S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(s2, s2)), nrm.sqm(c1, c2), nrm.sqm(s1, s2)), QA.add_cong(S.Q.mul(S.Q.mul(c1, s2), S.Q.mul(c1, s2)), S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(s2, s2)), S.Q.mul(S.Q.mul(s1, c2), S.Q.mul(s1, c2)), S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(c2, c2)), nrm.sqm(c1, s2), nrm.sqm(s1, c2)))), QA.m4(S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(c2, c2)), S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(s2, s2)), S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(s2, s2)), S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(c2, c2)))), LQ.q_add_cong_r(S.Q.add(S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(c2, c2)), S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(s2, s2))), S.Q.add(S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(s2, s2)), S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(c2, c2))), S.Q.add(S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(c2, c2)), S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(s2, s2))), LQ.q_add_comm(S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(s2, s2)), S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(c2, c2))))), LQ.q_sym(S.Q.mul(S.Q.add(S.Q.mul(c1, c1), S.Q.mul(s1, s1)), S.Q.add(S.Q.mul(c2, c2), S.Q.mul(s2, s2))), S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(c2, c2)), S.Q.mul(S.Q.mul(c1, c1), S.Q.mul(s2, s2))), S.Q.add(S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(c2, c2)), S.Q.mul(S.Q.mul(s1, s1), S.Q.mul(s2, s2)))), nrm.ex(S.Q.mul(c1, c1), S.Q.mul(s1, s1), S.Q.mul(c2, c2), S.Q.mul(s2, s2))))

# |g h|^2 = |g|^2 |h|^2
def lnorm_mul(g: DR.Lab, h: DR.Lab) -> S.Q.eq(DC.lnorm(LB.lmul(g, h)), S.Q.mul(DC.lnorm(g), DC.lnorm(h))):
  match g h:
    case DR.Lab{+c1, +s1} DR.Lab{+c2, +s2}:
      lnorm_mul.q(c1, s1, c2, s2)

# a product of nonzero labels is nonzero
def nz_mul(+g: DR.Lab, +h: DR.Lab, hg: Nz(g), hh: Nz(h)) -> Nz(LB.lmul(g, h)):
  %Equal.sym(Bool, DR.qnz(DC.lnorm(LB.lmul(g, h))), DR.qnz(S.Q.mul(DC.lnorm(g), DC.lnorm(h))), qnz_eq(DC.lnorm(LB.lmul(g, h)), S.Q.mul(DC.lnorm(g), DC.lnorm(h)), lnorm_mul(g, h))) : {_ == True{} : Bool}
  %Equal.sym(Bool, DR.qnz(S.Q.mul(DC.lnorm(g), DC.lnorm(h))), SV.band(DR.qnz(DC.lnorm(g)), DR.qnz(DC.lnorm(h))), qnz_mul(DC.lnorm(g), DC.lnorm(h))) : {_ == True{} : Bool}
  %Equal.sym(Bool, DR.qnz(DC.lnorm(g)), True{}, hg) : {SV.band(_, DR.qnz(DC.lnorm(h))) == True{} : Bool}
  hh

def negsq.n(n: S.Z, +d: S.Pos) -> {S.Q.mul(S.Q.neg(S.Q{n, d}), S.Q.neg(S.Q{n, d})) == S.Q.mul(S.Q{n, d}, S.Q{n, d}) : S.Q}:
  match n:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      {==}
    case S.Zneg{p}:
      {==}

def negsq(s: S.Q) -> {S.Q.mul(S.Q.neg(s), S.Q.neg(s)) == S.Q.mul(s, s) : S.Q}:
  match s:
    case S.Q{n, d}:
      negsq.n(n, d)

# so is a conjugate
def nz_conj(g: DR.Lab, h: Nz(g)) -> Nz(DR.Lab.conj(g)):
  match g:
    case DR.Lab{+c, +s}:
      %Equal.sym(S.Q, S.Q.mul(S.Q.neg(s), S.Q.neg(s)), S.Q.mul(s, s), negsq(s)) : {DR.qnz(S.Q.add(S.Q.mul(c, c), _)) == True{} : Bool}
      h

# The pair test's labels
# ----------------------

def nz_c1.n(n: S.Z, +d: S.Pos) -> Nz(DR.Lab{S.Q.neg(S.Q{n, d}), DR.qo()}):
  match n:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      {==}
    case S.Zneg{p}:
      {==}

# (-c, 1) is nonzero
def nz_c1(c: S.Q) -> Nz(DR.Lab{S.Q.neg(c), DR.qo()}):
  match c:
    case S.Q{n, d}:
      nz_c1.n(n, d)

def nz_at(+p: PT.Pr, +q: PT.Pr, e: {p == q : PT.Pr}, h: Nz(LB.lab_of(p))) -> Nz(LB.lab_of(q)):
  %e : Nz(LB.lab_of(_))
  h

def ptnz.second(b: Bool, +rows2: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr, +p: PT.Pr, hm: {PT.pt.second(b, rows2, B, u, v) == Some{p} : Maybe<&2, PT.Pr>}) -> Nz(LB.lab_of(p)):
  match b:
    case True{}:
      nz_at(PT.Pr{S.Q.neg(PT.lastc(DV.dropls(DV.rescb(EL.resid(rows2, v)), DV.resbt(EL.resid(rows2, v)), v, EP.qsnoc(B, u)), B)), DR.qo()}, p, PP.some_inj(PT.Pr{S.Q.neg(PT.lastc(DV.dropls(DV.rescb(EL.resid(rows2, v)), DV.resbt(EL.resid(rows2, v)), v, EP.qsnoc(B, u)), B)), DR.qo()}, p, hm),
        nz_c1(PT.lastc(DV.dropls(DV.rescb(EL.resid(rows2, v)), DV.resbt(EL.resid(rows2, v)), v, EP.qsnoc(B, u)), B)))
    case False{}:
      absurd(Nz(LB.lab_of(p)), PP.none_some(p, hm))

def ptnz.first(b: Bool, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr, +p: PT.Pr, hm: {PT.pt.first(b, rows, B, u, v) == Some{p} : Maybe<&2, PT.Pr>}) -> Nz(LB.lab_of(p)):
  match b:
    case True{}:
      nz_at(PT.Pr{DR.qo(), DR.qz()}, p, PP.some_inj(PT.Pr{DR.qo(), DR.qz()}, p, hm), {==})
    case False{}:
      ptnz.second(EP.isnil(EP.resp(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v))), EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), B, u, v, p, hm)

# a label the pair test finds is nonzero
def ptest_nz(+rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr, +p: PT.Pr, hm: {PT.ptest(rows, B, u, v) == Some{p} : Maybe<&2, PT.Pr>}) -> Nz(LB.lab_of(p)):
  ptnz.first(EP.isnil(EP.resp(EL.resid(rows, u))), rows, B, u, v, p, hm)

def wnz_at(+x: DR.Lab, +w: DR.Lab, e: {x == w : DR.Lab}, h: Nz(x)) -> Nz(w):
  %e : Nz(_)
  h

def lab_nz(m: Maybe<&2, PT.Pr>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr, +w: DR.Lab,
  hm: {PT.ptest(rows, B, u, v) == m : Maybe<&2, PT.Pr>}, hw: {LB.lab_map(m) == Some{w} : Maybe<&2, DR.Lab>}) -> Nz(w):
  match m:
    case Some{+p}:
      wnz_at(LB.lab_of(p), w, LP.lsome_inj(LB.lab_of(p), w, hw), ptest_nz(rows, B, u, v, p, hm))
    case None{}:
      absurd(Nz(w), LP.lnone_some(w, hw))

# the hull label test's labels are nonzero
def hs_lab_nz(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +t: Nat, +h: HS.HS, +z: SK.VE, +w: DR.Lab, hw: {LB.hs.lab(es, fs, t, h, z) == Some{w} : Maybe<&2, DR.Lab>}) -> Nz(w):
  lab_nz(LB.hs.ptest(es, fs, t, h, z), HS.hs.rows(h), HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t), HS.enc(z, t), HS.enc(DR.imul(z), t), w, {==}, hw)

# and so are the frame test's
def ks_lab_nz(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +k: KS.KS, +z: SK.VE, +w: DR.Lab, hw: {LB.ks.lab(es, fs, k, z) == Some{w} : Maybe<&2, DR.Lab>}) -> Nz(w):
  lab_nz(LB.ks.ptest(es, fs, k, z), KS.ks.rows(k), KS.kexprs(es, fs, KS.ks.ds(k)), SK.VE.y(z), SK.VE.x(z), w, {==}, hw)
