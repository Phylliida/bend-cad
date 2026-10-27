# bend-cad: proofs about labels (lib/lab.bend). The rotation identities are
# pointwise rational identities, each a chain of lib/qalg.bend's small
# lemmas: a product of rotations is the rotation by the product
# (gmul_comp), and a rotated form's encoding is the pair test's
# combination of the encodings of z and i z (enc_gmul). So the label test
# is sound (hs_lab_ok: a found w has w z in the hull) and complete
# (hs_lab_some: if some nonzero w has w z in the hull, it finds one), and
# so is the frame test against K (ks_lab_ok, ks_lab_some), whose identity
# is Im(w z) = a Im z + b Re z.
# Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/sketch.bend as SK
import ../spec/dir.bend as DR
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./q.bend as LQ
import ./qalg.bend as QA
import ./spanpf.bend as SN
import ./pair.bend as PT
import ./pairpf.bend as PP
import ./kspace.bend as KS
import ./kspacepf.bend as KP
import ./hspace.bend as HS
import ./hspacepf.bend as HP
import ./lab.bend as LB

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Nonzero rationals
# -----------------

def tf(h: {True{} == False{} : Bool}) -> Empty:
  %h : PP.none_some.p(_)
  Unit{}

def zd(z: S.Z) -> Data:
  match z:
    case S.Z0{}:
      Empty
    case S.Zpos{p}:
      Unit
    case S.Zneg{p}:
      Unit

def zpos_z0(+p: S.Pos, h: {S.Zpos{p} == S.Z0{} : S.Z}) -> Empty:
  %h : zd(_)
  Unit{}

def zneg_z0(+p: S.Pos, h: {S.Zneg{p} == S.Z0{} : S.Z}) -> Empty:
  %h : zd(_)
  Unit{}

def qnz_f.n(n: S.Z, +d: S.Pos, h: {DR.znz(n) == False{} : Bool}) -> S.Q.eq(S.Q{n, d}, S.Q{S.Z0{}, S.XH{}}):
  match n:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      absurd(S.Q.eq(S.Q{S.Zpos{p}, d}, S.Q{S.Z0{}, S.XH{}}), tf(h))
    case S.Zneg{p}:
      absurd(S.Q.eq(S.Q{S.Zneg{p}, d}, S.Q{S.Z0{}, S.XH{}}), tf(h))

# q is 0 when the test says so
def qnz_f(q: S.Q, h: {DR.qnz(q) == False{} : Bool}) -> S.Q.eq(q, S.Q{S.Z0{}, S.XH{}}):
  match q:
    case S.Q{n, d}:
      qnz_f.n(n, d, h)

def qnz_t.n(n: S.Z, +d: S.Pos, h: {DR.znz(n) == True{} : Bool}, e: S.Q.eq(S.Q{n, d}, S.Q{S.Z0{}, S.XH{}})) -> Empty:
  match n:
    case S.Z0{}:
      tf(Equal.sym(Bool, False{}, True{}, h))
    case S.Zpos{p}:
      zpos_z0(S.Pos.mul(p, S.XH{}), e)
    case S.Zneg{p}:
      zneg_z0(S.Pos.mul(p, S.XH{}), e)

# q is not 0 when the test says so
def qnz_t(q: S.Q, h: {DR.qnz(q) == True{} : Bool}, e: S.Q.eq(q, S.Q{S.Z0{}, S.XH{}})) -> Empty:
  match q:
    case S.Q{n, d}:
      qnz_t.n(n, d, h, e)

# Rational chains
# ---------------

# the real part of a product of rotations
def comp_x(+c1: S.Q, +s1: S.Q, +c2: S.Q, +s2: S.Q, +x: S.Q, +y: S.Q) -> S.Q.eq(S.Q.sub(S.Q.mul(c1, S.Q.sub(S.Q.mul(c2, x), S.Q.mul(s2, y))), S.Q.mul(s1, S.Q.add(S.Q.mul(s2, x), S.Q.mul(c2, y)))), S.Q.sub(S.Q.mul(S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), x), S.Q.mul(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), y))):
  QA.ch4(S.Q.sub(S.Q.mul(c1, S.Q.sub(S.Q.mul(c2, x), S.Q.mul(s2, y))), S.Q.mul(s1, S.Q.add(S.Q.mul(s2, x), S.Q.mul(c2, y)))), S.Q.sub(S.Q.sub(S.Q.mul(c1, S.Q.mul(c2, x)), S.Q.mul(c1, S.Q.mul(s2, y))), S.Q.add(S.Q.mul(s1, S.Q.mul(s2, x)), S.Q.mul(s1, S.Q.mul(c2, y)))), S.Q.sub(S.Q.sub(S.Q.mul(S.Q.mul(c1, c2), x), S.Q.mul(S.Q.mul(c1, s2), y)), S.Q.add(S.Q.mul(S.Q.mul(s1, s2), x), S.Q.mul(S.Q.mul(s1, c2), y))), S.Q.sub(S.Q.sub(S.Q.mul(S.Q.mul(c1, c2), x), S.Q.mul(S.Q.mul(s1, s2), x)), S.Q.add(S.Q.mul(S.Q.mul(c1, s2), y), S.Q.mul(S.Q.mul(s1, c2), y))), S.Q.sub(S.Q.mul(S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), x), S.Q.mul(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), y)),
    QA.sub_cong(S.Q.mul(c1, S.Q.sub(S.Q.mul(c2, x), S.Q.mul(s2, y))), S.Q.sub(S.Q.mul(c1, S.Q.mul(c2, x)), S.Q.mul(c1, S.Q.mul(s2, y))), S.Q.mul(s1, S.Q.add(S.Q.mul(s2, x), S.Q.mul(c2, y))), S.Q.add(S.Q.mul(s1, S.Q.mul(s2, x)), S.Q.mul(s1, S.Q.mul(c2, y))), QA.ldsub(c1, S.Q.mul(c2, x), S.Q.mul(s2, y)), QA.ldist(s1, S.Q.mul(s2, x), S.Q.mul(c2, y))),
    QA.sub_cong(S.Q.sub(S.Q.mul(c1, S.Q.mul(c2, x)), S.Q.mul(c1, S.Q.mul(s2, y))), S.Q.sub(S.Q.mul(S.Q.mul(c1, c2), x), S.Q.mul(S.Q.mul(c1, s2), y)), S.Q.add(S.Q.mul(s1, S.Q.mul(s2, x)), S.Q.mul(s1, S.Q.mul(c2, y))), S.Q.add(S.Q.mul(S.Q.mul(s1, s2), x), S.Q.mul(S.Q.mul(s1, c2), y)), QA.sub_cong(S.Q.mul(c1, S.Q.mul(c2, x)), S.Q.mul(S.Q.mul(c1, c2), x), S.Q.mul(c1, S.Q.mul(s2, y)), S.Q.mul(S.Q.mul(c1, s2), y), QA.ma(c1, c2, x), QA.ma(c1, s2, y)), QA.add_cong(S.Q.mul(s1, S.Q.mul(s2, x)), S.Q.mul(S.Q.mul(s1, s2), x), S.Q.mul(s1, S.Q.mul(c2, y)), S.Q.mul(S.Q.mul(s1, c2), y), QA.ma(s1, s2, x), QA.ma(s1, c2, y))),
    QA.r4a(S.Q.mul(S.Q.mul(c1, c2), x), S.Q.mul(S.Q.mul(c1, s2), y), S.Q.mul(S.Q.mul(s1, s2), x), S.Q.mul(S.Q.mul(s1, c2), y)),
    QA.sub_cong(S.Q.sub(S.Q.mul(S.Q.mul(c1, c2), x), S.Q.mul(S.Q.mul(s1, s2), x)), S.Q.mul(S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), x), S.Q.add(S.Q.mul(S.Q.mul(c1, s2), y), S.Q.mul(S.Q.mul(s1, c2), y)), S.Q.mul(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), y), LQ.q_sym(S.Q.mul(S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), x), S.Q.sub(S.Q.mul(S.Q.mul(c1, c2), x), S.Q.mul(S.Q.mul(s1, s2), x)), QA.rdsub(S.Q.mul(c1, c2), S.Q.mul(s1, s2), x)), LQ.q_sym(S.Q.mul(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), y), S.Q.add(S.Q.mul(S.Q.mul(c1, s2), y), S.Q.mul(S.Q.mul(s1, c2), y)), QA.rdist(S.Q.mul(c1, s2), S.Q.mul(s1, c2), y))))

# the imaginary part
def comp_y(+c1: S.Q, +s1: S.Q, +c2: S.Q, +s2: S.Q, +x: S.Q, +y: S.Q) -> S.Q.eq(S.Q.add(S.Q.mul(s1, S.Q.sub(S.Q.mul(c2, x), S.Q.mul(s2, y))), S.Q.mul(c1, S.Q.add(S.Q.mul(s2, x), S.Q.mul(c2, y)))), S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), x), S.Q.mul(S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), y))):
  QA.ch4(S.Q.add(S.Q.mul(s1, S.Q.sub(S.Q.mul(c2, x), S.Q.mul(s2, y))), S.Q.mul(c1, S.Q.add(S.Q.mul(s2, x), S.Q.mul(c2, y)))), S.Q.add(S.Q.sub(S.Q.mul(s1, S.Q.mul(c2, x)), S.Q.mul(s1, S.Q.mul(s2, y))), S.Q.add(S.Q.mul(c1, S.Q.mul(s2, x)), S.Q.mul(c1, S.Q.mul(c2, y)))), S.Q.add(S.Q.sub(S.Q.mul(S.Q.mul(s1, c2), x), S.Q.mul(S.Q.mul(s1, s2), y)), S.Q.add(S.Q.mul(S.Q.mul(c1, s2), x), S.Q.mul(S.Q.mul(c1, c2), y))), S.Q.add(S.Q.add(S.Q.mul(S.Q.mul(c1, s2), x), S.Q.mul(S.Q.mul(s1, c2), x)), S.Q.sub(S.Q.mul(S.Q.mul(c1, c2), y), S.Q.mul(S.Q.mul(s1, s2), y))), S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), x), S.Q.mul(S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), y)),
    QA.add_cong(S.Q.mul(s1, S.Q.sub(S.Q.mul(c2, x), S.Q.mul(s2, y))), S.Q.sub(S.Q.mul(s1, S.Q.mul(c2, x)), S.Q.mul(s1, S.Q.mul(s2, y))), S.Q.mul(c1, S.Q.add(S.Q.mul(s2, x), S.Q.mul(c2, y))), S.Q.add(S.Q.mul(c1, S.Q.mul(s2, x)), S.Q.mul(c1, S.Q.mul(c2, y))), QA.ldsub(s1, S.Q.mul(c2, x), S.Q.mul(s2, y)), QA.ldist(c1, S.Q.mul(s2, x), S.Q.mul(c2, y))),
    QA.add_cong(S.Q.sub(S.Q.mul(s1, S.Q.mul(c2, x)), S.Q.mul(s1, S.Q.mul(s2, y))), S.Q.sub(S.Q.mul(S.Q.mul(s1, c2), x), S.Q.mul(S.Q.mul(s1, s2), y)), S.Q.add(S.Q.mul(c1, S.Q.mul(s2, x)), S.Q.mul(c1, S.Q.mul(c2, y))), S.Q.add(S.Q.mul(S.Q.mul(c1, s2), x), S.Q.mul(S.Q.mul(c1, c2), y)), QA.sub_cong(S.Q.mul(s1, S.Q.mul(c2, x)), S.Q.mul(S.Q.mul(s1, c2), x), S.Q.mul(s1, S.Q.mul(s2, y)), S.Q.mul(S.Q.mul(s1, s2), y), QA.ma(s1, c2, x), QA.ma(s1, s2, y)), QA.add_cong(S.Q.mul(c1, S.Q.mul(s2, x)), S.Q.mul(S.Q.mul(c1, s2), x), S.Q.mul(c1, S.Q.mul(c2, y)), S.Q.mul(S.Q.mul(c1, c2), y), QA.ma(c1, s2, x), QA.ma(c1, c2, y))),
    QA.r4b(S.Q.mul(S.Q.mul(s1, c2), x), S.Q.mul(S.Q.mul(s1, s2), y), S.Q.mul(S.Q.mul(c1, s2), x), S.Q.mul(S.Q.mul(c1, c2), y)),
    QA.add_cong(S.Q.add(S.Q.mul(S.Q.mul(c1, s2), x), S.Q.mul(S.Q.mul(s1, c2), x)), S.Q.mul(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), x), S.Q.sub(S.Q.mul(S.Q.mul(c1, c2), y), S.Q.mul(S.Q.mul(s1, s2), y)), S.Q.mul(S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), y), LQ.q_sym(S.Q.mul(S.Q.add(S.Q.mul(c1, s2), S.Q.mul(s1, c2)), x), S.Q.add(S.Q.mul(S.Q.mul(c1, s2), x), S.Q.mul(S.Q.mul(s1, c2), x)), QA.rdist(S.Q.mul(c1, s2), S.Q.mul(s1, c2), x)), LQ.q_sym(S.Q.mul(S.Q.sub(S.Q.mul(c1, c2), S.Q.mul(s1, s2)), y), S.Q.sub(S.Q.mul(S.Q.mul(c1, c2), y), S.Q.mul(S.Q.mul(s1, s2), y)), QA.rdsub(S.Q.mul(c1, c2), S.Q.mul(s1, s2), y))))

# a rotated form's encoding is the pair combination of the encodings
def enc_rot(+a: S.Q, +b: S.Q, +x: S.Q, +y: S.Q, +tt: S.Q) -> S.Q.eq(S.Q.add(S.Q.sub(S.Q.mul(a, x), S.Q.mul(b, y)), S.Q.mul(tt, S.Q.add(S.Q.mul(b, x), S.Q.mul(a, y)))), S.Q.add(S.Q.mul(a, S.Q.add(x, S.Q.mul(tt, y))), S.Q.mul(b, S.Q.add(S.Q.neg(y), S.Q.mul(tt, x))))):
  LQ.q_trans(S.Q.add(S.Q.sub(S.Q.mul(a, x), S.Q.mul(b, y)), S.Q.mul(tt, S.Q.add(S.Q.mul(b, x), S.Q.mul(a, y)))), S.Q.add(S.Q.add(S.Q.mul(a, x), S.Q.mul(tt, S.Q.mul(a, y))), S.Q.add(S.Q.neg(S.Q.mul(b, y)), S.Q.mul(tt, S.Q.mul(b, x)))), S.Q.add(S.Q.mul(a, S.Q.add(x, S.Q.mul(tt, y))), S.Q.mul(b, S.Q.add(S.Q.neg(y), S.Q.mul(tt, x)))),
  QA.ch3(S.Q.add(S.Q.sub(S.Q.mul(a, x), S.Q.mul(b, y)), S.Q.mul(tt, S.Q.add(S.Q.mul(b, x), S.Q.mul(a, y)))), S.Q.add(S.Q.add(S.Q.mul(a, x), S.Q.neg(S.Q.mul(b, y))), S.Q.add(S.Q.mul(tt, S.Q.mul(b, x)), S.Q.mul(tt, S.Q.mul(a, y)))), S.Q.add(S.Q.add(S.Q.mul(a, x), S.Q.neg(S.Q.mul(b, y))), S.Q.add(S.Q.mul(tt, S.Q.mul(a, y)), S.Q.mul(tt, S.Q.mul(b, x)))), S.Q.add(S.Q.add(S.Q.mul(a, x), S.Q.mul(tt, S.Q.mul(a, y))), S.Q.add(S.Q.neg(S.Q.mul(b, y)), S.Q.mul(tt, S.Q.mul(b, x)))),
    LQ.q_add_cong_r(S.Q.sub(S.Q.mul(a, x), S.Q.mul(b, y)), S.Q.mul(tt, S.Q.add(S.Q.mul(b, x), S.Q.mul(a, y))), S.Q.add(S.Q.mul(tt, S.Q.mul(b, x)), S.Q.mul(tt, S.Q.mul(a, y))), QA.ldist(tt, S.Q.mul(b, x), S.Q.mul(a, y))),
    LQ.q_add_cong_r(S.Q.add(S.Q.mul(a, x), S.Q.neg(S.Q.mul(b, y))), S.Q.add(S.Q.mul(tt, S.Q.mul(b, x)), S.Q.mul(tt, S.Q.mul(a, y))), S.Q.add(S.Q.mul(tt, S.Q.mul(a, y)), S.Q.mul(tt, S.Q.mul(b, x))), LQ.q_add_comm(S.Q.mul(tt, S.Q.mul(b, x)), S.Q.mul(tt, S.Q.mul(a, y)))),
    QA.m4(S.Q.mul(a, x), S.Q.neg(S.Q.mul(b, y)), S.Q.mul(tt, S.Q.mul(a, y)), S.Q.mul(tt, S.Q.mul(b, x)))),
  LQ.q_trans(S.Q.add(S.Q.add(S.Q.mul(a, x), S.Q.mul(tt, S.Q.mul(a, y))), S.Q.add(S.Q.neg(S.Q.mul(b, y)), S.Q.mul(tt, S.Q.mul(b, x)))), S.Q.add(S.Q.add(S.Q.mul(a, x), S.Q.mul(a, S.Q.mul(tt, y))), S.Q.add(S.Q.mul(b, S.Q.neg(y)), S.Q.mul(b, S.Q.mul(tt, x)))), S.Q.add(S.Q.mul(a, S.Q.add(x, S.Q.mul(tt, y))), S.Q.mul(b, S.Q.add(S.Q.neg(y), S.Q.mul(tt, x)))), LQ.q_sym(S.Q.add(S.Q.add(S.Q.mul(a, x), S.Q.mul(a, S.Q.mul(tt, y))), S.Q.add(S.Q.mul(b, S.Q.neg(y)), S.Q.mul(b, S.Q.mul(tt, x)))), S.Q.add(S.Q.add(S.Q.mul(a, x), S.Q.mul(tt, S.Q.mul(a, y))), S.Q.add(S.Q.neg(S.Q.mul(b, y)), S.Q.mul(tt, S.Q.mul(b, x)))), QA.add_cong(S.Q.add(S.Q.mul(a, x), S.Q.mul(a, S.Q.mul(tt, y))), S.Q.add(S.Q.mul(a, x), S.Q.mul(tt, S.Q.mul(a, y))), S.Q.add(S.Q.mul(b, S.Q.neg(y)), S.Q.mul(b, S.Q.mul(tt, x))), S.Q.add(S.Q.neg(S.Q.mul(b, y)), S.Q.mul(tt, S.Q.mul(b, x))), LQ.q_add_cong_r(S.Q.mul(a, x), S.Q.mul(a, S.Q.mul(tt, y)), S.Q.mul(tt, S.Q.mul(a, y)), QA.mswap(a, tt, y)), QA.add_cong(S.Q.mul(b, S.Q.neg(y)), S.Q.neg(S.Q.mul(b, y)), S.Q.mul(b, S.Q.mul(tt, x)), S.Q.mul(tt, S.Q.mul(b, x)), QA.mneg(b, y), QA.mswap(b, tt, x)))), LQ.q_sym(S.Q.add(S.Q.mul(a, S.Q.add(x, S.Q.mul(tt, y))), S.Q.mul(b, S.Q.add(S.Q.neg(y), S.Q.mul(tt, x)))), S.Q.add(S.Q.add(S.Q.mul(a, x), S.Q.mul(a, S.Q.mul(tt, y))), S.Q.add(S.Q.mul(b, S.Q.neg(y)), S.Q.mul(b, S.Q.mul(tt, x)))), QA.add_cong(S.Q.mul(a, S.Q.add(x, S.Q.mul(tt, y))), S.Q.add(S.Q.mul(a, x), S.Q.mul(a, S.Q.mul(tt, y))), S.Q.mul(b, S.Q.add(S.Q.neg(y), S.Q.mul(tt, x))), S.Q.add(S.Q.mul(b, S.Q.neg(y)), S.Q.mul(b, S.Q.mul(tt, x))), QA.ldist(a, x, S.Q.mul(tt, y)), QA.ldist(b, S.Q.neg(y), S.Q.mul(tt, x))))))


# Rotations
# ---------

def enc_gmul.at(+p: List<&2, S.Q>, +a: S.Q, +b: S.Q, +z: SK.VE, +t: Nat)
  -> S.Q.eq(E.qeval(p, HS.enc(DR.gmul(DR.Lab{a, b}, z), t)), E.qeval(p, PT.pcomb(PT.Pr{a, b}, HS.enc(z, t), HS.enc(DR.imul(z), t)))):
  enc_rot(a, b, E.qeval(p, SK.VE.x(z)), E.qeval(p, SK.VE.y(z)), E.qlookup(p, t))

# (a + i b) z, encoded, is a enc(z) + b enc(i z)
def enc_gmul(+a: S.Q, +b: S.Q, +z: SK.VE, +t: Nat) -> SV.Ident(HS.enc(DR.gmul(DR.Lab{a, b}, z), t), PT.pcomb(PT.Pr{a, b}, HS.enc(z, t), HS.enc(DR.imul(z), t))):
  p => enc_gmul.at(p, a, b, z, t)

def enc_gmul_r.at(+p: List<&2, S.Q>, +a: S.Q, +b: S.Q, +z: SK.VE, +t: Nat)
  -> S.Q.eq(E.qeval(p, PT.pcomb(PT.Pr{a, b}, HS.enc(z, t), HS.enc(DR.imul(z), t))), E.qeval(p, HS.enc(DR.gmul(DR.Lab{a, b}, z), t))):
  LQ.q_sym(E.qeval(p, HS.enc(DR.gmul(DR.Lab{a, b}, z), t)), E.qeval(p, PT.pcomb(PT.Pr{a, b}, HS.enc(z, t), HS.enc(DR.imul(z), t))), enc_gmul.at(p, a, b, z, t))

def enc_gmul_r(+a: S.Q, +b: S.Q, +z: SK.VE, +t: Nat) -> SV.Ident(PT.pcomb(PT.Pr{a, b}, HS.enc(z, t), HS.enc(DR.imul(z), t)), HS.enc(DR.gmul(DR.Lab{a, b}, z), t)):
  p => enc_gmul_r.at(p, a, b, z, t)

def gmul_comp.ax(+p: List<&2, S.Q>, +c1: S.Q, +s1: S.Q, +c2: S.Q, +s2: S.Q, +x: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.x(DR.gmul(DR.Lab{c1, s1}, DR.gmul(DR.Lab{c2, s2}, x)))), E.qeval(p, SK.VE.x(DR.gmul(LB.lmul(DR.Lab{c1, s1}, DR.Lab{c2, s2}), x)))):
  comp_x(c1, s1, c2, s2, E.qeval(p, SK.VE.x(x)), E.qeval(p, SK.VE.y(x)))

def gmul_comp.ay(+p: List<&2, S.Q>, +c1: S.Q, +s1: S.Q, +c2: S.Q, +s2: S.Q, +x: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.y(DR.gmul(DR.Lab{c1, s1}, DR.gmul(DR.Lab{c2, s2}, x)))), E.qeval(p, SK.VE.y(DR.gmul(LB.lmul(DR.Lab{c1, s1}, DR.Lab{c2, s2}), x)))):
  comp_y(c1, s1, c2, s2, E.qeval(p, SK.VE.x(x)), E.qeval(p, SK.VE.y(x)))

# g (h x) = (g h) x
def gmul_comp(g: DR.Lab, h: DR.Lab, +x: SK.VE) -> DR.SameV(DR.gmul(g, DR.gmul(h, x)), DR.gmul(LB.lmul(g, h), x)):
  match g h:
    case DR.Lab{+c1, +s1} DR.Lab{+c2, +s2}:
      (p => gmul_comp.ax(p, c1, s1, c2, s2, x), p => gmul_comp.ay(p, c1, s1, c2, s2, x))

# The label test
# --------------

def lis_some(m: Maybe<&2, DR.Lab>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

def lsome_or(m: Maybe<&2, DR.Lab>, +d: DR.Lab) -> DR.Lab:
  match m:
    case Some{x}:
      x
    case None{}:
      d

def lsome_inj(+x: DR.Lab, +y: DR.Lab, h: {Some{x} == Some{y} : Maybe<&2, DR.Lab>}) -> {x == y : DR.Lab}:
  Equal.cong(Maybe<&2, DR.Lab>, DR.Lab, m => lsome_or(m, x), Some{x}, Some{y}, h)

def lnone_some(+y: DR.Lab, h: {None{} == Some{y} : Maybe<&2, DR.Lab>}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, Equal.cong(Maybe<&2, DR.Lab>, Bool, m => lis_some(m), None{}, Some{y}, h)) : PP.none_some.p(_)
  Unit{}

def lab_ok.some(p: PT.Pr, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +z: SK.VE, +t: Nat, +w: DR.Lab,
  +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hm: {PT.ptest(rows, B, HS.enc(z, t), HS.enc(DR.imul(z), t)) == Some{p} : Maybe<&2, PT.Pr>}, hw: {Some{LB.lab_of(p)} == Some{w} : Maybe<&2, DR.Lab>})
  -> SN.InSpan(HS.enc(DR.gmul(w, z), t), B):
  match p:
    case PT.Pr{+a, +bb}:
      %lsome_inj(DR.Lab{a, bb}, w, hw) : SN.InSpan(HS.enc(DR.gmul(_, z), t), B)
      PP.in_tr(PT.pcomb(PT.Pr{a, bb}, HS.enc(z, t), HS.enc(DR.imul(z), t)), HS.enc(DR.gmul(DR.Lab{a, bb}, z), t), B,
        PP.ptest_ok(rows, B, HS.enc(z, t), HS.enc(DR.imul(z), t), hr, hl, PT.Pr{a, bb}, hm), enc_gmul(a, bb, z, t))

def lab_ok.go(m: Maybe<&2, PT.Pr>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +z: SK.VE, +t: Nat, +w: DR.Lab,
  +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hm: {PT.ptest(rows, B, HS.enc(z, t), HS.enc(DR.imul(z), t)) == m : Maybe<&2, PT.Pr>}, hw: {LB.lab_map(m) == Some{w} : Maybe<&2, DR.Lab>})
  -> SN.InSpan(HS.enc(DR.gmul(w, z), t), B):
  match m:
    case Some{p}:
      lab_ok.some(p, rows, B, z, t, w, hr, hl, hm, hw)
    case None{}:
      absurd(SN.InSpan(HS.enc(DR.gmul(w, z), t), B), lnone_some(w, hw))

# a found label is right: w z is in the hull
def hs_lab_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, h: HS.HS, +z: SK.VE, +w: DR.Lab,
  hi: HP.HInv(es, fs, ctx, r, t, h), hw: {LB.hs.lab(es, fs, t, h, z) == Some{w} : Maybe<&2, DR.Lab>})
  -> {HS.hs.inb(h, DR.gmul(w, z), t) == True{} : Bool}:
  match h:
    case HS.HS{+rows, +ds}:
      (+hrv, rr) = hi
      (+hl, ha) = rr
      SN.zero_of_in(HS.encs(HS.hxs(es, fs, ds), t), rows, HS.enc(DR.gmul(w, z), t), hrv, hl,
        lab_ok.go(PT.ptest(rows, HS.encs(HS.hxs(es, fs, ds), t), HS.enc(z, t), HS.enc(DR.imul(z), t)), rows, HS.encs(HS.hxs(es, fs, ds), t), z, t, w, hrv, hl, {==}, hw))

def lis_map(m: Maybe<&2, PT.Pr>, h: {PP.is_some(m) == True{} : Bool}) -> {lis_some(LB.lab_map(m)) == True{} : Bool}:
  match m:
    case Some{p}:
      {==}
    case None{}:
      h

def lab_some.pick(b: Bool, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr, +a: S.Q, +bb: S.Q, +eb: {b == DR.qnz(bb) : Bool},
  +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hab: S.Q.eq(a, S.Q{S.Z0{}, S.XH{}}) -> S.Q.eq(bb, S.Q{S.Z0{}, S.XH{}}) -> Empty, +hi: SN.InSpan(PT.pcomb(PT.Pr{a, bb}, u, v), B))
  -> {PP.is_some(PT.ptest(rows, B, u, v)) == True{} : Bool}:
  match b:
    case True{}:
      PP.ptest_some_b(rows, B, u, v, a, bb, hr, hl, e => qnz_t(bb, Equal.sym(Bool, True{}, DR.qnz(bb), eb), e), hi)
    case False{}:
      PP.ptest_some_a(rows, B, u, v, a, bb, hr, hl, ea => hab(ea, qnz_f(bb, Equal.sym(Bool, False{}, DR.qnz(bb), eb))), qnz_f(bb, Equal.sym(Bool, False{}, DR.qnz(bb), eb)), hi)

# if some nonzero a + i b has (a + i b) z in the hull, the test finds a
# label
def hs_lab_some(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, +r: DR.Node, +t: Nat, h: HS.HS, +z: SK.VE, hi: HP.HInv(es, fs, ctx, r, t, h),
  +a: S.Q, +bb: S.Q, hab: S.Q.eq(a, S.Q{S.Z0{}, S.XH{}}) -> S.Q.eq(bb, S.Q{S.Z0{}, S.XH{}}) -> Empty,
  +hin: SN.InSpan(HS.enc(DR.gmul(DR.Lab{a, bb}, z), t), HS.encs(HS.hxs(es, fs, HS.hs.ds(h)), t)))
  -> {lis_some(LB.hs.lab(es, fs, t, h, z)) == True{} : Bool}:
  match h:
    case HS.HS{+rows, +ds}:
      (hrv, rr) = hi
      (hl, ha) = rr
      lis_map(PT.ptest(rows, HS.encs(HS.hxs(es, fs, ds), t), HS.enc(z, t), HS.enc(DR.imul(z), t)),
        lab_some.pick(DR.qnz(bb), rows, HS.encs(HS.hxs(es, fs, ds), t), HS.enc(z, t), HS.enc(DR.imul(z), t), a, bb, {==}, hrv, hl, hab,
          PP.in_tr(HS.enc(DR.gmul(DR.Lab{a, bb}, z), t), PT.pcomb(PT.Pr{a, bb}, HS.enc(z, t), HS.enc(DR.imul(z), t)), HS.encs(HS.hxs(es, fs, ds), t), hin, enc_gmul_r(a, bb, z, t))))

# The frame test
# --------------

def im_gmul.at(+p: List<&2, S.Q>, +a: S.Q, +b: S.Q, +z: SK.VE)
  -> S.Q.eq(E.qeval(p, SK.VE.y(DR.gmul(DR.Lab{a, b}, z))), E.qeval(p, PT.pcomb(PT.Pr{a, b}, SK.VE.y(z), SK.VE.x(z)))):
  LQ.q_add_comm(S.Q.mul(b, E.qeval(p, SK.VE.x(z))), S.Q.mul(a, E.qeval(p, SK.VE.y(z))))

# Im((a + i b) z) = a Im z + b Re z
def im_gmul(+a: S.Q, +b: S.Q, +z: SK.VE) -> SV.Ident(SK.VE.y(DR.gmul(DR.Lab{a, b}, z)), PT.pcomb(PT.Pr{a, b}, SK.VE.y(z), SK.VE.x(z))):
  p => im_gmul.at(p, a, b, z)

def im_gmul_r.at(+p: List<&2, S.Q>, +a: S.Q, +b: S.Q, +z: SK.VE)
  -> S.Q.eq(E.qeval(p, PT.pcomb(PT.Pr{a, b}, SK.VE.y(z), SK.VE.x(z))), E.qeval(p, SK.VE.y(DR.gmul(DR.Lab{a, b}, z)))):
  LQ.q_add_comm(S.Q.mul(a, E.qeval(p, SK.VE.y(z))), S.Q.mul(b, E.qeval(p, SK.VE.x(z))))

def im_gmul_r(+a: S.Q, +b: S.Q, +z: SK.VE) -> SV.Ident(PT.pcomb(PT.Pr{a, b}, SK.VE.y(z), SK.VE.x(z)), SK.VE.y(DR.gmul(DR.Lab{a, b}, z))):
  p => im_gmul_r.at(p, a, b, z)

def klab_ok.some(p: PT.Pr, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +z: SK.VE, +w: DR.Lab,
  +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hm: {PT.ptest(rows, B, SK.VE.y(z), SK.VE.x(z)) == Some{p} : Maybe<&2, PT.Pr>}, hw: {Some{LB.lab_of(p)} == Some{w} : Maybe<&2, DR.Lab>})
  -> SN.InSpan(SK.VE.y(DR.gmul(w, z)), B):
  match p:
    case PT.Pr{+a, +bb}:
      %lsome_inj(DR.Lab{a, bb}, w, hw) : SN.InSpan(SK.VE.y(DR.gmul(_, z)), B)
      PP.in_tr(PT.pcomb(PT.Pr{a, bb}, SK.VE.y(z), SK.VE.x(z)), SK.VE.y(DR.gmul(DR.Lab{a, bb}, z)), B,
        PP.ptest_ok(rows, B, SK.VE.y(z), SK.VE.x(z), hr, hl, PT.Pr{a, bb}, hm), im_gmul(a, bb, z))

def klab_ok.go(m: Maybe<&2, PT.Pr>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +z: SK.VE, +w: DR.Lab,
  +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hm: {PT.ptest(rows, B, SK.VE.y(z), SK.VE.x(z)) == m : Maybe<&2, PT.Pr>}, hw: {LB.lab_map(m) == Some{w} : Maybe<&2, DR.Lab>})
  -> SN.InSpan(SK.VE.y(DR.gmul(w, z)), B):
  match m:
    case Some{p}:
      klab_ok.some(p, rows, B, z, w, hr, hl, hm, hw)
    case None{}:
      absurd(SN.InSpan(SK.VE.y(DR.gmul(w, z)), B), lnone_some(w, hw))

# a label the frame test finds is right: Im(w z) is in K
def ks_lab_ok(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, k: KS.KS, +z: SK.VE, +w: DR.Lab,
  hi: KP.KInv(es, fs, ctx, k), hw: {LB.ks.lab(es, fs, k, z) == Some{w} : Maybe<&2, DR.Lab>})
  -> {KS.ks.inb(k, SK.VE.y(DR.gmul(w, z))) == True{} : Bool}:
  match k:
    case KS.KS{+rows, +ds}:
      (+hrv, rr) = hi
      (+hl, ha) = rr
      SN.zero_of_in(KS.kexprs(es, fs, ds), rows, SK.VE.y(DR.gmul(w, z)), hrv, hl,
        klab_ok.go(PT.ptest(rows, KS.kexprs(es, fs, ds), SK.VE.y(z), SK.VE.x(z)), rows, KS.kexprs(es, fs, ds), z, w, hrv, hl, {==}, hw))

# if some nonzero a + i b has Im((a + i b) z) in K, the frame test finds a
# label
def ks_lab_some(+es: List<&2, SK.Ent>, +fs: List<&2, DR.Fact>, +ctx: List<&2, E.QExpr>, k: KS.KS, +z: SK.VE, hi: KP.KInv(es, fs, ctx, k),
  +a: S.Q, +bb: S.Q, hab: S.Q.eq(a, S.Q{S.Z0{}, S.XH{}}) -> S.Q.eq(bb, S.Q{S.Z0{}, S.XH{}}) -> Empty,
  +hin: SN.InSpan(SK.VE.y(DR.gmul(DR.Lab{a, bb}, z)), KS.kexprs(es, fs, KS.ks.ds(k))))
  -> {lis_some(LB.ks.lab(es, fs, k, z)) == True{} : Bool}:
  match k:
    case KS.KS{+rows, +ds}:
      (hrv, rr) = hi
      (hl, ha) = rr
      lis_map(PT.ptest(rows, KS.kexprs(es, fs, ds), SK.VE.y(z), SK.VE.x(z)),
        lab_some.pick(DR.qnz(bb), rows, KS.kexprs(es, fs, ds), SK.VE.y(z), SK.VE.x(z), a, bb, {==}, hrv, hl, hab,
          PP.in_tr(SK.VE.y(DR.gmul(DR.Lab{a, bb}, z)), PT.pcomb(PT.Pr{a, bb}, SK.VE.y(z), SK.VE.x(z)), KS.kexprs(es, fs, ds), hin, im_gmul_r(a, bb, z))))
