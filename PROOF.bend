# bend-cad: the proofs of every law in LAWS.bend. Each delegates to the
# library (lib/), where the proofs live; the ring laws are one call each to
# the normalizer they are stated beside.

import Base
import ./LAWS.bend as Laws
import ./spec/num.bend as S
import ./spec/ring.bend as E
import ./lib/pos.bend as P
import ./lib/z.bend as LZ
import ./lib/zring.bend as R
import ./lib/qring.bend as QR
import ./lib/q.bend as LQ
import ./lib/qord.bend as LQO
import ./lib/qemb.bend as QE
import ./lib/fmat.bend as FM
import ./lib/dmat.bend as DM
import ./spec/mat.bend as M
import ./spec/field.bend as O
import ./lib/dyadic.bend as LD
import ./lib/big.bend as LB
import ./lib/meaning.bend as MN

# Positives
# ---------

def Laws.pos_add(a, b):
  Equal.sym(Nat, Nat.add(S.Pos.nat(a), S.Pos.nat(b)), S.Pos.nat(S.Pos.add(a, b)), P.add_nat(a, b))

def Laws.pos_mul(a, b):
  Equal.sym(Nat, Nat.mul(S.Pos.nat(a), S.Pos.nat(b)), S.Pos.nat(S.Pos.mul(a, b)), P.mul_nat(a, b))

def Laws.pos_inj(a, b, e):
  P.nat_inj(a, b, e)

def Laws.pos_of_succ(n):
  Equal.sym(Nat, 1n+n, S.Pos.nat(S.Pos.of_succ(n)), P.nat_os(n))

# Integers
# --------

def Laws.z_parts(x):
  LZ.diff_parts(x)

def Laws.z_pnat(a, b):
  Equal.sym(Nat, Nat.sub(a, b), S.Z.pnat(S.Z.of_diff(a, b)), LZ.sub_pnat(a, b))

def Laws.z_nnat(a, b):
  Equal.sym(Nat, Nat.sub(b, a), S.Z.nnat(S.Z.of_diff(a, b)), LZ.sub_nnat(a, b))

def Laws.z_add(a, b, c, d):
  Equal.sym(S.Z, S.Z.of_diff(Nat.add(a, c), Nat.add(b, d)), S.Z.add(S.Z.of_diff(a, b), S.Z.of_diff(c, d)), LZ.add_hom(a, b, c, d))

def Laws.z_mul(a, b, c, d):
  Equal.sym(S.Z, S.Z.of_diff(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), Nat.add(Nat.mul(a, d), Nat.mul(b, c))), S.Z.mul(S.Z.of_diff(a, b), S.Z.of_diff(c, d)), LZ.mul_hom(a, b, c, d))

def Laws.z_neg(a, b):
  Equal.sym(S.Z, S.Z.of_diff(b, a), S.Z.neg(S.Z.of_diff(a, b)), LZ.neg_diff(a, b))

def Laws.pos_cmp(a, b):
  P.cmp_nat(a, b)

def Laws.z_cmp(x, y):
  LZ.cmp_nat(x, y)

# Ring identities
# ---------------

def Laws.ring_eq(env, e1, e2, h):
  R.ring_eq(env, e1, e2, h)

# The commutative ring laws, each one normalizer call.

def Laws.z_add_comm(x, y):
  Laws.ring_eq([x, y], E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZAdd{E.ZVar{1n}, E.ZVar{0n}}, {==})

def Laws.z_add_assoc(x, y, z):
  Laws.ring_eq([x, y, z], E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZAdd{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}, {==})

def Laws.z_add_zero(x):
  Laws.ring_eq([x], E.ZAdd{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZVar{0n}, {==})

def Laws.z_add_neg(x):
  Laws.ring_eq([x], E.ZAdd{E.ZVar{0n}, E.ZNeg{E.ZVar{0n}}}, E.ZCst{S.Z0{}}, {==})

def Laws.z_mul_comm(x, y):
  Laws.ring_eq([x, y], E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{1n}, E.ZVar{0n}}, {==})

def Laws.z_mul_assoc(x, y, z):
  Laws.ring_eq([x, y, z], E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, {==})

def Laws.z_mul_one(x):
  Laws.ring_eq([x], E.ZMul{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{0n}, {==})

def Laws.z_mul_add(x, y, z):
  Laws.ring_eq([x, y, z], E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, {==})

# Rationals
# ---------

def Laws.q_refl(x):
  LQ.q_refl(x)

def Laws.q_sym(x, y, h):
  LQ.q_sym(x, y, h)

def Laws.q_trans(x, y, z, h1, h2):
  LQ.q_trans(x, y, z, h1, h2)

def Laws.q_add_cong(x, x2, y, y2, h1, h2):
  LQ.q_trans(S.Q.add(x, y), S.Q.add(x2, y), S.Q.add(x2, y2), LQ.q_add_cong_l(x, x2, y, h1), LQ.q_add_cong_r(x2, y, y2, h2))

def Laws.q_mul_cong(x, x2, y, y2, h1, h2):
  LQ.q_trans(S.Q.mul(x, y), S.Q.mul(x2, y), S.Q.mul(x2, y2), LQ.q_mul_cong_l(x, x2, y, h1), LQ.q_mul_cong_r(x2, y, y2, h2))

def Laws.q_neg_cong(x, x2, h):
  LQ.q_neg_cong(x, x2, h)

# The order

def Laws.q_lt_irrefl(x, h):
  LQO.q_lt_irrefl(x, h)

def Laws.q_lt_trans(x, y, z, h1, h2):
  LQO.q_lt_trans(x, y, z, h1, h2)

def Laws.q_lt_total(x, y):
  LQO.q_lt_total(x, y)

def Laws.q_lt_cong(x, x2, y, y2, h1, h2, h):
  LQO.q_lt_cong(x, x2, y, y2, h1, h2, h)

def Laws.q_lt_add(x, y, z, h):
  LQO.q_lt_add(x, y, z, h)

def Laws.q_lt_mul(x, y, hx, hy):
  LQO.q_lt_mul(x, y, hx, hy)

def Laws.qring_eq(env, e1, e2, h):
  QR.qring_eq(env, e1, e2, h)

# The field laws, each one rational-normalizer call.

def Laws.q_add_comm(x, y):
  Laws.qring_eq([x, y], E.QAdd{E.QVar{0n}, E.QVar{1n}}, E.QAdd{E.QVar{1n}, E.QVar{0n}}, {==})

def Laws.q_add_assoc(x, y, z):
  Laws.qring_eq([x, y, z], E.QAdd{E.QAdd{E.QVar{0n}, E.QVar{1n}}, E.QVar{2n}}, E.QAdd{E.QVar{0n}, E.QAdd{E.QVar{1n}, E.QVar{2n}}}, {==})

def Laws.q_add_zero(x):
  Laws.qring_eq([x], E.QAdd{E.QVar{0n}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, E.QVar{0n}, {==})

def Laws.q_add_neg(x):
  Laws.qring_eq([x], E.QAdd{E.QVar{0n}, E.QNeg{E.QVar{0n}}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}, {==})

def Laws.q_mul_comm(x, y):
  Laws.qring_eq([x, y], E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QMul{E.QVar{1n}, E.QVar{0n}}, {==})

def Laws.q_mul_assoc(x, y, z):
  Laws.qring_eq([x, y, z], E.QMul{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QVar{2n}}, E.QMul{E.QVar{0n}, E.QMul{E.QVar{1n}, E.QVar{2n}}}, {==})

def Laws.q_mul_one(x):
  Laws.qring_eq([x], E.QMul{E.QVar{0n}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}, E.QVar{0n}, {==})

def Laws.q_mul_add(x, y, z):
  Laws.qring_eq([x, y, z], E.QMul{E.QVar{0n}, E.QAdd{E.QVar{1n}, E.QVar{2n}}}, E.QAdd{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QMul{E.QVar{0n}, E.QVar{2n}}}, {==})

def Laws.q_mul_inv(x, h):
  LQ.q_mul_inv(x, h)

# The rationals in every ordered field

def Laws.ofq_eq(F, x, y, h):
  QE.ofq_eq(~F, x, y, h)

def Laws.ofq_add(F, x, y):
  QE.ofq_add(~F, x, y)

def Laws.ofq_mul(F, x, y):
  QE.ofq_mul(~F, x, y)

def Laws.ofq_neg(F, x):
  QE.ofq_neg(~F, x)

def Laws.ofq_zero(F):
  QE.ofq_zero(~F)

def Laws.ofq_one(F):
  QE.ofq_one(~F)

def Laws.ofq_lt(F, x, y, h):
  QE.ofq_lt(~F, x, y, h)

def Laws.ofq_lt_rev(F, x, y, h):
  QE.ofq_lt_rev(~F, x, y, h)

def Laws.ofq_eq_rev(F, x, y, e):
  QE.ofq_eq_rev(~F, x, y, e)

# Dyadics
# -------

def Laws.d_add(x, y):
  LD.toq_add(x, y)

def Laws.d_mul(x, y):
  LD.toq_mul(x, y)

def Laws.d_neg(x):
  LD.toq_neg(x)

# Vectors and matrices
# --------------------

def Laws.mat_assoc(F, a, b, v):
  Equal.sym(M.Vec(~F), M.matvec(~F, a, M.matvec(~F, b, v)), M.matvec(~F, M.matmul(~F, a, b), v), FM.mat_assoc(~F, a, b, v))

def Laws.mat_add(F, a, b, v):
  Equal.sym(M.Vec(~F), M.vadd(~F, M.matvec(~F, a, v), M.matvec(~F, b, v)), M.matvec(~F, M.madd(~F, a, b), v), FM.mat_add(~F, a, b, v))

def Laws.mat_neg(F, a, v):
  Equal.sym(M.Vec(~F), M.vneg(~F, M.matvec(~F, a, v)), M.matvec(~F, M.mneg(~F, a), v), FM.mat_neg(~F, a, v))

def Laws.mat_ident(F, v):
  Equal.sym(M.Vec(~F), v, M.matvec(~F, M.ident(~F, M.len(~F, v)), v), FM.mat_ident(~F, v))

def Laws.ofd_add(F, x, y):
  Equal.sym(O.C(F), O.add(F, M.ofd(~F, x), M.ofd(~F, y)), M.ofd(~F, S.D.add(x, y)), DM.ofd_add(~F, x, y))

def Laws.ofd_mul(F, x, y):
  Equal.sym(O.C(F), O.mul(F, M.ofd(~F, x), M.ofd(~F, y)), M.ofd(~F, S.D.mul(x, y)), DM.ofd_mul(~F, x, y))

def Laws.ofd_neg(F, x):
  Equal.sym(O.C(F), O.neg(F, M.ofd(~F, x)), M.ofd(~F, S.D.neg(x)), DM.ofd_neg(~F, x))

def Laws.dvadd_ofd(F, u, w):
  Equal.sym(M.Vec(~F), M.vadd(~F, M.ofdv(~F, u), M.ofdv(~F, w)), M.ofdv(~F, M.dvadd(u, w)), DM.dvadd_ofd(~F, u, w))

def Laws.dvneg_ofd(F, u):
  Equal.sym(M.Vec(~F), M.vneg(~F, M.ofdv(~F, u)), M.ofdv(~F, M.dvneg(u)), DM.dvneg_ofd(~F, u))

def Laws.dmatvec_ofd(F, a, v):
  Equal.sym(M.Vec(~F), M.matvec(~F, M.ofdm(~F, a), M.ofdv(~F, v)), M.ofdv(~F, M.dmatvec(a, v)), DM.dmatvec_ofd(~F, a, v))

def Laws.dmatmul_ofd(F, a, b):
  Equal.sym(M.Mat(~F), M.matmul(~F, M.ofdm(~F, a), M.ofdm(~F, b)), M.ofdm(~F, M.dmatmul(a, b)), DM.dmatmul_ofd(~F, a, b))

def Laws.dmadd_ofd(F, a, b):
  Equal.sym(M.Mat(~F), M.madd(~F, M.ofdm(~F, a), M.ofdm(~F, b)), M.ofdm(~F, M.dmadd(a, b)), DM.dmadd_ofd(~F, a, b))

def Laws.dmneg_ofd(F, a):
  Equal.sym(M.Mat(~F), M.mneg(~F, M.ofdm(~F, a)), M.ofdm(~F, M.dmneg(a)), DM.dmneg_ofd(~F, a))

def Laws.dident_ofd(F, n):
  Equal.sym(M.Mat(~F), M.ident(~F, n), M.ofdm(~F, M.dident(n)), DM.dident_ofd(~F, n))

def Laws.maj_matvec(F, m, b, v, s, hm, hv):
  DM.maj_matvec(~F, m, b, v, s, hm, hv)

def Laws.maj_ofd(F, a):
  DM.maj_ofd(~F, a)

def Laws.vbnd_ofd(F, v):
  DM.vbnd_ofd(~F, v)

def Laws.vbnd_add(F, u, s, w, t, hu, hw):
  FM.vbnd_add(~F, u, s, w, t, hu, hw)

def Laws.vbnd_neg(F, u, s, h):
  FM.vbnd_neg(~F, u, s, h)

def Laws.vbnd_mono(F, u, s, t, h, hst):
  FM.vbnd_mono(~F, u, s, t, h, hst)

# Big integers
# ------------

def Laws.big_add(bp, a, b, wa, wb):
  LB.add_ok(bp, a, b, wa, wb)

def Laws.big_sub(bp, a, b, wa, wb):
  LB.sub_ok(bp, a, b, wa, wb)

def Laws.big_neg(bp, a):
  LB.neg_ok(bp, a)

def Laws.big_mul(bp, a, b):
  LB.mul_ok(bp, a, b)

def Laws.big_cmp(bp, a, b, hb, wa, wb):
  LB.cmp_ok(bp, a, b, hb, wa, wb)

def Laws.big_add_wf(bp, a, b, hb, wa, wb):
  LB.add_wf(bp, a, b, hb, wa, wb)

def Laws.big_sub_wf(bp, a, b, hb, wa, wb):
  LB.sub_wf(bp, a, b, hb, wa, wb)

def Laws.big_neg_wf(bp, a, wa):
  LB.neg_wf(bp, a, wa)

def Laws.big_mul_wf(bp, a, b, hb, wa, wb):
  LB.mul_wf(bp, a, b, hb, wa, wb)

# Meaning lemmas
# --------------
# Each holds in every ordered field (lib/meaning.bend); F is passed on as a
# template argument.

def Laws.means_sound(F, env, es, k, w, h):
  MN.means_sound(~F, env, es, k, w, h)

def Laws.means_complete(F, env, es, k, h):
  MN.means_complete(~F, env, es, k, h)

def Laws.ent_sound(F, env, e, h):
  MN.ent_sound(~F, env, e, h)

def Laws.ent_complete(F, env, e, h):
  MN.ent_complete(~F, env, e, h)

def Laws.sketch_sound(F, env, sk, w, h):
  MN.sketch_sound(~F, env, sk, w, h)

def Laws.sketch_complete(F, env, sk, h):
  MN.sketch_complete(~F, env, sk, h)
