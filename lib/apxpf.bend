# bend-cad: approximate inverses and the block's linear algebra, for
# solve_complete (DESIGN §10.4, C5a). Proofs only.
#
# C4's dinverse_ok bounds every entry of I - A J. Newton and the radius
# search use that as bounds on vectors and norms: |w - A J w| <= n e |w|,
# |A w| <= (1 + n e) b |w| when J has an inverse of norm b, the right
# defect I - J A, and Y, the inverse rounded to fewer bits. The rest
# reads the block in F: slopes against the Jacobian at a box's center,
# the dyadic Jacobian and values through any embedding of the dyadics,
# and the checker's comparisons as complete for dyadics.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/box.bend as BX
import ../spec/knum.bend as N
import ../spec/deriv.bend as DV
import ./karith.bend as KA
import ./kball.bend as KB
import ./cert.bend as CK
import ./certdef.bend as C
import ./certpf.bend as CP
import ./kinst.bend as KI
import ./numer.bend as NU
import ./struct.bend as ST
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./fmat.bend as FM
import ./fvec.bend as FV
import ./dmat.bend as DM
import ./gjpf.bend as GJ
import ./normpf.bend as NP
import ./dgjpf.bend as DG
import ./bndpf.bend as BP
import ./roundpf.bend as RP
import ./slope.bend as SL
import ./real.bend as RL

# The dyadics through any embedding
# ---------------------------------
# Every embedding of the dyadics in F is ofd: the dyadic m/2^e is held
# as itself, so the embedding's ofq law fixes its image.

def plog_pow2(e: Nat) -> {KI.plog(S.Pos.pow2(e)) == Some{e} : Maybe<&2, Nat>}:
  match e:
    case 0n:
      {==}
    case 1n+k:
      %Equal.sym(Maybe<&2, Nat>, KI.plog(S.Pos.pow2(k)), Some{k}, plog_pow2(k)) : {KI.plog.succ(_) == Some{1n+k} : Maybe<&2, Nat>}
      {==}

def dofq_d(+m: S.Z, +e: Nat) -> {KI.dofq(S.D.toq(S.D{m, e})) == Some{S.D{m, e}} : Maybe<&2, S.D>}:
  %Equal.sym(Maybe<&2, Nat>, KI.plog(S.Pos.pow2(e)), Some{e}, plog_pow2(e)) : {KI.dofq.go(m, _) == Some{S.D{m, e}} : Maybe<&2, S.D>}
  {==}

def hofd(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, x: S.D) -> {N.emap(KI.dnum(), F, H, x) == M.ofd(~F, x) : O.C(F)}:
  match x:
    case S.D{+m, +e}:
      N.e_ofq(KI.dnum(), F, H)(S.D.toq(S.D{m, e}))(S.D{m, e})(dofq_d(m, e))

def ofkv_d(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, v: List<&2, S.D>) -> {N.ofkv(~KI.dnum(), ~F, ~H, v) == M.ofdv(~F, v) : M.Vec(~F)}:
  match v:
    case Nil{}:
      {==}
    case Con{+x, xs}:
      %Equal.sym(O.C(F), N.emap(KI.dnum(), F, H, x), M.ofd(~F, x), hofd(~F, ~H, x)) : {Con{_, N.ofkv(~KI.dnum(), ~F, ~H, xs)} == Con{M.ofd(~F, x), M.ofdv(~F, xs)} : M.Vec(~F)}
      %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, xs), M.ofdv(~F, xs), ofkv_d(~F, ~H, xs)) : {Con{M.ofd(~F, x), _} == Con{M.ofd(~F, x), M.ofdv(~F, xs)} : M.Vec(~F)}
      {==}

def ofkm_d(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, a: List<&2, List<&2, S.D>>) -> {N.ofkm(~KI.dnum(), ~F, ~H, a) == M.ofdm(~F, a) : M.Mat(~F)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, rs}:
      %Equal.sym(M.Vec(~F), N.ofkv(~KI.dnum(), ~F, ~H, r), M.ofdv(~F, r), ofkv_d(~F, ~H, r)) : {Con{_, N.ofkm(~KI.dnum(), ~F, ~H, rs)} == Con{M.ofdv(~F, r), M.ofdm(~F, rs)} : M.Mat(~F)}
      %Equal.sym(M.Mat(~F), N.ofkm(~KI.dnum(), ~F, ~H, rs), M.ofdm(~F, rs), ofkm_d(~F, ~H, rs)) : {Con{M.ofdv(~F, r), _} == Con{M.ofdv(~F, r), M.ofdm(~F, rs)} : M.Mat(~F)}
      {==}

def bcen_zip(env: List<&2, S.D>) -> {KB.bcenters(~KI.dnum(), CK.zipb(~KI.dnum(), env, Nil{})) == env : List<&2, S.D>}:
  match env:
    case Nil{}:
      {==}
    case Con{+x, xs}:
      %Equal.sym(List<&2, S.D>, KB.bcenters(~KI.dnum(), CK.zipb(~KI.dnum(), xs, Nil{})), xs, bcen_zip(xs)) : {Con{x, _} == Con{x, xs} : List<&2, S.D>}
      {==}

# the solver's Jacobian at env (the slope centers at a box of radius 0)
def djac_ofd(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +eqs: List<&2, E.QExpr>, +n: Nat, +env: List<&2, S.D>, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}) -> {M.ofdm(~F, NU.jac(eqs, n, env)) == DV.jac(~F, M.ofdv(~F, env), eqs, ST.iota(n, 0n)) : M.Mat(~F)}:
  %ofkm_d(~F, ~H, NU.jac(eqs, n, env)) : {_ == DV.jac(~F, M.ofdv(~F, env), eqs, ST.iota(n, 0n)) : M.Mat(~F)}
  %ofkv_d(~F, ~H, env) : {N.ofkm(~KI.dnum(), ~F, ~H, NU.jac(eqs, n, env)) == DV.jac(~F, _, eqs, ST.iota(n, 0n)) : M.Mat(~F)}
  %bcen_zip(env) : {N.ofkm(~KI.dnum(), ~F, ~H, NU.jac(eqs, n, env)) == DV.jac(~F, N.ofkv(~KI.dnum(), ~F, ~H, _), eqs, ST.iota(n, 0n)) : M.Mat(~F)}
  BP.mcen_jac(~KI.dnum(), ~F, ~H, CK.zipb(~KI.dnum(), env, Nil{}), n, 0n, eqs, hh)

# the solver's values at env
def dvals_ofd(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +eqs: List<&2, E.QExpr>, +env: List<&2, S.D>, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}) -> {M.ofdv(~F, NU.vals(eqs, env)) == C.fvals(~F, eqs, M.ofdv(~F, env)) : M.Vec(~F)}:
  %ofkv_d(~F, ~H, NU.vals(eqs, env)) : {_ == C.fvals(~F, eqs, M.ofdv(~F, env)) : M.Vec(~F)}
  %ofkv_d(~F, ~H, env) : {N.ofkv(~KI.dnum(), ~F, ~H, NU.vals(eqs, env)) == C.fvals(~F, eqs, _) : M.Vec(~F)}
  CP.kvals_ofk(~KI.dnum(), ~F, ~H, env, eqs, hh)

def ddot_ofd(~F: O.OField, xs: List<&2, S.D>, ys: List<&2, S.D>) -> {M.ofd(~F, NU.ddot(xs, ys)) == M.dot(~F, M.ofdv(~F, xs), M.ofdv(~F, ys)) : O.C(F)}:
  match xs ys:
    case Nil{} ys:
      Equal.sym(O.C(F), O.zero(F), M.ofd(~F, M.d0()), DM.ofd_zero(~F))
    case Con{+x, +t} Nil{}:
      Equal.sym(O.C(F), O.zero(F), M.ofd(~F, M.d0()), DM.ofd_zero(~F))
    case Con{+x, +t} Con{+y, +u}:
      %DM.ofd_add(~F, S.D.mul(x, y), NU.ddot(t, u)) : {_ == M.dot(~F, Con{M.ofd(~F, x), M.ofdv(~F, t)}, Con{M.ofd(~F, y), M.ofdv(~F, u)}) : O.C(F)}
      %DM.ofd_mul(~F, x, y) : {O.add(F, _, M.ofd(~F, NU.ddot(t, u))) == M.dot(~F, Con{M.ofd(~F, x), M.ofdv(~F, t)}, Con{M.ofd(~F, y), M.ofdv(~F, u)}) : O.C(F)}
      %Equal.sym(O.C(F), M.ofd(~F, NU.ddot(t, u)), M.dot(~F, M.ofdv(~F, t), M.ofdv(~F, u)), ddot_ofd(~F, t, u)) : {O.add(F, O.mul(F, M.ofd(~F, x), M.ofd(~F, y)), _) == M.dot(~F, Con{M.ofd(~F, x), M.ofdv(~F, t)}, Con{M.ofd(~F, y), M.ofdv(~F, u)}) : O.C(F)}
      {==}

def dmatvec_ofd(~F: O.OField, a: List<&2, List<&2, S.D>>, +v: List<&2, S.D>) -> {M.ofdv(~F, NU.dmatvec(a, v)) == M.matvec(~F, M.ofdm(~F, a), M.ofdv(~F, v)) : M.Vec(~F)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      %Equal.sym(O.C(F), M.ofd(~F, NU.ddot(r, v)), M.dot(~F, M.ofdv(~F, r), M.ofdv(~F, v)), ddot_ofd(~F, r, v)) : {Con{_, M.ofdv(~F, NU.dmatvec(t, v))} == M.matvec(~F, M.ofdm(~F, Con{r, t}), M.ofdv(~F, v)) : M.Vec(~F)}
      %Equal.sym(M.Vec(~F), M.ofdv(~F, NU.dmatvec(t, v)), M.matvec(~F, M.ofdm(~F, t), M.ofdv(~F, v)), dmatvec_ofd(~F, t, v)) : {Con{M.dot(~F, M.ofdv(~F, r), M.ofdv(~F, v)), _} == M.matvec(~F, M.ofdm(~F, Con{r, t}), M.ofdv(~F, v)) : M.Vec(~F)}
      {==}

# Sums by index
# -------------

def nateq_sym(a: Nat, b: Nat) -> {KA.nateq(a, b) == KA.nateq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      {==}
    case 1n+i 1n+j:
      nateq_sym(i, j)

# the first n entries of r, each at most t, sum to at most n t
def rowabs_lt(~F: O.OField, r: M.Vec(~F), n: Nat, +t: O.C(F), +ht: O.le(~F, O.zero(F), t), +h: GJ.All(~(k => M.bnd(~F, O.lookup(~F, r, k), t)), n)) -> O.le(~F, NP.rowabs(~F, r, n), O.mul(F, FR.ofn(~F, n), t)):
  match r n:
    case Nil{} 0n:
      FV.le_rw_r(~F, O.zero(F), O.zero(F), O.mul(F, O.zero(F), t), Equal.sym(O.C(F), O.mul(F, O.zero(F), t), O.zero(F), FL.zero_mul(~F, t)), FO.le_refl(~F, O.zero(F)))
    case Nil{} 1n++k:
      FO.mul_nonneg(~F, FR.ofn(~F, 1n+k), t, DG.ofn_nn(~F, 1n+k), ht)
    case Con{+a, +xs} 0n:
      FV.le_rw_r(~F, O.zero(F), O.zero(F), O.mul(F, O.zero(F), t), Equal.sym(O.C(F), O.mul(F, O.zero(F), t), O.zero(F), FL.zero_mul(~F, t)), FO.le_refl(~F, O.zero(F)))
    case Con{+a, +xs} 1n++k:
      FV.le_rw_r(~F, NP.rowabs(~F, Con{a, xs}, 1n+k), O.add(F, t, O.mul(F, FR.ofn(~F, k), t)), O.mul(F, FR.ofn(~F, 1n+k), t), FR.fring_eq(~F, [t, FR.ofn(~F, k)], E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{0n}}}, E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{1n}}, E.ZVar{0n}}, {==}),
        RP.le_add2(~F, FV.fabs(~F, a), t, NP.rowabs(~F, xs, k), O.mul(F, FR.ofn(~F, k), t),
          FV.fabs_le(~F, a, t, GJ.all_at(~(j => M.bnd(~F, O.lookup(~F, Con{a, xs}, j), t)), 1n+k, h, 0n, {==})),
          rowabs_lt(~F, xs, k, t, ht, DG.all_shift(~(j => M.bnd(~F, O.lookup(~F, Con{a, xs}, j), t)), k, h))))

def le_len(~F: O.OField, +v: M.Vec(~F), +n: Nat, lv: {M.len(~F, v) == n : Nat}) -> {KA.natle(M.len(~F, v), n) == True{} : Bool}:
  %Equal.sym(Nat, M.len(~F, v), n, lv) : {KA.natle(_, n) == True{} : Bool}
  GJ.le_refl(n)

def lt_len(~F: O.OField, +v: M.Vec(~F), +n: Nat, lv: {M.len(~F, v) == n : Nat}, +k: Nat, hk: {KA.natle(1n+k, M.len(~F, v)) == True{} : Bool}) -> {KA.natle(1n+k, n) == True{} : Bool}:
  %lv : {KA.natle(1n+k, _) == True{} : Bool}
  hk

# Approximate inverses
# --------------------
# A with every entry of I - A J at most e (C4's agood), J n x n.

# entry i of v - A J v is (unit_i - row i of A J) . v
def vf_eq(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +A: M.Mat(~F), +v: M.Vec(~F), +lv: {M.len(~F, v) == n : Nat}, +i: Nat) -> {O.lookup(~F, BX.vsub(~F, v, M.matvec(~F, A, M.matvec(~F, jm, v))), i) == M.dot(~F, BX.vsub(~F, GJ.unit(~F, n, i), M.vecmat(~F, DV.mrow(~F, A, i), jm)), v) : O.C(F)}:
  +w = M.matvec(~F, A, M.matvec(~F, jm, v))
  +vm = M.vecmat(~F, DV.mrow(~F, A, i), jm)
  +un = GJ.unit(~F, n, i)
  %Equal.sym(O.C(F), O.lookup(~F, BX.vsub(~F, v, w), i), O.sub(~F, O.lookup(~F, v, i), O.lookup(~F, w, i)), DG.look_diff(~F, v, w, i)) : {_ == M.dot(~F, BX.vsub(~F, un, vm), v) : O.C(F)}
  %Equal.sym(O.C(F), O.lookup(~F, v, i), M.dot(~F, un, v), GJ.dot_unit(~F, n, i, v, le_len(~F, v, n, lv))) : {O.sub(~F, _, O.lookup(~F, w, i)) == M.dot(~F, BX.vsub(~F, un, vm), v) : O.C(F)}
  %Equal.sym(O.C(F), O.lookup(~F, w, i), M.dot(~F, DV.mrow(~F, A, i), M.matvec(~F, jm, v)), GJ.look_matvec(~F, A, M.matvec(~F, jm, v), i)) : {O.sub(~F, M.dot(~F, un, v), _) == M.dot(~F, BX.vsub(~F, un, vm), v) : O.C(F)}
  %Equal.sym(O.C(F), M.dot(~F, DV.mrow(~F, A, i), M.matvec(~F, jm, v)), M.dot(~F, vm, v), FM.vecmat_dot(~F, DV.mrow(~F, A, i), jm, v)) : {O.sub(~F, M.dot(~F, un, v), _) == M.dot(~F, BX.vsub(~F, un, vm), v) : O.C(F)}
  %FM.dot_vadd(~F, un, M.vneg(~F, vm), v) : {O.sub(~F, M.dot(~F, un, v), M.dot(~F, vm, v)) == _ : O.C(F)}
  %FM.dot_vneg(~F, vm, v) : {O.sub(~F, M.dot(~F, un, v), M.dot(~F, vm, v)) == O.add(F, M.dot(~F, un, v), _) : O.C(F)}
  {==}

# the entries of unit_i - row i of A J, below n
def vf_ent(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +A: M.Mat(~F), +e: O.C(F), +ha: DG.agood(~F, n, jm, A, e), +i: Nat, +hi: {KA.natle(1n+i, n) == True{} : Bool}, +k: Nat, +hk: {KA.natle(1n+k, n) == True{} : Bool}) -> M.bnd(~F, O.lookup(~F, BX.vsub(~F, GJ.unit(~F, n, i), M.vecmat(~F, DV.mrow(~F, A, i), jm)), k), e):
  +vm = M.vecmat(~F, DV.mrow(~F, A, i), jm)
  %Equal.sym(O.C(F), O.lookup(~F, BX.vsub(~F, GJ.unit(~F, n, i), vm), k), O.sub(~F, O.lookup(~F, GJ.unit(~F, n, i), k), O.lookup(~F, vm, k)), DG.look_diff(~F, GJ.unit(~F, n, i), vm, k)) : M.bnd(~F, _, e)
  %GJ.look_unit(~F, n, i, k, hk) : M.bnd(~F, O.sub(~F, _, O.lookup(~F, vm, k)), e)
  %Equal.sym(O.C(F), O.lookup(~F, vm, k), M.dot(~F, DV.mrow(~F, A, i), GJ.mcol(~F, jm, k)), DG.look_vecmat(~F, DV.mrow(~F, A, i), jm, k)) : M.bnd(~F, O.sub(~F, GJ.dl(~F, KA.nateq(k, i)), _), e)
  %nateq_sym(i, k) : M.bnd(~F, O.sub(~F, GJ.dl(~F, _), M.dot(~F, DV.mrow(~F, A, i), GJ.mcol(~F, jm, k))), e)
  GJ.all_at(~(q => M.bnd(~F, O.sub(~F, GJ.dl(~F, KA.nateq(i, q)), M.dot(~F, DV.mrow(~F, A, i), GJ.mcol(~F, jm, q))), e)), n,
    GJ.all_at(~(p => GJ.All(~(q => M.bnd(~F, O.sub(~F, GJ.dl(~F, KA.nateq(p, q)), M.dot(~F, DV.mrow(~F, A, p), GJ.mcol(~F, jm, q))), e)), n)), n, ha, i, hi), k, hk)

# |(v - A J v)_i| <= n e |v|
def vf_at(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +A: M.Mat(~F), +e: O.C(F), +he: O.le(~F, O.zero(F), e), +ha: DG.agood(~F, n, jm, A, e), +v: M.Vec(~F), +lv: {M.len(~F, v) == n : Nat}, +i: Nat, +hi: {KA.natle(1n+i, n) == True{} : Bool}) -> M.bnd(~F, O.lookup(~F, BX.vsub(~F, v, M.matvec(~F, A, M.matvec(~F, jm, v))), i), O.mul(F, O.mul(F, FR.ofn(~F, n), e), NP.vn(~F, v))):
  +r = BX.vsub(~F, GJ.unit(~F, n, i), M.vecmat(~F, DV.mrow(~F, A, i), jm))
  +hr = rowabs_lt(~F, r, n, e, he, GJ.all_mk(~n, ~(k => M.bnd(~F, O.lookup(~F, r, k), e)), ~(k => hk => vf_ent(~F, n, jm, A, e, ha, i, hi, k, hk)), n, GJ.le_refl(n)))
  %Equal.sym(O.C(F), O.lookup(~F, BX.vsub(~F, v, M.matvec(~F, A, M.matvec(~F, jm, v))), i), M.dot(~F, r, v), vf_eq(~F, n, jm, A, v, lv, i)) : M.bnd(~F, _, O.mul(F, O.mul(F, FR.ofn(~F, n), e), NP.vn(~F, v)))
  FM.bnd_mono(~F, M.dot(~F, r, v), O.mul(F, NP.rowabs(~F, r, n), NP.vn(~F, v)), O.mul(F, O.mul(F, FR.ofn(~F, n), e), NP.vn(~F, v)),
    (%lv : M.bnd(~F, M.dot(~F, r, v), O.mul(F, NP.rowabs(~F, r, _), NP.vn(~F, v)))
      NP.dot_le(~F, r, v, NP.vn(~F, v), FV.vmax_all(~F, v), FV.vmax_nn(~F, v))),
    FM.sub_nonneg(~F, O.mul(F, NP.rowabs(~F, r, n), NP.vn(~F, v)), O.mul(F, O.mul(F, FR.ofn(~F, n), e), NP.vn(~F, v)), FV.mul_le_r(~F, NP.rowabs(~F, r, n), O.mul(F, FR.ofn(~F, n), e), NP.vn(~F, v), FV.vmax_nn(~F, v), hr)))

def len_vfa(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +A: M.Mat(~F), +hA: {GJ.nrows(~F, A) == n : Nat}, +v: M.Vec(~F), +lv: {M.len(~F, v) == n : Nat}) -> {M.len(~F, BX.vsub(~F, v, M.matvec(~F, A, M.matvec(~F, jm, v)))) == n : Nat}:
  CP.len_vsub(~F, v, M.matvec(~F, A, M.matvec(~F, jm, v)), n, lv, GJ.len_mv(~F, A, n, M.matvec(~F, jm, v), hA))

# the vector form of C4's bound: |v - A J v| <= n e |v|
def vform(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +A: M.Mat(~F), +e: O.C(F), +he: O.le(~F, O.zero(F), e), +ha: DG.agood(~F, n, jm, A, e), +hA: {GJ.nrows(~F, A) == n : Nat}, +v: M.Vec(~F), +lv: {M.len(~F, v) == n : Nat}) -> O.le(~F, NP.vn(~F, BX.vsub(~F, v, M.matvec(~F, A, M.matvec(~F, jm, v)))), O.mul(F, O.mul(F, FR.ofn(~F, n), e), NP.vn(~F, v))):
  +d = BX.vsub(~F, v, M.matvec(~F, A, M.matvec(~F, jm, v)))
  +t = O.mul(F, O.mul(F, FR.ofn(~F, n), e), NP.vn(~F, v))
  FV.vmax_lub(~F, d, t, DG.vall_lt(~F, ~d, ~t, ~(k => hk => vf_at(~F, n, jm, A, e, he, ha, v, lv, k, lt_len(~F, d, n, len_vfa(~F, n, jm, A, hA, v, lv), k, hk)))),
    FO.mul_nonneg(~F, O.mul(F, FR.ofn(~F, n), e), NP.vn(~F, v), FO.mul_nonneg(~F, FR.ofn(~F, n), e, DG.ofn_nn(~F, n), he), FV.vmax_nn(~F, v)))

# |q| <= |p| + |p - q|
def tri_at(~F: O.OField, +p: M.Vec(~F), +q: M.Vec(~F), +k: Nat) -> M.bnd(~F, O.lookup(~F, q, k), O.add(F, NP.vn(~F, p), NP.vn(~F, BX.vsub(~F, p, q)))):
  KB.bnd_val(~F, O.sub(~F, O.lookup(~F, p, k), O.lookup(~F, BX.vsub(~F, p, q), k)), O.lookup(~F, q, k), O.add(F, NP.vn(~F, p), NP.vn(~F, BX.vsub(~F, p, q))),
    (%Equal.sym(O.C(F), O.lookup(~F, BX.vsub(~F, p, q), k), O.sub(~F, O.lookup(~F, p, k), O.lookup(~F, q, k)), DG.look_diff(~F, p, q, k)) : {O.sub(~F, O.lookup(~F, p, k), _) == O.lookup(~F, q, k) : O.C(F)}
      FR.fring_eq(~F, [O.lookup(~F, p, k), O.lookup(~F, q, k)], E.ZSub{E.ZVar{0n}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}}, E.ZVar{1n}, {==})),
    FM.bnd_add(~F, O.lookup(~F, p, k), NP.vn(~F, p), O.neg(F, O.lookup(~F, BX.vsub(~F, p, q), k)), NP.vn(~F, BX.vsub(~F, p, q)),
      DG.look_bnd(~F, p, k, NP.vn(~F, p), FV.vmax_all(~F, p), FV.vmax_nn(~F, p)),
      FM.bnd_neg(~F, O.lookup(~F, BX.vsub(~F, p, q), k), NP.vn(~F, BX.vsub(~F, p, q)), DG.look_bnd(~F, BX.vsub(~F, p, q), k, NP.vn(~F, BX.vsub(~F, p, q)), FV.vmax_all(~F, BX.vsub(~F, p, q)), FV.vmax_nn(~F, BX.vsub(~F, p, q))))))

def vn_tri(~F: O.OField, +p: M.Vec(~F), +q: M.Vec(~F)) -> O.le(~F, NP.vn(~F, q), O.add(F, NP.vn(~F, p), NP.vn(~F, BX.vsub(~F, p, q)))):
  FV.vmax_lub(~F, q, O.add(F, NP.vn(~F, p), NP.vn(~F, BX.vsub(~F, p, q))), DG.vall_by(~F, ~q, ~O.add(F, NP.vn(~F, p), NP.vn(~F, BX.vsub(~F, p, q))), ~(k => tri_at(~F, p, q, k))),
    FO.nonneg_add(~F, NP.vn(~F, p), NP.vn(~F, BX.vsub(~F, p, q)), FV.vmax_nn(~F, p), FV.vmax_nn(~F, BX.vsub(~F, p, q))))

# alpha = (1 + n e) b
def alf(~F: O.OField, +n: Nat, +e: O.C(F), +b: O.C(F)) -> O.C(F):
  O.mul(F, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), e)), b)

def alf_nn(~F: O.OField, +n: Nat, +e: O.C(F), +b: O.C(F), +he: O.le(~F, O.zero(F), e), +hb: O.le(~F, O.zero(F), b)) -> O.le(~F, O.zero(F), alf(~F, n, e, b)):
  FO.mul_nonneg(~F, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), e)), b, FO.nonneg_add(~F, O.one(F), O.mul(F, FR.ofn(~F, n), e), NP.one_nn(~F), FO.mul_nonneg(~F, FR.ofn(~F, n), e, DG.ofn_nn(~F, n), he)), hb)

# |A J u| <= (1 + n e) |u|
def aju(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +A: M.Mat(~F), +e: O.C(F), +he: O.le(~F, O.zero(F), e), +ha: DG.agood(~F, n, jm, A, e), +hA: {GJ.nrows(~F, A) == n : Nat}, +u: M.Vec(~F), +lu: {M.len(~F, u) == n : Nat}) -> O.le(~F, NP.vn(~F, M.matvec(~F, A, M.matvec(~F, jm, u))), O.mul(F, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), e)), NP.vn(~F, u))):
  DM.le_trans(~F, NP.vn(~F, M.matvec(~F, A, M.matvec(~F, jm, u))), O.add(F, NP.vn(~F, u), NP.vn(~F, BX.vsub(~F, u, M.matvec(~F, A, M.matvec(~F, jm, u))))), O.mul(F, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), e)), NP.vn(~F, u)),
    vn_tri(~F, u, M.matvec(~F, A, M.matvec(~F, jm, u))),
    FV.le_rw_r(~F, O.add(F, NP.vn(~F, u), NP.vn(~F, BX.vsub(~F, u, M.matvec(~F, A, M.matvec(~F, jm, u))))), O.add(F, NP.vn(~F, u), O.mul(F, O.mul(F, FR.ofn(~F, n), e), NP.vn(~F, u))), O.mul(F, O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), e)), NP.vn(~F, u)),
      FR.fring_eq(~F, [NP.vn(~F, u), FR.ofn(~F, n), e], E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{0n}}}, E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZVar{0n}}, {==}),
      RP.le_add2(~F, NP.vn(~F, u), NP.vn(~F, u), NP.vn(~F, BX.vsub(~F, u, M.matvec(~F, A, M.matvec(~F, jm, u)))), O.mul(F, O.mul(F, FR.ofn(~F, n), e), NP.vn(~F, u)), FO.le_refl(~F, NP.vn(~F, u)), vform(~F, n, jm, A, e, he, ha, hA, u, lu))))

# with Z an inverse of norm <= b: |A w| <= alpha |w|
def abound.go(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +A: M.Mat(~F), +e: O.C(F), +b: O.C(F), +he: O.le(~F, O.zero(F), e), +ha: DG.agood(~F, n, jm, A, e), +hA: {GJ.nrows(~F, A) == n : Nat}, +hj: {GJ.nrows(~F, jm) == n : Nat}, +z: M.Mat(~F), +hinv: DV.Inverse(~F, jm, z, n), +hz: {GJ.nrows(~F, z) == n : Nat}, +hzb: O.le(~F, NP.mnorm(~F, z, n), b), +w: M.Vec(~F), +lw: {M.len(~F, w) == n : Nat}) -> O.le(~F, NP.vn(~F, M.matvec(~F, A, w)), O.mul(F, alf(~F, n, e, b), NP.vn(~F, w))):
  +u = M.matvec(~F, z, w)
  +c1 = O.add(F, O.one(F), O.mul(F, FR.ofn(~F, n), e))
  %GJ.inv_r(~F, jm, z, n, hinv, hj, w, lw) : O.le(~F, NP.vn(~F, M.matvec(~F, A, _)), O.mul(F, alf(~F, n, e, b), NP.vn(~F, w)))
  DM.le_trans(~F, NP.vn(~F, M.matvec(~F, A, M.matvec(~F, jm, u))), O.mul(F, c1, NP.vn(~F, u)), O.mul(F, alf(~F, n, e, b), NP.vn(~F, w)),
    aju(~F, n, jm, A, e, he, ha, hA, u, GJ.len_mv(~F, z, n, w, hz)),
    FV.le_rw_r(~F, O.mul(F, c1, NP.vn(~F, u)), O.mul(F, c1, O.mul(F, b, NP.vn(~F, w))), O.mul(F, alf(~F, n, e, b), NP.vn(~F, w)), FR.fring_eq(~F, [c1, b, NP.vn(~F, w)], E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, {==}),
      FV.mul_le(~F, c1, NP.vn(~F, u), O.mul(F, b, NP.vn(~F, w)), FO.nonneg_add(~F, O.one(F), O.mul(F, FR.ofn(~F, n), e), NP.one_nn(~F), FO.mul_nonneg(~F, FR.ofn(~F, n), e, DG.ofn_nn(~F, n), he)),
        DM.le_trans(~F, NP.vn(~F, u), O.mul(F, NP.mnorm(~F, z, n), NP.vn(~F, w)), O.mul(F, b, NP.vn(~F, w)), NP.mv_n(~F, z, n, w, lw), FV.mul_le_r(~F, NP.mnorm(~F, z, n), b, NP.vn(~F, w), FV.vmax_nn(~F, w), hzb)))))

def abound(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +A: M.Mat(~F), +e: O.C(F), +b: O.C(F), +he: O.le(~F, O.zero(F), e), +ha: DG.agood(~F, n, jm, A, e), +hA: {GJ.nrows(~F, A) == n : Nat}, +hj: {GJ.nrows(~F, jm) == n : Nat}, +hJ: NP.InvB(~F, jm, n, b), +w: M.Vec(~F), +lw: {M.len(~F, w) == n : Nat}) -> O.le(~F, NP.vn(~F, M.matvec(~F, A, w)), O.mul(F, alf(~F, n, e, b), NP.vn(~F, w))):
  match hJ:
    case (+z, p):
      match p:
        case (hinv, q):
          match q:
            case (hz, hzb):
              abound.go(~F, n, jm, A, e, b, he, ha, hA, hj, z, hinv, hz, hzb, w, lw)

# An operator bound gives the norm
# --------------------------------
# |M s| <= c for every s of length n with |s| <= 1 (ob, a template lemma)
# gives mnorm(M, n) <= c: each row read against its own signs.

def op_row(~F: O.OField, ~a: M.Mat(~F), ~n: Nat, ~c: O.C(F), ~ob: @s: M.Vec(~F) -> {M.len(~F, s) == n : Nat} -> O.le(~F, NP.vn(~F, s), O.one(F)) -> O.le(~F, NP.vn(~F, M.matvec(~F, a, s)), c), +k: Nat, +r: M.Vec(~F), +t: M.Mat(~F), e: {NP.mdrop(~F, k, a) == Con{r, t} : M.Mat(~F)}) -> O.le(~F, NP.rowabs(~F, r, n), c):
  %NP.sgnv_dot(~F, r, n) : O.le(~F, _, c)
  DM.le_trans(~F, M.dot(~F, r, NP.sgnv(~F, r, n)), NP.vn(~F, M.matvec(~F, Con{r, t}, NP.sgnv(~F, r, n))), c,
    DM.le_trans(~F, M.dot(~F, r, NP.sgnv(~F, r, n)), FV.fabs(~F, M.dot(~F, r, NP.sgnv(~F, r, n))), NP.vn(~F, M.matvec(~F, Con{r, t}, NP.sgnv(~F, r, n))), NP.bnd_lo(~F, M.dot(~F, r, NP.sgnv(~F, r, n)), FV.fabs(~F, M.dot(~F, r, NP.sgnv(~F, r, n))), FV.fabs_bnd(~F, M.dot(~F, r, NP.sgnv(~F, r, n)))), FV.fmax_l(~F, FV.fabs(~F, M.dot(~F, r, NP.sgnv(~F, r, n))), NP.vn(~F, M.matvec(~F, t, NP.sgnv(~F, r, n))))),
    DM.le_trans(~F, NP.vn(~F, M.matvec(~F, Con{r, t}, NP.sgnv(~F, r, n))), NP.vn(~F, M.matvec(~F, a, NP.sgnv(~F, r, n))), c,
      (%e : O.le(~F, NP.vn(~F, M.matvec(~F, _, NP.sgnv(~F, r, n))), NP.vn(~F, M.matvec(~F, a, NP.sgnv(~F, r, n))))
        NP.drop_mv(~F, k, a, NP.sgnv(~F, r, n))),
      ob(NP.sgnv(~F, r, n), NP.sgnv_len(~F, r, n), NP.sgnv_vn(~F, r, n))))

def op_rows(~F: O.OField, ~a: M.Mat(~F), ~n: Nat, ~c: O.C(F), ~ob: @s: M.Vec(~F) -> {M.len(~F, s) == n : Nat} -> O.le(~F, NP.vn(~F, s), O.one(F)) -> O.le(~F, NP.vn(~F, M.matvec(~F, a, s)), c), rest: M.Mat(~F), +k: Nat, +e: {NP.mdrop(~F, k, a) == rest : M.Mat(~F)}) -> NP.rowsle(~F, rest, n, c):
  match rest:
    case Nil{}:
      Unit{}
    case Con{+r, +t}:
      (op_row(~F, ~a, ~n, ~c, ~ob, k, r, t, e), op_rows(~F, ~a, ~n, ~c, ~ob, t, 1n+k, NP.drop_succ(~F, k, a, r, t, e)))

def op_mn(~F: O.OField, ~a: M.Mat(~F), ~n: Nat, ~c: O.C(F), ~ob: @s: M.Vec(~F) -> {M.len(~F, s) == n : Nat} -> O.le(~F, NP.vn(~F, s), O.one(F)) -> O.le(~F, NP.vn(~F, M.matvec(~F, a, s)), c), +hc: O.le(~F, O.zero(F), c)) -> O.le(~F, NP.mnorm(~F, a, n), c):
  NP.mnorm_lub(~F, a, n, c, op_rows(~F, ~a, ~n, ~c, ~ob, a, 0n, NP.mdrop0(~F, a)), hc)

# c |s| <= c for |s| <= 1
def le_by1(~F: O.OField, +x: O.C(F), +c: O.C(F), +s: O.C(F), +hc: O.le(~F, O.zero(F), c), hx: O.le(~F, x, O.mul(F, c, s)), hs: O.le(~F, s, O.one(F))) -> O.le(~F, x, c):
  DM.le_trans(~F, x, O.mul(F, c, s), c, hx, FV.le_rw_r(~F, O.mul(F, c, s), O.mul(F, c, O.one(F)), c, FR.fring_eq(~F, [c], E.ZMul{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{0n}, {==}), FV.mul_le(~F, c, s, O.one(F), hc, hs)))

# mnorm(A) <= alpha
def amn(~F: O.OField, +n: Nat, +jm: M.Mat(~F), +A: M.Mat(~F), +e: O.C(F), +b: O.C(F), +he: O.le(~F, O.zero(F), e), +hb: O.le(~F, O.zero(F), b), +ha: DG.agood(~F, n, jm, A, e), +hA: {GJ.nrows(~F, A) == n : Nat}, +hj: {GJ.nrows(~F, jm) == n : Nat}, +hJ: NP.InvB(~F, jm, n, b)) -> O.le(~F, NP.mnorm(~F, A, n), alf(~F, n, e, b)):
  op_mn(~F, ~A, ~n, ~alf(~F, n, e, b), ~(s => ls => hs => le_by1(~F, NP.vn(~F, M.matvec(~F, A, s)), alf(~F, n, e, b), NP.vn(~F, s), alf_nn(~F, n, e, b, he, hb), abound(~F, n, jm, A, e, b, he, ha, hA, hj, hJ, s, ls), hs)), alf_nn(~F, n, e, b, he, hb))

# F-boxes
# -------
# A box of F's own balls (BP.fnum): a center and one radius for every
# variable, so C3a's Lipschitz lemmas compare slopes between points of
# the box with the Jacobian at its center.

def fbx(~F: O.OField, c: M.Vec(~F), +rad: O.C(F)) -> List<&2, KB.KB<BP.fnum(~F)>>:
  match c:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      Con{KB.KB{a, rad}, fbx(~F, t, rad)}

def bcen_fbx(~F: O.OField, c: M.Vec(~F), +rad: O.C(F)) -> {KB.bcenters(~BP.fnum(~F), fbx(~F, c, rad)) == c : M.Vec(~F)}:
  match c:
    case Nil{}:
      {==}
    case Con{+a, t}:
      %Equal.sym(M.Vec(~F), KB.bcenters(~BP.fnum(~F), fbx(~F, t, rad)), t, bcen_fbx(~F, t, rad)) : {Con{a, _} == Con{a, t} : M.Vec(~F)}
      {==}

def cen_fbx(~F: O.OField, +c: M.Vec(~F), +rad: O.C(F)) -> {BP.cen(~BP.fnum(~F), ~F, ~BP.femb(~F), fbx(~F, c, rad)) == c : M.Vec(~F)}:
  %Equal.sym(M.Vec(~F), KB.bcenters(~BP.fnum(~F), fbx(~F, c, rad)), c, bcen_fbx(~F, c, rad)) : {N.ofkv(~BP.fnum(~F), ~F, ~BP.femb(~F), _) == c : M.Vec(~F)}
  BP.ofkv_id(~F, c)

def le_one_mul(~F: O.OField, +x: O.C(F)) -> O.le(~F, x, O.mul(F, O.one(F), x)):
  FV.le_rw_r(~F, x, x, O.mul(F, O.one(F), x), FR.fring_eq(~F, [x], E.ZVar{0n}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, {==}), FO.le_refl(~F, x))

# every center within bb - rad: the box has grade (bb, 1) at rad
def gbox_fbx(~F: O.OField, c: M.Vec(~F), +rad: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rad), hc: M.vbnd.all(~F, c, O.sub(~F, bb, rad))) -> BP.gbox(~BP.fnum(~F), ~F, ~BP.femb(~F), rad, bb, fbx(~F, c, rad)):
  match c:
    case Nil{}:
      Unit{}
    case Con{+a, +t}:
      (h1, h2) = hc
      ((hr, (h1, le_one_mul(~F, rad))), gbox_fbx(~F, t, rad, bb, hr, h2))

# x within rad of the center c, entry by entry, lies in the box
def inbox_fbx(~F: O.OField, x: M.Vec(~F), c: M.Vec(~F), +rad: O.C(F), h: M.vbnd.all(~F, BX.vsub(~F, x, c), rad), hl: {M.len(~F, x) == M.len(~F, c) : Nat}) -> KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), x, fbx(~F, c, rad)):
  match x c:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} Con{b, cs}:
      FO.absurd(KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), Nil{}, fbx(~F, Con{b, cs}, rad)), FV.zero_ne(M.len(~F, cs), hl))
    case Con{a, xs} Nil{}:
      FO.absurd(KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), Con{a, xs}, Nil{}), FV.succ_ne(M.len(~F, xs), hl))
    case Con{+a, +xs} Con{+b, +cs}:
      (h1, h2) = h
      (h1, inbox_fbx(~F, xs, cs, rad, h2, FV.succ_inj(M.len(~F, xs), M.len(~F, cs), hl)))

# The equations' constants
# ------------------------
# lam and ms bound every equation's slope grades ls and ms (C3a) at bb.

def eqok(~F: O.OField, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), eqs: List<&2, E.QExpr>) -> Data:
  match eqs:
    case Nil{}:
      Unit
    case Con{e, es}:
      M.Both(O.le(~F, BP.ls(~F, bb, e), lam), M.Both(O.le(~F, BP.ms(~F, bb, e), ms), eqok(~F, bb, lam, ms, es)))

def eqok_ls(~F: O.OField, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +e: E.QExpr, +es: List<&2, E.QExpr>, h: eqok(~F, bb, lam, ms, Con{e, es})) -> O.le(~F, BP.ls(~F, bb, e), lam):
  (h1, h2) = h
  h1

def eqok_ms.go(~F: O.OField, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +e: E.QExpr, +es: List<&2, E.QExpr>, h: M.Both(O.le(~F, BP.ms(~F, bb, e), ms), eqok(~F, bb, lam, ms, es))) -> O.le(~F, BP.ms(~F, bb, e), ms):
  (h1, h2) = h
  h1

def eqok_tl.go(~F: O.OField, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +e: E.QExpr, +es: List<&2, E.QExpr>, h: M.Both(O.le(~F, BP.ms(~F, bb, e), ms), eqok(~F, bb, lam, ms, es))) -> eqok(~F, bb, lam, ms, es):
  (h1, h2) = h
  h2

def eqok_rest(~F: O.OField, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +e: E.QExpr, +es: List<&2, E.QExpr>, h: eqok(~F, bb, lam, ms, Con{e, es})) -> M.Both(O.le(~F, BP.ms(~F, bb, e), ms), eqok(~F, bb, lam, ms, es)):
  (h1, h2) = h
  h2

def eqok_ms(~F: O.OField, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +e: E.QExpr, +es: List<&2, E.QExpr>, +h: eqok(~F, bb, lam, ms, Con{e, es})) -> O.le(~F, BP.ms(~F, bb, e), ms):
  eqok_ms.go(~F, bb, lam, ms, e, es, eqok_rest(~F, bb, lam, ms, e, es, h))

def eqok_tl(~F: O.OField, +bb: O.C(F), +lam: O.C(F), +ms: O.C(F), +e: E.QExpr, +es: List<&2, E.QExpr>, +h: eqok(~F, bb, lam, ms, Con{e, es})) -> eqok(~F, bb, lam, ms, es):
  eqok_tl.go(~F, bb, lam, ms, e, es, eqok_rest(~F, bb, lam, ms, e, es, h))

# Slopes against the Jacobian at the center
# ------------------------------------------

def le_mul_r(~F: O.OField, +a: O.C(F), +b: O.C(F), +s: O.C(F), +hs: O.le(~F, O.zero(F), s), h: O.le(~F, a, b)) -> O.le(~F, O.zero(F), O.sub(~F, O.mul(F, b, s), O.mul(F, a, s))):
  FM.sub_nonneg(~F, O.mul(F, a, s), O.mul(F, b, s), FV.mul_le_r(~F, a, b, s, hs, h))

# one equation's slopes between x1 and x2 differ from those at the center by lam rad
def srow_lip(~F: O.OField, +rad: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rad), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<BP.fnum(~F)>>, +hg: BP.gbox(~BP.fnum(~F), ~F, ~BP.femb(~F), rad, bb, box), +x1: M.Vec(~F), +x2: M.Vec(~F), +h1: KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), x1, box), +h2: KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), x2, box), +e: E.QExpr, +lam: O.C(F), +hl: O.le(~F, BP.ls(~F, bb, e), lam), cnt: Nat, +lo: Nat) -> M.vbnd.all(~F, BX.vsub(~F, SL.srange(~F, x1, x2, e, cnt, lo), SL.srange(~F, BP.cen(~BP.fnum(~F), ~F, ~BP.femb(~F), box), BP.cen(~BP.fnum(~F), ~F, ~BP.femb(~F), box), e, cnt, lo)), O.mul(F, lam, rad)):
  match cnt:
    case 0n:
      Unit{}
    case 1n+k:
      (FM.bnd_mono(~F, O.sub(~F, SL.sl(~F, lo, x1, x2, e), SL.sl(~F, lo, BP.cen(~BP.fnum(~F), ~F, ~BP.femb(~F), box), BP.cen(~BP.fnum(~F), ~F, ~BP.femb(~F), box), e)), O.mul(F, BP.ls(~F, bb, e), rad), O.mul(F, lam, rad),
         BP.sl_lip(~BP.fnum(~F), ~F, ~BP.femb(~F), rad, bb, hr, hb, box, hg, lo, x1, x2, h1, h2, e, BP.held_f(~F, e)),
         le_mul_r(~F, BP.ls(~F, bb, e), lam, rad, hr, hl)),
       srow_lip(~F, rad, bb, hr, hb, box, hg, x1, x2, h1, h2, e, lam, hl, k, 1n+lo))

# one equation's slopes are at most ms
def srow_maj(~F: O.OField, +rad: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rad), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<BP.fnum(~F)>>, +hg: BP.gbox(~BP.fnum(~F), ~F, ~BP.femb(~F), rad, bb, box), +x1: M.Vec(~F), +x2: M.Vec(~F), +h1: KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), x1, box), +h2: KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), x2, box), +e: E.QExpr, +ms: O.C(F), +hm: O.le(~F, BP.ms(~F, bb, e), ms), cnt: Nat, +lo: Nat) -> M.vbnd.all(~F, SL.srange(~F, x1, x2, e, cnt, lo), ms):
  match cnt:
    case 0n:
      Unit{}
    case 1n+k:
      (FM.bnd_mono(~F, SL.sl(~F, lo, x1, x2, e), BP.ms(~F, bb, e), ms, BP.sl_maj(~BP.fnum(~F), ~F, ~BP.femb(~F), rad, bb, hr, hb, box, hg, lo, x1, x2, h1, h2, e, BP.held_f(~F, e)), FM.sub_nonneg(~F, BP.ms(~F, bb, e), ms, hm)),
       srow_maj(~F, rad, bb, hr, hb, box, hg, x1, x2, h1, h2, e, ms, hm, k, 1n+lo))

def lr_nn(~F: O.OField, +cnt: Nat, +lam: O.C(F), +rad: O.C(F), +hl: O.le(~F, O.zero(F), lam), +hr: O.le(~F, O.zero(F), rad)) -> O.le(~F, O.zero(F), O.mul(F, FR.ofn(~F, cnt), O.mul(F, lam, rad))):
  FO.mul_nonneg(~F, FR.ofn(~F, cnt), O.mul(F, lam, rad), DG.ofn_nn(~F, cnt), FO.mul_nonneg(~F, lam, rad, hl, hr))

# S - J(center): every row's first cnt entries sum to at most cnt lam rad
def smat_lip(~F: O.OField, +rad: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rad), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<BP.fnum(~F)>>, +hg: BP.gbox(~BP.fnum(~F), ~F, ~BP.femb(~F), rad, bb, box), +x1: M.Vec(~F), +x2: M.Vec(~F), +h1: KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), x1, box), +h2: KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), x2, box), +lam: O.C(F), +ms: O.C(F), +hl0: O.le(~F, O.zero(F), lam), eqs: List<&2, E.QExpr>, +hq: eqok(~F, bb, lam, ms, eqs), +cnt: Nat, +lo: Nat) -> NP.rowsle(~F, M.madd(~F, CP.smat(~F, x1, x2, eqs, cnt, lo), M.mneg(~F, DV.jac(~F, BP.cen(~BP.fnum(~F), ~F, ~BP.femb(~F), box), eqs, ST.iota(cnt, lo)))), cnt, O.mul(F, FR.ofn(~F, cnt), O.mul(F, lam, rad))):
  match eqs:
    case Nil{}:
      Unit{}
    case Con{+e, +es}:
      +c = BP.cen(~BP.fnum(~F), ~F, ~BP.femb(~F), box)
      ((%BP.srange_jrow(~F, c, e, cnt, lo) : O.le(~F, NP.rowabs(~F, BX.vsub(~F, SL.srange(~F, x1, x2, e, cnt, lo), _), cnt), O.mul(F, FR.ofn(~F, cnt), O.mul(F, lam, rad)))
          DG.rowabs_le(~F, BX.vsub(~F, SL.srange(~F, x1, x2, e, cnt, lo), SL.srange(~F, c, c, e, cnt, lo)), cnt, O.mul(F, lam, rad), srow_lip(~F, rad, bb, hr, hb, box, hg, x1, x2, h1, h2, e, lam, eqok_ls(~F, bb, lam, ms, e, es, hq), cnt, lo), FO.mul_nonneg(~F, lam, rad, hl0, hr))),
       smat_lip(~F, rad, bb, hr, hb, box, hg, x1, x2, h1, h2, lam, ms, hl0, es, eqok_tl(~F, bb, lam, ms, e, es, hq), cnt, lo))

def smat_lip_mn(~F: O.OField, +rad: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rad), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<BP.fnum(~F)>>, +hg: BP.gbox(~BP.fnum(~F), ~F, ~BP.femb(~F), rad, bb, box), +x1: M.Vec(~F), +x2: M.Vec(~F), +h1: KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), x1, box), +h2: KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), x2, box), +lam: O.C(F), +ms: O.C(F), +hl0: O.le(~F, O.zero(F), lam), +eqs: List<&2, E.QExpr>, +hq: eqok(~F, bb, lam, ms, eqs), +cnt: Nat, +lo: Nat) -> O.le(~F, NP.mnorm(~F, M.madd(~F, CP.smat(~F, x1, x2, eqs, cnt, lo), M.mneg(~F, DV.jac(~F, BP.cen(~BP.fnum(~F), ~F, ~BP.femb(~F), box), eqs, ST.iota(cnt, lo)))), cnt), O.mul(F, FR.ofn(~F, cnt), O.mul(F, lam, rad))):
  NP.mnorm_lub(~F, M.madd(~F, CP.smat(~F, x1, x2, eqs, cnt, lo), M.mneg(~F, DV.jac(~F, BP.cen(~BP.fnum(~F), ~F, ~BP.femb(~F), box), eqs, ST.iota(cnt, lo)))), cnt, O.mul(F, FR.ofn(~F, cnt), O.mul(F, lam, rad)), smat_lip(~F, rad, bb, hr, hb, box, hg, x1, x2, h1, h2, lam, ms, hl0, eqs, hq, cnt, lo), lr_nn(~F, cnt, lam, rad, hl0, hr))

def smaj_cons(~F: O.OField, +r: M.Vec(~F), +t: M.Mat(~F), +ms: O.C(F), +cnt: Nat, +hm0: O.le(~F, O.zero(F), ms), +hr: M.vbnd.all(~F, r, ms), h: M.Both(DG.mall(~F, t, ms), NP.rowsle(~F, t, cnt, O.mul(F, FR.ofn(~F, cnt), ms)))) -> M.Both(DG.mall(~F, Con{r, t}, ms), NP.rowsle(~F, Con{r, t}, cnt, O.mul(F, FR.ofn(~F, cnt), ms))):
  (ha, hb) = h
  ((hr, ha), (DG.rowabs_le(~F, r, cnt, ms, hr, hm0), hb))

# |S| <= cnt ms
def smat_maj(~F: O.OField, +rad: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rad), +hb: O.le(~F, O.zero(F), bb), +box: List<&2, KB.KB<BP.fnum(~F)>>, +hg: BP.gbox(~BP.fnum(~F), ~F, ~BP.femb(~F), rad, bb, box), +x1: M.Vec(~F), +x2: M.Vec(~F), +h1: KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), x1, box), +h2: KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), x2, box), +lam: O.C(F), +ms: O.C(F), +hm0: O.le(~F, O.zero(F), ms), eqs: List<&2, E.QExpr>, +hq: eqok(~F, bb, lam, ms, eqs), +cnt: Nat, +lo: Nat) -> M.Both(DG.mall(~F, CP.smat(~F, x1, x2, eqs, cnt, lo), ms), NP.rowsle(~F, CP.smat(~F, x1, x2, eqs, cnt, lo), cnt, O.mul(F, FR.ofn(~F, cnt), ms))):
  match eqs:
    case Nil{}:
      (Unit{}, Unit{})
    case Con{+e, +es}:
      +hrow = srow_maj(~F, rad, bb, hr, hb, box, hg, x1, x2, h1, h2, e, ms, eqok_ms(~F, bb, lam, ms, e, es, hq), cnt, lo)
      smaj_cons(~F, SL.srange(~F, x1, x2, e, cnt, lo), CP.smat(~F, x1, x2, es, cnt, lo), ms, cnt, hm0, hrow, smat_maj(~F, rad, bb, hr, hb, box, hg, x1, x2, h1, h2, lam, ms, hm0, es, eqok_tl(~F, bb, lam, ms, e, es, hq), cnt, lo))

# The Jacobian at a point
# -----------------------

# the Jacobian is the slope matrix from a point to itself
def jac_smat(~F: O.OField, +x: M.Vec(~F), eqs: List<&2, E.QExpr>, +cnt: Nat, +lo: Nat) -> {DV.jac(~F, x, eqs, ST.iota(cnt, lo)) == CP.smat(~F, x, x, eqs, cnt, lo) : M.Mat(~F)}:
  match eqs:
    case Nil{}:
      {==}
    case Con{+e, +es}:
      %BP.srange_jrow(~F, x, e, cnt, lo) : {Con{_, DV.jac(~F, x, es, ST.iota(cnt, lo))} == CP.smat(~F, x, x, Con{e, es}, cnt, lo) : M.Mat(~F)}
      %Equal.sym(M.Mat(~F), DV.jac(~F, x, es, ST.iota(cnt, lo)), CP.smat(~F, x, x, es, cnt, lo), jac_smat(~F, x, es, cnt, lo)) : {Con{SL.srange(~F, x, x, e, cnt, lo), _} == CP.smat(~F, x, x, Con{e, es}, cnt, lo) : M.Mat(~F)}
      {==}

def nrows_jac(~F: O.OField, +x: M.Vec(~F), eqs: List<&2, E.QExpr>, +us: List<&2, Nat>) -> {GJ.nrows(~F, DV.jac(~F, x, eqs, us)) == CK.eqlen(eqs) : Nat}:
  match eqs:
    case Nil{}:
      {==}
    case Con{e, es}:
      %Equal.sym(Nat, GJ.nrows(~F, DV.jac(~F, x, es, us)), CK.eqlen(es), nrows_jac(~F, x, es, us)) : {1n+_ == 1n+CK.eqlen(es) : Nat}
      {==}

def len_jrow(~F: O.OField, +x: M.Vec(~F), +e: E.QExpr, us: List<&2, Nat>) -> {M.len(~F, DV.jrow(~F, x, e, us)) == DV.nlen(us) : Nat}:
  match us:
    case Nil{}:
      {==}
    case Con{u, t}:
      %Equal.sym(Nat, M.len(~F, DV.jrow(~F, x, e, t)), DV.nlen(t), len_jrow(~F, x, e, t)) : {1n+_ == 1n+DV.nlen(t) : Nat}
      {==}

def nlen_iota(n: Nat, +k: Nat) -> {DV.nlen(ST.iota(n, k)) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      %Equal.sym(Nat, DV.nlen(ST.iota(m, 1n+k)), m, nlen_iota(m, 1n+k)) : {1n+_ == 1n+m : Nat}
      {==}

# row i < (number of equations) of the Jacobian has cnt entries
def len_mrow_jac(~F: O.OField, +x: M.Vec(~F), eqs: List<&2, E.QExpr>, +cnt: Nat, +lo: Nat, i: Nat, hi: {KA.natle(1n+i, CK.eqlen(eqs)) == True{} : Bool}) -> {M.len(~F, DV.mrow(~F, DV.jac(~F, x, eqs, ST.iota(cnt, lo)), i)) == cnt : Nat}:
  match eqs i:
    case Nil{} i:
      FO.absurd({M.len(~F, DV.mrow(~F, DV.jac(~F, x, Nil{}, ST.iota(cnt, lo)), i)) == cnt : Nat}, KA.ft(hi))
    case Con{+e, es} 0n:
      Equal.trans(Nat, M.len(~F, DV.jrow(~F, x, e, ST.iota(cnt, lo))), DV.nlen(ST.iota(cnt, lo)), cnt, len_jrow(~F, x, e, ST.iota(cnt, lo)), nlen_iota(cnt, lo))
    case Con{+e, es} 1n+j:
      len_mrow_jac(~F, x, es, cnt, lo, j, hi)

def le_eq_r(+a: Nat, +b: Nat, +c: Nat, e: {b == c : Nat}, h: {KA.natle(a, b) == True{} : Bool}) -> {KA.natle(a, c) == True{} : Bool}:
  %e : {KA.natle(a, _) == True{} : Bool}
  h

# every row of the n x n Jacobian has n entries
def rows_jac(~F: O.OField, +x: M.Vec(~F), +eqs: List<&2, E.QExpr>, +n: Nat, +hn: {CK.eqlen(eqs) == n : Nat}) -> GJ.All(~(i => GJ.roww(~F, DV.jac(~F, x, eqs, ST.iota(n, 0n)), n, i)), n):
  GJ.all_mk(~n, ~(i => GJ.roww(~F, DV.jac(~F, x, eqs, ST.iota(n, 0n)), n, i)), ~(i => hi => len_mrow_jac(~F, x, eqs, n, 0n, i, le_eq_r(1n+i, n, CK.eqlen(eqs), Equal.sym(Nat, CK.eqlen(eqs), n, hn), hi))), n, GJ.le_refl(n))

def nrows_jacn(~F: O.OField, +x: M.Vec(~F), +eqs: List<&2, E.QExpr>, +n: Nat, +hn: {CK.eqlen(eqs) == n : Nat}) -> {GJ.nrows(~F, DV.jac(~F, x, eqs, ST.iota(n, 0n))) == n : Nat}:
  Equal.trans(Nat, GJ.nrows(~F, DV.jac(~F, x, eqs, ST.iota(n, 0n))), CK.eqlen(eqs), n, nrows_jac(~F, x, eqs, ST.iota(n, 0n)), hn)

# the Jacobian at a point of the box: entries at most ms, rows summing to n ms
def jac_maj(~F: O.OField, +rad: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rad), +hb: O.le(~F, O.zero(F), bb), +xs: M.Vec(~F), +hg: BP.gbox(~BP.fnum(~F), ~F, ~BP.femb(~F), rad, bb, fbx(~F, xs, rad)), +x: M.Vec(~F), +hx: KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), x, fbx(~F, xs, rad)), +lam: O.C(F), +ms: O.C(F), +hm0: O.le(~F, O.zero(F), ms), +eqs: List<&2, E.QExpr>, +hq: eqok(~F, bb, lam, ms, eqs), +cnt: Nat, +lo: Nat) -> M.Both(DG.mall(~F, DV.jac(~F, x, eqs, ST.iota(cnt, lo)), ms), NP.rowsle(~F, DV.jac(~F, x, eqs, ST.iota(cnt, lo)), cnt, O.mul(F, FR.ofn(~F, cnt), ms))):
  %Equal.sym(M.Mat(~F), DV.jac(~F, x, eqs, ST.iota(cnt, lo)), CP.smat(~F, x, x, eqs, cnt, lo), jac_smat(~F, x, eqs, cnt, lo)) : M.Both(DG.mall(~F, _, ms), NP.rowsle(~F, _, cnt, O.mul(F, FR.ofn(~F, cnt), ms)))
  smat_maj(~F, rad, bb, hr, hb, fbx(~F, xs, rad), hg, x, x, hx, hx, lam, ms, hm0, eqs, hq, cnt, lo)

def both_l(-A: Data, -B: Data, h: M.Both(A, B)) -> A:
  (a, b) = h
  a

def both_r(-A: Data, -B: Data, h: M.Both(A, B)) -> B:
  (a, b) = h
  b

# |J(x) - J(xs)| <= n lam rad for x in the box around xs
def jac_lip(~F: O.OField, +rad: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rad), +hb: O.le(~F, O.zero(F), bb), +xs: M.Vec(~F), +hg: BP.gbox(~BP.fnum(~F), ~F, ~BP.femb(~F), rad, bb, fbx(~F, xs, rad)), +x: M.Vec(~F), +hx: KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), x, fbx(~F, xs, rad)), +lam: O.C(F), +ms: O.C(F), +hl0: O.le(~F, O.zero(F), lam), +eqs: List<&2, E.QExpr>, +hq: eqok(~F, bb, lam, ms, eqs), +cnt: Nat, +lo: Nat) -> O.le(~F, NP.mnorm(~F, M.madd(~F, DV.jac(~F, x, eqs, ST.iota(cnt, lo)), M.mneg(~F, DV.jac(~F, xs, eqs, ST.iota(cnt, lo)))), cnt), O.mul(F, FR.ofn(~F, cnt), O.mul(F, lam, rad))):
  %Equal.sym(M.Mat(~F), DV.jac(~F, x, eqs, ST.iota(cnt, lo)), CP.smat(~F, x, x, eqs, cnt, lo), jac_smat(~F, x, eqs, cnt, lo)) : O.le(~F, NP.mnorm(~F, M.madd(~F, _, M.mneg(~F, DV.jac(~F, xs, eqs, ST.iota(cnt, lo)))), cnt), O.mul(F, FR.ofn(~F, cnt), O.mul(F, lam, rad)))
  %cen_fbx(~F, xs, rad) : O.le(~F, NP.mnorm(~F, M.madd(~F, CP.smat(~F, x, x, eqs, cnt, lo), M.mneg(~F, DV.jac(~F, _, eqs, ST.iota(cnt, lo)))), cnt), O.mul(F, FR.ofn(~F, cnt), O.mul(F, lam, rad)))
  smat_lip_mn(~F, rad, bb, hr, hb, fbx(~F, xs, rad), hg, x, x, hx, hx, lam, ms, hl0, eqs, hq, cnt, lo)

# a point of the box keeps the Jacobian invertible, with twice the norm
def invb_at(~F: O.OField, +n: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +rad: O.C(F), +bb: O.C(F), +hr: O.le(~F, O.zero(F), rad), +hb: O.le(~F, O.zero(F), bb), +xs: M.Vec(~F), +hg: BP.gbox(~BP.fnum(~F), ~F, ~BP.femb(~F), rad, bb, fbx(~F, xs, rad)), +x: M.Vec(~F), +hx: KB.inbox(~BP.fnum(~F), ~F, ~BP.femb(~F), x, fbx(~F, xs, rad)), +lam: O.C(F), +ms: O.C(F), +hl0: O.le(~F, O.zero(F), lam), +hq: eqok(~F, bb, lam, ms, eqs), +b: O.C(F), +hJ: NP.InvB(~F, DV.jac(~F, xs, eqs, ST.iota(n, 0n)), n, b), +hbd: O.le(~F, O.add(F, O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rad))), O.mul(F, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rad)))), O.one(F))) -> NP.InvB(~F, DV.jac(~F, x, eqs, ST.iota(n, 0n)), n, O.add(F, b, b)):
  NP.pert(~F, DV.jac(~F, xs, eqs, ST.iota(n, 0n)), DV.jac(~F, x, eqs, ST.iota(n, 0n)), n, b, O.mul(F, FR.ofn(~F, n), O.mul(F, lam, rad)), hJ, nrows_jacn(~F, xs, eqs, n, hn), nrows_jacn(~F, x, eqs, n, hn), rows_jac(~F, x, eqs, n, hn),
    jac_lip(~F, rad, bb, hr, hb, xs, hg, x, hx, lam, ms, hl0, eqs, hq, n, 0n), hbd)

# Elimination at a point
# ----------------------

# C4's bound on I - A J at w bits, for g and b
def epsa(~F: O.OField, +n: Nat, +g: O.C(F), +b: O.C(F), +w: Nat) -> O.C(F):
  O.add(F, O.mul(F, DG.kd(~F, DG.kst(~F, n, g, b, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, DG.kp(~F, DG.kst(~F, n, g, b, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})))

def epsa_nn(~F: O.OField, +n: Nat, +g: O.C(F), +b: O.C(F), +w: Nat, +hg: O.le(~F, O.zero(F), g), +hb: O.le(~F, O.zero(F), b)) -> O.le(~F, O.zero(F), epsa(~F, n, g, b, w)):
  +k = DG.kst_nn(~F, n, g, b, hg, hb, n)
  FO.nonneg_add(~F, O.mul(F, DG.kd(~F, DG.kst(~F, n, g, b, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})), O.mul(F, DG.kp(~F, DG.kst(~F, n, g, b, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w})),
    FO.mul_nonneg(~F, DG.kd(~F, DG.kst(~F, n, g, b, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), DG.knn_d(~F, DG.kst(~F, n, g, b, n), k), DG.u_nn(~F, w)),
    FO.mul_nonneg(~F, DG.kp(~F, DG.kst(~F, n, g, b, n)), M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), DG.knn_p(~F, DG.kst(~F, n, g, b, n), k), DG.u_nn(~F, w)))

# u acoef <= 1 for every column (C4's smallness)
def small(~F: O.OField, +n: Nat, +g: O.C(F), +b: O.C(F), +w: Nat) -> Data:
  GJ.All(~(q => O.le(~F, O.mul(F, M.ofd(~F, S.D{S.Zpos{S.XH{}}, w}), DG.acoef(~F, n, b, q, DG.kst(~F, n, g, b, q))), O.one(F))), n)

# the solver's elimination at the dyadic point env
def elim_at(~F: O.OField, ~H: N.Emb<KI.dnum(), F>, +n: Nat, +w: Nat, +eqs: List<&2, E.QExpr>, +hn: {CK.eqlen(eqs) == n : Nat}, +hh: {CK.allheld(~KI.dnum(), eqs) == True{} : Bool}, +env: List<&2, S.D>, +g: O.C(F), +b: O.C(F), +hg: O.le(~F, O.zero(F), g), +hb: O.le(~F, O.zero(F), b), +hJ: NP.InvB(~F, DV.jac(~F, M.ofdv(~F, env), eqs, ST.iota(n, 0n)), n, b), +hj: DG.mall(~F, DV.jac(~F, M.ofdv(~F, env), eqs, ST.iota(n, 0n)), g), +hsm: small(~F, n, g, b, w)) -> DG.dinv_res(~F, n, DV.jac(~F, M.ofdv(~F, env), eqs, ST.iota(n, 0n)), epsa(~F, n, g, b, w), NU.dinverse(n, w, NU.jac(eqs, n, env))):
  %djac_ofd(~F, ~H, eqs, n, env, hh) : DG.dinv_res(~F, n, _, epsa(~F, n, g, b, w), NU.dinverse(n, w, NU.jac(eqs, n, env)))
  DG.dinverse_ok(~F, n, w, NU.jac(eqs, n, env), g, b,
    (%Equal.sym(M.Mat(~F), M.ofdm(~F, NU.jac(eqs, n, env)), DV.jac(~F, M.ofdv(~F, env), eqs, ST.iota(n, 0n)), djac_ofd(~F, ~H, eqs, n, env, hh)) : GJ.All(~(i => GJ.roww(~F, _, n, i)), n)
      rows_jac(~F, M.ofdv(~F, env), eqs, n, hn)),
    (%Equal.sym(M.Mat(~F), M.ofdm(~F, NU.jac(eqs, n, env)), DV.jac(~F, M.ofdv(~F, env), eqs, ST.iota(n, 0n)), djac_ofd(~F, ~H, eqs, n, env, hh)) : {GJ.nrows(~F, _) == n : Nat}
      nrows_jacn(~F, M.ofdv(~F, env), eqs, n, hn)),
    (%Equal.sym(M.Mat(~F), M.ofdm(~F, NU.jac(eqs, n, env)), DV.jac(~F, M.ofdv(~F, env), eqs, ST.iota(n, 0n)), djac_ofd(~F, ~H, eqs, n, env, hh)) : NP.InvB(~F, _, n, b)
      hJ),
    (%Equal.sym(M.Mat(~F), M.ofdm(~F, NU.jac(eqs, n, env)), DV.jac(~F, M.ofdv(~F, env), eqs, ST.iota(n, 0n)), djac_ofd(~F, ~H, eqs, n, env, hh)) : DG.mall(~F, _, g)
      hj),
    hg, hb, hsm)

# The checker's comparisons are complete
# --------------------------------------
# In any K: when H a <= H b in F, K's comparison cannot say GT (the
# embedding's comparisons are sound and F is ordered), so kle is True;
# likewise klt from H a < H b. So an inequality proved in F passes the
# checker.

def cmp_gt(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), +b: N.NC(K), e: {N.ncmp(K, a, b) == GT{} : Cmp}) -> O.lt(F, N.emap(K, F, H, b), N.emap(K, F, H, a)):
  %e : N.cmeans(F, _, N.emap(K, F, H, a), N.emap(K, F, H, b))
  N.e_cmp(K, F, H)(a)(b)

def cmp_eq(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), +b: N.NC(K), e: {N.ncmp(K, a, b) == EQ{} : Cmp}) -> {N.emap(K, F, H, a) == N.emap(K, F, H, b) : O.C(F)}:
  %e : N.cmeans(F, _, N.emap(K, F, H, a), N.emap(K, F, H, b))
  N.e_cmp(K, F, H)(a)(b)

def kle_of.go(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), +b: N.NC(K), c: Cmp, e: {N.ncmp(K, a, b) == c : Cmp}, h: O.le(~F, N.emap(K, F, H, a), N.emap(K, F, H, b))) -> {KA.kle.go(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      FO.absurd({KA.kle.go(GT{}) == True{} : Bool}, RL.le_lt_absurd(~F, N.emap(K, F, H, a), N.emap(K, F, H, b), h, cmp_gt(~K, ~F, ~H, a, b, e)))

def kle_of(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), +b: N.NC(K), h: O.le(~F, N.emap(K, F, H, a), N.emap(K, F, H, b))) -> {KA.kle(~K, a, b) == True{} : Bool}:
  kle_of.go(~K, ~F, ~H, a, b, N.ncmp(K, a, b), {==}, h)

def lt_self(~F: O.OField, +x: O.C(F), +y: O.C(F), e: {x == y : O.C(F)}, h: O.lt(F, x, y)) -> Empty:
  O.lt_irrefl(F)(x)((%Equal.sym(O.C(F), x, y, e) : O.lt(F, x, _)
    h))

def klt_of.go(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), +b: N.NC(K), c: Cmp, e: {N.ncmp(K, a, b) == c : Cmp}, +h: O.lt(F, N.emap(K, F, H, a), N.emap(K, F, H, b))) -> {KA.klt.go(c) == True{} : Bool}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      FO.absurd({KA.klt.go(EQ{}) == True{} : Bool}, lt_self(~F, N.emap(K, F, H, a), N.emap(K, F, H, b), cmp_eq(~K, ~F, ~H, a, b, e), h))
    case GT{}:
      FO.absurd({KA.klt.go(GT{}) == True{} : Bool}, O.lt_irrefl(F)(N.emap(K, F, H, a))(O.lt_trans(F)(N.emap(K, F, H, a))(N.emap(K, F, H, b))(N.emap(K, F, H, a))(h)(cmp_gt(~K, ~F, ~H, a, b, e))))

def klt_of(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), +b: N.NC(K), +h: O.lt(F, N.emap(K, F, H, a), N.emap(K, F, H, b))) -> {KA.klt(~K, a, b) == True{} : Bool}:
  klt_of.go(~K, ~F, ~H, a, b, N.ncmp(K, a, b), {==}, h)

def le_zl(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +b: N.NC(K), h: O.le(~F, O.zero(F), N.emap(K, F, H, b))) -> O.le(~F, N.emap(K, F, H, N.nzero(K)), N.emap(K, F, H, b)):
  %Equal.sym(O.C(F), N.emap(K, F, H, N.nzero(K)), O.zero(F), N.e_zero(K, F, H)) : O.le(~F, _, N.emap(K, F, H, b))
  h

def le_zr(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), h: O.le(~F, N.emap(K, F, H, a), O.zero(F))) -> O.le(~F, N.emap(K, F, H, a), N.emap(K, F, H, N.nzero(K))):
  %Equal.sym(O.C(F), N.emap(K, F, H, N.nzero(K)), O.zero(F), N.e_zero(K, F, H)) : O.le(~F, N.emap(K, F, H, a), _)
  h

def band_t(+a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {KA.band(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {KA.band(_, b) == True{} : Bool}
  hb

# entrywise H u <= H w (zeros past each end) passes kvle
def kvle_of(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, u: N.KVec(~K), w: N.KVec(~K), h: FV.rle(~F, N.ofkv(~K, ~F, ~H, u), N.ofkv(~K, ~F, ~H, w))) -> {KA.kvle(~K, u, w) == True{} : Bool}:
  match u w:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+b, +ws}:
      (h1, h2) = h
      band_t(KA.kle(~K, N.nzero(K), b), KA.kvle(~K, Nil{}, ws), kle_of(~K, ~F, ~H, N.nzero(K), b, le_zl(~K, ~F, ~H, b, h1)), kvle_of(~K, ~F, ~H, Nil{}, ws, h2))
    case Con{+a, +us} Nil{}:
      (h1, h2) = h
      band_t(KA.kle(~K, a, N.nzero(K)), KA.kvle(~K, us, Nil{}), kle_of(~K, ~F, ~H, a, N.nzero(K), le_zr(~K, ~F, ~H, a, h1)), kvle_of(~K, ~F, ~H, us, Nil{}, h2))
    case Con{+a, +us} Con{+b, +ws}:
      (h1, h2) = h
      band_t(KA.kle(~K, a, b), KA.kvle(~K, us, ws), kle_of(~K, ~F, ~H, a, b, h1), kvle_of(~K, ~F, ~H, us, ws, h2))

def lt_one(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), h: O.lt(F, N.emap(K, F, H, a), O.one(F))) -> O.lt(F, N.emap(K, F, H, a), N.emap(K, F, H, N.none(K))):
  %Equal.sym(O.C(F), N.emap(K, F, H, N.none(K)), O.one(F), N.e_one(K, F, H)) : O.lt(F, N.emap(K, F, H, a), _)
  h

# n entries, each below 1 in F, pass kvlt against kones
def kvlt_ones_of(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, u: N.KVec(~K), n: Nat, hl: {KA.klen(~K, u) == n : Nat}, h: FV.vlt_all(~F, N.ofkv(~K, ~F, ~H, u), O.one(F))) -> {KA.kvlt(~K, u, KA.kones(~K, n)) == True{} : Bool}:
  match u n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n++k:
      FO.absurd({KA.kvlt(~K, Nil{}, KA.kones(~K, 1n+k)) == True{} : Bool}, FV.zero_ne(k, hl))
    case Con{+a, +us} 0n:
      FO.absurd({KA.kvlt(~K, Con{a, us}, KA.kones(~K, 0n)) == True{} : Bool}, FV.succ_ne(KA.klen(~K, us), hl))
    case Con{+a, +us} 1n++k:
      (h1, h2) = h
      band_t(KA.klt(~K, a, N.none(K)), KA.kvlt(~K, us, KA.kones(~K, k)), klt_of(~K, ~F, ~H, a, N.none(K), lt_one(~K, ~F, ~H, a, h1)), kvlt_ones_of(~K, ~F, ~H, us, k, FV.succ_inj(KA.klen(~K, us), k, hl), h2))
