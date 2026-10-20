# bend-cad: a nonzero residual makes its equation independent of the basis
# (PLAN-sk13a S2): no constant combination of B is identically e (indep),
# the spec's NotDerivable.
#
# The proof is a dual certificate. phi(ms, cs, p) = sum_t cs_t p[ms_t] is
# a functional on coefficient vectors over finitely many monomials. With
# mu a monomial where the residual r is nonzero (its pivot), back-
# substitution through the rows, newest first, gives weights
# (ycoefs) under which phi kills every row (y_allz), while phi(r) is r's
# coefficient at mu, not 0 (phi_res). The rows being triangular in the
# basis (rinv), phi then kills every basis equation (tri), but not e (r is
# bt e plus a combination of B). An identity e = sum l_k B_k would make
# phi(e) the same combination of phi(B_k), all 0 (psi). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/solve.bend as SV
import ./nat.bend as N
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./qemb.bend as QE
import ./qfield.bend as QF
import ./qnorm.bend as QN
import ./zring.bend as R
import ./zlaws.bend as ZL
import ./zord.bend as ZO
import ./karith.bend as KA
import ./redpoly.bend as RP
import ./identpf.bend as ID
import ./elim.bend as EL
import ./coefpf.bend as CF
import ./elimpf.bend as EP

def absurd(-A: Type, x: Empty) -> A:
  match x:

# The functional
# --------------

def phi(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +p: List<&2, R.ZTerm>) -> O.C(F):
  match ms cs:
    case Nil{} Nil{}:
      O.zero(F)
    case Nil{} Con{c, ct}:
      O.zero(F)
    case Con{m, mt} Nil{}:
      O.zero(F)
    case Con{m, mt} Con{c, ct}:
      O.add(F, O.mul(F, c, O.ofz(~F, EL.cz(m, p))), phi(~F, mt, ct, p))

def zz(~F: O.OField) -> {O.add(F, O.zero(F), O.zero(F)) == O.zero(F) : O.C(F)}:
  Equal.sym(O.C(F), O.zero(F), O.add(F, O.zero(F), O.zero(F)), FL.add_zero(~F, O.zero(F)))

def phi_padd(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +p: List<&2, R.ZTerm>, +q: List<&2, R.ZTerm>)
  -> {O.add(F, phi(~F, ms, cs, p), phi(~F, ms, cs, q)) == phi(~F, ms, cs, R.padd(p, q)) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      zz(~F)
    case Nil{} Con{c, ct}:
      zz(~F)
    case Con{m, mt} Nil{}:
      zz(~F)
    case Con{+m, +mt} Con{+c, +ct}:
      %CF.cz_padd(m, p, q) : {O.add(F, phi(~F, Con{m, mt}, Con{c, ct}, p), phi(~F, Con{m, mt}, Con{c, ct}, q)) == O.add(F, O.mul(F, c, O.ofz(~F, _)), phi(~F, mt, ct, R.padd(p, q))) : O.C(F)}
      %FR.ofz_add(~F, EL.cz(m, p), EL.cz(m, q))
        : {O.add(F, phi(~F, Con{m, mt}, Con{c, ct}, p), phi(~F, Con{m, mt}, Con{c, ct}, q)) == O.add(F, O.mul(F, c, _), phi(~F, mt, ct, R.padd(p, q))) : O.C(F)}
      %phi_padd(~F, mt, ct, p, q) : {O.add(F, phi(~F, Con{m, mt}, Con{c, ct}, p), phi(~F, Con{m, mt}, Con{c, ct}, q)) == O.add(F, O.mul(F, c, O.add(F, O.ofz(~F, EL.cz(m, p)), O.ofz(~F, EL.cz(m, q)))), _) : O.C(F)}
      FR.fring_eq(~F, [c, O.ofz(~F, EL.cz(m, p)), O.ofz(~F, EL.cz(m, q)), phi(~F, mt, ct, p), phi(~F, mt, ct, q)],
        E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{3n}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{4n}}},
        E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}, E.ZAdd{E.ZVar{3n}, E.ZVar{4n}}}, {==})

def phi_pscale0(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +k: S.Z, +p: List<&2, R.ZTerm>)
  -> {O.mul(F, O.ofz(~F, k), phi(~F, ms, cs, p)) == phi(~F, ms, cs, R.pscale(k, Nil{}, p)) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      Equal.sym(O.C(F), O.zero(F), O.mul(F, O.ofz(~F, k), O.zero(F)), FL.mul_zero(~F, O.ofz(~F, k)))
    case Nil{} Con{c, ct}:
      Equal.sym(O.C(F), O.zero(F), O.mul(F, O.ofz(~F, k), O.zero(F)), FL.mul_zero(~F, O.ofz(~F, k)))
    case Con{m, mt} Nil{}:
      Equal.sym(O.C(F), O.zero(F), O.mul(F, O.ofz(~F, k), O.zero(F)), FL.mul_zero(~F, O.ofz(~F, k)))
    case Con{+m, +mt} Con{+c, +ct}:
      %CF.cz_pscale0(m, k, p) : {O.mul(F, O.ofz(~F, k), phi(~F, Con{m, mt}, Con{c, ct}, p)) == O.add(F, O.mul(F, c, O.ofz(~F, _)), phi(~F, mt, ct, R.pscale(k, Nil{}, p))) : O.C(F)}
      %FR.ofz_mul(~F, k, EL.cz(m, p)) : {O.mul(F, O.ofz(~F, k), phi(~F, Con{m, mt}, Con{c, ct}, p)) == O.add(F, O.mul(F, c, _), phi(~F, mt, ct, R.pscale(k, Nil{}, p))) : O.C(F)}
      %phi_pscale0(~F, mt, ct, k, p) : {O.mul(F, O.ofz(~F, k), phi(~F, Con{m, mt}, Con{c, ct}, p)) == O.add(F, O.mul(F, c, O.mul(F, O.ofz(~F, k), O.ofz(~F, EL.cz(m, p)))), _) : O.C(F)}
      FR.fring_eq(~F, [c, O.ofz(~F, k), O.ofz(~F, EL.cz(m, p)), phi(~F, mt, ct, p)],
        E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{3n}}},
        E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, {==})

# phi reads coefficients only
def phi_same(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +p: List<&2, R.ZTerm>, +q: List<&2, R.ZTerm>, +hs: {EP.same(p, q) == True{} : Bool})
  -> {phi(~F, ms, cs, p) == phi(~F, ms, cs, q) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{c, ct}:
      {==}
    case Con{m, mt} Nil{}:
      {==}
    case Con{+m, +mt} Con{+c, +ct}:
      %Equal.sym(S.Z, EL.cz(m, p), EL.cz(m, q), EP.same_cz(p, q, hs, m)) : {O.add(F, O.mul(F, c, O.ofz(~F, _)), phi(~F, mt, ct, p)) == phi(~F, Con{m, mt}, Con{c, ct}, q) : O.C(F)}
      %Equal.sym(O.C(F), phi(~F, mt, ct, p), phi(~F, mt, ct, q), phi_same(~F, mt, ct, p, q, hs)) : {O.add(F, O.mul(F, c, O.ofz(~F, EL.cz(m, q))), _) == phi(~F, Con{m, mt}, Con{c, ct}, q) : O.C(F)}
      {==}

def phi_nil(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>) -> {O.zero(F) == phi(~F, ms, cs, Nil{}) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{c, ct}:
      {==}
    case Con{m, mt} Nil{}:
      {==}
    case Con{m, mt} Con{+c, ct}:
      %FL.mul_zero(~F, c) : {O.zero(F) == O.add(F, _, phi(~F, mt, ct, Nil{})) : O.C(F)}
      %phi_nil(~F, mt, ct) : {O.zero(F) == O.add(F, O.zero(F), _) : O.C(F)}
      Equal.sym(O.C(F), O.add(F, O.zero(F), O.zero(F)), O.zero(F), zz(~F))

# phi of the basis' combination cb: sum_k cb_k phi(NE(B_k))
def fphis(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, cb: List<&2, S.Z>, B: List<&2, E.QExpr>) -> O.C(F):
  match cb B:
    case Nil{} Nil{}:
      O.zero(F)
    case Nil{} Con{b, bs}:
      O.zero(F)
    case Con{c, ct} Nil{}:
      O.zero(F)
    case Con{c, ct} Con{b, bs}:
      O.add(F, O.mul(F, O.ofz(~F, c), phi(~F, ms, cs, EP.NE(b))), fphis(~F, ms, cs, ct, bs))

def phi_comb(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, cb: List<&2, S.Z>, B: List<&2, E.QExpr>) -> {fphis(~F, ms, cs, cb, B) == phi(~F, ms, cs, EP.comb(cb, B)) : O.C(F)}:
  match cb B:
    case Nil{} Nil{}:
      phi_nil(~F, ms, cs)
    case Nil{} Con{b, bs}:
      phi_nil(~F, ms, cs)
    case Con{c, ct} Nil{}:
      phi_nil(~F, ms, cs)
    case Con{+c, +ct} Con{+b, +bs}:
      %phi_padd(~F, ms, cs, R.pscale(c, Nil{}, EP.NE(b)), EP.comb(ct, bs)) : {fphis(~F, ms, cs, Con{c, ct}, Con{b, bs}) == _ : O.C(F)}
      %phi_pscale0(~F, ms, cs, c, EP.NE(b)) : {fphis(~F, ms, cs, Con{c, ct}, Con{b, bs}) == O.add(F, _, phi(~F, ms, cs, EP.comb(ct, bs))) : O.C(F)}
      %phi_comb(~F, ms, cs, ct, bs) : {fphis(~F, ms, cs, Con{c, ct}, Con{b, bs}) == O.add(F, O.mul(F, O.ofz(~F, c), phi(~F, ms, cs, EP.NE(b))), _) : O.C(F)}
      {==}

def phi_comb2(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, +bt: S.Pos, +e: E.QExpr, +cb: List<&2, S.Z>, +B: List<&2, E.QExpr>)
  -> {O.add(F, O.mul(F, O.ofp(~F, bt), phi(~F, ms, cs, EP.NE(e))), fphis(~F, ms, cs, cb, B)) == phi(~F, ms, cs, EP.comb2(bt, e, cb, B)) : O.C(F)}:
  %phi_padd(~F, ms, cs, R.pscale(S.Zpos{bt}, Nil{}, EP.NE(e)), EP.comb(cb, B)) : {O.add(F, O.mul(F, O.ofp(~F, bt), phi(~F, ms, cs, EP.NE(e))), fphis(~F, ms, cs, cb, B)) == _ : O.C(F)}
  %phi_pscale0(~F, ms, cs, S.Zpos{bt}, EP.NE(e)) : {O.add(F, O.mul(F, O.ofp(~F, bt), phi(~F, ms, cs, EP.NE(e))), fphis(~F, ms, cs, cb, B)) == O.add(F, _, phi(~F, ms, cs, EP.comb(cb, B))) : O.C(F)}
  %phi_comb(~F, ms, cs, cb, B) : {O.add(F, O.mul(F, O.ofp(~F, bt), phi(~F, ms, cs, EP.NE(e))), fphis(~F, ms, cs, cb, B)) == O.add(F, O.mul(F, O.ofp(~F, bt), phi(~F, ms, cs, EP.NE(e))), _) : O.C(F)}
  {==}

# Back-substitution
# -----------------

def ymons(rows: List<&2, EL.Row>, +mu: List<&2, Nat>) -> List<&2, List<&2, Nat>>:
  match rows:
    case Nil{}:
      Con{mu, Nil{}}
    case Con{row, t}:
      Con{EP.rowpv(row), ymons(t, mu)}

# the weights, newest row first: each row's pivot weight makes phi kill it
def ycoefs(~F: O.OField, rows: List<&2, EL.Row>, +mu: List<&2, Nat>) -> List<&2, O.C(F)>:
  match rows:
    case Nil{}:
      Con{O.one(F), Nil{}}
    case Con{+row, +t}:
      Con{O.mul(F, O.neg(F, phi(~F, ymons(t, mu), ycoefs(~F, t, mu), EP.rowp(row))), O.inv(F, O.ofz(~F, EL.cz(EP.rowpv(row), EP.rowp(row))))), ycoefs(~F, t, mu)}

# phi kills every row
def AllZ(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, rows: List<&2, EL.Row>) -> Data:
  match rows:
    case Nil{}:
      Unit
    case Con{row, t}:
      M.Both({phi(~F, ms, cs, EP.rowp(row)) == O.zero(F) : O.C(F)}, AllZ(~F, ms, cs, t))

# the pivot's weight kills its row
def head_zero(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, +pv: List<&2, Nat>, +p: List<&2, R.ZTerm>, hnz: {RP.nz(EL.cz(pv, p)) == True{} : Bool})
  -> {phi(~F, Con{pv, ms}, Con{O.mul(F, O.neg(F, phi(~F, ms, cs, p)), O.inv(F, O.ofz(~F, EL.cz(pv, p)))), cs}, p) == O.zero(F) : O.C(F)}:
  FO.cert1(~F, phi(~F, Con{pv, ms}, Con{O.mul(F, O.neg(F, phi(~F, ms, cs, p)), O.inv(F, O.ofz(~F, EL.cz(pv, p)))), cs}, p),
    O.neg(F, phi(~F, ms, cs, p)), O.sub(~F, O.mul(F, O.ofz(~F, EL.cz(pv, p)), O.inv(F, O.ofz(~F, EL.cz(pv, p)))), O.one(F)),
    FR.fring_eq(~F, [phi(~F, ms, cs, p), O.inv(F, O.ofz(~F, EL.cz(pv, p))), O.ofz(~F, EL.cz(pv, p))],
      E.ZAdd{E.ZMul{E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZVar{0n}},
      E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{1n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}),
    FO.inv_rel(~F, O.ofz(~F, EL.cz(pv, p)), ez => ID.ofz_nz(~F, EL.cz(pv, p), hnz, ez)))

# a later row, 0 at the pivot, stays killed whatever the pivot's weight
def ext_zero(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, +pv: List<&2, Nat>, +y: O.C(F), +p: List<&2, R.ZTerm>,
  h0: {EP.iszero(EL.cz(pv, p)) == True{} : Bool}, h: {phi(~F, ms, cs, p) == O.zero(F) : O.C(F)}) -> {phi(~F, Con{pv, ms}, Con{y, cs}, p) == O.zero(F) : O.C(F)}:
  %Equal.sym(S.Z, EL.cz(pv, p), S.Z0{}, EP.zero_of(EL.cz(pv, p), h0)) : {O.add(F, O.mul(F, y, O.ofz(~F, _)), phi(~F, ms, cs, p)) == O.zero(F) : O.C(F)}
  %FL.mul_zero(~F, y) : {O.add(F, _, phi(~F, ms, cs, p)) == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), phi(~F, ms, cs, p), O.zero(F), h) : {O.add(F, O.zero(F), _) == O.zero(F) : O.C(F)}
  zz(~F)

def allz_ext(~F: O.OField, rows: List<&2, EL.Row>, +pv: List<&2, Nat>, +y: O.C(F), +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>,
  hz: AllZ(~F, ms, cs, rows), +ha: {EP.zat(pv, rows) == True{} : Bool}) -> AllZ(~F, Con{pv, ms}, Con{y, cs}, rows):
  match rows:
    case Nil{}:
      Unit{}
    case Con{+row, +t}:
      (h1, h2) = hz
      (ext_zero(~F, ms, cs, pv, y, EP.rowp(row), KA.band_l(EP.iszero(EL.cz(pv, EP.rowp(row))), EP.zat(pv, t), ha), h1),
       allz_ext(~F, t, pv, y, ms, cs, h2, KA.band_r(EP.iszero(EL.cz(pv, EP.rowp(row))), EP.zat(pv, t), ha)))

# phi, with the back-substituted weights, kills every row
def y_allz(~F: O.OField, rows: List<&2, EL.Row>, +mu: List<&2, Nat>, +B: List<&2, E.QExpr>, +hok: {EP.allok(B, rows) == True{} : Bool}, +he: {EP.ech(rows) == True{} : Bool})
  -> AllZ(~F, ymons(rows, mu), ycoefs(~F, rows, mu), rows):
  match rows:
    case Nil{}:
      Unit{}
    case Con{EL.Row{+p, +cb, +bt, +pv}, +t}:
      (head_zero(~F, ymons(t, mu), ycoefs(~F, t, mu), pv, p, EP.rowok_nz(B, p, cb, bt, pv, KA.band_l(EP.rowok(B, EL.Row{p, cb, bt, pv}), EP.allok(B, t), hok))),
       allz_ext(~F, t, pv, O.mul(F, O.neg(F, phi(~F, ymons(t, mu), ycoefs(~F, t, mu), p)), O.inv(F, O.ofz(~F, EL.cz(pv, p)))), ymons(t, mu), ycoefs(~F, t, mu),
         y_allz(~F, t, mu, B, KA.band_r(EP.rowok(B, EL.Row{p, cb, bt, pv}), EP.allok(B, t), hok), KA.band_r(EP.zat(pv, t), EP.ech(t), he)),
         KA.band_l(EP.zat(pv, t), EP.ech(t), he)))

# on a polynomial 0 at every pivot, phi is the coefficient at mu
def phi_res(~F: O.OField, rows: List<&2, EL.Row>, +mu: List<&2, Nat>, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +hz: {EP.zp(rows, EL.Res{p, cb, bt}) == True{} : Bool})
  -> {phi(~F, ymons(rows, mu), ycoefs(~F, rows, mu), p) == O.ofz(~F, EL.cz(mu, p)) : O.C(F)}:
  match rows:
    case Nil{}:
      %FL.one_mul(~F, O.ofz(~F, EL.cz(mu, p))) : {O.add(F, _, O.zero(F)) == O.ofz(~F, EL.cz(mu, p)) : O.C(F)}
      Equal.sym(O.C(F), O.ofz(~F, EL.cz(mu, p)), O.add(F, O.ofz(~F, EL.cz(mu, p)), O.zero(F)), FL.add_zero(~F, O.ofz(~F, EL.cz(mu, p))))
    case Con{+row, +t}:
      %Equal.sym(S.Z, EL.cz(EP.rowpv(row), p), S.Z0{}, EP.zero_of(EL.cz(EP.rowpv(row), p), KA.band_l(EP.ZAt(EP.rowpv(row), EL.Res{p, cb, bt}), EP.zp(t, EL.Res{p, cb, bt}), hz)))
        : {O.add(F, O.mul(F, O.mul(F, O.neg(F, phi(~F, ymons(t, mu), ycoefs(~F, t, mu), EP.rowp(row))), O.inv(F, O.ofz(~F, EL.cz(EP.rowpv(row), EP.rowp(row))))), O.ofz(~F, _)), phi(~F, ymons(t, mu), ycoefs(~F, t, mu), p)) == O.ofz(~F, EL.cz(mu, p)) : O.C(F)}
      %FL.mul_zero(~F, O.mul(F, O.neg(F, phi(~F, ymons(t, mu), ycoefs(~F, t, mu), EP.rowp(row))), O.inv(F, O.ofz(~F, EL.cz(EP.rowpv(row), EP.rowp(row))))))
        : {O.add(F, _, phi(~F, ymons(t, mu), ycoefs(~F, t, mu), p)) == O.ofz(~F, EL.cz(mu, p)) : O.C(F)}
      %Equal.sym(O.C(F), phi(~F, ymons(t, mu), ycoefs(~F, t, mu), p), O.ofz(~F, EL.cz(mu, p)), phi_res(~F, t, mu, p, cb, bt, KA.band_r(EP.ZAt(EP.rowpv(row), EL.Res{p, cb, bt}), EP.zp(t, EL.Res{p, cb, bt}), hz)))
        : {O.add(F, O.zero(F), _) == O.ofz(~F, EL.cz(mu, p)) : O.C(F)}
      FL.zero_add(~F, O.ofz(~F, EL.cz(mu, p)))

# Every basis equation is killed
# ------------------------------

# phi kills the first n equations of B
def PZB(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, B: List<&2, E.QExpr>, n: Nat) -> Data:
  match B n:
    case Nil{} 0n:
      Unit
    case Nil{} 1n+k:
      Unit
    case Con{b, bs} 0n:
      Unit
    case Con{b, bs} 1n+k:
      M.Both({phi(~F, ms, cs, EP.NE(b)) == O.zero(F) : O.C(F)}, PZB(~F, ms, cs, bs, k))

def pzb0(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, B: List<&2, E.QExpr>) -> PZB(~F, ms, cs, B, 0n):
  match B:
    case Nil{}:
      Unit{}
    case Con{b, bs}:
      Unit{}

def pzb_snoc(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, B: List<&2, E.QExpr>, j: Nat, h: PZB(~F, ms, cs, B, j),
  hj: {phi(~F, ms, cs, EP.NE(SV.eqat(B, j))) == O.zero(F) : O.C(F)}, hl: {KA.natle(1n+j, SV.neqs(B)) == True{} : Bool}) -> PZB(~F, ms, cs, B, 1n+j):
  match B j:
    case Nil{} 0n:
      absurd(PZB(~F, ms, cs, Nil{}, 1n), KA.ft(hl))
    case Nil{} 1n+i:
      absurd(PZB(~F, ms, cs, Nil{}, 2n+i), KA.ft(hl))
    case Con{b, bs} 0n:
      (hj, pzb0(~F, ms, cs, bs))
    case Con{b, bs} 1n+i:
      (h1, h2) = h
      (h1, pzb_snoc(~F, ms, cs, bs, i, h2, hj, hl))

def fz(~F: O.OField, +a: O.C(F), +x: O.C(F), +y: O.C(F), hx: {x == O.zero(F) : O.C(F)}, hy: {y == O.zero(F) : O.C(F)}) -> {O.add(F, O.mul(F, a, x), y) == O.zero(F) : O.C(F)}:
  %Equal.sym(O.C(F), x, O.zero(F), hx) : {O.add(F, O.mul(F, a, _), y) == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), y, O.zero(F), hy) : {O.add(F, O.mul(F, a, O.zero(F)), _) == O.zero(F) : O.C(F)}
  %FL.mul_zero(~F, a) : {O.add(F, _, O.zero(F)) == O.zero(F) : O.C(F)}
  zz(~F)

# a combination of killed equations is killed
def fphis_zero(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, cb: List<&2, S.Z>, B: List<&2, E.QExpr>, n: Nat, hp: PZB(~F, ms, cs, B, n),
  hl: {KA.natle(EP.vlen(cb), n) == True{} : Bool}) -> {fphis(~F, ms, cs, cb, B) == O.zero(F) : O.C(F)}:
  match cb B n:
    case Nil{} Nil{} n:
      {==}
    case Nil{} Con{b, bs} n:
      {==}
    case Con{c, ct} Nil{} n:
      {==}
    case Con{c, ct} Con{b, bs} 0n:
      absurd({fphis(~F, ms, cs, Con{c, ct}, Con{b, bs}) == O.zero(F) : O.C(F)}, KA.ft(hl))
    case Con{+c, +ct} Con{+b, +bs} 1n+k:
      (h1, h2) = hp
      fz(~F, O.ofz(~F, c), phi(~F, ms, cs, EP.NE(b)), fphis(~F, ms, cs, ct, bs), h1, fphis_zero(~F, ms, cs, ct, bs, k, h2, hl))

# a killed row kills its own equation, its earlier ones being killed
def row_phi(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +e: E.QExpr, +B: List<&2, E.QExpr>,
  +hs: {EP.same(p, EP.comb2(bt, e, cb, B)) == True{} : Bool}, hz: {phi(~F, ms, cs, p) == O.zero(F) : O.C(F)}, hf: {fphis(~F, ms, cs, cb, B) == O.zero(F) : O.C(F)})
  -> {phi(~F, ms, cs, EP.NE(e)) == O.zero(F) : O.C(F)}:
  FO.mul_eq_zero(~F, O.ofp(~F, bt), phi(~F, ms, cs, EP.NE(e)), QE.ofp_ne(~F, bt),
    (%Equal.sym(O.C(F), O.mul(F, O.ofp(~F, bt), phi(~F, ms, cs, EP.NE(e))), O.add(F, O.mul(F, O.ofp(~F, bt), phi(~F, ms, cs, EP.NE(e))), O.zero(F)), FL.add_zero(~F, O.mul(F, O.ofp(~F, bt), phi(~F, ms, cs, EP.NE(e)))))
       : {_ == O.zero(F) : O.C(F)}
     %hf : {O.add(F, O.mul(F, O.ofp(~F, bt), phi(~F, ms, cs, EP.NE(e))), _) == O.zero(F) : O.C(F)}
     %Equal.sym(O.C(F), O.add(F, O.mul(F, O.ofp(~F, bt), phi(~F, ms, cs, EP.NE(e))), fphis(~F, ms, cs, cb, B)), phi(~F, ms, cs, EP.comb2(bt, e, cb, B)), phi_comb2(~F, ms, cs, bt, e, cb, B))
       : {_ == O.zero(F) : O.C(F)}
     %phi_same(~F, ms, cs, p, EP.comb2(bt, e, cb, B), hs) : {_ == O.zero(F) : O.C(F)}
     hz))

# triangular: the rows, killed, kill the basis entries they stand for
def tri(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, +B: List<&2, E.QExpr>, rows: List<&2, EL.Row>, +j: Nat,
  +hr: {EP.rinv(B, rows, j) == True{} : Bool}, hz: AllZ(~F, ms, cs, rows), +hp: PZB(~F, ms, cs, B, j), +hk: {KA.natle(Nat.add(j, EL.rlen(rows)), SV.neqs(B)) == True{} : Bool})
  -> PZB(~F, ms, cs, B, Nat.add(j, EL.rlen(rows))):
  match rows:
    case Nil{}:
      (%N.add_zero(j) : PZB(~F, ms, cs, B, _)
       hp)
    case Con{EL.Row{+p, +cb, +bt, +pv}, +t}:
      (h1, h2) = hz
      +pj = EP.rinv_pos(B, EL.Row{p, cb, bt, pv}, t, j, hr)
      %N.add_succ(j, EL.rlen(t)) : PZB(~F, ms, cs, B, _)
      tri(~F, ms, cs, B, t, 1n+j, EP.rinv_tl(B, EL.Row{p, cb, bt, pv}, t, j, hr), h2,
        pzb_snoc(~F, ms, cs, B, j, hp,
          (%pj : {phi(~F, ms, cs, EP.NE(SV.eqat(B, _))) == O.zero(F) : O.C(F)}
           row_phi(~F, ms, cs, p, cb, bt, SV.eqat(B, EP.vlen(cb)), B, EP.rowok_same(B, p, cb, bt, pv, EP.rinv_ok(B, EL.Row{p, cb, bt, pv}, t, j, hr)), h1,
             fphis_zero(~F, ms, cs, cb, B, j, hp, (%Equal.sym(Nat, EP.vlen(cb), j, pj) : {KA.natle(_, j) == True{} : Bool}
               KA.natle_refl(j))))),
          EP.succ_le(j, EL.rlen(t), SV.neqs(B), hk)),
        EP.succ_shift(j, EL.rlen(t), SV.neqs(B), hk))

# The functional through rational coefficients
# --------------------------------------------

def coefeq(+e1: E.QExpr, +e2: E.QExpr, +hz: {QN.qzero(E.QSub{e1, e2}) == True{} : Bool}, +m: List<&2, Nat>) -> S.Q.eq(CF.coef(e1, m), CF.coef(e2, m)):
  Equal.sym(S.Z, S.Z.mul(EL.cz(m, R.norm(QN.clr(e2))), S.Zpos{QN.den(e1)}), S.Z.mul(EL.cz(m, R.norm(QN.clr(e1))), S.Zpos{QN.den(e2)}),
    ZO.sub_eq(S.Z.mul(EL.cz(m, R.norm(QN.clr(e2))), S.Zpos{QN.den(e1)}), S.Z.mul(EL.cz(m, R.norm(QN.clr(e1))), S.Zpos{QN.den(e2)}),
      CF.coef_zero(e1, e2, m, QN.nil_of(R.norm(QN.clr(E.QSub{e1, e2})), hz))))

def psi(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +e: E.QExpr) -> O.C(F):
  match ms cs:
    case Nil{} Nil{}:
      O.zero(F)
    case Nil{} Con{c, ct}:
      O.zero(F)
    case Con{m, mt} Nil{}:
      O.zero(F)
    case Con{m, mt} Con{c, ct}:
      O.add(F, O.mul(F, c, O.ofq(~F, CF.coef(e, m))), psi(~F, mt, ct, e))

def psi_phi(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +e: E.QExpr) -> {psi(~F, ms, cs, e) == O.mul(F, phi(~F, ms, cs, EP.NE(e)), O.inv(F, O.ofp(~F, QN.den(e)))) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      Equal.sym(O.C(F), O.mul(F, O.zero(F), O.inv(F, O.ofp(~F, QN.den(e)))), O.zero(F), FL.zero_mul(~F, O.inv(F, O.ofp(~F, QN.den(e)))))
    case Nil{} Con{c, ct}:
      Equal.sym(O.C(F), O.mul(F, O.zero(F), O.inv(F, O.ofp(~F, QN.den(e)))), O.zero(F), FL.zero_mul(~F, O.inv(F, O.ofp(~F, QN.den(e)))))
    case Con{m, mt} Nil{}:
      Equal.sym(O.C(F), O.mul(F, O.zero(F), O.inv(F, O.ofp(~F, QN.den(e)))), O.zero(F), FL.zero_mul(~F, O.inv(F, O.ofp(~F, QN.den(e)))))
    case Con{+m, +mt} Con{+c, +ct}:
      %Equal.sym(O.C(F), psi(~F, mt, ct, e), O.mul(F, phi(~F, mt, ct, EP.NE(e)), O.inv(F, O.ofp(~F, QN.den(e)))), psi_phi(~F, mt, ct, e))
        : {O.add(F, O.mul(F, c, O.ofq(~F, CF.coef(e, m))), _) == O.mul(F, phi(~F, Con{m, mt}, Con{c, ct}, EP.NE(e)), O.inv(F, O.ofp(~F, QN.den(e)))) : O.C(F)}
      FR.fring_eq(~F, [c, O.ofz(~F, EL.cz(m, EP.NE(e))), O.inv(F, O.ofp(~F, QN.den(e))), phi(~F, mt, ct, EP.NE(e))],
        E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZMul{E.ZVar{3n}, E.ZVar{2n}}},
        E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{3n}}, E.ZVar{2n}}, {==})

def psum(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +ls: List<&2, S.Q>, +B: List<&2, E.QExpr>) -> O.C(F):
  match ms cs:
    case Nil{} Nil{}:
      O.zero(F)
    case Nil{} Con{c, ct}:
      O.zero(F)
    case Con{m, mt} Nil{}:
      O.zero(F)
    case Con{m, mt} Con{c, ct}:
      O.add(F, O.mul(F, c, O.ofq(~F, CF.qlin(ls, B, m))), psum(~F, mt, ct, ls, B))

# an identity e = lin(ls, B): psi(e) is the same sum over lin's coefficients
def psi_eq(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +e: E.QExpr, +ls: List<&2, S.Q>, +B: List<&2, E.QExpr>, +hz: {QN.qzero(E.QSub{e, SV.lin(ls, B)}) == True{} : Bool})
  -> {psi(~F, ms, cs, e) == psum(~F, ms, cs, ls, B) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{c, ct}:
      {==}
    case Con{m, mt} Nil{}:
      {==}
    case Con{+m, +mt} Con{+c, +ct}:
      %Equal.sym(O.C(F), O.ofq(~F, CF.coef(e, m)), O.ofq(~F, CF.coef(SV.lin(ls, B), m)), QE.ofq_eq(~F, CF.coef(e, m), CF.coef(SV.lin(ls, B), m), coefeq(e, SV.lin(ls, B), hz, m)))
        : {O.add(F, O.mul(F, c, _), psi(~F, mt, ct, e)) == psum(~F, Con{m, mt}, Con{c, ct}, ls, B) : O.C(F)}
      %CF.coef_lin(ls, B, m) : {O.add(F, O.mul(F, c, O.ofq(~F, _)), psi(~F, mt, ct, e)) == psum(~F, Con{m, mt}, Con{c, ct}, ls, B) : O.C(F)}
      %Equal.sym(O.C(F), psi(~F, mt, ct, e), psum(~F, mt, ct, ls, B), psi_eq(~F, mt, ct, e, ls, B, hz))
        : {O.add(F, O.mul(F, c, O.ofq(~F, CF.qlin(ls, B, m))), _) == psum(~F, Con{m, mt}, Con{c, ct}, ls, B) : O.C(F)}
      {==}

def psi_split(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +l: S.Q, +b: E.QExpr, +lt: List<&2, S.Q>, +bs: List<&2, E.QExpr>)
  -> {O.add(F, O.mul(F, O.ofq(~F, l), psi(~F, ms, cs, b)), psum(~F, ms, cs, lt, bs)) == psum(~F, ms, cs, Con{l, lt}, Con{b, bs}) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      %FL.mul_zero(~F, O.ofq(~F, l)) : {O.add(F, _, O.zero(F)) == O.zero(F) : O.C(F)}
      zz(~F)
    case Nil{} Con{c, ct}:
      %FL.mul_zero(~F, O.ofq(~F, l)) : {O.add(F, _, O.zero(F)) == O.zero(F) : O.C(F)}
      zz(~F)
    case Con{m, mt} Nil{}:
      %FL.mul_zero(~F, O.ofq(~F, l)) : {O.add(F, _, O.zero(F)) == O.zero(F) : O.C(F)}
      zz(~F)
    case Con{+m, +mt} Con{+c, +ct}:
      %Equal.sym(O.C(F), O.ofq(~F, S.Q.add(S.Q.mul(l, CF.coef(b, m)), CF.qlin(lt, bs, m))), O.add(F, O.ofq(~F, S.Q.mul(l, CF.coef(b, m))), O.ofq(~F, CF.qlin(lt, bs, m))),
          QE.ofq_add(~F, S.Q.mul(l, CF.coef(b, m)), CF.qlin(lt, bs, m)))
        : {O.add(F, O.mul(F, O.ofq(~F, l), psi(~F, Con{m, mt}, Con{c, ct}, b)), psum(~F, Con{m, mt}, Con{c, ct}, lt, bs)) == O.add(F, O.mul(F, c, _), psum(~F, mt, ct, Con{l, lt}, Con{b, bs})) : O.C(F)}
      %Equal.sym(O.C(F), O.ofq(~F, S.Q.mul(l, CF.coef(b, m))), O.mul(F, O.ofq(~F, l), O.ofq(~F, CF.coef(b, m))), QE.ofq_mul(~F, l, CF.coef(b, m)))
        : {O.add(F, O.mul(F, O.ofq(~F, l), psi(~F, Con{m, mt}, Con{c, ct}, b)), psum(~F, Con{m, mt}, Con{c, ct}, lt, bs)) == O.add(F, O.mul(F, c, O.add(F, _, O.ofq(~F, CF.qlin(lt, bs, m)))), psum(~F, mt, ct, Con{l, lt}, Con{b, bs})) : O.C(F)}
      %psi_split(~F, mt, ct, l, b, lt, bs)
        : {O.add(F, O.mul(F, O.ofq(~F, l), psi(~F, Con{m, mt}, Con{c, ct}, b)), psum(~F, Con{m, mt}, Con{c, ct}, lt, bs)) == O.add(F, O.mul(F, c, O.add(F, O.mul(F, O.ofq(~F, l), O.ofq(~F, CF.coef(b, m))), O.ofq(~F, CF.qlin(lt, bs, m)))), _) : O.C(F)}
      FR.fring_eq(~F, [c, O.ofq(~F, l), O.ofq(~F, CF.coef(b, m)), O.ofq(~F, CF.qlin(lt, bs, m)), psi(~F, mt, ct, b), psum(~F, mt, ct, lt, bs)],
        E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{4n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZVar{5n}}},
        E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{3n}}}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{4n}}, E.ZVar{5n}}}, {==})

def psum_nn(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>) -> {psum(~F, ms, cs, Nil{}, Nil{}) == O.zero(F) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{c, ct}:
      {==}
    case Con{m, mt} Nil{}:
      {==}
    case Con{+m, +mt} Con{+c, +ct}:
      %Equal.sym(O.C(F), O.ofq(~F, S.Q{S.Z0{}, S.XH{}}), O.zero(F), QE.ofq_zero(~F)) : {O.add(F, O.mul(F, c, _), psum(~F, mt, ct, Nil{}, Nil{})) == O.zero(F) : O.C(F)}
      %FL.mul_zero(~F, c) : {O.add(F, _, psum(~F, mt, ct, Nil{}, Nil{})) == O.zero(F) : O.C(F)}
      %Equal.sym(O.C(F), psum(~F, mt, ct, Nil{}, Nil{}), O.zero(F), psum_nn(~F, mt, ct)) : {O.add(F, O.zero(F), _) == O.zero(F) : O.C(F)}
      zz(~F)

def psum_nc(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +b: E.QExpr, +bs: List<&2, E.QExpr>) -> {psum(~F, ms, cs, Nil{}, Con{b, bs}) == O.zero(F) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{c, ct}:
      {==}
    case Con{m, mt} Nil{}:
      {==}
    case Con{+m, +mt} Con{+c, +ct}:
      %Equal.sym(O.C(F), O.ofq(~F, S.Q{S.Z0{}, S.XH{}}), O.zero(F), QE.ofq_zero(~F)) : {O.add(F, O.mul(F, c, _), psum(~F, mt, ct, Nil{}, Con{b, bs})) == O.zero(F) : O.C(F)}
      %FL.mul_zero(~F, c) : {O.add(F, _, psum(~F, mt, ct, Nil{}, Con{b, bs})) == O.zero(F) : O.C(F)}
      %Equal.sym(O.C(F), psum(~F, mt, ct, Nil{}, Con{b, bs}), O.zero(F), psum_nc(~F, mt, ct, b, bs)) : {O.add(F, O.zero(F), _) == O.zero(F) : O.C(F)}
      zz(~F)

def psum_cn(~F: O.OField, ms: List<&2, List<&2, Nat>>, cs: List<&2, O.C(F)>, +l: S.Q, +lt: List<&2, S.Q>) -> {psum(~F, ms, cs, Con{l, lt}, Nil{}) == O.zero(F) : O.C(F)}:
  match ms cs:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{c, ct}:
      {==}
    case Con{m, mt} Nil{}:
      {==}
    case Con{+m, +mt} Con{+c, +ct}:
      %Equal.sym(O.C(F), O.ofq(~F, S.Q{S.Z0{}, S.XH{}}), O.zero(F), QE.ofq_zero(~F)) : {O.add(F, O.mul(F, c, _), psum(~F, mt, ct, Con{l, lt}, Nil{})) == O.zero(F) : O.C(F)}
      %FL.mul_zero(~F, c) : {O.add(F, _, psum(~F, mt, ct, Con{l, lt}, Nil{})) == O.zero(F) : O.C(F)}
      %Equal.sym(O.C(F), psum(~F, mt, ct, Con{l, lt}, Nil{}), O.zero(F), psum_cn(~F, mt, ct, l, lt)) : {O.add(F, O.zero(F), _) == O.zero(F) : O.C(F)}
      zz(~F)

# psi of lin(ls, B): sum_k l_k psi(B_k)
def fpsi(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, ls: List<&2, S.Q>, B: List<&2, E.QExpr>) -> O.C(F):
  match ls B:
    case Nil{} Nil{}:
      O.zero(F)
    case Nil{} Con{b, bs}:
      O.zero(F)
    case Con{l, lt} Nil{}:
      O.zero(F)
    case Con{l, lt} Con{b, bs}:
      O.add(F, O.mul(F, O.ofq(~F, l), psi(~F, ms, cs, b)), fpsi(~F, ms, cs, lt, bs))

def psum_fpsi(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, ls: List<&2, S.Q>, B: List<&2, E.QExpr>) -> {psum(~F, ms, cs, ls, B) == fpsi(~F, ms, cs, ls, B) : O.C(F)}:
  match ls B:
    case Nil{} Nil{}:
      psum_nn(~F, ms, cs)
    case Nil{} Con{+b, +bs}:
      psum_nc(~F, ms, cs, b, bs)
    case Con{+l, +lt} Nil{}:
      psum_cn(~F, ms, cs, l, lt)
    case Con{+l, +lt} Con{+b, +bs}:
      %psi_split(~F, ms, cs, l, b, lt, bs)
        : {_ == fpsi(~F, ms, cs, Con{l, lt}, Con{b, bs}) : O.C(F)}
      %Equal.sym(O.C(F), psum(~F, ms, cs, lt, bs), fpsi(~F, ms, cs, lt, bs), psum_fpsi(~F, ms, cs, lt, bs))
        : {O.add(F, O.mul(F, O.ofq(~F, l), psi(~F, ms, cs, b)), _) == fpsi(~F, ms, cs, Con{l, lt}, Con{b, bs}) : O.C(F)}
      {==}

def psi_zero(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, +b: E.QExpr, h: {phi(~F, ms, cs, EP.NE(b)) == O.zero(F) : O.C(F)}) -> {psi(~F, ms, cs, b) == O.zero(F) : O.C(F)}:
  %Equal.sym(O.C(F), psi(~F, ms, cs, b), O.mul(F, phi(~F, ms, cs, EP.NE(b)), O.inv(F, O.ofp(~F, QN.den(b)))), psi_phi(~F, ms, cs, b)) : {_ == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), phi(~F, ms, cs, EP.NE(b)), O.zero(F), h) : {O.mul(F, _, O.inv(F, O.ofp(~F, QN.den(b)))) == O.zero(F) : O.C(F)}
  FL.zero_mul(~F, O.inv(F, O.ofp(~F, QN.den(b))))

# the basis being killed, so is every combination of it
def fpsi_zero(~F: O.OField, +ms: List<&2, List<&2, Nat>>, +cs: List<&2, O.C(F)>, ls: List<&2, S.Q>, B: List<&2, E.QExpr>, hp: PZB(~F, ms, cs, B, SV.neqs(B))) -> {fpsi(~F, ms, cs, ls, B) == O.zero(F) : O.C(F)}:
  match ls B:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, bs}:
      {==}
    case Con{l, lt} Nil{}:
      {==}
    case Con{+l, +lt} Con{+b, +bs}:
      (h1, h2) = hp
      %Equal.sym(O.C(F), psi(~F, ms, cs, b), O.zero(F), psi_zero(~F, ms, cs, b, h1)) : {O.add(F, O.mul(F, O.ofq(~F, l), _), fpsi(~F, ms, cs, lt, bs)) == O.zero(F) : O.C(F)}
      %Equal.sym(O.C(F), fpsi(~F, ms, cs, lt, bs), O.zero(F), fpsi_zero(~F, ms, cs, lt, bs, h2)) : {O.add(F, O.mul(F, O.ofq(~F, l), O.zero(F)), _) == O.zero(F) : O.C(F)}
      %FL.mul_zero(~F, O.ofq(~F, l)) : {O.add(F, _, O.zero(F)) == O.zero(F) : O.C(F)}
      zz(~F)

# Independence
# ------------

# the contradiction: psi(e) is 0, but phi(e) is not
def indep.ne(~F: O.OField, +B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos,
  +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat}, +hzp: {EP.zp(rows, EL.Res{p, cb, bt}) == True{} : Bool},
  +hlen: {EP.vlen(cb) == EL.rlen(rows) : Nat}, +hs: {EP.same(p, EP.comb2(bt, e, cb, B)) == True{} : Bool}, +hred: {RP.red(p) == True{} : Bool},
  +hne: {EP.isnil(p) == False{} : Bool}, +pz: PZB(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), B, SV.neqs(B)),
  hpsi: {psi(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), e) == O.zero(F) : O.C(F)}) -> Empty:
  ID.ofz_nz(~F, EL.cz(EL.pivot(p), p), EP.pivot_nz(p, hred, hne),
    (%phi_res(~F, rows, EL.pivot(p), p, cb, bt, hzp) : {_ == O.zero(F) : O.C(F)}
     %Equal.sym(O.C(F), phi(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), p), phi(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), EP.comb2(bt, e, cb, B)),
         phi_same(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), p, EP.comb2(bt, e, cb, B), hs)) : {_ == O.zero(F) : O.C(F)}
     %phi_comb2(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), bt, e, cb, B) : {_ == O.zero(F) : O.C(F)}
     fz(~F, O.ofp(~F, bt), phi(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), EP.NE(e)), fphis(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), cb, B),
       FO.mul_eq_zero(~F, O.inv(F, O.ofp(~F, QN.den(e))), phi(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), EP.NE(e)),
         FO.ne_of_gt(~F, O.inv(F, O.ofp(~F, QN.den(e))), O.zero(F), FO.inv_pos(~F, O.ofp(~F, QN.den(e)), QE.ofp_pos(~F, QN.den(e)))),
         (%FL.mul_comm(~F, phi(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), EP.NE(e)), O.inv(F, O.ofp(~F, QN.den(e)))) : {_ == O.zero(F) : O.C(F)}
          Equal.trans(O.C(F), O.mul(F, phi(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), EP.NE(e)), O.inv(F, O.ofp(~F, QN.den(e)))),
            psi(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), e), O.zero(F),
            Equal.sym(O.C(F), psi(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), e), O.mul(F, phi(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), EP.NE(e)), O.inv(F, O.ofp(~F, QN.den(e)))),
              psi_phi(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), e)), hpsi))),
       fphis_zero(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), cb, B, SV.neqs(B), pz,
         (%Equal.sym(Nat, EP.vlen(cb), SV.neqs(B), Equal.trans(Nat, EP.vlen(cb), EL.rlen(rows), SV.neqs(B), hlen, hl)) : {KA.natle(_, SV.neqs(B)) == True{} : Bool}
          KA.natle_refl(SV.neqs(B)))))))

# phi kills the whole basis
def pz_of(~F: O.OField, +B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +p: List<&2, R.ZTerm>, +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat})
  -> PZB(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), B, SV.neqs(B)):
  %hl : PZB(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), B, _)
  tri(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), B, rows, 0n, hr,
    y_allz(~F, rows, EL.pivot(p), B, EP.rinv_allok(B, rows, 0n, hr), EP.rinv_ech(B, rows, 0n, hr)),
    pzb0(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), B),
    (%hl : {KA.natle(EL.rlen(rows), _) == True{} : Bool}
     KA.natle_refl(EL.rlen(rows))))

# with e's residual r = (p, cb, bt), p not 0: no lin(ls, B) is identically e
def indep.go(~F: O.OField, +B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos,
  +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat}, +hzp: {EP.zp(rows, EL.Res{p, cb, bt}) == True{} : Bool},
  +hlen: {EP.vlen(cb) == EL.rlen(rows) : Nat}, +hs: {EP.same(p, EP.comb2(bt, e, cb, B)) == True{} : Bool}, +hred: {RP.red(p) == True{} : Bool},
  +hne: {EP.isnil(p) == False{} : Bool}, +ls: List<&2, S.Q>, hi: SV.Ident(e, SV.lin(ls, B))) -> Empty:
  +hz = ID.qzero_ident(e, SV.lin(ls, B), hi)
  +pz = pz_of(~F, B, rows, p, hr, hl)
  indep.ne(~F, B, rows, e, p, cb, bt, hr, hl, hzp, hlen, hs, hred, hne, pz,
    Equal.trans(O.C(F), psi(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), e), psum(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), ls, B), O.zero(F),
      psi_eq(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), e, ls, B, hz),
      Equal.trans(O.C(F), psum(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), ls, B), fpsi(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), ls, B), O.zero(F),
        psum_fpsi(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), ls, B), fpsi_zero(~F, ymons(rows, EL.pivot(p)), ycoefs(~F, rows, EL.pivot(p)), ls, B, pz))))

def indep.r(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, r: EL.Res, +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hzp: {EP.zp(rows, r) == True{} : Bool}, hlen: EP.LenR(r, EL.rlen(rows)), hrel: @m: List<&2, Nat> -> EP.Rel(m, r, e, B), hred: {EP.RedR(r) == True{} : Bool},
  hne: {EP.isnil(EP.resp(r)) == False{} : Bool}) -> @ls: List<&2, S.Q> -> SV.Ident(e, SV.lin(ls, B)) -> Empty:
  match r:
    case EL.Res{+p, +cb, +bt}:
      +hl0 = {hlen : {EP.vlen(cb) == EL.rlen(rows) : Nat}}
      +hred2 = hred
      +hne2 = hne
      +hzp2 = hzp
      +hs = EP.same_of(p, EP.comb2(bt, e, cb, B), hred2, EP.comb2_red(bt, e, cb, B), m => EP.new_rel(m, p, cb, bt, e, B, hrel))
      ls => hi => indep.go(~QF.qfield(), B, rows, e, p, cb, bt, hr, hl, hzp2, hl0, hs, hred2, hne2, ls, hi)

# a nonzero residual: e is no constant combination of the basis
def indep(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, +h: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hne: {EP.isnil(EP.resp(EL.resid(rows, e))) == False{} : Bool}) -> @ls: List<&2, S.Q> -> SV.Ident(e, SV.lin(ls, B)) -> Empty:
  indep.r(B, rows, e, EL.resid(rows, e), h, hl,
    EP.reduce_zp(rows, EL.start(e, EL.rlen(rows)), B, EP.rinv_allok(B, rows, 0n, h), EP.rinv_ech(B, rows, 0n, h)),
    EP.resid_len(rows, e, EP.rinv_cblt(B, rows, 0n, EL.rlen(rows), h, KA.natle_refl(EL.rlen(rows)))),
    m => EP.resid_rel(m, rows, e, B, EP.rinv_allok(B, rows, 0n, h)),
    EP.resid_red(rows, e, B, EP.rinv_allok(B, rows, 0n, h)), hne)
