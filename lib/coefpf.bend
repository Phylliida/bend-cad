# bend-cad: identities read coefficient by coefficient (PLAN-sk13a S1).
# coef(e, m) is the rational coefficient of the monomial m in e: the
# coefficient of m in e's cleared normal form, over e's denominator.
# - It is linear: coef of a sum, a difference, a negation, a constant
#   multiple (coef_add, coef_sub, coef_neg, coef_cmul), and of a constant
#   (coef_cst_one, coef_cst_other). A sum's denominator is a shared one
#   (lib/qnorm.bend: sd), not the product, so sums and differences (and
#   coef_lin) are equal as rationals (Q.eq) rather than as terms.
# - An identity has equal coefficients (ident_coef), by the completeness
#   of the normal forms (lib/identpf.bend: qzero_ident).
# So a degree-0 identity among expressions is a system of linear equations
# over the rationals, one per monomial: the bridge to elimination (S2) and
# the simplex (S3). Proofs only.
#
# Coefficients are summed over all terms with the monomial (cz), so the
# normalizer's steps act on them linearly whatever the list; only the
# constant on the right of a product needs sorted monomials (cz_mulc).
#
# Generated from tools/drafts/coefpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ./natring.bend as NR
import ./zring.bend as R
import ./zlaws.bend as ZL
import ./zord.bend as ZO
import ./karith.bend as KA
import ./qnorm.bend as QN
import ./redpoly.bend as RP
import ./identpf.bend as ID
import ./elim.bend as EL
import ./q.bend as LQ
import ./qalg.bend as QA

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Integer coefficients (EL.cz: summed over the terms with the monomial)
# --------------------------------------------------------------------

def ifz_zero(b: Bool, +x: S.Z) -> {x == S.Z.add(EL.ifz(b, S.Z0{}), x) : S.Z}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ifz_add(b: Bool, +c: S.Z, +d: S.Z, +x: S.Z) -> {S.Z.add(EL.ifz(b, c), S.Z.add(EL.ifz(b, d), x)) == S.Z.add(EL.ifz(b, S.Z.add(c, d)), x) : S.Z}:
  match b:
    case True{}:
      ZL.add_assoc(c, d, x)
    case False{}:
      {==}

def ifz_neg(b: Bool, +c: S.Z) -> {S.Z.neg(EL.ifz(b, c)) == EL.ifz(b, S.Z.neg(c)) : S.Z}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ifz_mul_l(b: Bool, +k: S.Z, +c: S.Z) -> {S.Z.mul(k, EL.ifz(b, c)) == EL.ifz(b, S.Z.mul(k, c)) : S.Z}:
  match b:
    case True{}:
      {==}
    case False{}:
      Equal.sym(S.Z, S.Z0{}, S.Z.mul(k, S.Z0{}), ZL.mul_zero(k))

def ifz_mul_r(b: Bool, +c: S.Z, +k: S.Z) -> {S.Z.mul(EL.ifz(b, c), k) == EL.ifz(b, S.Z.mul(c, k)) : S.Z}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cz_pcoef(+m: List<&2, Nat>, s: S.Z, +n: List<&2, Nat>, +rest: List<&2, R.ZTerm>) -> {S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), s), EL.cz(m, rest)) == EL.cz(m, R.pcoef(s, n, rest)) : S.Z}:
  match s:
    case S.Z0{}:
      Equal.sym(S.Z, EL.cz(m, rest), S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), S.Z0{}), EL.cz(m, rest)), ifz_zero(EL.iseq(NR.mcmp(m, n)), EL.cz(m, rest)))
    case S.Zpos{p}:
      {==}
    case S.Zneg{p}:
      {==}

def cz_pins.dec(o: Cmp, +m: List<&2, Nat>, +c: S.Z, +n: List<&2, Nat>, +d: S.Z, +k: List<&2, Nat>, +rest: List<&2, R.ZTerm>,
  eo: {o == NR.mcmp(n, k) : Cmp},
  rec: {S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), EL.cz(m, rest)) == EL.cz(m, R.pins(c, n, rest)) : S.Z})
  -> {S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, k)), d), EL.cz(m, rest))) == EL.cz(m, R.pins.dec(o, c, n, d, k, rest, R.pins(c, n, rest))) : S.Z}:
  match o:
    case LT{}:
      {==}
    case EQ{}:
      %cz_pcoef(m, S.Z.add(c, d), k, rest)
        : {S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, k)), d), EL.cz(m, rest))) == _ : S.Z}
      %Equal.sym(List<&2, Nat>, n, k, NR.mcmp_eq(n, k, eo)) : {S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, _)), c), S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, k)), d), EL.cz(m, rest))) == S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, k)), S.Z.add(c, d)), EL.cz(m, rest)) : S.Z}
      ifz_add(EL.iseq(NR.mcmp(m, k)), c, d, EL.cz(m, rest))
    case GT{}:
      %rec
        : {S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, k)), d), EL.cz(m, rest))) == S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, k)), d), _) : S.Z}
      ZL.add_swap(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), EL.ifz(EL.iseq(NR.mcmp(m, k)), d), EL.cz(m, rest))

def cz_pins(+m: List<&2, Nat>, +c: S.Z, +n: List<&2, Nat>, p: List<&2, R.ZTerm>) -> {S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), EL.cz(m, p)) == EL.cz(m, R.pins(c, n, p)) : S.Z}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{+d, +k}, +rest}:
      cz_pins.dec(NR.mcmp(n, k), m, c, n, d, k, rest, {==}, cz_pins(m, c, n, rest))

def cz_pinsert(+m: List<&2, Nat>, c: S.Z, +n: List<&2, Nat>, +p: List<&2, R.ZTerm>) -> {S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), EL.cz(m, p)) == EL.cz(m, R.pinsert(c, n, p)) : S.Z}:
  match c:
    case S.Z0{}:
      Equal.sym(S.Z, EL.cz(m, p), S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), S.Z0{}), EL.cz(m, p)), ifz_zero(EL.iseq(NR.mcmp(m, n)), EL.cz(m, p)))
    case S.Zpos{q}:
      cz_pins(m, S.Zpos{q}, n, p)
    case S.Zneg{q}:
      cz_pins(m, S.Zneg{q}, n, p)

def cz_padd(+m: List<&2, Nat>, p: List<&2, R.ZTerm>, +q: List<&2, R.ZTerm>) -> {S.Z.add(EL.cz(m, p), EL.cz(m, q)) == EL.cz(m, R.padd(p, q)) : S.Z}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{+c, +n}, +rest}:
      %cz_pinsert(m, c, n, R.padd(rest, q)) : {S.Z.add(S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), EL.cz(m, rest)), EL.cz(m, q)) == _ : S.Z}
      %cz_padd(m, rest, q) : {S.Z.add(S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), EL.cz(m, rest)), EL.cz(m, q)) == S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), _) : S.Z}
      Equal.sym(S.Z, S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), S.Z.add(EL.cz(m, rest), EL.cz(m, q))), S.Z.add(S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), EL.cz(m, rest)), EL.cz(m, q)),
        ZL.add_assoc(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), EL.cz(m, rest), EL.cz(m, q)))

def cz_pneg(+m: List<&2, Nat>, p: List<&2, R.ZTerm>) -> {S.Z.neg(EL.cz(m, p)) == EL.cz(m, R.pneg(p)) : S.Z}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{+c, +n}, +rest}:
      %cz_pneg(m, rest) : {S.Z.neg(S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), EL.cz(m, rest))) == S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), S.Z.neg(c)), _) : S.Z}
      %ifz_neg(EL.iseq(NR.mcmp(m, n)), c) : {S.Z.neg(S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), EL.cz(m, rest))) == S.Z.add(_, S.Z.neg(EL.cz(m, rest))) : S.Z}
      Equal.sym(S.Z, S.Z.add(S.Z.neg(EL.ifz(EL.iseq(NR.mcmp(m, n)), c)), S.Z.neg(EL.cz(m, rest))), S.Z.neg(S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), EL.cz(m, rest))),
        ZL.neg_add(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), EL.cz(m, rest)))

# scaling by a constant scales the coefficient
def cz_pscale0(+m: List<&2, Nat>, +k: S.Z, q: List<&2, R.ZTerm>) -> {S.Z.mul(k, EL.cz(m, q)) == EL.cz(m, R.pscale(k, Nil{}, q)) : S.Z}:
  match q:
    case Nil{}:
      Equal.sym(S.Z, S.Z0{}, S.Z.mul(k, S.Z0{}), ZL.mul_zero(k))
    case Con{R.ZTerm{+d, +n}, +rest}:
      %cz_pinsert(m, S.Z.mul(k, d), n, R.pscale(k, Nil{}, rest)) : {S.Z.mul(k, S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), d), EL.cz(m, rest))) == _ : S.Z}
      %cz_pscale0(m, k, rest) : {S.Z.mul(k, S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), d), EL.cz(m, rest))) == S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), S.Z.mul(k, d)), _) : S.Z}
      %ifz_mul_l(EL.iseq(NR.mcmp(m, n)), k, d) : {S.Z.mul(k, S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), d), EL.cz(m, rest))) == S.Z.add(_, S.Z.mul(k, EL.cz(m, rest))) : S.Z}
      Equal.sym(S.Z, S.Z.add(S.Z.mul(k, EL.ifz(EL.iseq(NR.mcmp(m, n)), d)), S.Z.mul(k, EL.cz(m, rest))), S.Z.mul(k, S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), d), EL.cz(m, rest))),
        ZL.mul_add_l(k, EL.ifz(EL.iseq(NR.mcmp(m, n)), d), EL.cz(m, rest)))

# a constant on the left of a product
def cz_cmul(+m: List<&2, Nat>, k: S.Z, +q: List<&2, R.ZTerm>) -> {S.Z.mul(k, EL.cz(m, q)) == EL.cz(m, R.pmul(R.pconst(k), q)) : S.Z}:
  match k:
    case S.Z0{}:
      {==}
    case S.Zpos{+p}:
      %cz_padd(m, R.pscale(S.Zpos{p}, Nil{}, q), Nil{})
        : {S.Z.mul(S.Zpos{p}, EL.cz(m, q)) == _ : S.Z}
      %ZL.add_zero(EL.cz(m, R.pscale(S.Zpos{p}, Nil{}, q))) : {S.Z.mul(S.Zpos{p}, EL.cz(m, q)) == _ : S.Z}
      cz_pscale0(m, S.Zpos{p}, q)
    case S.Zneg{+p}:
      %cz_padd(m, R.pscale(S.Zneg{p}, Nil{}, q), Nil{})
        : {S.Z.mul(S.Zneg{p}, EL.cz(m, q)) == _ : S.Z}
      %ZL.add_zero(EL.cz(m, R.pscale(S.Zneg{p}, Nil{}, q))) : {S.Z.mul(S.Zneg{p}, EL.cz(m, q)) == _ : S.Z}
      cz_pscale0(m, S.Zneg{p}, q)

def natle_isle(x: Nat, y: Nat, h: {KA.natle(x, y) == True{} : Bool}) -> {Nat.is_le(x, y) == True{} : Bool}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, KA.ft(h))
    case 1n+p 1n+q:
      natle_isle(p, q, h)

def minsert_self(+v: Nat, vs: List<&2, Nat>, h: {RP.mge(v, vs) == True{} : Bool}) -> {Con{v, vs} == NR.minsert(v, vs) : List<&2, Nat>}:
  match vs:
    case Nil{}:
      {==}
    case Con{+w, +ws}:
      %Equal.sym(Bool, Nat.is_le(v, w), True{}, natle_isle(v, w, KA.band_l(KA.natle(v, w), RP.mge(v, ws), h)))
        : {Con{v, Con{w, ws}} == NR.minsert.dec(_, v, w, ws, NR.minsert(v, ws)) : List<&2, Nat>}
      {==}

# a sorted monomial times 1 is itself
def mmul_nil(m: List<&2, Nat>, +h: {RP.msort(m) == True{} : Bool}) -> {m == NR.mmul(m, Nil{}) : List<&2, Nat>}:
  match m:
    case Nil{}:
      {==}
    case Con{+v, +vs}:
      %mmul_nil(vs, KA.band_r(RP.mge(v, vs), RP.msort(vs), h)) : {Con{v, vs} == NR.minsert(v, _) : List<&2, Nat>}
      minsert_self(v, vs, KA.band_l(RP.mge(v, vs), RP.msort(vs), h))

def pmul_nil(p: List<&2, R.ZTerm>) -> {Nil{} == R.pmul(p, Nil{}) : List<&2, R.ZTerm>}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{c, m}, rest}:
      pmul_nil(rest)

def cz_mulc1(+m: List<&2, Nat>, p: List<&2, R.ZTerm>, +k: S.Z, +hr: {RP.red(p) == True{} : Bool}) -> {S.Z.mul(EL.cz(m, p), k) == EL.cz(m, R.pmul(p, Con{R.ZTerm{k, Nil{}}, Nil{}})) : S.Z}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{+c, +n}, +rest}:
      %cz_padd(m, R.pinsert(S.Z.mul(c, k), NR.mmul(n, Nil{}), Nil{}), R.pmul(rest, Con{R.ZTerm{k, Nil{}}, Nil{}}))
        : {S.Z.mul(EL.cz(m, Con{R.ZTerm{c, n}, rest}), k) == _ : S.Z}
      %cz_pinsert(m, S.Z.mul(c, k), NR.mmul(n, Nil{}), Nil{})
        : {S.Z.mul(EL.cz(m, Con{R.ZTerm{c, n}, rest}), k) == S.Z.add(_, EL.cz(m, R.pmul(rest, Con{R.ZTerm{k, Nil{}}, Nil{}}))) : S.Z}
      %cz_mulc1(m, rest, k, RP.red_r(c, n, rest, hr))
        : {S.Z.mul(EL.cz(m, Con{R.ZTerm{c, n}, rest}), k) == S.Z.add(S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, NR.mmul(n, Nil{}))), S.Z.mul(c, k)), S.Z0{}), _) : S.Z}
      %mmul_nil(n, RP.red_m(c, n, rest, hr))
        : {S.Z.mul(EL.cz(m, Con{R.ZTerm{c, n}, rest}), k) == S.Z.add(S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, _)), S.Z.mul(c, k)), S.Z0{}), S.Z.mul(EL.cz(m, rest), k)) : S.Z}
      %ZL.add_zero(EL.ifz(EL.iseq(NR.mcmp(m, n)), S.Z.mul(c, k)))
        : {S.Z.mul(EL.cz(m, Con{R.ZTerm{c, n}, rest}), k) == S.Z.add(_, S.Z.mul(EL.cz(m, rest), k)) : S.Z}
      %ifz_mul_r(EL.iseq(NR.mcmp(m, n)), c, k)
        : {S.Z.mul(EL.cz(m, Con{R.ZTerm{c, n}, rest}), k) == S.Z.add(_, S.Z.mul(EL.cz(m, rest), k)) : S.Z}
      Equal.sym(S.Z, S.Z.add(S.Z.mul(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), k), S.Z.mul(EL.cz(m, rest), k)), S.Z.mul(S.Z.add(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), EL.cz(m, rest)), k),
        ZL.mul_add_r(EL.ifz(EL.iseq(NR.mcmp(m, n)), c), EL.cz(m, rest), k))

# a constant on the right of a product, over a reduced polynomial
def cz_mulc(+m: List<&2, Nat>, +p: List<&2, R.ZTerm>, k: S.Z, hr: {RP.red(p) == True{} : Bool}) -> {S.Z.mul(EL.cz(m, p), k) == EL.cz(m, R.pmul(p, R.pconst(k))) : S.Z}:
  match k:
    case S.Z0{}:
      %pmul_nil(p) : {S.Z.mul(EL.cz(m, p), S.Z0{}) == EL.cz(m, _) : S.Z}
      Equal.sym(S.Z, S.Z0{}, S.Z.mul(EL.cz(m, p), S.Z0{}), ZL.mul_zero(EL.cz(m, p)))
    case S.Zpos{q}:
      cz_mulc1(m, p, S.Zpos{q}, hr)
    case S.Zneg{q}:
      cz_mulc1(m, p, S.Zneg{q}, hr)

# Shared denominators
# -------------------

def zz(z: S.Z) -> Bool:
  match z:
    case S.Z0{}:
      True{}
    case S.Zpos{p}:
      False{}
    case S.Zneg{p}:
      False{}

# z p = 0 with p positive gives z = 0
def mulpos_zero(z: S.Z, +p: S.Pos, h: {S.Z.mul(z, S.Zpos{p}) == S.Z0{} : S.Z}) -> {z == S.Z0{} : S.Z}:
  match z:
    case S.Z0{}:
      {==}
    case S.Zpos{q}:
      absurd({S.Zpos{q} == S.Z0{} : S.Z}, KA.ft(Equal.cong(S.Z, Bool, x => zz(x), S.Z.mul(S.Zpos{q}, S.Zpos{p}), S.Z0{}, h)))
    case S.Zneg{q}:
      absurd({S.Zneg{q} == S.Z0{} : S.Z}, KA.ft(Equal.cong(S.Z, Bool, x => zz(x), S.Z.mul(S.Zneg{q}, S.Zpos{p}), S.Z0{}, h)))


# (c1 db + c2 da) d = (c1 fa + c2 fb) da db, when da fa = d = db fb
def dshare(+c1: S.Z, +c2: S.Z, +da: S.Pos, +db: S.Pos, +fa: S.Pos, +fb: S.Pos, +d: S.Pos, ha: {S.Pos.mul(da, fa) == d : S.Pos}, hb: {S.Pos.mul(db, fb) == d : S.Pos})
  -> {S.Z.mul(S.Z.add(S.Z.mul(c1, S.Zpos{db}), S.Z.mul(c2, S.Zpos{da})), S.Zpos{d}) == S.Z.mul(S.Z.add(S.Z.mul(c1, S.Zpos{fa}), S.Z.mul(c2, S.Zpos{fb})), S.Zpos{S.Pos.mul(da, db)}) : S.Z}:
  %R.ring_eq([c1, c2, S.Zpos{da}, S.Zpos{db}, S.Zpos{d}], E.ZAdd{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZVar{4n}}, E.ZMul{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{4n}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZVar{4n}}, {==}) : {_ == S.Z.mul(S.Z.add(S.Z.mul(c1, S.Zpos{fa}), S.Z.mul(c2, S.Zpos{fb})), S.Zpos{S.Pos.mul(da, db)}) : S.Z}
  %ha : {S.Z.add(S.Z.mul(S.Z.mul(c1, S.Zpos{db}), S.Zpos{_}), S.Z.mul(S.Z.mul(c2, S.Zpos{da}), S.Zpos{d})) == S.Z.mul(S.Z.add(S.Z.mul(c1, S.Zpos{fa}), S.Z.mul(c2, S.Zpos{fb})), S.Zpos{S.Pos.mul(da, db)}) : S.Z}
  %hb : {S.Z.add(S.Z.mul(S.Z.mul(c1, S.Zpos{db}), S.Zpos{S.Pos.mul(da, fa)}), S.Z.mul(S.Z.mul(c2, S.Zpos{da}), S.Zpos{_})) == S.Z.mul(S.Z.add(S.Z.mul(c1, S.Zpos{fa}), S.Z.mul(c2, S.Zpos{fb})), S.Zpos{S.Pos.mul(da, db)}) : S.Z}
  R.ring_eq([c1, c2, S.Zpos{da}, S.Zpos{db}, S.Zpos{fa}, S.Zpos{fb}], E.ZAdd{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{2n}, E.ZVar{4n}}}, E.ZMul{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZMul{E.ZVar{3n}, E.ZVar{5n}}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}, E.ZMul{E.ZVar{1n}, E.ZVar{5n}}}, E.ZMul{E.ZVar{2n}, E.ZVar{3n}}}, {==})

# c1 d2 - c2 d1 = 0 from c1 fa - c2 fb = 0, when d1 fa = d = d2 fb
def cross(+c1: S.Z, +c2: S.Z, +d1: S.Pos, +d2: S.Pos, +fa: S.Pos, +fb: S.Pos, +d: S.Pos, ha: {S.Pos.mul(d1, fa) == d : S.Pos}, hb: {S.Pos.mul(d2, fb) == d : S.Pos},
  h: {S.Z.sub(S.Z.mul(c1, S.Zpos{fa}), S.Z.mul(c2, S.Zpos{fb})) == S.Z0{} : S.Z}) -> {S.Z.sub(S.Z.mul(c1, S.Zpos{d2}), S.Z.mul(c2, S.Zpos{d1})) == S.Z0{} : S.Z}:
  mulpos_zero(S.Z.sub(S.Z.mul(c1, S.Zpos{d2}), S.Z.mul(c2, S.Zpos{d1})), d,
    (%R.ring_eq([c1, c2, S.Zpos{d1}, S.Zpos{d2}, S.Zpos{d}], E.ZSub{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZVar{4n}}, E.ZMul{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{4n}}}, E.ZMul{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZVar{4n}}, {==}) : {_ == S.Z0{} : S.Z}
     %ha : {S.Z.sub(S.Z.mul(S.Z.mul(c1, S.Zpos{d2}), S.Zpos{_}), S.Z.mul(S.Z.mul(c2, S.Zpos{d1}), S.Zpos{d})) == S.Z0{} : S.Z}
     %hb : {S.Z.sub(S.Z.mul(S.Z.mul(c1, S.Zpos{d2}), S.Zpos{S.Pos.mul(d1, fa)}), S.Z.mul(S.Z.mul(c2, S.Zpos{d1}), S.Zpos{_})) == S.Z0{} : S.Z}
     %R.ring_eq([c1, c2, S.Zpos{d1}, S.Zpos{d2}, S.Zpos{fa}, S.Zpos{fb}], E.ZMul{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}, E.ZMul{E.ZVar{1n}, E.ZVar{5n}}}, E.ZMul{E.ZVar{2n}, E.ZVar{3n}}}, E.ZSub{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{2n}, E.ZVar{4n}}}, E.ZMul{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZMul{E.ZVar{3n}, E.ZVar{5n}}}}, {==}) : {_ == S.Z0{} : S.Z}
     %Equal.sym(S.Z, S.Z.sub(S.Z.mul(c1, S.Zpos{fa}), S.Z.mul(c2, S.Zpos{fb})), S.Z0{}, h) : {S.Z.mul(_, S.Z.mul(S.Zpos{d1}, S.Zpos{d2})) == S.Z0{} : S.Z}
     {==}))

# a rational equal to one with numerator 0 has numerator 0
def num0(+x: S.Q, +y: S.Q, e: S.Q.eq(x, y), h: {S.Q.num(x) == S.Z0{} : S.Z}) -> {S.Q.num(y) == S.Z0{} : S.Z}:
  mulpos_zero(S.Q.num(y), S.Q.den(x),
    Equal.trans(S.Z, S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}), S.Z0{},
      Equal.sym(S.Z, S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}), S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), e),
      (%Equal.sym(S.Z, S.Q.num(x), S.Z0{}, h) : {S.Z.mul(_, S.Zpos{S.Q.den(y)}) == S.Z0{} : S.Z}
       {==})))

# Rational coefficients
# ---------------------

# the coefficient of the monomial m in e
def coef(+e: E.QExpr, +m: List<&2, Nat>) -> S.Q:
  S.Q{EL.cz(m, R.norm(QN.clr(e))), QN.den(e)}


def coef_add(+a: E.QExpr, +b: E.QExpr, +m: List<&2, Nat>) -> S.Q.eq(S.Q.add(coef(a, m), coef(b, m)), coef(E.QAdd{a, b}, m)):
  %cz_padd(m, R.pmul(R.norm(QN.clr(a)), R.pconst(S.Zpos{QN.SD.fa(QN.sd(QN.den(a), QN.den(b)))})), R.pmul(R.norm(QN.clr(b)), R.pconst(S.Zpos{QN.SD.fb(QN.sd(QN.den(a), QN.den(b)))}))) : {S.Z.mul(S.Z.add(S.Z.mul(EL.cz(m, R.norm(QN.clr(a))), S.Zpos{QN.den(b)}), S.Z.mul(EL.cz(m, R.norm(QN.clr(b))), S.Zpos{QN.den(a)})), S.Zpos{QN.SD.d(QN.sd(QN.den(a), QN.den(b)))}) == S.Z.mul(_, S.Zpos{S.Pos.mul(QN.den(a), QN.den(b))}) : S.Z}
  %cz_mulc(m, R.norm(QN.clr(a)), S.Zpos{QN.SD.fa(QN.sd(QN.den(a), QN.den(b)))}, RP.norm_red(QN.clr(a))) : {S.Z.mul(S.Z.add(S.Z.mul(EL.cz(m, R.norm(QN.clr(a))), S.Zpos{QN.den(b)}), S.Z.mul(EL.cz(m, R.norm(QN.clr(b))), S.Zpos{QN.den(a)})), S.Zpos{QN.SD.d(QN.sd(QN.den(a), QN.den(b)))}) == S.Z.mul(S.Z.add(_, EL.cz(m, R.pmul(R.norm(QN.clr(b)), R.pconst(S.Zpos{QN.SD.fb(QN.sd(QN.den(a), QN.den(b)))})))), S.Zpos{S.Pos.mul(QN.den(a), QN.den(b))}) : S.Z}
  %cz_mulc(m, R.norm(QN.clr(b)), S.Zpos{QN.SD.fb(QN.sd(QN.den(a), QN.den(b)))}, RP.norm_red(QN.clr(b))) : {S.Z.mul(S.Z.add(S.Z.mul(EL.cz(m, R.norm(QN.clr(a))), S.Zpos{QN.den(b)}), S.Z.mul(EL.cz(m, R.norm(QN.clr(b))), S.Zpos{QN.den(a)})), S.Zpos{QN.SD.d(QN.sd(QN.den(a), QN.den(b)))}) == S.Z.mul(S.Z.add(S.Z.mul(EL.cz(m, R.norm(QN.clr(a))), S.Zpos{QN.SD.fa(QN.sd(QN.den(a), QN.den(b)))}), _), S.Zpos{S.Pos.mul(QN.den(a), QN.den(b))}) : S.Z}
  dshare(EL.cz(m, R.norm(QN.clr(a))), EL.cz(m, R.norm(QN.clr(b))), QN.den(a), QN.den(b), QN.SD.fa(QN.sd(QN.den(a), QN.den(b))), QN.SD.fb(QN.sd(QN.den(a), QN.den(b))), QN.SD.d(QN.sd(QN.den(a), QN.den(b))), QN.sd_a(QN.den(a), QN.den(b)), QN.sd_b(QN.den(a), QN.den(b)))

def coef_neg(+a: E.QExpr, +m: List<&2, Nat>) -> {S.Q.neg(coef(a, m)) == coef(E.QNeg{a}, m) : S.Q}:
  %cz_pneg(m, R.norm(QN.clr(a))) : {S.Q.neg(coef(a, m)) == S.Q{_, QN.den(a)} : S.Q}
  {==}

def coef_sub(+a: E.QExpr, +b: E.QExpr, +m: List<&2, Nat>) -> S.Q.eq(S.Q.sub(coef(a, m), coef(b, m)), coef(E.QSub{a, b}, m)):
  %cz_padd(m, R.pmul(R.norm(QN.clr(a)), R.pconst(S.Zpos{QN.SD.fa(QN.sd(QN.den(a), QN.den(b)))})), R.pneg(R.pmul(R.norm(QN.clr(b)), R.pconst(S.Zpos{QN.SD.fb(QN.sd(QN.den(a), QN.den(b)))})))) : {S.Z.mul(S.Z.add(S.Z.mul(EL.cz(m, R.norm(QN.clr(a))), S.Zpos{QN.den(b)}), S.Z.mul(S.Z.neg(EL.cz(m, R.norm(QN.clr(b)))), S.Zpos{QN.den(a)})), S.Zpos{QN.SD.d(QN.sd(QN.den(a), QN.den(b)))}) == S.Z.mul(_, S.Zpos{S.Pos.mul(QN.den(a), QN.den(b))}) : S.Z}
  %cz_pneg(m, R.pmul(R.norm(QN.clr(b)), R.pconst(S.Zpos{QN.SD.fb(QN.sd(QN.den(a), QN.den(b)))}))) : {S.Z.mul(S.Z.add(S.Z.mul(EL.cz(m, R.norm(QN.clr(a))), S.Zpos{QN.den(b)}), S.Z.mul(S.Z.neg(EL.cz(m, R.norm(QN.clr(b)))), S.Zpos{QN.den(a)})), S.Zpos{QN.SD.d(QN.sd(QN.den(a), QN.den(b)))}) == S.Z.mul(S.Z.add(EL.cz(m, R.pmul(R.norm(QN.clr(a)), R.pconst(S.Zpos{QN.SD.fa(QN.sd(QN.den(a), QN.den(b)))}))), _), S.Zpos{S.Pos.mul(QN.den(a), QN.den(b))}) : S.Z}
  %cz_mulc(m, R.norm(QN.clr(a)), S.Zpos{QN.SD.fa(QN.sd(QN.den(a), QN.den(b)))}, RP.norm_red(QN.clr(a))) : {S.Z.mul(S.Z.add(S.Z.mul(EL.cz(m, R.norm(QN.clr(a))), S.Zpos{QN.den(b)}), S.Z.mul(S.Z.neg(EL.cz(m, R.norm(QN.clr(b)))), S.Zpos{QN.den(a)})), S.Zpos{QN.SD.d(QN.sd(QN.den(a), QN.den(b)))}) == S.Z.mul(S.Z.add(_, S.Z.neg(EL.cz(m, R.pmul(R.norm(QN.clr(b)), R.pconst(S.Zpos{QN.SD.fb(QN.sd(QN.den(a), QN.den(b)))}))))), S.Zpos{S.Pos.mul(QN.den(a), QN.den(b))}) : S.Z}
  %cz_mulc(m, R.norm(QN.clr(b)), S.Zpos{QN.SD.fb(QN.sd(QN.den(a), QN.den(b)))}, RP.norm_red(QN.clr(b))) : {S.Z.mul(S.Z.add(S.Z.mul(EL.cz(m, R.norm(QN.clr(a))), S.Zpos{QN.den(b)}), S.Z.mul(S.Z.neg(EL.cz(m, R.norm(QN.clr(b)))), S.Zpos{QN.den(a)})), S.Zpos{QN.SD.d(QN.sd(QN.den(a), QN.den(b)))}) == S.Z.mul(S.Z.add(S.Z.mul(EL.cz(m, R.norm(QN.clr(a))), S.Zpos{QN.SD.fa(QN.sd(QN.den(a), QN.den(b)))}), S.Z.neg(_)), S.Zpos{S.Pos.mul(QN.den(a), QN.den(b))}) : S.Z}
  %ZL.neg_mul(EL.cz(m, R.norm(QN.clr(b))), S.Zpos{QN.SD.fb(QN.sd(QN.den(a), QN.den(b)))}) : {S.Z.mul(S.Z.add(S.Z.mul(EL.cz(m, R.norm(QN.clr(a))), S.Zpos{QN.den(b)}), S.Z.mul(S.Z.neg(EL.cz(m, R.norm(QN.clr(b)))), S.Zpos{QN.den(a)})), S.Zpos{QN.SD.d(QN.sd(QN.den(a), QN.den(b)))}) == S.Z.mul(S.Z.add(S.Z.mul(EL.cz(m, R.norm(QN.clr(a))), S.Zpos{QN.SD.fa(QN.sd(QN.den(a), QN.den(b)))}), _), S.Zpos{S.Pos.mul(QN.den(a), QN.den(b))}) : S.Z}
  dshare(EL.cz(m, R.norm(QN.clr(a))), S.Z.neg(EL.cz(m, R.norm(QN.clr(b)))), QN.den(a), QN.den(b), QN.SD.fa(QN.sd(QN.den(a), QN.den(b))), QN.SD.fb(QN.sd(QN.den(a), QN.den(b))), QN.SD.d(QN.sd(QN.den(a), QN.den(b))), QN.sd_a(QN.den(a), QN.den(b)), QN.sd_b(QN.den(a), QN.den(b)))

# a constant multiple
def coef_cmul(l: S.Q, +a: E.QExpr, +m: List<&2, Nat>) -> {S.Q.mul(l, coef(a, m)) == coef(E.QMul{E.QCst{l}, a}, m) : S.Q}:
  match l:
    case S.Q{+n, +d}:
      %cz_cmul(m, n, R.norm(QN.clr(a))) : {S.Q.mul(S.Q{n, d}, coef(a, m)) == S.Q{_, S.Pos.mul(d, QN.den(a))} : S.Q}
      {==}

# a constant: its coefficient at 1 is itself, elsewhere 0
def coef_cst_one.n(n: S.Z, +d: S.Pos) -> {S.Q{n, d} == coef(E.QCst{S.Q{n, d}}, Nil{}) : S.Q}:
  match n:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      {==}
    case S.Zneg{p}:
      {==}

def coef_cst_one(k: S.Q) -> {k == coef(E.QCst{k}, Nil{}) : S.Q}:
  match k:
    case S.Q{n, d}:
      coef_cst_one.n(n, d)


def coef_cst_other.n(n: S.Z, +d: S.Pos, +v: Nat, +vs: List<&2, Nat>) -> S.Q.eq(coef(E.QCst{S.Q{n, d}}, Con{v, vs}), SV.qzero()):
  match n:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      {==}
    case S.Zneg{p}:
      {==}

def coef_cst_other(k: S.Q, +v: Nat, +vs: List<&2, Nat>) -> S.Q.eq(coef(E.QCst{k}, Con{v, vs}), SV.qzero()):
  match k:
    case S.Q{n, d}:
      coef_cst_other.n(n, d, v, vs)

# l_1 coef(e_1) + ... + l_n coef(e_n), shaped like SV.lin
def qlin(ls: List<&2, S.Q>, es: List<&2, E.QExpr>, +m: List<&2, Nat>) -> S.Q:
  match ls es:
    case Nil{} Nil{}:
      S.Q{S.Z0{}, S.XH{}}
    case Nil{} Con{e, et}:
      S.Q{S.Z0{}, S.XH{}}
    case Con{l, lt} Nil{}:
      S.Q{S.Z0{}, S.XH{}}
    case Con{l, lt} Con{e, et}:
      S.Q.add(S.Q.mul(l, coef(e, m)), qlin(lt, et, m))

# the coefficients of a combination are the combination of coefficients
def coef_lin(ls: List<&2, S.Q>, es: List<&2, E.QExpr>, +m: List<&2, Nat>) -> S.Q.eq(qlin(ls, es, m), coef(SV.lin(ls, es), m)):
  match ls es:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{e, et}:
      {==}
    case Con{l, lt} Nil{}:
      {==}
    case Con{+l, +lt} Con{+e, +et}:
      LQ.q_trans(S.Q.add(S.Q.mul(l, coef(e, m)), qlin(lt, et, m)), S.Q.add(coef(E.QMul{E.QCst{l}, e}, m), coef(SV.lin(lt, et), m)), coef(SV.lin(Con{l, lt}, Con{e, et}), m),
        (%coef_cmul(l, e, m) : S.Q.eq(S.Q.add(S.Q.mul(l, coef(e, m)), qlin(lt, et, m)), S.Q.add(_, coef(SV.lin(lt, et), m)))
         LQ.q_add_cong_r(S.Q.mul(l, coef(e, m)), qlin(lt, et, m), coef(SV.lin(lt, et), m), coef_lin(lt, et, m))),
        coef_add(E.QMul{E.QCst{l}, e}, SV.lin(lt, et), m))

# Identities have equal coefficients
# ----------------------------------


# the cleared difference's coefficient, by the shared denominator's factors
def coef_zero.f(+e1: E.QExpr, +e2: E.QExpr, +m: List<&2, Nat>, nil: {Nil{} == R.norm(QN.clr(E.QSub{e1, e2})) : List<&2, R.ZTerm>})
  -> {S.Z.sub(S.Z.mul(EL.cz(m, R.norm(QN.clr(e1))), S.Zpos{QN.SD.fa(QN.sd(QN.den(e1), QN.den(e2)))}), S.Z.mul(EL.cz(m, R.norm(QN.clr(e2))), S.Zpos{QN.SD.fb(QN.sd(QN.den(e1), QN.den(e2)))})) == S.Z0{} : S.Z}:
  %Equal.sym(S.Z, S.Z.mul(EL.cz(m, R.norm(QN.clr(e1))), S.Zpos{QN.SD.fa(QN.sd(QN.den(e1), QN.den(e2)))}), EL.cz(m, R.pmul(R.norm(QN.clr(e1)), R.pconst(S.Zpos{QN.SD.fa(QN.sd(QN.den(e1), QN.den(e2)))}))),
      cz_mulc(m, R.norm(QN.clr(e1)), S.Zpos{QN.SD.fa(QN.sd(QN.den(e1), QN.den(e2)))}, RP.norm_red(QN.clr(e1))))
    : {S.Z.add(_, S.Z.neg(S.Z.mul(EL.cz(m, R.norm(QN.clr(e2))), S.Zpos{QN.SD.fb(QN.sd(QN.den(e1), QN.den(e2)))}))) == S.Z0{} : S.Z}
  %Equal.sym(S.Z, S.Z.mul(EL.cz(m, R.norm(QN.clr(e2))), S.Zpos{QN.SD.fb(QN.sd(QN.den(e1), QN.den(e2)))}), EL.cz(m, R.pmul(R.norm(QN.clr(e2)), R.pconst(S.Zpos{QN.SD.fb(QN.sd(QN.den(e1), QN.den(e2)))}))),
      cz_mulc(m, R.norm(QN.clr(e2)), S.Zpos{QN.SD.fb(QN.sd(QN.den(e1), QN.den(e2)))}, RP.norm_red(QN.clr(e2))))
    : {S.Z.add(EL.cz(m, R.pmul(R.norm(QN.clr(e1)), R.pconst(S.Zpos{QN.SD.fa(QN.sd(QN.den(e1), QN.den(e2)))}))), S.Z.neg(_)) == S.Z0{} : S.Z}
  %Equal.sym(S.Z, S.Z.neg(EL.cz(m, R.pmul(R.norm(QN.clr(e2)), R.pconst(S.Zpos{QN.SD.fb(QN.sd(QN.den(e1), QN.den(e2)))})))), EL.cz(m, R.pneg(R.pmul(R.norm(QN.clr(e2)), R.pconst(S.Zpos{QN.SD.fb(QN.sd(QN.den(e1), QN.den(e2)))})))),
      cz_pneg(m, R.pmul(R.norm(QN.clr(e2)), R.pconst(S.Zpos{QN.SD.fb(QN.sd(QN.den(e1), QN.den(e2)))}))))
    : {S.Z.add(EL.cz(m, R.pmul(R.norm(QN.clr(e1)), R.pconst(S.Zpos{QN.SD.fa(QN.sd(QN.den(e1), QN.den(e2)))}))), _) == S.Z0{} : S.Z}
  %Equal.sym(S.Z, S.Z.add(EL.cz(m, R.pmul(R.norm(QN.clr(e1)), R.pconst(S.Zpos{QN.SD.fa(QN.sd(QN.den(e1), QN.den(e2)))}))), EL.cz(m, R.pneg(R.pmul(R.norm(QN.clr(e2)), R.pconst(S.Zpos{QN.SD.fb(QN.sd(QN.den(e1), QN.den(e2)))}))))),
      EL.cz(m, R.padd(R.pmul(R.norm(QN.clr(e1)), R.pconst(S.Zpos{QN.SD.fa(QN.sd(QN.den(e1), QN.den(e2)))})), R.pneg(R.pmul(R.norm(QN.clr(e2)), R.pconst(S.Zpos{QN.SD.fb(QN.sd(QN.den(e1), QN.den(e2)))}))))),
      cz_padd(m, R.pmul(R.norm(QN.clr(e1)), R.pconst(S.Zpos{QN.SD.fa(QN.sd(QN.den(e1), QN.den(e2)))})), R.pneg(R.pmul(R.norm(QN.clr(e2)), R.pconst(S.Zpos{QN.SD.fb(QN.sd(QN.den(e1), QN.den(e2)))})))))
    : {_ == S.Z0{} : S.Z}
  %nil : {EL.cz(m, _) == S.Z0{} : S.Z}
  {==}

def coef_zero(+e1: E.QExpr, +e2: E.QExpr, +m: List<&2, Nat>, nil: {Nil{} == R.norm(QN.clr(E.QSub{e1, e2})) : List<&2, R.ZTerm>})
  -> {S.Z.sub(S.Z.mul(EL.cz(m, R.norm(QN.clr(e1))), S.Zpos{QN.den(e2)}), S.Z.mul(EL.cz(m, R.norm(QN.clr(e2))), S.Zpos{QN.den(e1)})) == S.Z0{} : S.Z}:
  cross(EL.cz(m, R.norm(QN.clr(e1))), EL.cz(m, R.norm(QN.clr(e2))), QN.den(e1), QN.den(e2), QN.SD.fa(QN.sd(QN.den(e1), QN.den(e2))), QN.SD.fb(QN.sd(QN.den(e1), QN.den(e2))), QN.SD.d(QN.sd(QN.den(e1), QN.den(e2))), QN.sd_a(QN.den(e1), QN.den(e2)), QN.sd_b(QN.den(e1), QN.den(e2)), coef_zero.f(e1, e2, m, nil))

# an identity has equal coefficients at every monomial
def ident_coef(+e1: E.QExpr, +e2: E.QExpr, hi: SV.Ident(e1, e2), +m: List<&2, Nat>) -> S.Q.eq(coef(e1, m), coef(e2, m)):
  Equal.sym(S.Z, S.Z.mul(EL.cz(m, R.norm(QN.clr(e2))), S.Zpos{QN.den(e1)}), S.Z.mul(EL.cz(m, R.norm(QN.clr(e1))), S.Zpos{QN.den(e2)}),
    ZO.sub_eq(S.Z.mul(EL.cz(m, R.norm(QN.clr(e2))), S.Zpos{QN.den(e1)}), S.Z.mul(EL.cz(m, R.norm(QN.clr(e1))), S.Zpos{QN.den(e2)}),
      coef_zero(e1, e2, m, QN.nil_of(R.norm(QN.clr(E.QSub{e1, e2})), ID.qzero_ident(e1, e2, hi)))))
