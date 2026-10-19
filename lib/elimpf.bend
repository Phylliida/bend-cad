# bend-cad: the degree-0 elimination's invariants (PLAN-sk13a S2), at the
# level of integer coefficients. B is the basis, in order; NE(e) is e's
# cleared normal form; zv(m, B) lists the basis' coefficients at the
# monomial m.
# - A row records how it was made: its polynomial and
#   comb2(bt, B_j, cb, B) = bt NE(B_j) + cb . NE(B) have the same
#   coefficients (same), j being the length of cb, its position.
# - The rows are in echelon form (rinv): each is reduced, nonzero at its
#   pivot, and every later row is 0 there.
# - Reducing an equation e against the rows (EL.resid) gives a residual,
#   reduced, 0 at every pivot, whose coefficient at every m is
#   bt NE(e) + cb . zv(m, B) (resid_rel), with cb as long as B.
# - A nonzero residual extends the rows, and the basis by e (new_rinv).
# What a residual means for derivability is lib/indpf.bend. Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ./natring.bend as NR
import ./zring.bend as R
import ./nat.bend as N
import ./zlaws.bend as ZL
import ./zord.bend as ZO
import ./karith.bend as KA
import ./qnorm.bend as QN
import ./redpoly.bend as RP
import ./elim.bend as EL
import ./coefpf.bend as CF

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Normal forms and combinations
# -----------------------------

def NE(e: E.QExpr) -> List<&2, R.ZTerm>:
  R.norm(QN.clr(e))

# the coefficients of the basis at m
def zv(+m: List<&2, Nat>, B: List<&2, E.QExpr>) -> List<&2, S.Z>:
  match B:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      Con{EL.cz(m, NE(b)), zv(m, t)}

# u . w, up to the shorter
def zdot(u: List<&2, S.Z>, w: List<&2, S.Z>) -> S.Z:
  match u w:
    case Nil{} Nil{}:
      S.Z0{}
    case Nil{} Con{y, s}:
      S.Z0{}
    case Con{x, t} Nil{}:
      S.Z0{}
    case Con{x, t} Con{y, s}:
      S.Z.add(S.Z.mul(x, y), zdot(t, s))

# u . NE(B), as a polynomial
def comb(u: List<&2, S.Z>, B: List<&2, E.QExpr>) -> List<&2, R.ZTerm>:
  match u B:
    case Nil{} Nil{}:
      Nil{}
    case Nil{} Con{b, t}:
      Nil{}
    case Con{x, s} Nil{}:
      Nil{}
    case Con{x, s} Con{b, t}:
      R.padd(R.pscale(x, Nil{}, NE(b)), comb(s, t))

# bt NE(e) + u . NE(B)
def comb2(+bt: S.Pos, e: E.QExpr, u: List<&2, S.Z>, B: List<&2, E.QExpr>) -> List<&2, R.ZTerm>:
  R.padd(R.pscale(S.Zpos{bt}, Nil{}, NE(e)), comb(u, B))

def isnil(p: List<&2, R.ZTerm>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{h, t}:
      False{}

def nil_of(p: List<&2, R.ZTerm>, h: {isnil(p) == True{} : Bool}) -> {Nil{} == p : List<&2, R.ZTerm>}:
  match p:
    case Nil{}:
      {==}
    case Con{t, r}:
      absurd({Nil{} == Con{t, r} : List<&2, R.ZTerm>}, KA.ft(h))

# p and q have the same coefficients (both being reduced)
def same(+p: List<&2, R.ZTerm>, q: List<&2, R.ZTerm>) -> Bool:
  isnil(R.padd(p, R.pneg(q)))

def vlen(u: List<&2, S.Z>) -> Nat:
  match u:
    case Nil{}:
      0n
    case Con{x, t}:
      1n+vlen(t)

def iszero(z: S.Z) -> Bool:
  match z:
    case S.Z0{}:
      True{}
    case S.Zpos{p}:
      False{}
    case S.Zneg{p}:
      False{}

def zero_of(z: S.Z, h: {iszero(z) == True{} : Bool}) -> {z == S.Z0{} : S.Z}:
  match z:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      absurd({S.Zpos{p} == S.Z0{} : S.Z}, KA.ft(h))
    case S.Zneg{p}:
      absurd({S.Zneg{p} == S.Z0{} : S.Z}, KA.ft(h))

def iszero_of(+z: S.Z, h: {z == S.Z0{} : S.Z}) -> {iszero(z) == True{} : Bool}:
  %Equal.sym(S.Z, z, S.Z0{}, h) : {iszero(_) == True{} : Bool}
  {==}

# Coefficients of combinations
# ----------------------------

def cz_comb(+m: List<&2, Nat>, u: List<&2, S.Z>, B: List<&2, E.QExpr>) -> {zdot(u, zv(m, B)) == EL.cz(m, comb(u, B)) : S.Z}:
  match u B:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, t}:
      {==}
    case Con{x, s} Nil{}:
      {==}
    case Con{+x, +s} Con{+b, +t}:
      %CF.cz_padd(m, R.pscale(x, Nil{}, NE(b)), comb(s, t)) : {zdot(Con{x, s}, zv(m, Con{b, t})) == _ : S.Z}
      %CF.cz_pscale0(m, x, NE(b)) : {zdot(Con{x, s}, zv(m, Con{b, t})) == S.Z.add(_, EL.cz(m, comb(s, t))) : S.Z}
      %cz_comb(m, s, t) : {zdot(Con{x, s}, zv(m, Con{b, t})) == S.Z.add(S.Z.mul(x, EL.cz(m, NE(b))), _) : S.Z}
      {==}

def cz_comb2(+m: List<&2, Nat>, +bt: S.Pos, +e: E.QExpr, +u: List<&2, S.Z>, +B: List<&2, E.QExpr>)
  -> {S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, NE(e))), zdot(u, zv(m, B))) == EL.cz(m, comb2(bt, e, u, B)) : S.Z}:
  %CF.cz_padd(m, R.pscale(S.Zpos{bt}, Nil{}, NE(e)), comb(u, B)) : {S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, NE(e))), zdot(u, zv(m, B))) == _ : S.Z}
  %CF.cz_pscale0(m, S.Zpos{bt}, NE(e)) : {S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, NE(e))), zdot(u, zv(m, B))) == S.Z.add(_, EL.cz(m, comb(u, B))) : S.Z}
  %cz_comb(m, u, B) : {S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, NE(e))), zdot(u, zv(m, B))) == S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, NE(e))), _) : S.Z}
  {==}

def comb_red(u: List<&2, S.Z>, B: List<&2, E.QExpr>) -> {RP.red(comb(u, B)) == True{} : Bool}:
  match u B:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, t}:
      {==}
    case Con{x, s} Nil{}:
      {==}
    case Con{+x, +s} Con{+b, +t}:
      RP.padd_red(R.pscale(x, Nil{}, NE(b)), comb(s, t), RP.pscale_red(x, Nil{}, NE(b), RP.norm_red(QN.clr(b))), comb_red(s, t))

def comb2_red(+bt: S.Pos, +e: E.QExpr, +u: List<&2, S.Z>, +B: List<&2, E.QExpr>) -> {RP.red(comb2(bt, e, u, B)) == True{} : Bool}:
  RP.padd_red(R.pscale(S.Zpos{bt}, Nil{}, NE(e)), comb(u, B), RP.pscale_red(S.Zpos{bt}, Nil{}, NE(e), RP.norm_red(QN.clr(e))), comb_red(u, B))

# Reduced polynomials and their coefficients
# ------------------------------------------

# below every monomial of p: coefficient 0
def cz_lts(+n: List<&2, Nat>, p: List<&2, R.ZTerm>, h: {RP.mlts(n, p) == True{} : Bool}) -> {EL.cz(n, p) == S.Z0{} : S.Z}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{+d, +k}, +rest}:
      +h2 = h
      %RP.of_lt(NR.mcmp(n, k), KA.band_l(RP.islt(NR.mcmp(n, k)), RP.mlts(n, rest), h2)) : {S.Z.add(EL.ifz(EL.iseq(_), d), EL.cz(n, rest)) == S.Z0{} : S.Z}
      cz_lts(n, rest, KA.band_r(RP.islt(NR.mcmp(n, k)), RP.mlts(n, rest), h2))

def head_zero(+c: S.Z, +n: List<&2, Nat>, +rest: List<&2, R.ZTerm>, h: {EL.cz(n, Con{R.ZTerm{c, n}, rest}) == S.Z0{} : S.Z}, hl: {RP.mlts(n, rest) == True{} : Bool}) -> {c == S.Z0{} : S.Z}:
  %Equal.sym(S.Z, c, S.Z.add(c, S.Z0{}), ZL.add_zero(c)) : {_ == S.Z0{} : S.Z}
  %cz_lts(n, rest, hl) : {S.Z.add(c, _) == S.Z0{} : S.Z}
  %Equal.sym(Cmp, EQ{}, NR.mcmp(n, n), RP.mcmp_refl(n)) : {S.Z.add(EL.ifz(EL.iseq(_), c), EL.cz(n, rest)) == S.Z0{} : S.Z}
  h

# a reduced polynomial with every coefficient 0 is 0
def red_zero(p: List<&2, R.ZTerm>, hr: {RP.red(p) == True{} : Bool}, hz: @m: List<&2, Nat> -> {EL.cz(m, p) == S.Z0{} : S.Z}) -> {isnil(p) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{+c, +n}, +rest}:
      +hr2 = hr
      absurd({isnil(Con{R.ZTerm{c, n}, rest}) == True{} : Bool}, KA.ft(
        (%head_zero(c, n, rest, hz(n), RP.red_l(c, n, rest, hr2)) : {RP.nz(_) == True{} : Bool}
         RP.red_c(c, n, rest, hr2))))

def same_cz(+p: List<&2, R.ZTerm>, +q: List<&2, R.ZTerm>, h: {same(p, q) == True{} : Bool}, +m: List<&2, Nat>) -> {EL.cz(m, p) == EL.cz(m, q) : S.Z}:
  Equal.sym(S.Z, EL.cz(m, q), EL.cz(m, p), ZO.sub_eq(EL.cz(m, q), EL.cz(m, p),
    (%Equal.sym(S.Z, S.Z.neg(EL.cz(m, q)), EL.cz(m, R.pneg(q)), CF.cz_pneg(m, q)) : {S.Z.add(EL.cz(m, p), _) == S.Z0{} : S.Z}
     %Equal.sym(S.Z, S.Z.add(EL.cz(m, p), EL.cz(m, R.pneg(q))), EL.cz(m, R.padd(p, R.pneg(q))), CF.cz_padd(m, p, R.pneg(q))) : {_ == S.Z0{} : S.Z}
     %nil_of(R.padd(p, R.pneg(q)), h) : {EL.cz(m, _) == S.Z0{} : S.Z}
     {==})))

def same_of.at(+p: List<&2, R.ZTerm>, +q: List<&2, R.ZTerm>, +m: List<&2, Nat>, e: {EL.cz(m, p) == EL.cz(m, q) : S.Z}) -> {EL.cz(m, R.padd(p, R.pneg(q))) == S.Z0{} : S.Z}:
  %CF.cz_padd(m, p, R.pneg(q)) : {_ == S.Z0{} : S.Z}
  %CF.cz_pneg(m, q) : {S.Z.add(EL.cz(m, p), _) == S.Z0{} : S.Z}
  %Equal.sym(S.Z, EL.cz(m, p), EL.cz(m, q), e) : {S.Z.add(_, S.Z.neg(EL.cz(m, q))) == S.Z0{} : S.Z}
  R.ring_eq([EL.cz(m, q)], E.ZAdd{E.ZVar{0n}, E.ZNeg{E.ZVar{0n}}}, E.ZCst{S.Z0{}}, {==})

def same_of.fn(+p: List<&2, R.ZTerm>, +q: List<&2, R.ZTerm>, hz: @m: List<&2, Nat> -> {EL.cz(m, p) == EL.cz(m, q) : S.Z}, +m: List<&2, Nat>) -> {EL.cz(m, R.padd(p, R.pneg(q))) == S.Z0{} : S.Z}:
  same_of.at(p, q, m, hz(m))

# reduced polynomials with equal coefficients everywhere are the same
def same_of(+p: List<&2, R.ZTerm>, +q: List<&2, R.ZTerm>, hp: {RP.red(p) == True{} : Bool}, hq: {RP.red(q) == True{} : Bool},
  hz: @m: List<&2, Nat> -> {EL.cz(m, p) == EL.cz(m, q) : S.Z}) -> {same(p, q) == True{} : Bool}:
  red_zero(R.padd(p, R.pneg(q)), RP.padd_red(p, R.pneg(q), hp, RP.pneg_red(q, hq)), m => same_of.fn(p, q, hz, m))

# The pivot's coefficient is nonzero
# ----------------------------------

def mcmp_lt.dec(o: Cmp, +a: List<&2, Nat>, +b: List<&2, Nat>, +e: {LT{} == NR.mcmp(a, b) : Cmp}, eo: {o == NR.mcmp(b, a) : Cmp}) -> {GT{} == NR.mcmp(b, a) : Cmp}:
  match o:
    case LT{}:
      (%Equal.trans(Cmp, LT{}, NR.mcmp(a, a), EQ{}, RP.mlt_trans(a, b, a, e, eo), Equal.sym(Cmp, EQ{}, NR.mcmp(a, a), RP.mcmp_refl(a))) : NR.CmpD(_, Unit, {GT{} == NR.mcmp(b, a) : Cmp}, Unit)
       Unit{})
    case EQ{}:
      (%Equal.trans(Cmp, LT{}, NR.mcmp(a, a), EQ{},
          (%NR.mcmp_eq(b, a, eo) : {LT{} == NR.mcmp(a, _) : Cmp}
           e),
          Equal.sym(Cmp, EQ{}, NR.mcmp(a, a), RP.mcmp_refl(a))) : NR.CmpD(_, Unit, {GT{} == NR.mcmp(b, a) : Cmp}, Unit)
       Unit{})
    case GT{}:
      eo

def mcmp_lt(+a: List<&2, Nat>, +b: List<&2, Nat>, +e: {LT{} == NR.mcmp(a, b) : Cmp}) -> {GT{} == NR.mcmp(b, a) : Cmp}:
  mcmp_lt.dec(NR.mcmp(b, a), a, b, e, {==})

# m below a list's terms is below its last monomial
def lts_pivot(r2: List<&2, R.ZTerm>, +m: List<&2, Nat>, d: S.Z, +n: List<&2, Nat>, h: {RP.mlts(m, Con{R.ZTerm{d, n}, r2}) == True{} : Bool}) -> {RP.islt(NR.mcmp(m, EL.pivot.go(r2, n))) == True{} : Bool}:
  match r2:
    case Nil{}:
      KA.band_l(RP.islt(NR.mcmp(m, n)), RP.mlts(m, Nil{}), h)
    case Con{R.ZTerm{+e, +k}, +r3}:
      lts_pivot(r3, m, e, k, KA.band_r(RP.islt(NR.mcmp(m, n)), RP.mlts(m, Con{R.ZTerm{e, k}, r3}), h))

def piv_nz(rest: List<&2, R.ZTerm>, +c: S.Z, +m: List<&2, Nat>, +hr: {RP.red(Con{R.ZTerm{c, m}, rest}) == True{} : Bool}) -> {RP.nz(EL.cz(EL.pivot.go(rest, m), Con{R.ZTerm{c, m}, rest})) == True{} : Bool}:
  match rest:
    case Nil{}:
      %RP.mcmp_refl(m) : {RP.nz(S.Z.add(EL.ifz(EL.iseq(_), c), S.Z0{})) == True{} : Bool}
      %ZL.add_zero(c) : {RP.nz(_) == True{} : Bool}
      RP.red_c(c, m, Nil{}, hr)
    case Con{R.ZTerm{+d, +n}, +r2}:
      %mcmp_lt(m, EL.pivot.go(r2, n), RP.of_lt(NR.mcmp(m, EL.pivot.go(r2, n)), lts_pivot(r2, m, d, n, RP.red_l(c, m, Con{R.ZTerm{d, n}, r2}, hr))))
        : {RP.nz(S.Z.add(EL.ifz(EL.iseq(_), c), EL.cz(EL.pivot.go(r2, n), Con{R.ZTerm{d, n}, r2}))) == True{} : Bool}
      piv_nz(r2, d, n, RP.red_r(c, m, Con{R.ZTerm{d, n}, r2}, hr))

# a reduced polynomial other than 0 is nonzero at its pivot
def pivot_nz(p: List<&2, R.ZTerm>, hr: {RP.red(p) == True{} : Bool}, hne: {isnil(p) == False{} : Bool}) -> {RP.nz(EL.cz(EL.pivot(p), p)) == True{} : Bool}:
  match p:
    case Nil{}:
      absurd({RP.nz(EL.cz(EL.pivot(Nil{}), Nil{})) == True{} : Bool}, KA.tf(hne))
    case Con{R.ZTerm{+c, +m}, +rest}:
      piv_nz(rest, c, m, hr)

# Dot products
# ------------

def zdot_nil(z: List<&2, S.Z>) -> {S.Z0{} == zdot(Nil{}, z) : S.Z}:
  match z:
    case Nil{}:
      {==}
    case Con{y, s}:
      {==}

def zdot_vadd(u: List<&2, S.Z>, w: List<&2, S.Z>, z: List<&2, S.Z>) -> {S.Z.add(zdot(u, z), zdot(w, z)) == zdot(EL.vadd(u, w), z) : S.Z}:
  match u w z:
    case Nil{} Nil{} Nil{}:
      {==}
    case Nil{} Nil{} Con{y, s}:
      {==}
    case Nil{} Con{x2, t2} Nil{}:
      {==}
    case Nil{} Con{x2, t2} Con{y, s}:
      {==}
    case Con{x, t} Nil{} Nil{}:
      {==}
    case Con{+x, +t} Nil{} Con{+y, +s}:
      Equal.sym(S.Z, S.Z.add(S.Z.mul(x, y), zdot(t, s)), S.Z.add(S.Z.add(S.Z.mul(x, y), zdot(t, s)), S.Z0{}), ZL.add_zero(S.Z.add(S.Z.mul(x, y), zdot(t, s))))
    case Con{x, t} Con{x2, t2} Nil{}:
      {==}
    case Con{+x, +t} Con{+x2, +t2} Con{+y, +s}:
      %zdot_vadd(t, t2, s) : {S.Z.add(zdot(Con{x, t}, Con{y, s}), zdot(Con{x2, t2}, Con{y, s})) == S.Z.add(S.Z.mul(S.Z.add(x, x2), y), _) : S.Z}
      R.ring_eq([x, x2, y, zdot(t, s), zdot(t2, s)],
        E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{3n}}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{4n}}},
        E.ZAdd{E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZAdd{E.ZVar{3n}, E.ZVar{4n}}}, {==})

def zdot_vscale(+k: S.Z, u: List<&2, S.Z>, z: List<&2, S.Z>) -> {S.Z.mul(k, zdot(u, z)) == zdot(EL.vscale(k, u), z) : S.Z}:
  match u z:
    case Nil{} Nil{}:
      Equal.sym(S.Z, S.Z0{}, S.Z.mul(k, S.Z0{}), ZL.mul_zero(k))
    case Nil{} Con{y, s}:
      Equal.sym(S.Z, S.Z0{}, S.Z.mul(k, S.Z0{}), ZL.mul_zero(k))
    case Con{x, t} Nil{}:
      Equal.sym(S.Z, S.Z0{}, S.Z.mul(k, S.Z0{}), ZL.mul_zero(k))
    case Con{+x, +t} Con{+y, +s}:
      %zdot_vscale(k, t, s) : {S.Z.mul(k, zdot(Con{x, t}, Con{y, s})) == S.Z.add(S.Z.mul(S.Z.mul(k, x), y), _) : S.Z}
      R.ring_eq([k, x, y, zdot(t, s)],
        E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{3n}}},
        E.ZAdd{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}, {==})

# appending x adds x times the entry at the old length
def zdot_vsnoc(u: List<&2, S.Z>, +x: S.Z, z: List<&2, S.Z>) -> {S.Z.add(zdot(u, z), S.Z.mul(x, E.lookup(z, vlen(u)))) == zdot(EL.vsnoc(u, x), z) : S.Z}:
  match u z:
    case Nil{} Nil{}:
      Equal.sym(S.Z, S.Z0{}, S.Z.mul(x, S.Z0{}), ZL.mul_zero(x))
    case Nil{} Con{+y, +s}:
      %zdot_nil(s) : {S.Z.mul(x, y) == S.Z.add(S.Z.mul(x, y), _) : S.Z}
      ZL.add_zero(S.Z.mul(x, y))
    case Con{a, t} Nil{}:
      Equal.sym(S.Z, S.Z0{}, S.Z.mul(x, S.Z0{}), ZL.mul_zero(x))
    case Con{+a, +t} Con{+y, +s}:
      %zdot_vsnoc(t, x, s) : {S.Z.add(zdot(Con{a, t}, Con{y, s}), S.Z.mul(x, E.lookup(s, vlen(t)))) == S.Z.add(S.Z.mul(a, y), _) : S.Z}
      Equal.sym(S.Z, S.Z.add(S.Z.mul(a, y), S.Z.add(zdot(t, s), S.Z.mul(x, E.lookup(s, vlen(t))))), S.Z.add(S.Z.add(S.Z.mul(a, y), zdot(t, s)), S.Z.mul(x, E.lookup(s, vlen(t)))),
        ZL.add_assoc(S.Z.mul(a, y), zdot(t, s), S.Z.mul(x, E.lookup(s, vlen(t)))))

def zdot_zeros(n: Nat, z: List<&2, S.Z>) -> {S.Z0{} == zdot(EL.zeros(n), z) : S.Z}:
  match n z:
    case 0n z:
      zdot_nil(z)
    case 1n+k Nil{}:
      {==}
    case 1n+k Con{y, s}:
      zdot_zeros(k, s)

# entry j of zv(m, B): the coefficient of equation j (0 past the end)
def lookup_zv(+m: List<&2, Nat>, B: List<&2, E.QExpr>, j: Nat) -> {EL.cz(m, NE(SV.eqat(B, j))) == E.lookup(zv(m, B), j) : S.Z}:
  match B j:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+i:
      {==}
    case Con{b, t} 0n:
      {==}
    case Con{b, t} 1n+i:
      lookup_zv(m, t, i)

# The residual's relation
# -----------------------

# one step's algebra, a nonzero: |b| r - sgn(b) a R keeps the relation
def step_rel.nz(+m: List<&2, Nat>, +a: S.Z, +b: S.Z, +rp: List<&2, R.ZTerm>, +rcb: List<&2, S.Z>, +rbt: S.Pos, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +e: E.QExpr, +B: List<&2, E.QExpr>,
  hr: {EL.cz(m, rp) == S.Z.add(S.Z.mul(S.Zpos{rbt}, EL.cz(m, NE(e))), zdot(rcb, zv(m, B))) : S.Z}, hR: {EL.cz(m, p) == S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, NE(SV.eqat(B, vlen(cb))))), zdot(cb, zv(m, B))) : S.Z})
  -> {EL.cz(m, R.padd(R.pscale(S.Zpos{EL.babs(b)}, Nil{}, rp), R.pneg(R.pscale(EL.bsgn(b, a), Nil{}, p)))) == S.Z.add(S.Z.mul(S.Zpos{S.Pos.mul(EL.babs(b), rbt)}, EL.cz(m, NE(e))), zdot(EL.vadd(EL.vscale(S.Zpos{EL.babs(b)}, rcb), EL.vscale(S.Z.neg(EL.bsgn(b, a)), EL.vsnoc(cb, S.Zpos{bt}))), zv(m, B))) : S.Z}:
  %CF.cz_padd(m, R.pscale(S.Zpos{EL.babs(b)}, Nil{}, rp), R.pneg(R.pscale(EL.bsgn(b, a), Nil{}, p))) : {_ == S.Z.add(S.Z.mul(S.Zpos{S.Pos.mul(EL.babs(b), rbt)}, EL.cz(m, NE(e))), zdot(EL.vadd(EL.vscale(S.Zpos{EL.babs(b)}, rcb), EL.vscale(S.Z.neg(EL.bsgn(b, a)), EL.vsnoc(cb, S.Zpos{bt}))), zv(m, B))) : S.Z}
  %CF.cz_pneg(m, R.pscale(EL.bsgn(b, a), Nil{}, p)) : {S.Z.add(EL.cz(m, R.pscale(S.Zpos{EL.babs(b)}, Nil{}, rp)), _) == S.Z.add(S.Z.mul(S.Zpos{S.Pos.mul(EL.babs(b), rbt)}, EL.cz(m, NE(e))), zdot(EL.vadd(EL.vscale(S.Zpos{EL.babs(b)}, rcb), EL.vscale(S.Z.neg(EL.bsgn(b, a)), EL.vsnoc(cb, S.Zpos{bt}))), zv(m, B))) : S.Z}
  %CF.cz_pscale0(m, S.Zpos{EL.babs(b)}, rp) : {S.Z.add(_, S.Z.neg(EL.cz(m, R.pscale(EL.bsgn(b, a), Nil{}, p)))) == S.Z.add(S.Z.mul(S.Zpos{S.Pos.mul(EL.babs(b), rbt)}, EL.cz(m, NE(e))), zdot(EL.vadd(EL.vscale(S.Zpos{EL.babs(b)}, rcb), EL.vscale(S.Z.neg(EL.bsgn(b, a)), EL.vsnoc(cb, S.Zpos{bt}))), zv(m, B))) : S.Z}
  %CF.cz_pscale0(m, EL.bsgn(b, a), p) : {S.Z.add(S.Z.mul(S.Zpos{EL.babs(b)}, EL.cz(m, rp)), S.Z.neg(_)) == S.Z.add(S.Z.mul(S.Zpos{S.Pos.mul(EL.babs(b), rbt)}, EL.cz(m, NE(e))), zdot(EL.vadd(EL.vscale(S.Zpos{EL.babs(b)}, rcb), EL.vscale(S.Z.neg(EL.bsgn(b, a)), EL.vsnoc(cb, S.Zpos{bt}))), zv(m, B))) : S.Z}
  %Equal.sym(S.Z, EL.cz(m, rp), S.Z.add(S.Z.mul(S.Zpos{rbt}, EL.cz(m, NE(e))), zdot(rcb, zv(m, B))), hr) : {S.Z.add(S.Z.mul(S.Zpos{EL.babs(b)}, _), S.Z.neg(S.Z.mul(EL.bsgn(b, a), EL.cz(m, p)))) == S.Z.add(S.Z.mul(S.Zpos{S.Pos.mul(EL.babs(b), rbt)}, EL.cz(m, NE(e))), zdot(EL.vadd(EL.vscale(S.Zpos{EL.babs(b)}, rcb), EL.vscale(S.Z.neg(EL.bsgn(b, a)), EL.vsnoc(cb, S.Zpos{bt}))), zv(m, B))) : S.Z}
  %Equal.sym(S.Z, EL.cz(m, p), S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, NE(SV.eqat(B, vlen(cb))))), zdot(cb, zv(m, B))), hR) : {S.Z.add(S.Z.mul(S.Zpos{EL.babs(b)}, S.Z.add(S.Z.mul(S.Zpos{rbt}, EL.cz(m, NE(e))), zdot(rcb, zv(m, B)))), S.Z.neg(S.Z.mul(EL.bsgn(b, a), _))) == S.Z.add(S.Z.mul(S.Zpos{S.Pos.mul(EL.babs(b), rbt)}, EL.cz(m, NE(e))), zdot(EL.vadd(EL.vscale(S.Zpos{EL.babs(b)}, rcb), EL.vscale(S.Z.neg(EL.bsgn(b, a)), EL.vsnoc(cb, S.Zpos{bt}))), zv(m, B))) : S.Z}
  %zdot_vadd(EL.vscale(S.Zpos{EL.babs(b)}, rcb), EL.vscale(S.Z.neg(EL.bsgn(b, a)), EL.vsnoc(cb, S.Zpos{bt})), zv(m, B)) : {S.Z.add(S.Z.mul(S.Zpos{EL.babs(b)}, S.Z.add(S.Z.mul(S.Zpos{rbt}, EL.cz(m, NE(e))), zdot(rcb, zv(m, B)))), S.Z.neg(S.Z.mul(EL.bsgn(b, a), S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, NE(SV.eqat(B, vlen(cb))))), zdot(cb, zv(m, B)))))) == S.Z.add(S.Z.mul(S.Zpos{S.Pos.mul(EL.babs(b), rbt)}, EL.cz(m, NE(e))), _) : S.Z}
  %zdot_vscale(S.Zpos{EL.babs(b)}, rcb, zv(m, B)) : {S.Z.add(S.Z.mul(S.Zpos{EL.babs(b)}, S.Z.add(S.Z.mul(S.Zpos{rbt}, EL.cz(m, NE(e))), zdot(rcb, zv(m, B)))), S.Z.neg(S.Z.mul(EL.bsgn(b, a), S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, NE(SV.eqat(B, vlen(cb))))), zdot(cb, zv(m, B)))))) == S.Z.add(S.Z.mul(S.Zpos{S.Pos.mul(EL.babs(b), rbt)}, EL.cz(m, NE(e))), S.Z.add(_, zdot(EL.vscale(S.Z.neg(EL.bsgn(b, a)), EL.vsnoc(cb, S.Zpos{bt})), zv(m, B)))) : S.Z}
  %zdot_vscale(S.Z.neg(EL.bsgn(b, a)), EL.vsnoc(cb, S.Zpos{bt}), zv(m, B)) : {S.Z.add(S.Z.mul(S.Zpos{EL.babs(b)}, S.Z.add(S.Z.mul(S.Zpos{rbt}, EL.cz(m, NE(e))), zdot(rcb, zv(m, B)))), S.Z.neg(S.Z.mul(EL.bsgn(b, a), S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, NE(SV.eqat(B, vlen(cb))))), zdot(cb, zv(m, B)))))) == S.Z.add(S.Z.mul(S.Zpos{S.Pos.mul(EL.babs(b), rbt)}, EL.cz(m, NE(e))), S.Z.add(S.Z.mul(S.Zpos{EL.babs(b)}, zdot(rcb, zv(m, B))), _)) : S.Z}
  %zdot_vsnoc(cb, S.Zpos{bt}, zv(m, B)) : {S.Z.add(S.Z.mul(S.Zpos{EL.babs(b)}, S.Z.add(S.Z.mul(S.Zpos{rbt}, EL.cz(m, NE(e))), zdot(rcb, zv(m, B)))), S.Z.neg(S.Z.mul(EL.bsgn(b, a), S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, NE(SV.eqat(B, vlen(cb))))), zdot(cb, zv(m, B)))))) == S.Z.add(S.Z.mul(S.Zpos{S.Pos.mul(EL.babs(b), rbt)}, EL.cz(m, NE(e))), S.Z.add(S.Z.mul(S.Zpos{EL.babs(b)}, zdot(rcb, zv(m, B))), S.Z.mul(S.Z.neg(EL.bsgn(b, a)), _))) : S.Z}
  %lookup_zv(m, B, vlen(cb)) : {S.Z.add(S.Z.mul(S.Zpos{EL.babs(b)}, S.Z.add(S.Z.mul(S.Zpos{rbt}, EL.cz(m, NE(e))), zdot(rcb, zv(m, B)))), S.Z.neg(S.Z.mul(EL.bsgn(b, a), S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, NE(SV.eqat(B, vlen(cb))))), zdot(cb, zv(m, B)))))) == S.Z.add(S.Z.mul(S.Zpos{S.Pos.mul(EL.babs(b), rbt)}, EL.cz(m, NE(e))), S.Z.add(S.Z.mul(S.Zpos{EL.babs(b)}, zdot(rcb, zv(m, B))), S.Z.mul(S.Z.neg(EL.bsgn(b, a)), S.Z.add(zdot(cb, zv(m, B)), S.Z.mul(S.Zpos{bt}, _))))) : S.Z}
  R.ring_eq([S.Zpos{EL.babs(b)}, S.Zpos{rbt}, EL.cz(m, NE(e)), zdot(rcb, zv(m, B)), EL.bsgn(b, a), S.Zpos{bt}, EL.cz(m, NE(SV.eqat(B, vlen(cb)))), zdot(cb, zv(m, B))],
    E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{3n}}}, E.ZNeg{E.ZMul{E.ZVar{4n}, E.ZAdd{E.ZMul{E.ZVar{5n}, E.ZVar{6n}}, E.ZVar{7n}}}}},
    E.ZAdd{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZNeg{E.ZVar{4n}}, E.ZAdd{E.ZVar{7n}, E.ZMul{E.ZVar{5n}, E.ZVar{6n}}}}}}, {==})

# r's relation at m: r.p = bt NE(e) + cb . NE(B) there
def Rel(+m: List<&2, Nat>, r: EL.Res, e: E.QExpr, B: List<&2, E.QExpr>) -> Type:
  match r:
    case EL.Res{p, cb, bt}:
      {EL.cz(m, p) == S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, NE(e))), zdot(cb, zv(m, B))) : S.Z}

# a row: reduced, nonzero at its pivot, made from its equation (at its
# position, the length of cb) and the earlier ones
def rowok(+B: List<&2, E.QExpr>, row: EL.Row) -> Bool:
  match row:
    case EL.Row{+p, +cb, +bt, +pv}:
      KA.band(RP.red(p), KA.band(RP.nz(EL.cz(pv, p)), same(p, comb2(bt, SV.eqat(B, vlen(cb)), cb, B))))

def rowok_red(+B: List<&2, E.QExpr>, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +pv: List<&2, Nat>, h: {rowok(B, EL.Row{p, cb, bt, pv}) == True{} : Bool}) -> {RP.red(p) == True{} : Bool}:
  KA.band_l(RP.red(p), KA.band(RP.nz(EL.cz(pv, p)), same(p, comb2(bt, SV.eqat(B, vlen(cb)), cb, B))), h)

def rowok_nz(+B: List<&2, E.QExpr>, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +pv: List<&2, Nat>, h: {rowok(B, EL.Row{p, cb, bt, pv}) == True{} : Bool}) -> {RP.nz(EL.cz(pv, p)) == True{} : Bool}:
  KA.band_l(RP.nz(EL.cz(pv, p)), same(p, comb2(bt, SV.eqat(B, vlen(cb)), cb, B)), KA.band_r(RP.red(p), KA.band(RP.nz(EL.cz(pv, p)), same(p, comb2(bt, SV.eqat(B, vlen(cb)), cb, B))), h))

def rowok_same(+B: List<&2, E.QExpr>, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +pv: List<&2, Nat>, h: {rowok(B, EL.Row{p, cb, bt, pv}) == True{} : Bool}) -> {same(p, comb2(bt, SV.eqat(B, vlen(cb)), cb, B)) == True{} : Bool}:
  KA.band_r(RP.nz(EL.cz(pv, p)), same(p, comb2(bt, SV.eqat(B, vlen(cb)), cb, B)), KA.band_r(RP.red(p), KA.band(RP.nz(EL.cz(pv, p)), same(p, comb2(bt, SV.eqat(B, vlen(cb)), cb, B))), h))

def rowok_mk(+B: List<&2, E.QExpr>, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +pv: List<&2, Nat>, hr: {RP.red(p) == True{} : Bool}, hn: {RP.nz(EL.cz(pv, p)) == True{} : Bool},
  hs: {same(p, comb2(bt, SV.eqat(B, vlen(cb)), cb, B)) == True{} : Bool}) -> {rowok(B, EL.Row{p, cb, bt, pv}) == True{} : Bool}:
  KA.band_i(RP.red(p), KA.band(RP.nz(EL.cz(pv, p)), same(p, comb2(bt, SV.eqat(B, vlen(cb)), cb, B))), hr, KA.band_i(RP.nz(EL.cz(pv, p)), same(p, comb2(bt, SV.eqat(B, vlen(cb)), cb, B)), hn, hs))

# a row's relation at m
def row_rel(+m: List<&2, Nat>, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +B: List<&2, E.QExpr>, hs: {same(p, comb2(bt, SV.eqat(B, vlen(cb)), cb, B)) == True{} : Bool})
  -> {EL.cz(m, p) == S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, NE(SV.eqat(B, vlen(cb))))), zdot(cb, zv(m, B))) : S.Z}:
  Equal.trans(S.Z, EL.cz(m, p), EL.cz(m, comb2(bt, SV.eqat(B, vlen(cb)), cb, B)), S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, NE(SV.eqat(B, vlen(cb))))), zdot(cb, zv(m, B))),
    same_cz(p, comb2(bt, SV.eqat(B, vlen(cb)), cb, B), hs, m),
    Equal.sym(S.Z, S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, NE(SV.eqat(B, vlen(cb))))), zdot(cb, zv(m, B))), EL.cz(m, comb2(bt, SV.eqat(B, vlen(cb)), cb, B)), cz_comb2(m, bt, SV.eqat(B, vlen(cb)), cb, B)))

def step_rel.go(a: S.Z, +b: S.Z, +rp: List<&2, R.ZTerm>, +rcb: List<&2, S.Z>, +rbt: S.Pos, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +m: List<&2, Nat>, +e: E.QExpr, +B: List<&2, E.QExpr>,
  hr: {EL.cz(m, rp) == S.Z.add(S.Z.mul(S.Zpos{rbt}, EL.cz(m, NE(e))), zdot(rcb, zv(m, B))) : S.Z},
  hR: {EL.cz(m, p) == S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, NE(SV.eqat(B, vlen(cb))))), zdot(cb, zv(m, B))) : S.Z})
  -> Rel(m, EL.step.go(a, b, rp, rcb, rbt, p, cb, bt), e, B):
  match a:
    case S.Z0{}:
      hr
    case S.Zpos{+q}:
      step_rel.nz(m, S.Zpos{q}, b, rp, rcb, rbt, p, cb, bt, e, B, hr, hR)
    case S.Zneg{+q}:
      step_rel.nz(m, S.Zneg{q}, b, rp, rcb, rbt, p, cb, bt, e, B, hr, hR)

def step_rel(+m: List<&2, Nat>, +row: EL.Row, +r: EL.Res, +e: E.QExpr, +B: List<&2, E.QExpr>, hok: {rowok(B, row) == True{} : Bool}, hr: Rel(m, r, e, B)) -> Rel(m, EL.step(row, r), e, B):
  match row r:
    case EL.Row{+p, +cb, +bt, +pv} EL.Res{+rp, +rcb, +rbt}:
      step_rel.go(EL.cz(pv, rp), EL.cz(pv, p), rp, rcb, rbt, p, cb, bt, m, e, B, hr, row_rel(m, p, cb, bt, B, rowok_same(B, p, cb, bt, pv, hok)))

def allok(+B: List<&2, E.QExpr>, rows: List<&2, EL.Row>) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case Con{row, t}:
      KA.band(rowok(B, row), allok(B, t))

def reduce_rel(+m: List<&2, Nat>, rows: List<&2, EL.Row>, +r: EL.Res, +e: E.QExpr, +B: List<&2, E.QExpr>, +hok: {allok(B, rows) == True{} : Bool}, hr: Rel(m, r, e, B)) -> Rel(m, EL.reduce(rows, r), e, B):
  match rows:
    case Nil{}:
      hr
    case Con{+row, +t}:
      reduce_rel(m, t, EL.step(row, r), e, B, KA.band_r(rowok(B, row), allok(B, t), hok), step_rel(m, row, r, e, B, KA.band_l(rowok(B, row), allok(B, t), hok), hr))

def start_rel(+m: List<&2, Nat>, +e: E.QExpr, +B: List<&2, E.QExpr>, +k: Nat) -> Rel(m, EL.start(e, k), e, B):
  %zdot_zeros(k, zv(m, B)) : {EL.cz(m, NE(e)) == S.Z.add(S.Z.mul(S.Zpos{S.XH{}}, EL.cz(m, NE(e))), _) : S.Z}
  %ZL.add_zero(S.Z.mul(S.Zpos{S.XH{}}, EL.cz(m, NE(e)))) : {EL.cz(m, NE(e)) == _ : S.Z}
  ZL.one_mul(EL.cz(m, NE(e)))

# the residual's relation at every m
def resid_rel(+m: List<&2, Nat>, +rows: List<&2, EL.Row>, +e: E.QExpr, +B: List<&2, E.QExpr>, +hok: {allok(B, rows) == True{} : Bool}) -> Rel(m, EL.resid(rows, e), e, B):
  reduce_rel(m, rows, EL.start(e, EL.rlen(rows)), e, B, hok, start_rel(m, e, B, EL.rlen(rows)))

# The residual is reduced
# -----------------------

def RedR(r: EL.Res) -> Bool:
  match r:
    case EL.Res{p, cb, bt}:
      RP.red(p)

def step_red.go(a: S.Z, +b: S.Z, +rp: List<&2, R.ZTerm>, +rcb: List<&2, S.Z>, +rbt: S.Pos, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos,
  +hr: {RP.red(rp) == True{} : Bool}, +hp: {RP.red(p) == True{} : Bool}) -> {RedR(EL.step.go(a, b, rp, rcb, rbt, p, cb, bt)) == True{} : Bool}:
  match a:
    case S.Z0{}:
      hr
    case S.Zpos{+q}:
      RP.padd_red(R.pscale(S.Zpos{EL.babs(b)}, Nil{}, rp), R.pneg(R.pscale(EL.bsgn(b, S.Zpos{q}), Nil{}, p)), RP.pscale_red(S.Zpos{EL.babs(b)}, Nil{}, rp, hr),
        RP.pneg_red(R.pscale(EL.bsgn(b, S.Zpos{q}), Nil{}, p), RP.pscale_red(EL.bsgn(b, S.Zpos{q}), Nil{}, p, hp)))
    case S.Zneg{+q}:
      RP.padd_red(R.pscale(S.Zpos{EL.babs(b)}, Nil{}, rp), R.pneg(R.pscale(EL.bsgn(b, S.Zneg{q}), Nil{}, p)), RP.pscale_red(S.Zpos{EL.babs(b)}, Nil{}, rp, hr),
        RP.pneg_red(R.pscale(EL.bsgn(b, S.Zneg{q}), Nil{}, p), RP.pscale_red(EL.bsgn(b, S.Zneg{q}), Nil{}, p, hp)))

def step_red(+B: List<&2, E.QExpr>, +row: EL.Row, +r: EL.Res, hok: {rowok(B, row) == True{} : Bool}, hr: {RedR(r) == True{} : Bool}) -> {RedR(EL.step(row, r)) == True{} : Bool}:
  match row r:
    case EL.Row{+p, +cb, +bt, +pv} EL.Res{+rp, +rcb, +rbt}:
      step_red.go(EL.cz(pv, rp), EL.cz(pv, p), rp, rcb, rbt, p, cb, bt, hr, rowok_red(B, p, cb, bt, pv, hok))

def reduce_red(rows: List<&2, EL.Row>, +r: EL.Res, +B: List<&2, E.QExpr>, +hok: {allok(B, rows) == True{} : Bool}, hr: {RedR(r) == True{} : Bool}) -> {RedR(EL.reduce(rows, r)) == True{} : Bool}:
  match rows:
    case Nil{}:
      hr
    case Con{+row, +t}:
      reduce_red(t, EL.step(row, r), B, KA.band_r(rowok(B, row), allok(B, t), hok), step_red(B, row, r, KA.band_l(rowok(B, row), allok(B, t), hok), hr))

def resid_red(+rows: List<&2, EL.Row>, +e: E.QExpr, +B: List<&2, E.QExpr>, +hok: {allok(B, rows) == True{} : Bool}) -> {RedR(EL.resid(rows, e)) == True{} : Bool}:
  reduce_red(rows, EL.start(e, EL.rlen(rows)), B, hok, RP.norm_red(QN.clr(e)))

# The residual is 0 at every pivot
# --------------------------------

def rowp(row: EL.Row) -> List<&2, R.ZTerm>:
  match row:
    case EL.Row{p, cb, bt, pv}:
      p

def rowpv(row: EL.Row) -> List<&2, Nat>:
  match row:
    case EL.Row{p, cb, bt, pv}:
      pv

def rowcb(row: EL.Row) -> List<&2, S.Z>:
  match row:
    case EL.Row{p, cb, bt, pv}:
      cb

def ZAt(+mu: List<&2, Nat>, r: EL.Res) -> Bool:
  match r:
    case EL.Res{p, cb, bt}:
      iszero(EL.cz(mu, p))

# every row is 0 at mu
def zat(+mu: List<&2, Nat>, rows: List<&2, EL.Row>) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case Con{row, t}:
      KA.band(iszero(EL.cz(mu, rowp(row))), zat(mu, t))

# echelon: every row's pivot is 0 in the later rows
def ech(rows: List<&2, EL.Row>) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case Con{+row, +t}:
      KA.band(zat(rowpv(row), t), ech(t))

# r is 0 at every row's pivot
def zp(rows: List<&2, EL.Row>, +r: EL.Res) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case Con{row, t}:
      KA.band(ZAt(rowpv(row), r), zp(t, r))

def zero_alg(b: S.Z, +a: S.Z, hb: {RP.nz(b) == True{} : Bool}) -> {S.Z.add(S.Z.mul(S.Zpos{EL.babs(b)}, a), S.Z.neg(S.Z.mul(EL.bsgn(b, a), b))) == S.Z0{} : S.Z}:
  match b:
    case S.Z0{}:
      absurd({S.Z.add(S.Z.mul(S.Zpos{EL.babs(S.Z0{})}, a), S.Z.neg(S.Z.mul(EL.bsgn(S.Z0{}, a), S.Z0{}))) == S.Z0{} : S.Z}, KA.ft(hb))
    case S.Zpos{+q}:
      R.ring_eq([S.Zpos{q}, a], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZNeg{E.ZMul{E.ZVar{1n}, E.ZVar{0n}}}}, E.ZCst{S.Z0{}}, {==})
    case S.Zneg{+q}:
      R.ring_eq([S.Zpos{q}, a], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZNeg{E.ZMul{E.ZNeg{E.ZVar{1n}}, E.ZNeg{E.ZVar{0n}}}}}, E.ZCst{S.Z0{}}, {==})

# the coefficient of a step's polynomial at mu
def step_cz(+mu: List<&2, Nat>, +b1: S.Z, +s: S.Z, +rp: List<&2, R.ZTerm>, +p: List<&2, R.ZTerm>)
  -> {S.Z.add(S.Z.mul(b1, EL.cz(mu, rp)), S.Z.neg(S.Z.mul(s, EL.cz(mu, p)))) == EL.cz(mu, R.padd(R.pscale(b1, Nil{}, rp), R.pneg(R.pscale(s, Nil{}, p)))) : S.Z}:
  %CF.cz_padd(mu, R.pscale(b1, Nil{}, rp), R.pneg(R.pscale(s, Nil{}, p))) : {S.Z.add(S.Z.mul(b1, EL.cz(mu, rp)), S.Z.neg(S.Z.mul(s, EL.cz(mu, p)))) == _ : S.Z}
  %CF.cz_pneg(mu, R.pscale(s, Nil{}, p)) : {S.Z.add(S.Z.mul(b1, EL.cz(mu, rp)), S.Z.neg(S.Z.mul(s, EL.cz(mu, p)))) == S.Z.add(EL.cz(mu, R.pscale(b1, Nil{}, rp)), _) : S.Z}
  %CF.cz_pscale0(mu, b1, rp) : {S.Z.add(S.Z.mul(b1, EL.cz(mu, rp)), S.Z.neg(S.Z.mul(s, EL.cz(mu, p)))) == S.Z.add(_, S.Z.neg(EL.cz(mu, R.pscale(s, Nil{}, p)))) : S.Z}
  %CF.cz_pscale0(mu, s, p) : {S.Z.add(S.Z.mul(b1, EL.cz(mu, rp)), S.Z.neg(S.Z.mul(s, EL.cz(mu, p)))) == S.Z.add(S.Z.mul(b1, EL.cz(mu, rp)), S.Z.neg(_)) : S.Z}
  {==}

def step_zero.go(a: S.Z, +b: S.Z, +rp: List<&2, R.ZTerm>, +rcb: List<&2, S.Z>, +rbt: S.Pos, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +pv: List<&2, Nat>,
  ea: {a == EL.cz(pv, rp) : S.Z}, eb: {b == EL.cz(pv, p) : S.Z}, hb: {RP.nz(b) == True{} : Bool}) -> {ZAt(pv, EL.step.go(a, b, rp, rcb, rbt, p, cb, bt)) == True{} : Bool}:
  match a:
    case S.Z0{}:
      iszero_of(EL.cz(pv, rp), Equal.sym(S.Z, S.Z0{}, EL.cz(pv, rp), ea))
    case S.Zpos{+q}:
      iszero_of(EL.cz(pv, R.padd(R.pscale(S.Zpos{EL.babs(b)}, Nil{}, rp), R.pneg(R.pscale(EL.bsgn(b, S.Zpos{q}), Nil{}, p)))),
        (%step_cz(pv, S.Zpos{EL.babs(b)}, EL.bsgn(b, S.Zpos{q}), rp, p) : {_ == S.Z0{} : S.Z}
         %ea : {S.Z.add(S.Z.mul(S.Zpos{EL.babs(b)}, _), S.Z.neg(S.Z.mul(EL.bsgn(b, S.Zpos{q}), EL.cz(pv, p)))) == S.Z0{} : S.Z}
         %eb : {S.Z.add(S.Z.mul(S.Zpos{EL.babs(b)}, S.Zpos{q}), S.Z.neg(S.Z.mul(EL.bsgn(b, S.Zpos{q}), _))) == S.Z0{} : S.Z}
         zero_alg(b, S.Zpos{q}, hb)))
    case S.Zneg{+q}:
      iszero_of(EL.cz(pv, R.padd(R.pscale(S.Zpos{EL.babs(b)}, Nil{}, rp), R.pneg(R.pscale(EL.bsgn(b, S.Zneg{q}), Nil{}, p)))),
        (%step_cz(pv, S.Zpos{EL.babs(b)}, EL.bsgn(b, S.Zneg{q}), rp, p) : {_ == S.Z0{} : S.Z}
         %ea : {S.Z.add(S.Z.mul(S.Zpos{EL.babs(b)}, _), S.Z.neg(S.Z.mul(EL.bsgn(b, S.Zneg{q}), EL.cz(pv, p)))) == S.Z0{} : S.Z}
         %eb : {S.Z.add(S.Z.mul(S.Zpos{EL.babs(b)}, S.Zneg{q}), S.Z.neg(S.Z.mul(EL.bsgn(b, S.Zneg{q}), _))) == S.Z0{} : S.Z}
         zero_alg(b, S.Zneg{q}, hb)))

# a step makes r 0 at the row's pivot
def step_zero(+B: List<&2, E.QExpr>, row: EL.Row, r: EL.Res, hok: {rowok(B, row) == True{} : Bool}) -> {ZAt(rowpv(row), EL.step(row, r)) == True{} : Bool}:
  match row r:
    case EL.Row{+p, +cb, +bt, +pv} EL.Res{+rp, +rcb, +rbt}:
      step_zero.go(EL.cz(pv, rp), EL.cz(pv, p), rp, rcb, rbt, p, cb, bt, pv, {==}, {==}, rowok_nz(B, p, cb, bt, pv, hok))

def keep_alg(+b1: S.Z, +s: S.Z, +x: S.Z, +y: S.Z, hx: {x == S.Z0{} : S.Z}, hy: {y == S.Z0{} : S.Z}) -> {S.Z.add(S.Z.mul(b1, x), S.Z.neg(S.Z.mul(s, y))) == S.Z0{} : S.Z}:
  %Equal.sym(S.Z, x, S.Z0{}, hx) : {S.Z.add(S.Z.mul(b1, _), S.Z.neg(S.Z.mul(s, y))) == S.Z0{} : S.Z}
  %Equal.sym(S.Z, y, S.Z0{}, hy) : {S.Z.add(S.Z.mul(b1, S.Z0{}), S.Z.neg(S.Z.mul(s, _))) == S.Z0{} : S.Z}
  R.ring_eq([b1, s], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZNeg{E.ZMul{E.ZVar{1n}, E.ZCst{S.Z0{}}}}}, E.ZCst{S.Z0{}}, {==})

def step_keep.go(a: S.Z, +b: S.Z, +rp: List<&2, R.ZTerm>, +rcb: List<&2, S.Z>, +rbt: S.Pos, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +mu: List<&2, Nat>,
  +h1: {iszero(EL.cz(mu, rp)) == True{} : Bool}, +h2: {iszero(EL.cz(mu, p)) == True{} : Bool}) -> {ZAt(mu, EL.step.go(a, b, rp, rcb, rbt, p, cb, bt)) == True{} : Bool}:
  match a:
    case S.Z0{}:
      h1
    case S.Zpos{+q}:
      iszero_of(EL.cz(mu, R.padd(R.pscale(S.Zpos{EL.babs(b)}, Nil{}, rp), R.pneg(R.pscale(EL.bsgn(b, S.Zpos{q}), Nil{}, p)))),
        (%step_cz(mu, S.Zpos{EL.babs(b)}, EL.bsgn(b, S.Zpos{q}), rp, p) : {_ == S.Z0{} : S.Z}
         keep_alg(S.Zpos{EL.babs(b)}, EL.bsgn(b, S.Zpos{q}), EL.cz(mu, rp), EL.cz(mu, p), zero_of(EL.cz(mu, rp), h1), zero_of(EL.cz(mu, p), h2))))
    case S.Zneg{+q}:
      iszero_of(EL.cz(mu, R.padd(R.pscale(S.Zpos{EL.babs(b)}, Nil{}, rp), R.pneg(R.pscale(EL.bsgn(b, S.Zneg{q}), Nil{}, p)))),
        (%step_cz(mu, S.Zpos{EL.babs(b)}, EL.bsgn(b, S.Zneg{q}), rp, p) : {_ == S.Z0{} : S.Z}
         keep_alg(S.Zpos{EL.babs(b)}, EL.bsgn(b, S.Zneg{q}), EL.cz(mu, rp), EL.cz(mu, p), zero_of(EL.cz(mu, rp), h1), zero_of(EL.cz(mu, p), h2))))

# a step keeps r 0 where both r and the row are
def step_keep(+mu: List<&2, Nat>, row: EL.Row, r: EL.Res, h1: {ZAt(mu, r) == True{} : Bool}, h2: {iszero(EL.cz(mu, rowp(row))) == True{} : Bool}) -> {ZAt(mu, EL.step(row, r)) == True{} : Bool}:
  match row r:
    case EL.Row{+p, +cb, +bt, +pv} EL.Res{+rp, +rcb, +rbt}:
      step_keep.go(EL.cz(pv, rp), EL.cz(pv, p), rp, rcb, rbt, p, cb, bt, mu, h1, h2)

def keep_reduce(rows: List<&2, EL.Row>, +r: EL.Res, +mu: List<&2, Nat>, +hz: {zat(mu, rows) == True{} : Bool}, h0: {ZAt(mu, r) == True{} : Bool}) -> {ZAt(mu, EL.reduce(rows, r)) == True{} : Bool}:
  match rows:
    case Nil{}:
      h0
    case Con{+row, +t}:
      keep_reduce(t, EL.step(row, r), mu, KA.band_r(iszero(EL.cz(mu, rowp(row))), zat(mu, t), hz),
        step_keep(mu, row, r, h0, KA.band_l(iszero(EL.cz(mu, rowp(row))), zat(mu, t), hz)))

def reduce_zp(rows: List<&2, EL.Row>, +r: EL.Res, +B: List<&2, E.QExpr>, +hok: {allok(B, rows) == True{} : Bool}, +he: {ech(rows) == True{} : Bool}) -> {zp(rows, EL.reduce(rows, r)) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case Con{+row, +t}:
      KA.band_i(ZAt(rowpv(row), EL.reduce(t, EL.step(row, r))), zp(t, EL.reduce(t, EL.step(row, r))),
        keep_reduce(t, EL.step(row, r), rowpv(row), KA.band_l(zat(rowpv(row), t), ech(t), he), step_zero(B, row, r, KA.band_l(rowok(B, row), allok(B, t), hok))),
        reduce_zp(t, EL.step(row, r), B, KA.band_r(rowok(B, row), allok(B, t), hok), KA.band_r(zat(rowpv(row), t), ech(t), he)))

# The residual's combination is as long as the basis
# --------------------------------------------------

def LenR(r: EL.Res, +k: Nat) -> Type:
  match r:
    case EL.Res{p, cb, bt}:
      {vlen(cb) == k : Nat}

def vlen_vscale(+k: S.Z, u: List<&2, S.Z>) -> {vlen(u) == vlen(EL.vscale(k, u)) : Nat}:
  match u:
    case Nil{}:
      {==}
    case Con{x, t}:
      %vlen_vscale(k, t) : {1n+vlen(t) == 1n+_ : Nat}
      {==}

def vlen_vsnoc(u: List<&2, S.Z>, +x: S.Z) -> {1n+vlen(u) == vlen(EL.vsnoc(u, x)) : Nat}:
  match u:
    case Nil{}:
      {==}
    case Con{h, t}:
      %vlen_vsnoc(t, x) : {2n+vlen(t) == 1n+_ : Nat}
      {==}

def vlen_vadd(u: List<&2, S.Z>, w: List<&2, S.Z>, h: {KA.natle(vlen(w), vlen(u)) == True{} : Bool}) -> {vlen(u) == vlen(EL.vadd(u, w)) : Nat}:
  match u w:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, s}:
      absurd({vlen(Nil{}) == vlen(EL.vadd(Nil{}, Con{y, s})) : Nat}, KA.ft(h))
    case Con{x, t} Nil{}:
      {==}
    case Con{x, t} Con{y, s}:
      %vlen_vadd(t, s, h) : {1n+vlen(t) == 1n+_ : Nat}
      {==}

def vlen_zeros(n: Nat) -> {n == vlen(EL.zeros(n)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      %vlen_zeros(k) : {1n+k == 1n+_ : Nat}
      {==}

def step_len.nz(+b1: S.Z, +s: S.Z, +rcb: List<&2, S.Z>, +cb: List<&2, S.Z>, +bt: S.Pos, +k: Nat, +hl: {vlen(rcb) == k : Nat}, hc: {KA.natle(1n+vlen(cb), k) == True{} : Bool})
  -> {vlen(EL.vadd(EL.vscale(b1, rcb), EL.vscale(s, EL.vsnoc(cb, S.Zpos{bt})))) == k : Nat}:
  %vlen_vadd(EL.vscale(b1, rcb), EL.vscale(s, EL.vsnoc(cb, S.Zpos{bt})),
      (%vlen_vscale(s, EL.vsnoc(cb, S.Zpos{bt})) : {KA.natle(_, vlen(EL.vscale(b1, rcb))) == True{} : Bool}
       %vlen_vsnoc(cb, S.Zpos{bt}) : {KA.natle(_, vlen(EL.vscale(b1, rcb))) == True{} : Bool}
       %vlen_vscale(b1, rcb) : {KA.natle(1n+vlen(cb), _) == True{} : Bool}
       %Equal.sym(Nat, vlen(rcb), k, hl) : {KA.natle(1n+vlen(cb), _) == True{} : Bool}
       hc)) : {_ == k : Nat}
  %vlen_vscale(b1, rcb) : {_ == k : Nat}
  hl

def step_len.go(a: S.Z, +b: S.Z, +rp: List<&2, R.ZTerm>, +rcb: List<&2, S.Z>, +rbt: S.Pos, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +k: Nat,
  hl: {vlen(rcb) == k : Nat}, hc: {KA.natle(1n+vlen(cb), k) == True{} : Bool}) -> LenR(EL.step.go(a, b, rp, rcb, rbt, p, cb, bt), k):
  match a:
    case S.Z0{}:
      hl
    case S.Zpos{+q}:
      step_len.nz(S.Zpos{EL.babs(b)}, S.Z.neg(EL.bsgn(b, S.Zpos{q})), rcb, cb, bt, k, hl, hc)
    case S.Zneg{+q}:
      step_len.nz(S.Zpos{EL.babs(b)}, S.Z.neg(EL.bsgn(b, S.Zneg{q})), rcb, cb, bt, k, hl, hc)

def step_len(+row: EL.Row, +r: EL.Res, +k: Nat, hc: {KA.natle(1n+vlen(rowcb(row)), k) == True{} : Bool}, hl: LenR(r, k)) -> LenR(EL.step(row, r), k):
  match row r:
    case EL.Row{+p, +cb, +bt, +pv} EL.Res{+rp, +rcb, +rbt}:
      step_len.go(EL.cz(pv, rp), EL.cz(pv, p), rp, rcb, rbt, p, cb, bt, k, hl, hc)

# every row's combination is shorter than k
def cblt(rows: List<&2, EL.Row>, +k: Nat) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case Con{row, t}:
      KA.band(KA.natle(1n+vlen(rowcb(row)), k), cblt(t, k))

def reduce_len(rows: List<&2, EL.Row>, +r: EL.Res, +k: Nat, +hc: {cblt(rows, k) == True{} : Bool}, hl: LenR(r, k)) -> LenR(EL.reduce(rows, r), k):
  match rows:
    case Nil{}:
      hl
    case Con{+row, +t}:
      reduce_len(t, EL.step(row, r), k, KA.band_r(KA.natle(1n+vlen(rowcb(row)), k), cblt(t, k), hc),
        step_len(row, r, k, KA.band_l(KA.natle(1n+vlen(rowcb(row)), k), cblt(t, k), hc), hl))

def resid_len(+rows: List<&2, EL.Row>, +e: E.QExpr, +hc: {cblt(rows, EL.rlen(rows)) == True{} : Bool}) -> LenR(EL.resid(rows, e), EL.rlen(rows)):
  reduce_len(rows, EL.start(e, EL.rlen(rows)), EL.rlen(rows), hc, Equal.sym(Nat, EL.rlen(rows), vlen(EL.zeros(EL.rlen(rows))), vlen_zeros(EL.rlen(rows))))

# The rows' invariant
# -------------------

# rows from position j: each ok, at its position, echelon
def rinv(+B: List<&2, E.QExpr>, rows: List<&2, EL.Row>, +j: Nat) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case Con{+row, +t}:
      KA.band(rowok(B, row), KA.band(KA.nateq(vlen(rowcb(row)), j), KA.band(zat(rowpv(row), t), rinv(B, t, 1n+j))))

def rinv_ok(+B: List<&2, E.QExpr>, +row: EL.Row, +t: List<&2, EL.Row>, +j: Nat, h: {rinv(B, Con{row, t}, j) == True{} : Bool}) -> {rowok(B, row) == True{} : Bool}:
  KA.band_l(rowok(B, row), KA.band(KA.nateq(vlen(rowcb(row)), j), KA.band(zat(rowpv(row), t), rinv(B, t, 1n+j))), h)

def rinv_pos(+B: List<&2, E.QExpr>, +row: EL.Row, +t: List<&2, EL.Row>, +j: Nat, h: {rinv(B, Con{row, t}, j) == True{} : Bool}) -> {vlen(rowcb(row)) == j : Nat}:
  KA.nateq_ok(vlen(rowcb(row)), j, KA.band_l(KA.nateq(vlen(rowcb(row)), j), KA.band(zat(rowpv(row), t), rinv(B, t, 1n+j)),
    KA.band_r(rowok(B, row), KA.band(KA.nateq(vlen(rowcb(row)), j), KA.band(zat(rowpv(row), t), rinv(B, t, 1n+j))), h)))

def rinv_zat(+B: List<&2, E.QExpr>, +row: EL.Row, +t: List<&2, EL.Row>, +j: Nat, h: {rinv(B, Con{row, t}, j) == True{} : Bool}) -> {zat(rowpv(row), t) == True{} : Bool}:
  KA.band_l(zat(rowpv(row), t), rinv(B, t, 1n+j), KA.band_r(KA.nateq(vlen(rowcb(row)), j), KA.band(zat(rowpv(row), t), rinv(B, t, 1n+j)),
    KA.band_r(rowok(B, row), KA.band(KA.nateq(vlen(rowcb(row)), j), KA.band(zat(rowpv(row), t), rinv(B, t, 1n+j))), h)))

def rinv_tl(+B: List<&2, E.QExpr>, +row: EL.Row, +t: List<&2, EL.Row>, +j: Nat, h: {rinv(B, Con{row, t}, j) == True{} : Bool}) -> {rinv(B, t, 1n+j) == True{} : Bool}:
  KA.band_r(zat(rowpv(row), t), rinv(B, t, 1n+j), KA.band_r(KA.nateq(vlen(rowcb(row)), j), KA.band(zat(rowpv(row), t), rinv(B, t, 1n+j)),
    KA.band_r(rowok(B, row), KA.band(KA.nateq(vlen(rowcb(row)), j), KA.band(zat(rowpv(row), t), rinv(B, t, 1n+j))), h)))

def rinv_allok(+B: List<&2, E.QExpr>, rows: List<&2, EL.Row>, +j: Nat, +h: {rinv(B, rows, j) == True{} : Bool}) -> {allok(B, rows) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case Con{+row, +t}:
      KA.band_i(rowok(B, row), allok(B, t), rinv_ok(B, row, t, j, h), rinv_allok(B, t, 1n+j, rinv_tl(B, row, t, j, h)))

def rinv_ech(+B: List<&2, E.QExpr>, rows: List<&2, EL.Row>, +j: Nat, +h: {rinv(B, rows, j) == True{} : Bool}) -> {ech(rows) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case Con{+row, +t}:
      KA.band_i(zat(rowpv(row), t), ech(t), rinv_zat(B, row, t, j, h), rinv_ech(B, t, 1n+j, rinv_tl(B, row, t, j, h)))

# j + 1 + n bounds 1 + j
def succ_le(+j: Nat, +n: Nat, +k: Nat, h: {KA.natle(Nat.add(j, 1n+n), k) == True{} : Bool}) -> {KA.natle(1n+j, k) == True{} : Bool}:
  KA.natle_trans(1n+j, Nat.add(j, 1n+n), k, (%N.add_succ(j, n) : {KA.natle(1n+j, _) == True{} : Bool}
    KA.natle_add_r(j, n)), h)

def succ_shift(+j: Nat, +n: Nat, +k: Nat, h: {KA.natle(Nat.add(j, 1n+n), k) == True{} : Bool}) -> {KA.natle(Nat.add(1n+j, n), k) == True{} : Bool}:
  %Equal.sym(Nat, 1n+Nat.add(j, n), Nat.add(j, 1n+n), N.add_succ(j, n)) : {KA.natle(_, k) == True{} : Bool}
  h

def rinv_cblt(+B: List<&2, E.QExpr>, rows: List<&2, EL.Row>, +j: Nat, +k: Nat, +h: {rinv(B, rows, j) == True{} : Bool}, +hk: {KA.natle(Nat.add(j, EL.rlen(rows)), k) == True{} : Bool}) -> {cblt(rows, k) == True{} : Bool}:
  match rows:
    case Nil{}:
      {==}
    case Con{+row, +t}:
      KA.band_i(KA.natle(1n+vlen(rowcb(row)), k), cblt(t, k),
        (%Equal.sym(Nat, vlen(rowcb(row)), j, rinv_pos(B, row, t, j, h)) : {KA.natle(1n+_, k) == True{} : Bool}
         succ_le(j, EL.rlen(t), k, hk)),
        rinv_cblt(B, t, 1n+j, k, rinv_tl(B, row, t, j, h), succ_shift(j, EL.rlen(t), k, hk)))

# A new row
# ---------

def qsnoc(B: List<&2, E.QExpr>, e: E.QExpr) -> List<&2, E.QExpr>:
  match B:
    case Nil{}:
      Con{e, Nil{}}
    case Con{b, t}:
      Con{b, qsnoc(t, e)}

def resp(r: EL.Res) -> List<&2, R.ZTerm>:
  match r:
    case EL.Res{p, cb, bt}:
      p

def eqat_snoc(B: List<&2, E.QExpr>, +e: E.QExpr, j: Nat, h: {KA.natle(1n+j, SV.neqs(B)) == True{} : Bool}) -> {SV.eqat(B, j) == SV.eqat(qsnoc(B, e), j) : E.QExpr}:
  match B j:
    case Nil{} 0n:
      absurd({SV.eqat(Nil{}, 0n) == SV.eqat(qsnoc(Nil{}, e), 0n) : E.QExpr}, KA.ft(h))
    case Nil{} 1n+i:
      absurd({SV.eqat(Nil{}, 1n+i) == SV.eqat(qsnoc(Nil{}, e), 1n+i) : E.QExpr}, KA.ft(h))
    case Con{b, t} 0n:
      {==}
    case Con{b, t} 1n+i:
      eqat_snoc(t, e, i, h)

def eqat_last(B: List<&2, E.QExpr>, +e: E.QExpr) -> {e == SV.eqat(qsnoc(B, e), SV.neqs(B)) : E.QExpr}:
  match B:
    case Nil{}:
      {==}
    case Con{b, t}:
      eqat_last(t, e)

def comb_snoc(u: List<&2, S.Z>, B: List<&2, E.QExpr>, +e: E.QExpr, h: {KA.natle(vlen(u), SV.neqs(B)) == True{} : Bool}) -> {comb(u, B) == comb(u, qsnoc(B, e)) : List<&2, R.ZTerm>}:
  match u B:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, t}:
      {==}
    case Con{x, s} Nil{}:
      absurd({comb(Con{x, s}, Nil{}) == comb(Con{x, s}, qsnoc(Nil{}, e)) : List<&2, R.ZTerm>}, KA.ft(h))
    case Con{+x, +s} Con{+b, +t}:
      %comb_snoc(s, t, e, h) : {comb(Con{x, s}, Con{b, t}) == R.padd(R.pscale(x, Nil{}, NE(b)), _) : List<&2, R.ZTerm>}
      {==}

# a row stays ok as the basis grows
def rowok_snoc(+B: List<&2, E.QExpr>, +e: E.QExpr, row: EL.Row, hok: {rowok(B, row) == True{} : Bool}, hc: {KA.natle(1n+vlen(rowcb(row)), SV.neqs(B)) == True{} : Bool}) -> {rowok(qsnoc(B, e), row) == True{} : Bool}:
  match row:
    case EL.Row{+p, +cb, +bt, +pv}:
      +hok2 = hok
      +hc2 = hc
      rowok_mk(qsnoc(B, e), p, cb, bt, pv, rowok_red(B, p, cb, bt, pv, hok2), rowok_nz(B, p, cb, bt, pv, hok2),
        (%eqat_snoc(B, e, vlen(cb), hc2) : {same(p, comb2(bt, _, cb, qsnoc(B, e))) == True{} : Bool}
         %comb_snoc(cb, B, e, KA.natle_pred(vlen(cb), SV.neqs(B), hc2)) : {same(p, R.padd(R.pscale(S.Zpos{bt}, Nil{}, NE(SV.eqat(B, vlen(cb)))), _)) == True{} : Bool}
         rowok_same(B, p, cb, bt, pv, hok2)))

def zat_snoc(+mu: List<&2, Nat>, rows: List<&2, EL.Row>, +nr: EL.Row, +h1: {zat(mu, rows) == True{} : Bool}, +h2: {iszero(EL.cz(mu, rowp(nr))) == True{} : Bool}) -> {zat(mu, EL.rsnoc(rows, nr)) == True{} : Bool}:
  match rows:
    case Nil{}:
      KA.band_i(iszero(EL.cz(mu, rowp(nr))), True{}, h2, {==})
    case Con{+row, +t}:
      KA.band_i(iszero(EL.cz(mu, rowp(row))), zat(mu, EL.rsnoc(t, nr)), KA.band_l(iszero(EL.cz(mu, rowp(row))), zat(mu, t), h1),
        zat_snoc(mu, t, nr, KA.band_r(iszero(EL.cz(mu, rowp(row))), zat(mu, t), h1), h2))

def rinv_snoc(+B: List<&2, E.QExpr>, +e: E.QExpr, rows: List<&2, EL.Row>, +j: Nat, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +pv: List<&2, Nat>,
  +h: {rinv(B, rows, j) == True{} : Bool}, +hk: {KA.natle(Nat.add(j, EL.rlen(rows)), SV.neqs(B)) == True{} : Bool},
  +hnr: {rowok(qsnoc(B, e), EL.Row{p, cb, bt, pv}) == True{} : Bool}, +hnl: {vlen(cb) == Nat.add(j, EL.rlen(rows)) : Nat},
  +hz: {zp(rows, EL.Res{p, cb, bt}) == True{} : Bool}) -> {rinv(qsnoc(B, e), EL.rsnoc(rows, EL.Row{p, cb, bt, pv}), j) == True{} : Bool}:
  match rows:
    case Nil{}:
      KA.band_i(rowok(qsnoc(B, e), EL.Row{p, cb, bt, pv}), KA.band(KA.nateq(vlen(cb), j), True{}), hnr,
        KA.band_i(KA.nateq(vlen(cb), j), True{}, KA.nateq_of(vlen(cb), j,
          (%Equal.sym(Nat, j, Nat.add(j, 0n), N.add_zero(j)) : {vlen(cb) == _ : Nat}
           hnl)), {==}))
    case Con{+row, +t}:
      KA.band_i(rowok(qsnoc(B, e), row), KA.band(KA.nateq(vlen(rowcb(row)), j), KA.band(zat(rowpv(row), EL.rsnoc(t, EL.Row{p, cb, bt, pv})), rinv(qsnoc(B, e), EL.rsnoc(t, EL.Row{p, cb, bt, pv}), 1n+j))),
        rowok_snoc(B, e, row, rinv_ok(B, row, t, j, h),
          (%Equal.sym(Nat, vlen(rowcb(row)), j, rinv_pos(B, row, t, j, h)) : {KA.natle(1n+_, SV.neqs(B)) == True{} : Bool}
           succ_le(j, EL.rlen(t), SV.neqs(B), hk))),
        KA.band_i(KA.nateq(vlen(rowcb(row)), j), KA.band(zat(rowpv(row), EL.rsnoc(t, EL.Row{p, cb, bt, pv})), rinv(qsnoc(B, e), EL.rsnoc(t, EL.Row{p, cb, bt, pv}), 1n+j)),
          KA.nateq_of(vlen(rowcb(row)), j, rinv_pos(B, row, t, j, h)),
          KA.band_i(zat(rowpv(row), EL.rsnoc(t, EL.Row{p, cb, bt, pv})), rinv(qsnoc(B, e), EL.rsnoc(t, EL.Row{p, cb, bt, pv}), 1n+j),
            zat_snoc(rowpv(row), t, EL.Row{p, cb, bt, pv}, rinv_zat(B, row, t, j, h), KA.band_l(ZAt(rowpv(row), EL.Res{p, cb, bt}), zp(t, EL.Res{p, cb, bt}), hz)),
            rinv_snoc(B, e, t, 1n+j, p, cb, bt, pv, rinv_tl(B, row, t, j, h), succ_shift(j, EL.rlen(t), SV.neqs(B), hk), hnr,
              Equal.trans(Nat, vlen(cb), Nat.add(j, 1n+EL.rlen(t)), 1n+Nat.add(j, EL.rlen(t)), hnl, Equal.sym(Nat, 1n+Nat.add(j, EL.rlen(t)), Nat.add(j, 1n+EL.rlen(t)), N.add_succ(j, EL.rlen(t)))),
              KA.band_r(ZAt(rowpv(row), EL.Res{p, cb, bt}), zp(t, EL.Res{p, cb, bt}), hz)))))

def new_rel(+m: List<&2, Nat>, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +e: E.QExpr, +B: List<&2, E.QExpr>, hrel: @m2: List<&2, Nat> -> Rel(m2, EL.Res{p, cb, bt}, e, B))
  -> {EL.cz(m, p) == EL.cz(m, comb2(bt, e, cb, B)) : S.Z}:
  Equal.trans(S.Z, EL.cz(m, p), S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, NE(e))), zdot(cb, zv(m, B))), EL.cz(m, comb2(bt, e, cb, B)), hrel(m), cz_comb2(m, bt, e, cb, B))

def new_rinv.r(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, r: EL.Res, h: {rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hred: {RedR(r) == True{} : Bool}, hzp: {zp(rows, r) == True{} : Bool}, hlen: LenR(r, EL.rlen(rows)), hrel: @m: List<&2, Nat> -> Rel(m, r, e, B), hne: {isnil(resp(r)) == False{} : Bool})
  -> {rinv(qsnoc(B, e), EL.rsnoc(rows, EL.row_of(r)), 0n) == True{} : Bool}:
  match r:
    case EL.Res{+p, +cb, +bt}:
      +hred2 = hred
      +hl0 = {hlen : {vlen(cb) == EL.rlen(rows) : Nat}}
      +hcl = Equal.trans(Nat, vlen(cb), EL.rlen(rows), SV.neqs(B), hl0, hl)
      rinv_snoc(B, e, rows, 0n, p, cb, bt, EL.pivot(p), h,
        (%hl : {KA.natle(EL.rlen(rows), _) == True{} : Bool}
         KA.natle_refl(EL.rlen(rows))),
        rowok_mk(qsnoc(B, e), p, cb, bt, EL.pivot(p), hred2, pivot_nz(p, hred2, hne),
          (%Equal.sym(Nat, vlen(cb), SV.neqs(B), hcl) : {same(p, comb2(bt, SV.eqat(qsnoc(B, e), _), cb, qsnoc(B, e))) == True{} : Bool}
           %eqat_last(B, e) : {same(p, comb2(bt, _, cb, qsnoc(B, e))) == True{} : Bool}
           %comb_snoc(cb, B, e, (%hcl : {KA.natle(vlen(cb), _) == True{} : Bool}
              KA.natle_refl(vlen(cb)))) : {same(p, R.padd(R.pscale(S.Zpos{bt}, Nil{}, NE(e)), _)) == True{} : Bool}
           same_of(p, comb2(bt, e, cb, B), hred2, comb2_red(bt, e, cb, B), m => new_rel(m, p, cb, bt, e, B, hrel)))),
        hl0, hzp)

# a nonzero residual extends the rows, and the basis by e
def new_rinv(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, +h: {rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hne: {isnil(resp(EL.resid(rows, e))) == False{} : Bool}) -> {rinv(qsnoc(B, e), EL.rsnoc(rows, EL.row_of(EL.resid(rows, e))), 0n) == True{} : Bool}:
  new_rinv.r(B, rows, e, EL.resid(rows, e), h, hl, resid_red(rows, e, B, rinv_allok(B, rows, 0n, h)),
    reduce_zp(rows, EL.start(e, EL.rlen(rows)), B, rinv_allok(B, rows, 0n, h), rinv_ech(B, rows, 0n, h)),
    resid_len(rows, e, rinv_cblt(B, rows, 0n, EL.rlen(rows), h, KA.natle_refl(EL.rlen(rows)))),
    m => resid_rel(m, rows, e, B, rinv_allok(B, rows, 0n, h)), hne)
