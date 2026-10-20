# bend-cad: the simplex's dictionary read in an ordered field (PLAN-sk13a
# S3). A row Rw{D, M} reads as R = M / D: its value at a point w (one entry
# per variable) is rv(r, w) = (M . w) / D. Pivoting on p = M_ie (pivot row
# (D_i, M_i), leaving i, entering e) sends every row's value at w to the old
# row's value at w with entry e lowered by
#   t(w) = (M_i . w - D_i w_i) / p,
# that is R' = R - (R_e / R_ie)(R_i - e_i) (phis_ok). Everything about the
# dictionary that the proofs use follows from this.
#
# Generated from tools/drafts/simppf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./qemb.bend as QE
import ./karith.bend as KA
import ./nat.bend as LN
import ./zring.bend as R
import ./elim.bend as EL
import ./simplex.bend as SX

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Vectors
# -------

# u . w, u an integer vector read in F
def zdot(~F: O.OField, u: List<&2, S.Z>, w: M.Vec(~F)) -> O.C(F):
  match u w:
    case Nil{} w:
      O.zero(F)
    case Con{x, t} Nil{}:
      O.zero(F)
    case Con{x, t} Con{y, s}:
      O.add(F, O.mul(F, O.ofz(~F, x), y), zdot(~F, t, s))

# entry j (0 past the end)
def fat(~F: O.OField, w: M.Vec(~F), j: Nat) -> O.C(F):
  match w j:
    case Nil{} j:
      O.zero(F)
    case Con{y, s} 0n:
      y
    case Con{y, s} 1n+k:
      fat(~F, s, k)

# w with entry e lowered by t
def wsub(~F: O.OField, w: M.Vec(~F), e: Nat, +t: O.C(F)) -> M.Vec(~F):
  match w e:
    case Nil{} 0n:
      Con{O.sub(~F, O.zero(F), t), Nil{}}
    case Nil{} 1n+k:
      Con{O.zero(F), wsub(~F, Nil{}, k, t)}
    case Con{y, s} 0n:
      Con{O.sub(~F, y, t), s}
    case Con{y, s} 1n+k:
      Con{y, wsub(~F, s, k, t)}

def zdot_nil_r(~F: O.OField, u: List<&2, S.Z>) -> {O.zero(F) == zdot(~F, u, Nil{}) : O.C(F)}:
  match u:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

def zz(~F: O.OField) -> {O.add(F, O.zero(F), O.zero(F)) == O.zero(F) : O.C(F)}:
  O.add_zero(F)(O.zero(F))

# u . (w - t e_e) = u . w - u_e t
def zdot_wsub(~F: O.OField, u: List<&2, S.Z>, w: M.Vec(~F), e: Nat, +t: O.C(F)) -> {O.sub(~F, zdot(~F, u, w), O.mul(F, O.ofz(~F, SX.at(u, e)), t)) == zdot(~F, u, wsub(~F, w, e, t)) : O.C(F)}:
  match u w e:
    case Nil{} w e:
      FR.fring_eq(~F, [t], E.ZSub{E.ZCst{S.Z0{}}, E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}}, E.ZCst{S.Z0{}}, {==})
    case Con{+x, +ut} Nil{} 0n:
      %zdot_nil_r(~F, ut) : {O.sub(~F, O.zero(F), O.mul(F, O.ofz(~F, x), t)) == O.add(F, O.mul(F, O.ofz(~F, x), O.sub(~F, O.zero(F), t)), _) : O.C(F)}
      FR.fring_eq(~F, [O.ofz(~F, x), t], E.ZSub{E.ZCst{S.Z0{}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZSub{E.ZCst{S.Z0{}}, E.ZVar{1n}}}, E.ZCst{S.Z0{}}}, {==})
    case Con{+x, +ut} Nil{} 1n++k:
      %zdot_wsub(~F, ut, Nil{}, k, t) : {O.sub(~F, O.zero(F), O.mul(F, O.ofz(~F, SX.at(ut, k)), t)) == O.add(F, O.mul(F, O.ofz(~F, x), O.zero(F)), _) : O.C(F)}
      %zdot_nil_r(~F, ut) : {O.sub(~F, O.zero(F), O.mul(F, O.ofz(~F, SX.at(ut, k)), t)) == O.add(F, O.mul(F, O.ofz(~F, x), O.zero(F)), O.sub(~F, _, O.mul(F, O.ofz(~F, SX.at(ut, k)), t))) : O.C(F)}
      FR.fring_eq(~F, [O.ofz(~F, x), O.ofz(~F, SX.at(ut, k)), t], E.ZSub{E.ZCst{S.Z0{}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZSub{E.ZCst{S.Z0{}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}, {==})
    case Con{+x, +ut} Con{+y, +s} 0n:
      FR.fring_eq(~F, [O.ofz(~F, x), y, t, zdot(~F, ut, s)], E.ZSub{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{3n}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZSub{E.ZVar{1n}, E.ZVar{2n}}}, E.ZVar{3n}}, {==})
    case Con{+x, +ut} Con{+y, +s} 1n++k:
      %zdot_wsub(~F, ut, s, k, t) : {O.sub(~F, O.add(F, O.mul(F, O.ofz(~F, x), y), zdot(~F, ut, s)), O.mul(F, O.ofz(~F, SX.at(ut, k)), t)) == O.add(F, O.mul(F, O.ofz(~F, x), y), _) : O.C(F)}
      FR.fring_eq(~F, [O.ofz(~F, x), y, t, O.ofz(~F, SX.at(ut, k)), zdot(~F, ut, s)], E.ZSub{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{4n}}, E.ZMul{E.ZVar{3n}, E.ZVar{2n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZVar{4n}, E.ZMul{E.ZVar{3n}, E.ZVar{2n}}}}, {==})

# u1 . w + u2 . w = (u1 + u2) . w
def zdot_vadd(~F: O.OField, u1: List<&2, S.Z>, u2: List<&2, S.Z>, +w: M.Vec(~F)) -> {O.add(F, zdot(~F, u1, w), zdot(~F, u2, w)) == zdot(~F, EL.vadd(u1, u2), w) : O.C(F)}:
  match u1 u2 w:
    case Nil{} Nil{} w:
      zz(~F)
    case Nil{} Con{+y, +s} w:
      FL.zero_add(~F, zdot(~F, Con{y, s}, w))
    case Con{+x, +t} Nil{} w:
      Equal.sym(O.C(F), zdot(~F, Con{x, t}, w), O.add(F, zdot(~F, Con{x, t}, w), O.zero(F)), FL.add_zero(~F, zdot(~F, Con{x, t}, w)))
    case Con{x, t} Con{y, s} Nil{}:
      zz(~F)
    case Con{+x, +t} Con{+y, +s} Con{+z, +r}:
      %zdot_vadd(~F, t, s, r) : {O.add(F, O.add(F, O.mul(F, O.ofz(~F, x), z), zdot(~F, t, r)), O.add(F, O.mul(F, O.ofz(~F, y), z), zdot(~F, s, r))) == O.add(F, O.mul(F, O.ofz(~F, S.Z.add(x, y)), z), _) : O.C(F)}
      %FR.ofz_add(~F, x, y) : {O.add(F, O.add(F, O.mul(F, O.ofz(~F, x), z), zdot(~F, t, r)), O.add(F, O.mul(F, O.ofz(~F, y), z), zdot(~F, s, r))) == O.add(F, O.mul(F, _, z), O.add(F, zdot(~F, t, r), zdot(~F, s, r))) : O.C(F)}
      FR.fring_eq(~F, [O.ofz(~F, x), O.ofz(~F, y), z, zdot(~F, t, r), zdot(~F, s, r)], E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{3n}}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{4n}}}, E.ZAdd{E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZAdd{E.ZVar{3n}, E.ZVar{4n}}}, {==})

# k (u . w) = (k u) . w
def zdot_vscale(~F: O.OField, +k: S.Z, u: List<&2, S.Z>, +w: M.Vec(~F)) -> {O.mul(F, O.ofz(~F, k), zdot(~F, u, w)) == zdot(~F, EL.vscale(k, u), w) : O.C(F)}:
  match u w:
    case Nil{} w:
      Equal.sym(O.C(F), O.zero(F), O.mul(F, O.ofz(~F, k), O.zero(F)), FL.mul_zero(~F, O.ofz(~F, k)))
    case Con{x, t} Nil{}:
      Equal.sym(O.C(F), O.zero(F), O.mul(F, O.ofz(~F, k), O.zero(F)), FL.mul_zero(~F, O.ofz(~F, k)))
    case Con{+x, +t} Con{+y, +s}:
      %zdot_vscale(~F, k, t, s) : {O.mul(F, O.ofz(~F, k), O.add(F, O.mul(F, O.ofz(~F, x), y), zdot(~F, t, s))) == O.add(F, O.mul(F, O.ofz(~F, S.Z.mul(k, x)), y), _) : O.C(F)}
      %FR.ofz_mul(~F, k, x) : {O.mul(F, O.ofz(~F, k), O.add(F, O.mul(F, O.ofz(~F, x), y), zdot(~F, t, s))) == O.add(F, O.mul(F, _, y), O.mul(F, O.ofz(~F, k), zdot(~F, t, s))) : O.C(F)}
      FR.fring_eq(~F, [O.ofz(~F, k), O.ofz(~F, x), y, zdot(~F, t, s)], E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{3n}}}, E.ZAdd{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}, {==})

# zeros . w = 0
def zdot_zeros(~F: O.OField, j: Nat, w: M.Vec(~F)) -> {O.zero(F) == zdot(~F, EL.zeros(j), w) : O.C(F)}:
  match j w:
    case 0n w:
      {==}
    case 1n+k Nil{}:
      {==}
    case 1n+k Con{+y, +s}:
      %zdot_zeros(~F, k, s) : {O.zero(F) == O.add(F, O.mul(F, O.zero(F), y), _) : O.C(F)}
      FR.fring_eq(~F, [y], E.ZCst{S.Z0{}}, E.ZAdd{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZCst{S.Z0{}}}, {==})

# e_i . w = w_i, for i < len
def zdot_unit(~F: O.OField, len: Nat, i: Nat, w: M.Vec(~F), hi: {SX.ltn(i, len) == True{} : Bool}) -> {fat(~F, w, i) == zdot(~F, SX.unit(len, i), w) : O.C(F)}:
  match len i w:
    case 0n 0n w:
      absurd({fat(~F, w, 0n) == zdot(~F, SX.unit(0n, 0n), w) : O.C(F)}, KA.ft(hi))
    case 0n 1n++h w:
      absurd({fat(~F, w, 1n+h) == zdot(~F, SX.unit(0n, 1n+h), w) : O.C(F)}, KA.ft(hi))
    case 1n++j 0n Nil{}:
      {==}
    case 1n++j 0n Con{+y, +s}:
      %zdot_zeros(~F, j, s) : {y == O.add(F, O.mul(F, O.one(F), y), _) : O.C(F)}
      FR.fring_eq(~F, [y], E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, E.ZCst{S.Z0{}}}, {==})
    case 1n++j 1n++h Nil{}:
      {==}
    case 1n++j 1n++h Con{+y, +s}:
      %zdot_unit(~F, j, h, s, hi) : {fat(~F, s, h) == O.add(F, O.mul(F, O.zero(F), y), _) : O.C(F)}
      FR.fring_eq(~F, [y, fat(~F, s, h)], E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZVar{1n}}, {==})

# Rows
# ----

# row r's value at w: (M . w) / D
def rv(~F: O.OField, +r: SX.Rw, +w: M.Vec(~F)) -> O.C(F):
  O.mul(F, zdot(~F, SX.Rw.m(r), w), O.inv(F, O.ofp(~F, SX.Rw.d(r))))

# every row's value at w
def rmap(~F: O.OField, rs: List<&2, SX.Rw>, +w: M.Vec(~F)) -> M.Vec(~F):
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{rv(~F, r, w), rmap(~F, t, w)}

# r . (w - t e_e) = r . w - R_e t
def rv_wsub(~F: O.OField, +r: SX.Rw, +w: M.Vec(~F), +e: Nat, +t: O.C(F)) -> {O.sub(~F, rv(~F, r, w), O.mul(F, O.mul(F, O.ofz(~F, SX.at(SX.Rw.m(r), e)), O.inv(F, O.ofp(~F, SX.Rw.d(r)))), t)) == rv(~F, r, wsub(~F, w, e, t)) : O.C(F)}:
  %zdot_wsub(~F, SX.Rw.m(r), w, e, t) : {O.sub(~F, rv(~F, r, w), O.mul(F, O.mul(F, O.ofz(~F, SX.at(SX.Rw.m(r), e)), O.inv(F, O.ofp(~F, SX.Rw.d(r)))), t)) == O.mul(F, _, O.inv(F, O.ofp(~F, SX.Rw.d(r)))) : O.C(F)}
  FR.fring_eq(~F, [zdot(~F, SX.Rw.m(r), w), O.ofz(~F, SX.at(SX.Rw.m(r), e)), O.inv(F, O.ofp(~F, SX.Rw.d(r))), t], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{3n}}}, E.ZMul{E.ZSub{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZVar{2n}}, {==})

# the pivot's step at w: (M_i . w - D_i w_i) / p
def tval(~F: O.OField, +mi: List<&2, S.Z>, +di: S.Pos, +i: Nat, +p: S.Z, +w: M.Vec(~F)) -> O.C(F):
  O.mul(F, O.sub(~F, zdot(~F, mi, w), O.mul(F, O.ofp(~F, di), fat(~F, w, i))), O.inv(F, O.ofz(~F, p)))

def ofz_ne(~F: O.OField, p: S.Z, h: {SX.iszero(p) == False{} : Bool}) -> {O.ofz(~F, p) == O.zero(F) : O.C(F)} -> Empty:
  match p:
    case S.Z0{}:
      absurd({O.ofz(~F, S.Z0{}) == O.zero(F) : O.C(F)} -> Empty, KA.tf(h))
    case S.Zpos{+q}:
      QE.ofp_ne(~F, q)
    case S.Zneg{+q}:
      e => QE.ofp_ne(~F, q)(FO.eq_of_sub(~F, O.ofp(~F, q), O.zero(F), FO.cert1(~F, O.sub(~F, O.ofp(~F, q), O.zero(F)), O.neg(F, O.one(F)), O.sub(~F, O.neg(F, O.ofp(~F, q)), O.zero(F)), FR.fring_eq(~F, [O.ofp(~F, q)], E.ZSub{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZMul{E.ZNeg{E.ZCst{S.Zpos{S.XH{}}}}, E.ZSub{E.ZNeg{E.ZVar{0n}}, E.ZCst{S.Z0{}}}}, {==}), FO.sub_of_eq(~F, O.neg(F, O.ofp(~F, q)), O.zero(F), e))))

def iszero_eq(c: S.Z, h: {True{} == SX.iszero(c) : Bool}) -> {S.Z0{} == c : S.Z}:
  match c:
    case S.Z0{}:
      {==}
    case S.Zpos{q}:
      absurd({S.Z0{} == S.Zpos{q} : S.Z}, KA.tf(h))
    case S.Zneg{q}:
      absurd({S.Z0{} == S.Zneg{q} : S.Z}, KA.tf(h))

# the pivot row becomes e_i
def phi1(~F: O.OField, +mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, +p: S.Z, +len: Nat, +w: M.Vec(~F), hpe: {SX.at(mi, e) == p : S.Z}, +hp: {SX.iszero(p) == False{} : Bool}, +hi: {SX.ltn(i, len) == True{} : Bool}) -> {rv(~F, SX.Rw{di, mi}, wsub(~F, w, e, tval(~F, mi, di, i, p, w))) == rv(~F, SX.Rw{S.XH{}, SX.unit(len, i)}, w) : O.C(F)}:
  %rv_wsub(~F, SX.Rw{di, mi}, w, e, tval(~F, mi, di, i, p, w)) : {_ == rv(~F, SX.Rw{S.XH{}, SX.unit(len, i)}, w) : O.C(F)}
  %Equal.sym(S.Z, SX.at(mi, e), p, hpe) : {O.sub(~F, O.mul(F, zdot(~F, mi, w), O.inv(F, O.ofp(~F, di))), O.mul(F, O.mul(F, O.ofz(~F, _), O.inv(F, O.ofp(~F, di))), tval(~F, mi, di, i, p, w))) == rv(~F, SX.Rw{S.XH{}, SX.unit(len, i)}, w) : O.C(F)}
  %zdot_unit(~F, len, i, w, hi) : {O.sub(~F, O.mul(F, zdot(~F, mi, w), O.inv(F, O.ofp(~F, di))), O.mul(F, O.mul(F, O.ofz(~F, p), O.inv(F, O.ofp(~F, di))), tval(~F, mi, di, i, p, w))) == O.mul(F, _, O.inv(F, O.ofp(~F, S.XH{}))) : O.C(F)}
  FO.eq_of_sub(~F, O.sub(~F, O.mul(F, zdot(~F, mi, w), O.inv(F, O.ofp(~F, di))), O.mul(F, O.mul(F, O.ofz(~F, p), O.inv(F, O.ofp(~F, di))), O.mul(F, O.sub(~F, zdot(~F, mi, w), O.mul(F, O.ofp(~F, di), fat(~F, w, i))), O.inv(F, O.ofz(~F, p))))), O.mul(F, fat(~F, w, i), O.inv(F, O.ofp(~F, S.XH{}))), FO.cert3(~F, O.sub(~F, O.sub(~F, O.mul(F, zdot(~F, mi, w), O.inv(F, O.ofp(~F, di))), O.mul(F, O.mul(F, O.ofz(~F, p), O.inv(F, O.ofp(~F, di))), O.mul(F, O.sub(~F, zdot(~F, mi, w), O.mul(F, O.ofp(~F, di), fat(~F, w, i))), O.inv(F, O.ofz(~F, p))))), O.mul(F, fat(~F, w, i), O.inv(F, O.ofp(~F, S.XH{})))), O.mul(F, O.inv(F, O.ofp(~F, di)), O.add(F, O.neg(F, zdot(~F, mi, w)), O.mul(F, O.ofp(~F, di), fat(~F, w, i)))), O.sub(~F, O.mul(F, O.ofz(~F, p), O.inv(F, O.ofz(~F, p))), O.one(F)), fat(~F, w, i), O.sub(~F, O.mul(F, O.ofp(~F, di), O.inv(F, O.ofp(~F, di))), O.one(F)), O.neg(F, fat(~F, w, i)), O.sub(~F, O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.XH{}))), O.one(F)), FR.fring_eq(~F, [fat(~F, w, i), O.inv(F, O.ofp(~F, S.XH{})), zdot(~F, mi, w), O.inv(F, O.ofp(~F, di)), O.ofz(~F, p), O.ofp(~F, di), O.inv(F, O.ofz(~F, p))], E.ZSub{E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{3n}}, E.ZMul{E.ZSub{E.ZVar{2n}, E.ZMul{E.ZVar{5n}, E.ZVar{0n}}}, E.ZVar{6n}}}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZMul{E.ZVar{3n}, E.ZAdd{E.ZNeg{E.ZVar{2n}}, E.ZMul{E.ZVar{5n}, E.ZVar{0n}}}}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{6n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZVar{0n}, E.ZSub{E.ZMul{E.ZVar{5n}, E.ZVar{3n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZSub{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{1n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), FO.inv_rel(~F, O.ofz(~F, p), ofz_ne(~F, p, hp)), QE.ofp_rel(~F, di), QE.ofp_rel(~F, S.XH{})))

# a row with M_xe = 0 is unchanged
def phi2(~F: O.OField, +mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, +p: S.Z, +r: SX.Rw, +w: M.Vec(~F), hb: {True{} == SX.iszero(SX.at(SX.Rw.m(r), e)) : Bool}) -> {rv(~F, r, wsub(~F, w, e, tval(~F, mi, di, i, p, w))) == rv(~F, r, w) : O.C(F)}:
  %rv_wsub(~F, r, w, e, tval(~F, mi, di, i, p, w)) : {_ == rv(~F, r, w) : O.C(F)}
  %iszero_eq(SX.at(SX.Rw.m(r), e), hb) : {O.sub(~F, rv(~F, r, w), O.mul(F, O.mul(F, O.ofz(~F, _), O.inv(F, O.ofp(~F, SX.Rw.d(r)))), tval(~F, mi, di, i, p, w))) == rv(~F, r, w) : O.C(F)}
  FR.fring_eq(~F, [rv(~F, r, w), O.inv(F, O.ofp(~F, SX.Rw.d(r))), tval(~F, mi, di, i, p, w)], E.ZSub{E.ZVar{0n}, E.ZMul{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{1n}}, E.ZVar{2n}}}, E.ZVar{0n}, {==})
def phi3.pos(~F: O.OField, +mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, +q: S.Pos, +len: Nat, r: SX.Rw, +w: M.Vec(~F), +hi: {SX.ltn(i, len) == True{} : Bool}) -> {rv(~F, r, wsub(~F, w, e, tval(~F, mi, di, i, S.Zpos{q}, w))) == rv(~F, SX.phi.go(False{}, mi, di, i, S.Zpos{q}, len, SX.at(SX.Rw.m(r), e), r), w) : O.C(F)}:
  match r:
    case SX.Rw{+d, +m}:
      %rv_wsub(~F, SX.Rw{d, m}, w, e, tval(~F, mi, di, i, S.Zpos{q}, w)) : {_ == O.mul(F, zdot(~F, EL.vadd(EL.vadd(EL.vscale(S.Zpos{q}, m), EL.vscale(S.Z.neg(SX.at(m, e)), mi)), EL.vscale(S.Z.mul(SX.at(m, e), S.Zpos{di}), SX.unit(len, i))), w), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      %zdot_vadd(~F, EL.vadd(EL.vscale(S.Zpos{q}, m), EL.vscale(S.Z.neg(SX.at(m, e)), mi)), EL.vscale(S.Z.mul(SX.at(m, e), S.Zpos{di}), SX.unit(len, i)), w) : {O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), tval(~F, mi, di, i, S.Zpos{q}, w))) == O.mul(F, _, O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      %zdot_vadd(~F, EL.vscale(S.Zpos{q}, m), EL.vscale(S.Z.neg(SX.at(m, e)), mi), w) : {O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), tval(~F, mi, di, i, S.Zpos{q}, w))) == O.mul(F, O.add(F, _, zdot(~F, EL.vscale(S.Z.mul(SX.at(m, e), S.Zpos{di}), SX.unit(len, i)), w)), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      %zdot_vscale(~F, S.Zpos{q}, m, w) : {O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), tval(~F, mi, di, i, S.Zpos{q}, w))) == O.mul(F, O.add(F, O.add(F, _, zdot(~F, EL.vscale(S.Z.neg(SX.at(m, e)), mi), w)), zdot(~F, EL.vscale(S.Z.mul(SX.at(m, e), S.Zpos{di}), SX.unit(len, i)), w)), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      %zdot_vscale(~F, S.Z.neg(SX.at(m, e)), mi, w) : {O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), tval(~F, mi, di, i, S.Zpos{q}, w))) == O.mul(F, O.add(F, O.add(F, O.mul(F, O.ofz(~F, S.Zpos{q}), zdot(~F, m, w)), _), zdot(~F, EL.vscale(S.Z.mul(SX.at(m, e), S.Zpos{di}), SX.unit(len, i)), w)), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      %zdot_vscale(~F, S.Z.mul(SX.at(m, e), S.Zpos{di}), SX.unit(len, i), w) : {O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), tval(~F, mi, di, i, S.Zpos{q}, w))) == O.mul(F, O.add(F, O.add(F, O.mul(F, O.ofz(~F, S.Zpos{q}), zdot(~F, m, w)), O.mul(F, O.ofz(~F, S.Z.neg(SX.at(m, e))), zdot(~F, mi, w))), _), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      %zdot_unit(~F, len, i, w, hi) : {O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), tval(~F, mi, di, i, S.Zpos{q}, w))) == O.mul(F, O.add(F, O.add(F, O.mul(F, O.ofz(~F, S.Zpos{q}), zdot(~F, m, w)), O.mul(F, O.ofz(~F, S.Z.neg(SX.at(m, e))), zdot(~F, mi, w))), O.mul(F, O.ofz(~F, S.Z.mul(SX.at(m, e), S.Zpos{di})), _)), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      %FR.ofz_neg(~F, SX.at(m, e)) : {O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), tval(~F, mi, di, i, S.Zpos{q}, w))) == O.mul(F, O.add(F, O.add(F, O.mul(F, O.ofz(~F, S.Zpos{q}), zdot(~F, m, w)), O.mul(F, _, zdot(~F, mi, w))), O.mul(F, O.ofz(~F, S.Z.mul(SX.at(m, e), S.Zpos{di})), fat(~F, w, i))), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      %FR.ofz_mul(~F, SX.at(m, e), S.Zpos{di}) : {O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), tval(~F, mi, di, i, S.Zpos{q}, w))) == O.mul(F, O.add(F, O.add(F, O.mul(F, O.ofz(~F, S.Zpos{q}), zdot(~F, m, w)), O.mul(F, O.neg(F, O.ofz(~F, SX.at(m, e))), zdot(~F, mi, w))), O.mul(F, _, fat(~F, w, i))), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      FO.eq_of_sub(~F, O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), O.mul(F, O.sub(~F, zdot(~F, mi, w), O.mul(F, O.ofp(~F, di), fat(~F, w, i))), O.inv(F, O.ofp(~F, q))))), O.mul(F, O.add(F, O.add(F, O.mul(F, O.ofp(~F, q), zdot(~F, m, w)), O.mul(F, O.neg(F, O.ofz(~F, SX.at(m, e))), zdot(~F, mi, w))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.ofp(~F, di)), fat(~F, w, i))), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))), FO.cert4(~F, O.sub(~F, O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), O.mul(F, O.sub(~F, zdot(~F, mi, w), O.mul(F, O.ofp(~F, di), fat(~F, w, i))), O.inv(F, O.ofp(~F, q))))), O.mul(F, O.add(F, O.add(F, O.mul(F, O.ofp(~F, q), zdot(~F, m, w)), O.mul(F, O.neg(F, O.ofz(~F, SX.at(m, e))), zdot(~F, mi, w))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.ofp(~F, di)), fat(~F, w, i))), O.inv(F, O.ofp(~F, S.Pos.mul(q, d))))), O.neg(F, O.mul(F, O.mul(F, O.add(F, O.sub(~F, O.mul(F, O.ofp(~F, q), zdot(~F, m, w)), O.mul(F, O.ofz(~F, SX.at(m, e)), zdot(~F, mi, w))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.ofp(~F, di)), fat(~F, w, i))), O.inv(F, O.ofp(~F, d))), O.inv(F, O.ofp(~F, q)))), O.sub(~F, O.mul(F, O.ofp(~F, S.Pos.mul(q, d)), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))), O.one(F)), O.mul(F, O.mul(F, O.mul(F, O.add(F, O.sub(~F, O.mul(F, O.ofp(~F, q), zdot(~F, m, w)), O.mul(F, O.ofz(~F, SX.at(m, e)), zdot(~F, mi, w))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.ofp(~F, di)), fat(~F, w, i))), O.inv(F, O.ofp(~F, d))), O.inv(F, O.ofp(~F, q))), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))), O.sub(~F, O.ofp(~F, S.Pos.mul(q, d)), O.mul(F, O.ofp(~F, q), O.ofp(~F, d))), O.neg(F, O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.mul(F, O.add(F, O.sub(~F, O.mul(F, O.ofp(~F, q), zdot(~F, m, w)), O.mul(F, O.ofz(~F, SX.at(m, e)), zdot(~F, mi, w))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.ofp(~F, di)), fat(~F, w, i))), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))), O.ofp(~F, d)), O.inv(F, O.ofp(~F, d))))), O.sub(~F, O.mul(F, O.ofp(~F, q), O.inv(F, O.ofp(~F, q))), O.one(F)), O.mul(F, O.add(F, O.sub(~F, O.mul(F, O.ofp(~F, q), zdot(~F, m, w)), O.mul(F, O.ofz(~F, SX.at(m, e)), zdot(~F, mi, w))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.ofp(~F, di)), fat(~F, w, i))), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))), O.sub(~F, O.mul(F, O.ofp(~F, d), O.inv(F, O.ofp(~F, d))), O.one(F)), FR.fring_eq(~F, [zdot(~F, m, w), zdot(~F, mi, w), O.ofz(~F, SX.at(m, e)), O.ofp(~F, di), fat(~F, w, i), O.ofp(~F, q), O.ofp(~F, d), O.inv(F, O.ofp(~F, S.Pos.mul(q, d))), O.ofp(~F, S.Pos.mul(q, d)), O.inv(F, O.ofp(~F, d)), O.inv(F, O.ofp(~F, q))], E.ZSub{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{9n}}, E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{9n}}, E.ZMul{E.ZSub{E.ZVar{1n}, E.ZMul{E.ZVar{3n}, E.ZVar{4n}}}, E.ZVar{10n}}}}, E.ZMul{E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{5n}, E.ZVar{0n}}, E.ZMul{E.ZNeg{E.ZVar{2n}}, E.ZVar{1n}}}, E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZVar{4n}}}, E.ZVar{7n}}}, E.ZAdd{E.ZAdd{E.ZAdd{E.ZMul{E.ZNeg{E.ZMul{E.ZMul{E.ZAdd{E.ZSub{E.ZMul{E.ZVar{5n}, E.ZVar{0n}}, E.ZMul{E.ZVar{2n}, E.ZVar{1n}}}, E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZVar{4n}}}, E.ZVar{9n}}, E.ZVar{10n}}}, E.ZSub{E.ZMul{E.ZVar{8n}, E.ZVar{7n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZMul{E.ZMul{E.ZMul{E.ZAdd{E.ZSub{E.ZMul{E.ZVar{5n}, E.ZVar{0n}}, E.ZMul{E.ZVar{2n}, E.ZVar{1n}}}, E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZVar{4n}}}, E.ZVar{9n}}, E.ZVar{10n}}, E.ZVar{7n}}, E.ZSub{E.ZVar{8n}, E.ZMul{E.ZVar{5n}, E.ZVar{6n}}}}}, E.ZMul{E.ZNeg{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{9n}}, E.ZMul{E.ZMul{E.ZMul{E.ZAdd{E.ZSub{E.ZMul{E.ZVar{5n}, E.ZVar{0n}}, E.ZMul{E.ZVar{2n}, E.ZVar{1n}}}, E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZVar{4n}}}, E.ZVar{7n}}, E.ZVar{6n}}, E.ZVar{9n}}}}, E.ZSub{E.ZMul{E.ZVar{5n}, E.ZVar{10n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZMul{E.ZAdd{E.ZSub{E.ZMul{E.ZVar{5n}, E.ZVar{0n}}, E.ZMul{E.ZVar{2n}, E.ZVar{1n}}}, E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZVar{4n}}}, E.ZVar{7n}}, E.ZSub{E.ZMul{E.ZVar{6n}, E.ZVar{9n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), QE.ofp_rel(~F, S.Pos.mul(q, d)), FO.sub_of_eq(~F, O.ofp(~F, S.Pos.mul(q, d)), O.mul(F, O.ofp(~F, q), O.ofp(~F, d)), Equal.sym(O.C(F), O.mul(F, O.ofp(~F, q), O.ofp(~F, d)), O.ofp(~F, S.Pos.mul(q, d)), FR.ofz_mul(~F, S.Zpos{q}, S.Zpos{d}))), FO.inv_rel(~F, O.ofp(~F, q), QE.ofp_ne(~F, q)), QE.ofp_rel(~F, d)))

def phi3.neg(~F: O.OField, +mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, +q: S.Pos, +len: Nat, r: SX.Rw, +w: M.Vec(~F), +hi: {SX.ltn(i, len) == True{} : Bool}) -> {rv(~F, r, wsub(~F, w, e, tval(~F, mi, di, i, S.Zneg{q}, w))) == rv(~F, SX.phi.go(False{}, mi, di, i, S.Zneg{q}, len, SX.at(SX.Rw.m(r), e), r), w) : O.C(F)}:
  match r:
    case SX.Rw{+d, +m}:
      %rv_wsub(~F, SX.Rw{d, m}, w, e, tval(~F, mi, di, i, S.Zneg{q}, w)) : {_ == O.mul(F, zdot(~F, EL.vadd(EL.vadd(EL.vscale(S.Zpos{q}, m), EL.vscale(S.Z.neg(S.Z.neg(SX.at(m, e))), mi)), EL.vscale(S.Z.mul(S.Z.neg(SX.at(m, e)), S.Zpos{di}), SX.unit(len, i))), w), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      %zdot_vadd(~F, EL.vadd(EL.vscale(S.Zpos{q}, m), EL.vscale(S.Z.neg(S.Z.neg(SX.at(m, e))), mi)), EL.vscale(S.Z.mul(S.Z.neg(SX.at(m, e)), S.Zpos{di}), SX.unit(len, i)), w) : {O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), tval(~F, mi, di, i, S.Zneg{q}, w))) == O.mul(F, _, O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      %zdot_vadd(~F, EL.vscale(S.Zpos{q}, m), EL.vscale(S.Z.neg(S.Z.neg(SX.at(m, e))), mi), w) : {O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), tval(~F, mi, di, i, S.Zneg{q}, w))) == O.mul(F, O.add(F, _, zdot(~F, EL.vscale(S.Z.mul(S.Z.neg(SX.at(m, e)), S.Zpos{di}), SX.unit(len, i)), w)), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      %zdot_vscale(~F, S.Zpos{q}, m, w) : {O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), tval(~F, mi, di, i, S.Zneg{q}, w))) == O.mul(F, O.add(F, O.add(F, _, zdot(~F, EL.vscale(S.Z.neg(S.Z.neg(SX.at(m, e))), mi), w)), zdot(~F, EL.vscale(S.Z.mul(S.Z.neg(SX.at(m, e)), S.Zpos{di}), SX.unit(len, i)), w)), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      %zdot_vscale(~F, S.Z.neg(S.Z.neg(SX.at(m, e))), mi, w) : {O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), tval(~F, mi, di, i, S.Zneg{q}, w))) == O.mul(F, O.add(F, O.add(F, O.mul(F, O.ofz(~F, S.Zpos{q}), zdot(~F, m, w)), _), zdot(~F, EL.vscale(S.Z.mul(S.Z.neg(SX.at(m, e)), S.Zpos{di}), SX.unit(len, i)), w)), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      %zdot_vscale(~F, S.Z.mul(S.Z.neg(SX.at(m, e)), S.Zpos{di}), SX.unit(len, i), w) : {O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), tval(~F, mi, di, i, S.Zneg{q}, w))) == O.mul(F, O.add(F, O.add(F, O.mul(F, O.ofz(~F, S.Zpos{q}), zdot(~F, m, w)), O.mul(F, O.ofz(~F, S.Z.neg(S.Z.neg(SX.at(m, e)))), zdot(~F, mi, w))), _), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      %zdot_unit(~F, len, i, w, hi) : {O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), tval(~F, mi, di, i, S.Zneg{q}, w))) == O.mul(F, O.add(F, O.add(F, O.mul(F, O.ofz(~F, S.Zpos{q}), zdot(~F, m, w)), O.mul(F, O.ofz(~F, S.Z.neg(S.Z.neg(SX.at(m, e)))), zdot(~F, mi, w))), O.mul(F, O.ofz(~F, S.Z.mul(S.Z.neg(SX.at(m, e)), S.Zpos{di})), _)), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      %FR.ofz_neg(~F, S.Z.neg(SX.at(m, e))) : {O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), tval(~F, mi, di, i, S.Zneg{q}, w))) == O.mul(F, O.add(F, O.add(F, O.mul(F, O.ofz(~F, S.Zpos{q}), zdot(~F, m, w)), O.mul(F, _, zdot(~F, mi, w))), O.mul(F, O.ofz(~F, S.Z.mul(S.Z.neg(SX.at(m, e)), S.Zpos{di})), fat(~F, w, i))), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      %FR.ofz_mul(~F, S.Z.neg(SX.at(m, e)), S.Zpos{di}) : {O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), tval(~F, mi, di, i, S.Zneg{q}, w))) == O.mul(F, O.add(F, O.add(F, O.mul(F, O.ofz(~F, S.Zpos{q}), zdot(~F, m, w)), O.mul(F, O.neg(F, O.ofz(~F, S.Z.neg(SX.at(m, e)))), zdot(~F, mi, w))), O.mul(F, _, fat(~F, w, i))), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      %FR.ofz_neg(~F, SX.at(m, e)) : {O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), tval(~F, mi, di, i, S.Zneg{q}, w))) == O.mul(F, O.add(F, O.add(F, O.mul(F, O.ofz(~F, S.Zpos{q}), zdot(~F, m, w)), O.mul(F, O.neg(F, _), zdot(~F, mi, w))), O.mul(F, O.mul(F, _, O.ofz(~F, S.Zpos{di})), fat(~F, w, i))), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))) : O.C(F)}
      FO.eq_of_sub(~F, O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), O.mul(F, O.sub(~F, zdot(~F, mi, w), O.mul(F, O.ofp(~F, di), fat(~F, w, i))), O.inv(F, O.neg(F, O.ofp(~F, q)))))), O.mul(F, O.add(F, O.add(F, O.mul(F, O.ofp(~F, q), zdot(~F, m, w)), O.mul(F, O.neg(F, O.neg(F, O.ofz(~F, SX.at(m, e)))), zdot(~F, mi, w))), O.mul(F, O.mul(F, O.neg(F, O.ofz(~F, SX.at(m, e))), O.ofp(~F, di)), fat(~F, w, i))), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))), FO.cert4(~F, O.sub(~F, O.sub(~F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.inv(F, O.ofp(~F, d))), O.mul(F, O.sub(~F, zdot(~F, mi, w), O.mul(F, O.ofp(~F, di), fat(~F, w, i))), O.inv(F, O.neg(F, O.ofp(~F, q)))))), O.mul(F, O.add(F, O.add(F, O.mul(F, O.ofp(~F, q), zdot(~F, m, w)), O.mul(F, O.neg(F, O.neg(F, O.ofz(~F, SX.at(m, e)))), zdot(~F, mi, w))), O.mul(F, O.mul(F, O.neg(F, O.ofz(~F, SX.at(m, e))), O.ofp(~F, di)), fat(~F, w, i))), O.inv(F, O.ofp(~F, S.Pos.mul(q, d))))), O.neg(F, O.mul(F, O.mul(F, O.add(F, O.sub(~F, O.mul(F, O.neg(F, O.ofp(~F, q)), zdot(~F, m, w)), O.mul(F, O.ofz(~F, SX.at(m, e)), zdot(~F, mi, w))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.ofp(~F, di)), fat(~F, w, i))), O.inv(F, O.ofp(~F, d))), O.inv(F, O.neg(F, O.ofp(~F, q))))), O.sub(~F, O.mul(F, O.ofp(~F, S.Pos.mul(q, d)), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))), O.one(F)), O.mul(F, O.mul(F, O.mul(F, O.add(F, O.sub(~F, O.mul(F, O.neg(F, O.ofp(~F, q)), zdot(~F, m, w)), O.mul(F, O.ofz(~F, SX.at(m, e)), zdot(~F, mi, w))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.ofp(~F, di)), fat(~F, w, i))), O.inv(F, O.ofp(~F, d))), O.inv(F, O.neg(F, O.ofp(~F, q)))), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))), O.sub(~F, O.ofp(~F, S.Pos.mul(q, d)), O.mul(F, O.ofp(~F, q), O.ofp(~F, d))), O.neg(F, O.add(F, O.mul(F, zdot(~F, m, w), O.inv(F, O.ofp(~F, d))), O.mul(F, O.mul(F, O.mul(F, O.add(F, O.sub(~F, O.mul(F, O.neg(F, O.ofp(~F, q)), zdot(~F, m, w)), O.mul(F, O.ofz(~F, SX.at(m, e)), zdot(~F, mi, w))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.ofp(~F, di)), fat(~F, w, i))), O.inv(F, O.ofp(~F, S.Pos.mul(q, d)))), O.ofp(~F, d)), O.inv(F, O.ofp(~F, d))))), O.sub(~F, O.mul(F, O.neg(F, O.ofp(~F, q)), O.inv(F, O.neg(F, O.ofp(~F, q)))), O.one(F)), O.neg(F, O.mul(F, O.add(F, O.sub(~F, O.mul(F, O.neg(F, O.ofp(~F, q)), zdot(~F, m, w)), O.mul(F, O.ofz(~F, SX.at(m, e)), zdot(~F, mi, w))), O.mul(F, O.mul(F, O.ofz(~F, SX.at(m, e)), O.ofp(~F, di)), fat(~F, w, i))), O.inv(F, O.ofp(~F, S.Pos.mul(q, d))))), O.sub(~F, O.mul(F, O.ofp(~F, d), O.inv(F, O.ofp(~F, d))), O.one(F)), FR.fring_eq(~F, [zdot(~F, m, w), zdot(~F, mi, w), O.ofz(~F, SX.at(m, e)), O.ofp(~F, di), fat(~F, w, i), O.ofp(~F, q), O.ofp(~F, d), O.inv(F, O.ofp(~F, S.Pos.mul(q, d))), O.ofp(~F, S.Pos.mul(q, d)), O.inv(F, O.ofp(~F, d)), O.inv(F, O.neg(F, O.ofp(~F, q)))], E.ZSub{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{9n}}, E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{9n}}, E.ZMul{E.ZSub{E.ZVar{1n}, E.ZMul{E.ZVar{3n}, E.ZVar{4n}}}, E.ZVar{10n}}}}, E.ZMul{E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{5n}, E.ZVar{0n}}, E.ZMul{E.ZNeg{E.ZNeg{E.ZVar{2n}}}, E.ZVar{1n}}}, E.ZMul{E.ZMul{E.ZNeg{E.ZVar{2n}}, E.ZVar{3n}}, E.ZVar{4n}}}, E.ZVar{7n}}}, E.ZAdd{E.ZAdd{E.ZAdd{E.ZMul{E.ZNeg{E.ZMul{E.ZMul{E.ZAdd{E.ZSub{E.ZMul{E.ZNeg{E.ZVar{5n}}, E.ZVar{0n}}, E.ZMul{E.ZVar{2n}, E.ZVar{1n}}}, E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZVar{4n}}}, E.ZVar{9n}}, E.ZVar{10n}}}, E.ZSub{E.ZMul{E.ZVar{8n}, E.ZVar{7n}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZMul{E.ZMul{E.ZMul{E.ZMul{E.ZAdd{E.ZSub{E.ZMul{E.ZNeg{E.ZVar{5n}}, E.ZVar{0n}}, E.ZMul{E.ZVar{2n}, E.ZVar{1n}}}, E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZVar{4n}}}, E.ZVar{9n}}, E.ZVar{10n}}, E.ZVar{7n}}, E.ZSub{E.ZVar{8n}, E.ZMul{E.ZVar{5n}, E.ZVar{6n}}}}}, E.ZMul{E.ZNeg{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{9n}}, E.ZMul{E.ZMul{E.ZMul{E.ZAdd{E.ZSub{E.ZMul{E.ZNeg{E.ZVar{5n}}, E.ZVar{0n}}, E.ZMul{E.ZVar{2n}, E.ZVar{1n}}}, E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZVar{4n}}}, E.ZVar{7n}}, E.ZVar{6n}}, E.ZVar{9n}}}}, E.ZSub{E.ZMul{E.ZNeg{E.ZVar{5n}}, E.ZVar{10n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, E.ZMul{E.ZNeg{E.ZMul{E.ZAdd{E.ZSub{E.ZMul{E.ZNeg{E.ZVar{5n}}, E.ZVar{0n}}, E.ZMul{E.ZVar{2n}, E.ZVar{1n}}}, E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}, E.ZVar{4n}}}, E.ZVar{7n}}}, E.ZSub{E.ZMul{E.ZVar{6n}, E.ZVar{9n}}, E.ZCst{S.Zpos{S.XH{}}}}}}, {==}), QE.ofp_rel(~F, S.Pos.mul(q, d)), FO.sub_of_eq(~F, O.ofp(~F, S.Pos.mul(q, d)), O.mul(F, O.ofp(~F, q), O.ofp(~F, d)), Equal.sym(O.C(F), O.mul(F, O.ofp(~F, q), O.ofp(~F, d)), O.ofp(~F, S.Pos.mul(q, d)), FR.ofz_mul(~F, S.Zpos{q}, S.Zpos{d}))), FO.inv_rel(~F, O.neg(F, O.ofp(~F, q)), ofz_ne(~F, S.Zneg{q}, {==})), QE.ofp_rel(~F, d)))


# a row with M_xe = c != 0: |p| D_x x = |p| M_x - sgn(p) c M_i + sgn(p) c D_i e_i
def phi3(~F: O.OField, +mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, p: S.Z, +len: Nat, r: SX.Rw, +w: M.Vec(~F), hp: {SX.iszero(p) == False{} : Bool}, +hi: {SX.ltn(i, len) == True{} : Bool}) -> {rv(~F, r, wsub(~F, w, e, tval(~F, mi, di, i, p, w))) == rv(~F, SX.phi.go(False{}, mi, di, i, p, len, SX.at(SX.Rw.m(r), e), r), w) : O.C(F)}:
  match p:
    case S.Z0{}:
      absurd({rv(~F, r, wsub(~F, w, e, tval(~F, mi, di, i, S.Z0{}, w))) == rv(~F, SX.phi.go(False{}, mi, di, i, S.Z0{}, len, SX.at(SX.Rw.m(r), e), r), w) : O.C(F)}, KA.tf(hp))
    case S.Zpos{+q}:
      phi3.pos(~F, mi, di, e, i, q, len, r, w, hi)
    case S.Zneg{+q}:
      phi3.neg(~F, mi, di, e, i, q, len, r, w, hi)

def phi_go_ok(~F: O.OField, b: Bool, +mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, +p: S.Z, +len: Nat, +r: SX.Rw, +w: M.Vec(~F), hb: {b == SX.iszero(SX.at(SX.Rw.m(r), e)) : Bool}, hp: {SX.iszero(p) == False{} : Bool}, hi: {SX.ltn(i, len) == True{} : Bool}) -> {rv(~F, r, wsub(~F, w, e, tval(~F, mi, di, i, p, w))) == rv(~F, SX.phi.go(b, mi, di, i, p, len, SX.at(SX.Rw.m(r), e), r), w) : O.C(F)}:
  match b:
    case True{}:
      phi2(~F, mi, di, e, i, p, r, w, hb)
    case False{}:
      phi3(~F, mi, di, e, i, p, len, r, w, hp, hi)

# the row at md (counting down) is the pivot row
def pivrow(rs: List<&2, SX.Rw>, md: Maybe<&2, Nat>, +di: S.Pos, +mi: List<&2, S.Z>) -> Data:
  match md:
    case None{}:
      Unit
    case Some{d}:
      {SX.rowat(rs, d) == SX.Rw{di, mi} : SX.Rw}

# every row after the pivot, read at w, is the old row at w - t(w) e_e
def phis_ok(~F: O.OField, +mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, +p: S.Z, +len: Nat, rs: List<&2, SX.Rw>, md: Maybe<&2, Nat>, +w: M.Vec(~F), h: pivrow(rs, md, di, mi), +hpe: {SX.at(mi, e) == p : S.Z}, +hp: {SX.iszero(p) == False{} : Bool}, +hi: {SX.ltn(i, len) == True{} : Bool}) -> {rmap(~F, rs, wsub(~F, w, e, tval(~F, mi, di, i, p, w))) == rmap(~F, SX.phis(mi, di, e, i, p, len, rs, md), w) : M.Vec(~F)}:
  match rs md:
    case Nil{} md:
      {==}
    case Con{+r, +t} None{}:
      %phi_go_ok(~F, SX.iszero(SX.at(SX.Rw.m(r), e)), mi, di, e, i, p, len, r, w, {==}, hp, hi) : {Con{rv(~F, r, wsub(~F, w, e, tval(~F, mi, di, i, p, w))), rmap(~F, t, wsub(~F, w, e, tval(~F, mi, di, i, p, w)))} == Con{_, rmap(~F, SX.phis(mi, di, e, i, p, len, t, None{}), w)} : M.Vec(~F)}
      %phis_ok(~F, mi, di, e, i, p, len, t, None{}, w, Unit{}, hpe, hp, hi) : {Con{rv(~F, r, wsub(~F, w, e, tval(~F, mi, di, i, p, w))), rmap(~F, t, wsub(~F, w, e, tval(~F, mi, di, i, p, w)))} == Con{rv(~F, r, wsub(~F, w, e, tval(~F, mi, di, i, p, w))), _} : M.Vec(~F)}
      {==}
    case Con{+r, +t} Some{0n}:
      %Equal.sym(SX.Rw, r, SX.Rw{di, mi}, h) : {Con{rv(~F, _, wsub(~F, w, e, tval(~F, mi, di, i, p, w))), rmap(~F, t, wsub(~F, w, e, tval(~F, mi, di, i, p, w)))} == Con{rv(~F, SX.Rw{S.XH{}, SX.unit(len, i)}, w), rmap(~F, SX.phis(mi, di, e, i, p, len, t, None{}), w)} : M.Vec(~F)}
      %phi1(~F, mi, di, e, i, p, len, w, hpe, hp, hi) : {Con{rv(~F, SX.Rw{di, mi}, wsub(~F, w, e, tval(~F, mi, di, i, p, w))), rmap(~F, t, wsub(~F, w, e, tval(~F, mi, di, i, p, w)))} == Con{_, rmap(~F, SX.phis(mi, di, e, i, p, len, t, None{}), w)} : M.Vec(~F)}
      %phis_ok(~F, mi, di, e, i, p, len, t, None{}, w, Unit{}, hpe, hp, hi) : {Con{rv(~F, SX.Rw{di, mi}, wsub(~F, w, e, tval(~F, mi, di, i, p, w))), rmap(~F, t, wsub(~F, w, e, tval(~F, mi, di, i, p, w)))} == Con{rv(~F, SX.Rw{di, mi}, wsub(~F, w, e, tval(~F, mi, di, i, p, w))), _} : M.Vec(~F)}
      {==}
    case Con{+r, +t} Some{1n+d}:
      %phi_go_ok(~F, SX.iszero(SX.at(SX.Rw.m(r), e)), mi, di, e, i, p, len, r, w, {==}, hp, hi) : {Con{rv(~F, r, wsub(~F, w, e, tval(~F, mi, di, i, p, w))), rmap(~F, t, wsub(~F, w, e, tval(~F, mi, di, i, p, w)))} == Con{_, rmap(~F, SX.phis(mi, di, e, i, p, len, t, Some{d}), w)} : M.Vec(~F)}
      %phis_ok(~F, mi, di, e, i, p, len, t, Some{d}, w, h, hpe, hp, hi) : {Con{rv(~F, r, wsub(~F, w, e, tval(~F, mi, di, i, p, w))), rmap(~F, t, wsub(~F, w, e, tval(~F, mi, di, i, p, w)))} == Con{rv(~F, r, wsub(~F, w, e, tval(~F, mi, di, i, p, w))), _} : M.Vec(~F)}
      {==}

# the pivot's step at w for the tableau's rows: i leaves, e enters
def pstep(~F: O.OField, +rows: List<&2, SX.Rw>, +i: Nat, +e: Nat, +w: M.Vec(~F)) -> O.C(F):
  tval(~F, SX.Rw.m(SX.rowat(rows, i)), SX.Rw.d(SX.rowat(rows, i)), i, SX.at(SX.Rw.m(SX.rowat(rows, i)), e), w)

def pivot_go_ok(~F: O.OField, ri: SX.Rw, +e: Nat, +i: Nat, +len: Nat, +rows: List<&2, SX.Rw>, +bas: List<&2, Bool>, +w: M.Vec(~F), h: {SX.rowat(rows, i) == ri : SX.Rw}, hp: {SX.iszero(SX.at(SX.Rw.m(ri), e)) == False{} : Bool}, hi: {SX.ltn(i, len) == True{} : Bool}) -> {rmap(~F, rows, wsub(~F, w, e, tval(~F, SX.Rw.m(ri), SX.Rw.d(ri), i, SX.at(SX.Rw.m(ri), e), w))) == rmap(~F, SX.Tab.rows(SX.pivot.go(ri, e, i, len, rows, bas)), w) : M.Vec(~F)}:
  match ri:
    case SX.Rw{+di, +mi}:
      phis_ok(~F, mi, di, e, i, SX.at(mi, e), len, rows, Some{i}, w, h, {==}, hp, hi)

# the tableau's rows after the pivot, read at w, are the old rows at
# w - t(w) e_e
def pivot_ok(~F: O.OField, +len: Nat, t: SX.Tab, +i: Nat, +e: Nat, +w: M.Vec(~F), hp: {SX.iszero(SX.at(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), e)) == False{} : Bool}, hi: {SX.ltn(i, len) == True{} : Bool}) -> {rmap(~F, SX.Tab.rows(t), wsub(~F, w, e, pstep(~F, SX.Tab.rows(t), i, e, w))) == rmap(~F, SX.Tab.rows(SX.pivot(len, t, i, e)), w) : M.Vec(~F)}:
  match t:
    case SX.Tab{+rows, +bas}:
      pivot_go_ok(~F, SX.rowat(rows, i), e, i, len, rows, bas, w, {==}, hp, hi)

# Points of the system, and the invariants
# ----------------------------------------
# A point gives every variable a value. It is a point of the system when
# each slack's entry is a_k . (the y entries), read by the slack's initial
# row (zeros at the slacks, then a_k). The dictionary keeps two facts, for
# every point:
# - I1: reading the rows at any w gives a point of the system;
# - I2: a point of the system satisfies every row (x_j = R_j . x).

def nrows(rs: List<&2, SX.Rw>) -> Nat:
  match rs:
    case Nil{}:
      0n
    case Con{r, t}:
      1n+nrows(t)

def invg(~F: O.OField, qs: List<&2, SX.Ineq>, +m: Nat, +x: M.Vec(~F), xr: M.Vec(~F)) -> Data:
  match qs xr:
    case Nil{} xr:
      Unit
    case Con{SX.Ineq{a, b, s}, qt} Nil{}:
      M.Both({O.zero(F) == zdot(~F, SX.cat(EL.zeros(m), a), x) : O.C(F)}, invg(~F, qt, m, x, Nil{}))
    case Con{SX.Ineq{a, b, s}, qt} Con{y, xt}:
      M.Both({y == zdot(~F, SX.cat(EL.zeros(m), a), x) : O.C(F)}, invg(~F, qt, m, x, xt))

def InV(~F: O.OField, +lp: SX.LP, +x: M.Vec(~F)) -> Data:
  invg(~F, SX.LP.qs(lp), SX.LP.m(lp), x, x)

# u agrees with v at each of v's entries (u reads 0 past its end)
def Agree(~F: O.OField, u: M.Vec(~F), v: M.Vec(~F)) -> Data:
  match u v:
    case Nil{} Nil{}:
      Unit
    case Nil{} Con{a, vt}:
      M.Both({O.zero(F) == a : O.C(F)}, Agree(~F, Nil{}, vt))
    case Con{y, ut} Nil{}:
      Unit
    case Con{y, ut} Con{a, vt}:
      M.Both({y == a : O.C(F)}, Agree(~F, ut, vt))

# x satisfies every row
def RSat(~F: O.OField, +rows: List<&2, SX.Rw>, +x: M.Vec(~F)) -> Data:
  Agree(~F, x, rmap(~F, rows, x))

def I1(~F: O.OField, +lp: SX.LP, +rows: List<&2, SX.Rw>) -> Type:
  @w: M.Vec(~F) -> InV(~F, lp, rmap(~F, rows, w))

def I2(~F: O.OField, +lp: SX.LP, +rows: List<&2, SX.Rw>) -> Type:
  @x: M.Vec(~F) -> InV(~F, lp, x) -> RSat(~F, rows, x)

def ltn0(j: Nat, h: {SX.ltn(j, 0n) == True{} : Bool}) -> {False{} == True{} : Bool}:
  match j:
    case 0n:
      h
    case 1n+k:
      h

# u agrees with the rows read at x: u_j = R_j . x, for j below the rows
def agree_at(~F: O.OField, rs: List<&2, SX.Rw>, +x: M.Vec(~F), u: M.Vec(~F), j: Nat, h: Agree(~F, u, rmap(~F, rs, x)), hj: {SX.ltn(j, nrows(rs)) == True{} : Bool}) -> {fat(~F, u, j) == rv(~F, SX.rowat(rs, j), x) : O.C(F)}:
  match rs u j:
    case Nil{} u j:
      absurd({fat(~F, u, j) == rv(~F, SX.rowat(Nil{}, j), x) : O.C(F)}, KA.ft(ltn0(j, hj)))
    case Con{r, t} Nil{} 0n:
      (h1, h2) = h
      h1
    case Con{r, t} Nil{} 1n+k:
      (h1, h2) = h
      agree_at(~F, t, x, Nil{}, k, h2, hj)
    case Con{r, t} Con{y, ut} 0n:
      (h1, h2) = h
      h1
    case Con{r, t} Con{y, ut} 1n+k:
      (h1, h2) = h
      agree_at(~F, t, x, ut, k, h2, hj)

# I1 survives a pivot
def i1_pivot.at(~F: O.OField, +lp: SX.LP, +len: Nat, +t: SX.Tab, +i: Nat, +e: Nat, +w: M.Vec(~F), h1: I1(~F, lp, SX.Tab.rows(t)), hp: {SX.iszero(SX.at(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), e)) == False{} : Bool}, hi: {SX.ltn(i, len) == True{} : Bool}) -> InV(~F, lp, rmap(~F, SX.Tab.rows(SX.pivot(len, t, i, e)), w)):
  %pivot_ok(~F, len, t, i, e, w, hp, hi) : InV(~F, lp, _)
  h1(wsub(~F, w, e, pstep(~F, SX.Tab.rows(t), i, e, w)))

def i1_pivot(~F: O.OField, +lp: SX.LP, +len: Nat, +t: SX.Tab, +i: Nat, +e: Nat, h1: I1(~F, lp, SX.Tab.rows(t)), hp: {SX.iszero(SX.at(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), e)) == False{} : Bool}, hi: {SX.ltn(i, len) == True{} : Bool}) -> I1(~F, lp, SX.Tab.rows(SX.pivot(len, t, i, e))):
  w => i1_pivot.at(~F, lp, len, t, i, e, w, h1, hp, hi)

# at a point satisfying the pivot row, the pivot's step is 0
def tzero(~F: O.OField, +rows: List<&2, SX.Rw>, +i: Nat, +e: Nat, +x: M.Vec(~F), h: {fat(~F, x, i) == rv(~F, SX.rowat(rows, i), x) : O.C(F)}) -> {O.zero(F) == pstep(~F, rows, i, e, x) : O.C(F)}:
  %Equal.sym(O.C(F), fat(~F, x, i), rv(~F, SX.rowat(rows, i), x), h) : {O.zero(F) == O.mul(F, O.sub(~F, zdot(~F, SX.Rw.m(SX.rowat(rows, i)), x), O.mul(F, O.ofp(~F, SX.Rw.d(SX.rowat(rows, i))), _)), O.inv(F, O.ofz(~F, SX.at(SX.Rw.m(SX.rowat(rows, i)), e)))) : O.C(F)}
  FO.eq_of_sub(~F, O.zero(F), O.mul(F, O.sub(~F, zdot(~F, SX.Rw.m(SX.rowat(rows, i)), x), O.mul(F, O.ofp(~F, SX.Rw.d(SX.rowat(rows, i))), O.mul(F, zdot(~F, SX.Rw.m(SX.rowat(rows, i)), x), O.inv(F, O.ofp(~F, SX.Rw.d(SX.rowat(rows, i))))))), O.inv(F, O.ofz(~F, SX.at(SX.Rw.m(SX.rowat(rows, i)), e)))), FO.cert1(~F, O.sub(~F, O.zero(F), O.mul(F, O.sub(~F, zdot(~F, SX.Rw.m(SX.rowat(rows, i)), x), O.mul(F, O.ofp(~F, SX.Rw.d(SX.rowat(rows, i))), O.mul(F, zdot(~F, SX.Rw.m(SX.rowat(rows, i)), x), O.inv(F, O.ofp(~F, SX.Rw.d(SX.rowat(rows, i))))))), O.inv(F, O.ofz(~F, SX.at(SX.Rw.m(SX.rowat(rows, i)), e))))), O.mul(F, zdot(~F, SX.Rw.m(SX.rowat(rows, i)), x), O.inv(F, O.ofz(~F, SX.at(SX.Rw.m(SX.rowat(rows, i)), e)))), O.sub(~F, O.mul(F, O.ofp(~F, SX.Rw.d(SX.rowat(rows, i))), O.inv(F, O.ofp(~F, SX.Rw.d(SX.rowat(rows, i))))), O.one(F)), FR.fring_eq(~F, [zdot(~F, SX.Rw.m(SX.rowat(rows, i)), x), O.ofp(~F, SX.Rw.d(SX.rowat(rows, i))), O.inv(F, O.ofp(~F, SX.Rw.d(SX.rowat(rows, i)))), O.inv(F, O.ofz(~F, SX.at(SX.Rw.m(SX.rowat(rows, i)), e)))], E.ZSub{E.ZCst{S.Z0{}}, E.ZMul{E.ZSub{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}}, E.ZVar{3n}}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZSub{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), QE.ofp_rel(~F, SX.Rw.d(SX.rowat(rows, i)))))

# lowering an entry by 0 changes no row's value
def rmap_wsub0(~F: O.OField, rs: List<&2, SX.Rw>, +x: M.Vec(~F), +e: Nat) -> {rmap(~F, rs, x) == rmap(~F, rs, wsub(~F, x, e, O.zero(F))) : M.Vec(~F)}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      %rv_wsub(~F, r, x, e, O.zero(F)) : {Con{rv(~F, r, x), rmap(~F, t, x)} == Con{_, rmap(~F, t, wsub(~F, x, e, O.zero(F)))} : M.Vec(~F)}
      %rmap_wsub0(~F, t, x, e) : {Con{rv(~F, r, x), rmap(~F, t, x)} == Con{O.sub(~F, rv(~F, r, x), O.mul(F, O.mul(F, O.ofz(~F, SX.at(SX.Rw.m(r), e)), O.inv(F, O.ofp(~F, SX.Rw.d(r)))), O.zero(F))), _} : M.Vec(~F)}
      %FR.fring_eq(~F, [rv(~F, r, x), O.ofz(~F, SX.at(SX.Rw.m(r), e)), O.inv(F, O.ofp(~F, SX.Rw.d(r)))], E.ZVar{0n}, E.ZSub{E.ZVar{0n}, E.ZMul{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZCst{S.Z0{}}}}, {==}) : {Con{rv(~F, r, x), rmap(~F, t, x)} == Con{_, rmap(~F, t, x)} : M.Vec(~F)}
      {==}

# I2 survives a pivot
def i2_pivot.at(~F: O.OField, +lp: SX.LP, +len: Nat, +t: SX.Tab, +i: Nat, +e: Nat, +x: M.Vec(~F), hx: InV(~F, lp, x), h2: I2(~F, lp, SX.Tab.rows(t)), hp: {SX.iszero(SX.at(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), e)) == False{} : Bool}, hi: {SX.ltn(i, len) == True{} : Bool}, hn: {SX.ltn(i, nrows(SX.Tab.rows(t))) == True{} : Bool}) -> RSat(~F, SX.Tab.rows(SX.pivot(len, t, i, e)), x):
  +old = h2(x, hx)
  %pivot_ok(~F, len, t, i, e, x, hp, hi) : Agree(~F, x, _)
  %tzero(~F, SX.Tab.rows(t), i, e, x, agree_at(~F, SX.Tab.rows(t), x, x, i, old, hn)) : Agree(~F, x, rmap(~F, SX.Tab.rows(t), wsub(~F, x, e, _)))
  %rmap_wsub0(~F, SX.Tab.rows(t), x, e) : Agree(~F, x, _)
  old

def i2_pivot(~F: O.OField, +lp: SX.LP, +len: Nat, +t: SX.Tab, +i: Nat, +e: Nat, h2: I2(~F, lp, SX.Tab.rows(t)), hp: {SX.iszero(SX.at(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), e)) == False{} : Bool}, hi: {SX.ltn(i, len) == True{} : Bool}, hn: {SX.ltn(i, nrows(SX.Tab.rows(t))) == True{} : Bool}) -> I2(~F, lp, SX.Tab.rows(SX.pivot(len, t, i, e))):
  x => hx => i2_pivot.at(~F, lp, len, t, i, e, x, hx, h2, hp, hi, hn)

# The basis
# ---------

# entry k of a Bool list (False past the end)
def bat(bs: List<&2, Bool>, k: Nat) -> Bool:
  match bs k:
    case Nil{} k:
      False{}
    case Con{b, t} 0n:
      b
    case Con{b, t} 1n+j:
      bat(t, j)

def blen(bs: List<&2, Bool>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case Con{b, t}:
      1n+blen(t)

# setting entry j to b: entry j is b
def bat_setb_eq(bs: List<&2, Bool>, j: Nat, +b: Bool, h: {SX.ltn(j, blen(bs)) == True{} : Bool}) -> {bat(SX.setb(bs, j, b), j) == b : Bool}:
  match bs j:
    case Nil{} j:
      absurd({bat(SX.setb(Nil{}, j, b), j) == b : Bool}, KA.ft(ltn0(j, h)))
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+k:
      bat_setb_eq(t, k, b, h)

# and the others are unchanged
def bat_setb_ne(bs: List<&2, Bool>, j: Nat, +b: Bool, k: Nat, h: {SX.eqn(k, j) == False{} : Bool}) -> {bat(bs, k) == bat(SX.setb(bs, j, b), k) : Bool}:
  match bs j k:
    case Nil{} j k:
      {==}
    case Con{x, t} 0n 0n:
      absurd({bat(Con{x, t}, 0n) == bat(SX.setb(Con{x, t}, 0n, b), 0n) : Bool}, KA.tf(h))
    case Con{x, t} 0n 1n+m:
      {==}
    case Con{x, t} 1n+i 0n:
      {==}
    case Con{x, t} 1n+i 1n+m:
      bat_setb_ne(t, i, b, m, h)

def blen_setb(bs: List<&2, Bool>, j: Nat, +b: Bool) -> {blen(bs) == blen(SX.setb(bs, j, b)) : Nat}:
  match bs j:
    case Nil{} j:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{+x, +t} 1n+k:
      %blen_setb(t, k, b) : {1n+blen(t) == 1n+_ : Nat}
      {==}

# lowering entry e leaves entry k != e alone
def fat_wsub_ne(~F: O.OField, w: M.Vec(~F), e: Nat, +t: O.C(F), k: Nat, h: {SX.eqn(k, e) == False{} : Bool}) -> {fat(~F, w, k) == fat(~F, wsub(~F, w, e, t), k) : O.C(F)}:
  match w e k:
    case Nil{} 0n 0n:
      absurd({fat(~F, Nil{}, 0n) == fat(~F, wsub(~F, Nil{}, 0n, t), 0n) : O.C(F)}, KA.tf(h))
    case Nil{} 0n 1n+m:
      {==}
    case Nil{} 1n+i 0n:
      {==}
    case Nil{} 1n+i 1n+m:
      fat_wsub_ne(~F, Nil{}, i, t, m, h)
    case Con{y, s} 0n 0n:
      absurd({fat(~F, Con{y, s}, 0n) == fat(~F, wsub(~F, Con{y, s}, 0n, t), 0n) : O.C(F)}, KA.tf(h))
    case Con{y, s} 0n 1n+m:
      {==}
    case Con{y, s} 1n+i 0n:
      {==}
    case Con{y, s} 1n+i 1n+m:
      fat_wsub_ne(~F, s, i, t, m, h)

# reading the rows at w, then entry k, is row k at w
def fat_rmap(~F: O.OField, rs: List<&2, SX.Rw>, +w: M.Vec(~F), k: Nat) -> {rv(~F, SX.rowat(rs, k), w) == fat(~F, rmap(~F, rs, w), k) : O.C(F)}:
  match rs k:
    case Nil{} k:
      FL.zero_mul(~F, O.inv(F, O.ofp(~F, S.XH{})))
    case Con{r, t} 0n:
      {==}
    case Con{r, t} 1n+j:
      fat_rmap(~F, t, w, j)

# IU: each nonbasic row (below len) reads off its own entry
def IU(~F: O.OField, +len: Nat, +t: SX.Tab) -> Type:
  @k: Nat -> {bat(SX.Tab.bas(t), k) == False{} : Bool} -> {SX.ltn(k, len) == True{} : Bool} -> @w: M.Vec(~F) -> {rv(~F, SX.rowat(SX.Tab.rows(t), k), w) == fat(~F, w, k) : O.C(F)}

def iu_piv_i.go(~F: O.OField, ri: SX.Rw, +rows: List<&2, SX.Rw>, +i: Nat, +e: Nat, +len: Nat, +w: M.Vec(~F), h: {SX.rowat(rows, i) == ri : SX.Rw}, hp: {SX.iszero(SX.at(SX.Rw.m(ri), e)) == False{} : Bool}, +hi: {SX.ltn(i, len) == True{} : Bool}) -> {rv(~F, ri, wsub(~F, w, e, tval(~F, SX.Rw.m(ri), SX.Rw.d(ri), i, SX.at(SX.Rw.m(ri), e), w))) == fat(~F, w, i) : O.C(F)}:
  match ri:
    case SX.Rw{+di, +mi}:
      %Equal.sym(O.C(F), rv(~F, SX.Rw{di, mi}, wsub(~F, w, e, tval(~F, mi, di, i, SX.at(mi, e), w))), rv(~F, SX.Rw{S.XH{}, SX.unit(len, i)}, w), phi1(~F, mi, di, e, i, SX.at(mi, e), len, w, {==}, hp, hi)) : {_ == fat(~F, w, i) : O.C(F)}
      %zdot_unit(~F, len, i, w, hi) : {O.mul(F, _, O.inv(F, O.ofp(~F, S.XH{}))) == fat(~F, w, i) : O.C(F)}
      FO.eq_of_sub(~F, O.mul(F, fat(~F, w, i), O.inv(F, O.ofp(~F, S.XH{}))), fat(~F, w, i), FO.cert1(~F, O.sub(~F, O.mul(F, fat(~F, w, i), O.inv(F, O.ofp(~F, S.XH{}))), fat(~F, w, i)), fat(~F, w, i), O.sub(~F, O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.XH{}))), O.one(F)), FR.fring_eq(~F, [fat(~F, w, i), O.inv(F, O.ofp(~F, S.XH{}))], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{0n}}, E.ZMul{E.ZVar{0n}, E.ZSub{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{1n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), QE.ofp_rel(~F, S.XH{})))

# the leaving variable's new row reads off its entry
def iu_piv_i(~F: O.OField, +len: Nat, +t: SX.Tab, +i: Nat, +e: Nat, +w: M.Vec(~F), +hp: {SX.iszero(SX.at(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), e)) == False{} : Bool}, +hi: {SX.ltn(i, len) == True{} : Bool}) -> {rv(~F, SX.rowat(SX.Tab.rows(SX.pivot(len, t, i, e)), i), w) == fat(~F, w, i) : O.C(F)}:
  %Equal.sym(O.C(F), rv(~F, SX.rowat(SX.Tab.rows(SX.pivot(len, t, i, e)), i), w), fat(~F, rmap(~F, SX.Tab.rows(SX.pivot(len, t, i, e)), w), i), fat_rmap(~F, SX.Tab.rows(SX.pivot(len, t, i, e)), w, i)) : {_ == fat(~F, w, i) : O.C(F)}
  %pivot_ok(~F, len, t, i, e, w, hp, hi) : {fat(~F, _, i) == fat(~F, w, i) : O.C(F)}
  %fat_rmap(~F, SX.Tab.rows(t), wsub(~F, w, e, pstep(~F, SX.Tab.rows(t), i, e, w)), i) : {_ == fat(~F, w, i) : O.C(F)}
  iu_piv_i.go(~F, SX.rowat(SX.Tab.rows(t), i), SX.Tab.rows(t), i, e, len, w, {==}, hp, hi)

# a row that stays nonbasic (k != i, k != e) still reads off its entry
def iu_piv_k(~F: O.OField, +len: Nat, +t: SX.Tab, +i: Nat, +e: Nat, +k: Nat, +w: M.Vec(~F), hu: IU(~F, len, t), hk: {bat(SX.Tab.bas(t), k) == False{} : Bool}, hkl: {SX.ltn(k, len) == True{} : Bool}, +hke: {SX.eqn(k, e) == False{} : Bool}, +hp: {SX.iszero(SX.at(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), e)) == False{} : Bool}, +hi: {SX.ltn(i, len) == True{} : Bool}) -> {rv(~F, SX.rowat(SX.Tab.rows(SX.pivot(len, t, i, e)), k), w) == fat(~F, w, k) : O.C(F)}:
  %Equal.sym(O.C(F), rv(~F, SX.rowat(SX.Tab.rows(SX.pivot(len, t, i, e)), k), w), fat(~F, rmap(~F, SX.Tab.rows(SX.pivot(len, t, i, e)), w), k), fat_rmap(~F, SX.Tab.rows(SX.pivot(len, t, i, e)), w, k)) : {_ == fat(~F, w, k) : O.C(F)}
  %pivot_ok(~F, len, t, i, e, w, hp, hi) : {fat(~F, _, k) == fat(~F, w, k) : O.C(F)}
  %fat_rmap(~F, SX.Tab.rows(t), wsub(~F, w, e, pstep(~F, SX.Tab.rows(t), i, e, w)), k) : {_ == fat(~F, w, k) : O.C(F)}
  %Equal.sym(O.C(F), rv(~F, SX.rowat(SX.Tab.rows(t), k), wsub(~F, w, e, pstep(~F, SX.Tab.rows(t), i, e, w))), fat(~F, wsub(~F, w, e, pstep(~F, SX.Tab.rows(t), i, e, w)), k), hu(k, hk, hkl, wsub(~F, w, e, pstep(~F, SX.Tab.rows(t), i, e, w)))) : {_ == fat(~F, w, k) : O.C(F)}
  Equal.sym(O.C(F), fat(~F, w, k), fat(~F, wsub(~F, w, e, pstep(~F, SX.Tab.rows(t), i, e, w)), k), fat_wsub_ne(~F, w, e, pstep(~F, SX.Tab.rows(t), i, e, w), k, hke))

def eqn_eq(a: Nat, b: Nat, h: {SX.eqn(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      absurd({0n == 1n+j : Nat}, KA.ft(h))
    case 1n+i 0n:
      absurd({1n+i == 0n : Nat}, KA.ft(h))
    case 1n+i 1n+j:
      %eqn_eq(i, j, h) : {1n+i == 1n+_ : Nat}
      {==}

def bas_pivot.go(ri: SX.Rw, +e: Nat, +i: Nat, +len: Nat, +rows: List<&2, SX.Rw>, +bas: List<&2, Bool>) -> {SX.setb(SX.setb(bas, i, False{}), e, True{}) == SX.Tab.bas(SX.pivot.go(ri, e, i, len, rows, bas)) : List<&2, Bool>}:
  match ri:
    case SX.Rw{di, mi}:
      {==}

# the pivot's basis: i out, e in
def bas_pivot(+len: Nat, t: SX.Tab, +i: Nat, +e: Nat) -> {SX.setb(SX.setb(SX.Tab.bas(t), i, False{}), e, True{}) == SX.Tab.bas(SX.pivot(len, t, i, e)) : List<&2, Bool>}:
  match t:
    case SX.Tab{+rows, +bas}:
      bas_pivot.go(SX.rowat(rows, i), e, i, len, rows, bas)

def nb_ne_e.c(+bas: List<&2, Bool>, +i: Nat, +e: Nat, +k: Nat, hke: {k == e : Nat}, hk: {bat(SX.setb(SX.setb(bas, i, False{}), e, True{}), k) == False{} : Bool}, he: {SX.ltn(e, blen(bas)) == True{} : Bool}) -> {True{} == False{} : Bool}:
  %bat_setb_eq(SX.setb(bas, i, False{}), e, True{}, (%blen_setb(bas, i, False{}) : {SX.ltn(e, _) == True{} : Bool}
    he)) : {_ == False{} : Bool}
  %hke : {bat(SX.setb(SX.setb(bas, i, False{}), e, True{}), _) == False{} : Bool}
  hk

def nb_ne_e.go(b: Bool, +bas: List<&2, Bool>, +i: Nat, +e: Nat, +k: Nat, hb: {b == SX.eqn(k, e) : Bool}, hk: {bat(SX.setb(SX.setb(bas, i, False{}), e, True{}), k) == False{} : Bool}, he: {SX.ltn(e, blen(bas)) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      absurd({True{} == False{} : Bool}, KA.tf(nb_ne_e.c(bas, i, e, k, eqn_eq(k, e, Equal.sym(Bool, True{}, SX.eqn(k, e), hb)), hk, he)))

# k is nonbasic after the pivot and not i: it is not e, and was nonbasic
def nb_ne_e(bas: List<&2, Bool>, +i: Nat, +e: Nat, +k: Nat, hk: {bat(SX.setb(SX.setb(bas, i, False{}), e, True{}), k) == False{} : Bool}, he: {SX.ltn(e, blen(bas)) == True{} : Bool}) -> {SX.eqn(k, e) == False{} : Bool}:
  nb_ne_e.go(SX.eqn(k, e), bas, i, e, k, {==}, hk, he)

def iu_pivot.k(~F: O.OField, b: Bool, +len: Nat, +t: SX.Tab, +i: Nat, +e: Nat, +k: Nat, +w: M.Vec(~F), +hb: {b == SX.eqn(k, i) : Bool}, hu: IU(~F, len, t), +hk: {bat(SX.setb(SX.setb(SX.Tab.bas(t), i, False{}), e, True{}), k) == False{} : Bool}, hkl: {SX.ltn(k, len) == True{} : Bool}, +hp: {SX.iszero(SX.at(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), e)) == False{} : Bool}, +hi: {SX.ltn(i, len) == True{} : Bool}, +he: {SX.ltn(e, blen(SX.Tab.bas(t))) == True{} : Bool}) -> {rv(~F, SX.rowat(SX.Tab.rows(SX.pivot(len, t, i, e)), k), w) == fat(~F, w, k) : O.C(F)}:
  match b:
    case True{}:
      %Equal.sym(Nat, k, i, eqn_eq(k, i, Equal.sym(Bool, True{}, SX.eqn(k, i), hb))) : {rv(~F, SX.rowat(SX.Tab.rows(SX.pivot(len, t, i, e)), _), w) == fat(~F, w, _) : O.C(F)}
      iu_piv_i(~F, len, t, i, e, w, hp, hi)
    case False{}:
      +hke = nb_ne_e(SX.Tab.bas(t), i, e, k, hk, he)
      iu_piv_k(~F, len, t, i, e, k, w, hu,
        (%Equal.sym(Bool, bat(SX.Tab.bas(t), k), bat(SX.setb(SX.Tab.bas(t), i, False{}), k), bat_setb_ne(SX.Tab.bas(t), i, False{}, k, Equal.sym(Bool, False{}, SX.eqn(k, i), hb))) : {_ == False{} : Bool}
         %Equal.sym(Bool, bat(SX.setb(SX.Tab.bas(t), i, False{}), k), bat(SX.setb(SX.setb(SX.Tab.bas(t), i, False{}), e, True{}), k), bat_setb_ne(SX.setb(SX.Tab.bas(t), i, False{}), e, True{}, k, hke)) : {_ == False{} : Bool}
         hk),
        hkl, hke, hp, hi)

def iu_pivot.at(~F: O.OField, +len: Nat, +t: SX.Tab, +i: Nat, +e: Nat, +k: Nat, hk: {bat(SX.Tab.bas(SX.pivot(len, t, i, e)), k) == False{} : Bool}, hkl: {SX.ltn(k, len) == True{} : Bool}, +w: M.Vec(~F), hu: IU(~F, len, t), +hp: {SX.iszero(SX.at(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), e)) == False{} : Bool}, +hi: {SX.ltn(i, len) == True{} : Bool}, +he: {SX.ltn(e, blen(SX.Tab.bas(t))) == True{} : Bool}) -> {rv(~F, SX.rowat(SX.Tab.rows(SX.pivot(len, t, i, e)), k), w) == fat(~F, w, k) : O.C(F)}:
  iu_pivot.k(~F, SX.eqn(k, i), len, t, i, e, k, w, {==}, hu, (%Equal.sym(List<&2, Bool>, SX.setb(SX.setb(SX.Tab.bas(t), i, False{}), e, True{}), SX.Tab.bas(SX.pivot(len, t, i, e)), bas_pivot(len, t, i, e)) : {bat(_, k) == False{} : Bool}
    hk), hkl, hp, hi, he)

# IU survives a pivot
def iu_pivot(~F: O.OField, +len: Nat, +t: SX.Tab, +i: Nat, +e: Nat, hu: IU(~F, len, t), +hp: {SX.iszero(SX.at(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), e)) == False{} : Bool}, +hi: {SX.ltn(i, len) == True{} : Bool}, +he: {SX.ltn(e, blen(SX.Tab.bas(t))) == True{} : Bool}) -> IU(~F, len, SX.pivot(len, t, i, e)):
  k => hk => hkl => w => iu_pivot.at(~F, len, t, i, e, k, hk, hkl, w, hu, hp, hi, he)

# IZ: every row is 0 at each basic column (integers)
# --------------------------------------------------

def at_zeros(n: Nat, j: Nat) -> {S.Z0{} == SX.at(EL.zeros(n), j) : S.Z}:
  match n j:
    case 0n j:
      {==}
    case 1n+k 0n:
      {==}
    case 1n+k 1n+h:
      at_zeros(k, h)

def at_unit_ne(len: Nat, i: Nat, j: Nat, h: {SX.eqn(j, i) == False{} : Bool}) -> {S.Z0{} == SX.at(SX.unit(len, i), j) : S.Z}:
  match len i j:
    case 0n i j:
      {==}
    case 1n+l 0n 0n:
      absurd({S.Z0{} == SX.at(SX.unit(1n+l, 0n), 0n) : S.Z}, KA.tf(h))
    case 1n+l 0n 1n+k:
      at_zeros(l, k)
    case 1n+l 1n+g 0n:
      {==}
    case 1n+l 1n+g 1n+k:
      at_unit_ne(l, g, k, h)

def at_vadd(u: List<&2, S.Z>, w: List<&2, S.Z>, j: Nat) -> {S.Z.add(SX.at(u, j), SX.at(w, j)) == SX.at(EL.vadd(u, w), j) : S.Z}:
  match u w j:
    case Nil{} Nil{} j:
      {==}
    case Nil{} Con{y, s} j:
      {==}
    case Con{+x, +t} Nil{} j:
      R.ring_eq([SX.at(Con{x, t}, j)], E.ZAdd{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZVar{0n}, {==})
    case Con{x, t} Con{y, s} 0n:
      {==}
    case Con{x, t} Con{y, s} 1n+k:
      at_vadd(t, s, k)

def at_vscale(+k: S.Z, u: List<&2, S.Z>, j: Nat) -> {S.Z.mul(k, SX.at(u, j)) == SX.at(EL.vscale(k, u), j) : S.Z}:
  match u j:
    case Nil{} j:
      R.ring_eq([k], E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+h:
      at_vscale(k, t, h)

# every row is 0 at column j
def zcol(rs: List<&2, SX.Rw>, +j: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, t}:
      KA.band(SX.iszero(SX.at(SX.Rw.m(r), j)), zcol(t, j))

def zcol_at(rs: List<&2, SX.Rw>, +j: Nat, k: Nat, h: {zcol(rs, j) == True{} : Bool}) -> {SX.iszero(SX.at(SX.Rw.m(SX.rowat(rs, k)), j)) == True{} : Bool}:
  match rs k:
    case Nil{} k:
      {==}
    case Con{+r, +t} 0n:
      KA.band_l(SX.iszero(SX.at(SX.Rw.m(r), j)), zcol(t, j), h)
    case Con{+r, +t} 1n+g:
      zcol_at(t, j, g, KA.band_r(SX.iszero(SX.at(SX.Rw.m(r), j)), zcol(t, j), h))

def IZ(+t: SX.Tab) -> Type:
  @j: Nat -> {bat(SX.Tab.bas(t), j) == True{} : Bool} -> {zcol(SX.Tab.rows(t), j) == True{} : Bool}

def iszero_of(+c: S.Z, e: {S.Z0{} == c : S.Z}) -> {SX.iszero(c) == True{} : Bool}:
  %e : {SX.iszero(_) == True{} : Bool}
  {==}

# entry j of a combined row
def comb_at(+mi: List<&2, S.Z>, +di: S.Pos, +i: Nat, +p: S.Z, +len: Nat, +c: S.Z, +m: List<&2, S.Z>, +j: Nat) -> {S.Z.add(S.Z.add(S.Z.mul(S.Zpos{EL.babs(p)}, SX.at(m, j)), S.Z.mul(S.Z.neg(EL.bsgn(p, c)), SX.at(mi, j))), S.Z.mul(S.Z.mul(EL.bsgn(p, c), S.Zpos{di}), SX.at(SX.unit(len, i), j))) == SX.at(EL.vadd(EL.vadd(EL.vscale(S.Zpos{EL.babs(p)}, m), EL.vscale(S.Z.neg(EL.bsgn(p, c)), mi)), EL.vscale(S.Z.mul(EL.bsgn(p, c), S.Zpos{di}), SX.unit(len, i))), j) : S.Z}:
  %at_vadd(EL.vadd(EL.vscale(S.Zpos{EL.babs(p)}, m), EL.vscale(S.Z.neg(EL.bsgn(p, c)), mi)), EL.vscale(S.Z.mul(EL.bsgn(p, c), S.Zpos{di}), SX.unit(len, i)), j) : {S.Z.add(S.Z.add(S.Z.mul(S.Zpos{EL.babs(p)}, SX.at(m, j)), S.Z.mul(S.Z.neg(EL.bsgn(p, c)), SX.at(mi, j))), S.Z.mul(S.Z.mul(EL.bsgn(p, c), S.Zpos{di}), SX.at(SX.unit(len, i), j))) == _ : S.Z}
  %at_vadd(EL.vscale(S.Zpos{EL.babs(p)}, m), EL.vscale(S.Z.neg(EL.bsgn(p, c)), mi), j) : {S.Z.add(S.Z.add(S.Z.mul(S.Zpos{EL.babs(p)}, SX.at(m, j)), S.Z.mul(S.Z.neg(EL.bsgn(p, c)), SX.at(mi, j))), S.Z.mul(S.Z.mul(EL.bsgn(p, c), S.Zpos{di}), SX.at(SX.unit(len, i), j))) == S.Z.add(_, SX.at(EL.vscale(S.Z.mul(EL.bsgn(p, c), S.Zpos{di}), SX.unit(len, i)), j)) : S.Z}
  %at_vscale(S.Zpos{EL.babs(p)}, m, j) : {S.Z.add(S.Z.add(S.Z.mul(S.Zpos{EL.babs(p)}, SX.at(m, j)), S.Z.mul(S.Z.neg(EL.bsgn(p, c)), SX.at(mi, j))), S.Z.mul(S.Z.mul(EL.bsgn(p, c), S.Zpos{di}), SX.at(SX.unit(len, i), j))) == S.Z.add(S.Z.add(_, SX.at(EL.vscale(S.Z.neg(EL.bsgn(p, c)), mi), j)), SX.at(EL.vscale(S.Z.mul(EL.bsgn(p, c), S.Zpos{di}), SX.unit(len, i)), j)) : S.Z}
  %at_vscale(S.Z.neg(EL.bsgn(p, c)), mi, j) : {S.Z.add(S.Z.add(S.Z.mul(S.Zpos{EL.babs(p)}, SX.at(m, j)), S.Z.mul(S.Z.neg(EL.bsgn(p, c)), SX.at(mi, j))), S.Z.mul(S.Z.mul(EL.bsgn(p, c), S.Zpos{di}), SX.at(SX.unit(len, i), j))) == S.Z.add(S.Z.add(S.Z.mul(S.Zpos{EL.babs(p)}, SX.at(m, j)), _), SX.at(EL.vscale(S.Z.mul(EL.bsgn(p, c), S.Zpos{di}), SX.unit(len, i)), j)) : S.Z}
  %at_vscale(S.Z.mul(EL.bsgn(p, c), S.Zpos{di}), SX.unit(len, i), j) : {S.Z.add(S.Z.add(S.Z.mul(S.Zpos{EL.babs(p)}, SX.at(m, j)), S.Z.mul(S.Z.neg(EL.bsgn(p, c)), SX.at(mi, j))), S.Z.mul(S.Z.mul(EL.bsgn(p, c), S.Zpos{di}), SX.at(SX.unit(len, i), j))) == S.Z.add(S.Z.add(S.Z.mul(S.Zpos{EL.babs(p)}, SX.at(m, j)), S.Z.mul(S.Z.neg(EL.bsgn(p, c)), SX.at(mi, j))), _) : S.Z}
  {==}

# |p| c - sgn(p) c p = 0
def zsum0(p: S.Z, +c: S.Z, +di: S.Pos, hp: {SX.iszero(p) == False{} : Bool}) -> {S.Z0{} == S.Z.add(S.Z.add(S.Z.mul(S.Zpos{EL.babs(p)}, c), S.Z.mul(S.Z.neg(EL.bsgn(p, c)), p)), S.Z.mul(S.Z.mul(EL.bsgn(p, c), S.Zpos{di}), S.Z0{})) : S.Z}:
  match p:
    case S.Z0{}:
      absurd({S.Z0{} == S.Z.add(S.Z.add(S.Z.mul(S.Zpos{EL.babs(S.Z0{})}, c), S.Z.mul(S.Z.neg(EL.bsgn(S.Z0{}, c)), S.Z0{})), S.Z.mul(S.Z.mul(EL.bsgn(S.Z0{}, c), S.Zpos{di}), S.Z0{})) : S.Z}, KA.tf(hp))
    case S.Zpos{+q}:
      R.ring_eq([S.Zpos{q}, c, S.Zpos{di}], E.ZCst{S.Z0{}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZNeg{E.ZVar{1n}}, E.ZVar{0n}}}, E.ZMul{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZCst{S.Z0{}}}}, {==})
    case S.Zneg{+q}:
      R.ring_eq([S.Zpos{q}, c, S.Zpos{di}], E.ZCst{S.Z0{}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZNeg{E.ZNeg{E.ZVar{1n}}}, E.ZNeg{E.ZVar{0n}}}}, E.ZMul{E.ZMul{E.ZNeg{E.ZVar{1n}}, E.ZVar{2n}}, E.ZCst{S.Z0{}}}}, {==})

# a combined row is 0 at the entering column
def rowz_e3(+mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, +p: S.Z, +len: Nat, r: SX.Rw, hpe: {SX.at(mi, e) == p : S.Z}, hp: {SX.iszero(p) == False{} : Bool}, hei: {SX.eqn(e, i) == False{} : Bool}) -> {SX.iszero(SX.at(SX.Rw.m(SX.phi.go(False{}, mi, di, i, p, len, SX.at(SX.Rw.m(r), e), r)), e)) == True{} : Bool}:
  match r:
    case SX.Rw{+d, +m}:
      iszero_of(SX.at(EL.vadd(EL.vadd(EL.vscale(S.Zpos{EL.babs(p)}, m), EL.vscale(S.Z.neg(EL.bsgn(p, SX.at(m, e))), mi)), EL.vscale(S.Z.mul(EL.bsgn(p, SX.at(m, e)), S.Zpos{di}), SX.unit(len, i))), e),
        Equal.trans(S.Z, S.Z0{}, S.Z.add(S.Z.add(S.Z.mul(S.Zpos{EL.babs(p)}, SX.at(m, e)), S.Z.mul(S.Z.neg(EL.bsgn(p, SX.at(m, e))), SX.at(mi, e))), S.Z.mul(S.Z.mul(EL.bsgn(p, SX.at(m, e)), S.Zpos{di}), SX.at(SX.unit(len, i), e))), SX.at(EL.vadd(EL.vadd(EL.vscale(S.Zpos{EL.babs(p)}, m), EL.vscale(S.Z.neg(EL.bsgn(p, SX.at(m, e))), mi)), EL.vscale(S.Z.mul(EL.bsgn(p, SX.at(m, e)), S.Zpos{di}), SX.unit(len, i))), e),
          (%Equal.sym(S.Z, SX.at(mi, e), p, hpe) : {S.Z0{} == S.Z.add(S.Z.add(S.Z.mul(S.Zpos{EL.babs(p)}, SX.at(m, e)), S.Z.mul(S.Z.neg(EL.bsgn(p, SX.at(m, e))), _)), S.Z.mul(S.Z.mul(EL.bsgn(p, SX.at(m, e)), S.Zpos{di}), SX.at(SX.unit(len, i), e))) : S.Z}
           %at_unit_ne(len, i, e, hei) : {S.Z0{} == S.Z.add(S.Z.add(S.Z.mul(S.Zpos{EL.babs(p)}, SX.at(m, e)), S.Z.mul(S.Z.neg(EL.bsgn(p, SX.at(m, e))), p)), S.Z.mul(S.Z.mul(EL.bsgn(p, SX.at(m, e)), S.Zpos{di}), _)) : S.Z}
           zsum0(p, SX.at(m, e), di, hp)),
          comb_at(mi, di, i, p, len, SX.at(m, e), m, e)))

def rowz_e(b: Bool, +mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, +p: S.Z, +len: Nat, +r: SX.Rw, hb: {b == SX.iszero(SX.at(SX.Rw.m(r), e)) : Bool}, hpe: {SX.at(mi, e) == p : S.Z}, hp: {SX.iszero(p) == False{} : Bool}, hei: {SX.eqn(e, i) == False{} : Bool}) -> {SX.iszero(SX.at(SX.Rw.m(SX.phi.go(b, mi, di, i, p, len, SX.at(SX.Rw.m(r), e), r)), e)) == True{} : Bool}:
  match b:
    case True{}:
      Equal.sym(Bool, True{}, SX.iszero(SX.at(SX.Rw.m(r), e)), hb)
    case False{}:
      rowz_e3(mi, di, e, i, p, len, r, hpe, hp, hei)

# after the pivot every row is 0 at the entering column
def zcol_e(+mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, +p: S.Z, +len: Nat, rs: List<&2, SX.Rw>, md: Maybe<&2, Nat>, +hpe: {SX.at(mi, e) == p : S.Z}, +hp: {SX.iszero(p) == False{} : Bool}, +hei: {SX.eqn(e, i) == False{} : Bool}) -> {zcol(SX.phis(mi, di, e, i, p, len, rs, md), e) == True{} : Bool}:
  match rs md:
    case Nil{} md:
      {==}
    case Con{+r, +t} None{}:
      KA.band_i(SX.iszero(SX.at(SX.Rw.m(SX.phi.go(SX.iszero(SX.at(SX.Rw.m(r), e)), mi, di, i, p, len, SX.at(SX.Rw.m(r), e), r)), e)), zcol(SX.phis(mi, di, e, i, p, len, t, None{}), e),
        rowz_e(SX.iszero(SX.at(SX.Rw.m(r), e)), mi, di, e, i, p, len, r, {==}, hpe, hp, hei), zcol_e(mi, di, e, i, p, len, t, None{}, hpe, hp, hei))
    case Con{+r, +t} Some{0n}:
      KA.band_i(SX.iszero(SX.at(SX.unit(len, i), e)), zcol(SX.phis(mi, di, e, i, p, len, t, None{}), e),
        iszero_of(SX.at(SX.unit(len, i), e), at_unit_ne(len, i, e, hei)), zcol_e(mi, di, e, i, p, len, t, None{}, hpe, hp, hei))
    case Con{+r, +t} Some{1n++d}:
      KA.band_i(SX.iszero(SX.at(SX.Rw.m(SX.phi.go(SX.iszero(SX.at(SX.Rw.m(r), e)), mi, di, i, p, len, SX.at(SX.Rw.m(r), e), r)), e)), zcol(SX.phis(mi, di, e, i, p, len, t, Some{d}), e),
        rowz_e(SX.iszero(SX.at(SX.Rw.m(r), e)), mi, di, e, i, p, len, r, {==}, hpe, hp, hei), zcol_e(mi, di, e, i, p, len, t, Some{d}, hpe, hp, hei))

# a combined row stays 0 at a column j != i where it and the pivot row
# were 0
def rowz_ne3(+mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, +p: S.Z, +len: Nat, r: SX.Rw, +j: Nat, hrz: {SX.iszero(SX.at(SX.Rw.m(r), j)) == True{} : Bool}, hzi: {SX.iszero(SX.at(mi, j)) == True{} : Bool}, hji: {SX.eqn(j, i) == False{} : Bool}) -> {SX.iszero(SX.at(SX.Rw.m(SX.phi.go(False{}, mi, di, i, p, len, SX.at(SX.Rw.m(r), e), r)), j)) == True{} : Bool}:
  match r:
    case SX.Rw{+d, +m}:
      iszero_of(SX.at(EL.vadd(EL.vadd(EL.vscale(S.Zpos{EL.babs(p)}, m), EL.vscale(S.Z.neg(EL.bsgn(p, SX.at(m, e))), mi)), EL.vscale(S.Z.mul(EL.bsgn(p, SX.at(m, e)), S.Zpos{di}), SX.unit(len, i))), j),
        Equal.trans(S.Z, S.Z0{}, S.Z.add(S.Z.add(S.Z.mul(S.Zpos{EL.babs(p)}, SX.at(m, j)), S.Z.mul(S.Z.neg(EL.bsgn(p, SX.at(m, e))), SX.at(mi, j))), S.Z.mul(S.Z.mul(EL.bsgn(p, SX.at(m, e)), S.Zpos{di}), SX.at(SX.unit(len, i), j))), SX.at(EL.vadd(EL.vadd(EL.vscale(S.Zpos{EL.babs(p)}, m), EL.vscale(S.Z.neg(EL.bsgn(p, SX.at(m, e))), mi)), EL.vscale(S.Z.mul(EL.bsgn(p, SX.at(m, e)), S.Zpos{di}), SX.unit(len, i))), j),
          (%iszero_eq(SX.at(m, j), Equal.sym(Bool, SX.iszero(SX.at(m, j)), True{}, hrz)) : {S.Z0{} == S.Z.add(S.Z.add(S.Z.mul(S.Zpos{EL.babs(p)}, _), S.Z.mul(S.Z.neg(EL.bsgn(p, SX.at(m, e))), SX.at(mi, j))), S.Z.mul(S.Z.mul(EL.bsgn(p, SX.at(m, e)), S.Zpos{di}), SX.at(SX.unit(len, i), j))) : S.Z}
           %iszero_eq(SX.at(mi, j), Equal.sym(Bool, SX.iszero(SX.at(mi, j)), True{}, hzi)) : {S.Z0{} == S.Z.add(S.Z.add(S.Z.mul(S.Zpos{EL.babs(p)}, S.Z0{}), S.Z.mul(S.Z.neg(EL.bsgn(p, SX.at(m, e))), _)), S.Z.mul(S.Z.mul(EL.bsgn(p, SX.at(m, e)), S.Zpos{di}), SX.at(SX.unit(len, i), j))) : S.Z}
           %at_unit_ne(len, i, j, hji) : {S.Z0{} == S.Z.add(S.Z.add(S.Z.mul(S.Zpos{EL.babs(p)}, S.Z0{}), S.Z.mul(S.Z.neg(EL.bsgn(p, SX.at(m, e))), S.Z0{})), S.Z.mul(S.Z.mul(EL.bsgn(p, SX.at(m, e)), S.Zpos{di}), _)) : S.Z}
           R.ring_eq([S.Zpos{EL.babs(p)}, S.Z.neg(EL.bsgn(p, SX.at(m, e))), S.Z.mul(EL.bsgn(p, SX.at(m, e)), S.Zpos{di})], E.ZCst{S.Z0{}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZMul{E.ZVar{1n}, E.ZCst{S.Z0{}}}}, E.ZMul{E.ZVar{2n}, E.ZCst{S.Z0{}}}}, {==})),
          comb_at(mi, di, i, p, len, SX.at(m, e), m, j)))

def rowz_ne(b: Bool, +mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, +p: S.Z, +len: Nat, +r: SX.Rw, +j: Nat, hb: {b == SX.iszero(SX.at(SX.Rw.m(r), e)) : Bool}, hrz: {SX.iszero(SX.at(SX.Rw.m(r), j)) == True{} : Bool}, hzi: {SX.iszero(SX.at(mi, j)) == True{} : Bool}, hji: {SX.eqn(j, i) == False{} : Bool}) -> {SX.iszero(SX.at(SX.Rw.m(SX.phi.go(b, mi, di, i, p, len, SX.at(SX.Rw.m(r), e), r)), j)) == True{} : Bool}:
  match b:
    case True{}:
      hrz
    case False{}:
      rowz_ne3(mi, di, e, i, p, len, r, j, hrz, hzi, hji)

# after the pivot every row is still 0 at a basic column j != i
def zcol_ne(+mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, +p: S.Z, +len: Nat, rs: List<&2, SX.Rw>, md: Maybe<&2, Nat>, +j: Nat, +hz: {zcol(rs, j) == True{} : Bool}, +hzi: {SX.iszero(SX.at(mi, j)) == True{} : Bool}, +hji: {SX.eqn(j, i) == False{} : Bool}) -> {zcol(SX.phis(mi, di, e, i, p, len, rs, md), j) == True{} : Bool}:
  match rs md:
    case Nil{} md:
      {==}
    case Con{+r, +t} None{}:
      KA.band_i(SX.iszero(SX.at(SX.Rw.m(SX.phi.go(SX.iszero(SX.at(SX.Rw.m(r), e)), mi, di, i, p, len, SX.at(SX.Rw.m(r), e), r)), j)), zcol(SX.phis(mi, di, e, i, p, len, t, None{}), j),
        rowz_ne(SX.iszero(SX.at(SX.Rw.m(r), e)), mi, di, e, i, p, len, r, j, {==}, KA.band_l(SX.iszero(SX.at(SX.Rw.m(r), j)), zcol(t, j), hz), hzi, hji),
        zcol_ne(mi, di, e, i, p, len, t, None{}, j, KA.band_r(SX.iszero(SX.at(SX.Rw.m(r), j)), zcol(t, j), hz), hzi, hji))
    case Con{+r, +t} Some{0n}:
      KA.band_i(SX.iszero(SX.at(SX.unit(len, i), j)), zcol(SX.phis(mi, di, e, i, p, len, t, None{}), j),
        iszero_of(SX.at(SX.unit(len, i), j), at_unit_ne(len, i, j, hji)),
        zcol_ne(mi, di, e, i, p, len, t, None{}, j, KA.band_r(SX.iszero(SX.at(SX.Rw.m(r), j)), zcol(t, j), hz), hzi, hji))
    case Con{+r, +t} Some{1n++d}:
      KA.band_i(SX.iszero(SX.at(SX.Rw.m(SX.phi.go(SX.iszero(SX.at(SX.Rw.m(r), e)), mi, di, i, p, len, SX.at(SX.Rw.m(r), e), r)), j)), zcol(SX.phis(mi, di, e, i, p, len, t, Some{d}), j),
        rowz_ne(SX.iszero(SX.at(SX.Rw.m(r), e)), mi, di, e, i, p, len, r, j, {==}, KA.band_l(SX.iszero(SX.at(SX.Rw.m(r), j)), zcol(t, j), hz), hzi, hji),
        zcol_ne(mi, di, e, i, p, len, t, Some{d}, j, KA.band_r(SX.iszero(SX.at(SX.Rw.m(r), j)), zcol(t, j), hz), hzi, hji))

def zcol_piv_e.go(ri: SX.Rw, +e: Nat, +i: Nat, +len: Nat, +rows: List<&2, SX.Rw>, +bas: List<&2, Bool>, hp: {SX.iszero(SX.at(SX.Rw.m(ri), e)) == False{} : Bool}, hei: {SX.eqn(e, i) == False{} : Bool}) -> {zcol(SX.Tab.rows(SX.pivot.go(ri, e, i, len, rows, bas)), e) == True{} : Bool}:
  match ri:
    case SX.Rw{+di, +mi}:
      zcol_e(mi, di, e, i, SX.at(mi, e), len, rows, Some{i}, {==}, hp, hei)

def zcol_piv_e(+len: Nat, t: SX.Tab, +i: Nat, +e: Nat, hp: {SX.iszero(SX.at(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), e)) == False{} : Bool}, hei: {SX.eqn(e, i) == False{} : Bool}) -> {zcol(SX.Tab.rows(SX.pivot(len, t, i, e)), e) == True{} : Bool}:
  match t:
    case SX.Tab{+rows, +bas}:
      zcol_piv_e.go(SX.rowat(rows, i), e, i, len, rows, bas, hp, hei)

def zcol_piv_ne.go(ri: SX.Rw, +e: Nat, +i: Nat, +len: Nat, +rows: List<&2, SX.Rw>, +bas: List<&2, Bool>, +j: Nat, h: {SX.rowat(rows, i) == ri : SX.Rw}, +hz: {zcol(rows, j) == True{} : Bool}, hji: {SX.eqn(j, i) == False{} : Bool}) -> {zcol(SX.Tab.rows(SX.pivot.go(ri, e, i, len, rows, bas)), j) == True{} : Bool}:
  match ri:
    case SX.Rw{+di, +mi}:
      zcol_ne(mi, di, e, i, SX.at(mi, e), len, rows, Some{i}, j, hz,
        (%h : {SX.iszero(SX.at(SX.Rw.m(_), j)) == True{} : Bool}
         zcol_at(rows, j, i, hz)), hji)

def zcol_piv_ne(+len: Nat, t: SX.Tab, +i: Nat, +e: Nat, +j: Nat, hz: {zcol(SX.Tab.rows(t), j) == True{} : Bool}, hji: {SX.eqn(j, i) == False{} : Bool}) -> {zcol(SX.Tab.rows(SX.pivot(len, t, i, e)), j) == True{} : Bool}:
  match t:
    case SX.Tab{+rows, +bas}:
      zcol_piv_ne.go(SX.rowat(rows, i), e, i, len, rows, bas, j, {==}, hz, hji)

# entry k of bs, k != j, from entry k after setting j
def bat_unset(bs: List<&2, Bool>, +j: Nat, +b: Bool, +k: Nat, hne: {SX.eqn(k, j) == False{} : Bool}, h: {bat(SX.setb(bs, j, b), k) == True{} : Bool}) -> {bat(bs, k) == True{} : Bool}:
  %Equal.sym(Bool, bat(bs, k), bat(SX.setb(bs, j, b), k), bat_setb_ne(bs, j, b, k, hne)) : {_ == True{} : Bool}
  h

def nb_ne_i.c(+bas: List<&2, Bool>, +i: Nat, +j: Nat, hji: {j == i : Nat}, h: {bat(SX.setb(bas, i, False{}), j) == True{} : Bool}, hil: {SX.ltn(i, blen(bas)) == True{} : Bool}) -> {False{} == True{} : Bool}:
  %bat_setb_eq(bas, i, False{}, hil) : {_ == True{} : Bool}
  %hji : {bat(SX.setb(bas, i, False{}), _) == True{} : Bool}
  h

# j is basic in bas with i set nonbasic: j != i
def nb_ne_i.go(b: Bool, +bas: List<&2, Bool>, +i: Nat, +j: Nat, hb: {b == SX.eqn(j, i) : Bool}, h: {bat(SX.setb(bas, i, False{}), j) == True{} : Bool}, hil: {SX.ltn(i, blen(bas)) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case False{}:
      {==}
    case True{}:
      absurd({True{} == False{} : Bool}, KA.ft(nb_ne_i.c(bas, i, j, eqn_eq(j, i, Equal.sym(Bool, True{}, SX.eqn(j, i), hb)), h, hil)))

def iz_pivot.j(b: Bool, +len: Nat, +t: SX.Tab, +i: Nat, +e: Nat, +j: Nat, hb: {b == SX.eqn(j, e) : Bool}, hj: {bat(SX.setb(SX.setb(SX.Tab.bas(t), i, False{}), e, True{}), j) == True{} : Bool}, hz: IZ(t), hp: {SX.iszero(SX.at(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), e)) == False{} : Bool}, hei: {SX.eqn(e, i) == False{} : Bool}, +hil: {SX.ltn(i, blen(SX.Tab.bas(t))) == True{} : Bool}) -> {zcol(SX.Tab.rows(SX.pivot(len, t, i, e)), j) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, j, e, eqn_eq(j, e, Equal.sym(Bool, True{}, SX.eqn(j, e), hb))) : {zcol(SX.Tab.rows(SX.pivot(len, t, i, e)), _) == True{} : Bool}
      zcol_piv_e(len, t, i, e, hp, hei)
    case False{}:
      +hj2 = bat_unset(SX.setb(SX.Tab.bas(t), i, False{}), e, True{}, j, Equal.sym(Bool, False{}, SX.eqn(j, e), hb), hj)
      +hji = nb_ne_i.go(SX.eqn(j, i), SX.Tab.bas(t), i, j, {==}, hj2, hil)
      zcol_piv_ne(len, t, i, e, j, hz(j, bat_unset(SX.Tab.bas(t), i, False{}, j, hji, hj2)), hji)

def iz_pivot.at(+len: Nat, +t: SX.Tab, +i: Nat, +e: Nat, +j: Nat, hj: {bat(SX.Tab.bas(SX.pivot(len, t, i, e)), j) == True{} : Bool}, hz: IZ(t), hp: {SX.iszero(SX.at(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), e)) == False{} : Bool}, hei: {SX.eqn(e, i) == False{} : Bool}, hil: {SX.ltn(i, blen(SX.Tab.bas(t))) == True{} : Bool}) -> {zcol(SX.Tab.rows(SX.pivot(len, t, i, e)), j) == True{} : Bool}:
  iz_pivot.j(SX.eqn(j, e), len, t, i, e, j, {==}, (%Equal.sym(List<&2, Bool>, SX.setb(SX.setb(SX.Tab.bas(t), i, False{}), e, True{}), SX.Tab.bas(SX.pivot(len, t, i, e)), bas_pivot(len, t, i, e)) : {bat(_, j) == True{} : Bool}
    hj), hz, hp, hei, hil)

# IZ survives a pivot
def iz_pivot(+len: Nat, +t: SX.Tab, +i: Nat, +e: Nat, hz: IZ(t), +hp: {SX.iszero(SX.at(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), e)) == False{} : Bool}, +hei: {SX.eqn(e, i) == False{} : Bool}, +hil: {SX.ltn(i, blen(SX.Tab.bas(t))) == True{} : Bool}) -> IZ(SX.pivot(len, t, i, e)):
  j => hj => iz_pivot.at(len, t, i, e, j, hj, hz, hp, hei, hil)

# The starting dictionary
# -----------------------
# Slacks basic with rows (1, zeros(m) ++ a_k), the y's nonbasic with rows
# (1, e_k). It satisfies every invariant when each a_k has at most n
# entries (lpwf).

def inv1(~F: O.OField) -> {O.inv(F, O.ofp(~F, S.XH{})) == O.one(F) : O.C(F)}:
  FO.eq_of_sub(~F, O.inv(F, O.ofp(~F, S.XH{})), O.one(F), FO.cert1(~F, O.sub(~F, O.inv(F, O.ofp(~F, S.XH{})), O.one(F)), O.one(F), O.sub(~F, O.mul(F, O.one(F), O.inv(F, O.ofp(~F, S.XH{}))), O.one(F)), FR.fring_eq(~F, [O.inv(F, O.ofp(~F, S.XH{}))], E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZSub{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}), QE.ofp_rel(~F, S.XH{})))

# every a_k has at most n entries
def lpwf.go(qs: List<&2, SX.Ineq>, +n: Nat) -> Bool:
  match qs:
    case Nil{}:
      True{}
    case Con{SX.Ineq{a, b, s}, t}:
      KA.band(KA.natle(SX.vlen(a), n), lpwf.go(t, n))

def lpwf(lp: SX.LP) -> Bool:
  match lp:
    case SX.LP{qs, +n}:
      lpwf.go(qs, n)

# F-vectors: append, and dropping the first k entries
def fcat(~F: O.OField, u: M.Vec(~F), w: M.Vec(~F)) -> M.Vec(~F):
  match u:
    case Nil{}:
      w
    case Con{x, t}:
      Con{x, fcat(~F, t, w)}

def ydrop(~F: O.OField, k: Nat, w: M.Vec(~F)) -> M.Vec(~F):
  match k w:
    case 0n w:
      w
    case 1n+j Nil{}:
      Nil{}
    case 1n+j Con{y, s}:
      ydrop(~F, j, s)

def rmap_rcat(~F: O.OField, u: List<&2, SX.Rw>, +v: List<&2, SX.Rw>, +w: M.Vec(~F)) -> {fcat(~F, rmap(~F, u, w), rmap(~F, v, w)) == rmap(~F, SX.rcat(u, v), w) : M.Vec(~F)}:
  match u:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      %rmap_rcat(~F, t, v, w) : {Con{rv(~F, r, w), fcat(~F, rmap(~F, t, w), rmap(~F, v, w))} == Con{rv(~F, r, w), _} : M.Vec(~F)}
      {==}

def len_srows(~F: O.OField, qs: List<&2, SX.Ineq>, +m: Nat, +w: M.Vec(~F)) -> {SX.qlen(qs) == M.len(~F, rmap(~F, SX.srows(qs, m), w)) : Nat}:
  match qs:
    case Nil{}:
      {==}
    case Con{SX.Ineq{a, b, s}, +t}:
      %len_srows(~F, t, m, w) : {1n+SX.qlen(t) == 1n+_ : Nat}
      {==}

def ydrop_fcat(~F: O.OField, u: M.Vec(~F), +w: M.Vec(~F)) -> {w == ydrop(~F, M.len(~F, u), fcat(~F, u, w)) : M.Vec(~F)}:
  match u:
    case Nil{}:
      {==}
    case Con{x, t}:
      ydrop_fcat(~F, t, w)

# zeros(m) ++ a against w is a against w from entry m
def zdot_cat_zeros(~F: O.OField, m: Nat, +a: List<&2, S.Z>, w: M.Vec(~F)) -> {zdot(~F, a, ydrop(~F, m, w)) == zdot(~F, SX.cat(EL.zeros(m), a), w) : O.C(F)}:
  match m w:
    case 0n w:
      {==}
    case 1n++j Nil{}:
      Equal.sym(O.C(F), O.zero(F), zdot(~F, a, Nil{}), zdot_nil_r(~F, a))
    case 1n++j Con{+y, +s}:
      %zdot_cat_zeros(~F, j, a, s) : {zdot(~F, a, ydrop(~F, j, s)) == O.add(F, O.mul(F, O.zero(F), y), _) : O.C(F)}
      FR.fring_eq(~F, [y, zdot(~F, a, ydrop(~F, j, s))], E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZVar{1n}}, {==})

# a . (w from k) splits off entry k
def zdot_ydrop(~F: O.OField, +x: S.Z, +at: List<&2, S.Z>, k: Nat, w: M.Vec(~F)) -> {O.add(F, O.mul(F, O.ofz(~F, x), fat(~F, w, k)), zdot(~F, at, ydrop(~F, 1n+k, w))) == zdot(~F, Con{x, at}, ydrop(~F, k, w)) : O.C(F)}:
  match k w:
    case 0n Nil{}:
      %zdot_nil_r(~F, at) : {O.add(F, O.mul(F, O.ofz(~F, x), O.zero(F)), _) == O.zero(F) : O.C(F)}
      FR.fring_eq(~F, [O.ofz(~F, x)], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})
    case 0n Con{y, s}:
      {==}
    case 1n+j Nil{}:
      %zdot_nil_r(~F, at) : {O.add(F, O.mul(F, O.ofz(~F, x), O.zero(F)), _) == O.zero(F) : O.C(F)}
      FR.fring_eq(~F, [O.ofz(~F, x)], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})
    case 1n+j Con{y, s}:
      zdot_ydrop(~F, x, at, j, s)

def ltn_of(a: Nat, b: Nat, h: {KA.natle(1n+a, b) == True{} : Bool}) -> {SX.ltn(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      absurd({SX.ltn(0n, 0n) == True{} : Bool}, KA.ft(h))
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      absurd({SX.ltn(1n+i, 0n) == True{} : Bool}, KA.ft(h))
    case 1n+i 1n+j:
      ltn_of(i, j, h)

# k + 1 + j <= N: k < N
def lt_of_add(+k: Nat, +j: Nat, +N: Nat, hk: {KA.natle(Nat.add(k, 1n+j), N) == True{} : Bool}) -> {SX.ltn(k, N) == True{} : Bool}:
  ltn_of(k, N, KA.natle_trans(1n+k, Nat.add(k, 1n+j), N, (%LN.add_succ(k, j) : {KA.natle(1n+k, _) == True{} : Bool}
    KA.natle_add_r(k, j)), hk))

# a . (the y rows from k, read at w) = a . (w from k), for a of at most c
# entries and units below N
def ydot(~F: O.OField, a: List<&2, S.Z>, c: Nat, +N: Nat, +k: Nat, +w: M.Vec(~F), ha: {KA.natle(SX.vlen(a), c) == True{} : Bool}, hk: {KA.natle(Nat.add(k, c), N) == True{} : Bool}) -> {O.mul(F, zdot(~F, a, ydrop(~F, k, w)), O.inv(F, O.ofp(~F, S.XH{}))) == zdot(~F, a, rmap(~F, SX.yrows(c, N, k), w)) : O.C(F)}:
  match a c:
    case Nil{} c:
      FL.zero_mul(~F, O.inv(F, O.ofp(~F, S.XH{})))
    case Con{x, at} 0n:
      absurd({O.mul(F, zdot(~F, Con{x, at}, ydrop(~F, k, w)), O.inv(F, O.ofp(~F, S.XH{}))) == zdot(~F, Con{x, at}, rmap(~F, SX.yrows(0n, N, k), w)) : O.C(F)}, KA.ft(ha))
    case Con{+x, +at} 1n++j:
      +hk2 = hk
      %ydot(~F, at, j, N, 1n+k, w, ha, (%Equal.sym(Nat, 1n+Nat.add(k, j), Nat.add(k, 1n+j), LN.add_succ(k, j)) : {KA.natle(_, N) == True{} : Bool}
        hk2)) : {O.mul(F, zdot(~F, Con{x, at}, ydrop(~F, k, w)), O.inv(F, O.ofp(~F, S.XH{}))) == O.add(F, O.mul(F, O.ofz(~F, x), O.mul(F, zdot(~F, SX.unit(N, k), w), O.inv(F, O.ofp(~F, S.XH{})))), _) : O.C(F)}
      %zdot_unit(~F, N, k, w, lt_of_add(k, j, N, hk2)) : {O.mul(F, zdot(~F, Con{x, at}, ydrop(~F, k, w)), O.inv(F, O.ofp(~F, S.XH{}))) == O.add(F, O.mul(F, O.ofz(~F, x), O.mul(F, _, O.inv(F, O.ofp(~F, S.XH{})))), O.mul(F, zdot(~F, at, ydrop(~F, 1n+k, w)), O.inv(F, O.ofp(~F, S.XH{})))) : O.C(F)}
      %zdot_ydrop(~F, x, at, k, w) : {O.mul(F, _, O.inv(F, O.ofp(~F, S.XH{}))) == O.add(F, O.mul(F, O.ofz(~F, x), O.mul(F, fat(~F, w, k), O.inv(F, O.ofp(~F, S.XH{})))), O.mul(F, zdot(~F, at, ydrop(~F, 1n+k, w)), O.inv(F, O.ofp(~F, S.XH{})))) : O.C(F)}
      FR.fring_eq(~F, [O.ofz(~F, x), fat(~F, w, k), zdot(~F, at, ydrop(~F, 1n+k, w)), O.inv(F, O.ofp(~F, S.XH{}))], E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZVar{3n}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, E.ZMul{E.ZVar{2n}, E.ZVar{3n}}}, {==})

# the slack rows of the start, read at w, against X = S ++ Y (S the slack
# rows' values, m of them; Y the y rows' values)
def i1w(~F: O.OField, qs: List<&2, SX.Ineq>, +m: Nat, +n: Nat, +S: M.Vec(~F), +w: M.Vec(~F), hS: {M.len(~F, S) == m : Nat}, hwf: {lpwf.go(qs, n) == True{} : Bool}) -> invg(~F, qs, m, fcat(~F, S, rmap(~F, SX.yrows(n, Nat.add(m, n), m), w)), fcat(~F, rmap(~F, SX.srows(qs, m), w), rmap(~F, SX.yrows(n, Nat.add(m, n), m), w))):
  match qs:
    case Nil{}:
      Unit{}
    case Con{SX.Ineq{+a, b, s}, +qt}:
      +hS2 = hS
      +hwf2 = hwf
      ((%zdot_cat_zeros(~F, m, a, w) : {O.mul(F, _, O.inv(F, O.ofp(~F, S.XH{}))) == zdot(~F, SX.cat(EL.zeros(m), a), fcat(~F, S, rmap(~F, SX.yrows(n, Nat.add(m, n), m), w))) : O.C(F)}
        %Equal.sym(O.C(F), O.mul(F, zdot(~F, a, ydrop(~F, m, w)), O.inv(F, O.ofp(~F, S.XH{}))), zdot(~F, a, rmap(~F, SX.yrows(n, Nat.add(m, n), m), w)), ydot(~F, a, n, Nat.add(m, n), m, w, KA.band_l(KA.natle(SX.vlen(a), n), lpwf.go(qt, n), hwf2), KA.natle_refl(Nat.add(m, n)))) : {_ == zdot(~F, SX.cat(EL.zeros(m), a), fcat(~F, S, rmap(~F, SX.yrows(n, Nat.add(m, n), m), w))) : O.C(F)}
        %zdot_cat_zeros(~F, m, a, fcat(~F, S, rmap(~F, SX.yrows(n, Nat.add(m, n), m), w))) : {zdot(~F, a, rmap(~F, SX.yrows(n, Nat.add(m, n), m), w)) == _ : O.C(F)}
        %hS2 : {zdot(~F, a, rmap(~F, SX.yrows(n, Nat.add(m, n), m), w)) == zdot(~F, a, ydrop(~F, _, fcat(~F, S, rmap(~F, SX.yrows(n, Nat.add(m, n), m), w)))) : O.C(F)}
        %ydrop_fcat(~F, S, rmap(~F, SX.yrows(n, Nat.add(m, n), m), w)) : {zdot(~F, a, rmap(~F, SX.yrows(n, Nat.add(m, n), m), w)) == zdot(~F, a, _) : O.C(F)}
        {==}),
       i1w(~F, qt, m, n, S, w, hS2, KA.band_r(KA.natle(SX.vlen(a), n), lpwf.go(qt, n), hwf2)))

def i1_init.go(~F: O.OField, +qs: List<&2, SX.Ineq>, +n: Nat, +w: M.Vec(~F), hwf: {lpwf.go(qs, n) == True{} : Bool}) -> InV(~F, SX.LP{qs, n}, rmap(~F, SX.Tab.rows(SX.init(SX.LP{qs, n})), w)):
  %rmap_rcat(~F, SX.srows(qs, SX.qlen(qs)), SX.yrows(n, Nat.add(SX.qlen(qs), n), SX.qlen(qs)), w) : invg(~F, qs, SX.qlen(qs), _, _)
  i1w(~F, qs, SX.qlen(qs), n, rmap(~F, SX.srows(qs, SX.qlen(qs)), w), w, Equal.sym(Nat, SX.qlen(qs), M.len(~F, rmap(~F, SX.srows(qs, SX.qlen(qs)), w)), len_srows(~F, qs, SX.qlen(qs), w)), hwf)

# I1 at the start
def i1_init(~F: O.OField, lp: SX.LP, hwf: {lpwf(lp) == True{} : Bool}) -> I1(~F, lp, SX.Tab.rows(SX.init(lp))):
  match lp:
    case SX.LP{+qs, +n}:
      w => i1_init.go(~F, qs, n, w, hwf)

def fhd(~F: O.OField, u: M.Vec(~F)) -> O.C(F):
  match u:
    case Nil{}:
      O.zero(F)
    case Con{y, s}:
      y

def ftl(~F: O.OField, u: M.Vec(~F)) -> M.Vec(~F):
  match u:
    case Nil{}:
      Nil{}
    case Con{y, s}:
      s

def fhd_ydrop(~F: O.OField, k: Nat, x: M.Vec(~F)) -> {fat(~F, x, k) == fhd(~F, ydrop(~F, k, x)) : O.C(F)}:
  match k x:
    case 0n Nil{}:
      {==}
    case 0n Con{y, s}:
      {==}
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{y, s}:
      fhd_ydrop(~F, j, s)

def ftl_ydrop(~F: O.OField, k: Nat, x: M.Vec(~F)) -> {ydrop(~F, 1n+k, x) == ftl(~F, ydrop(~F, k, x)) : M.Vec(~F)}:
  match k x:
    case 0n Nil{}:
      {==}
    case 0n Con{y, s}:
      {==}
    case 1n+j Nil{}:
      {==}
    case 1n+j Con{y, s}:
      ftl_ydrop(~F, j, s)

def ydrop_nil(~F: O.OField, k: Nat) -> {Nil{} == ydrop(~F, k, Nil{}) : M.Vec(~F)}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      {==}

def agree_nil(~F: O.OField, u: M.Vec(~F)) -> Agree(~F, u, Nil{}):
  match u:
    case Nil{}:
      Unit{}
    case Con{y, s}:
      Unit{}

def agree_cons(~F: O.OField, u: M.Vec(~F), +v: O.C(F), +vt: M.Vec(~F), hh: {fhd(~F, u) == v : O.C(F)}, ht: Agree(~F, ftl(~F, u), vt)) -> Agree(~F, u, Con{v, vt}):
  match u:
    case Nil{}:
      (hh, ht)
    case Con{y, s}:
      (hh, ht)

# a value times 1/1 is itself
def by_inv1(~F: O.OField, +y: O.C(F), +z: O.C(F), h: {y == z : O.C(F)}) -> {y == O.mul(F, z, O.inv(F, O.ofp(~F, S.XH{}))) : O.C(F)}:
  %Equal.sym(O.C(F), O.inv(F, O.ofp(~F, S.XH{})), O.one(F), inv1(~F)) : {y == O.mul(F, z, _) : O.C(F)}
  %FL.mul_one(~F, z) : {y == _ : O.C(F)}
  h

# the y rows from k agree with x from k
def agree_y(~F: O.OField, c: Nat, +N: Nat, +k: Nat, +x: M.Vec(~F), hk: {KA.natle(Nat.add(k, c), N) == True{} : Bool}) -> Agree(~F, ydrop(~F, k, x), rmap(~F, SX.yrows(c, N, k), x)):
  match c:
    case 0n:
      agree_nil(~F, ydrop(~F, k, x))
    case 1n++j:
      +hk2 = hk
      agree_cons(~F, ydrop(~F, k, x), rv(~F, SX.Rw{S.XH{}, SX.unit(N, k)}, x), rmap(~F, SX.yrows(j, N, 1n+k), x),
        (%fhd_ydrop(~F, k, x) : {_ == rv(~F, SX.Rw{S.XH{}, SX.unit(N, k)}, x) : O.C(F)}
         by_inv1(~F, fat(~F, x, k), zdot(~F, SX.unit(N, k), x), zdot_unit(~F, N, k, x, lt_of_add(k, j, N, hk2)))),
        (%ftl_ydrop(~F, k, x) : Agree(~F, _, rmap(~F, SX.yrows(j, N, 1n+k), x))
         agree_y(~F, j, N, 1n+k, x, (%Equal.sym(Nat, 1n+Nat.add(k, j), Nat.add(k, 1n+j), LN.add_succ(k, j)) : {KA.natle(_, N) == True{} : Bool}
           hk2))))

# the slack rows of the start agree with x, given the system's condition
def i2w(~F: O.OField, qs: List<&2, SX.Ineq>, +m: Nat, +n: Nat, +x: M.Vec(~F), xr: M.Vec(~F), h: invg(~F, qs, m, x, xr), ht: Agree(~F, ydrop(~F, SX.qlen(qs), xr), rmap(~F, SX.yrows(n, Nat.add(m, n), m), x))) -> Agree(~F, xr, fcat(~F, rmap(~F, SX.srows(qs, m), x), rmap(~F, SX.yrows(n, Nat.add(m, n), m), x))):
  match qs xr:
    case Nil{} xr:
      ht
    case Con{SX.Ineq{+a, b, s}, +qt} Nil{}:
      (h1, h2) = h
      ((%Equal.sym(O.C(F), O.inv(F, O.ofp(~F, S.XH{})), O.one(F), inv1(~F)) : {O.zero(F) == O.mul(F, zdot(~F, SX.cat(EL.zeros(m), a), x), _) : O.C(F)}
        %h1 : {O.zero(F) == O.mul(F, _, O.one(F)) : O.C(F)}
        Equal.sym(O.C(F), O.mul(F, O.zero(F), O.one(F)), O.zero(F), FL.zero_mul(~F, O.one(F)))),
       i2w(~F, qt, m, n, x, Nil{}, h2, (%ydrop_nil(~F, SX.qlen(qt)) : Agree(~F, _, rmap(~F, SX.yrows(n, Nat.add(m, n), m), x))
         ht)))
    case Con{SX.Ineq{+a, b, s}, +qt} Con{+y, +xt}:
      (h1, h2) = h
      (by_inv1(~F, y, zdot(~F, SX.cat(EL.zeros(m), a), x), h1), i2w(~F, qt, m, n, x, xt, h2, ht))

def i2_init.go(~F: O.OField, +qs: List<&2, SX.Ineq>, +n: Nat, +x: M.Vec(~F), hx: InV(~F, SX.LP{qs, n}, x)) -> RSat(~F, SX.Tab.rows(SX.init(SX.LP{qs, n})), x):
  %rmap_rcat(~F, SX.srows(qs, SX.qlen(qs)), SX.yrows(n, Nat.add(SX.qlen(qs), n), SX.qlen(qs)), x) : Agree(~F, x, _)
  i2w(~F, qs, SX.qlen(qs), n, x, x, hx, agree_y(~F, n, Nat.add(SX.qlen(qs), n), SX.qlen(qs), x, KA.natle_refl(Nat.add(SX.qlen(qs), n))))

# I2 at the start
def i2_init(~F: O.OField, lp: SX.LP) -> I2(~F, lp, SX.Tab.rows(SX.init(lp))):
  match lp:
    case SX.LP{+qs, +n}:
      x => hx => i2_init.go(~F, qs, n, x, hx)

def ltn_add_cancel(m: Nat, +k: Nat, +n: Nat, h: {SX.ltn(Nat.add(m, k), Nat.add(m, n)) == True{} : Bool}) -> {SX.ltn(k, n) == True{} : Bool}:
  match m:
    case 0n:
      h
    case 1n+j:
      ltn_add_cancel(j, k, n, h)

def yrow_at(c: Nat, +N: Nat, +i: Nat, k: Nat, hk: {SX.ltn(k, c) == True{} : Bool}) -> {SX.rowat(SX.yrows(c, N, i), k) == SX.Rw{S.XH{}, SX.unit(N, Nat.add(k, i))} : SX.Rw}:
  match c k:
    case 0n k:
      absurd({SX.rowat(SX.yrows(0n, N, i), k) == SX.Rw{S.XH{}, SX.unit(N, Nat.add(k, i))} : SX.Rw}, KA.ft(ltn0(k, hk)))
    case 1n+j 0n:
      {==}
    case 1n+j 1n++h:
      %Equal.sym(Nat, 1n+Nat.add(h, i), Nat.add(h, 1n+i), LN.add_succ(h, i)) : {SX.rowat(SX.yrows(j, N, 1n+i), h) == SX.Rw{S.XH{}, SX.unit(N, _)} : SX.Rw}
      yrow_at(j, N, 1n+i, h, hk)

def off_eq(+off: Nat, +m: Nat, h: {Nat.add(off, 0n) == m : Nat}) -> {off == m : Nat}:
  %Equal.sym(Nat, off, Nat.add(off, 0n), LN.add_zero(off)) : {_ == m : Nat}
  h

# the y rows of the start read off their entries
def iu0.base(~F: O.OField, +m: Nat, +n: Nat, +k: Nat, +w: M.Vec(~F), +hk: {SX.ltn(Nat.add(m, k), Nat.add(m, n)) == True{} : Bool}) -> {rv(~F, SX.rowat(SX.yrows(n, Nat.add(m, n), m), k), w) == fat(~F, w, Nat.add(m, k)) : O.C(F)}:
  %Equal.sym(SX.Rw, SX.rowat(SX.yrows(n, Nat.add(m, n), m), k), SX.Rw{S.XH{}, SX.unit(Nat.add(m, n), Nat.add(k, m))}, yrow_at(n, Nat.add(m, n), m, k, ltn_add_cancel(m, k, n, hk))) : {rv(~F, _, w) == fat(~F, w, Nat.add(m, k)) : O.C(F)}
  %LN.add_comm(k, m) : {rv(~F, SX.Rw{S.XH{}, SX.unit(Nat.add(m, n), Nat.add(k, m))}, w) == fat(~F, w, _) : O.C(F)}
  Equal.sym(O.C(F), fat(~F, w, Nat.add(k, m)), rv(~F, SX.Rw{S.XH{}, SX.unit(Nat.add(m, n), Nat.add(k, m))}, w), by_inv1(~F, fat(~F, w, Nat.add(k, m)), zdot(~F, SX.unit(Nat.add(m, n), Nat.add(k, m)), w), zdot_unit(~F, Nat.add(m, n), Nat.add(k, m), w, (%LN.add_comm(m, k) : {SX.ltn(_, Nat.add(m, n)) == True{} : Bool}
    hk))))

# the start's nonbasic rows (the y's, after peeling off the slacks) read off
# their entries; off slacks peeled so far, k the index after them
def iu0(~F: O.OField, qs: List<&2, SX.Ineq>, +m: Nat, +n: Nat, +off: Nat, k: Nat, +w: M.Vec(~F), +hoff: {Nat.add(off, SX.qlen(qs)) == m : Nat}, hb: {bat(SX.bcat(SX.trues(SX.qlen(qs), True{}), SX.trues(n, False{})), k) == False{} : Bool}, hk: {SX.ltn(Nat.add(off, k), Nat.add(m, n)) == True{} : Bool}) -> {rv(~F, SX.rowat(SX.rcat(SX.srows(qs, m), SX.yrows(n, Nat.add(m, n), m)), k), w) == fat(~F, w, Nat.add(off, k)) : O.C(F)}:
  match qs k:
    case Con{q, qt} 0n:
      absurd({rv(~F, SX.rowat(SX.rcat(SX.srows(Con{q, qt}, m), SX.yrows(n, Nat.add(m, n), m)), 0n), w) == fat(~F, w, Nat.add(off, 0n)) : O.C(F)}, KA.tf(hb))
    case Con{SX.Ineq{a, b, s}, +qt} 1n++j:
      %LN.add_succ(off, j) : {rv(~F, SX.rowat(SX.rcat(SX.srows(qt, m), SX.yrows(n, Nat.add(m, n), m)), j), w) == fat(~F, w, _) : O.C(F)}
      iu0(~F, qt, m, n, 1n+off, j, w,
        (%Equal.sym(Nat, 1n+Nat.add(off, SX.qlen(qt)), Nat.add(off, 1n+SX.qlen(qt)), LN.add_succ(off, SX.qlen(qt))) : {_ == m : Nat}
         hoff), hb,
        (%Equal.sym(Nat, 1n+Nat.add(off, j), Nat.add(off, 1n+j), LN.add_succ(off, j)) : {SX.ltn(_, Nat.add(m, n)) == True{} : Bool}
         hk))
    case Nil{} +k:
      %Equal.sym(Nat, off, m, off_eq(off, m, hoff)) : {rv(~F, SX.rowat(SX.yrows(n, Nat.add(m, n), m), k), w) == fat(~F, w, Nat.add(_, k)) : O.C(F)}
      iu0.base(~F, m, n, k, w, (%off_eq(off, m, hoff) : {SX.ltn(Nat.add(_, k), Nat.add(m, n)) == True{} : Bool}
        hk))

def iu_init.at(~F: O.OField, +qs: List<&2, SX.Ineq>, +n: Nat, +k: Nat, hk: {bat(SX.Tab.bas(SX.init(SX.LP{qs, n})), k) == False{} : Bool}, hkl: {SX.ltn(k, SX.LP.nv(SX.LP{qs, n})) == True{} : Bool}, +w: M.Vec(~F)) -> {rv(~F, SX.rowat(SX.Tab.rows(SX.init(SX.LP{qs, n})), k), w) == fat(~F, w, k) : O.C(F)}:
  iu0(~F, qs, SX.qlen(qs), n, 0n, k, w, {==}, hk, hkl)

# IU at the start
def iu_init(~F: O.OField, lp: SX.LP) -> IU(~F, SX.LP.nv(lp), SX.init(lp)):
  match lp:
    case SX.LP{+qs, +n}:
      k => hk => hkl => w => iu_init.at(~F, qs, n, k, hk, hkl, w)

def bat_trues_f(n: Nat, j: Nat, h: {bat(SX.trues(n, False{}), j) == True{} : Bool}) -> Empty:
  match n j:
    case 0n j:
      KA.ft(h)
    case 1n+k 0n:
      KA.ft(h)
    case 1n+k 1n+i:
      bat_trues_f(k, i, h)

# a basic variable of the start is a slack
def bat_lt(m: Nat, +n: Nat, j: Nat, h: {bat(SX.bcat(SX.trues(m, True{}), SX.trues(n, False{})), j) == True{} : Bool}) -> {SX.ltn(j, m) == True{} : Bool}:
  match m j:
    case 0n j:
      absurd({SX.ltn(j, 0n) == True{} : Bool}, bat_trues_f(n, j, h))
    case 1n+k 0n:
      {==}
    case 1n+k 1n+i:
      bat_lt(k, n, i, h)

def at_cat_zeros(m: Nat, +a: List<&2, S.Z>, j: Nat, h: {SX.ltn(j, m) == True{} : Bool}) -> {S.Z0{} == SX.at(SX.cat(EL.zeros(m), a), j) : S.Z}:
  match m j:
    case 0n j:
      absurd({S.Z0{} == SX.at(SX.cat(EL.zeros(0n), a), j) : S.Z}, KA.ft(ltn0(j, h)))
    case 1n+k 0n:
      {==}
    case 1n+k 1n+i:
      at_cat_zeros(k, a, i, h)

def zcol_srows(qs: List<&2, SX.Ineq>, +m: Nat, +j: Nat, +h: {SX.ltn(j, m) == True{} : Bool}) -> {zcol(SX.srows(qs, m), j) == True{} : Bool}:
  match qs:
    case Nil{}:
      {==}
    case Con{SX.Ineq{+a, b, s}, +qt}:
      KA.band_i(SX.iszero(SX.at(SX.cat(EL.zeros(m), a), j)), zcol(SX.srows(qt, m), j), iszero_of(SX.at(SX.cat(EL.zeros(m), a), j), at_cat_zeros(m, a, j, h)), zcol_srows(qt, m, j, h))

def ltn_ne(j: Nat, i: Nat, h: {SX.ltn(j, i) == True{} : Bool}) -> {SX.eqn(j, i) == False{} : Bool}:
  match j i:
    case 0n 0n:
      absurd({SX.eqn(0n, 0n) == False{} : Bool}, KA.ft(h))
    case 0n 1n+b:
      {==}
    case 1n+a 0n:
      {==}
    case 1n+a 1n+b:
      ltn_ne(a, b, h)

def ltn_succ_r(j: Nat, i: Nat, h: {SX.ltn(j, i) == True{} : Bool}) -> {SX.ltn(j, 1n+i) == True{} : Bool}:
  match j i:
    case 0n i:
      {==}
    case 1n+a 0n:
      absurd({SX.ltn(1n+a, 1n) == True{} : Bool}, KA.ft(h))
    case 1n+a 1n+b:
      ltn_succ_r(a, b, h)

def zcol_yrows(c: Nat, +N: Nat, +i: Nat, +j: Nat, +h: {SX.ltn(j, i) == True{} : Bool}) -> {zcol(SX.yrows(c, N, i), j) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n++k:
      KA.band_i(SX.iszero(SX.at(SX.unit(N, i), j)), zcol(SX.yrows(k, N, 1n+i), j), iszero_of(SX.at(SX.unit(N, i), j), at_unit_ne(N, i, j, ltn_ne(j, i, h))), zcol_yrows(k, N, 1n+i, j, ltn_succ_r(j, i, h)))

def zcol_rcat(u: List<&2, SX.Rw>, +v: List<&2, SX.Rw>, +j: Nat, +hu: {zcol(u, j) == True{} : Bool}, hv: {zcol(v, j) == True{} : Bool}) -> {zcol(SX.rcat(u, v), j) == True{} : Bool}:
  match u:
    case Nil{}:
      hv
    case Con{+r, +t}:
      KA.band_i(SX.iszero(SX.at(SX.Rw.m(r), j)), zcol(SX.rcat(t, v), j), KA.band_l(SX.iszero(SX.at(SX.Rw.m(r), j)), zcol(t, j), hu), zcol_rcat(t, v, j, KA.band_r(SX.iszero(SX.at(SX.Rw.m(r), j)), zcol(t, j), hu), hv))

def iz_init.at(+qs: List<&2, SX.Ineq>, +n: Nat, +j: Nat, hj: {bat(SX.Tab.bas(SX.init(SX.LP{qs, n})), j) == True{} : Bool}) -> {zcol(SX.Tab.rows(SX.init(SX.LP{qs, n})), j) == True{} : Bool}:
  +hl = bat_lt(SX.qlen(qs), n, j, hj)
  zcol_rcat(SX.srows(qs, SX.qlen(qs)), SX.yrows(n, Nat.add(SX.qlen(qs), n), SX.qlen(qs)), j, zcol_srows(qs, SX.qlen(qs), j, hl), zcol_yrows(n, Nat.add(SX.qlen(qs), n), SX.qlen(qs), j, hl))

# IZ at the start
def iz_init(lp: SX.LP) -> IZ(SX.init(lp)):
  match lp:
    case SX.LP{+qs, +n}:
      j => hj => iz_init.at(qs, n, j, hj)

# Sizes: N rows, N basis flags, rows of at most N entries
# -------------------------------------------------------

def nrows_rcat(u: List<&2, SX.Rw>, +v: List<&2, SX.Rw>) -> {Nat.add(nrows(u), nrows(v)) == nrows(SX.rcat(u, v)) : Nat}:
  match u:
    case Nil{}:
      {==}
    case Con{r, +t}:
      %nrows_rcat(t, v) : {1n+Nat.add(nrows(t), nrows(v)) == 1n+_ : Nat}
      {==}

def nrows_srows(qs: List<&2, SX.Ineq>, +m: Nat) -> {SX.qlen(qs) == nrows(SX.srows(qs, m)) : Nat}:
  match qs:
    case Nil{}:
      {==}
    case Con{SX.Ineq{a, b, s}, +t}:
      %nrows_srows(t, m) : {1n+SX.qlen(t) == 1n+_ : Nat}
      {==}

def nrows_yrows(c: Nat, +N: Nat, +i: Nat) -> {c == nrows(SX.yrows(c, N, i)) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n++k:
      %nrows_yrows(k, N, 1n+i) : {1n+k == 1n+_ : Nat}
      {==}

def nr_init(lp: SX.LP) -> {nrows(SX.Tab.rows(SX.init(lp))) == SX.LP.nv(lp) : Nat}:
  match lp:
    case SX.LP{+qs, +n}:
      %nrows_rcat(SX.srows(qs, SX.qlen(qs)), SX.yrows(n, Nat.add(SX.qlen(qs), n), SX.qlen(qs))) : {_ == Nat.add(SX.qlen(qs), n) : Nat}
      %nrows_srows(qs, SX.qlen(qs)) : {Nat.add(_, nrows(SX.yrows(n, Nat.add(SX.qlen(qs), n), SX.qlen(qs)))) == Nat.add(SX.qlen(qs), n) : Nat}
      %nrows_yrows(n, Nat.add(SX.qlen(qs), n), SX.qlen(qs)) : {Nat.add(SX.qlen(qs), _) == Nat.add(SX.qlen(qs), n) : Nat}
      {==}

def nrows_phis(+mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, +p: S.Z, +len: Nat, rs: List<&2, SX.Rw>, md: Maybe<&2, Nat>) -> {nrows(rs) == nrows(SX.phis(mi, di, e, i, p, len, rs, md)) : Nat}:
  match rs md:
    case Nil{} md:
      {==}
    case Con{r, +t} None{}:
      %nrows_phis(mi, di, e, i, p, len, t, None{}) : {1n+nrows(t) == 1n+_ : Nat}
      {==}
    case Con{r, +t} Some{0n}:
      %nrows_phis(mi, di, e, i, p, len, t, None{}) : {1n+nrows(t) == 1n+_ : Nat}
      {==}
    case Con{r, +t} Some{1n++d}:
      %nrows_phis(mi, di, e, i, p, len, t, Some{d}) : {1n+nrows(t) == 1n+_ : Nat}
      {==}

def nr_pivot.go(ri: SX.Rw, +e: Nat, +i: Nat, +len: Nat, +rows: List<&2, SX.Rw>, +bas: List<&2, Bool>) -> {nrows(rows) == nrows(SX.Tab.rows(SX.pivot.go(ri, e, i, len, rows, bas))) : Nat}:
  match ri:
    case SX.Rw{+di, +mi}:
      nrows_phis(mi, di, e, i, SX.at(mi, e), len, rows, Some{i})

def nr_pivot(+len: Nat, t: SX.Tab, +i: Nat, +e: Nat) -> {nrows(SX.Tab.rows(t)) == nrows(SX.Tab.rows(SX.pivot(len, t, i, e))) : Nat}:
  match t:
    case SX.Tab{+rows, +bas}:
      nr_pivot.go(SX.rowat(rows, i), e, i, len, rows, bas)

def blen_bcat(u: List<&2, Bool>, +v: List<&2, Bool>) -> {Nat.add(blen(u), blen(v)) == blen(SX.bcat(u, v)) : Nat}:
  match u:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %blen_bcat(t, v) : {1n+Nat.add(blen(t), blen(v)) == 1n+_ : Nat}
      {==}

def blen_trues(c: Nat, +b: Bool) -> {c == blen(SX.trues(c, b)) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n++k:
      %blen_trues(k, b) : {1n+k == 1n+_ : Nat}
      {==}

def bl_init(lp: SX.LP) -> {blen(SX.Tab.bas(SX.init(lp))) == SX.LP.nv(lp) : Nat}:
  match lp:
    case SX.LP{+qs, +n}:
      %blen_bcat(SX.trues(SX.qlen(qs), True{}), SX.trues(n, False{})) : {_ == Nat.add(SX.qlen(qs), n) : Nat}
      %blen_trues(SX.qlen(qs), True{}) : {Nat.add(_, blen(SX.trues(n, False{}))) == Nat.add(SX.qlen(qs), n) : Nat}
      %blen_trues(n, False{}) : {Nat.add(SX.qlen(qs), _) == Nat.add(SX.qlen(qs), n) : Nat}
      {==}

def bl_pivot(+len: Nat, +t: SX.Tab, +i: Nat, +e: Nat) -> {blen(SX.Tab.bas(t)) == blen(SX.Tab.bas(SX.pivot(len, t, i, e))) : Nat}:
  %bas_pivot(len, t, i, e) : {blen(SX.Tab.bas(t)) == blen(_) : Nat}
  %blen_setb(SX.setb(SX.Tab.bas(t), i, False{}), e, True{}) : {blen(SX.Tab.bas(t)) == _ : Nat}
  blen_setb(SX.Tab.bas(t), i, False{})

# every row has at most N entries
def rlok(rs: List<&2, SX.Rw>, +N: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, t}:
      KA.band(KA.natle(SX.vlen(SX.Rw.m(r)), N), rlok(t, N))

def rlok_at(rs: List<&2, SX.Rw>, +N: Nat, k: Nat, h: {rlok(rs, N) == True{} : Bool}) -> {KA.natle(SX.vlen(SX.Rw.m(SX.rowat(rs, k))), N) == True{} : Bool}:
  match rs k:
    case Nil{} k:
      {==}
    case Con{+r, +t} 0n:
      KA.band_l(KA.natle(SX.vlen(SX.Rw.m(r)), N), rlok(t, N), h)
    case Con{+r, +t} 1n+j:
      rlok_at(t, N, j, KA.band_r(KA.natle(SX.vlen(SX.Rw.m(r)), N), rlok(t, N), h))

def vlen_zeros(l: Nat) -> {l == SX.vlen(EL.zeros(l)) : Nat}:
  match l:
    case 0n:
      {==}
    case 1n++k:
      %vlen_zeros(k) : {1n+k == 1n+_ : Nat}
      {==}

def vlen_unit(len: Nat, i: Nat) -> {len == SX.vlen(SX.unit(len, i)) : Nat}:
  match len i:
    case 0n i:
      {==}
    case 1n++l 0n:
      %vlen_zeros(l) : {1n+l == 1n+_ : Nat}
      {==}
    case 1n++l 1n+h:
      %vlen_unit(l, h) : {1n+l == 1n+_ : Nat}
      {==}

def vlen_vscale(+k: S.Z, u: List<&2, S.Z>) -> {SX.vlen(u) == SX.vlen(EL.vscale(k, u)) : Nat}:
  match u:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %vlen_vscale(k, t) : {1n+SX.vlen(t) == 1n+_ : Nat}
      {==}

def vlen_cat(u: List<&2, S.Z>, +w: List<&2, S.Z>) -> {Nat.add(SX.vlen(u), SX.vlen(w)) == SX.vlen(SX.cat(u, w)) : Nat}:
  match u:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %vlen_cat(t, w) : {1n+Nat.add(SX.vlen(t), SX.vlen(w)) == 1n+_ : Nat}
      {==}

def vlen_vadd_le(u: List<&2, S.Z>, w: List<&2, S.Z>, N: Nat, hu: {KA.natle(SX.vlen(u), N) == True{} : Bool}, hw: {KA.natle(SX.vlen(w), N) == True{} : Bool}) -> {KA.natle(SX.vlen(EL.vadd(u, w)), N) == True{} : Bool}:
  match u w N:
    case Nil{} Nil{} N:
      {==}
    case Nil{} Con{y, s} N:
      hw
    case Con{x, t} Nil{} N:
      hu
    case Con{x, t} Con{y, s} 0n:
      absurd({KA.natle(SX.vlen(EL.vadd(Con{x, t}, Con{y, s})), 0n) == True{} : Bool}, KA.ft(hu))
    case Con{x, t} Con{y, s} 1n+k:
      vlen_vadd_le(t, s, k, hu, hw)

def vle_scale(+k: S.Z, +u: List<&2, S.Z>, +N: Nat, h: {KA.natle(SX.vlen(u), N) == True{} : Bool}) -> {KA.natle(SX.vlen(EL.vscale(k, u)), N) == True{} : Bool}:
  %vlen_vscale(k, u) : {KA.natle(_, N) == True{} : Bool}
  h

def vle_unit(+len: Nat, +i: Nat) -> {KA.natle(SX.vlen(SX.unit(len, i)), len) == True{} : Bool}:
  %vlen_unit(len, i) : {KA.natle(_, len) == True{} : Bool}
  KA.natle_refl(len)

def rowl3(+mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, +p: S.Z, +len: Nat, r: SX.Rw, hr: {KA.natle(SX.vlen(SX.Rw.m(r)), len) == True{} : Bool}, hmi: {KA.natle(SX.vlen(mi), len) == True{} : Bool}) -> {KA.natle(SX.vlen(SX.Rw.m(SX.phi.go(False{}, mi, di, i, p, len, SX.at(SX.Rw.m(r), e), r))), len) == True{} : Bool}:
  match r:
    case SX.Rw{d, +m}:
      vlen_vadd_le(EL.vadd(EL.vscale(S.Zpos{EL.babs(p)}, m), EL.vscale(S.Z.neg(EL.bsgn(p, SX.at(m, e))), mi)), EL.vscale(S.Z.mul(EL.bsgn(p, SX.at(m, e)), S.Zpos{di}), SX.unit(len, i)), len,
        vlen_vadd_le(EL.vscale(S.Zpos{EL.babs(p)}, m), EL.vscale(S.Z.neg(EL.bsgn(p, SX.at(m, e))), mi), len, vle_scale(S.Zpos{EL.babs(p)}, m, len, hr), vle_scale(S.Z.neg(EL.bsgn(p, SX.at(m, e))), mi, len, hmi)),
        vle_scale(S.Z.mul(EL.bsgn(p, SX.at(m, e)), S.Zpos{di}), SX.unit(len, i), len, vle_unit(len, i)))

def rowl(b: Bool, +mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, +p: S.Z, +len: Nat, +r: SX.Rw, hr: {KA.natle(SX.vlen(SX.Rw.m(r)), len) == True{} : Bool}, hmi: {KA.natle(SX.vlen(mi), len) == True{} : Bool}) -> {KA.natle(SX.vlen(SX.Rw.m(SX.phi.go(b, mi, di, i, p, len, SX.at(SX.Rw.m(r), e), r))), len) == True{} : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      rowl3(mi, di, e, i, p, len, r, hr, hmi)

def rlok_phis(+mi: List<&2, S.Z>, +di: S.Pos, +e: Nat, +i: Nat, +p: S.Z, +len: Nat, rs: List<&2, SX.Rw>, md: Maybe<&2, Nat>, h: {rlok(rs, len) == True{} : Bool}, +hmi: {KA.natle(SX.vlen(mi), len) == True{} : Bool}) -> {rlok(SX.phis(mi, di, e, i, p, len, rs, md), len) == True{} : Bool}:
  match rs md:
    case Nil{} md:
      {==}
    case Con{+r, +t} None{}:
      +h2 = h
      KA.band_i(KA.natle(SX.vlen(SX.Rw.m(SX.phi.go(SX.iszero(SX.at(SX.Rw.m(r), e)), mi, di, i, p, len, SX.at(SX.Rw.m(r), e), r))), len), rlok(SX.phis(mi, di, e, i, p, len, t, None{}), len),
        rowl(SX.iszero(SX.at(SX.Rw.m(r), e)), mi, di, e, i, p, len, r, KA.band_l(KA.natle(SX.vlen(SX.Rw.m(r)), len), rlok(t, len), h2), hmi),
        rlok_phis(mi, di, e, i, p, len, t, None{}, KA.band_r(KA.natle(SX.vlen(SX.Rw.m(r)), len), rlok(t, len), h2), hmi))
    case Con{+r, +t} Some{0n}:
      KA.band_i(KA.natle(SX.vlen(SX.unit(len, i)), len), rlok(SX.phis(mi, di, e, i, p, len, t, None{}), len), vle_unit(len, i),
        rlok_phis(mi, di, e, i, p, len, t, None{}, KA.band_r(KA.natle(SX.vlen(SX.Rw.m(r)), len), rlok(t, len), h), hmi))
    case Con{+r, +t} Some{1n++d}:
      +h2 = h
      KA.band_i(KA.natle(SX.vlen(SX.Rw.m(SX.phi.go(SX.iszero(SX.at(SX.Rw.m(r), e)), mi, di, i, p, len, SX.at(SX.Rw.m(r), e), r))), len), rlok(SX.phis(mi, di, e, i, p, len, t, Some{d}), len),
        rowl(SX.iszero(SX.at(SX.Rw.m(r), e)), mi, di, e, i, p, len, r, KA.band_l(KA.natle(SX.vlen(SX.Rw.m(r)), len), rlok(t, len), h2), hmi),
        rlok_phis(mi, di, e, i, p, len, t, Some{d}, KA.band_r(KA.natle(SX.vlen(SX.Rw.m(r)), len), rlok(t, len), h2), hmi))

def rl_pivot.go(ri: SX.Rw, +e: Nat, +i: Nat, +len: Nat, +rows: List<&2, SX.Rw>, +bas: List<&2, Bool>, hri: {SX.rowat(rows, i) == ri : SX.Rw}, +h: {rlok(rows, len) == True{} : Bool}) -> {rlok(SX.Tab.rows(SX.pivot.go(ri, e, i, len, rows, bas)), len) == True{} : Bool}:
  match ri:
    case SX.Rw{+di, +mi}:
      rlok_phis(mi, di, e, i, SX.at(mi, e), len, rows, Some{i}, h, (%hri : {KA.natle(SX.vlen(SX.Rw.m(_)), len) == True{} : Bool}
        rlok_at(rows, len, i, h)))

def rl_pivot(+len: Nat, t: SX.Tab, +i: Nat, +e: Nat, h: {rlok(SX.Tab.rows(t), len) == True{} : Bool}) -> {rlok(SX.Tab.rows(SX.pivot(len, t, i, e)), len) == True{} : Bool}:
  match t:
    case SX.Tab{+rows, +bas}:
      rl_pivot.go(SX.rowat(rows, i), e, i, len, rows, bas, {==}, h)

def rlok_rcat(u: List<&2, SX.Rw>, +v: List<&2, SX.Rw>, +N: Nat, +hu: {rlok(u, N) == True{} : Bool}, hv: {rlok(v, N) == True{} : Bool}) -> {rlok(SX.rcat(u, v), N) == True{} : Bool}:
  match u:
    case Nil{}:
      hv
    case Con{+r, +t}:
      KA.band_i(KA.natle(SX.vlen(SX.Rw.m(r)), N), rlok(SX.rcat(t, v), N), KA.band_l(KA.natle(SX.vlen(SX.Rw.m(r)), N), rlok(t, N), hu), rlok_rcat(t, v, N, KA.band_r(KA.natle(SX.vlen(SX.Rw.m(r)), N), rlok(t, N), hu), hv))

def rlok_srows(qs: List<&2, SX.Ineq>, +m: Nat, +n: Nat, h: {lpwf.go(qs, n) == True{} : Bool}) -> {rlok(SX.srows(qs, m), Nat.add(m, n)) == True{} : Bool}:
  match qs:
    case Nil{}:
      {==}
    case Con{SX.Ineq{+a, b, s}, +qt}:
      +h2 = h
      KA.band_i(KA.natle(SX.vlen(SX.cat(EL.zeros(m), a)), Nat.add(m, n)), rlok(SX.srows(qt, m), Nat.add(m, n)),
        (%vlen_cat(EL.zeros(m), a) : {KA.natle(_, Nat.add(m, n)) == True{} : Bool}
         %vlen_zeros(m) : {KA.natle(Nat.add(_, SX.vlen(a)), Nat.add(m, n)) == True{} : Bool}
         KA.natle_add_mono(m, SX.vlen(a), n, KA.band_l(KA.natle(SX.vlen(a), n), lpwf.go(qt, n), h2))),
        rlok_srows(qt, m, n, KA.band_r(KA.natle(SX.vlen(a), n), lpwf.go(qt, n), h2)))

def rlok_yrows(c: Nat, +N: Nat, +i: Nat) -> {rlok(SX.yrows(c, N, i), N) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n++k:
      KA.band_i(KA.natle(SX.vlen(SX.unit(N, i)), N), rlok(SX.yrows(k, N, 1n+i), N), vle_unit(N, i), rlok_yrows(k, N, 1n+i))

def rl_init(lp: SX.LP, h: {lpwf(lp) == True{} : Bool}) -> {rlok(SX.Tab.rows(SX.init(lp)), SX.LP.nv(lp)) == True{} : Bool}:
  match lp:
    case SX.LP{+qs, +n}:
      rlok_rcat(SX.srows(qs, SX.qlen(qs)), SX.yrows(n, Nat.add(SX.qlen(qs), n), SX.qlen(qs)), Nat.add(SX.qlen(qs), n), rlok_srows(qs, SX.qlen(qs), n, h), rlok_yrows(n, Nat.add(SX.qlen(qs), n), SX.qlen(qs)))
