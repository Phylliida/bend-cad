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
