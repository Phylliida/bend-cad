# Telescoping slopes in every ordered field: for an expression e and two
# assignments X1, X2, sl(i, X1, X2, e) is e's slope in variable i, built by
#   slope(a b) = a(X1) slope(b) + b(X2) slope(a),
# so that e(X1) - e(X2) is the sum over i of sl(i) (X1_i - X2_i)
# (slope_ok). Untrusted: proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/box.bend as BX
import ./certdef.bend as C
import ./karith.bend as KA
import ./nat.bend as LN
import ./fring.bend as FR
import ./fmat.bend as FM
import ./ford.bend as FO
import ./fvec.bend as FV

# 1 if b, else 0
def find(~F: O.OField, b: Bool) -> O.C(F):
  match b:
    case True{}:
      O.one(F)
    case False{}:
      O.zero(F)

# e's slope in variable i between X1 and X2
def sl(~F: O.OField, +i: Nat, +x1: M.Vec(~F), +x2: M.Vec(~F), e: E.QExpr) -> O.C(F):
  match e:
    case E.QVar{j}:
      find(~F, KA.nateq(i, j))
    case E.QCst{q}:
      O.zero(F)
    case E.QAdd{a, b}:
      O.add(F, sl(~F, i, x1, x2, a), sl(~F, i, x1, x2, b))
    case E.QSub{a, b}:
      O.sub(~F, sl(~F, i, x1, x2, a), sl(~F, i, x1, x2, b))
    case E.QMul{+a, +b}:
      O.add(F, O.mul(F, O.eval(~F, x1, a), sl(~F, i, x1, x2, b)), O.mul(F, O.eval(~F, x2, b), sl(~F, i, x1, x2, a)))
    case E.QNeg{a}:
      O.neg(F, sl(~F, i, x1, x2, a))

# the slopes in the cnt variables lo, lo + 1, ...
def srange(~F: O.OField, +x1: M.Vec(~F), +x2: M.Vec(~F), +e: E.QExpr, cnt: Nat, +lo: Nat) -> M.Vec(~F):
  match cnt:
    case 0n:
      Nil{}
    case 1n+k:
      Con{sl(~F, lo, x1, x2, e), srange(~F, x1, x2, e, k, 1n+lo)}

# every variable of e is below m
def below(+m: Nat, e: E.QExpr) -> Bool:
  match e:
    case E.QVar{j}:
      KA.natle(1n+j, m)
    case E.QCst{q}:
      True{}
    case E.QAdd{a, b}:
      KA.band(below(m, a), below(m, b))
    case E.QSub{a, b}:
      KA.band(below(m, a), below(m, b))
    case E.QMul{a, b}:
      KA.band(below(m, a), below(m, b))
    case E.QNeg{a}:
      below(m, a)

# Natural-number facts
# --------------------

def nateq_refl(a: Nat) -> {KA.nateq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      nateq_refl(p)

# t + 1 + j is not j
def nateq_gt(+t: Nat, j: Nat) -> {KA.nateq(Nat.add(1n+t, j), j) == False{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      %LN.add_succ(t, p) : {KA.nateq(_, p) == False{} : Bool}
      nateq_gt(t, p)

# lo is not k + 1 + lo
def nateq_lt(+k: Nat, lo: Nat) -> {KA.nateq(lo, Nat.add(1n+k, lo)) == False{} : Bool}:
  match lo:
    case 0n:
      {==}
    case 1n+p:
      %LN.add_succ(k, p) : {KA.nateq(p, _) == False{} : Bool}
      nateq_lt(k, p)

# Rows of slopes
# --------------

# a constant's slopes are 0
def czero_dot(~F: O.OField, +x1: M.Vec(~F), +x2: M.Vec(~F), +q: S.Q, c: Nat, +lo: Nat, d: M.Vec(~F)) -> {O.zero(F) == M.dot(~F, srange(~F, x1, x2, E.QCst{q}, c, lo), d) : O.C(F)}:
  match c d:
    case 0n d:
      {==}
    case 1n+k Nil{}:
      {==}
    case 1n+k Con{+d0, ds}:
      %czero_dot(~F, x1, x2, q, k, 1n+lo, ds) : {O.zero(F) == O.add(F, O.mul(F, O.zero(F), d0), _) : O.C(F)}
      FR.fring_eq(~F, [d0], E.ZCst{S.Z0{}}, E.ZAdd{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZCst{S.Z0{}}}, {==})

# variable j's slopes in variables past j are 0
def zrow(~F: O.OField, c: Nat, d: M.Vec(~F), +x1: M.Vec(~F), +x2: M.Vec(~F), +j: Nat, +t: Nat) -> {O.zero(F) == M.dot(~F, srange(~F, x1, x2, E.QVar{j}, c, Nat.add(1n+t, j)), d) : O.C(F)}:
  match c d:
    case 0n d:
      {==}
    case 1n+k Nil{}:
      {==}
    case 1n+k Con{+d0, ds}:
      %Equal.sym(Bool, KA.nateq(Nat.add(1n+t, j), j), False{}, nateq_gt(t, j)) : {O.zero(F) == O.add(F, O.mul(F, find(~F, _), d0), M.dot(~F, srange(~F, x1, x2, E.QVar{j}, k, 1n+Nat.add(1n+t, j)), ds)) : O.C(F)}
      %zrow(~F, k, ds, x1, x2, j, 1n+t) : {O.zero(F) == O.add(F, O.mul(F, O.zero(F), d0), _) : O.C(F)}
      FR.fring_eq(~F, [d0], E.ZCst{S.Z0{}}, E.ZAdd{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZCst{S.Z0{}}}, {==})

def unit_dot.zero(~F: O.OField, +x1: M.Vec(~F), +x2: M.Vec(~F), +c: Nat, +lo: Nat, d: M.Vec(~F)) -> {O.lookup(~F, d, 0n) == M.dot(~F, Con{O.one(F), srange(~F, x1, x2, E.QVar{lo}, c, 1n+lo)}, d) : O.C(F)}:
  match d:
    case Nil{}:
      {==}
    case Con{+d0, ds}:
      %zrow(~F, c, ds, x1, x2, lo, 0n) : {d0 == O.add(F, O.mul(F, O.one(F), d0), _) : O.C(F)}
      FR.fring_eq(~F, [d0], E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, E.ZCst{S.Z0{}}}, {==})

# variable k + lo's slopes, dotted with the slice d of variables from lo,
# pick out d_k (for k < cnt)
def unit_dot(~F: O.OField, +x1: M.Vec(~F), +x2: M.Vec(~F), k: Nat, cnt: Nat, +lo: Nat, d: M.Vec(~F), h: {KA.natle(1n+k, cnt) == True{} : Bool}) -> {O.lookup(~F, d, k) == M.dot(~F, srange(~F, x1, x2, E.QVar{Nat.add(k, lo)}, cnt, lo), d) : O.C(F)}:
  match k cnt d:
    case k 0n d:
      FO.absurd({O.lookup(~F, d, k) == O.zero(F) : O.C(F)}, KA.ft(h))
    case 0n 1n+c d:
      %Equal.sym(Bool, KA.nateq(lo, lo), True{}, nateq_refl(lo)) : {O.lookup(~F, d, 0n) == M.dot(~F, Con{find(~F, _), srange(~F, x1, x2, E.QVar{lo}, c, 1n+lo)}, d) : O.C(F)}
      unit_dot.zero(~F, x1, x2, c, lo, d)
    case 1n+kk 1n+c Nil{}:
      {==}
    case 1n++kk 1n+c Con{+d0, +ds}:
      %Equal.sym(Bool, KA.nateq(lo, Nat.add(1n+kk, lo)), False{}, nateq_lt(kk, lo)) : {O.lookup(~F, ds, kk) == O.add(F, O.mul(F, find(~F, _), d0), M.dot(~F, srange(~F, x1, x2, E.QVar{Nat.add(1n+kk, lo)}, c, 1n+lo), ds)) : O.C(F)}
      %Equal.sym(Nat, 1n+Nat.add(kk, lo), Nat.add(kk, 1n+lo), LN.add_succ(kk, lo)) : {O.lookup(~F, ds, kk) == O.add(F, O.mul(F, O.zero(F), d0), M.dot(~F, srange(~F, x1, x2, E.QVar{_}, c, 1n+lo), ds)) : O.C(F)}
      %unit_dot(~F, x1, x2, kk, c, 1n+lo, ds, h) : {O.lookup(~F, ds, kk) == O.add(F, O.mul(F, O.zero(F), d0), _) : O.C(F)}
      FR.fring_eq(~F, [O.lookup(~F, ds, kk), d0], E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{1n}}, E.ZVar{0n}}, {==})

# Entries of differences
# ----------------------

def lookup_vneg(~F: O.OField, w: M.Vec(~F), i: Nat) -> {O.neg(F, O.lookup(~F, w, i)) == O.lookup(~F, M.vneg(~F, w), i) : O.C(F)}:
  match w i:
    case Nil{} i:
      FR.fring_eq(~F, Nil{}, E.ZNeg{E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})
    case Con{b, ws} 0n:
      {==}
    case Con{b, ws} 1n+j:
      lookup_vneg(~F, ws, j)

def lookup_vsub(~F: O.OField, u: M.Vec(~F), +w: M.Vec(~F), +i: Nat) -> {O.sub(~F, O.lookup(~F, u, i), O.lookup(~F, w, i)) == O.lookup(~F, BX.vsub(~F, u, w), i) : O.C(F)}:
  match u w i:
    case Nil{} w i:
      %lookup_vneg(~F, w, i) : {O.sub(~F, O.zero(F), O.lookup(~F, w, i)) == _ : O.C(F)}
      FR.fring_eq(~F, [O.lookup(~F, w, i)], E.ZSub{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZNeg{E.ZVar{0n}}, {==})
    case Con{+a, +us} Nil{} i:
      FR.fring_eq(~F, [O.lookup(~F, Con{a, us}, i)], E.ZSub{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZVar{0n}, {==})
    case Con{a, us} Con{b, ws} 0n:
      {==}
    case Con{a, us} Con{b, ws} 1n+j:
      lookup_vsub(~F, us, ws, j)

# Slope rows of compound expressions
# ----------------------------------

def srange_add(~F: O.OField, +x1: M.Vec(~F), +x2: M.Vec(~F), +a: E.QExpr, +b: E.QExpr, cnt: Nat, +lo: Nat) -> {M.vadd(~F, srange(~F, x1, x2, a, cnt, lo), srange(~F, x1, x2, b, cnt, lo)) == srange(~F, x1, x2, E.QAdd{a, b}, cnt, lo) : M.Vec(~F)}:
  match cnt:
    case 0n:
      {==}
    case 1n+k:
      %srange_add(~F, x1, x2, a, b, k, 1n+lo) : {Con{O.add(F, sl(~F, lo, x1, x2, a), sl(~F, lo, x1, x2, b)), M.vadd(~F, srange(~F, x1, x2, a, k, 1n+lo), srange(~F, x1, x2, b, k, 1n+lo))} == Con{O.add(F, sl(~F, lo, x1, x2, a), sl(~F, lo, x1, x2, b)), _} : M.Vec(~F)}
      {==}

def srange_sub(~F: O.OField, +x1: M.Vec(~F), +x2: M.Vec(~F), +a: E.QExpr, +b: E.QExpr, cnt: Nat, +lo: Nat) -> {M.vadd(~F, srange(~F, x1, x2, a, cnt, lo), M.vneg(~F, srange(~F, x1, x2, b, cnt, lo))) == srange(~F, x1, x2, E.QSub{a, b}, cnt, lo) : M.Vec(~F)}:
  match cnt:
    case 0n:
      {==}
    case 1n+k:
      %srange_sub(~F, x1, x2, a, b, k, 1n+lo) : {Con{O.sub(~F, sl(~F, lo, x1, x2, a), sl(~F, lo, x1, x2, b)), M.vadd(~F, srange(~F, x1, x2, a, k, 1n+lo), M.vneg(~F, srange(~F, x1, x2, b, k, 1n+lo)))} == Con{O.sub(~F, sl(~F, lo, x1, x2, a), sl(~F, lo, x1, x2, b)), _} : M.Vec(~F)}
      {==}

def srange_neg(~F: O.OField, +x1: M.Vec(~F), +x2: M.Vec(~F), +a: E.QExpr, cnt: Nat, +lo: Nat) -> {M.vneg(~F, srange(~F, x1, x2, a, cnt, lo)) == srange(~F, x1, x2, E.QNeg{a}, cnt, lo) : M.Vec(~F)}:
  match cnt:
    case 0n:
      {==}
    case 1n+k:
      %srange_neg(~F, x1, x2, a, k, 1n+lo) : {Con{O.neg(F, sl(~F, lo, x1, x2, a)), M.vneg(~F, srange(~F, x1, x2, a, k, 1n+lo))} == Con{O.neg(F, sl(~F, lo, x1, x2, a)), _} : M.Vec(~F)}
      {==}

def srange_mul(~F: O.OField, +x1: M.Vec(~F), +x2: M.Vec(~F), +a: E.QExpr, +b: E.QExpr, cnt: Nat, +lo: Nat) -> {M.vadd(~F, M.vscale(~F, O.eval(~F, x1, a), srange(~F, x1, x2, b, cnt, lo)), M.vscale(~F, O.eval(~F, x2, b), srange(~F, x1, x2, a, cnt, lo))) == srange(~F, x1, x2, E.QMul{a, b}, cnt, lo) : M.Vec(~F)}:
  match cnt:
    case 0n:
      {==}
    case 1n+k:
      %srange_mul(~F, x1, x2, a, b, k, 1n+lo) : {Con{sl(~F, lo, x1, x2, E.QMul{a, b}), M.vadd(~F, M.vscale(~F, O.eval(~F, x1, a), srange(~F, x1, x2, b, k, 1n+lo)), M.vscale(~F, O.eval(~F, x2, b), srange(~F, x1, x2, a, k, 1n+lo)))} == Con{sl(~F, lo, x1, x2, E.QMul{a, b}), _} : M.Vec(~F)}
      {==}

# The slope identity
# ------------------

def slope_ok.var(~F: O.OField, +x1: M.Vec(~F), +x2: M.Vec(~F), +j: Nat, m: Nat, h: {KA.natle(1n+j, m) == True{} : Bool}) -> {O.lookup(~F, BX.vsub(~F, x1, x2), j) == M.dot(~F, srange(~F, x1, x2, E.QVar{j}, m, 0n), BX.vsub(~F, x1, x2)) : O.C(F)}:
  %Equal.sym(Nat, j, Nat.add(j, 0n), LN.add_zero(j)) : {O.lookup(~F, BX.vsub(~F, x1, x2), j) == M.dot(~F, srange(~F, x1, x2, E.QVar{_}, m, 0n), BX.vsub(~F, x1, x2)) : O.C(F)}
  unit_dot(~F, x1, x2, j, m, 0n, BX.vsub(~F, x1, x2), h)

# e(X1) - e(X2) = sum over i < m of sl_i (X1_i - X2_i), for e's variables < m
def slope_ok(~F: O.OField, +x1: M.Vec(~F), +x2: M.Vec(~F), e: E.QExpr, +m: Nat, +hb: {below(m, e) == True{} : Bool}) -> {O.sub(~F, O.eval(~F, x1, e), O.eval(~F, x2, e)) == M.dot(~F, srange(~F, x1, x2, e, m, 0n), BX.vsub(~F, x1, x2)) : O.C(F)}:
  match e:
    case E.QVar{+j}:
      Equal.trans(O.C(F), O.sub(~F, O.lookup(~F, x1, j), O.lookup(~F, x2, j)), O.lookup(~F, BX.vsub(~F, x1, x2), j), M.dot(~F, srange(~F, x1, x2, E.QVar{j}, m, 0n), BX.vsub(~F, x1, x2)), lookup_vsub(~F, x1, x2, j), slope_ok.var(~F, x1, x2, j, m, hb))
    case E.QCst{+q}:
      Equal.trans(O.C(F), O.sub(~F, O.ofq(~F, q), O.ofq(~F, q)), O.zero(F), M.dot(~F, srange(~F, x1, x2, E.QCst{q}, m, 0n), BX.vsub(~F, x1, x2)), O.add_neg(F)(O.ofq(~F, q)), czero_dot(~F, x1, x2, q, m, 0n, BX.vsub(~F, x1, x2)))
    case E.QAdd{+a, +b}:
      %srange_add(~F, x1, x2, a, b, m, 0n) : {O.sub(~F, O.eval(~F, x1, E.QAdd{a, b}), O.eval(~F, x2, E.QAdd{a, b})) == M.dot(~F, _, BX.vsub(~F, x1, x2)) : O.C(F)}
      %FM.dot_vadd(~F, srange(~F, x1, x2, a, m, 0n), srange(~F, x1, x2, b, m, 0n), BX.vsub(~F, x1, x2)) : {O.sub(~F, O.eval(~F, x1, E.QAdd{a, b}), O.eval(~F, x2, E.QAdd{a, b})) == _ : O.C(F)}
      %slope_ok(~F, x1, x2, a, m, KA.band_l(below(m, a), below(m, b), hb)) : {O.sub(~F, O.eval(~F, x1, E.QAdd{a, b}), O.eval(~F, x2, E.QAdd{a, b})) == O.add(F, _, M.dot(~F, srange(~F, x1, x2, b, m, 0n), BX.vsub(~F, x1, x2))) : O.C(F)}
      %slope_ok(~F, x1, x2, b, m, KA.band_r(below(m, a), below(m, b), hb)) : {O.sub(~F, O.eval(~F, x1, E.QAdd{a, b}), O.eval(~F, x2, E.QAdd{a, b})) == O.add(F, O.sub(~F, O.eval(~F, x1, a), O.eval(~F, x2, a)), _) : O.C(F)}
      FR.fring_eq(~F, [O.eval(~F, x1, a), O.eval(~F, x1, b), O.eval(~F, x2, a), O.eval(~F, x2, b)], E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZAdd{E.ZVar{2n}, E.ZVar{3n}}}, E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, E.ZSub{E.ZVar{1n}, E.ZVar{3n}}}, {==})
    case E.QSub{+a, +b}:
      %srange_sub(~F, x1, x2, a, b, m, 0n) : {O.sub(~F, O.eval(~F, x1, E.QSub{a, b}), O.eval(~F, x2, E.QSub{a, b})) == M.dot(~F, _, BX.vsub(~F, x1, x2)) : O.C(F)}
      %FM.dot_vadd(~F, srange(~F, x1, x2, a, m, 0n), M.vneg(~F, srange(~F, x1, x2, b, m, 0n)), BX.vsub(~F, x1, x2)) : {O.sub(~F, O.eval(~F, x1, E.QSub{a, b}), O.eval(~F, x2, E.QSub{a, b})) == _ : O.C(F)}
      %FM.dot_vneg(~F, srange(~F, x1, x2, b, m, 0n), BX.vsub(~F, x1, x2)) : {O.sub(~F, O.eval(~F, x1, E.QSub{a, b}), O.eval(~F, x2, E.QSub{a, b})) == O.add(F, M.dot(~F, srange(~F, x1, x2, a, m, 0n), BX.vsub(~F, x1, x2)), _) : O.C(F)}
      %slope_ok(~F, x1, x2, a, m, KA.band_l(below(m, a), below(m, b), hb)) : {O.sub(~F, O.eval(~F, x1, E.QSub{a, b}), O.eval(~F, x2, E.QSub{a, b})) == O.add(F, _, O.neg(F, M.dot(~F, srange(~F, x1, x2, b, m, 0n), BX.vsub(~F, x1, x2)))) : O.C(F)}
      %slope_ok(~F, x1, x2, b, m, KA.band_r(below(m, a), below(m, b), hb)) : {O.sub(~F, O.eval(~F, x1, E.QSub{a, b}), O.eval(~F, x2, E.QSub{a, b})) == O.add(F, O.sub(~F, O.eval(~F, x1, a), O.eval(~F, x2, a)), O.neg(F, _)) : O.C(F)}
      FR.fring_eq(~F, [O.eval(~F, x1, a), O.eval(~F, x1, b), O.eval(~F, x2, a), O.eval(~F, x2, b)], E.ZSub{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZVar{2n}, E.ZVar{3n}}}, E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, E.ZNeg{E.ZSub{E.ZVar{1n}, E.ZVar{3n}}}}, {==})
    case E.QMul{+a, +b}:
      %srange_mul(~F, x1, x2, a, b, m, 0n) : {O.sub(~F, O.eval(~F, x1, E.QMul{a, b}), O.eval(~F, x2, E.QMul{a, b})) == M.dot(~F, _, BX.vsub(~F, x1, x2)) : O.C(F)}
      %FM.dot_vadd(~F, M.vscale(~F, O.eval(~F, x1, a), srange(~F, x1, x2, b, m, 0n)), M.vscale(~F, O.eval(~F, x2, b), srange(~F, x1, x2, a, m, 0n)), BX.vsub(~F, x1, x2)) : {O.sub(~F, O.eval(~F, x1, E.QMul{a, b}), O.eval(~F, x2, E.QMul{a, b})) == _ : O.C(F)}
      %FM.dot_vscale(~F, O.eval(~F, x1, a), srange(~F, x1, x2, b, m, 0n), BX.vsub(~F, x1, x2)) : {O.sub(~F, O.eval(~F, x1, E.QMul{a, b}), O.eval(~F, x2, E.QMul{a, b})) == O.add(F, _, M.dot(~F, M.vscale(~F, O.eval(~F, x2, b), srange(~F, x1, x2, a, m, 0n)), BX.vsub(~F, x1, x2))) : O.C(F)}
      %FM.dot_vscale(~F, O.eval(~F, x2, b), srange(~F, x1, x2, a, m, 0n), BX.vsub(~F, x1, x2)) : {O.sub(~F, O.eval(~F, x1, E.QMul{a, b}), O.eval(~F, x2, E.QMul{a, b})) == O.add(F, O.mul(F, O.eval(~F, x1, a), M.dot(~F, srange(~F, x1, x2, b, m, 0n), BX.vsub(~F, x1, x2))), _) : O.C(F)}
      %slope_ok(~F, x1, x2, b, m, KA.band_r(below(m, a), below(m, b), hb)) : {O.sub(~F, O.eval(~F, x1, E.QMul{a, b}), O.eval(~F, x2, E.QMul{a, b})) == O.add(F, O.mul(F, O.eval(~F, x1, a), _), O.mul(F, O.eval(~F, x2, b), M.dot(~F, srange(~F, x1, x2, a, m, 0n), BX.vsub(~F, x1, x2)))) : O.C(F)}
      %slope_ok(~F, x1, x2, a, m, KA.band_l(below(m, a), below(m, b), hb)) : {O.sub(~F, O.eval(~F, x1, E.QMul{a, b}), O.eval(~F, x2, E.QMul{a, b})) == O.add(F, O.mul(F, O.eval(~F, x1, a), O.sub(~F, O.eval(~F, x1, b), O.eval(~F, x2, b))), O.mul(F, O.eval(~F, x2, b), _)) : O.C(F)}
      FR.fring_eq(~F, [O.eval(~F, x1, a), O.eval(~F, x1, b), O.eval(~F, x2, a), O.eval(~F, x2, b)], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{2n}, E.ZVar{3n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZSub{E.ZVar{1n}, E.ZVar{3n}}}, E.ZMul{E.ZVar{3n}, E.ZSub{E.ZVar{0n}, E.ZVar{2n}}}}, {==})
    case E.QNeg{+a}:
      %srange_neg(~F, x1, x2, a, m, 0n) : {O.sub(~F, O.eval(~F, x1, E.QNeg{a}), O.eval(~F, x2, E.QNeg{a})) == M.dot(~F, _, BX.vsub(~F, x1, x2)) : O.C(F)}
      %FM.dot_vneg(~F, srange(~F, x1, x2, a, m, 0n), BX.vsub(~F, x1, x2)) : {O.sub(~F, O.eval(~F, x1, E.QNeg{a}), O.eval(~F, x2, E.QNeg{a})) == _ : O.C(F)}
      %slope_ok(~F, x1, x2, a, m, hb) : {O.sub(~F, O.eval(~F, x1, E.QNeg{a}), O.eval(~F, x2, E.QNeg{a})) == O.neg(F, _) : O.C(F)}
      FR.fring_eq(~F, [O.eval(~F, x1, a), O.eval(~F, x2, a)], E.ZSub{E.ZNeg{E.ZVar{0n}}, E.ZNeg{E.ZVar{1n}}}, E.ZNeg{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}}, {==})
