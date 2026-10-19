# bend-cad: rational expressions decided in every ordered field (DESIGN
# §8.11: the certificates of dropped equations and conflicts). Untrusted
# code, proven. A rational expression's denominators are cleared: clr(e) is
# an integer expression and den(e) a positive with
#   eval(e) · den(e) = zeval(clr(e))
# in every ordered field (clr_ok). The integer normalizer R.norm, proven
# sound in every ordered field (lib/fring.bend: norm_ok), then decides
# whether e is identically 0: qzero_ok.
#
# Generated from tools/drafts/qnorm.draft by tools/expand.py; edit the draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./qemb.bend as QE
import ./zring.bend as R
import ./karith.bend as KA

# Clearing denominators
# ---------------------

# a common denominator of e's constants
def den(e: E.QExpr) -> S.Pos:
  match e:
    case E.QVar{i}:
      S.XH{}
    case E.QCst{S.Q{n, d}}:
      d
    case E.QAdd{a, b}:
      S.Pos.mul(den(a), den(b))
    case E.QSub{a, b}:
      S.Pos.mul(den(a), den(b))
    case E.QMul{a, b}:
      S.Pos.mul(den(a), den(b))
    case E.QNeg{a}:
      den(a)

# e times den(e), as an integer expression
def clr(e: E.QExpr) -> E.ZExpr:
  match e:
    case E.QVar{i}:
      E.ZVar{i}
    case E.QCst{S.Q{n, d}}:
      E.ZCst{n}
    case E.QAdd{+a, +b}:
      E.ZAdd{E.ZMul{clr(a), E.ZCst{S.Zpos{den(b)}}}, E.ZMul{clr(b), E.ZCst{S.Zpos{den(a)}}}}
    case E.QSub{+a, +b}:
      E.ZSub{E.ZMul{clr(a), E.ZCst{S.Zpos{den(b)}}}, E.ZMul{clr(b), E.ZCst{S.Zpos{den(a)}}}}
    case E.QMul{a, b}:
      E.ZMul{clr(a), clr(b)}
    case E.QNeg{a}:
      E.ZNeg{clr(a)}

# n/d times d is n
def cst_ok(~F: O.OField, +n: S.Z, +d: S.Pos) -> {O.mul(F, O.mul(F, O.ofz(~F, n), O.inv(F, O.ofp(~F, d))), O.ofp(~F, d)) == O.ofz(~F, n) : O.C(F)}:
  %FL.mul_assoc(~F, O.ofz(~F, n), O.inv(F, O.ofp(~F, d)), O.ofp(~F, d)) : {_ == O.ofz(~F, n) : O.C(F)}
  %FL.mul_comm(~F, O.ofp(~F, d), O.inv(F, O.ofp(~F, d))) : {O.mul(F, O.ofz(~F, n), _) == O.ofz(~F, n) : O.C(F)}
  %Equal.sym(O.C(F), O.mul(F, O.ofp(~F, d), O.inv(F, O.ofp(~F, d))), O.one(F), O.mul_inv(F)(O.ofp(~F, d), QE.ofp_ne(~F, d))) : {O.mul(F, O.ofz(~F, n), _) == O.ofz(~F, n) : O.C(F)}
  O.mul_one(F)(O.ofz(~F, n))

# eval(e) · den(e) = zeval(clr(e)), in every ordered field
def clr_ok(~F: O.OField, +env: List<&2, O.C(F)>, e: E.QExpr) -> {O.mul(F, O.eval(~F, env, e), O.ofp(~F, den(e))) == FR.zeval(~F, env, clr(e)) : O.C(F)}:
  match e:
    case E.QVar{+i}:
      O.mul_one(F)(O.lookup(~F, env, i))
    case E.QCst{S.Q{+n, +d}}:
      cst_ok(~F, n, d)
    case E.QAdd{+a, +b}:
      %FR.ofz_mul(~F, S.Zpos{den(a)}, S.Zpos{den(b)}) : {O.mul(F, O.add(F, O.eval(~F, env, a), O.eval(~F, env, b)), _) == O.add(F, O.mul(F, FR.zeval(~F, env, clr(a)), O.ofp(~F, den(b))), O.mul(F, FR.zeval(~F, env, clr(b)), O.ofp(~F, den(a)))) : O.C(F)}
      %clr_ok(~F, env, a) : {O.mul(F, O.add(F, O.eval(~F, env, a), O.eval(~F, env, b)), O.mul(F, O.ofp(~F, den(a)), O.ofp(~F, den(b)))) == O.add(F, O.mul(F, _, O.ofp(~F, den(b))), O.mul(F, FR.zeval(~F, env, clr(b)), O.ofp(~F, den(a)))) : O.C(F)}
      %clr_ok(~F, env, b) : {O.mul(F, O.add(F, O.eval(~F, env, a), O.eval(~F, env, b)), O.mul(F, O.ofp(~F, den(a)), O.ofp(~F, den(b)))) == O.add(F, O.mul(F, O.mul(F, O.eval(~F, env, a), O.ofp(~F, den(a))), O.ofp(~F, den(b))), O.mul(F, _, O.ofp(~F, den(a)))) : O.C(F)}
      FR.fring_eq(~F, [O.eval(~F, env, a), O.eval(~F, env, b), O.ofp(~F, den(a)), O.ofp(~F, den(b))], E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{2n}, E.ZVar{3n}}}, E.ZAdd{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{3n}}, E.ZMul{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZVar{2n}}}, {==})
    case E.QSub{+a, +b}:
      %FR.ofz_mul(~F, S.Zpos{den(a)}, S.Zpos{den(b)}) : {O.mul(F, O.sub(~F, O.eval(~F, env, a), O.eval(~F, env, b)), _) == O.sub(~F, O.mul(F, FR.zeval(~F, env, clr(a)), O.ofp(~F, den(b))), O.mul(F, FR.zeval(~F, env, clr(b)), O.ofp(~F, den(a)))) : O.C(F)}
      %clr_ok(~F, env, a) : {O.mul(F, O.sub(~F, O.eval(~F, env, a), O.eval(~F, env, b)), O.mul(F, O.ofp(~F, den(a)), O.ofp(~F, den(b)))) == O.sub(~F, O.mul(F, _, O.ofp(~F, den(b))), O.mul(F, FR.zeval(~F, env, clr(b)), O.ofp(~F, den(a)))) : O.C(F)}
      %clr_ok(~F, env, b) : {O.mul(F, O.sub(~F, O.eval(~F, env, a), O.eval(~F, env, b)), O.mul(F, O.ofp(~F, den(a)), O.ofp(~F, den(b)))) == O.sub(~F, O.mul(F, O.mul(F, O.eval(~F, env, a), O.ofp(~F, den(a))), O.ofp(~F, den(b))), O.mul(F, _, O.ofp(~F, den(a)))) : O.C(F)}
      FR.fring_eq(~F, [O.eval(~F, env, a), O.eval(~F, env, b), O.ofp(~F, den(a)), O.ofp(~F, den(b))], E.ZMul{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{2n}, E.ZVar{3n}}}, E.ZSub{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{3n}}, E.ZMul{E.ZMul{E.ZVar{1n}, E.ZVar{3n}}, E.ZVar{2n}}}, {==})
    case E.QMul{+a, +b}:
      %FR.ofz_mul(~F, S.Zpos{den(a)}, S.Zpos{den(b)}) : {O.mul(F, O.mul(F, O.eval(~F, env, a), O.eval(~F, env, b)), _) == O.mul(F, FR.zeval(~F, env, clr(a)), FR.zeval(~F, env, clr(b))) : O.C(F)}
      %clr_ok(~F, env, a) : {O.mul(F, O.mul(F, O.eval(~F, env, a), O.eval(~F, env, b)), O.mul(F, O.ofp(~F, den(a)), O.ofp(~F, den(b)))) == O.mul(F, _, FR.zeval(~F, env, clr(b))) : O.C(F)}
      %clr_ok(~F, env, b) : {O.mul(F, O.mul(F, O.eval(~F, env, a), O.eval(~F, env, b)), O.mul(F, O.ofp(~F, den(a)), O.ofp(~F, den(b)))) == O.mul(F, O.mul(F, O.eval(~F, env, a), O.ofp(~F, den(a))), _) : O.C(F)}
      FR.fring_eq(~F, [O.eval(~F, env, a), O.eval(~F, env, b), O.ofp(~F, den(a)), O.ofp(~F, den(b))], E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{2n}, E.ZVar{3n}}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}, {==})
    case E.QNeg{+a}:
      %clr_ok(~F, env, a) : {O.mul(F, O.neg(F, O.eval(~F, env, a)), O.ofp(~F, den(a))) == O.neg(F, _) : O.C(F)}
      FR.fring_eq(~F, [O.eval(~F, env, a), O.ofp(~F, den(a))], E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZVar{1n}}, E.ZNeg{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, {==})

# Deciding zero
# -------------

def isnil(p: List<&2, R.ZTerm>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{t, r}:
      False{}

# e is identically 0: its cleared form normalizes to the zero polynomial
def qzero(e: E.QExpr) -> Bool:
  isnil(R.norm(clr(e)))

def nil_of(p: List<&2, R.ZTerm>, h: {isnil(p) == True{} : Bool}) -> {Nil{} == p : List<&2, R.ZTerm>}:
  match p:
    case Nil{}:
      {==}
    case Con{t, r}:
      FO.absurd({Nil{} == Con{t, r} : List<&2, R.ZTerm>}, KA.ft(h))

def qz_mul(~F: O.OField, +env: List<&2, O.C(F)>, +e: E.QExpr, +h: {qzero(e) == True{} : Bool}) -> {O.mul(F, O.ofp(~F, den(e)), O.eval(~F, env, e)) == O.zero(F) : O.C(F)}:
  %FL.mul_comm(~F, O.eval(~F, env, e), O.ofp(~F, den(e))) : {_ == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), O.mul(F, O.eval(~F, env, e), O.ofp(~F, den(e))), FR.zeval(~F, env, clr(e)), clr_ok(~F, env, e)) : {_ == O.zero(F) : O.C(F)}
  %FR.norm_ok(~F, env, clr(e)) : {_ == O.zero(F) : O.C(F)}
  %nil_of(R.norm(clr(e)), h) : {FR.fepoly(~F, env, _) == O.zero(F) : O.C(F)}
  {==}

# The use: a rational expression that qzero passes is 0 in every ordered
# field, under every assignment of its variables
def qzero_ok(~F: O.OField, +env: List<&2, O.C(F)>, +e: E.QExpr, +h: {qzero(e) == True{} : Bool}) -> {O.eval(~F, env, e) == O.zero(F) : O.C(F)}:
  FO.mul_eq_zero(~F, O.ofp(~F, den(e)), O.eval(~F, env, e), QE.ofp_ne(~F, den(e)), qz_mul(~F, env, e, h))
