# bend-cad: rational expressions decided in every ordered field (DESIGN
# §8.11: the certificates of dropped equations and conflicts). Untrusted
# code, proven. A rational expression's denominators are cleared: clr(e) is
# an integer expression and den(e) a positive with
#   eval(e) · den(e) = zeval(clr(e))
# in every ordered field (clr_ok). A sum is cleared by a shared
# denominator of its two sides (sd), which takes their common factors of 2
# once: the inputs are dyadic, and a product of denominators would double
# the twos at every sum. The integer normalizer R.norm, proven
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
import ./nat.bend as N
import ./pos.bend as P

# Shared denominators
# -------------------

# a shared denominator of x and y: d = x fa = y fb
type SD is Data:
  SD{d: S.Pos, fa: S.Pos, fb: S.Pos}

def SD.d(r: SD) -> S.Pos:
  match r:
    case SD{d, fa, fb}:
      d

def SD.fa(r: SD) -> S.Pos:
  match r:
    case SD{d, fa, fb}:
      fa

def SD.fb(r: SD) -> S.Pos:
  match r:
    case SD{d, fa, fb}:
      fb

# twice r's denominator, by the same factors
def sd.o(+r: SD) -> SD:
  SD{S.XO{SD.d(r)}, SD.fa(r), SD.fb(r)}

# the product
def sd.p(+x: S.Pos, +y: S.Pos) -> SD:
  SD{S.Pos.mul(x, y), y, x}

# x = 2^k x' and y = 2^k y', x' or y' odd, share 2^k x' y'
def sd(x: S.Pos, y: S.Pos) -> SD:
  match x y:
    case S.XH{} y:
      sd.p(S.XH{}, y)
    case S.XO{a} S.XH{}:
      sd.p(S.XO{a}, S.XH{})
    case S.XO{a} S.XO{b}:
      sd.o(sd(a, b))
    case S.XO{a} S.XI{b}:
      sd.p(S.XO{a}, S.XI{b})
    case S.XI{a} y:
      sd.p(S.XI{a}, y)

def pcomm(+x: S.Pos, +y: S.Pos) -> {S.Pos.mul(x, y) == S.Pos.mul(y, x) : S.Pos}:
  P.nat_inj(S.Pos.mul(x, y), S.Pos.mul(y, x),
    Equal.trans(Nat, S.Pos.nat(S.Pos.mul(x, y)), Nat.mul(S.Pos.nat(y), S.Pos.nat(x)), S.Pos.nat(S.Pos.mul(y, x)),
      Equal.trans(Nat, S.Pos.nat(S.Pos.mul(x, y)), Nat.mul(S.Pos.nat(x), S.Pos.nat(y)), Nat.mul(S.Pos.nat(y), S.Pos.nat(x)),
        Equal.sym(Nat, Nat.mul(S.Pos.nat(x), S.Pos.nat(y)), S.Pos.nat(S.Pos.mul(x, y)), P.mul_nat(x, y)),
        N.mul_comm(S.Pos.nat(x), S.Pos.nat(y))),
      P.mul_nat(y, x)))

def sd_a(x: S.Pos, y: S.Pos) -> {S.Pos.mul(x, SD.fa(sd(x, y))) == SD.d(sd(x, y)) : S.Pos}:
  match x y:
    case S.XH{} +y:
      {==}
    case S.XO{+a} S.XH{}:
      {==}
    case S.XO{+a} S.XO{+b}:
      Equal.cong(S.Pos, S.Pos, p => S.XO{p}, S.Pos.mul(a, SD.fa(sd(a, b))), SD.d(sd(a, b)), sd_a(a, b))
    case S.XO{+a} S.XI{+b}:
      {==}
    case S.XI{+a} +y:
      {==}

def sd_b(x: S.Pos, y: S.Pos) -> {S.Pos.mul(y, SD.fb(sd(x, y))) == SD.d(sd(x, y)) : S.Pos}:
  match x y:
    case S.XH{} +y:
      pcomm(y, S.XH{})
    case S.XO{+a} S.XH{}:
      pcomm(S.XH{}, S.XO{a})
    case S.XO{+a} S.XO{+b}:
      Equal.cong(S.Pos, S.Pos, p => S.XO{p}, S.Pos.mul(b, SD.fb(sd(a, b))), SD.d(sd(a, b)), sd_b(a, b))
    case S.XO{+a} S.XI{+b}:
      pcomm(S.XI{b}, S.XO{a})
    case S.XI{+a} +y:
      pcomm(y, S.XI{a})

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
      SD.d(sd(den(a), den(b)))
    case E.QSub{a, b}:
      SD.d(sd(den(a), den(b)))
    case E.QMul{a, b}:
      S.Pos.mul(den(a), den(b))
    case E.QNeg{a}:
      den(a)

# x fa + y fb and x fa - y fb, r's factors computed once
def clr.add(+x: E.ZExpr, +y: E.ZExpr, +r: SD) -> E.ZExpr:
  E.ZAdd{E.ZMul{x, E.ZCst{S.Zpos{SD.fa(r)}}}, E.ZMul{y, E.ZCst{S.Zpos{SD.fb(r)}}}}

def clr.sub(+x: E.ZExpr, +y: E.ZExpr, +r: SD) -> E.ZExpr:
  E.ZSub{E.ZMul{x, E.ZCst{S.Zpos{SD.fa(r)}}}, E.ZMul{y, E.ZCst{S.Zpos{SD.fb(r)}}}}

# e times den(e), as an integer expression
def clr(e: E.QExpr) -> E.ZExpr:
  match e:
    case E.QVar{i}:
      E.ZVar{i}
    case E.QCst{S.Q{n, d}}:
      E.ZCst{n}
    case E.QAdd{+a, +b}:
      clr.add(clr(a), clr(b), sd(den(a), den(b)))
    case E.QSub{+a, +b}:
      clr.sub(clr(a), clr(b), sd(den(a), den(b)))
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

# x d = (x p) f when p f = d
def fac_ok(~F: O.OField, +x: O.C(F), +p: S.Pos, +f: S.Pos, +d: S.Pos, h: {S.Pos.mul(p, f) == d : S.Pos}) -> {O.mul(F, O.mul(F, x, O.ofp(~F, p)), O.ofp(~F, f)) == O.mul(F, x, O.ofp(~F, d)) : O.C(F)}:
  %h : {O.mul(F, O.mul(F, x, O.ofp(~F, p)), O.ofp(~F, f)) == O.mul(F, x, O.ofp(~F, _)) : O.C(F)}
  %FR.ofz_mul(~F, S.Zpos{p}, S.Zpos{f}) : {O.mul(F, O.mul(F, x, O.ofp(~F, p)), O.ofp(~F, f)) == O.mul(F, x, _) : O.C(F)}
  FR.fring_eq(~F, [x, O.ofp(~F, p), O.ofp(~F, f)], E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, {==})


# eval(e) · den(e) = zeval(clr(e)), in every ordered field
def clr_ok(~F: O.OField, +env: List<&2, O.C(F)>, e: E.QExpr) -> {O.mul(F, O.eval(~F, env, e), O.ofp(~F, den(e))) == FR.zeval(~F, env, clr(e)) : O.C(F)}:
  match e:
    case E.QVar{+i}:
      O.mul_one(F)(O.lookup(~F, env, i))
    case E.QCst{S.Q{+n, +d}}:
      cst_ok(~F, n, d)
    case E.QAdd{+a, +b}:
      %FR.fring_eq(~F, [O.eval(~F, env, a), O.eval(~F, env, b), O.ofp(~F, SD.d(sd(den(a), den(b))))], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZMul{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, {==}) : {_ == O.add(F, O.mul(F, FR.zeval(~F, env, clr(a)), O.ofp(~F, SD.fa(sd(den(a), den(b))))), O.mul(F, FR.zeval(~F, env, clr(b)), O.ofp(~F, SD.fb(sd(den(a), den(b)))))) : O.C(F)}
      %fac_ok(~F, O.eval(~F, env, a), den(a), SD.fa(sd(den(a), den(b))), SD.d(sd(den(a), den(b))), sd_a(den(a), den(b))) : {O.add(F, _, O.mul(F, O.eval(~F, env, b), O.ofp(~F, SD.d(sd(den(a), den(b)))))) == O.add(F, O.mul(F, FR.zeval(~F, env, clr(a)), O.ofp(~F, SD.fa(sd(den(a), den(b))))), O.mul(F, FR.zeval(~F, env, clr(b)), O.ofp(~F, SD.fb(sd(den(a), den(b)))))) : O.C(F)}
      %fac_ok(~F, O.eval(~F, env, b), den(b), SD.fb(sd(den(a), den(b))), SD.d(sd(den(a), den(b))), sd_b(den(a), den(b))) : {O.add(F, O.mul(F, O.mul(F, O.eval(~F, env, a), O.ofp(~F, den(a))), O.ofp(~F, SD.fa(sd(den(a), den(b))))), _) == O.add(F, O.mul(F, FR.zeval(~F, env, clr(a)), O.ofp(~F, SD.fa(sd(den(a), den(b))))), O.mul(F, FR.zeval(~F, env, clr(b)), O.ofp(~F, SD.fb(sd(den(a), den(b)))))) : O.C(F)}
      %clr_ok(~F, env, a) : {O.add(F, O.mul(F, O.mul(F, O.eval(~F, env, a), O.ofp(~F, den(a))), O.ofp(~F, SD.fa(sd(den(a), den(b))))), O.mul(F, O.mul(F, O.eval(~F, env, b), O.ofp(~F, den(b))), O.ofp(~F, SD.fb(sd(den(a), den(b)))))) == O.add(F, O.mul(F, _, O.ofp(~F, SD.fa(sd(den(a), den(b))))), O.mul(F, FR.zeval(~F, env, clr(b)), O.ofp(~F, SD.fb(sd(den(a), den(b)))))) : O.C(F)}
      %clr_ok(~F, env, b) : {O.add(F, O.mul(F, O.mul(F, O.eval(~F, env, a), O.ofp(~F, den(a))), O.ofp(~F, SD.fa(sd(den(a), den(b))))), O.mul(F, O.mul(F, O.eval(~F, env, b), O.ofp(~F, den(b))), O.ofp(~F, SD.fb(sd(den(a), den(b)))))) == O.add(F, O.mul(F, O.mul(F, O.eval(~F, env, a), O.ofp(~F, den(a))), O.ofp(~F, SD.fa(sd(den(a), den(b))))), O.mul(F, _, O.ofp(~F, SD.fb(sd(den(a), den(b)))))) : O.C(F)}
      {==}
    case E.QSub{+a, +b}:
      %FR.fring_eq(~F, [O.eval(~F, env, a), O.eval(~F, env, b), O.ofp(~F, SD.d(sd(den(a), den(b))))], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZMul{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, {==}) : {_ == O.sub(~F, O.mul(F, FR.zeval(~F, env, clr(a)), O.ofp(~F, SD.fa(sd(den(a), den(b))))), O.mul(F, FR.zeval(~F, env, clr(b)), O.ofp(~F, SD.fb(sd(den(a), den(b)))))) : O.C(F)}
      %fac_ok(~F, O.eval(~F, env, a), den(a), SD.fa(sd(den(a), den(b))), SD.d(sd(den(a), den(b))), sd_a(den(a), den(b))) : {O.sub(~F, _, O.mul(F, O.eval(~F, env, b), O.ofp(~F, SD.d(sd(den(a), den(b)))))) == O.sub(~F, O.mul(F, FR.zeval(~F, env, clr(a)), O.ofp(~F, SD.fa(sd(den(a), den(b))))), O.mul(F, FR.zeval(~F, env, clr(b)), O.ofp(~F, SD.fb(sd(den(a), den(b)))))) : O.C(F)}
      %fac_ok(~F, O.eval(~F, env, b), den(b), SD.fb(sd(den(a), den(b))), SD.d(sd(den(a), den(b))), sd_b(den(a), den(b))) : {O.sub(~F, O.mul(F, O.mul(F, O.eval(~F, env, a), O.ofp(~F, den(a))), O.ofp(~F, SD.fa(sd(den(a), den(b))))), _) == O.sub(~F, O.mul(F, FR.zeval(~F, env, clr(a)), O.ofp(~F, SD.fa(sd(den(a), den(b))))), O.mul(F, FR.zeval(~F, env, clr(b)), O.ofp(~F, SD.fb(sd(den(a), den(b)))))) : O.C(F)}
      %clr_ok(~F, env, a) : {O.sub(~F, O.mul(F, O.mul(F, O.eval(~F, env, a), O.ofp(~F, den(a))), O.ofp(~F, SD.fa(sd(den(a), den(b))))), O.mul(F, O.mul(F, O.eval(~F, env, b), O.ofp(~F, den(b))), O.ofp(~F, SD.fb(sd(den(a), den(b)))))) == O.sub(~F, O.mul(F, _, O.ofp(~F, SD.fa(sd(den(a), den(b))))), O.mul(F, FR.zeval(~F, env, clr(b)), O.ofp(~F, SD.fb(sd(den(a), den(b)))))) : O.C(F)}
      %clr_ok(~F, env, b) : {O.sub(~F, O.mul(F, O.mul(F, O.eval(~F, env, a), O.ofp(~F, den(a))), O.ofp(~F, SD.fa(sd(den(a), den(b))))), O.mul(F, O.mul(F, O.eval(~F, env, b), O.ofp(~F, den(b))), O.ofp(~F, SD.fb(sd(den(a), den(b)))))) == O.sub(~F, O.mul(F, O.mul(F, O.eval(~F, env, a), O.ofp(~F, den(a))), O.ofp(~F, SD.fa(sd(den(a), den(b))))), O.mul(F, _, O.ofp(~F, SD.fb(sd(den(a), den(b)))))) : O.C(F)}
      {==}
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
