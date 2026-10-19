# bend-cad: identities decided by normal forms (PLAN-sk13a S1). The spec's
# Ident (equal at every rational point) holds exactly when the cleared
# difference normalizes to the zero polynomial:
#   ident_ok:     QN.qzero(e1 - e2) ⇒ Ident(e1, e2)
#   qzero_ident:  Ident(e1, e2) ⇒ QN.qzero(e1 - e2)   (the non-root lemma)
#   ident_all:    Ident(e1, e2) ⇒ e1 = e2 in every ordered field
# and the same against the constant 0 (ident0_ok, qzero0_ident). So
# dependence is decided exactly: dep(e, v) is not QN.qzero(deriv(e, v)),
# and dep_ok / nodep_ok give the spec's Depends and its negation.
#
# Soundness is lib/qnorm.bend's qzero_ok in the canonical rationals
# (lib/qfield.bend), read back through ofq. Completeness: if the normal
# form p is not zero, then e is not 0 at the point nonroot gives
# (wit_ne): there e times its denominator is ofz(p at that point), not 0.
# Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/deriv.bend as DV
import ../spec/solve.bend as SV
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./qemb.bend as QE
import ./qfield.bend as QF
import ./qnorm.bend as QN
import ./zring.bend as R
import ./karith.bend as KA
import ./redpoly.bend as RP
import ./nonroot.bend as NRT

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Rational points in a field
# --------------------------

def qmap(~F: O.OField, x: List<&2, S.Q>) -> List<&2, O.C(F)>:
  match x:
    case Nil{}:
      Nil{}
    case Con{q, t}:
      Con{O.ofq(~F, q), qmap(~F, t)}

def lk_qmap(~F: O.OField, x: List<&2, S.Q>, i: Nat) -> {O.lookup(~F, qmap(~F, x), i) == O.ofq(~F, E.qlookup(x, i)) : O.C(F)}:
  match x i:
    case Nil{} 0n:
      Equal.sym(O.C(F), O.ofq(~F, S.Q{S.Z0{}, S.XH{}}), O.zero(F), QE.ofq_zero(~F))
    case Nil{} 1n+j:
      Equal.sym(O.C(F), O.ofq(~F, S.Q{S.Z0{}, S.XH{}}), O.zero(F), QE.ofq_zero(~F))
    case Con{q, t} 0n:
      {==}
    case Con{q, t} 1n+j:
      lk_qmap(~F, t, j)

# an expression at rational points is its rational value
def qbr(~F: O.OField, +x: List<&2, S.Q>, e: E.QExpr) -> {O.eval(~F, qmap(~F, x), e) == O.ofq(~F, E.qeval(x, e)) : O.C(F)}:
  match e:
    case E.QVar{i}:
      lk_qmap(~F, x, i)
    case E.QCst{c}:
      {==}
    case E.QAdd{+a, +b}:
      %Equal.sym(O.C(F), O.ofq(~F, S.Q.add(E.qeval(x, a), E.qeval(x, b))), O.add(F, O.ofq(~F, E.qeval(x, a)), O.ofq(~F, E.qeval(x, b))), QE.ofq_add(~F, E.qeval(x, a), E.qeval(x, b))) : {O.add(F, O.eval(~F, qmap(~F, x), a), O.eval(~F, qmap(~F, x), b)) == _ : O.C(F)}
      %qbr(~F, x, a) : {O.add(F, O.eval(~F, qmap(~F, x), a), O.eval(~F, qmap(~F, x), b)) == O.add(F, _, O.ofq(~F, E.qeval(x, b))) : O.C(F)}
      %qbr(~F, x, b) : {O.add(F, O.eval(~F, qmap(~F, x), a), O.eval(~F, qmap(~F, x), b)) == O.add(F, O.eval(~F, qmap(~F, x), a), _) : O.C(F)}
      {==}
    case E.QSub{+a, +b}:
      %Equal.sym(O.C(F), O.ofq(~F, S.Q.add(E.qeval(x, a), S.Q.neg(E.qeval(x, b)))), O.add(F, O.ofq(~F, E.qeval(x, a)), O.ofq(~F, S.Q.neg(E.qeval(x, b)))), QE.ofq_add(~F, E.qeval(x, a), S.Q.neg(E.qeval(x, b)))) : {O.sub(~F, O.eval(~F, qmap(~F, x), a), O.eval(~F, qmap(~F, x), b)) == _ : O.C(F)}
      %Equal.sym(O.C(F), O.ofq(~F, S.Q.neg(E.qeval(x, b))), O.neg(F, O.ofq(~F, E.qeval(x, b))), QE.ofq_neg(~F, E.qeval(x, b))) : {O.sub(~F, O.eval(~F, qmap(~F, x), a), O.eval(~F, qmap(~F, x), b)) == O.add(F, O.ofq(~F, E.qeval(x, a)), _) : O.C(F)}
      %qbr(~F, x, a) : {O.sub(~F, O.eval(~F, qmap(~F, x), a), O.eval(~F, qmap(~F, x), b)) == O.add(F, _, O.neg(F, O.ofq(~F, E.qeval(x, b)))) : O.C(F)}
      %qbr(~F, x, b) : {O.sub(~F, O.eval(~F, qmap(~F, x), a), O.eval(~F, qmap(~F, x), b)) == O.add(F, O.eval(~F, qmap(~F, x), a), O.neg(F, _)) : O.C(F)}
      {==}
    case E.QMul{+a, +b}:
      %Equal.sym(O.C(F), O.ofq(~F, S.Q.mul(E.qeval(x, a), E.qeval(x, b))), O.mul(F, O.ofq(~F, E.qeval(x, a)), O.ofq(~F, E.qeval(x, b))), QE.ofq_mul(~F, E.qeval(x, a), E.qeval(x, b))) : {O.mul(F, O.eval(~F, qmap(~F, x), a), O.eval(~F, qmap(~F, x), b)) == _ : O.C(F)}
      %qbr(~F, x, a) : {O.mul(F, O.eval(~F, qmap(~F, x), a), O.eval(~F, qmap(~F, x), b)) == O.mul(F, _, O.ofq(~F, E.qeval(x, b))) : O.C(F)}
      %qbr(~F, x, b) : {O.mul(F, O.eval(~F, qmap(~F, x), a), O.eval(~F, qmap(~F, x), b)) == O.mul(F, O.eval(~F, qmap(~F, x), a), _) : O.C(F)}
      {==}
    case E.QNeg{+a}:
      %Equal.sym(O.C(F), O.ofq(~F, S.Q.neg(E.qeval(x, a))), O.neg(F, O.ofq(~F, E.qeval(x, a))), QE.ofq_neg(~F, E.qeval(x, a))) : {O.neg(F, O.eval(~F, qmap(~F, x), a)) == _ : O.C(F)}
      %qbr(~F, x, a) : {O.neg(F, O.eval(~F, qmap(~F, x), a)) == O.neg(F, _) : O.C(F)}
      {==}

# Integer points
# --------------

def qz(z: List<&2, S.Z>) -> List<&2, S.Q>:
  match z:
    case Nil{}:
      Nil{}
    case Con{n, t}:
      Con{S.Q{n, S.XH{}}, qz(t)}

def inv_one(~F: O.OField) -> {O.inv(F, O.one(F)) == O.one(F) : O.C(F)}:
  %Equal.sym(O.C(F), O.inv(F, O.one(F)), O.mul(F, O.one(F), O.inv(F, O.one(F))), FL.one_mul(~F, O.inv(F, O.one(F)))) : {_ == O.one(F) : O.C(F)}
  O.mul_inv(F)(O.one(F))(QE.ofp_ne(~F, S.XH{}))

def ofq_int(~F: O.OField, +n: S.Z) -> {O.ofz(~F, n) == O.ofq(~F, S.Q{n, S.XH{}}) : O.C(F)}:
  %Equal.sym(O.C(F), O.inv(F, O.one(F)), O.one(F), inv_one(~F)) : {O.ofz(~F, n) == O.mul(F, O.ofz(~F, n), _) : O.C(F)}
  FL.mul_one(~F, O.ofz(~F, n))

def lk_qz(~F: O.OField, z: List<&2, S.Z>, i: Nat) -> {O.ofz(~F, E.lookup(z, i)) == O.lookup(~F, qmap(~F, qz(z)), i) : O.C(F)}:
  match z i:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{n, t} 0n:
      ofq_int(~F, n)
    case Con{n, t} 1n+j:
      lk_qz(~F, t, j)

def fem_qz(~F: O.OField, +z: List<&2, S.Z>, m: List<&2, Nat>) -> {O.ofz(~F, R.emono(z, m)) == FR.femono(~F, qmap(~F, qz(z)), m) : O.C(F)}:
  match m:
    case Nil{}:
      {==}
    case Con{+v, +vs}:
      %lk_qz(~F, z, v) : {O.ofz(~F, R.emono(z, Con{v, vs})) == O.mul(F, _, FR.femono(~F, qmap(~F, qz(z)), vs)) : O.C(F)}
      %fem_qz(~F, z, vs) : {O.ofz(~F, R.emono(z, Con{v, vs})) == O.mul(F, O.ofz(~F, E.lookup(z, v)), _) : O.C(F)}
      Equal.sym(O.C(F), O.mul(F, O.ofz(~F, E.lookup(z, v)), O.ofz(~F, R.emono(z, vs))), O.ofz(~F, S.Z.mul(E.lookup(z, v), R.emono(z, vs))), FR.ofz_mul(~F, E.lookup(z, v), R.emono(z, vs)))

def fep_qz(~F: O.OField, +z: List<&2, S.Z>, p: List<&2, R.ZTerm>) -> {O.ofz(~F, R.epoly(z, p)) == FR.fepoly(~F, qmap(~F, qz(z)), p) : O.C(F)}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{+c, +m}, +rest}:
      %fem_qz(~F, z, m) : {O.ofz(~F, R.epoly(z, Con{R.ZTerm{c, m}, rest})) == O.add(F, O.mul(F, O.ofz(~F, c), _), FR.fepoly(~F, qmap(~F, qz(z)), rest)) : O.C(F)}
      %fep_qz(~F, z, rest) : {O.ofz(~F, R.epoly(z, Con{R.ZTerm{c, m}, rest})) == O.add(F, O.mul(F, O.ofz(~F, c), O.ofz(~F, R.emono(z, m))), _) : O.C(F)}
      %Equal.sym(O.C(F), O.mul(F, O.ofz(~F, c), O.ofz(~F, R.emono(z, m))), O.ofz(~F, S.Z.mul(c, R.emono(z, m))), FR.ofz_mul(~F, c, R.emono(z, m)))
        : {O.ofz(~F, R.epoly(z, Con{R.ZTerm{c, m}, rest})) == O.add(F, _, O.ofz(~F, R.epoly(z, rest))) : O.C(F)}
      Equal.sym(O.C(F), O.add(F, O.ofz(~F, S.Z.mul(c, R.emono(z, m))), O.ofz(~F, R.epoly(z, rest))), O.ofz(~F, S.Z.add(S.Z.mul(c, R.emono(z, m)), R.epoly(z, rest))),
        FR.ofz_add(~F, S.Z.mul(c, R.emono(z, m)), R.epoly(z, rest)))

def ofz_nz(~F: O.OField, c: S.Z, h: {RP.nz(c) == True{} : Bool}, e: {O.ofz(~F, c) == O.zero(F) : O.C(F)}) -> Empty:
  match c:
    case S.Z0{}:
      KA.ft(h)
    case S.Zpos{p}:
      QE.ofp_ne(~F, p)(e)
    case S.Zneg{+p}:
      QE.ofp_ne(~F, p)(
        (%FL.neg_neg(~F, O.ofp(~F, p)) : {_ == O.zero(F) : O.C(F)}
         %Equal.sym(O.C(F), O.neg(F, O.ofp(~F, p)), O.zero(F), e) : {O.neg(F, _) == O.zero(F) : O.C(F)}
         Equal.sym(O.C(F), O.zero(F), O.neg(F, O.zero(F)), FL.neg_zero(~F))))

# Completeness: a rational expression whose normal form is not zero is not 0
# at its witness point
# ---------------------------------------------------------------------------

def wpt(e: E.QExpr) -> List<&2, S.Q>:
  qz(NRT.witness(R.norm(QN.clr(e))))

# a type that is empty exactly at a nonempty list
def NilT(p: List<&2, R.ZTerm>) -> Type:
  match p:
    case Nil{}:
      Unit
    case Con{t, r}:
      Empty

def nonnil(p: List<&2, R.ZTerm>, h: {QN.isnil(p) == False{} : Bool}) -> {Nil{} == p : List<&2, R.ZTerm>} -> Empty:
  match p:
    case Nil{}:
      en => KA.tf(h)
    case Con{t, r}:
      en => (%en : NilT(_)
        Unit{})

# e's cleared form, read at the witness of its normal form, is ofz of the
# normal form's value there
def wit_zero(~F: O.OField, +e: E.QExpr, ez: {O.eval(~F, qmap(~F, wpt(e)), e) == O.zero(F) : O.C(F)})
  -> {O.ofz(~F, R.epoly(NRT.witness(R.norm(QN.clr(e))), R.norm(QN.clr(e)))) == O.zero(F) : O.C(F)}:
  %Equal.sym(O.C(F), O.ofz(~F, R.epoly(NRT.witness(R.norm(QN.clr(e))), R.norm(QN.clr(e)))), FR.fepoly(~F, qmap(~F, wpt(e)), R.norm(QN.clr(e))),
      fep_qz(~F, NRT.witness(R.norm(QN.clr(e))), R.norm(QN.clr(e)))) : {_ == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), FR.fepoly(~F, qmap(~F, wpt(e)), R.norm(QN.clr(e))), FR.zeval(~F, qmap(~F, wpt(e)), QN.clr(e)), FR.norm_ok(~F, qmap(~F, wpt(e)), QN.clr(e)))
    : {_ == O.zero(F) : O.C(F)}
  %QN.clr_ok(~F, qmap(~F, wpt(e)), e) : {_ == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), O.eval(~F, qmap(~F, wpt(e)), e), O.zero(F), ez) : {O.mul(F, _, O.ofp(~F, QN.den(e))) == O.zero(F) : O.C(F)}
  FL.zero_mul(~F, O.ofp(~F, QN.den(e)))

# a rational expression that qzero rejects is not 0 at its witness point
def wit_ne(~F: O.OField, +e: E.QExpr, h: {QN.qzero(e) == False{} : Bool}, ez: {O.eval(~F, qmap(~F, wpt(e)), e) == O.zero(F) : O.C(F)}) -> Empty:
  ofz_nz(~F, R.epoly(NRT.witness(R.norm(QN.clr(e))), R.norm(QN.clr(e))),
    NRT.nonroot(R.norm(QN.clr(e)), RP.norm_red(QN.clr(e)), nonnil(R.norm(QN.clr(e)), h)),
    wit_zero(~F, e, ez))

# Ident, decided
# --------------

def eq_q(~F: O.OField, +x: List<&2, S.Q>, +e1: E.QExpr, +e2: E.QExpr, h: {O.eval(~F, qmap(~F, x), e1) == O.eval(~F, qmap(~F, x), e2) : O.C(F)})
  -> {O.ofq(~F, E.qeval(x, e1)) == O.ofq(~F, E.qeval(x, e2)) : O.C(F)}:
  %qbr(~F, x, e1) : {_ == O.ofq(~F, E.qeval(x, e2)) : O.C(F)}
  %qbr(~F, x, e2) : {O.eval(~F, qmap(~F, x), e1) == _ : O.C(F)}
  h

def q_eq(~F: O.OField, +x: List<&2, S.Q>, +e1: E.QExpr, +e2: E.QExpr, h: {O.ofq(~F, E.qeval(x, e1)) == O.ofq(~F, E.qeval(x, e2)) : O.C(F)})
  -> {O.eval(~F, qmap(~F, x), e1) == O.eval(~F, qmap(~F, x), e2) : O.C(F)}:
  %Equal.sym(O.C(F), O.eval(~F, qmap(~F, x), e1), O.ofq(~F, E.qeval(x, e1)), qbr(~F, x, e1)) : {_ == O.eval(~F, qmap(~F, x), e2) : O.C(F)}
  %Equal.sym(O.C(F), O.eval(~F, qmap(~F, x), e2), O.ofq(~F, E.qeval(x, e2)), qbr(~F, x, e2)) : {O.ofq(~F, E.qeval(x, e1)) == _ : O.C(F)}
  h

def ident_at(~F: O.OField, +e1: E.QExpr, +e2: E.QExpr, +h: {QN.qzero(E.QSub{e1, e2}) == True{} : Bool}, +x: List<&2, S.Q>) -> S.Q.eq(E.qeval(x, e1), E.qeval(x, e2)):
  QE.ofq_eq_rev(~F, E.qeval(x, e1), E.qeval(x, e2),
    eq_q(~F, x, e1, e2, FO.eq_of_sub(~F, O.eval(~F, qmap(~F, x), e1), O.eval(~F, qmap(~F, x), e2), QN.qzero_ok(~F, qmap(~F, x), E.QSub{e1, e2}, h))))

# soundness: equal normal forms make an identity
def ident_ok(+e1: E.QExpr, +e2: E.QExpr, +h: {QN.qzero(E.QSub{e1, e2}) == True{} : Bool}) -> SV.Ident(e1, e2):
  x => ident_at(~QF.qfield(), e1, e2, h, x)

def qzero_ident.dec(~F: O.OField, b: Bool, +e1: E.QExpr, +e2: E.QExpr, eb: {b == QN.qzero(E.QSub{e1, e2}) : Bool}, hi: SV.Ident(e1, e2))
  -> {QN.qzero(E.QSub{e1, e2}) == True{} : Bool}:
  match b:
    case True{}:
      Equal.sym(Bool, True{}, QN.qzero(E.QSub{e1, e2}), eb)
    case False{}:
      absurd({QN.qzero(E.QSub{e1, e2}) == True{} : Bool}, wit_ne(~F, E.QSub{e1, e2}, Equal.sym(Bool, False{}, QN.qzero(E.QSub{e1, e2}), eb),
        FO.sub_of_eq(~F, O.eval(~F, qmap(~F, wpt(E.QSub{e1, e2})), e1), O.eval(~F, qmap(~F, wpt(E.QSub{e1, e2})), e2),
          q_eq(~F, wpt(E.QSub{e1, e2}), e1, e2, QE.ofq_eq(~F, E.qeval(wpt(E.QSub{e1, e2}), e1), E.qeval(wpt(E.QSub{e1, e2}), e2), hi(wpt(E.QSub{e1, e2})))))))

# completeness: an identity has equal normal forms
def qzero_ident(+e1: E.QExpr, +e2: E.QExpr, hi: SV.Ident(e1, e2)) -> {QN.qzero(E.QSub{e1, e2}) == True{} : Bool}:
  qzero_ident.dec(~QF.qfield(), QN.qzero(E.QSub{e1, e2}), e1, e2, {==}, hi)

# an identity holds in every ordered field
def ident_all(~F: O.OField, +e1: E.QExpr, +e2: E.QExpr, hi: SV.Ident(e1, e2), +env: List<&2, O.C(F)>) -> {O.eval(~F, env, e1) == O.eval(~F, env, e2) : O.C(F)}:
  FO.eq_of_sub(~F, O.eval(~F, env, e1), O.eval(~F, env, e2), QN.qzero_ok(~F, env, E.QSub{e1, e2}, qzero_ident(e1, e2, hi)))

# The same against 0
# ------------------

def ident0_at(~F: O.OField, +e: E.QExpr, +h: {QN.qzero(e) == True{} : Bool}, +x: List<&2, S.Q>) -> S.Q.eq(E.qeval(x, e), SV.qzero()):
  QE.ofq_eq_rev(~F, E.qeval(x, e), SV.qzero(),
    (%qbr(~F, x, e) : {_ == O.ofq(~F, SV.qzero()) : O.C(F)}
     %Equal.sym(O.C(F), O.ofq(~F, SV.qzero()), O.zero(F), QE.ofq_zero(~F)) : {O.eval(~F, qmap(~F, x), e) == _ : O.C(F)}
     QN.qzero_ok(~F, qmap(~F, x), e, h)))

def ident0_ok(+e: E.QExpr, +h: {QN.qzero(e) == True{} : Bool}) -> SV.Ident(e, E.QCst{SV.qzero()}):
  x => ident0_at(~QF.qfield(), e, h, x)

def qzero0.dec(~F: O.OField, b: Bool, +e: E.QExpr, eb: {b == QN.qzero(e) : Bool}, hi: SV.Ident(e, E.QCst{SV.qzero()})) -> {QN.qzero(e) == True{} : Bool}:
  match b:
    case True{}:
      Equal.sym(Bool, True{}, QN.qzero(e), eb)
    case False{}:
      absurd({QN.qzero(e) == True{} : Bool}, wit_ne(~F, e, Equal.sym(Bool, False{}, QN.qzero(e), eb),
        (%Equal.sym(O.C(F), O.eval(~F, qmap(~F, wpt(e)), e), O.ofq(~F, E.qeval(wpt(e), e)), qbr(~F, wpt(e), e)) : {_ == O.zero(F) : O.C(F)}
         %QE.ofq_zero(~F) : {O.ofq(~F, E.qeval(wpt(e), e)) == _ : O.C(F)}
         QE.ofq_eq(~F, E.qeval(wpt(e), e), SV.qzero(), hi(wpt(e))))))

def qzero0_ident(+e: E.QExpr, hi: SV.Ident(e, E.QCst{SV.qzero()})) -> {QN.qzero(e) == True{} : Bool}:
  qzero0.dec(~QF.qfield(), QN.qzero(e), e, {==}, hi)

# Dependence, decided
# -------------------

def dep.go(b: Bool) -> Bool:
  match b:
    case True{}:
      False{}
    case False{}:
      True{}

# e depends on v: its derivative in v does not normalize to 0
def dep(+e: E.QExpr, +v: Nat) -> Bool:
  dep.go(QN.qzero(DV.deriv(e, v)))

def dep_t(b: Bool, h: {dep.go(b) == True{} : Bool}, hz: {b == True{} : Bool}) -> Empty:
  match b:
    case True{}:
      KA.ft(h)
    case False{}:
      KA.ft(hz)

def dep_f(b: Bool, h: {dep.go(b) == False{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      absurd({False{} == True{} : Bool}, KA.tf(h))

def dep_ok(+e: E.QExpr, +v: Nat, +h: {dep(e, v) == True{} : Bool}) -> SV.Depends(e, v):
  hi => dep_t(QN.qzero(DV.deriv(e, v)), h, qzero0_ident(DV.deriv(e, v), hi))

def nodep_ok(+e: E.QExpr, +v: Nat, h: {dep(e, v) == False{} : Bool}) -> SV.Ident(DV.deriv(e, v), E.QCst{SV.qzero()}):
  ident0_ok(DV.deriv(e, v), dep_f(QN.qzero(DV.deriv(e, v)), h))

def dep_of.dec(b: Bool, +e: E.QExpr, +v: Nat, eb: {b == dep(e, v) : Bool}, hd: SV.Depends(e, v)) -> {dep(e, v) == True{} : Bool}:
  match b:
    case True{}:
      Equal.sym(Bool, True{}, dep(e, v), eb)
    case False{}:
      absurd({dep(e, v) == True{} : Bool}, hd(nodep_ok(e, v, Equal.sym(Bool, False{}, dep(e, v), eb))))

# and conversely: Depends makes dep true
def dep_of(+e: E.QExpr, +v: Nat, hd: SV.Depends(e, v)) -> {dep(e, v) == True{} : Bool}:
  dep_of.dec(dep(e, v), e, v, {==}, hd)
