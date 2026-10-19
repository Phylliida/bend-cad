# bend-cad: identities and dependence decided by normal forms
# (PLAN-sk13a S1), restated here so the gate checks lib/redpoly.bend,
# lib/nonroot.bend and lib/identpf.bend until the solver imports them.
# - Every normal form is reduced: terms ascending strictly by monomial,
#   no zero coefficient, every monomial sorted.
# - The non-root lemma: a reduced integer polynomial other than 0 is not 0
#   at some integer point.
# - Ident(e1, e2) (equal at every rational point) holds exactly when
#   e1 - e2, its denominators cleared, normalizes to 0; then e1 = e2 in
#   every ordered field. The same against the constant 0.
# - e depends on v (the spec's Depends: its derivative in v is not
#   identically 0) exactly when dep(e, v), which normalizes the
#   derivative.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/deriv.bend as DV
import ../spec/solve.bend as SV
import ../lib/zring.bend as R
import ../lib/qnorm.bend as QN
import ../lib/redpoly.bend as RP
import ../lib/nonroot.bend as NRT
import ../lib/identpf.bend as ID

def norm_reduced(e: E.ZExpr) -> {RP.red(R.norm(e)) == True{} : Bool}:
  RP.norm_red(e)

def nonroot(+p: List<&2, R.ZTerm>, hr: {RP.red(p) == True{} : Bool}, hne: {Nil{} == p : List<&2, R.ZTerm>} -> Empty) -> {RP.nz(R.epoly(NRT.witness(p), p)) == True{} : Bool}:
  NRT.nonroot(p, hr, hne)

def ident_sound(+e1: E.QExpr, +e2: E.QExpr, +h: {QN.qzero(E.QSub{e1, e2}) == True{} : Bool}) -> SV.Ident(e1, e2):
  ID.ident_ok(e1, e2, h)

def ident_complete(+e1: E.QExpr, +e2: E.QExpr, hi: SV.Ident(e1, e2)) -> {QN.qzero(E.QSub{e1, e2}) == True{} : Bool}:
  ID.qzero_ident(e1, e2, hi)

def ident_transfer(~F: O.OField, +e1: E.QExpr, +e2: E.QExpr, hi: SV.Ident(e1, e2), +env: List<&2, O.C(F)>) -> {O.eval(~F, env, e1) == O.eval(~F, env, e2) : O.C(F)}:
  ID.ident_all(~F, e1, e2, hi, env)

def ident0_sound(+e: E.QExpr, +h: {QN.qzero(e) == True{} : Bool}) -> SV.Ident(e, E.QCst{SV.qzero()}):
  ID.ident0_ok(e, h)

def ident0_complete(+e: E.QExpr, hi: SV.Ident(e, E.QCst{SV.qzero()})) -> {QN.qzero(e) == True{} : Bool}:
  ID.qzero0_ident(e, hi)

def depends_sound(+e: E.QExpr, +v: Nat, +h: {ID.dep(e, v) == True{} : Bool}) -> SV.Depends(e, v):
  ID.dep_ok(e, v, h)

def depends_not(+e: E.QExpr, +v: Nat, h: {ID.dep(e, v) == False{} : Bool}) -> SV.Ident(DV.deriv(e, v), E.QCst{SV.qzero()}):
  ID.nodep_ok(e, v, h)

def depends_complete(+e: E.QExpr, +v: Nat, hd: SV.Depends(e, v)) -> {ID.dep(e, v) == True{} : Bool}:
  ID.dep_of(e, v, hd)

# x - x + y: depends on y, not on x
def xxy() -> E.QExpr:
  E.QAdd{E.QSub{E.QVar{0n}, E.QVar{0n}}, E.QVar{1n}}

def xxy_deps() -> {[ID.dep(xxy(), 0n), ID.dep(xxy(), 1n)] == [False{}, True{}] : List<Bool>}:
  {==}

# (x + 1)(x - 1) is x x - 1
def sq_ident() -> SV.Ident(E.QMul{E.QAdd{E.QVar{0n}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}, E.QSub{E.QVar{0n}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}},
    E.QSub{E.QMul{E.QVar{0n}, E.QVar{0n}}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}):
  ID.ident_ok(E.QMul{E.QAdd{E.QVar{0n}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}, E.QSub{E.QVar{0n}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}},
    E.QSub{E.QMul{E.QVar{0n}, E.QVar{0n}}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}, {==})

# x y - x is not 0 everywhere: its witness shows it
def wit_demo() -> {RP.nz(R.epoly(NRT.witness(R.norm(E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{0n}})), R.norm(E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{0n}}))) == True{} : Bool}:
  {==}
