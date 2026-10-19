# bend-cad: identities and dependence decided by normal forms
# (PLAN-sk13a S1), restated here so the gate checks lib/redpoly.bend,
# lib/nonroot.bend, lib/identpf.bend and lib/coefpf.bend until the solver
# imports them.
# - Every normal form is reduced: terms ascending strictly by monomial,
#   no zero coefficient, every monomial sorted.
# - The non-root lemma: a reduced integer polynomial other than 0 is not 0
#   at some integer point.
# - Ident(e1, e2) (equal at every rational point) holds exactly when
#   e1 - e2, its denominators cleared, normalizes to 0; then e1 = e2 in
#   every ordered field. The same against the constant 0.
# - Identities read coefficient by coefficient: coef(e, m), the rational
#   coefficient of the monomial m in e, is linear over combinations (the
#   coefficients of lin(ls, es) are qlin), a constant's is itself at 1 and
#   0 elsewhere, and Ident(e1, e2) gives equal coefficients everywhere.
# - e depends on v (the spec's Depends: its derivative in v is not
#   identically 0) exactly when dep(e, v), which normalizes the
#   derivative. The structure's adjacency dadj(e) (the variables e
#   mentions that it depends on) is exactly that: each is depended on, and
#   e depends on nothing outside it (lib/deppf.bend).

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/deriv.bend as DV
import ../spec/solve.bend as SV
import ../lib/zring.bend as R
import ../lib/listpf.bend as L
import ../lib/qnorm.bend as QN
import ../lib/redpoly.bend as RP
import ../lib/nonroot.bend as NRT
import ../lib/identpf.bend as ID
import ../lib/coefpf.bend as CF
import ../lib/deppf.bend as DP

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

def ident_coefs(+e1: E.QExpr, +e2: E.QExpr, hi: SV.Ident(e1, e2), +m: List<&2, Nat>) -> S.Q.eq(CF.coef(e1, m), CF.coef(e2, m)):
  CF.ident_coef(e1, e2, hi, m)

def coef_lin(ls: List<&2, S.Q>, es: List<&2, E.QExpr>, +m: List<&2, Nat>) -> {CF.qlin(ls, es, m) == CF.coef(SV.lin(ls, es), m) : S.Q}:
  CF.coef_lin(ls, es, m)

def coef_const_one(k: S.Q) -> {k == CF.coef(E.QCst{k}, Nil{}) : S.Q}:
  CF.coef_cst_one(k)

def coef_const_other(k: S.Q, +v: Nat, +vs: List<&2, Nat>) -> S.Q.eq(CF.coef(E.QCst{k}, Con{v, vs}), SV.qzero()):
  CF.coef_cst_other(k, v, vs)

# (x + 1)(x - 1): coefficient 1 at x x, -1 at 1, 0 at x
def sq_coefs() -> {[CF.coef(E.QMul{E.QAdd{E.QVar{0n}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}, E.QSub{E.QVar{0n}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}}, [0n, 0n]),
                    CF.coef(E.QMul{E.QAdd{E.QVar{0n}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}, E.QSub{E.QVar{0n}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}}, Nil{}),
                    CF.coef(E.QMul{E.QAdd{E.QVar{0n}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}, E.QSub{E.QVar{0n}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}}, [0n])]
    == [S.Q{S.Zpos{S.XH{}}, S.XH{}}, S.Q{S.Zneg{S.XH{}}, S.XH{}}, S.Q{S.Z0{}, S.XH{}}] : List<S.Q>}:
  {==}

def adjacency_depends(+e: E.QExpr, +v: Nat, h: {SV.mem(v, DP.dadj(e)) == True{} : Bool}) -> SV.Depends(e, v):
  DP.dadj_depends(e, v, h)

def adjacency_within(+e: E.QExpr, +w: List<&2, Nat>, +hs: {L.subl(DP.dadj(e), w) == True{} : Bool}) -> SV.DependsWithin(e, w):
  DP.dadj_within(e, w, hs)

# x - x + y: depends on y, not on x
def xxy() -> E.QExpr:
  E.QAdd{E.QSub{E.QVar{0n}, E.QVar{0n}}, E.QVar{1n}}

def xxy_deps() -> {[ID.dep(xxy(), 0n), ID.dep(xxy(), 1n)] == [False{}, True{}] : List<Bool>}:
  {==}

def xxy_adj() -> {DP.dadj(xxy()) == [1n] : List<&2, Nat>}:
  {==}

# (x + 1)(x - 1) is x x - 1
def sq_ident() -> SV.Ident(E.QMul{E.QAdd{E.QVar{0n}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}, E.QSub{E.QVar{0n}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}},
    E.QSub{E.QMul{E.QVar{0n}, E.QVar{0n}}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}):
  ID.ident_ok(E.QMul{E.QAdd{E.QVar{0n}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}, E.QSub{E.QVar{0n}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}},
    E.QSub{E.QMul{E.QVar{0n}, E.QVar{0n}}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}, {==})

# x y - x is not 0 everywhere: its witness shows it
def wit_demo() -> {RP.nz(R.epoly(NRT.witness(R.norm(E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{0n}})), R.norm(E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{0n}}))) == True{} : Bool}:
  {==}
