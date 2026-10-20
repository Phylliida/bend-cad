# bend-cad: the degree-0 elimination (PLAN-sk13a S2), restated here so the
# gate checks lib/elimpf.bend, lib/drvpf.bend and lib/indpf.bend until the
# solver's single pass (S4) imports them. B is a basis, rows its echelon
# rows (EP.rinv, one row per equation of B, in order), e an equation:
# - no rows for no basis;
# - a nonzero residual extends the rows, and B by e;
# - a zero residual: e is a constant combination of B (the spec's Ident,
#   with the multipliers DR.dropls);
# - a nonzero residual: e is no constant combination of B.
# With B = [x - y]: 2x - 2y drops, x + y is independent.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../lib/elim.bend as EL
import ../lib/elimpf.bend as EP
import ../lib/drvpf.bend as DR
import ../lib/indpf.bend as IN

def rows_none(+B: List<&2, E.QExpr>) -> {EP.rinv(B, Nil{}, 0n) == True{} : Bool}:
  {==}

def rows_grow(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, +h: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hne: {EP.isnil(EP.resp(EL.resid(rows, e))) == False{} : Bool}) -> {EP.rinv(EP.qsnoc(B, e), EL.rsnoc(rows, EL.row_of(EL.resid(rows, e))), 0n) == True{} : Bool}:
  EP.new_rinv(B, rows, e, h, hl, hne)

def drop_derivable(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, +h: {EP.rinv(B, rows, 0n) == True{} : Bool}, hnil: {EP.isnil(EP.resp(EL.resid(rows, e))) == True{} : Bool})
  -> SV.Ident(e, SV.lin(DR.dropls(DR.rescb(EL.resid(rows, e)), DR.resbt(EL.resid(rows, e)), e, B), B)):
  DR.derivable(B, rows, e, h, hnil)

def kept_independent(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, +h: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hne: {EP.isnil(EP.resp(EL.resid(rows, e))) == False{} : Bool}) -> @ls: List<&2, S.Q> -> SV.Ident(e, SV.lin(ls, B)) -> Empty:
  IN.indep(B, rows, e, h, hl, hne)

# Demo
# ----

def one() -> S.Q:
  S.Q{S.Zpos{S.XH{}}, S.XH{}}

def two() -> S.Q:
  S.Q{S.Zpos{S.XO{S.XH{}}}, S.XH{}}

# x - y, 2x - 2y, x + y
def g1() -> E.QExpr:
  E.QSub{E.QVar{0n}, E.QVar{1n}}

def g2() -> E.QExpr:
  E.QSub{E.QMul{E.QCst{two()}, E.QVar{0n}}, E.QMul{E.QCst{two()}, E.QVar{1n}}}

def g3() -> E.QExpr:
  E.QAdd{E.QVar{0n}, E.QVar{1n}}

def rows1() -> List<&2, EL.Row>:
  EL.rsnoc(Nil{}, EL.row_of(EL.resid(Nil{}, g1())))

def rows1_ok() -> {EP.rinv(EP.qsnoc(Nil{}, g1()), rows1(), 0n) == True{} : Bool}:
  EP.new_rinv(Nil{}, Nil{}, g1(), {==}, {==}, {==})

def g2_drops() -> SV.Ident(g2(), SV.lin(DR.dropls(DR.rescb(EL.resid(rows1(), g2())), DR.resbt(EL.resid(rows1(), g2())), g2(), [g1()]), [g1()])):
  DR.derivable([g1()], rows1(), g2(), rows1_ok(), {==})

def g3_independent() -> @ls: List<&2, S.Q> -> SV.Ident(g3(), SV.lin(ls, [g1()])) -> Empty:
  IN.indep([g1()], rows1(), g3(), rows1_ok(), {==}, {==})

# the drop's multiplier: 2x - 2y is 2 (x - y)
def g2_mult() -> {DR.dropls(DR.rescb(EL.resid(rows1(), g2())), DR.resbt(EL.resid(rows1(), g2())), g2(), [g1()]) == [two()] : List<&2, S.Q>}:
  {==}
