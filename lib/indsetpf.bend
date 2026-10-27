# bend-cad: proofs about independence of a set (lib/indset.bend). If vs
# pass indset after the rows of B, a combination lin(ls, vs) in the span
# of B has every coefficient 0 (indset_ok), by induction from the front:
# the rest's combination is in the span of B and the first, so (the rest
# passing after it) its coefficients are 0; then l v is in the span of B,
# and l is 0 or v would be too, against its nonzero residual. A zero
# combination is 0 (lin_allz). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ../spec/dir.bend as DR
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./indpf.bend as IN
import ./q.bend as LQ
import ./qring.bend as QR
import ./qalg.bend as QA
import ./listpf.bend as LP2
import ./spanpf.bend as SN
import ./pairpf.bend as PP
import ./labpf.bend as LP
import ./indset.bend as IS

def absurd(-A: Type, x: Empty) -> A:
  match x:

def bnot_t(b: Bool, h: {SV.bnot(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Equal.sym(Bool, False{}, True{}, h)
    case False{}:
      {==}

# A zero combination
# ------------------

def lin_allz.at(+p: List<&2, S.Q>, ls: List<&2, S.Q>, vs: List<&2, E.QExpr>, +h: {IS.allz(ls, vs) == True{} : Bool})
  -> S.Q.eq(E.qeval(p, SV.lin(ls, vs)), S.Q{S.Z0{}, S.XH{}}):
  match ls vs:
    case Con{+l, +lt} Con{+v, +vt}:
      LQ.q_trans(S.Q.add(S.Q.mul(l, E.qeval(p, v)), E.qeval(p, SV.lin(lt, vt))), S.Q.add(S.Q.mul(S.Q{S.Z0{}, S.XH{}}, E.qeval(p, v)), S.Q{S.Z0{}, S.XH{}}), S.Q{S.Z0{}, S.XH{}},
        QA.add_cong(S.Q.mul(l, E.qeval(p, v)), S.Q.mul(S.Q{S.Z0{}, S.XH{}}, E.qeval(p, v)), E.qeval(p, SV.lin(lt, vt)), S.Q{S.Z0{}, S.XH{}},
          LQ.q_mul_cong_l(l, S.Q{S.Z0{}, S.XH{}}, E.qeval(p, v), LP.qnz_f(l, bnot_t(DR.qnz(l), LP2.band_l(SV.bnot(DR.qnz(l)), IS.allz(lt, vt), h)))),
          lin_allz.at(p, lt, vt, LP2.band_r(SV.bnot(DR.qnz(l)), IS.allz(lt, vt), h))),
        QR.qring_eq([E.qeval(p, v)], E.QAdd{E.QMul{E.QCst{S.Q{S.Z0{}, S.XH{}}}, E.QVar{0n}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}, {==}))
    case Nil{} vs:
      LQ.q_refl(S.Q{S.Z0{}, S.XH{}})
    case Con{+l, +lt} Nil{}:
      LQ.q_refl(S.Q{S.Z0{}, S.XH{}})

# with every coefficient 0, the combination is 0
def lin_allz(+ls: List<&2, S.Q>, +vs: List<&2, E.QExpr>, +h: {IS.allz(ls, vs) == True{} : Bool}) -> SV.Ident(SV.lin(ls, vs), E.QCst{S.Q{S.Z0{}, S.XH{}}}):
  p => lin_allz.at(p, ls, vs, h)

# The induction
# -------------

# L = 1 (l v + L) + (-l v + 0)
def lift.at(+p: List<&2, S.Q>, +l: S.Q, +v: E.QExpr, +L: E.QExpr)
  -> S.Q.eq(E.qeval(p, L), E.qeval(p, E.QAdd{E.QMul{E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}, E.QAdd{E.QMul{E.QCst{l}, v}, L}}, E.QAdd{E.QMul{E.QCst{S.Q.neg(l)}, v}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}})):
  QR.qring_eq([l, E.qeval(p, v), E.qeval(p, L)], E.QVar{2n},
    E.QAdd{E.QMul{E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}, E.QAdd{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QVar{2n}}}, E.QAdd{E.QMul{E.QNeg{E.QVar{0n}}, E.QVar{1n}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}}, {==})

# v = (1/l)(l v + L) + 0, when L is 0 and l is not
def solve1.at(+p: List<&2, S.Q>, +l: S.Q, +v: E.QExpr, +L: E.QExpr, hl: S.Q.eq(l, S.Q{S.Z0{}, S.XH{}}) -> Empty, hL: S.Q.eq(E.qeval(p, L), S.Q{S.Z0{}, S.XH{}}))
  -> S.Q.eq(E.qeval(p, v), E.qeval(p, E.QAdd{E.QMul{E.QCst{S.Q.inv(l)}, E.QAdd{E.QMul{E.QCst{l}, v}, L}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}})):
  QA.ch4(E.qeval(p, v), S.Q.mul(S.Q{S.Zpos{S.XH{}}, S.XH{}}, E.qeval(p, v)), S.Q.mul(S.Q.mul(l, S.Q.inv(l)), E.qeval(p, v)),
    S.Q.add(S.Q.mul(S.Q.inv(l), S.Q.add(S.Q.mul(l, E.qeval(p, v)), S.Q{S.Z0{}, S.XH{}})), S.Q{S.Z0{}, S.XH{}}),
    S.Q.add(S.Q.mul(S.Q.inv(l), S.Q.add(S.Q.mul(l, E.qeval(p, v)), E.qeval(p, L))), S.Q{S.Z0{}, S.XH{}}),
    LQ.q_sym(S.Q.mul(S.Q{S.Zpos{S.XH{}}, S.XH{}}, E.qeval(p, v)), E.qeval(p, v), QA.one_mul(E.qeval(p, v))),
    LQ.q_mul_cong_l(S.Q{S.Zpos{S.XH{}}, S.XH{}}, S.Q.mul(l, S.Q.inv(l)), E.qeval(p, v), LQ.q_sym(S.Q.mul(l, S.Q.inv(l)), S.Q{S.Zpos{S.XH{}}, S.XH{}}, LQ.q_mul_inv(l, hl))),
    QR.qring_eq([l, S.Q.inv(l), E.qeval(p, v)], E.QMul{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QVar{2n}},
      E.QAdd{E.QMul{E.QVar{1n}, E.QAdd{E.QMul{E.QVar{0n}, E.QVar{2n}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, {==}),
    LQ.q_add_cong_l(S.Q.mul(S.Q.inv(l), S.Q.add(S.Q.mul(l, E.qeval(p, v)), S.Q{S.Z0{}, S.XH{}})), S.Q.mul(S.Q.inv(l), S.Q.add(S.Q.mul(l, E.qeval(p, v)), E.qeval(p, L))), S.Q{S.Z0{}, S.XH{}},
      LQ.q_mul_cong_r(S.Q.inv(l), S.Q.add(S.Q.mul(l, E.qeval(p, v)), S.Q{S.Z0{}, S.XH{}}), S.Q.add(S.Q.mul(l, E.qeval(p, v)), E.qeval(p, L)),
        LQ.q_add_cong_r(S.Q.mul(l, E.qeval(p, v)), S.Q{S.Z0{}, S.XH{}}, E.qeval(p, L), LQ.q_sym(E.qeval(p, L), S.Q{S.Z0{}, S.XH{}}, hL)))))

def solve1.ok(+p: List<&2, S.Q>, +l: S.Q, +v: E.QExpr, +lt: List<&2, S.Q>, +vt: List<&2, E.QExpr>, +eb: {True{} == DR.qnz(l) : Bool}, +hz: {IS.allz(lt, vt) == True{} : Bool})
  -> S.Q.eq(E.qeval(p, v), E.qeval(p, E.QAdd{E.QMul{E.QCst{S.Q.inv(l)}, E.QAdd{E.QMul{E.QCst{l}, v}, SV.lin(lt, vt)}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}})):
  solve1.at(p, l, v, SV.lin(lt, vt), e => LP.qnz_t(l, Equal.sym(Bool, True{}, DR.qnz(l), eb), e), lin_allz.at(p, lt, vt, hz))

def indep_in(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +v: E.QExpr, +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hne: {EP.isnil(EP.resp(EL.resid(rows, v))) == False{} : Bool}, +h: SN.InSpan(v, B)) -> Empty:
  IN.indep(B, rows, v, hr, hl, hne)(SN.in_ls(v, B, h), SN.in_ident(v, B, h))

# the first coefficient is 0, given the rest are
def indset_ok.first(b: Bool, +l: S.Q, +v: E.QExpr, +lt: List<&2, S.Q>, +vt: List<&2, E.QExpr>, +B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>,
  +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat}, +eb: {b == DR.qnz(l) : Bool},
  hne: {EP.isnil(EP.resp(EL.resid(rows, v))) == False{} : Bool}, +hin: SN.InSpan(E.QAdd{E.QMul{E.QCst{l}, v}, SV.lin(lt, vt)}, B), +hz: {IS.allz(lt, vt) == True{} : Bool})
  -> {SV.band(SV.bnot(b), IS.allz(lt, vt)) == True{} : Bool}:
  match b:
    case True{}:
      absurd({SV.band(SV.bnot(True{}), IS.allz(lt, vt)) == True{} : Bool},
        indep_in(B, rows, v, hr, hl, hne,
          PP.in_tr(E.QAdd{E.QMul{E.QCst{S.Q.inv(l)}, E.QAdd{E.QMul{E.QCst{l}, v}, SV.lin(lt, vt)}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, v, B,
            SN.in_comb(S.Q.inv(l), E.QAdd{E.QMul{E.QCst{l}, v}, SV.lin(lt, vt)}, E.QCst{S.Q{S.Z0{}, S.XH{}}}, B, hin, SN.in_zero(B)),
            p => solve1.ok(p, l, v, lt, vt, eb, hz))))
    case False{}:
      hz

def allz_nil(ls: List<&2, S.Q>) -> {IS.allz(ls, Nil{}) == True{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{l, lt}:
      {==}

# a combination of vs in the span of B has every coefficient 0
def indset_ok(vs: List<&2, E.QExpr>, +B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  +hi: {IS.indset(vs, rows) == True{} : Bool}, ls: List<&2, S.Q>, +hin: SN.InSpan(SV.lin(ls, vs), B)) -> {IS.allz(ls, vs) == True{} : Bool}:
  match vs ls:
    case Con{+v, +vt} Con{+l, +lt}:
      indset_ok.first(DR.qnz(l), l, v, lt, vt, B, rows, hr, hl, {==},
        bnot_t(EP.isnil(EP.resp(EL.resid(rows, v))), LP2.band_l(SV.bnot(EP.isnil(EP.resp(EL.resid(rows, v)))), IS.indset(vt, EL.rsnoc(rows, EL.row_of(EL.resid(rows, v)))), hi)),
        hin,
        indset_ok(vt, EP.qsnoc(B, v), EL.rsnoc(rows, EL.row_of(EL.resid(rows, v))),
          EP.new_rinv(B, rows, v, hr, hl, bnot_t(EP.isnil(EP.resp(EL.resid(rows, v))), LP2.band_l(SV.bnot(EP.isnil(EP.resp(EL.resid(rows, v)))), IS.indset(vt, EL.rsnoc(rows, EL.row_of(EL.resid(rows, v)))), hi))),
          PP.len_snoc(B, rows, v, EL.row_of(EL.resid(rows, v)), hl),
          LP2.band_r(SV.bnot(EP.isnil(EP.resp(EL.resid(rows, v)))), IS.indset(vt, EL.rsnoc(rows, EL.row_of(EL.resid(rows, v)))), hi),
          lt,
          PP.in_tr(E.QAdd{E.QMul{E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}, E.QAdd{E.QMul{E.QCst{l}, v}, SV.lin(lt, vt)}}, E.QAdd{E.QMul{E.QCst{S.Q.neg(l)}, v}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}}, SV.lin(lt, vt), EP.qsnoc(B, v),
            SN.in_comb(S.Q{S.Zpos{S.XH{}}, S.XH{}}, E.QAdd{E.QMul{E.QCst{l}, v}, SV.lin(lt, vt)}, E.QAdd{E.QMul{E.QCst{S.Q.neg(l)}, v}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, EP.qsnoc(B, v),
              SN.in_snoc(E.QAdd{E.QMul{E.QCst{l}, v}, SV.lin(lt, vt)}, B, v, hin),
              SN.in_comb(S.Q.neg(l), v, E.QCst{S.Q{S.Z0{}, S.XH{}}}, EP.qsnoc(B, v), SN.in_last(B, v), SN.in_zero(EP.qsnoc(B, v)))),
            p => lift.at(p, l, v, SV.lin(lt, vt)))))
    case Nil{} ls:
      allz_nil(ls)
    case Con{+v, +vt} Nil{}:
      {==}
