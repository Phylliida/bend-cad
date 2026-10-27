# bend-cad: the pair test, proven (PLAN-sk13b B3). Sound: what it returns
# combines u and v into the span. Complete: if some a u + b v with b not 0
# lies in the span, it returns something (u in the span, or v in the span
# of B and u); and if b is 0 and a is not, u is in the span and it returns
# (1, 0). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./drvpf.bend as DV
import ./q.bend as LQ
import ./qring.bend as QR
import ./spanpf.bend as SN
import ./cwpf.bend as CW
import ./pair.bend as PT

def absurd(-A: Type, x: Empty) -> A:
  match x:

# The last coefficient
# --------------------

def qdrop_nil(n: Nat) -> {PT.qdrop(n, Nil{}) == Nil{} : List<&2, S.Q>}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def qdrop_succ(+n: Nat, ls: List<&2, S.Q>) -> {PT.qdrop(1n+n, ls) == PT.qdrop(n, SN.qtl(ls)) : List<&2, S.Q>}:
  match ls:
    case Nil{}:
      Equal.sym(List<&2, S.Q>, PT.qdrop(n, Nil{}), Nil{}, qdrop_nil(n))
    case Con{l, lt}:
      {==}

def lastc_con(+ls: List<&2, S.Q>, +b: E.QExpr, +bt: List<&2, E.QExpr>) -> {PT.lastc(ls, Con{b, bt}) == PT.lastc(SN.qtl(ls), bt) : S.Q}:
  %Equal.sym(List<&2, S.Q>, PT.qdrop(1n+SV.neqs(bt), ls), PT.qdrop(SV.neqs(bt), SN.qtl(ls)), qdrop_succ(SV.neqs(bt), ls)) : {PT.qhd(_) == PT.lastc(SN.qtl(ls), bt) : S.Q}
  {==}

def qhd_eq(ls: List<&2, S.Q>) -> {PT.qhd(ls) == SN.qhd(ls) : S.Q}:
  match ls:
    case Nil{}:
      {==}
    case Con{l, lt}:
      {==}

def lin_snoc_last.base(+p: List<&2, S.Q>, +h: S.Q, +lt: List<&2, S.Q>, +x: E.QExpr) -> S.Q.eq(S.Q.add(S.Q.mul(h, E.qeval(p, x)), E.qeval(p, SV.lin(lt, Nil{}))), S.Q.add(E.qeval(p, E.QCst{S.Q{S.Z0{}, S.XH{}}}), S.Q.mul(h, E.qeval(p, x)))):
  %Equal.sym(E.QExpr, SV.lin(lt, Nil{}), E.QCst{S.Q{S.Z0{}, S.XH{}}}, SN.lin_nil(lt)) : S.Q.eq(S.Q.add(S.Q.mul(h, E.qeval(p, x)), E.qeval(p, _)), S.Q.add(E.qeval(p, E.QCst{S.Q{S.Z0{}, S.XH{}}}), S.Q.mul(h, E.qeval(p, x))))
  QR.qring_eq([h, E.qeval(p, x)], E.QAdd{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, E.QAdd{E.QCst{S.Q{S.Z0{}, S.XH{}}}, E.QMul{E.QVar{0n}, E.QVar{1n}}}, {==})

def lin_snoc_last.go(+p: List<&2, S.Q>, +ls: List<&2, S.Q>, +b: E.QExpr, +bt: List<&2, E.QExpr>, +x: E.QExpr,
  h1: S.Q.eq(E.qeval(p, SV.lin(ls, Con{b, EP.qsnoc(bt, x)})), S.Q.add(S.Q.mul(SN.qhd(ls), E.qeval(p, b)), E.qeval(p, SV.lin(SN.qtl(ls), EP.qsnoc(bt, x))))),
  ih: S.Q.eq(E.qeval(p, SV.lin(SN.qtl(ls), EP.qsnoc(bt, x))), S.Q.add(E.qeval(p, SV.lin(SN.qtl(ls), bt)), S.Q.mul(PT.lastc(SN.qtl(ls), bt), E.qeval(p, x)))),
  h2: S.Q.eq(E.qeval(p, SV.lin(ls, Con{b, bt})), S.Q.add(S.Q.mul(SN.qhd(ls), E.qeval(p, b)), E.qeval(p, SV.lin(SN.qtl(ls), bt)))))
  -> S.Q.eq(E.qeval(p, SV.lin(ls, EP.qsnoc(Con{b, bt}, x))), S.Q.add(E.qeval(p, SV.lin(ls, Con{b, bt})), S.Q.mul(PT.lastc(SN.qtl(ls), bt), E.qeval(p, x)))):
  LQ.q_trans(E.qeval(p, SV.lin(ls, Con{b, EP.qsnoc(bt, x)})),
    S.Q.add(S.Q.mul(SN.qhd(ls), E.qeval(p, b)), S.Q.add(E.qeval(p, SV.lin(SN.qtl(ls), bt)), S.Q.mul(PT.lastc(SN.qtl(ls), bt), E.qeval(p, x)))),
    S.Q.add(E.qeval(p, SV.lin(ls, Con{b, bt})), S.Q.mul(PT.lastc(SN.qtl(ls), bt), E.qeval(p, x))),
    LQ.q_trans(E.qeval(p, SV.lin(ls, Con{b, EP.qsnoc(bt, x)})), S.Q.add(S.Q.mul(SN.qhd(ls), E.qeval(p, b)), E.qeval(p, SV.lin(SN.qtl(ls), EP.qsnoc(bt, x)))),
      S.Q.add(S.Q.mul(SN.qhd(ls), E.qeval(p, b)), S.Q.add(E.qeval(p, SV.lin(SN.qtl(ls), bt)), S.Q.mul(PT.lastc(SN.qtl(ls), bt), E.qeval(p, x)))),
      h1, LQ.q_add_cong_r(S.Q.mul(SN.qhd(ls), E.qeval(p, b)), E.qeval(p, SV.lin(SN.qtl(ls), EP.qsnoc(bt, x))), S.Q.add(E.qeval(p, SV.lin(SN.qtl(ls), bt)), S.Q.mul(PT.lastc(SN.qtl(ls), bt), E.qeval(p, x))), ih)),
    LQ.q_trans(S.Q.add(S.Q.mul(SN.qhd(ls), E.qeval(p, b)), S.Q.add(E.qeval(p, SV.lin(SN.qtl(ls), bt)), S.Q.mul(PT.lastc(SN.qtl(ls), bt), E.qeval(p, x)))),
      S.Q.add(S.Q.add(S.Q.mul(SN.qhd(ls), E.qeval(p, b)), E.qeval(p, SV.lin(SN.qtl(ls), bt))), S.Q.mul(PT.lastc(SN.qtl(ls), bt), E.qeval(p, x))),
      S.Q.add(E.qeval(p, SV.lin(ls, Con{b, bt})), S.Q.mul(PT.lastc(SN.qtl(ls), bt), E.qeval(p, x))),
      QR.qring_eq([S.Q.mul(SN.qhd(ls), E.qeval(p, b)), E.qeval(p, SV.lin(SN.qtl(ls), bt)), S.Q.mul(PT.lastc(SN.qtl(ls), bt), E.qeval(p, x))],
        E.QAdd{E.QVar{0n}, E.QAdd{E.QVar{1n}, E.QVar{2n}}}, E.QAdd{E.QAdd{E.QVar{0n}, E.QVar{1n}}, E.QVar{2n}}, {==}),
      LQ.q_add_cong_l(S.Q.add(S.Q.mul(SN.qhd(ls), E.qeval(p, b)), E.qeval(p, SV.lin(SN.qtl(ls), bt))), E.qeval(p, SV.lin(ls, Con{b, bt})), S.Q.mul(PT.lastc(SN.qtl(ls), bt), E.qeval(p, x)),
        LQ.q_sym(E.qeval(p, SV.lin(ls, Con{b, bt})), S.Q.add(S.Q.mul(SN.qhd(ls), E.qeval(p, b)), E.qeval(p, SV.lin(SN.qtl(ls), bt))), h2))))

# lin over B with x appended: lin over B, plus x's coefficient times x
def lin_snoc_last(B: List<&2, E.QExpr>, +p: List<&2, S.Q>, +ls: List<&2, S.Q>, +x: E.QExpr)
  -> S.Q.eq(E.qeval(p, SV.lin(ls, EP.qsnoc(B, x))), S.Q.add(E.qeval(p, SV.lin(ls, B)), S.Q.mul(PT.lastc(ls, B), E.qeval(p, x)))):
  match B:
    case Nil{}:
      %Equal.sym(E.QExpr, SV.lin(ls, Nil{}), E.QCst{S.Q{S.Z0{}, S.XH{}}}, SN.lin_nil(ls)) : S.Q.eq(E.qeval(p, SV.lin(ls, [x])), S.Q.add(E.qeval(p, _), S.Q.mul(PT.lastc(ls, Nil{}), E.qeval(p, x))))
      %Equal.sym(S.Q, PT.qhd(ls), SN.qhd(ls), qhd_eq(ls)) : S.Q.eq(E.qeval(p, SV.lin(ls, [x])), S.Q.add(E.qeval(p, E.QCst{S.Q{S.Z0{}, S.XH{}}}), S.Q.mul(_, E.qeval(p, x))))
      LQ.q_trans(E.qeval(p, SV.lin(ls, [x])), S.Q.add(S.Q.mul(SN.qhd(ls), E.qeval(p, x)), E.qeval(p, SV.lin(SN.qtl(ls), Nil{}))), S.Q.add(E.qeval(p, E.QCst{S.Q{S.Z0{}, S.XH{}}}), S.Q.mul(SN.qhd(ls), E.qeval(p, x))),
        SN.lin_ht(p, ls, x, Nil{}),
        lin_snoc_last.base(p, SN.qhd(ls), SN.qtl(ls), x))
    case Con{+b, +bt}:
      %Equal.sym(S.Q, PT.lastc(ls, Con{b, bt}), PT.lastc(SN.qtl(ls), bt), lastc_con(ls, b, bt)) : S.Q.eq(E.qeval(p, SV.lin(ls, EP.qsnoc(Con{b, bt}, x))), S.Q.add(E.qeval(p, SV.lin(ls, Con{b, bt})), S.Q.mul(_, E.qeval(p, x))))
      lin_snoc_last.go(p, ls, b, bt, x, SN.lin_ht(p, ls, b, EP.qsnoc(bt, x)), lin_snoc_last(bt, p, SN.qtl(ls), x), SN.lin_ht(p, ls, b, bt))


# Transport and small facts
# -------------------------

def ident_tr.at(+p: List<&2, S.Q>, +e: E.QExpr, +e2: E.QExpr, +ls: List<&2, S.Q>, +B: List<&2, E.QExpr>, hi: SV.Ident(e2, e), h: SV.Ident(e, SV.lin(ls, B))) -> S.Q.eq(E.qeval(p, e2), E.qeval(p, SV.lin(ls, B))):
  LQ.q_trans(E.qeval(p, e2), E.qeval(p, e), E.qeval(p, SV.lin(ls, B)), hi(p), h(p))

# membership moves along an identity
def in_tr(+e: E.QExpr, +e2: E.QExpr, +B: List<&2, E.QExpr>, +h: SN.InSpan(e, B), hi: SV.Ident(e2, e)) -> SN.InSpan(e2, B):
  SN.in_of_ident(e2, B, SN.in_ls(e, B, h), p => ident_tr.at(p, e, e2, SN.in_ls(e, B, h), B, hi, SN.in_ident(e, B, h)))

def some_or(m: Maybe<&2, PT.Pr>, +d: PT.Pr) -> PT.Pr:
  match m:
    case Some{x}:
      x
    case None{}:
      d

def is_some(m: Maybe<&2, PT.Pr>) -> Bool:
  match m:
    case Some{x}:
      True{}
    case None{}:
      False{}

def some_inj(+x: PT.Pr, +y: PT.Pr, h: {Some{x} == Some{y} : Maybe<&2, PT.Pr>}) -> {x == y : PT.Pr}:
  Equal.cong(Maybe<&2, PT.Pr>, PT.Pr, m => some_or(m, x), Some{x}, Some{y}, h)

def none_some.p(b: Bool) -> Data:
  match b:
    case False{}:
      Empty
    case True{}:
      Unit

# Sound
# -----

def none_some(+y: PT.Pr, h: {None{} == Some{y} : Maybe<&2, PT.Pr>}) -> Empty:
  %Equal.sym(Bool, False{}, True{}, Equal.cong(Maybe<&2, PT.Pr>, Bool, m => is_some(m), None{}, Some{y}, h)) : none_some.p(_)
  Unit{}

def pt_first.at(+p: List<&2, S.Q>, +u: E.QExpr, +v: E.QExpr) -> S.Q.eq(E.qeval(p, PT.pcomb(PT.Pr{S.Q{S.Zpos{S.XH{}}, S.XH{}}, S.Q{S.Z0{}, S.XH{}}}, u, v)), E.qeval(p, u)):
  QR.qring_eq([E.qeval(p, u), E.qeval(p, v)], E.QAdd{E.QMul{E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}, E.QVar{0n}}, E.QMul{E.QCst{S.Q{S.Z0{}, S.XH{}}}, E.QVar{1n}}}, E.QVar{0n}, {==})

def pt_first.true(+rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr, +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, hz: {EP.isnil(EP.resp(EL.resid(rows, u))) == True{} : Bool})
  -> SN.InSpan(PT.pcomb(PT.Pr{S.Q{S.Zpos{S.XH{}}, S.XH{}}, S.Q{S.Z0{}, S.XH{}}}, u, v), B):
  in_tr(u, PT.pcomb(PT.Pr{S.Q{S.Zpos{S.XH{}}, S.XH{}}, S.Q{S.Z0{}, S.XH{}}}, u, v), B, SN.in_of_zero(B, rows, u, hr, hz),
    p => pt_first.at(p, u, v))

def pt_second.at(+p: List<&2, S.Q>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr, +L: List<&2, S.Q>, hv: SV.Ident(v, SV.lin(L, EP.qsnoc(B, u))))
  -> S.Q.eq(E.qeval(p, PT.pcomb(PT.Pr{S.Q.neg(PT.lastc(L, B)), S.Q{S.Zpos{S.XH{}}, S.XH{}}}, u, v)), E.qeval(p, SV.lin(L, B))):
  LQ.q_trans(E.qeval(p, PT.pcomb(PT.Pr{S.Q.neg(PT.lastc(L, B)), S.Q{S.Zpos{S.XH{}}, S.XH{}}}, u, v)),
    S.Q.add(S.Q.mul(S.Q.neg(PT.lastc(L, B)), E.qeval(p, u)), S.Q.mul(S.Q{S.Zpos{S.XH{}}, S.XH{}}, S.Q.add(E.qeval(p, SV.lin(L, B)), S.Q.mul(PT.lastc(L, B), E.qeval(p, u))))),
    E.qeval(p, SV.lin(L, B)),
    LQ.q_add_cong_r(S.Q.mul(S.Q.neg(PT.lastc(L, B)), E.qeval(p, u)), S.Q.mul(S.Q{S.Zpos{S.XH{}}, S.XH{}}, E.qeval(p, v)), S.Q.mul(S.Q{S.Zpos{S.XH{}}, S.XH{}}, S.Q.add(E.qeval(p, SV.lin(L, B)), S.Q.mul(PT.lastc(L, B), E.qeval(p, u)))),
      LQ.q_mul_cong_r(S.Q{S.Zpos{S.XH{}}, S.XH{}}, E.qeval(p, v), S.Q.add(E.qeval(p, SV.lin(L, B)), S.Q.mul(PT.lastc(L, B), E.qeval(p, u))),
        LQ.q_trans(E.qeval(p, v), E.qeval(p, SV.lin(L, EP.qsnoc(B, u))), S.Q.add(E.qeval(p, SV.lin(L, B)), S.Q.mul(PT.lastc(L, B), E.qeval(p, u))), hv(p), lin_snoc_last(B, p, L, u)))),
    QR.qring_eq([PT.lastc(L, B), E.qeval(p, u), E.qeval(p, SV.lin(L, B))],
      E.QAdd{E.QMul{E.QNeg{E.QVar{0n}}, E.QVar{1n}}, E.QMul{E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}, E.QAdd{E.QVar{2n}, E.QMul{E.QVar{0n}, E.QVar{1n}}}}},
      E.QVar{2n}, {==}))

def pt_second.mk(+B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr, +L: List<&2, S.Q>, hv: SV.Ident(v, SV.lin(L, EP.qsnoc(B, u))))
  -> SN.InSpan(PT.pcomb(PT.Pr{S.Q.neg(PT.lastc(L, B)), S.Q{S.Zpos{S.XH{}}, S.XH{}}}, u, v), B):
  SN.in_of_ident(PT.pcomb(PT.Pr{S.Q.neg(PT.lastc(L, B)), S.Q{S.Zpos{S.XH{}}, S.XH{}}}, u, v), B, L, p => pt_second.at(p, B, u, v, L, hv))
def pt_second.true(+rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr, +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  +hne: {EP.isnil(EP.resp(EL.resid(rows, u))) == False{} : Bool}, hz: {EP.isnil(EP.resp(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v))) == True{} : Bool})
  -> SN.InSpan(PT.pcomb(PT.Pr{S.Q.neg(PT.lastc(DV.dropls(DV.rescb(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v)), DV.resbt(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v)), v, EP.qsnoc(B, u)), B)), S.Q{S.Zpos{S.XH{}}, S.XH{}}}, u, v), B):
  pt_second.mk(B, u, v, DV.dropls(DV.rescb(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v)), DV.resbt(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v)), v, EP.qsnoc(B, u)),
    DV.derivable(EP.qsnoc(B, u), EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v, EP.new_rinv(B, rows, u, hr, hl, hne), hz))


def pt_second.ok(b2: Bool, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr, +p0: PT.Pr,
  eb2: {b2 == EP.isnil(EP.resp(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v))) : Bool},
  +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat}, +hne: {EP.isnil(EP.resp(EL.resid(rows, u))) == False{} : Bool},
  hp: {PT.pt.second(b2, EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), B, u, v) == Some{p0} : Maybe<&2, PT.Pr>}) -> SN.InSpan(PT.pcomb(p0, u, v), B):
  match b2:
    case True{}:
      %some_inj(PT.Pr{S.Q.neg(PT.lastc(DV.dropls(DV.rescb(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v)), DV.resbt(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v)), v, EP.qsnoc(B, u)), B)), S.Q{S.Zpos{S.XH{}}, S.XH{}}}, p0, hp) : SN.InSpan(PT.pcomb(_, u, v), B)
      pt_second.true(rows, B, u, v, hr, hl, hne, Equal.sym(Bool, True{}, EP.isnil(EP.resp(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v))), eb2))
    case False{}:
      absurd(SN.InSpan(PT.pcomb(p0, u, v), B), none_some(p0, hp))

def pt_first.ok(b: Bool, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr, +p0: PT.Pr,
  eb: {b == EP.isnil(EP.resp(EL.resid(rows, u))) : Bool}, +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hp: {PT.pt.first(b, rows, B, u, v) == Some{p0} : Maybe<&2, PT.Pr>}) -> SN.InSpan(PT.pcomb(p0, u, v), B):
  match b:
    case True{}:
      %some_inj(PT.Pr{S.Q{S.Zpos{S.XH{}}, S.XH{}}, S.Q{S.Z0{}, S.XH{}}}, p0, hp) : SN.InSpan(PT.pcomb(_, u, v), B)
      pt_first.true(rows, B, u, v, hr, Equal.sym(Bool, True{}, EP.isnil(EP.resp(EL.resid(rows, u))), eb))
    case False{}:
      pt_second.ok(EP.isnil(EP.resp(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v))), rows, B, u, v, p0, {==}, hr, hl, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, u))), eb), hp)

# what the test returns combines u and v into the span
def ptest_ok(+rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr, +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat}, +p0: PT.Pr,
  hp: {PT.ptest(rows, B, u, v) == Some{p0} : Maybe<&2, PT.Pr>}) -> SN.InSpan(PT.pcomb(p0, u, v), B):
  pt_first.ok(EP.isnil(EP.resp(EL.resid(rows, u))), rows, B, u, v, p0, {==}, hr, hl, hp)

# Complete
# --------

def len_snoc(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +u: E.QExpr, +x: EL.Row, hl: {EL.rlen(rows) == SV.neqs(B) : Nat}) -> {EL.rlen(EL.rsnoc(rows, x)) == SV.neqs(EP.qsnoc(B, u)) : Nat}:
  %Equal.sym(Nat, SV.neqs(EP.qsnoc(B, u)), 1n+SV.neqs(B), CW.neqs_qsnoc(B, u)) : {EL.rlen(EL.rsnoc(rows, x)) == _ : Nat}
  %Equal.sym(Nat, EL.rlen(EL.rsnoc(rows, x)), 1n+EL.rlen(rows), CW.rlen_rsnoc(rows, x)) : {_ == 1n+SV.neqs(B) : Nat}
  %Equal.sym(Nat, EL.rlen(rows), SV.neqs(B), hl) : {1n+_ == 1n+SV.neqs(B) : Nat}
  {==}

# v from a u + b v, b not 0: v = (1/b)(a u + b v) + (-(a/b) u + 0)
def solve_v.at(+p: List<&2, S.Q>, +a: S.Q, +b: S.Q, +u: E.QExpr, +v: E.QExpr, hb: S.Q.eq(b, S.Q{S.Z0{}, S.XH{}}) -> Empty)
  -> S.Q.eq(E.qeval(p, v), E.qeval(p, E.QAdd{E.QMul{E.QCst{S.Q.inv(b)}, PT.pcomb(PT.Pr{a, b}, u, v)}, E.QAdd{E.QMul{E.QCst{S.Q.neg(S.Q.mul(a, S.Q.inv(b)))}, u}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}})):
  LQ.q_trans(E.qeval(p, v), S.Q.mul(S.Q.mul(b, S.Q.inv(b)), E.qeval(p, v)), E.qeval(p, E.QAdd{E.QMul{E.QCst{S.Q.inv(b)}, PT.pcomb(PT.Pr{a, b}, u, v)}, E.QAdd{E.QMul{E.QCst{S.Q.neg(S.Q.mul(a, S.Q.inv(b)))}, u}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}}),
    LQ.q_trans(E.qeval(p, v), S.Q.mul(S.Q{S.Zpos{S.XH{}}, S.XH{}}, E.qeval(p, v)), S.Q.mul(S.Q.mul(b, S.Q.inv(b)), E.qeval(p, v)),
      QR.qring_eq([E.qeval(p, v)], E.QVar{0n}, E.QMul{E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}, E.QVar{0n}}, {==}),
      LQ.q_mul_cong_l(S.Q{S.Zpos{S.XH{}}, S.XH{}}, S.Q.mul(b, S.Q.inv(b)), E.qeval(p, v), LQ.q_sym(S.Q.mul(b, S.Q.inv(b)), S.Q{S.Zpos{S.XH{}}, S.XH{}}, LQ.q_mul_inv(b, hb)))),
    QR.qring_eq([b, S.Q.inv(b), a, E.qeval(p, u), E.qeval(p, v)],
      E.QMul{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QVar{4n}},
      E.QAdd{E.QMul{E.QVar{1n}, E.QAdd{E.QMul{E.QVar{2n}, E.QVar{3n}}, E.QMul{E.QVar{0n}, E.QVar{4n}}}}, E.QAdd{E.QMul{E.QNeg{E.QMul{E.QVar{2n}, E.QVar{1n}}}, E.QVar{3n}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}},
      {==}))

def pt_second.some(b2: Bool, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr,
  eb2: {b2 == EP.isnil(EP.resp(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v))) : Bool}, hz: {EP.isnil(EP.resp(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v))) == True{} : Bool})
  -> {is_some(PT.pt.second(b2, EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), B, u, v)) == True{} : Bool}:
  %Equal.sym(Bool, b2, EP.isnil(EP.resp(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v))), eb2) : {is_some(PT.pt.second(_, EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), B, u, v)) == True{} : Bool}
  %Equal.sym(Bool, EP.isnil(EP.resp(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v))), True{}, hz) : {is_some(PT.pt.second(_, EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), B, u, v)) == True{} : Bool}
  {==}

def pt_first.some_b(b: Bool, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr, +a: S.Q, +bb: S.Q,
  eb: {b == EP.isnil(EP.resp(EL.resid(rows, u))) : Bool}, +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hb: S.Q.eq(bb, S.Q{S.Z0{}, S.XH{}}) -> Empty, +hi: SN.InSpan(PT.pcomb(PT.Pr{a, bb}, u, v), B))
  -> {is_some(PT.pt.first(b, rows, B, u, v)) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      pt_second.some(EP.isnil(EP.resp(EL.resid(EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v))), rows, B, u, v, {==},
        SN.zero_of_in(EP.qsnoc(B, u), EL.rsnoc(rows, EL.row_of(EL.resid(rows, u))), v,
          EP.new_rinv(B, rows, u, hr, hl, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, u))), eb)),
          len_snoc(B, rows, u, EL.row_of(EL.resid(rows, u)), hl),
          in_tr(E.QAdd{E.QMul{E.QCst{S.Q.inv(bb)}, PT.pcomb(PT.Pr{a, bb}, u, v)}, E.QAdd{E.QMul{E.QCst{S.Q.neg(S.Q.mul(a, S.Q.inv(bb)))}, u}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}}, v, EP.qsnoc(B, u),
            SN.in_comb(S.Q.inv(bb), PT.pcomb(PT.Pr{a, bb}, u, v), E.QAdd{E.QMul{E.QCst{S.Q.neg(S.Q.mul(a, S.Q.inv(bb)))}, u}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, EP.qsnoc(B, u),
              SN.in_snoc(PT.pcomb(PT.Pr{a, bb}, u, v), B, u, hi),
              SN.in_comb(S.Q.neg(S.Q.mul(a, S.Q.inv(bb))), u, E.QCst{S.Q{S.Z0{}, S.XH{}}}, EP.qsnoc(B, u), SN.in_last(B, u), SN.in_zero(EP.qsnoc(B, u)))),
            p => solve_v.at(p, a, bb, u, v, hb))))

# a u + b v in the span with b not 0: the test finds something
def ptest_some_b(+rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr, +a: S.Q, +bb: S.Q, +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  hb: S.Q.eq(bb, S.Q{S.Z0{}, S.XH{}}) -> Empty, +hi: SN.InSpan(PT.pcomb(PT.Pr{a, bb}, u, v), B)) -> {is_some(PT.ptest(rows, B, u, v)) == True{} : Bool}:
  pt_first.some_b(EP.isnil(EP.resp(EL.resid(rows, u))), rows, B, u, v, a, bb, {==}, hr, hl, hb, hi)

# u from a u + b v with b = 0, a not 0: u = (1/a)(a u + b v) + 0
def solve_u.at(+p: List<&2, S.Q>, +a: S.Q, +b: S.Q, +u: E.QExpr, +v: E.QExpr, ha: S.Q.eq(a, S.Q{S.Z0{}, S.XH{}}) -> Empty, hb: S.Q.eq(b, S.Q{S.Z0{}, S.XH{}}))
  -> S.Q.eq(E.qeval(p, u), E.qeval(p, E.QAdd{E.QMul{E.QCst{S.Q.inv(a)}, PT.pcomb(PT.Pr{a, b}, u, v)}, E.QCst{S.Q{S.Z0{}, S.XH{}}}})):
  LQ.q_trans(E.qeval(p, u), S.Q.mul(S.Q.mul(a, S.Q.inv(a)), E.qeval(p, u)), E.qeval(p, E.QAdd{E.QMul{E.QCst{S.Q.inv(a)}, PT.pcomb(PT.Pr{a, b}, u, v)}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}),
    LQ.q_trans(E.qeval(p, u), S.Q.mul(S.Q{S.Zpos{S.XH{}}, S.XH{}}, E.qeval(p, u)), S.Q.mul(S.Q.mul(a, S.Q.inv(a)), E.qeval(p, u)),
      QR.qring_eq([E.qeval(p, u)], E.QVar{0n}, E.QMul{E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}, E.QVar{0n}}, {==}),
      LQ.q_mul_cong_l(S.Q{S.Zpos{S.XH{}}, S.XH{}}, S.Q.mul(a, S.Q.inv(a)), E.qeval(p, u), LQ.q_sym(S.Q.mul(a, S.Q.inv(a)), S.Q{S.Zpos{S.XH{}}, S.XH{}}, LQ.q_mul_inv(a, ha)))),
    LQ.q_trans(S.Q.mul(S.Q.mul(a, S.Q.inv(a)), E.qeval(p, u)),
      S.Q.add(S.Q.mul(S.Q.inv(a), S.Q.add(S.Q.mul(a, E.qeval(p, u)), S.Q.mul(S.Q{S.Z0{}, S.XH{}}, E.qeval(p, v)))), S.Q{S.Z0{}, S.XH{}}),
      E.qeval(p, E.QAdd{E.QMul{E.QCst{S.Q.inv(a)}, PT.pcomb(PT.Pr{a, b}, u, v)}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}),
      QR.qring_eq([a, S.Q.inv(a), E.qeval(p, u), E.qeval(p, v)],
        E.QMul{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QVar{2n}},
        E.QAdd{E.QMul{E.QVar{1n}, E.QAdd{E.QMul{E.QVar{0n}, E.QVar{2n}}, E.QMul{E.QCst{S.Q{S.Z0{}, S.XH{}}}, E.QVar{3n}}}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, {==}),
      LQ.q_add_cong_l(S.Q.mul(S.Q.inv(a), S.Q.add(S.Q.mul(a, E.qeval(p, u)), S.Q.mul(S.Q{S.Z0{}, S.XH{}}, E.qeval(p, v)))), S.Q.mul(S.Q.inv(a), S.Q.add(S.Q.mul(a, E.qeval(p, u)), S.Q.mul(b, E.qeval(p, v)))), S.Q{S.Z0{}, S.XH{}},
        LQ.q_mul_cong_r(S.Q.inv(a), S.Q.add(S.Q.mul(a, E.qeval(p, u)), S.Q.mul(S.Q{S.Z0{}, S.XH{}}, E.qeval(p, v))), S.Q.add(S.Q.mul(a, E.qeval(p, u)), S.Q.mul(b, E.qeval(p, v))),
          LQ.q_add_cong_r(S.Q.mul(a, E.qeval(p, u)), S.Q.mul(S.Q{S.Z0{}, S.XH{}}, E.qeval(p, v)), S.Q.mul(b, E.qeval(p, v)),
            LQ.q_mul_cong_l(S.Q{S.Z0{}, S.XH{}}, b, E.qeval(p, v), LQ.q_sym(b, S.Q{S.Z0{}, S.XH{}}, hb)))))))

def pt_first.some_a(+rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr, hz: {EP.isnil(EP.resp(EL.resid(rows, u))) == True{} : Bool})
  -> {is_some(PT.ptest(rows, B, u, v)) == True{} : Bool}:
  %Equal.sym(Bool, EP.isnil(EP.resp(EL.resid(rows, u))), True{}, hz) : {is_some(PT.pt.first(_, rows, B, u, v)) == True{} : Bool}
  {==}

# a u + b v in the span with b = 0 and a not 0: u is in it, and the test
# finds (1, 0)
def ptest_some_a(+rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +u: E.QExpr, +v: E.QExpr, +a: S.Q, +bb: S.Q, +hr: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat},
  ha: S.Q.eq(a, S.Q{S.Z0{}, S.XH{}}) -> Empty, hb: S.Q.eq(bb, S.Q{S.Z0{}, S.XH{}}), +hi: SN.InSpan(PT.pcomb(PT.Pr{a, bb}, u, v), B)) -> {is_some(PT.ptest(rows, B, u, v)) == True{} : Bool}:
  pt_first.some_a(rows, B, u, v,
    SN.zero_of_in(B, rows, u, hr, hl,
      in_tr(E.QAdd{E.QMul{E.QCst{S.Q.inv(a)}, PT.pcomb(PT.Pr{a, bb}, u, v)}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, u, B,
        SN.in_comb(S.Q.inv(a), PT.pcomb(PT.Pr{a, bb}, u, v), E.QCst{S.Q{S.Z0{}, S.XH{}}}, B, hi, SN.in_zero(B)),
        p => solve_u.at(p, a, bb, u, v, ha, hb))))
