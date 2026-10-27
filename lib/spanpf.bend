# bend-cad: spans of polynomials, for the direction layer's closure
# (PLAN-sk13b B3). InSpan(e, B): some constant combination of B is e,
# carried in the normalizer's reusable form (an Ident is a function, which
# Bend's affine types let one use only once; lib/identpf.bend relates the
# two). Membership is decided exactly by sk-13a's elimination: a zero
# residual gives it (derivable), and a nonzero one rules it out (indep).
# A span only grows when a generator is appended. Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ./elim.bend as EL
import ./elimpf.bend as EP
import ./drvpf.bend as DV
import ./indpf.bend as IN
import ./qnorm.bend as QN
import ./identpf.bend as ID
import ./q.bend as LQ
import ./qring.bend as QR
import ./qalg.bend as QA

def absurd(-A: Type, x: Empty) -> A:
  match x:

# some constant combination of B is e (reusable)
def InSpan(+e: E.QExpr, +B: List<&2, E.QExpr>) -> Data:
  Sigma<&2, &2, List<&2, S.Q>, ls => {QN.qzero(E.QSub{e, SV.lin(ls, B)}) == True{} : Bool}>

def in_ls(+e: E.QExpr, +B: List<&2, E.QExpr>, h: InSpan(e, B)) -> List<&2, S.Q>:
  (ls, q) = h
  ls

def in_qz(+e: E.QExpr, +B: List<&2, E.QExpr>, h: InSpan(e, B)) -> {QN.qzero(E.QSub{e, SV.lin(in_ls(e, B, h), B)}) == True{} : Bool}:
  (ls, q) = h
  q

def in_ident(+e: E.QExpr, +B: List<&2, E.QExpr>, +h: InSpan(e, B)) -> SV.Ident(e, SV.lin(in_ls(e, B, h), B)):
  ID.ident_ok(e, SV.lin(in_ls(e, B, h), B), in_qz(e, B, h))

def in_of_ident(+e: E.QExpr, +B: List<&2, E.QExpr>, +ls: List<&2, S.Q>, h: SV.Ident(e, SV.lin(ls, B))) -> InSpan(e, B):
  (ls, ID.qzero_ident(e, SV.lin(ls, B), h))

# Deciding membership
# -------------------

# a zero residual: e is in the span
def in_of_zero(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, +h: {EP.rinv(B, rows, 0n) == True{} : Bool}, hz: {EP.isnil(EP.resp(EL.resid(rows, e))) == True{} : Bool}) -> InSpan(e, B):
  in_of_ident(e, B, DV.dropls(DV.rescb(EL.resid(rows, e)), DV.resbt(EL.resid(rows, e)), e, B), DV.derivable(B, rows, e, h, hz))

def zero_of_in.pick(b: Bool, +B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, eb: {b == EP.isnil(EP.resp(EL.resid(rows, e))) : Bool},
  +h: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat}, +hi: InSpan(e, B)) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      absurd({False{} == True{} : Bool}, IN.indep(B, rows, e, h, hl, Equal.sym(Bool, False{}, EP.isnil(EP.resp(EL.resid(rows, e))), eb))(in_ls(e, B, hi), in_ident(e, B, hi)))

# in the span: the residual is 0
def zero_of_in(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, +h: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat}, +hi: InSpan(e, B)) -> {EP.isnil(EP.resp(EL.resid(rows, e))) == True{} : Bool}:
  zero_of_in.pick(EP.isnil(EP.resp(EL.resid(rows, e))), B, rows, e, {==}, h, hl, hi)

# Growing the span
# ----------------

# ls cut to B's length
def ltrunc(ls: List<&2, S.Q>, B: List<&2, E.QExpr>) -> List<&2, S.Q>:
  match ls B:
    case Con{l, lt} Con{b, bt}:
      Con{l, ltrunc(lt, bt)}
    case Nil{} B:
      Nil{}
    case Con{l, lt} Nil{}:
      Nil{}

def lin_trunc(ls: List<&2, S.Q>, B: List<&2, E.QExpr>) -> {SV.lin(ltrunc(ls, B), B) == SV.lin(ls, B) : E.QExpr}:
  match ls B:
    case Con{+l, +lt} Con{+b, +bt}:
      %Equal.sym(E.QExpr, SV.lin(ltrunc(lt, bt), bt), SV.lin(lt, bt), lin_trunc(lt, bt)) : {E.QAdd{E.QMul{E.QCst{l}, b}, _} == SV.lin(Con{l, lt}, Con{b, bt}) : E.QExpr}
      {==}
    case Nil{} B:
      {==}
    case Con{l, lt} Nil{}:
      {==}

def lin_trunc_snoc(ls: List<&2, S.Q>, B: List<&2, E.QExpr>, +x: E.QExpr) -> {SV.lin(ltrunc(ls, B), EP.qsnoc(B, x)) == SV.lin(ltrunc(ls, B), B) : E.QExpr}:
  match ls B:
    case Con{+l, +lt} Con{+b, +bt}:
      %Equal.sym(E.QExpr, SV.lin(ltrunc(lt, bt), EP.qsnoc(bt, x)), SV.lin(ltrunc(lt, bt), bt), lin_trunc_snoc(lt, bt, x)) : {E.QAdd{E.QMul{E.QCst{l}, b}, _} == SV.lin(ltrunc(Con{l, lt}, Con{b, bt}), Con{b, bt}) : E.QExpr}
      {==}
    case Nil{} B:
      {==}
    case Con{l, lt} Nil{}:
      {==}

def in_snoc.qz(+e: E.QExpr, +B: List<&2, E.QExpr>, +x: E.QExpr, +ls: List<&2, S.Q>, q: {QN.qzero(E.QSub{e, SV.lin(ls, B)}) == True{} : Bool}) -> {QN.qzero(E.QSub{e, SV.lin(ltrunc(ls, B), EP.qsnoc(B, x))}) == True{} : Bool}:
  %Equal.sym(E.QExpr, SV.lin(ltrunc(ls, B), EP.qsnoc(B, x)), SV.lin(ltrunc(ls, B), B), lin_trunc_snoc(ls, B, x)) : {QN.qzero(E.QSub{e, _}) == True{} : Bool}
  %Equal.sym(E.QExpr, SV.lin(ltrunc(ls, B), B), SV.lin(ls, B), lin_trunc(ls, B)) : {QN.qzero(E.QSub{e, _}) == True{} : Bool}
  q

def in_snoc.mk(+e: E.QExpr, +B: List<&2, E.QExpr>, +x: E.QExpr, +ls: List<&2, S.Q>, q: {QN.qzero(E.QSub{e, SV.lin(ls, B)}) == True{} : Bool}) -> InSpan(e, EP.qsnoc(B, x)):
  (ltrunc(ls, B), in_snoc.qz(e, B, x, ls, q))

# a span only grows
def in_snoc(+e: E.QExpr, +B: List<&2, E.QExpr>, +x: E.QExpr, h: InSpan(e, B)) -> InSpan(e, EP.qsnoc(B, x)):
  (+ls, q) = h
  in_snoc.mk(e, B, x, ls, q)

def unit_at(B: List<&2, E.QExpr>) -> List<&2, S.Q>:
  match B:
    case Nil{}:
      [S.Q{S.Zpos{S.XH{}}, S.XH{}}]
    case Con{b, bt}:
      Con{S.Q{S.Z0{}, S.XH{}}, unit_at(bt)}

# x = 1 x (+ 0 b for each earlier b), at each point
def in_last.at(+p: List<&2, S.Q>, B: List<&2, E.QExpr>, +x: E.QExpr) -> S.Q.eq(E.qeval(p, x), E.qeval(p, SV.lin(unit_at(B), EP.qsnoc(B, x)))):
  match B:
    case Nil{}:
      QR.qring_eq([E.qeval(p, x)], E.QVar{0n}, E.QAdd{E.QMul{E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}, E.QVar{0n}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, {==})
    case Con{+b, +bt}:
      LQ.q_trans(E.qeval(p, x), S.Q.add(S.Q.mul(S.Q{S.Z0{}, S.XH{}}, E.qeval(p, b)), E.qeval(p, x)), E.qeval(p, SV.lin(unit_at(Con{b, bt}), EP.qsnoc(Con{b, bt}, x))),
        QR.qring_eq([E.qeval(p, x), E.qeval(p, b)], E.QVar{0n}, E.QAdd{E.QMul{E.QCst{S.Q{S.Z0{}, S.XH{}}}, E.QVar{1n}}, E.QVar{0n}}, {==}),
        LQ.q_add_cong_r(S.Q.mul(S.Q{S.Z0{}, S.XH{}}, E.qeval(p, b)), E.qeval(p, x), E.qeval(p, SV.lin(unit_at(bt), EP.qsnoc(bt, x))), in_last.at(p, bt, x)))

def in_last.id(B: List<&2, E.QExpr>, +x: E.QExpr) -> SV.Ident(x, SV.lin(unit_at(B), EP.qsnoc(B, x))):
  p => in_last.at(p, B, x)

# every generator is in its span
def in_last(+B: List<&2, E.QExpr>, +x: E.QExpr) -> InSpan(x, EP.qsnoc(B, x)):
  in_of_ident(x, EP.qsnoc(B, x), unit_at(B), in_last.id(B, x))

# 0, ..., 0, 1

# Combining coefficients
# ----------------------

def qhd(ls: List<&2, S.Q>) -> S.Q:
  match ls:
    case Nil{}:
      S.Q{S.Z0{}, S.XH{}}
    case Con{l, lt}:
      l

def qtl(ls: List<&2, S.Q>) -> List<&2, S.Q>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, lt}:
      lt

def lin_nil(ls: List<&2, S.Q>) -> {SV.lin(ls, Nil{}) == E.QCst{S.Q{S.Z0{}, S.XH{}}} : E.QExpr}:
  match ls:
    case Nil{}:
      {==}
    case Con{l, lt}:
      {==}

# lin on a nonempty basis, head first, a missing coefficient read as 0
def lin_ht(+p: List<&2, S.Q>, ls: List<&2, S.Q>, +b: E.QExpr, +bt: List<&2, E.QExpr>) -> S.Q.eq(E.qeval(p, SV.lin(ls, Con{b, bt})), S.Q.add(S.Q.mul(qhd(ls), E.qeval(p, b)), E.qeval(p, SV.lin(qtl(ls), bt)))):
  match ls:
    case Nil{}:
      QR.qring_eq([E.qeval(p, b)], E.QCst{S.Q{S.Z0{}, S.XH{}}}, E.QAdd{E.QMul{E.QCst{S.Q{S.Z0{}, S.XH{}}}, E.QVar{0n}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, {==})
    case Con{+l, +lt}:
      LQ.q_refl(E.qeval(p, SV.lin(Con{l, lt}, Con{b, bt})))

# l ls1 + ls2, entry by entry along B
def lc(B: List<&2, E.QExpr>, +l: S.Q, +ls1: List<&2, S.Q>, +ls2: List<&2, S.Q>) -> List<&2, S.Q>:
  match B:
    case Nil{}:
      Nil{}
    case Con{b, bt}:
      Con{S.Q.add(S.Q.mul(l, qhd(ls1)), qhd(ls2)), lc(bt, l, qtl(ls1), qtl(ls2))}

# (l h1 + h2) b + (l r1 + r2) = l (h1 b + r1) + (h2 b + r2), as a chain
def lc_step(+l: S.Q, +h1: S.Q, +h2: S.Q, +b: S.Q, +r1: S.Q, +r2: S.Q)
  -> S.Q.eq(S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(l, h1), h2), b), S.Q.add(S.Q.mul(l, r1), r2)), S.Q.add(S.Q.mul(l, S.Q.add(S.Q.mul(h1, b), r1)), S.Q.add(S.Q.mul(h2, b), r2))):
  LQ.q_trans(S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(l, h1), h2), b), S.Q.add(S.Q.mul(l, r1), r2)),
    S.Q.add(S.Q.add(S.Q.mul(l, S.Q.mul(h1, b)), S.Q.mul(h2, b)), S.Q.add(S.Q.mul(l, r1), r2)),
    S.Q.add(S.Q.mul(l, S.Q.add(S.Q.mul(h1, b), r1)), S.Q.add(S.Q.mul(h2, b), r2)),
    LQ.q_add_cong_l(S.Q.mul(S.Q.add(S.Q.mul(l, h1), h2), b), S.Q.add(S.Q.mul(l, S.Q.mul(h1, b)), S.Q.mul(h2, b)), S.Q.add(S.Q.mul(l, r1), r2),
      LQ.q_trans(S.Q.mul(S.Q.add(S.Q.mul(l, h1), h2), b), S.Q.add(S.Q.mul(S.Q.mul(l, h1), b), S.Q.mul(h2, b)), S.Q.add(S.Q.mul(l, S.Q.mul(h1, b)), S.Q.mul(h2, b)),
        QA.rdist(S.Q.mul(l, h1), h2, b), LQ.q_add_cong_l(S.Q.mul(S.Q.mul(l, h1), b), S.Q.mul(l, S.Q.mul(h1, b)), S.Q.mul(h2, b), QA.massoc(l, h1, b)))),
    LQ.q_trans(S.Q.add(S.Q.add(S.Q.mul(l, S.Q.mul(h1, b)), S.Q.mul(h2, b)), S.Q.add(S.Q.mul(l, r1), r2)),
      S.Q.add(S.Q.add(S.Q.mul(l, S.Q.mul(h1, b)), S.Q.mul(l, r1)), S.Q.add(S.Q.mul(h2, b), r2)),
      S.Q.add(S.Q.mul(l, S.Q.add(S.Q.mul(h1, b), r1)), S.Q.add(S.Q.mul(h2, b), r2)),
      QA.m4(S.Q.mul(l, S.Q.mul(h1, b)), S.Q.mul(h2, b), S.Q.mul(l, r1), r2),
      LQ.q_add_cong_l(S.Q.add(S.Q.mul(l, S.Q.mul(h1, b)), S.Q.mul(l, r1)), S.Q.mul(l, S.Q.add(S.Q.mul(h1, b), r1)), S.Q.add(S.Q.mul(h2, b), r2),
        LQ.q_sym(S.Q.mul(l, S.Q.add(S.Q.mul(h1, b), r1)), S.Q.add(S.Q.mul(l, S.Q.mul(h1, b)), S.Q.mul(l, r1)), QA.ldist(l, S.Q.mul(h1, b), r1)))))

def lin_lc.go(+p: List<&2, S.Q>, +l: S.Q, +ls1: List<&2, S.Q>, +ls2: List<&2, S.Q>, +b: E.QExpr, +bt: List<&2, E.QExpr>,
  ih: S.Q.eq(E.qeval(p, SV.lin(lc(bt, l, qtl(ls1), qtl(ls2)), bt)), S.Q.add(S.Q.mul(l, E.qeval(p, SV.lin(qtl(ls1), bt))), E.qeval(p, SV.lin(qtl(ls2), bt)))),
  h1: S.Q.eq(E.qeval(p, SV.lin(ls1, Con{b, bt})), S.Q.add(S.Q.mul(qhd(ls1), E.qeval(p, b)), E.qeval(p, SV.lin(qtl(ls1), bt)))),
  h2: S.Q.eq(E.qeval(p, SV.lin(ls2, Con{b, bt})), S.Q.add(S.Q.mul(qhd(ls2), E.qeval(p, b)), E.qeval(p, SV.lin(qtl(ls2), bt)))))
  -> S.Q.eq(E.qeval(p, SV.lin(lc(Con{b, bt}, l, ls1, ls2), Con{b, bt})), S.Q.add(S.Q.mul(l, E.qeval(p, SV.lin(ls1, Con{b, bt}))), E.qeval(p, SV.lin(ls2, Con{b, bt})))):
  LQ.q_trans(E.qeval(p, SV.lin(lc(Con{b, bt}, l, ls1, ls2), Con{b, bt})),
    S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(l, qhd(ls1)), qhd(ls2)), E.qeval(p, b)), S.Q.add(S.Q.mul(l, E.qeval(p, SV.lin(qtl(ls1), bt))), E.qeval(p, SV.lin(qtl(ls2), bt)))),
    S.Q.add(S.Q.mul(l, E.qeval(p, SV.lin(ls1, Con{b, bt}))), E.qeval(p, SV.lin(ls2, Con{b, bt}))),
    LQ.q_add_cong_r(S.Q.mul(S.Q.add(S.Q.mul(l, qhd(ls1)), qhd(ls2)), E.qeval(p, b)), E.qeval(p, SV.lin(lc(bt, l, qtl(ls1), qtl(ls2)), bt)), S.Q.add(S.Q.mul(l, E.qeval(p, SV.lin(qtl(ls1), bt))), E.qeval(p, SV.lin(qtl(ls2), bt))), ih),
    LQ.q_trans(S.Q.add(S.Q.mul(S.Q.add(S.Q.mul(l, qhd(ls1)), qhd(ls2)), E.qeval(p, b)), S.Q.add(S.Q.mul(l, E.qeval(p, SV.lin(qtl(ls1), bt))), E.qeval(p, SV.lin(qtl(ls2), bt)))),
      S.Q.add(S.Q.mul(l, S.Q.add(S.Q.mul(qhd(ls1), E.qeval(p, b)), E.qeval(p, SV.lin(qtl(ls1), bt)))), S.Q.add(S.Q.mul(qhd(ls2), E.qeval(p, b)), E.qeval(p, SV.lin(qtl(ls2), bt)))),
      S.Q.add(S.Q.mul(l, E.qeval(p, SV.lin(ls1, Con{b, bt}))), E.qeval(p, SV.lin(ls2, Con{b, bt}))),
      lc_step(l, qhd(ls1), qhd(ls2), E.qeval(p, b), E.qeval(p, SV.lin(qtl(ls1), bt)), E.qeval(p, SV.lin(qtl(ls2), bt))),
      LQ.q_trans(S.Q.add(S.Q.mul(l, S.Q.add(S.Q.mul(qhd(ls1), E.qeval(p, b)), E.qeval(p, SV.lin(qtl(ls1), bt)))), S.Q.add(S.Q.mul(qhd(ls2), E.qeval(p, b)), E.qeval(p, SV.lin(qtl(ls2), bt)))),
        S.Q.add(S.Q.mul(l, E.qeval(p, SV.lin(ls1, Con{b, bt}))), S.Q.add(S.Q.mul(qhd(ls2), E.qeval(p, b)), E.qeval(p, SV.lin(qtl(ls2), bt)))),
        S.Q.add(S.Q.mul(l, E.qeval(p, SV.lin(ls1, Con{b, bt}))), E.qeval(p, SV.lin(ls2, Con{b, bt}))),
        LQ.q_add_cong_l(S.Q.mul(l, S.Q.add(S.Q.mul(qhd(ls1), E.qeval(p, b)), E.qeval(p, SV.lin(qtl(ls1), bt)))), S.Q.mul(l, E.qeval(p, SV.lin(ls1, Con{b, bt}))), S.Q.add(S.Q.mul(qhd(ls2), E.qeval(p, b)), E.qeval(p, SV.lin(qtl(ls2), bt))),
          LQ.q_mul_cong_r(l, S.Q.add(S.Q.mul(qhd(ls1), E.qeval(p, b)), E.qeval(p, SV.lin(qtl(ls1), bt))), E.qeval(p, SV.lin(ls1, Con{b, bt})), LQ.q_sym(E.qeval(p, SV.lin(ls1, Con{b, bt})), S.Q.add(S.Q.mul(qhd(ls1), E.qeval(p, b)), E.qeval(p, SV.lin(qtl(ls1), bt))), h1))),
        LQ.q_add_cong_r(S.Q.mul(l, E.qeval(p, SV.lin(ls1, Con{b, bt}))), S.Q.add(S.Q.mul(qhd(ls2), E.qeval(p, b)), E.qeval(p, SV.lin(qtl(ls2), bt))), E.qeval(p, SV.lin(ls2, Con{b, bt})), LQ.q_sym(E.qeval(p, SV.lin(ls2, Con{b, bt})), S.Q.add(S.Q.mul(qhd(ls2), E.qeval(p, b)), E.qeval(p, SV.lin(qtl(ls2), bt))), h2)))))

def lin_lc(B: List<&2, E.QExpr>, +p: List<&2, S.Q>, +l: S.Q, +ls1: List<&2, S.Q>, +ls2: List<&2, S.Q>)
  -> S.Q.eq(E.qeval(p, SV.lin(lc(B, l, ls1, ls2), B)), S.Q.add(S.Q.mul(l, E.qeval(p, SV.lin(ls1, B))), E.qeval(p, SV.lin(ls2, B)))):
  match B:
    case Nil{}:
      %Equal.sym(E.QExpr, SV.lin(ls1, Nil{}), E.QCst{S.Q{S.Z0{}, S.XH{}}}, lin_nil(ls1)) : S.Q.eq(E.qeval(p, SV.lin(lc(Nil{}, l, ls1, ls2), Nil{})), S.Q.add(S.Q.mul(l, E.qeval(p, _)), E.qeval(p, SV.lin(ls2, Nil{}))))
      %Equal.sym(E.QExpr, SV.lin(ls2, Nil{}), E.QCst{S.Q{S.Z0{}, S.XH{}}}, lin_nil(ls2)) : S.Q.eq(E.qeval(p, SV.lin(lc(Nil{}, l, ls1, ls2), Nil{})), S.Q.add(S.Q.mul(l, E.qeval(p, E.QCst{S.Q{S.Z0{}, S.XH{}}})), E.qeval(p, _)))
      QR.qring_eq([l], E.QCst{S.Q{S.Z0{}, S.XH{}}}, E.QAdd{E.QMul{E.QVar{0n}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, {==})
    case Con{+b, +bt}:
      lin_lc.go(p, l, ls1, ls2, b, bt, lin_lc(bt, p, l, qtl(ls1), qtl(ls2)), lin_ht(p, ls1, b, bt), lin_ht(p, ls2, b, bt))


# spans are closed under l e1 + e2
def in_comb.at(+p: List<&2, S.Q>, +l: S.Q, +e1: E.QExpr, +e2: E.QExpr, +B: List<&2, E.QExpr>, +ls1: List<&2, S.Q>, +ls2: List<&2, S.Q>,
  i1: SV.Ident(e1, SV.lin(ls1, B)), i2: SV.Ident(e2, SV.lin(ls2, B))) -> S.Q.eq(E.qeval(p, E.QAdd{E.QMul{E.QCst{l}, e1}, e2}), E.qeval(p, SV.lin(lc(B, l, ls1, ls2), B))):
  LQ.q_trans(E.qeval(p, E.QAdd{E.QMul{E.QCst{l}, e1}, e2}), S.Q.add(S.Q.mul(l, E.qeval(p, SV.lin(ls1, B))), E.qeval(p, SV.lin(ls2, B))), E.qeval(p, SV.lin(lc(B, l, ls1, ls2), B)),
    LQ.q_trans(S.Q.add(S.Q.mul(l, E.qeval(p, e1)), E.qeval(p, e2)), S.Q.add(S.Q.mul(l, E.qeval(p, SV.lin(ls1, B))), E.qeval(p, e2)), S.Q.add(S.Q.mul(l, E.qeval(p, SV.lin(ls1, B))), E.qeval(p, SV.lin(ls2, B))),
      LQ.q_add_cong_l(S.Q.mul(l, E.qeval(p, e1)), S.Q.mul(l, E.qeval(p, SV.lin(ls1, B))), E.qeval(p, e2), LQ.q_mul_cong_r(l, E.qeval(p, e1), E.qeval(p, SV.lin(ls1, B)), i1(p))),
      LQ.q_add_cong_r(S.Q.mul(l, E.qeval(p, SV.lin(ls1, B))), E.qeval(p, e2), E.qeval(p, SV.lin(ls2, B)), i2(p))),
    LQ.q_sym(E.qeval(p, SV.lin(lc(B, l, ls1, ls2), B)), S.Q.add(S.Q.mul(l, E.qeval(p, SV.lin(ls1, B))), E.qeval(p, SV.lin(ls2, B))), lin_lc(B, p, l, ls1, ls2)))

def in_comb(+l: S.Q, +e1: E.QExpr, +e2: E.QExpr, +B: List<&2, E.QExpr>, +h1: InSpan(e1, B), +h2: InSpan(e2, B)) -> InSpan(E.QAdd{E.QMul{E.QCst{l}, e1}, e2}, B):
  in_of_ident(E.QAdd{E.QMul{E.QCst{l}, e1}, e2}, B, lc(B, l, in_ls(e1, B, h1), in_ls(e2, B, h2)),
    p => in_comb.at(p, l, e1, e2, B, in_ls(e1, B, h1), in_ls(e2, B, h2), in_ident(e1, B, h1), in_ident(e2, B, h2)))

# 0 is in every span
def in_zero(+B: List<&2, E.QExpr>) -> InSpan(E.QCst{S.Q{S.Z0{}, S.XH{}}}, B):
  (Nil{}, {==})
