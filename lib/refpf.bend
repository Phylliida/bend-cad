# bend-cad: lib/refute.bend's refutations are refutations (PLAN-sk13a S3).
# Whatever certificate refute(es, ss) returns satisfies the spec's
# Refutes0(es, ss, ls, ms, k): the multipliers have the right lengths and
# signs, and l . es + m . ss = k as polynomials, with k < 0, or k = 0 and a
# strict side weighted positively.
# - A constant row c of the equations: its recorded combination is c, so
#   -sgn(c) times it is -|c|.
# - The simplex's Unsat: the multipliers mu (lib/unsatpf.bend) cancel every
#   monomial left after reducing the sides against the rows; what the
#   reduction subtracted is the basis' combination, read back over es.
# Coefficients are compared through an ordered field, as in
# lib/drvpf.bend. Proofs only.
#
# Generated from tools/drafts/refpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./nat.bend as LN
import ./zring.bend as R
import ./zlaws.bend as ZL
import ./zord.bend as ZO
import ./fring.bend as FR
import ./ford.bend as FO
import ./qemb.bend as QE
import ./qfield.bend as QF
import ./lqfield.bend as LQF
import ./qnorm.bend as QN
import ./natring.bend as NR
import ./redpoly.bend as RP
import ./identpf.bend as ID
import ./elim.bend as EL
import ./coefpf.bend as CF
import ./elimpf.bend as EP
import ./drvpf.bend as DR
import ./simplex.bend as SX
import ./simppf.bend as SP
import ./runpf.bend as RN
import ./termpf.bend as TP
import ./refute.bend as RF
import ./unsatpf.bend as UN
import ./listpf.bend as LI
import ./lexpf.bend as LX

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Rationals in a field
# --------------------

def ofq_qz(~F: O.OField, +x: S.Z) -> {O.ofq(~F, RF.qz(x)) == O.ofz(~F, x) : O.C(F)}:
  %Equal.sym(O.C(F), O.inv(F, O.ofp(~F, S.XH{})), O.one(F), SP.inv1(~F)) : {O.mul(F, O.ofz(~F, x), _) == O.ofz(~F, x) : O.C(F)}
  FR.fring_eq(~F, [O.ofz(~F, x)], E.ZMul{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{0n}, {==})

# a constant's coefficients: K at 1, 0 elsewhere
def cst_coef(~F: O.OField, +K: S.Z, m: List<&2, Nat>) -> {O.ofq(~F, CF.coef(E.QCst{RF.qz(K)}, m)) == O.ofz(~F, EL.ifz(RF.iscst(m), K)) : O.C(F)}:
  match m:
    case Nil{}:
      %CF.coef_cst_one(RF.qz(K)) : {O.ofq(~F, _) == O.ofz(~F, K) : O.C(F)}
      ofq_qz(~F, K)
    case Con{+v, +vs}:
      Equal.trans(O.C(F), O.ofq(~F, CF.coef(E.QCst{RF.qz(K)}, Con{v, vs})), O.ofq(~F, SV.qzero()), O.zero(F),
        QE.ofq_eq(~F, CF.coef(E.QCst{RF.qz(K)}, Con{v, vs}), SV.qzero(), CF.coef_cst_other(RF.qz(K), v, vs)), QE.ofq_zero(~F))

# The sides' combination, coefficient by coefficient
# --------------------------------------------------

def qslin(ms: List<&2, S.Q>, ss: List<&2, SK.Side>, +m: List<&2, Nat>) -> S.Q:
  match ms ss:
    case Nil{} ss:
      S.Q{S.Z0{}, S.XH{}}
    case Con{l, lt} Nil{}:
      S.Q{S.Z0{}, S.XH{}}
    case Con{l, lt} Con{s, st}:
      S.Q.add(S.Q.mul(l, CF.coef(SV.sexpr(s), m)), qslin(lt, st, m))

def coef_slin(ms: List<&2, S.Q>, ss: List<&2, SK.Side>, +m: List<&2, Nat>) -> {qslin(ms, ss, m) == CF.coef(SV.slin(ms, ss), m) : S.Q}:
  match ms ss:
    case Nil{} ss:
      {==}
    case Con{l, lt} Nil{}:
      {==}
    case Con{+l, +lt} Con{+s, +st}:
      %CF.coef_add(E.QMul{E.QCst{l}, SV.sexpr(s)}, SV.slin(lt, st), m) : {qslin(Con{l, lt}, Con{s, st}, m) == _ : S.Q}
      %CF.coef_cmul(l, SV.sexpr(s), m) : {qslin(Con{l, lt}, Con{s, st}, m) == S.Q.add(_, CF.coef(SV.slin(lt, st), m)) : S.Q}
      %coef_slin(lt, st, m) : {qslin(Con{l, lt}, Con{s, st}, m) == S.Q.add(S.Q.mul(l, CF.coef(SV.sexpr(s), m)), _) : S.Q}
      {==}

# qslin read in F
def fqs(~F: O.OField, ms: List<&2, S.Q>, ss: List<&2, SK.Side>, +m: List<&2, Nat>) -> O.C(F):
  match ms ss:
    case Nil{} ss:
      O.zero(F)
    case Con{l, lt} Nil{}:
      O.zero(F)
    case Con{l, lt} Con{s, st}:
      O.add(F, O.mul(F, O.ofq(~F, l), O.ofq(~F, CF.coef(SV.sexpr(s), m))), fqs(~F, lt, st, m))

def ofq_qslin(~F: O.OField, ms: List<&2, S.Q>, ss: List<&2, SK.Side>, +m: List<&2, Nat>) -> {fqs(~F, ms, ss, m) == O.ofq(~F, qslin(ms, ss, m)) : O.C(F)}:
  match ms ss:
    case Nil{} ss:
      Equal.sym(O.C(F), O.ofq(~F, S.Q{S.Z0{}, S.XH{}}), O.zero(F), QE.ofq_zero(~F))
    case Con{l, lt} Nil{}:
      Equal.sym(O.C(F), O.ofq(~F, S.Q{S.Z0{}, S.XH{}}), O.zero(F), QE.ofq_zero(~F))
    case Con{+l, +lt} Con{+s, +st}:
      %Equal.sym(O.C(F), O.ofq(~F, S.Q.add(S.Q.mul(l, CF.coef(SV.sexpr(s), m)), qslin(lt, st, m))), O.add(F, O.ofq(~F, S.Q.mul(l, CF.coef(SV.sexpr(s), m))), O.ofq(~F, qslin(lt, st, m))),
          QE.ofq_add(~F, S.Q.mul(l, CF.coef(SV.sexpr(s), m)), qslin(lt, st, m))) : {fqs(~F, Con{l, lt}, Con{s, st}, m) == _ : O.C(F)}
      %Equal.sym(O.C(F), O.ofq(~F, S.Q.mul(l, CF.coef(SV.sexpr(s), m))), O.mul(F, O.ofq(~F, l), O.ofq(~F, CF.coef(SV.sexpr(s), m))), QE.ofq_mul(~F, l, CF.coef(SV.sexpr(s), m)))
        : {fqs(~F, Con{l, lt}, Con{s, st}, m) == O.add(F, _, O.ofq(~F, qslin(lt, st, m))) : O.C(F)}
      %ofq_qslin(~F, lt, st, m) : {fqs(~F, Con{l, lt}, Con{s, st}, m) == O.add(F, O.mul(F, O.ofq(~F, l), O.ofq(~F, CF.coef(SV.sexpr(s), m))), _) : O.C(F)}
      {==}

# Identities from coefficients
# ----------------------------


def ident_m(~F: O.OField, +ls: List<&2, S.Q>, +es: List<&2, E.QExpr>, +ms: List<&2, S.Q>, +ss: List<&2, SK.Side>, +k: S.Q, +m: List<&2, Nat>,
  h: {O.add(F, DR.fql(~F, ls, es, m), fqs(~F, ms, ss, m)) == O.ofq(~F, CF.coef(E.QCst{k}, m)) : O.C(F)}) -> {EL.cz(m, R.norm(QN.clr(E.QSub{E.QAdd{SV.lin(ls, es), SV.slin(ms, ss)}, E.QCst{k}}))) == S.Z0{} : S.Z}:
  %CF.coef_sub(E.QAdd{SV.lin(ls, es), SV.slin(ms, ss)}, E.QCst{k}, m) : {S.Q.num(_) == S.Z0{} : S.Z}
  %CF.coef_add(SV.lin(ls, es), SV.slin(ms, ss), m) : {S.Q.num(S.Q.sub(_, CF.coef(E.QCst{k}, m))) == S.Z0{} : S.Z}
  %CF.coef_lin(ls, es, m) : {S.Q.num(S.Q.sub(S.Q.add(_, CF.coef(SV.slin(ms, ss), m)), CF.coef(E.QCst{k}, m))) == S.Z0{} : S.Z}
  %coef_slin(ms, ss, m) : {S.Q.num(S.Q.sub(S.Q.add(CF.qlin(ls, es, m), _), CF.coef(E.QCst{k}, m))) == S.Z0{} : S.Z}
  DR.num_zero(~F, S.Q.sub(S.Q.add(CF.qlin(ls, es, m), qslin(ms, ss, m)), CF.coef(E.QCst{k}, m)),
    (%Equal.sym(O.C(F), O.ofq(~F, S.Q.add(S.Q.add(CF.qlin(ls, es, m), qslin(ms, ss, m)), S.Q.neg(CF.coef(E.QCst{k}, m)))), O.add(F, O.ofq(~F, S.Q.add(CF.qlin(ls, es, m), qslin(ms, ss, m))), O.ofq(~F, S.Q.neg(CF.coef(E.QCst{k}, m)))), QE.ofq_add(~F, S.Q.add(CF.qlin(ls, es, m), qslin(ms, ss, m)), S.Q.neg(CF.coef(E.QCst{k}, m))))
       : {_ == O.zero(F) : O.C(F)}
     %Equal.sym(O.C(F), O.ofq(~F, S.Q.add(CF.qlin(ls, es, m), qslin(ms, ss, m))), O.add(F, O.ofq(~F, CF.qlin(ls, es, m)), O.ofq(~F, qslin(ms, ss, m))), QE.ofq_add(~F, CF.qlin(ls, es, m), qslin(ms, ss, m)))
       : {O.add(F, _, O.ofq(~F, S.Q.neg(CF.coef(E.QCst{k}, m)))) == O.zero(F) : O.C(F)}
     %Equal.sym(O.C(F), O.ofq(~F, S.Q.neg(CF.coef(E.QCst{k}, m))), O.neg(F, O.ofq(~F, CF.coef(E.QCst{k}, m))), QE.ofq_neg(~F, CF.coef(E.QCst{k}, m)))
       : {O.add(F, O.add(F, O.ofq(~F, CF.qlin(ls, es, m)), O.ofq(~F, qslin(ms, ss, m))), _) == O.zero(F) : O.C(F)}
     %DR.ofq_qlin(~F, ls, es, m) : {O.add(F, O.add(F, _, O.ofq(~F, qslin(ms, ss, m))), O.neg(F, O.ofq(~F, CF.coef(E.QCst{k}, m)))) == O.zero(F) : O.C(F)}
     %ofq_qslin(~F, ms, ss, m) : {O.add(F, O.add(F, DR.fql(~F, ls, es, m), _), O.neg(F, O.ofq(~F, CF.coef(E.QCst{k}, m)))) == O.zero(F) : O.C(F)}
     %Equal.sym(O.C(F), O.add(F, DR.fql(~F, ls, es, m), fqs(~F, ms, ss, m)), O.ofq(~F, CF.coef(E.QCst{k}, m)), h) : {O.add(F, _, O.neg(F, O.ofq(~F, CF.coef(E.QCst{k}, m)))) == O.zero(F) : O.C(F)}
     FR.fring_eq(~F, [O.ofq(~F, CF.coef(E.QCst{k}, m))], E.ZAdd{E.ZVar{0n}, E.ZNeg{E.ZVar{0n}}}, E.ZCst{S.Z0{}}, {==})))

def ident_fn(~F: O.OField, +ls: List<&2, S.Q>, +es: List<&2, E.QExpr>, +ms: List<&2, S.Q>, +ss: List<&2, SK.Side>, +k: S.Q,
  hz: @m: List<&2, Nat> -> {O.add(F, DR.fql(~F, ls, es, m), fqs(~F, ms, ss, m)) == O.ofq(~F, CF.coef(E.QCst{k}, m)) : O.C(F)}, +m: List<&2, Nat>)
  -> {EL.cz(m, R.norm(QN.clr(E.QSub{E.QAdd{SV.lin(ls, es), SV.slin(ms, ss)}, E.QCst{k}}))) == S.Z0{} : S.Z}:
  ident_m(~F, ls, es, ms, ss, k, m, hz(m))

# l . es + m . ss = k as polynomials, from its coefficients read in F
def ident_of(~F: O.OField, +ls: List<&2, S.Q>, +es: List<&2, E.QExpr>, +ms: List<&2, S.Q>, +ss: List<&2, SK.Side>, +k: S.Q,
  hz: @m: List<&2, Nat> -> {O.add(F, DR.fql(~F, ls, es, m), fqs(~F, ms, ss, m)) == O.ofq(~F, CF.coef(E.QCst{k}, m)) : O.C(F)})
  -> SV.Ident(E.QAdd{SV.lin(ls, es), SV.slin(ms, ss)}, E.QCst{k}):
  ID.ident_ok(E.QAdd{SV.lin(ls, es), SV.slin(ms, ss)}, E.QCst{k},
    DR.qn_isnil(R.norm(QN.clr(E.QSub{E.QAdd{SV.lin(ls, es), SV.slin(ms, ss)}, E.QCst{k}})),
      EP.red_zero(R.norm(QN.clr(E.QSub{E.QAdd{SV.lin(ls, es), SV.slin(ms, ss)}, E.QCst{k}})), RP.norm_red(QN.clr(E.QSub{E.QAdd{SV.lin(ls, es), SV.slin(ms, ss)}, E.QCst{k}})),
        m => ident_fn(~F, ls, es, ms, ss, k, hz, m))))

# The multipliers over es
# -----------------------

# the equations the walk kept, in order
def kept(keep: List<&2, Bool>, es: List<&2, E.QExpr>) -> List<&2, E.QExpr>:
  match keep es:
    case Nil{} es:
      Nil{}
    case Con{b, kt} Nil{}:
      Nil{}
    case Con{True{}, kt} Con{e, et}:
      Con{e, kept(kt, et)}
    case Con{False{}, kt} Con{e, et}:
      kept(kt, et)

def zdot_nil_r(u: List<&2, S.Z>) -> {S.Z0{} == EP.zdot(u, Nil{}) : S.Z}:
  match u:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

def zdot_hdtl(cs: List<&2, S.Z>, +y: S.Z, +s: List<&2, S.Z>) -> {S.Z.add(S.Z.mul(RF.hd(cs), y), EP.zdot(RF.tl(cs), s)) == EP.zdot(cs, Con{y, s}) : S.Z}:
  match cs:
    case Nil{}:
      Equal.sym(S.Z, S.Z0{}, EP.zdot(Nil{}, s), EP.zdot_nil(s))
    case Con{c, ct}:
      {==}

def fql_nil(~F: O.OField, es: List<&2, E.QExpr>, +m: List<&2, Nat>) -> {DR.fql(~F, Nil{}, es, m) == O.zero(F) : O.C(F)}:
  match es:
    case Nil{}:
      {==}
    case Con{e, et}:
      {==}


# l_j = c_j den(e_j) at the kept equations, 0 at the dropped: l . coef(es)
# is c . (the kept equations' integer coefficients)
def fql_expand(~F: O.OField, keep: List<&2, Bool>, es: List<&2, E.QExpr>, +cs: List<&2, S.Z>, +m: List<&2, Nat>)
  -> {DR.fql(~F, RF.expand(keep, es, cs), es, m) == O.ofz(~F, EP.zdot(cs, EP.zv(m, kept(keep, es)))) : O.C(F)}:
  match keep es:
    case Nil{} es:
      %zdot_nil_r(cs) : {DR.fql(~F, Nil{}, es, m) == O.ofz(~F, _) : O.C(F)}
      fql_nil(~F, es, m)
    case Con{True{}, kt} Nil{}:
      %zdot_nil_r(cs) : {DR.fql(~F, Nil{}, Nil{}, m) == O.ofz(~F, _) : O.C(F)}
      {==}
    case Con{False{}, kt} Nil{}:
      %zdot_nil_r(cs) : {DR.fql(~F, Nil{}, Nil{}, m) == O.ofz(~F, _) : O.C(F)}
      {==}
    case Con{True{}, +kt} Con{+e, +et}:
      %zdot_hdtl(cs, EL.cz(m, EP.NE(e)), EP.zv(m, kept(kt, et))) : {O.add(F, O.mul(F, O.ofq(~F, RF.qz(S.Z.mul(RF.hd(cs), S.Zpos{QN.den(e)}))), O.ofq(~F, CF.coef(e, m))), DR.fql(~F, RF.expand(kt, et, RF.tl(cs)), et, m)) == O.ofz(~F, _) : O.C(F)}
      %FR.ofz_add(~F, S.Z.mul(RF.hd(cs), EL.cz(m, EP.NE(e))), EP.zdot(RF.tl(cs), EP.zv(m, kept(kt, et)))) : {O.add(F, O.mul(F, O.ofq(~F, RF.qz(S.Z.mul(RF.hd(cs), S.Zpos{QN.den(e)}))), O.ofq(~F, CF.coef(e, m))), DR.fql(~F, RF.expand(kt, et, RF.tl(cs)), et, m)) == _ : O.C(F)}
      %fql_expand(~F, kt, et, RF.tl(cs), m) : {O.add(F, O.mul(F, O.ofq(~F, RF.qz(S.Z.mul(RF.hd(cs), S.Zpos{QN.den(e)}))), O.ofq(~F, CF.coef(e, m))), DR.fql(~F, RF.expand(kt, et, RF.tl(cs)), et, m)) == O.add(F, O.ofz(~F, S.Z.mul(RF.hd(cs), EL.cz(m, EP.NE(e)))), _) : O.C(F)}
      %Equal.trans(O.C(F), O.mul(F, O.ofq(~F, RF.qz(S.Z.mul(RF.hd(cs), S.Zpos{QN.den(e)}))), O.ofq(~F, CF.coef(e, m))), O.ofq(~F, S.Q{S.Z.mul(RF.hd(cs), EL.cz(m, EP.NE(e))), S.XH{}}), O.ofz(~F, S.Z.mul(RF.hd(cs), EL.cz(m, EP.NE(e)))), DR.cancel(~F, RF.hd(cs), QN.den(e), S.XH{}, EL.cz(m, EP.NE(e))), ofq_qz(~F, S.Z.mul(RF.hd(cs), EL.cz(m, EP.NE(e)))))
        : {O.add(F, O.mul(F, O.ofq(~F, RF.qz(S.Z.mul(RF.hd(cs), S.Zpos{QN.den(e)}))), O.ofq(~F, CF.coef(e, m))), DR.fql(~F, RF.expand(kt, et, RF.tl(cs)), et, m)) == O.add(F, _, DR.fql(~F, RF.expand(kt, et, RF.tl(cs)), et, m)) : O.C(F)}
      {==}
    case Con{False{}, +kt} Con{+e, +et}:
      Equal.trans(O.C(F), O.add(F, O.mul(F, O.ofq(~F, RF.qz(S.Z0{})), O.ofq(~F, CF.coef(e, m))), DR.fql(~F, RF.expand(kt, et, cs), et, m)), DR.fql(~F, RF.expand(kt, et, cs), et, m), O.ofz(~F, EP.zdot(cs, EP.zv(m, kept(kt, et)))),
        FR.fring_eq(~F, [O.inv(F, O.one(F)), O.ofq(~F, CF.coef(e, m)), DR.fql(~F, RF.expand(kt, et, cs), et, m)], E.ZAdd{E.ZMul{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZVar{2n}, {==}),
        fql_expand(~F, kt, et, cs, m))

# The sides' multipliers
# ----------------------

def sexpr_eq(s: SK.Side) -> {RF.sexpr(s) == SV.sexpr(s) : E.QExpr}:
  match s:
    case SK.Gt0{e}:
      {==}
    case SK.Ge0{e}:
      {==}

# sum_k mu_k bt_k NE(s_k), coefficient at m
def sdot(mu: List<&2, S.Z>, rs: List<&2, EL.Res>, ss: List<&2, SK.Side>, +m: List<&2, Nat>) -> S.Z:
  match mu rs ss:
    case Nil{} rs ss:
      S.Z0{}
    case Con{u, ut} Nil{} ss:
      S.Z0{}
    case Con{u, ut} Con{r, rt} Nil{}:
      S.Z0{}
    case Con{u, ut} Con{r, rt} Con{s, st}:
      S.Z.add(S.Z.mul(S.Z.mul(u, S.Zpos{RF.Res.bt(r)}), EL.cz(m, EP.NE(SV.sexpr(s)))), sdot(ut, rt, st, m))

def sm_term(~F: O.OField, +u: S.Z, +bt: S.Pos, +s: SK.Side, +m: List<&2, Nat>)
  -> {O.mul(F, O.ofq(~F, RF.qz(S.Z.mul(u, S.Zpos{S.Pos.mul(bt, QN.den(RF.sexpr(s)))}))), O.ofq(~F, CF.coef(SV.sexpr(s), m))) == O.ofz(~F, S.Z.mul(S.Z.mul(u, S.Zpos{bt}), EL.cz(m, EP.NE(SV.sexpr(s))))) : O.C(F)}:
  %Equal.sym(E.QExpr, RF.sexpr(s), SV.sexpr(s), sexpr_eq(s)) : {O.mul(F, O.ofq(~F, RF.qz(S.Z.mul(u, S.Zpos{S.Pos.mul(bt, QN.den(_))}))), O.ofq(~F, CF.coef(SV.sexpr(s), m))) == O.ofz(~F, S.Z.mul(S.Z.mul(u, S.Zpos{bt}), EL.cz(m, EP.NE(SV.sexpr(s))))) : O.C(F)}
  %Equal.sym(S.Z, S.Z.mul(u, S.Z.mul(S.Zpos{bt}, S.Zpos{QN.den(SV.sexpr(s))})), S.Z.mul(S.Z.mul(u, S.Zpos{bt}), S.Zpos{QN.den(SV.sexpr(s))}), ZL.mul_assoc(u, S.Zpos{bt}, S.Zpos{QN.den(SV.sexpr(s))}))
    : {O.mul(F, O.ofq(~F, RF.qz(_)), O.ofq(~F, CF.coef(SV.sexpr(s), m))) == O.ofz(~F, S.Z.mul(S.Z.mul(u, S.Zpos{bt}), EL.cz(m, EP.NE(SV.sexpr(s))))) : O.C(F)}
  Equal.trans(O.C(F), O.mul(F, O.ofq(~F, RF.qz(S.Z.mul(S.Z.mul(u, S.Zpos{bt}), S.Zpos{QN.den(SV.sexpr(s))}))), O.ofq(~F, CF.coef(SV.sexpr(s), m))),
    O.ofq(~F, S.Q{S.Z.mul(S.Z.mul(u, S.Zpos{bt}), EL.cz(m, EP.NE(SV.sexpr(s)))), S.XH{}}), O.ofz(~F, S.Z.mul(S.Z.mul(u, S.Zpos{bt}), EL.cz(m, EP.NE(SV.sexpr(s))))),
    DR.cancel(~F, S.Z.mul(u, S.Zpos{bt}), QN.den(SV.sexpr(s)), S.XH{}, EL.cz(m, EP.NE(SV.sexpr(s)))),
    ofq_qz(~F, S.Z.mul(S.Z.mul(u, S.Zpos{bt}), EL.cz(m, EP.NE(SV.sexpr(s))))))

def fqs_smults(~F: O.OField, mu: List<&2, S.Z>, rs: List<&2, EL.Res>, ss: List<&2, SK.Side>, +m: List<&2, Nat>)
  -> {fqs(~F, RF.smults(mu, rs, ss), ss, m) == O.ofz(~F, sdot(mu, rs, ss, m)) : O.C(F)}:
  match mu rs ss:
    case Nil{} rs ss:
      {==}
    case Con{u, ut} Nil{} ss:
      {==}
    case Con{u, ut} Con{r, rt} Nil{}:
      {==}
    case Con{+u, +ut} Con{+r, +rt} Con{+s, +st}:
      %FR.ofz_add(~F, S.Z.mul(S.Z.mul(u, S.Zpos{RF.Res.bt(r)}), EL.cz(m, EP.NE(SV.sexpr(s)))), sdot(ut, rt, st, m))
        : {O.add(F, O.mul(F, O.ofq(~F, RF.qz(S.Z.mul(u, S.Zpos{S.Pos.mul(RF.Res.bt(r), QN.den(RF.sexpr(s)))}))), O.ofq(~F, CF.coef(SV.sexpr(s), m))), fqs(~F, RF.smults(ut, rt, st), st, m)) == _ : O.C(F)}
      %fqs_smults(~F, ut, rt, st, m)
        : {O.add(F, O.mul(F, O.ofq(~F, RF.qz(S.Z.mul(u, S.Zpos{S.Pos.mul(RF.Res.bt(r), QN.den(RF.sexpr(s)))}))), O.ofq(~F, CF.coef(SV.sexpr(s), m))), fqs(~F, RF.smults(ut, rt, st), st, m)) == O.add(F, O.ofz(~F, S.Z.mul(S.Z.mul(u, S.Zpos{RF.Res.bt(r)}), EL.cz(m, EP.NE(SV.sexpr(s))))), _) : O.C(F)}
      %sm_term(~F, u, RF.Res.bt(r), s, m)
        : {O.add(F, O.mul(F, O.ofq(~F, RF.qz(S.Z.mul(u, S.Zpos{S.Pos.mul(RF.Res.bt(r), QN.den(RF.sexpr(s)))}))), O.ofq(~F, CF.coef(SV.sexpr(s), m))), fqs(~F, RF.smults(ut, rt, st), st, m)) == O.add(F, _, fqs(~F, RF.smults(ut, rt, st), st, m)) : O.C(F)}
      {==}

# The sides after reduction
# -------------------------

# sum_k mu_k p_k, coefficient at m
def pdot(mu: List<&2, S.Z>, rs: List<&2, EL.Res>, +m: List<&2, Nat>) -> S.Z:
  match mu rs:
    case Nil{} rs:
      S.Z0{}
    case Con{u, ut} Nil{}:
      S.Z0{}
    case Con{u, ut} Con{r, rt}:
      S.Z.add(S.Z.mul(u, EL.cz(m, RF.Res.p(r))), pdot(ut, rt, m))

def pdot_ksum(mu: List<&2, S.Z>, rs: List<&2, EL.Res>) -> {pdot(mu, rs, Nil{}) == RF.ksum(mu, rs) : S.Z}:
  match mu rs:
    case Nil{} rs:
      {==}
    case Con{u, ut} Nil{}:
      {==}
    case Con{+u, ut} Con{+r, rt}:
      %pdot_ksum(ut, rt) : {S.Z.add(S.Z.mul(u, EL.cz(Nil{}, RF.Res.p(r))), pdot(ut, rt, Nil{})) == S.Z.add(S.Z.mul(u, EL.cz(Nil{}, RF.Res.p(r))), _) : S.Z}
      {==}


def lp_step(+m: List<&2, Nat>, +u: S.Z, r: EL.Res, +s: SK.Side, +B: List<&2, E.QExpr>, +CB: List<&2, S.Z>, +S0: S.Z, +P0: S.Z,
  hr: EP.Rel(m, r, RF.sexpr(s), B), ih: {S.Z.add(EP.zdot(CB, EP.zv(m, B)), S0) == P0 : S.Z})
  -> {S.Z.add(EP.zdot(EL.vadd(EL.vscale(u, RF.Res.cb(r)), CB), EP.zv(m, B)), S.Z.add(S.Z.mul(S.Z.mul(u, S.Zpos{RF.Res.bt(r)}), EL.cz(m, EP.NE(SV.sexpr(s)))), S0)) == S.Z.add(S.Z.mul(u, EL.cz(m, RF.Res.p(r))), P0) : S.Z}:
  match r:
    case EL.Res{+p, +cb, +bt}:
      %EP.zdot_vadd(EL.vscale(u, cb), CB, EP.zv(m, B)) : {S.Z.add(_, S.Z.add(S.Z.mul(S.Z.mul(u, S.Zpos{bt}), EL.cz(m, EP.NE(SV.sexpr(s)))), S0)) == S.Z.add(S.Z.mul(u, EL.cz(m, p)), P0) : S.Z}
      %EP.zdot_vscale(u, cb, EP.zv(m, B)) : {S.Z.add(S.Z.add(_, EP.zdot(CB, EP.zv(m, B))), S.Z.add(S.Z.mul(S.Z.mul(u, S.Zpos{bt}), EL.cz(m, EP.NE(SV.sexpr(s)))), S0)) == S.Z.add(S.Z.mul(u, EL.cz(m, p)), P0) : S.Z}
      %Equal.sym(S.Z, EL.cz(m, p), S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, EP.NE(RF.sexpr(s)))), EP.zdot(cb, EP.zv(m, B))), hr)
        : {S.Z.add(S.Z.add(S.Z.mul(u, EP.zdot(cb, EP.zv(m, B))), EP.zdot(CB, EP.zv(m, B))), S.Z.add(S.Z.mul(S.Z.mul(u, S.Zpos{bt}), EL.cz(m, EP.NE(SV.sexpr(s)))), S0)) == S.Z.add(S.Z.mul(u, _), P0) : S.Z}
      %Equal.sym(E.QExpr, RF.sexpr(s), SV.sexpr(s), sexpr_eq(s))
        : {S.Z.add(S.Z.add(S.Z.mul(u, EP.zdot(cb, EP.zv(m, B))), EP.zdot(CB, EP.zv(m, B))), S.Z.add(S.Z.mul(S.Z.mul(u, S.Zpos{bt}), EL.cz(m, EP.NE(SV.sexpr(s)))), S0)) == S.Z.add(S.Z.mul(u, S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, EP.NE(_))), EP.zdot(cb, EP.zv(m, B)))), P0) : S.Z}
      %ih : {S.Z.add(S.Z.add(S.Z.mul(u, EP.zdot(cb, EP.zv(m, B))), EP.zdot(CB, EP.zv(m, B))), S.Z.add(S.Z.mul(S.Z.mul(u, S.Zpos{bt}), EL.cz(m, EP.NE(SV.sexpr(s)))), S0)) == S.Z.add(S.Z.mul(u, S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, EP.NE(SV.sexpr(s)))), EP.zdot(cb, EP.zv(m, B)))), _) : S.Z}
      R.ring_eq([u, S.Zpos{bt}, EL.cz(m, EP.NE(SV.sexpr(s))), EP.zdot(cb, EP.zv(m, B)), EP.zdot(CB, EP.zv(m, B)), S0], E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZVar{4n}}, E.ZAdd{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZVar{5n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{3n}}}, E.ZAdd{E.ZVar{4n}, E.ZVar{5n}}}, {==})

# what the reduction subtracted (the basis' combination) plus the sides'
# multiples is sum_k mu_k p_k
def lp_rel(+m: List<&2, Nat>, mu: List<&2, S.Z>, ss: List<&2, SK.Side>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +hok: {EP.allok(B, rows) == True{} : Bool})
  -> {S.Z.add(EP.zdot(RF.cbsum(mu, RF.sres(rows, ss)), EP.zv(m, B)), sdot(mu, RF.sres(rows, ss), ss, m)) == pdot(mu, RF.sres(rows, ss), m) : S.Z}:
  match mu ss:
    case Nil{} ss:
      %EP.zdot_nil(EP.zv(m, B)) : {S.Z.add(_, S.Z0{}) == S.Z0{} : S.Z}
      {==}
    case Con{u, ut} Nil{}:
      %EP.zdot_nil(EP.zv(m, B)) : {S.Z.add(_, S.Z0{}) == S.Z0{} : S.Z}
      {==}
    case Con{+u, +ut} Con{+s, +st}:
      lp_step(m, u, EL.resid(rows, RF.sexpr(s)), s, B, RF.cbsum(ut, RF.sres(rows, st)), sdot(ut, RF.sres(rows, st), st, m), pdot(ut, RF.sres(rows, st), m),
        EP.resid_rel(m, rows, RF.sexpr(s), B, hok), lp_rel(m, ut, st, rows, B, hok))

# Monomials: membership and position
# ----------------------------------

def memm(+n: List<&2, Nat>, ys: List<&2, List<&2, Nat>>) -> Bool:
  match ys:
    case Nil{}:
      False{}
    case Con{y, t}:
      SV.bor(EL.iseq(NR.mcmp(n, y)), memm(n, t))

def iseq_eq(o: Cmp, h: {EL.iseq(o) == True{} : Bool}) -> {EQ{} == o : Cmp}:
  match o:
    case LT{}:
      absurd({EQ{} == LT{} : Cmp}, KA.ft(h))
    case EQ{}:
      {==}
    case GT{}:
      absurd({EQ{} == GT{} : Cmp}, KA.ft(h))

def bor_fl(a: Bool, +b: Bool, h: {SV.bor(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.tf(h))
    case False{}:
      {==}

def bor_fr(a: Bool, +b: Bool, h: {SV.bor(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      absurd({b == False{} : Bool}, KA.tf(h))
    case False{}:
      h

def bor_mono_r(a: Bool, +b: Bool, +c: Bool, h: {SV.bor(a, b) == True{} : Bool}, f: {b == True{} : Bool} -> {c == True{} : Bool}) -> {SV.bor(a, c) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      f(h)

def memm_ne.c(b: Bool, +m: List<&2, Nat>, +n: List<&2, Nat>, +y: List<&2, Nat>, +t: List<&2, List<&2, Nat>>, +hb: {b == EL.iseq(NR.mcmp(n, y)) : Bool},
  hn: {SV.bor(EL.iseq(NR.mcmp(n, y)), memm(n, t)) == True{} : Bool}, +hm: {SV.bor(EL.iseq(NR.mcmp(m, y)), memm(m, t)) == False{} : Bool},
  ih: {memm(n, t) == True{} : Bool} -> {memm(m, t) == False{} : Bool} -> {EL.iseq(NR.mcmp(m, n)) == False{} : Bool}) -> {EL.iseq(NR.mcmp(m, n)) == False{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(List<&2, Nat>, n, y, NR.mcmp_eq(n, y, iseq_eq(NR.mcmp(n, y), Equal.sym(Bool, True{}, EL.iseq(NR.mcmp(n, y)), hb)))) : {EL.iseq(NR.mcmp(m, _)) == False{} : Bool}
      bor_fl(EL.iseq(NR.mcmp(m, y)), memm(m, t), hm)
    case False{}:
      ih((%Equal.sym(Bool, False{}, EL.iseq(NR.mcmp(n, y)), hb) : {SV.bor(_, memm(n, t)) == True{} : Bool}
          hn),
        bor_fr(EL.iseq(NR.mcmp(m, y)), memm(m, t), hm))

# n is in ys and m is not: m is not n
def memm_ne(+m: List<&2, Nat>, +n: List<&2, Nat>, ys: List<&2, List<&2, Nat>>, hn: {memm(n, ys) == True{} : Bool}, hm: {memm(m, ys) == False{} : Bool}) -> {EL.iseq(NR.mcmp(m, n)) == False{} : Bool}:
  match ys:
    case Nil{}:
      absurd({EL.iseq(NR.mcmp(m, n)) == False{} : Bool}, KA.ft(hn))
    case Con{+y, +t}:
      memm_ne.c(EL.iseq(NR.mcmp(n, y)), m, n, y, t, {==}, hn, hm, a => b => memm_ne(m, n, t, a, b))

def ins_mono.d(o: Cmp, +x: List<&2, Nat>, +m: List<&2, Nat>, +h0: List<&2, Nat>, +t: List<&2, List<&2, Nat>>, h: {memm(x, Con{h0, t}) == True{} : Bool},
  ih: {memm(x, t) == True{} : Bool} -> {memm(x, RF.ins(m, t)) == True{} : Bool}) -> {memm(x, RF.ins.dec(o, m, h0, t, RF.ins(m, t))) == True{} : Bool}:
  match o:
    case LT{}:
      LI.bor_r(EL.iseq(NR.mcmp(x, m)), memm(x, Con{h0, t}), h)
    case EQ{}:
      h
    case GT{}:
      bor_mono_r(EL.iseq(NR.mcmp(x, h0)), memm(x, t), memm(x, RF.ins(m, t)), h, ih)

def ins_mono(+x: List<&2, Nat>, +m: List<&2, Nat>, ys: List<&2, List<&2, Nat>>, h: {memm(x, ys) == True{} : Bool}) -> {memm(x, RF.ins(m, ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      absurd({memm(x, RF.ins(m, Nil{})) == True{} : Bool}, KA.ft(h))
    case Con{+h0, +t}:
      ins_mono.d(NR.mcmp(m, h0), x, m, h0, t, h, a => ins_mono(x, m, t, a))

def ins_self.d(o: Cmp, +m: List<&2, Nat>, +h0: List<&2, Nat>, +t: List<&2, List<&2, Nat>>, ho: {o == NR.mcmp(m, h0) : Cmp}, ih: {memm(m, RF.ins(m, t)) == True{} : Bool})
  -> {memm(m, RF.ins.dec(o, m, h0, t, RF.ins(m, t))) == True{} : Bool}:
  match o:
    case LT{}:
      %RP.mcmp_refl(m) : {SV.bor(EL.iseq(_), memm(m, Con{h0, t})) == True{} : Bool}
      {==}
    case EQ{}:
      %ho : {SV.bor(EL.iseq(_), memm(m, t)) == True{} : Bool}
      {==}
    case GT{}:
      LI.bor_r(EL.iseq(NR.mcmp(m, h0)), memm(m, RF.ins(m, t)), ih)

def ins_self(+m: List<&2, Nat>, ys: List<&2, List<&2, Nat>>) -> {memm(m, RF.ins(m, ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      %RP.mcmp_refl(m) : {SV.bor(EL.iseq(_), False{}) == True{} : Bool}
      {==}
    case Con{+h0, +t}:
      ins_self.d(NR.mcmp(m, h0), m, h0, t, {==}, ins_self(m, t))

def insnc_mono(+x: List<&2, Nat>, m: List<&2, Nat>, +ys: List<&2, List<&2, Nat>>, h: {memm(x, ys) == True{} : Bool}) -> {memm(x, RF.insnc(m, ys)) == True{} : Bool}:
  match m:
    case Nil{}:
      h
    case Con{+a, +b}:
      ins_mono(x, Con{a, b}, ys, h)

def tmons_mono(+x: List<&2, Nat>, p: List<&2, R.ZTerm>, +ys: List<&2, List<&2, Nat>>, h: {memm(x, ys) == True{} : Bool}) -> {memm(x, RF.tmons(p, ys)) == True{} : Bool}:
  match p:
    case Nil{}:
      h
    case Con{R.ZTerm{c, +mm}, t}:
      tmons_mono(x, t, RF.insnc(mm, ys), insnc_mono(x, mm, ys, h))

def ymons_mono(+x: List<&2, Nat>, rs: List<&2, EL.Res>, +ys: List<&2, List<&2, Nat>>, h: {memm(x, ys) == True{} : Bool}) -> {memm(x, RF.ymons(rs, ys)) == True{} : Bool}:
  match rs:
    case Nil{}:
      h
    case Con{+r, t}:
      ymons_mono(x, t, RF.tmons(RF.Res.p(r), ys), tmons_mono(x, RF.Res.p(r), ys, h))

# every monomial of p other than 1 is in ys
def covp(p: List<&2, R.ZTerm>, +ys: List<&2, List<&2, Nat>>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{R.ZTerm{c, +n}, t}:
      KA.band(SV.bor(RF.iscst(n), memm(n, ys)), covp(t, ys))

def covp_tm(p: List<&2, R.ZTerm>, +q: List<&2, R.ZTerm>, +ys: List<&2, List<&2, Nat>>, h: {covp(p, ys) == True{} : Bool}) -> {covp(p, RF.tmons(q, ys)) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{c, +n}, +t}:
      +h2 = h
      KA.band_i(SV.bor(RF.iscst(n), memm(n, RF.tmons(q, ys))), covp(t, RF.tmons(q, ys)),
        bor_mono_r(RF.iscst(n), memm(n, ys), memm(n, RF.tmons(q, ys)), KA.band_l(SV.bor(RF.iscst(n), memm(n, ys)), covp(t, ys), h2), a => tmons_mono(n, q, ys, a)),
        covp_tm(t, q, ys, KA.band_r(SV.bor(RF.iscst(n), memm(n, ys)), covp(t, ys), h2)))

def covp_ym(p: List<&2, R.ZTerm>, +rs: List<&2, EL.Res>, +ys: List<&2, List<&2, Nat>>, h: {covp(p, ys) == True{} : Bool}) -> {covp(p, RF.ymons(rs, ys)) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{c, +n}, +t}:
      +h2 = h
      KA.band_i(SV.bor(RF.iscst(n), memm(n, RF.ymons(rs, ys))), covp(t, RF.ymons(rs, ys)),
        bor_mono_r(RF.iscst(n), memm(n, ys), memm(n, RF.ymons(rs, ys)), KA.band_l(SV.bor(RF.iscst(n), memm(n, ys)), covp(t, ys), h2), a => ymons_mono(n, rs, ys, a)),
        covp_ym(t, rs, ys, KA.band_r(SV.bor(RF.iscst(n), memm(n, ys)), covp(t, ys), h2)))

def cs_head(n: List<&2, Nat>, +t: List<&2, R.ZTerm>, +ys: List<&2, List<&2, Nat>>) -> {SV.bor(RF.iscst(n), memm(n, RF.tmons(t, RF.insnc(n, ys)))) == True{} : Bool}:
  match n:
    case Nil{}:
      {==}
    case Con{+a, +b}:
      tmons_mono(Con{a, b}, t, RF.ins(Con{a, b}, ys), ins_self(Con{a, b}, ys))

def covp_self(p: List<&2, R.ZTerm>, +ys: List<&2, List<&2, Nat>>) -> {covp(p, RF.tmons(p, ys)) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{c, +n}, +t}:
      KA.band_i(SV.bor(RF.iscst(n), memm(n, RF.tmons(t, RF.insnc(n, ys)))), covp(t, RF.tmons(t, RF.insnc(n, ys))),
        cs_head(n, t, ys), covp_self(t, RF.insnc(n, ys)))

def covall(rs: List<&2, EL.Res>, +ys: List<&2, List<&2, Nat>>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, t}:
      KA.band(covp(RF.Res.p(r), ys), covall(t, ys))

# ymons collects every monomial of the residuals
def covall_self(rs: List<&2, EL.Res>, +ys: List<&2, List<&2, Nat>>) -> {covall(rs, RF.ymons(rs, ys)) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      KA.band_i(covp(RF.Res.p(r), RF.ymons(t, RF.tmons(RF.Res.p(r), ys))), covall(t, RF.ymons(t, RF.tmons(RF.Res.p(r), ys))),
        covp_ym(RF.Res.p(r), t, RF.tmons(RF.Res.p(r), ys), covp_self(RF.Res.p(r), ys)), covall_self(t, RF.tmons(RF.Res.p(r), ys)))

def nz_ne(+v: Nat, +vs: List<&2, Nat>, n: List<&2, Nat>, +ys: List<&2, List<&2, Nat>>, hb: {SV.bor(RF.iscst(n), memm(n, ys)) == True{} : Bool}, hm: {memm(Con{v, vs}, ys) == False{} : Bool})
  -> {EL.iseq(NR.mcmp(Con{v, vs}, n)) == False{} : Bool}:
  match n:
    case Nil{}:
      {==}
    case Con{+a, +b}:
      memm_ne(Con{v, vs}, Con{a, b}, ys, hb, hm)

# a monomial other than 1 outside ys has coefficient 0
def cz_notin(+v: Nat, +vs: List<&2, Nat>, p: List<&2, R.ZTerm>, +ys: List<&2, List<&2, Nat>>, hc: {covp(p, ys) == True{} : Bool}, +hm: {memm(Con{v, vs}, ys) == False{} : Bool})
  -> {EL.cz(Con{v, vs}, p) == S.Z0{} : S.Z}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{+c, +n}, +t}:
      +hc2 = hc
      %Equal.sym(Bool, EL.iseq(NR.mcmp(Con{v, vs}, n)), False{}, nz_ne(v, vs, n, ys, KA.band_l(SV.bor(RF.iscst(n), memm(n, ys)), covp(t, ys), hc2), hm))
        : {S.Z.add(EL.ifz(_, c), EL.cz(Con{v, vs}, t)) == S.Z0{} : S.Z}
      cz_notin(v, vs, t, ys, KA.band_r(SV.bor(RF.iscst(n), memm(n, ys)), covp(t, ys), hc2), hm)

def pdot_notin(mu: List<&2, S.Z>, rs: List<&2, EL.Res>, +v: Nat, +vs: List<&2, Nat>, +ys: List<&2, List<&2, Nat>>, +hc: {covall(rs, ys) == True{} : Bool}, +hm: {memm(Con{v, vs}, ys) == False{} : Bool})
  -> {pdot(mu, rs, Con{v, vs}) == S.Z0{} : S.Z}:
  match mu rs:
    case Nil{} rs:
      {==}
    case Con{u, ut} Nil{}:
      {==}
    case Con{+u, +ut} Con{+r, +rt}:
      %Equal.sym(S.Z, EL.cz(Con{v, vs}, RF.Res.p(r)), S.Z0{}, cz_notin(v, vs, RF.Res.p(r), ys, KA.band_l(covp(RF.Res.p(r), ys), covall(rt, ys), hc), hm))
        : {S.Z.add(S.Z.mul(u, _), pdot(ut, rt, Con{v, vs})) == S.Z0{} : S.Z}
      %Equal.sym(S.Z, pdot(ut, rt, Con{v, vs}), S.Z0{}, pdot_notin(ut, rt, v, vs, ys, KA.band_r(covp(RF.Res.p(r), ys), covall(rt, ys), hc), hm))
        : {S.Z.add(S.Z.mul(u, S.Z0{}), _) == S.Z0{} : S.Z}
      R.ring_eq([u], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})

# where m sits in ys, if it does
def midx(+n: List<&2, Nat>, ys: List<&2, List<&2, Nat>>) -> Maybe<&2, Nat>:
  match ys:
    case Nil{}:
      None{}
    case Con{y, t}:
      SX.pick(EL.iseq(NR.mcmp(n, y)), 0n, RN.mapS(midx(n, t)))

def mnth(ys: List<&2, List<&2, Nat>>, l: Nat) -> List<&2, Nat>:
  match ys l:
    case Nil{} l:
      Nil{}
    case Con{y, t} 0n:
      y
    case Con{y, t} 1n+k:
      mnth(t, k)

def midx_none.c(b: Bool, +n: List<&2, Nat>, +t: List<&2, List<&2, Nat>>, h: {SX.pick(b, 0n, RN.mapS(midx(n, t))) == None{} : Maybe<&2, Nat>},
  ih: {midx(n, t) == None{} : Maybe<&2, Nat>} -> {memm(n, t) == False{} : Bool}) -> {SV.bor(b, memm(n, t)) == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, RN.none_some(0n, Equal.sym(Maybe<&2, Nat>, Some{0n}, None{}, h)))
    case False{}:
      ih(RN.map_none(midx(n, t), h))

def midx_none(+n: List<&2, Nat>, ys: List<&2, List<&2, Nat>>, h: {midx(n, ys) == None{} : Maybe<&2, Nat>}) -> {memm(n, ys) == False{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      midx_none.c(EL.iseq(NR.mcmp(n, y)), n, t, h, a => midx_none(n, t, a))

def midx_some.c(b: Bool, +n: List<&2, Nat>, +y: List<&2, Nat>, +t: List<&2, List<&2, Nat>>, l: Nat, hb: {b == EL.iseq(NR.mcmp(n, y)) : Bool}, h: {SX.pick(b, 0n, RN.mapS(midx(n, t))) == Some{l} : Maybe<&2, Nat>},
  ih: @k: Nat -> {midx(n, t) == Some{k} : Maybe<&2, Nat>} -> M.Both({mnth(t, k) == n : List<&2, Nat>}, {SX.ltn(k, RF.mlen(t)) == True{} : Bool}))
  -> M.Both({mnth(Con{y, t}, l) == n : List<&2, Nat>}, {SX.ltn(l, 1n+RF.mlen(t)) == True{} : Bool}):
  match b:
    case True{}:
      %RN.some_inj(0n, l, h) : M.Both({mnth(Con{y, t}, _) == n : List<&2, Nat>}, {SX.ltn(_, 1n+RF.mlen(t)) == True{} : Bool})
      (Equal.sym(List<&2, Nat>, n, y, NR.mcmp_eq(n, y, iseq_eq(NR.mcmp(n, y), Equal.sym(Bool, True{}, EL.iseq(NR.mcmp(n, y)), hb)))), {==})
    case False{}:
      match l:
        case 0n:
          absurd(M.Both({mnth(Con{y, t}, 0n) == n : List<&2, Nat>}, {SX.ltn(0n, 1n+RF.mlen(t)) == True{} : Bool}), RN.map_zero(midx(n, t), h))
        case 1n++k:
          ih(k, RN.map_succ(midx(n, t), k, h))

def midx_some(+n: List<&2, Nat>, ys: List<&2, List<&2, Nat>>, l: Nat, h: {midx(n, ys) == Some{l} : Maybe<&2, Nat>}) -> M.Both({mnth(ys, l) == n : List<&2, Nat>}, {SX.ltn(l, RF.mlen(ys)) == True{} : Bool}):
  match ys:
    case Nil{}:
      absurd(M.Both({mnth(Nil{}, l) == n : List<&2, Nat>}, {SX.ltn(l, 0n) == True{} : Bool}), RN.none_some(l, h))
    case Con{+y, +t}:
      midx_some.c(EL.iseq(NR.mcmp(n, y)), n, y, t, l, {==}, h, k => a => midx_some(n, t, k, a))

def at_coefs(ys: List<&2, List<&2, Nat>>, +p: List<&2, R.ZTerm>, l: Nat, hl: {SX.ltn(l, RF.mlen(ys)) == True{} : Bool}) -> {SX.at(RF.coefs(ys, p), l) == EL.cz(mnth(ys, l), p) : S.Z}:
  match ys l:
    case Nil{} l:
      absurd({SX.at(Nil{}, l) == EL.cz(Nil{}, p) : S.Z}, KA.ft(SP.ltn0(l, hl)))
    case Con{y, t} 0n:
      {==}
    case Con{y, t} 1n+k:
      at_coefs(t, p, k, hl)

# column l of the LP is the coefficient at ys_l
def acol_pdot(mu: List<&2, S.Z>, ss: List<&2, SK.Side>, +rows: List<&2, EL.Row>, +ys: List<&2, List<&2, Nat>>, +l: Nat, +n: List<&2, Nat>,
  +hl: {SX.ltn(l, RF.mlen(ys)) == True{} : Bool}, +he: {mnth(ys, l) == n : List<&2, Nat>})
  -> {SX.dot(mu, UN.acol(RF.ineqs(ys, RF.sres(rows, ss), ss), l)) == pdot(mu, RF.sres(rows, ss), n) : S.Z}:
  match mu ss:
    case Nil{} +ss:
      Equal.sym(S.Z, S.Z0{}, SX.dot(Nil{}, UN.acol(RF.ineqs(ys, RF.sres(rows, ss), ss), l)), UN.dot_nil_l(UN.acol(RF.ineqs(ys, RF.sres(rows, ss), ss), l)))
    case Con{u, ut} Nil{}:
      {==}
    case Con{+u, +ut} Con{+s, +st}:
      %he : {S.Z.add(S.Z.mul(u, SX.at(RF.coefs(ys, RF.Res.p(EL.resid(rows, RF.sexpr(s)))), l)), SX.dot(ut, UN.acol(RF.ineqs(ys, RF.sres(rows, st), st), l)))
        == S.Z.add(S.Z.mul(u, EL.cz(_, RF.Res.p(EL.resid(rows, RF.sexpr(s))))), pdot(ut, RF.sres(rows, st), n)) : S.Z}
      %at_coefs(ys, RF.Res.p(EL.resid(rows, RF.sexpr(s))), l, hl) : {S.Z.add(S.Z.mul(u, SX.at(RF.coefs(ys, RF.Res.p(EL.resid(rows, RF.sexpr(s)))), l)), SX.dot(ut, UN.acol(RF.ineqs(ys, RF.sres(rows, st), st), l)))
        == S.Z.add(S.Z.mul(u, _), pdot(ut, RF.sres(rows, st), n)) : S.Z}
      %acol_pdot(ut, st, rows, ys, l, n, hl, he) : {S.Z.add(S.Z.mul(u, SX.at(RF.coefs(ys, RF.Res.p(EL.resid(rows, RF.sexpr(s)))), l)), SX.dot(ut, UN.acol(RF.ineqs(ys, RF.sres(rows, st), st), l)))
        == S.Z.add(S.Z.mul(u, SX.at(RF.coefs(ys, RF.Res.p(EL.resid(rows, RF.sexpr(s)))), l)), _) : S.Z}
      {==}

# The walk over the equations
# ---------------------------

def bnext(b: Bool, +B: List<&2, E.QExpr>, +e: E.QExpr) -> List<&2, E.QExpr>:
  match b:
    case True{}:
      B
    case False{}:
      EP.qsnoc(B, e)


# the basis after walking es
def wB(es: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>) -> List<&2, E.QExpr>:
  match es:
    case Nil{}:
      B
    case Con{+e, t}:
      wB(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)), bnext(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e))

def wk_rows(b: Bool, w: RF.Walk) -> {RF.Walk.rows(RF.walk.k(b, w)) == RF.Walk.rows(w) : List<&2, EL.Row>}:
  match w:
    case RF.Walk{rows, keep}:
      {==}

def wk_keep(b: Bool, w: RF.Walk) -> {RF.Walk.keep(RF.walk.k(b, w)) == Con{RF.bnot(b), RF.Walk.keep(w)} : List<&2, Bool>}:
  match w:
    case RF.Walk{rows, keep}:
      {==}

def nil_bridge.p(p: List<&2, R.ZTerm>, h: {RF.isnilp(p) == False{} : Bool}) -> {EP.isnil(p) == False{} : Bool}:
  match p:
    case Nil{}:
      absurd({EP.isnil(Nil{}) == False{} : Bool}, KA.tf(h))
    case Con{x, t}:
      {==}

def nil_bridge(r: EL.Res, h: {RF.isnilp(RF.Res.p(r)) == False{} : Bool}) -> {EP.isnil(EP.resp(r)) == False{} : Bool}:
  match r:
    case EL.Res{p, cb, bt}:
      nil_bridge.p(p, h)

def rlen_rsnoc(rows: List<&2, EL.Row>, +x: EL.Row) -> {EL.rlen(EL.rsnoc(rows, x)) == 1n+EL.rlen(rows) : Nat}:
  match rows:
    case Nil{}:
      {==}
    case Con{h, +t}:
      %rlen_rsnoc(t, x) : {1n+EL.rlen(EL.rsnoc(t, x)) == 1n+_ : Nat}
      {==}

def neqs_qsnoc(B: List<&2, E.QExpr>, +e: E.QExpr) -> {SV.neqs(EP.qsnoc(B, e)) == 1n+SV.neqs(B) : Nat}:
  match B:
    case Nil{}:
      {==}
    case Con{b, +t}:
      %neqs_qsnoc(t, e) : {1n+SV.neqs(EP.qsnoc(t, e)) == 1n+_ : Nat}
      {==}

def step_inv(b: Bool, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, +e: E.QExpr, hb: {b == RF.isnilp(RF.Res.p(EL.resid(rows, e))) : Bool}, +h: {EP.rinv(B, rows, 0n) == True{} : Bool}, +hl: {EL.rlen(rows) == SV.neqs(B) : Nat})
  -> M.Both({EP.rinv(bnext(b, B, e), RF.walk.next(b, rows, EL.resid(rows, e)), 0n) == True{} : Bool}, {EL.rlen(RF.walk.next(b, rows, EL.resid(rows, e))) == SV.neqs(bnext(b, B, e)) : Nat}):
  match b:
    case True{}:
      (h, hl)
    case False{}:
      (EP.new_rinv(B, rows, e, h, hl, nil_bridge(EL.resid(rows, e), Equal.sym(Bool, False{}, RF.isnilp(RF.Res.p(EL.resid(rows, e))), hb))),
       Equal.trans(Nat, EL.rlen(EL.rsnoc(rows, EL.row_of(EL.resid(rows, e)))), 1n+EL.rlen(rows), SV.neqs(EP.qsnoc(B, e)), rlen_rsnoc(rows, EL.row_of(EL.resid(rows, e))),
         Equal.trans(Nat, 1n+EL.rlen(rows), 1n+SV.neqs(B), SV.neqs(EP.qsnoc(B, e)),
           (%hl : {1n+EL.rlen(rows) == 1n+_ : Nat}
             {==}),
           Equal.sym(Nat, SV.neqs(EP.qsnoc(B, e)), 1n+SV.neqs(B), neqs_qsnoc(B, e)))))

def walk_inv(es: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, h: {EP.rinv(B, rows, 0n) == True{} : Bool}, hl: {EL.rlen(rows) == SV.neqs(B) : Nat})
  -> M.Both({EP.rinv(wB(es, rows, B), RF.Walk.rows(RF.walk(es, rows)), 0n) == True{} : Bool}, {EL.rlen(RF.Walk.rows(RF.walk(es, rows))) == SV.neqs(wB(es, rows, B)) : Nat}):
  match es:
    case Nil{}:
      (h, hl)
    case Con{+e, +t}:
      +st = step_inv(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, B, e, {==}, h, hl)
      %Equal.sym(List<&2, EL.Row>, RF.Walk.rows(RF.walk.k(RF.isnilp(RF.Res.p(EL.resid(rows, e))), RF.walk(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e))))), RF.Walk.rows(RF.walk(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)))), wk_rows(RF.isnilp(RF.Res.p(EL.resid(rows, e))), RF.walk(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)))))
        : M.Both({EP.rinv(wB(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)), bnext(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e)), _, 0n) == True{} : Bool}, {EL.rlen(_) == SV.neqs(wB(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)), bnext(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e))) : Nat})
      walk_inv(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)), bnext(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e),
        LX.both_l({EP.rinv(bnext(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e), RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)), 0n) == True{} : Bool}, {EL.rlen(RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e))) == SV.neqs(bnext(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e)) : Nat}, st),
        LX.both_r({EP.rinv(bnext(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e), RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)), 0n) == True{} : Bool}, {EL.rlen(RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e))) == SV.neqs(bnext(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e)) : Nat}, st))

# each row's recorded pivot is its largest monomial
def pvok1(r: EL.Row) -> Bool:
  match r:
    case EL.Row{p, cb, bt, pv}:
      EL.iseq(NR.mcmp(pv, EL.pivot(p)))

def pvok(rows: List<&2, EL.Row>) -> Bool:
  match rows:
    case Nil{}:
      True{}
    case Con{r, t}:
      KA.band(pvok1(r), pvok(t))

def pvok_snoc(rows: List<&2, EL.Row>, +x: EL.Row, +h: {pvok(rows) == True{} : Bool}, hx: {pvok1(x) == True{} : Bool}) -> {pvok(EL.rsnoc(rows, x)) == True{} : Bool}:
  match rows:
    case Nil{}:
      KA.band_i(pvok1(x), True{}, hx, {==})
    case Con{+r, +t}:
      KA.band_i(pvok1(r), pvok(EL.rsnoc(t, x)), KA.band_l(pvok1(r), pvok(t), h), pvok_snoc(t, x, KA.band_r(pvok1(r), pvok(t), h), hx))

def pvok_row_of(r: EL.Res) -> {pvok1(EL.row_of(r)) == True{} : Bool}:
  match r:
    case EL.Res{+p, cb, bt}:
      %RP.mcmp_refl(EL.pivot(p)) : {EL.iseq(_) == True{} : Bool}
      {==}

def pvok_next(b: Bool, +rows: List<&2, EL.Row>, +r: EL.Res, h: {pvok(rows) == True{} : Bool}) -> {pvok(RF.walk.next(b, rows, r)) == True{} : Bool}:
  match b:
    case True{}:
      h
    case False{}:
      pvok_snoc(rows, EL.row_of(r), h, pvok_row_of(r))

def pvok_walk(es: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, h: {pvok(rows) == True{} : Bool}) -> {pvok(RF.Walk.rows(RF.walk(es, rows))) == True{} : Bool}:
  match es:
    case Nil{}:
      h
    case Con{+e, +t}:
      %Equal.sym(List<&2, EL.Row>, RF.Walk.rows(RF.walk.k(RF.isnilp(RF.Res.p(EL.resid(rows, e))), RF.walk(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e))))), RF.Walk.rows(RF.walk(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)))), wk_rows(RF.isnilp(RF.Res.p(EL.resid(rows, e))), RF.walk(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e))))) : {pvok(_) == True{} : Bool}
      pvok_walk(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)), pvok_next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e), h))

# the basis is the kept equations
def qcat(B: List<&2, E.QExpr>, X: List<&2, E.QExpr>) -> List<&2, E.QExpr>:
  match B:
    case Nil{}:
      X
    case Con{b, t}:
      Con{b, qcat(t, X)}

def qcat_nil(B: List<&2, E.QExpr>) -> {B == qcat(B, Nil{}) : List<&2, E.QExpr>}:
  match B:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %qcat_nil(t) : {Con{b, t} == Con{b, _} : List<&2, E.QExpr>}
      {==}

def qcat_snoc(B: List<&2, E.QExpr>, +e: E.QExpr, +X: List<&2, E.QExpr>) -> {qcat(EP.qsnoc(B, e), X) == qcat(B, Con{e, X}) : List<&2, E.QExpr>}:
  match B:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      %qcat_snoc(t, e, X) : {Con{b, qcat(EP.qsnoc(t, e), X)} == Con{b, _} : List<&2, E.QExpr>}
      {==}

def kb(b: Bool, +B: List<&2, E.QExpr>, +e: E.QExpr, +K: List<&2, Bool>, +t: List<&2, E.QExpr>) -> {qcat(bnext(b, B, e), kept(K, t)) == qcat(B, kept(Con{RF.bnot(b), K}, Con{e, t})) : List<&2, E.QExpr>}:
  match b:
    case True{}:
      {==}
    case False{}:
      qcat_snoc(B, e, kept(K, t))

def wB_kept(es: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>) -> {wB(es, rows, B) == qcat(B, kept(RF.Walk.keep(RF.walk(es, rows)), es)) : List<&2, E.QExpr>}:
  match es:
    case Nil{}:
      qcat_nil(B)
    case Con{+e, +t}:
      %Equal.sym(List<&2, Bool>, RF.Walk.keep(RF.walk.k(RF.isnilp(RF.Res.p(EL.resid(rows, e))), RF.walk(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e))))), Con{RF.bnot(RF.isnilp(RF.Res.p(EL.resid(rows, e)))), RF.Walk.keep(RF.walk(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e))))}, wk_keep(RF.isnilp(RF.Res.p(EL.resid(rows, e))), RF.walk(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)))))
        : {wB(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)), bnext(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e)) == qcat(B, kept(_, Con{e, t})) : List<&2, E.QExpr>}
      Equal.trans(List<&2, E.QExpr>, wB(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)), bnext(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e)), qcat(bnext(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e), kept(RF.Walk.keep(RF.walk(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)))), t)), qcat(B, kept(Con{RF.bnot(RF.isnilp(RF.Res.p(EL.resid(rows, e)))), RF.Walk.keep(RF.walk(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e))))}, Con{e, t})),
        wB_kept(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)), bnext(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e)), kb(RF.isnilp(RF.Res.p(EL.resid(rows, e))), B, e, RF.Walk.keep(RF.walk(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)))), t))

def qlen_exp.c(b: Bool, +e: E.QExpr, +t: List<&2, E.QExpr>, +K: List<&2, Bool>, +cs: List<&2, S.Z>, ih: @c: List<&2, S.Z> -> {SV.qlen(RF.expand(K, t, c)) == SV.neqs(t) : Nat})
  -> {SV.qlen(RF.expand(Con{RF.bnot(b), K}, Con{e, t}, cs)) == 1n+SV.neqs(t) : Nat}:
  match b:
    case True{}:
      %ih(cs) : {1n+SV.qlen(RF.expand(K, t, cs)) == 1n+_ : Nat}
      {==}
    case False{}:
      %ih(RF.tl(cs)) : {1n+SV.qlen(RF.expand(K, t, RF.tl(cs))) == 1n+_ : Nat}
      {==}

# one multiplier per equation
def qlen_wexp(es: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +cs: List<&2, S.Z>) -> {SV.qlen(RF.expand(RF.Walk.keep(RF.walk(es, rows)), es, cs)) == SV.neqs(es) : Nat}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      %Equal.sym(List<&2, Bool>, RF.Walk.keep(RF.walk.k(RF.isnilp(RF.Res.p(EL.resid(rows, e))), RF.walk(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e))))), Con{RF.bnot(RF.isnilp(RF.Res.p(EL.resid(rows, e)))), RF.Walk.keep(RF.walk(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e))))}, wk_keep(RF.isnilp(RF.Res.p(EL.resid(rows, e))), RF.walk(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)))))
        : {SV.qlen(RF.expand(_, Con{e, t}, cs)) == 1n+SV.neqs(t) : Nat}
      qlen_exp.c(RF.isnilp(RF.Res.p(EL.resid(rows, e))), e, t, RF.Walk.keep(RF.walk(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)))), cs, c => qlen_wexp(t, RF.walk.next(RF.isnilp(RF.Res.p(EL.resid(rows, e))), rows, EL.resid(rows, e)), c))


# the walk from no rows: echelon over the kept equations
def w_rinv(+es: List<&2, E.QExpr>) -> {EP.rinv(kept(RF.Walk.keep(RF.walk(es, Nil{})), es), RF.Walk.rows(RF.walk(es, Nil{})), 0n) == True{} : Bool}:
  %wB_kept(es, Nil{}, Nil{}) : {EP.rinv(_, RF.Walk.rows(RF.walk(es, Nil{})), 0n) == True{} : Bool}
  LX.both_l({EP.rinv(wB(es, Nil{}, Nil{}), RF.Walk.rows(RF.walk(es, Nil{})), 0n) == True{} : Bool}, {EL.rlen(RF.Walk.rows(RF.walk(es, Nil{}))) == SV.neqs(wB(es, Nil{}, Nil{})) : Nat}, walk_inv(es, Nil{}, Nil{}, {==}, {==}))

def w_allok(+es: List<&2, E.QExpr>) -> {EP.allok(kept(RF.Walk.keep(RF.walk(es, Nil{})), es), RF.Walk.rows(RF.walk(es, Nil{}))) == True{} : Bool}:
  EP.rinv_allok(kept(RF.Walk.keep(RF.walk(es, Nil{})), es), RF.Walk.rows(RF.walk(es, Nil{})), 0n, w_rinv(es))

def w_pv(+es: List<&2, E.QExpr>) -> {pvok(RF.Walk.rows(RF.walk(es, Nil{}))) == True{} : Bool}:
  pvok_walk(es, Nil{}, {==})

# A constant row
# --------------

# the row the search found: a constant (pivot 1), made from the basis, its
# pivot its largest monomial
def Facts(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +j: Nat) -> Data:
  M.Both({RF.iscst(RF.Row.pv(RF.rowat(rows, j))) == True{} : Bool}, M.Both({EP.rowok(B, RF.rowat(rows, j)) == True{} : Bool}, {pvok1(RF.rowat(rows, j)) == True{} : Bool}))

def crow_shift(rows: List<&2, EL.Row>, +j: Nat) -> {RF.crow(rows, 1n+j) == RN.mapS(RF.crow(rows, j)) : Maybe<&2, Nat>}:
  match rows:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      %Equal.sym(Maybe<&2, Nat>, RF.crow(t, 2n+j), RN.mapS(RF.crow(t, 1n+j)), crow_shift(t, 1n+j)) : {SX.pick(RF.iscst(RF.Row.pv(r)), 1n+j, _) == RN.mapS(SX.pick(RF.iscst(RF.Row.pv(r)), j, RF.crow(t, 1n+j))) : Maybe<&2, Nat>}
      RN.pick_map(RF.iscst(RF.Row.pv(r)), j, RF.crow(t, 1n+j))

def crow_ok.c(b: Bool, +r: EL.Row, +t: List<&2, EL.Row>, +B: List<&2, E.QExpr>, j: Nat, hb: {b == RF.iscst(RF.Row.pv(r)) : Bool}, h: {SX.pick(b, 0n, RF.crow(t, 1n)) == Some{j} : Maybe<&2, Nat>},
  +ha: {EP.allok(B, Con{r, t}) == True{} : Bool}, +hp: {pvok(Con{r, t}) == True{} : Bool}, ih: @k: Nat -> {RF.crow(t, 0n) == Some{k} : Maybe<&2, Nat>} -> Facts(B, t, k)) -> Facts(B, Con{r, t}, j):
  match b:
    case True{}:
      %RN.some_inj(0n, j, h) : Facts(B, Con{r, t}, _)
      (Equal.sym(Bool, True{}, RF.iscst(RF.Row.pv(r)), hb), (KA.band_l(EP.rowok(B, r), EP.allok(B, t), ha), KA.band_l(pvok1(r), pvok(t), hp)))
    case False{}:
      match j:
        case 0n:
          absurd(Facts(B, Con{r, t}, 0n), RN.map_zero(RF.crow(t, 0n), (%crow_shift(t, 0n) : {_ == Some{0n} : Maybe<&2, Nat>}
            h)))
        case 1n++k:
          ih(k, RN.map_succ(RF.crow(t, 0n), k, (%crow_shift(t, 0n) : {_ == Some{1n+k} : Maybe<&2, Nat>}
            h)))

def crow_ok(rows: List<&2, EL.Row>, +B: List<&2, E.QExpr>, j: Nat, h: {RF.crow(rows, 0n) == Some{j} : Maybe<&2, Nat>}, +ha: {EP.allok(B, rows) == True{} : Bool}, +hp: {pvok(rows) == True{} : Bool}) -> Facts(B, rows, j):
  match rows:
    case Nil{}:
      absurd(Facts(B, Nil{}, j), RN.none_some(j, h))
    case Con{+r, +t}:
      crow_ok.c(RF.iscst(RF.Row.pv(r)), r, t, B, j, {==}, h, ha, hp,
        k => a => crow_ok(t, B, k, a, KA.band_r(EP.rowok(B, r), EP.allok(B, t), ha), KA.band_r(pvok1(r), pvok(t), hp)))

def lt_nil(n: List<&2, Nat>, h: {RP.islt(NR.mcmp(n, Nil{})) == True{} : Bool}) -> Empty:
  match n:
    case Nil{}:
      KA.ft(h)
    case Con{a, b}:
      KA.ft(h)

# a reduced polynomial whose largest monomial is 1 is a constant
def rconst.c(p: List<&2, R.ZTerm>, +v: Nat, +vs: List<&2, Nat>, hr: {RP.red(p) == True{} : Bool}, hp: {Nil{} == EL.pivot(p) : List<&2, Nat>}) -> {EL.cz(Con{v, vs}, p) == S.Z0{} : S.Z}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{c, n}, Nil{}}:
      %hp : {S.Z.add(EL.ifz(EL.iseq(NR.mcmp(Con{v, vs}, _)), c), S.Z0{}) == S.Z0{} : S.Z}
      {==}
    case Con{R.ZTerm{c, +n}, Con{R.ZTerm{+d, +n2}, +r2}}:
      absurd({EL.cz(Con{v, vs}, Con{R.ZTerm{c, n}, Con{R.ZTerm{d, n2}, r2}}) == S.Z0{} : S.Z},
        lt_nil(n, (%Equal.sym(List<&2, Nat>, Nil{}, EL.pivot.go(r2, n2), hp) : {RP.islt(NR.mcmp(n, _)) == True{} : Bool}
          EP.lts_pivot(r2, n, d, n2, KA.band_l(RP.mlts(n, Con{R.ZTerm{d, n2}, r2}), RP.red(Con{R.ZTerm{d, n2}, r2}),
            KA.band_r(RP.msort(n), KA.band(RP.mlts(n, Con{R.ZTerm{d, n2}, r2}), RP.red(Con{R.ZTerm{d, n2}, r2})),
              KA.band_r(RP.nz(c), KA.band(RP.msort(n), KA.band(RP.mlts(n, Con{R.ZTerm{d, n2}, r2}), RP.red(Con{R.ZTerm{d, n2}, r2}))), hr)))))))

def rconst(+p: List<&2, R.ZTerm>, hr: {RP.red(p) == True{} : Bool}, hp: {Nil{} == EL.pivot(p) : List<&2, Nat>}, m: List<&2, Nat>) -> {EL.cz(m, p) == EL.ifz(RF.iscst(m), EL.cz(Nil{}, p)) : S.Z}:
  match m:
    case Nil{}:
      {==}
    case Con{v, vs}:
      rconst.c(p, v, vs, hr, hp)

# the row's combination bt NE(B_j) + cb . NE(B) at m is the row's coefficient
def rowz(+m: List<&2, Nat>, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +B: List<&2, E.QExpr>, hs: {EP.same(p, EP.comb2(bt, SV.eqat(B, EP.vlen(cb)), cb, B)) == True{} : Bool})
  -> {EP.zdot(EL.vsnoc(cb, S.Zpos{bt}), EP.zv(m, B)) == EL.cz(m, p) : S.Z}:
  %EP.zdot_vsnoc(cb, S.Zpos{bt}, EP.zv(m, B)) : {_ == EL.cz(m, p) : S.Z}
  %EP.lookup_zv(m, B, EP.vlen(cb)) : {S.Z.add(EP.zdot(cb, EP.zv(m, B)), S.Z.mul(S.Zpos{bt}, _)) == EL.cz(m, p) : S.Z}
  %Equal.sym(S.Z, EL.cz(m, p), S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, EP.NE(SV.eqat(B, EP.vlen(cb))))), EP.zdot(cb, EP.zv(m, B))), EP.row_rel(m, p, cb, bt, B, hs))
    : {S.Z.add(EP.zdot(cb, EP.zv(m, B)), S.Z.mul(S.Zpos{bt}, EL.cz(m, EP.NE(SV.eqat(B, EP.vlen(cb)))))) == _ : S.Z}
  R.ring_eq([EP.zdot(cb, EP.zv(m, B)), S.Zpos{bt}, EL.cz(m, EP.NE(SV.eqat(B, EP.vlen(cb))))], E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{0n}}, {==})

def nsgn_mul(c: S.Z) -> {S.Z.mul(RF.nsgn(c), c) == RF.nabs(c) : S.Z}:
  match c:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      {==}
    case S.Zneg{p}:
      {==}


def zrow(+m: List<&2, Nat>, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +B: List<&2, E.QExpr>, hs: {EP.same(p, EP.comb2(bt, SV.eqat(B, EP.vlen(cb)), cb, B)) == True{} : Bool},
  hr: {RP.red(p) == True{} : Bool}, hp: {Nil{} == EL.pivot(p) : List<&2, Nat>}) -> {EP.zdot(EL.vscale(RF.nsgn(EL.cz(Nil{}, p)), EL.vsnoc(cb, S.Zpos{bt})), EP.zv(m, B)) == EL.ifz(RF.iscst(m), RF.nabs(EL.cz(Nil{}, p))) : S.Z}:
  %EP.zdot_vscale(RF.nsgn(EL.cz(Nil{}, p)), EL.vsnoc(cb, S.Zpos{bt}), EP.zv(m, B)) : {_ == EL.ifz(RF.iscst(m), RF.nabs(EL.cz(Nil{}, p))) : S.Z}
  %Equal.sym(S.Z, EP.zdot(EL.vsnoc(cb, S.Zpos{bt}), EP.zv(m, B)), EL.cz(m, p), rowz(m, p, cb, bt, B, hs)) : {S.Z.mul(RF.nsgn(EL.cz(Nil{}, p)), _) == EL.ifz(RF.iscst(m), RF.nabs(EL.cz(Nil{}, p))) : S.Z}
  %Equal.sym(S.Z, EL.cz(m, p), EL.ifz(RF.iscst(m), EL.cz(Nil{}, p)), rconst(p, hr, hp, m)) : {S.Z.mul(RF.nsgn(EL.cz(Nil{}, p)), _) == EL.ifz(RF.iscst(m), RF.nabs(EL.cz(Nil{}, p))) : S.Z}
  %Equal.sym(S.Z, S.Z.mul(RF.nsgn(EL.cz(Nil{}, p)), EL.ifz(RF.iscst(m), EL.cz(Nil{}, p))), EL.ifz(RF.iscst(m), S.Z.mul(RF.nsgn(EL.cz(Nil{}, p)), EL.cz(Nil{}, p))), CF.ifz_mul_l(RF.iscst(m), RF.nsgn(EL.cz(Nil{}, p)), EL.cz(Nil{}, p))) : {_ == EL.ifz(RF.iscst(m), RF.nabs(EL.cz(Nil{}, p))) : S.Z}
  %nsgn_mul(EL.cz(Nil{}, p)) : {EL.ifz(RF.iscst(m), S.Z.mul(RF.nsgn(EL.cz(Nil{}, p)), EL.cz(Nil{}, p))) == EL.ifz(RF.iscst(m), _) : S.Z}
  {==}

def fqs_zeros(~F: O.OField, ss: List<&2, SK.Side>, +m: List<&2, Nat>) -> {fqs(~F, RF.qzeros(ss), ss, m) == O.zero(F) : O.C(F)}:
  match ss:
    case Nil{}:
      {==}
    case Con{+s, +st}:
      %Equal.sym(O.C(F), fqs(~F, RF.qzeros(st), st, m), O.zero(F), fqs_zeros(~F, st, m)) : {O.add(F, O.mul(F, O.ofq(~F, RF.qz(S.Z0{})), O.ofq(~F, CF.coef(SV.sexpr(s), m))), _) == O.zero(F) : O.C(F)}
      FR.fring_eq(~F, [O.inv(F, O.one(F)), O.ofq(~F, CF.coef(SV.sexpr(s), m))], E.ZAdd{E.ZMul{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZVar{1n}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})

# the row's refutation, coefficient by coefficient
def hz_row(~F: O.OField, +keep: List<&2, Bool>, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +B: List<&2, E.QExpr>,
  +hB: {B == kept(keep, es) : List<&2, E.QExpr>}, +hs: {EP.same(p, EP.comb2(bt, SV.eqat(B, EP.vlen(cb)), cb, B)) == True{} : Bool},
  +hr: {RP.red(p) == True{} : Bool}, +hp: {Nil{} == EL.pivot(p) : List<&2, Nat>}, +m: List<&2, Nat>)
  -> {O.add(F, DR.fql(~F, RF.expand(keep, es, EL.vscale(RF.nsgn(EL.cz(Nil{}, p)), EL.vsnoc(cb, S.Zpos{bt}))), es, m), fqs(~F, RF.qzeros(ss), ss, m)) == O.ofq(~F, CF.coef(E.QCst{RF.qz(RF.nabs(EL.cz(Nil{}, p)))}, m)) : O.C(F)}:
  %Equal.sym(O.C(F), DR.fql(~F, RF.expand(keep, es, EL.vscale(RF.nsgn(EL.cz(Nil{}, p)), EL.vsnoc(cb, S.Zpos{bt}))), es, m), O.ofz(~F, EP.zdot(EL.vscale(RF.nsgn(EL.cz(Nil{}, p)), EL.vsnoc(cb, S.Zpos{bt})), EP.zv(m, kept(keep, es)))), fql_expand(~F, keep, es, EL.vscale(RF.nsgn(EL.cz(Nil{}, p)), EL.vsnoc(cb, S.Zpos{bt})), m))
    : {O.add(F, _, fqs(~F, RF.qzeros(ss), ss, m)) == O.ofq(~F, CF.coef(E.QCst{RF.qz(RF.nabs(EL.cz(Nil{}, p)))}, m)) : O.C(F)}
  %Equal.sym(O.C(F), fqs(~F, RF.qzeros(ss), ss, m), O.zero(F), fqs_zeros(~F, ss, m))
    : {O.add(F, O.ofz(~F, EP.zdot(EL.vscale(RF.nsgn(EL.cz(Nil{}, p)), EL.vsnoc(cb, S.Zpos{bt})), EP.zv(m, kept(keep, es)))), _) == O.ofq(~F, CF.coef(E.QCst{RF.qz(RF.nabs(EL.cz(Nil{}, p)))}, m)) : O.C(F)}
  %hB : {O.add(F, O.ofz(~F, EP.zdot(EL.vscale(RF.nsgn(EL.cz(Nil{}, p)), EL.vsnoc(cb, S.Zpos{bt})), EP.zv(m, _))), O.zero(F)) == O.ofq(~F, CF.coef(E.QCst{RF.qz(RF.nabs(EL.cz(Nil{}, p)))}, m)) : O.C(F)}
  %Equal.sym(O.C(F), O.ofq(~F, CF.coef(E.QCst{RF.qz(RF.nabs(EL.cz(Nil{}, p)))}, m)), O.ofz(~F, EL.ifz(RF.iscst(m), RF.nabs(EL.cz(Nil{}, p)))), cst_coef(~F, RF.nabs(EL.cz(Nil{}, p)), m))
    : {O.add(F, O.ofz(~F, EP.zdot(EL.vscale(RF.nsgn(EL.cz(Nil{}, p)), EL.vsnoc(cb, S.Zpos{bt})), EP.zv(m, B))), O.zero(F)) == _ : O.C(F)}
  %Equal.sym(S.Z, EP.zdot(EL.vscale(RF.nsgn(EL.cz(Nil{}, p)), EL.vsnoc(cb, S.Zpos{bt})), EP.zv(m, B)), EL.ifz(RF.iscst(m), RF.nabs(EL.cz(Nil{}, p))), zrow(m, p, cb, bt, B, hs, hr, hp))
    : {O.add(F, O.ofz(~F, _), O.zero(F)) == O.ofz(~F, EL.ifz(RF.iscst(m), RF.nabs(EL.cz(Nil{}, p)))) : O.C(F)}
  FR.fring_eq(~F, [O.ofz(~F, EL.ifz(RF.iscst(m), RF.nabs(EL.cz(Nil{}, p))))], E.ZAdd{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZVar{0n}, {==})

def qlen_qzeros(ss: List<&2, SK.Side>) -> {SV.qlen(RF.qzeros(ss)) == SV.slen(ss) : Nat}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, +st}:
      %qlen_qzeros(st) : {1n+SV.qlen(RF.qzeros(st)) == 1n+_ : Nat}
      {==}

def nonneg_qzeros(ss: List<&2, SK.Side>) -> {SV.nonneg(RF.qzeros(ss)) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, st}:
      nonneg_qzeros(st)

def nabs_neg(c: S.Z, h: {RP.nz(c) == True{} : Bool}) -> {SV.islt(S.Q.cmp(RF.qz(RF.nabs(c)), SV.qzero())) == True{} : Bool}:
  match c:
    case S.Z0{}:
      absurd({SV.islt(S.Q.cmp(RF.qz(S.Z0{}), SV.qzero())) == True{} : Bool}, KA.ft(h))
    case S.Zpos{p}:
      {==}
    case S.Zneg{p}:
      {==}

def eq_len(+a: Nat, +b: Nat, e: {a == b : Nat}) -> {SV.eq(a, b) == True{} : Bool}:
  %e : {SV.eq(a, _) == True{} : Bool}
  LI.eq_refl(a)

def row_ref.r(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +keep: List<&2, Bool>, r: EL.Row, +B: List<&2, E.QExpr>, +hB: {B == kept(keep, es) : List<&2, E.QExpr>},
  hlen: @c: List<&2, S.Z> -> {SV.qlen(RF.expand(keep, es, c)) == SV.neqs(es) : Nat},
  hc: {RF.iscst(RF.Row.pv(r)) == True{} : Bool}, hok: {EP.rowok(B, r) == True{} : Bool}, hpv: {pvok1(r) == True{} : Bool})
  -> SV.Refutes0(es, ss, RF.expand(keep, es, EL.vscale(RF.nsgn(EL.cz(Nil{}, RF.Row.p(r))), EL.vsnoc(RF.Row.cb(r), S.Zpos{RF.Row.bt(r)}))), RF.qzeros(ss), RF.qz(RF.nabs(EL.cz(Nil{}, RF.Row.p(r))))):
  match r:
    case EL.Row{+p, +cb, +bt, Nil{}}:
      +hok2 = hok
      (LI.band_i(SV.eq(SV.qlen(RF.expand(keep, es, EL.vscale(RF.nsgn(EL.cz(Nil{}, p)), EL.vsnoc(cb, S.Zpos{bt})))), SV.neqs(es)), SV.band(SV.eq(SV.qlen(RF.qzeros(ss)), SV.slen(ss)), SV.band(SV.nonneg(RF.qzeros(ss)), SV.bor(SV.islt(S.Q.cmp(RF.qz(RF.nabs(EL.cz(Nil{}, p))), SV.qzero())), SV.band(SV.iszz(S.Q.num(RF.qz(RF.nabs(EL.cz(Nil{}, p))))), SV.strict_pos(RF.qzeros(ss), ss))))),
         eq_len(SV.qlen(RF.expand(keep, es, EL.vscale(RF.nsgn(EL.cz(Nil{}, p)), EL.vsnoc(cb, S.Zpos{bt})))), SV.neqs(es), hlen(EL.vscale(RF.nsgn(EL.cz(Nil{}, p)), EL.vsnoc(cb, S.Zpos{bt})))),
         LI.band_i(SV.eq(SV.qlen(RF.qzeros(ss)), SV.slen(ss)), SV.band(SV.nonneg(RF.qzeros(ss)), SV.bor(SV.islt(S.Q.cmp(RF.qz(RF.nabs(EL.cz(Nil{}, p))), SV.qzero())), SV.band(SV.iszz(S.Q.num(RF.qz(RF.nabs(EL.cz(Nil{}, p))))), SV.strict_pos(RF.qzeros(ss), ss)))),
           eq_len(SV.qlen(RF.qzeros(ss)), SV.slen(ss), qlen_qzeros(ss)),
           LI.band_i(SV.nonneg(RF.qzeros(ss)), SV.bor(SV.islt(S.Q.cmp(RF.qz(RF.nabs(EL.cz(Nil{}, p))), SV.qzero())), SV.band(SV.iszz(S.Q.num(RF.qz(RF.nabs(EL.cz(Nil{}, p))))), SV.strict_pos(RF.qzeros(ss), ss))),
             nonneg_qzeros(ss),
             LI.bor_l(SV.islt(S.Q.cmp(RF.qz(RF.nabs(EL.cz(Nil{}, p))), SV.qzero())), SV.band(SV.iszz(S.Q.num(RF.qz(RF.nabs(EL.cz(Nil{}, p))))), SV.strict_pos(RF.qzeros(ss), ss)),
               nabs_neg(EL.cz(Nil{}, p), EP.rowok_nz(B, p, cb, bt, Nil{}, hok2)))))),
       ident_of(~QF.qfield(), RF.expand(keep, es, EL.vscale(RF.nsgn(EL.cz(Nil{}, p)), EL.vsnoc(cb, S.Zpos{bt}))), es, RF.qzeros(ss), ss, RF.qz(RF.nabs(EL.cz(Nil{}, p))),
         m => hz_row(~QF.qfield(), keep, es, ss, p, cb, bt, B, hB, EP.rowok_same(B, p, cb, bt, Nil{}, hok2), EP.rowok_red(B, p, cb, bt, Nil{}, hok2),
           NR.mcmp_eq(Nil{}, EL.pivot(p), iseq_eq(NR.mcmp(Nil{}, EL.pivot(p)), hpv)), m)))
    case EL.Row{p, cb, bt, Con{v, vs}}:
      absurd(SV.Refutes0(es, ss, RF.expand(keep, es, EL.vscale(RF.nsgn(EL.cz(Nil{}, p)), EL.vsnoc(cb, S.Zpos{bt}))), RF.qzeros(ss), RF.qz(RF.nabs(EL.cz(Nil{}, p)))), KA.ft(hc))

# The simplex's certificate
# -------------------------

def qlen_ineqs(+ys: List<&2, List<&2, Nat>>, +rows: List<&2, EL.Row>, ss: List<&2, SK.Side>) -> {SX.qlen(RF.ineqs(ys, RF.sres(rows, ss), ss)) == SV.slen(ss) : Nat}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, +st}:
      %qlen_ineqs(ys, rows, st) : {1n+SX.qlen(RF.ineqs(ys, RF.sres(rows, st), st)) == 1n+_ : Nat}
      {==}

def reslen_sres(+rows: List<&2, EL.Row>, ss: List<&2, SK.Side>) -> {RF.reslen(RF.sres(rows, ss)) == SV.slen(ss) : Nat}:
  match ss:
    case Nil{}:
      {==}
    case Con{s, +st}:
      %reslen_sres(rows, st) : {1n+RF.reslen(RF.sres(rows, st)) == 1n+_ : Nat}
      {==}

def qlen_smults(mu: List<&2, S.Z>, +rows: List<&2, EL.Row>, ss: List<&2, SK.Side>, h: {KA.nateq(SX.vlen(mu), SV.slen(ss)) == True{} : Bool}) -> {SV.qlen(RF.smults(mu, RF.sres(rows, ss), ss)) == SV.slen(ss) : Nat}:
  match mu ss:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{s, st}:
      absurd({0n == 1n+SV.slen(st) : Nat}, KA.ft(h))
    case Con{u, ut} Nil{}:
      absurd({SV.qlen(RF.smults(Con{u, ut}, Nil{}, Nil{})) == 0n : Nat}, KA.ft(h))
    case Con{u, +ut} Con{+s, +st}:
      %qlen_smults(ut, rows, st, h) : {1n+SV.qlen(RF.smults(ut, RF.sres(rows, st), st)) == 1n+_ : Nat}
      {==}

def nn_entry(u: S.Z, +q: S.Pos, hu: {UN.nn(u) == True{} : Bool}) -> {SV.bnot(SV.islt(S.Q.cmp(RF.qz(S.Z.mul(u, S.Zpos{q})), SV.qzero()))) == True{} : Bool}:
  match u:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      {==}
    case S.Zneg{p}:
      absurd({SV.bnot(SV.islt(S.Q.cmp(RF.qz(S.Z.mul(S.Zneg{p}, S.Zpos{q})), SV.qzero()))) == True{} : Bool}, KA.ft(hu))

def nn_smults(mu: List<&2, S.Z>, rs: List<&2, EL.Res>, ss: List<&2, SK.Side>, h: {UN.znn(mu) == True{} : Bool}) -> {SV.nonneg(RF.smults(mu, rs, ss)) == True{} : Bool}:
  match mu rs ss:
    case Nil{} rs ss:
      {==}
    case Con{u, ut} Nil{} ss:
      {==}
    case Con{u, ut} Con{r, rt} Nil{}:
      {==}
    case Con{+u, +ut} Con{+r, +rt} Con{+s, +st}:
      +h2 = h
      LI.band_i(SV.bnot(SV.islt(S.Q.cmp(RF.qz(S.Z.mul(u, S.Zpos{S.Pos.mul(RF.Res.bt(r), QN.den(RF.sexpr(s)))})), SV.qzero()))), SV.nonneg(RF.smults(ut, rt, st)),
        nn_entry(u, S.Pos.mul(RF.Res.bt(r), QN.den(RF.sexpr(s))), KA.band_l(UN.nn(u), UN.znn(ut), h2)),
        nn_smults(ut, rt, st, KA.band_r(UN.nn(u), UN.znn(ut), h2)))

def bcol_ksum(mu: List<&2, S.Z>, +rows: List<&2, EL.Row>, ss: List<&2, SK.Side>, +ys: List<&2, List<&2, Nat>>) -> {SX.dot(mu, UN.bcol(RF.ineqs(ys, RF.sres(rows, ss), ss))) == RF.ksum(mu, RF.sres(rows, ss)) : S.Z}:
  match mu ss:
    case Nil{} +ss:
      Equal.sym(S.Z, S.Z0{}, SX.dot(Nil{}, UN.bcol(RF.ineqs(ys, RF.sres(rows, ss), ss))), UN.dot_nil_l(UN.bcol(RF.ineqs(ys, RF.sres(rows, ss), ss))))
    case Con{u, ut} Nil{}:
      {==}
    case Con{+u, +ut} Con{+s, +st}:
      %bcol_ksum(ut, rows, st, ys) : {S.Z.add(S.Z.mul(u, EL.cz(Nil{}, RF.Res.p(EL.resid(rows, RF.sexpr(s))))), SX.dot(ut, UN.bcol(RF.ineqs(ys, RF.sres(rows, st), st))))
        == S.Z.add(S.Z.mul(u, EL.cz(Nil{}, RF.Res.p(EL.resid(rows, RF.sexpr(s))))), _) : S.Z}
      {==}

def sp.g(u: S.Z, +q: S.Pos, +D: S.Z, +mt: List<&2, S.Q>, +st: List<&2, SK.Side>, hu: {UN.nn(u) == True{} : Bool},
  hs: {SX.islt(S.Z.cmp(S.Z0{}, S.Z.add(S.Z.mul(u, S.Zpos{S.XH{}}), D))) == True{} : Bool}, ih: {SX.islt(S.Z.cmp(S.Z0{}, D)) == True{} : Bool} -> {SV.strict_pos(mt, st) == True{} : Bool})
  -> {SV.bor(SV.islt(S.Q.cmp(SV.qzero(), RF.qz(S.Z.mul(u, S.Zpos{q})))), SV.strict_pos(mt, st)) == True{} : Bool}:
  match u:
    case S.Z0{}:
      LI.bor_r(SV.islt(S.Q.cmp(SV.qzero(), RF.qz(S.Z0{}))), SV.strict_pos(mt, st), ih(hs))
    case S.Zpos{p}:
      {==}
    case S.Zneg{p}:
      absurd({SV.bor(SV.islt(S.Q.cmp(SV.qzero(), RF.qz(S.Z.mul(S.Zneg{p}, S.Zpos{q})))), SV.strict_pos(mt, st)) == True{} : Bool}, KA.ft(hu))

def sp.c(s: SK.Side, +u: S.Z, +q: S.Pos, +D: S.Z, +mt: List<&2, S.Q>, +st: List<&2, SK.Side>, hu: {UN.nn(u) == True{} : Bool},
  hs: {SX.islt(S.Z.cmp(S.Z0{}, S.Z.add(S.Z.mul(u, SX.ind(RF.strict(s))), D))) == True{} : Bool}, ih: {SX.islt(S.Z.cmp(S.Z0{}, D)) == True{} : Bool} -> {SV.strict_pos(mt, st) == True{} : Bool})
  -> {SV.strict_pos(Con{RF.qz(S.Z.mul(u, S.Zpos{q})), mt}, Con{s, st}) == True{} : Bool}:
  match s:
    case SK.Gt0{e}:
      sp.g(u, q, D, mt, st, hu, hs, ih)
    case SK.Ge0{e}:
      ih((%Equal.sym(S.Z, S.Z0{}, S.Z.mul(u, S.Z0{}), ZL.mul_zero(u)) : {SX.islt(S.Z.cmp(S.Z0{}, S.Z.add(_, D))) == True{} : Bool}
        hs))

# sum mu_k [s_k strict] > 0: a strict side has a positive multiplier
def sp_of(mu: List<&2, S.Z>, ss: List<&2, SK.Side>, +rows: List<&2, EL.Row>, +ys: List<&2, List<&2, Nat>>, hn: {UN.znn(mu) == True{} : Bool},
  hs: {SX.islt(S.Z.cmp(S.Z0{}, SX.dot(mu, UN.scol(RF.ineqs(ys, RF.sres(rows, ss), ss))))) == True{} : Bool}) -> {SV.strict_pos(RF.smults(mu, RF.sres(rows, ss), ss), ss) == True{} : Bool}:
  match mu ss:
    case Nil{} +ss:
      absurd({SV.strict_pos(Nil{}, ss) == True{} : Bool}, KA.ft((%Equal.sym(S.Z, S.Z0{}, SX.dot(Nil{}, UN.scol(RF.ineqs(ys, RF.sres(rows, ss), ss))), UN.dot_nil_l(UN.scol(RF.ineqs(ys, RF.sres(rows, ss), ss)))) : {SX.islt(S.Z.cmp(S.Z0{}, _)) == True{} : Bool}
        hs)))
    case Con{u, ut} Nil{}:
      absurd({SV.strict_pos(RF.smults(Con{u, ut}, Nil{}, Nil{}), Nil{}) == True{} : Bool}, KA.ft(hs))
    case Con{+u, +ut} Con{+s, +st}:
      +hn2 = hn
      sp.c(s, u, S.Pos.mul(RF.Res.bt(EL.resid(rows, RF.sexpr(s))), QN.den(RF.sexpr(s))), SX.dot(ut, UN.scol(RF.ineqs(ys, RF.sres(rows, st), st))), RF.smults(ut, RF.sres(rows, st), st), st,
        KA.band_l(UN.nn(u), UN.znn(ut), hn2), hs, a => sp_of(ut, st, rows, ys, KA.band_r(UN.nn(u), UN.znn(ut), hn2), a))

# K < 0, or K = 0 and a strict side weighted positively
def lex_ref.go(o: Cmp, +K: S.Z, +T: S.Z, +SP: Bool, ho: {S.Z.cmp(K, S.Z0{}) == o : Cmp}, h: {SX.lexlt.go(o, S.Z0{}, T) == True{} : Bool},
  hsp: {SX.islt(S.Z.cmp(S.Z0{}, T)) == True{} : Bool} -> {SP == True{} : Bool}) -> {SV.bor(SV.islt(S.Q.cmp(RF.qz(K), SV.qzero())), SV.band(SV.iszz(K), SP)) == True{} : Bool}:
  match o:
    case LT{}:
      %ZL.mul_one(K) : {SV.bor(SV.islt(S.Z.cmp(_, S.Z0{})), SV.band(SV.iszz(K), SP)) == True{} : Bool}
      %Equal.sym(Cmp, S.Z.cmp(K, S.Z0{}), LT{}, ho) : {SV.bor(SV.islt(_), SV.band(SV.iszz(K), SP)) == True{} : Bool}
      {==}
    case EQ{}:
      %Equal.sym(S.Z, K, S.Z0{}, ZO.sub_eq(K, S.Z0{}, ZO.eq_zero(K, S.Z0{}, ho))) : {SV.bor(SV.islt(S.Q.cmp(RF.qz(_), SV.qzero())), SV.band(SV.iszz(_), SP)) == True{} : Bool}
      hsp(h)
    case GT{}:
      absurd({SV.bor(SV.islt(S.Q.cmp(RF.qz(K), SV.qzero())), SV.band(SV.iszz(K), SP)) == True{} : Bool}, KA.ft(h))


# (unsat_cols holds in every ordered field; it is read in lib/lqfield.bend's,
# which checks far faster than qfield's)
def pv.c(mi: Maybe<&2, Nat>, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +t: SX.Tab, +i: Nat, +h: {SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)) == SX.Unsat{t, i} : SX.Run}, +v: Nat, +vs: List<&2, Nat>, hmi: {mi == midx(Con{v, vs}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})) : Maybe<&2, Nat>})
  -> {pdot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Con{v, vs}) == S.Z0{} : S.Z}:
  match mi:
    case None{}:
      pdot_notin(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), v, vs, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), covall_self(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), midx_none(Con{v, vs}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), Equal.sym(Maybe<&2, Nat>, None{}, midx(Con{v, vs}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})), hmi)))
    case Some{+l}:
      +hs = midx_some(Con{v, vs}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), l, Equal.sym(Maybe<&2, Nat>, Some{l}, midx(Con{v, vs}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})), hmi))
      Equal.trans(S.Z, pdot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Con{v, vs}), SX.dot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), UN.acol(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), l)), S.Z0{},
        Equal.sym(S.Z, SX.dot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), UN.acol(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), l)), pdot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Con{v, vs}),
          acol_pdot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), ss, RF.Walk.rows(RF.walk(es, Nil{})), RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), l, Con{v, vs}, LX.both_r({mnth(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), l) == Con{v, vs} : List<&2, Nat>}, {SX.ltn(l, RF.mlen(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}))) == True{} : Bool}, hs),
            LX.both_l({mnth(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), l) == Con{v, vs} : List<&2, Nat>}, {SX.ltn(l, RF.mlen(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}))) == True{} : Bool}, hs))),
        UN.unsat_cols(~LQF.lqfield(), RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), t, i, h, l, LX.both_r({mnth(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), l) == Con{v, vs} : List<&2, Nat>}, {SX.ltn(l, RF.mlen(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}))) == True{} : Bool}, hs)))

# sum_k mu_k p_k is K at 1 and 0 elsewhere
def pdot_val(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +t: SX.Tab, +i: Nat, +h: {SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)) == SX.Unsat{t, i} : SX.Run}, m: List<&2, Nat>) -> {pdot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), m) == EL.ifz(RF.iscst(m), RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss))) : S.Z}:
  match m:
    case Nil{}:
      pdot_ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss))
    case Con{+v, +vs}:
      pv.c(midx(Con{v, vs}, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})), es, ss, t, i, h, v, vs, {==})

def hz_lp(~F: O.OField, +es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +t: SX.Tab, +i: Nat, +h: {SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)) == SX.Unsat{t, i} : SX.Run}, +m: List<&2, Nat>)
  -> {O.add(F, DR.fql(~F, RF.expand(RF.Walk.keep(RF.walk(es, Nil{})), es, RF.cbsum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss))), es, m), fqs(~F, RF.smults(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), ss, m)) == O.ofq(~F, CF.coef(E.QCst{RF.qz(RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)))}, m)) : O.C(F)}:
  %Equal.sym(O.C(F), DR.fql(~F, RF.expand(RF.Walk.keep(RF.walk(es, Nil{})), es, RF.cbsum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss))), es, m), O.ofz(~F, EP.zdot(RF.cbsum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)), EP.zv(m, kept(RF.Walk.keep(RF.walk(es, Nil{})), es)))), fql_expand(~F, RF.Walk.keep(RF.walk(es, Nil{})), es, RF.cbsum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)), m))
    : {O.add(F, _, fqs(~F, RF.smults(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), ss, m)) == O.ofq(~F, CF.coef(E.QCst{RF.qz(RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)))}, m)) : O.C(F)}
  %Equal.sym(O.C(F), fqs(~F, RF.smults(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), ss, m), O.ofz(~F, sdot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss, m)), fqs_smults(~F, RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss, m))
    : {O.add(F, O.ofz(~F, EP.zdot(RF.cbsum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)), EP.zv(m, kept(RF.Walk.keep(RF.walk(es, Nil{})), es)))), _) == O.ofq(~F, CF.coef(E.QCst{RF.qz(RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)))}, m)) : O.C(F)}
  %Equal.sym(O.C(F), O.add(F, O.ofz(~F, EP.zdot(RF.cbsum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)), EP.zv(m, kept(RF.Walk.keep(RF.walk(es, Nil{})), es)))), O.ofz(~F, sdot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss, m))), O.ofz(~F, S.Z.add(EP.zdot(RF.cbsum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)), EP.zv(m, kept(RF.Walk.keep(RF.walk(es, Nil{})), es))), sdot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss, m))),
      FR.ofz_add(~F, EP.zdot(RF.cbsum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)), EP.zv(m, kept(RF.Walk.keep(RF.walk(es, Nil{})), es))), sdot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss, m)))
    : {_ == O.ofq(~F, CF.coef(E.QCst{RF.qz(RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)))}, m)) : O.C(F)}
  %Equal.sym(S.Z, S.Z.add(EP.zdot(RF.cbsum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)), EP.zv(m, kept(RF.Walk.keep(RF.walk(es, Nil{})), es))), sdot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss, m)), pdot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), m), lp_rel(m, RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), ss, RF.Walk.rows(RF.walk(es, Nil{})), kept(RF.Walk.keep(RF.walk(es, Nil{})), es), w_allok(es)))
    : {O.ofz(~F, _) == O.ofq(~F, CF.coef(E.QCst{RF.qz(RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)))}, m)) : O.C(F)}
  %Equal.sym(O.C(F), O.ofq(~F, CF.coef(E.QCst{RF.qz(RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)))}, m)), O.ofz(~F, EL.ifz(RF.iscst(m), RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)))), cst_coef(~F, RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)), m))
    : {O.ofz(~F, pdot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), m)) == _ : O.C(F)}
  %pdot_val(es, ss, t, i, h, m) : {O.ofz(~F, pdot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), m)) == O.ofz(~F, _) : O.C(F)}
  {==}

def lp_refq(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, +t: SX.Tab, +i: Nat, +h: {SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)) == SX.Unsat{t, i} : SX.Run})
  -> SV.Refutes0(es, ss, RF.expand(RF.Walk.keep(RF.walk(es, Nil{})), es, RF.cbsum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss))), RF.smults(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), RF.qz(RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)))):
  (LI.band_i(SV.eq(SV.qlen(RF.expand(RF.Walk.keep(RF.walk(es, Nil{})), es, RF.cbsum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)))), SV.neqs(es)), SV.band(SV.eq(SV.qlen(RF.smults(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SV.slen(ss)), SV.band(SV.nonneg(RF.smults(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SV.bor(SV.islt(S.Q.cmp(RF.qz(RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss))), SV.qzero())), SV.band(SV.iszz(RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss))), SV.strict_pos(RF.smults(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), ss))))),
     eq_len(SV.qlen(RF.expand(RF.Walk.keep(RF.walk(es, Nil{})), es, RF.cbsum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)))), SV.neqs(es), qlen_wexp(es, Nil{}, RF.cbsum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)))),
     LI.band_i(SV.eq(SV.qlen(RF.smults(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SV.slen(ss)), SV.band(SV.nonneg(RF.smults(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SV.bor(SV.islt(S.Q.cmp(RF.qz(RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss))), SV.qzero())), SV.band(SV.iszz(RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss))), SV.strict_pos(RF.smults(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), ss)))),
       eq_len(SV.qlen(RF.smults(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SV.slen(ss), qlen_smults(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.Walk.rows(RF.walk(es, Nil{})), ss, KA.nateq_of(SX.vlen(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n)), SV.slen(ss),
         Equal.trans(Nat, SX.vlen(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SV.slen(ss), UN.vlen_mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), qlen_ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.Walk.rows(RF.walk(es, Nil{})), ss))))),
       LI.band_i(SV.nonneg(RF.smults(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SV.bor(SV.islt(S.Q.cmp(RF.qz(RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss))), SV.qzero())), SV.band(SV.iszz(RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss))), SV.strict_pos(RF.smults(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), ss))),
         nn_smults(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss, UN.unsat_nn(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), t, i, h)),
         lex_ref.go(S.Z.cmp(RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)), S.Z0{}), RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)), SX.dot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), UN.scol(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss))), SV.strict_pos(RF.smults(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), ss), {==},
           (%bcol_ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.Walk.rows(RF.walk(es, Nil{})), ss, RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{})) : {SX.lexlt(_, S.Z0{}, S.Z0{}, SX.dot(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), UN.scol(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)))) == True{} : Bool}
             UN.unsat_lex(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), t, i, h)),
           a => sp_of(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), ss, RF.Walk.rows(RF.walk(es, Nil{})), RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), UN.unsat_nn(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), t, i, h), a))))),
   ident_of(~QF.qfield(), RF.expand(RF.Walk.keep(RF.walk(es, Nil{})), es, RF.cbsum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss))), es, RF.smults(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), ss, RF.qz(RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss))),
     m => hz_lp(~QF.qfield(), es, ss, t, i, h, m)))

# Every certificate refute returns is a refutation
# ------------------------------------------------

def CertOk(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, mc: Maybe<&2, RF.Cert>) -> Type:
  match mc:
    case None{}:
      Unit
    case Some{RF.Cert{ls, ms, k}}:
      SV.Refutes0(es, ss, ls, ms, k)


def sound.r(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, r: SX.Run, hr: {r == SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)) : SX.Run}) -> CertOk(es, ss, RF.cert.run(RF.Walk.keep(RF.walk(es, Nil{})), es, ss, RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), r)):
  match r:
    case SX.Go{t}:
      Unit{}
    case SX.Sat{t}:
      Unit{}
    case SX.Unsat{+t, +i}:
      %Equal.trans(Nat, SX.qlen(RF.ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), SV.slen(ss), RF.reslen(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)), qlen_ineqs(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.Walk.rows(RF.walk(es, Nil{})), ss), Equal.sym(Nat, RF.reslen(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)), SV.slen(ss), reslen_sres(RF.Walk.rows(RF.walk(es, Nil{})), ss)))
        : SV.Refutes0(es, ss, RF.expand(RF.Walk.keep(RF.walk(es, Nil{})), es, RF.cbsum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), _, 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss))), RF.smults(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), _, 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss), RF.qz(RF.ksum(RF.mults(SX.Rw.m(SX.rowat(SX.Tab.rows(t), i)), i, SX.Rw.d(SX.rowat(SX.Tab.rows(t), i)), _, 0n), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss))))
      lp_refq(es, ss, t, i, Equal.sym(SX.Run, SX.Unsat{t, i}, SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), hr))

def sound.c(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>, mj: Maybe<&2, Nat>, hmj: {mj == RF.crow(RF.Walk.rows(RF.walk(es, Nil{})), 0n) : Maybe<&2, Nat>}) -> CertOk(es, ss, RF.cert(es, ss, RF.decide.c(RF.walk(es, Nil{}), mj, ss))):
  match mj:
    case Some{+j}:
      +fa = crow_ok(RF.Walk.rows(RF.walk(es, Nil{})), kept(RF.Walk.keep(RF.walk(es, Nil{})), es), j, Equal.sym(Maybe<&2, Nat>, Some{j}, RF.crow(RF.Walk.rows(RF.walk(es, Nil{})), 0n), hmj), w_allok(es), w_pv(es))
      row_ref.r(es, ss, RF.Walk.keep(RF.walk(es, Nil{})), RF.rowat(RF.Walk.rows(RF.walk(es, Nil{})), j), kept(RF.Walk.keep(RF.walk(es, Nil{})), es), {==}, c => qlen_wexp(es, Nil{}, c),
        LX.both_l({RF.iscst(RF.Row.pv(RF.rowat(RF.Walk.rows(RF.walk(es, Nil{})), j))) == True{} : Bool}, M.Both({EP.rowok(kept(RF.Walk.keep(RF.walk(es, Nil{})), es), RF.rowat(RF.Walk.rows(RF.walk(es, Nil{})), j)) == True{} : Bool}, {pvok1(RF.rowat(RF.Walk.rows(RF.walk(es, Nil{})), j)) == True{} : Bool}), fa),
        LX.both_l({EP.rowok(kept(RF.Walk.keep(RF.walk(es, Nil{})), es), RF.rowat(RF.Walk.rows(RF.walk(es, Nil{})), j)) == True{} : Bool}, {pvok1(RF.rowat(RF.Walk.rows(RF.walk(es, Nil{})), j)) == True{} : Bool},
          LX.both_r({RF.iscst(RF.Row.pv(RF.rowat(RF.Walk.rows(RF.walk(es, Nil{})), j))) == True{} : Bool}, M.Both({EP.rowok(kept(RF.Walk.keep(RF.walk(es, Nil{})), es), RF.rowat(RF.Walk.rows(RF.walk(es, Nil{})), j)) == True{} : Bool}, {pvok1(RF.rowat(RF.Walk.rows(RF.walk(es, Nil{})), j)) == True{} : Bool}), fa)),
        LX.both_r({EP.rowok(kept(RF.Walk.keep(RF.walk(es, Nil{})), es), RF.rowat(RF.Walk.rows(RF.walk(es, Nil{})), j)) == True{} : Bool}, {pvok1(RF.rowat(RF.Walk.rows(RF.walk(es, Nil{})), j)) == True{} : Bool},
          LX.both_r({RF.iscst(RF.Row.pv(RF.rowat(RF.Walk.rows(RF.walk(es, Nil{})), j))) == True{} : Bool}, M.Both({EP.rowok(kept(RF.Walk.keep(RF.walk(es, Nil{})), es), RF.rowat(RF.Walk.rows(RF.walk(es, Nil{})), j)) == True{} : Bool}, {pvok1(RF.rowat(RF.Walk.rows(RF.walk(es, Nil{})), j)) == True{} : Bool}), fa)))
    case None{}:
      sound.r(es, ss, SX.solve(RF.mklp(RF.ymons(RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), Nil{}), RF.sres(RF.Walk.rows(RF.walk(es, Nil{})), ss), ss)), {==})

# refute's certificates are Motzkin refutations of es and ss
def refute_sound(+es: List<&2, E.QExpr>, +ss: List<&2, SK.Side>) -> CertOk(es, ss, RF.refute(es, ss)):
  sound.c(es, ss, RF.crow(RF.Walk.rows(RF.walk(es, Nil{})), 0n), {==})
