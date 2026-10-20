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
