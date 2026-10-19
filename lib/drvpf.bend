# bend-cad: what a residual says about derivability (PLAN-sk13a S2). The
# basis B, the rows and the residual r = EL.resid(rows, e) are as in
# lib/elimpf.bend: at every monomial, r.p = bt NE(e) + cb . NE(B).
# - r.p is 0: e is a constant combination of B (drop_ident), with the
#   multipliers dropls(cb, bt, e, B), l_k = -cb_k den(B_k) / (bt den(e)).
# - r.p is not 0: e is no constant combination of B (indep, further
#   below).
# The coefficient arithmetic runs in an ordered field through ofq (the
# canonical rationals for the spec's Ident). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/solve.bend as SV
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./qemb.bend as QE
import ./qfield.bend as QF
import ./qnorm.bend as QN
import ./zring.bend as R
import ./zlaws.bend as ZL
import ./karith.bend as KA
import ./redpoly.bend as RP
import ./identpf.bend as ID
import ./elim.bend as EL
import ./coefpf.bend as CF
import ./elimpf.bend as EP

def absurd(-A: Type, x: Empty) -> A:
  match x:

# The drop's multipliers
# ----------------------

def dropls(cb: List<&2, S.Z>, +bt: S.Pos, +e: E.QExpr, B: List<&2, E.QExpr>) -> List<&2, S.Q>:
  match cb B:
    case Nil{} Nil{}:
      Nil{}
    case Nil{} Con{b, bs}:
      Nil{}
    case Con{c, ct} Nil{}:
      Nil{}
    case Con{c, ct} Con{b, bs}:
      Con{S.Q{S.Z.mul(S.Z.neg(c), S.Zpos{QN.den(b)}), S.Pos.mul(bt, QN.den(e))}, dropls(ct, bt, e, bs)}

# qlin read in F
def fql(~F: O.OField, ls: List<&2, S.Q>, B: List<&2, E.QExpr>, +m: List<&2, Nat>) -> O.C(F):
  match ls B:
    case Nil{} Nil{}:
      O.zero(F)
    case Nil{} Con{b, bs}:
      O.zero(F)
    case Con{l, lt} Nil{}:
      O.zero(F)
    case Con{l, lt} Con{b, bs}:
      O.add(F, O.mul(F, O.ofq(~F, l), O.ofq(~F, CF.coef(b, m))), fql(~F, lt, bs, m))

def ofq_qlin(~F: O.OField, ls: List<&2, S.Q>, B: List<&2, E.QExpr>, +m: List<&2, Nat>) -> {fql(~F, ls, B, m) == O.ofq(~F, CF.qlin(ls, B, m)) : O.C(F)}:
  match ls B:
    case Nil{} Nil{}:
      Equal.sym(O.C(F), O.ofq(~F, S.Q{S.Z0{}, S.XH{}}), O.zero(F), QE.ofq_zero(~F))
    case Nil{} Con{b, bs}:
      Equal.sym(O.C(F), O.ofq(~F, S.Q{S.Z0{}, S.XH{}}), O.zero(F), QE.ofq_zero(~F))
    case Con{l, lt} Nil{}:
      Equal.sym(O.C(F), O.ofq(~F, S.Q{S.Z0{}, S.XH{}}), O.zero(F), QE.ofq_zero(~F))
    case Con{+l, +lt} Con{+b, +bs}:
      %Equal.sym(O.C(F), O.ofq(~F, S.Q.add(S.Q.mul(l, CF.coef(b, m)), CF.qlin(lt, bs, m))), O.add(F, O.ofq(~F, S.Q.mul(l, CF.coef(b, m))), O.ofq(~F, CF.qlin(lt, bs, m))),
          QE.ofq_add(~F, S.Q.mul(l, CF.coef(b, m)), CF.qlin(lt, bs, m))) : {fql(~F, Con{l, lt}, Con{b, bs}, m) == _ : O.C(F)}
      %Equal.sym(O.C(F), O.ofq(~F, S.Q.mul(l, CF.coef(b, m))), O.mul(F, O.ofq(~F, l), O.ofq(~F, CF.coef(b, m))), QE.ofq_mul(~F, l, CF.coef(b, m)))
        : {fql(~F, Con{l, lt}, Con{b, bs}, m) == O.add(F, _, O.ofq(~F, CF.qlin(lt, bs, m))) : O.C(F)}
      %ofq_qlin(~F, lt, bs, m) : {fql(~F, Con{l, lt}, Con{b, bs}, m) == O.add(F, O.mul(F, O.ofq(~F, l), O.ofq(~F, CF.coef(b, m))), _) : O.C(F)}
      {==}

# a d / q times z / d is a z / q
def cancel(~F: O.OField, +a: S.Z, +d: S.Pos, +q: S.Pos, +z: S.Z) -> {O.mul(F, O.ofq(~F, S.Q{S.Z.mul(a, S.Zpos{d}), q}), O.ofq(~F, S.Q{z, d})) == O.ofq(~F, S.Q{S.Z.mul(a, z), q}) : O.C(F)}:
  %FR.ofz_mul(~F, a, S.Zpos{d}) : {O.mul(F, O.mul(F, _, O.inv(F, O.ofp(~F, q))), O.mul(F, O.ofz(~F, z), O.inv(F, O.ofp(~F, d)))) == O.ofq(~F, S.Q{S.Z.mul(a, z), q}) : O.C(F)}
  %FR.ofz_mul(~F, a, z) : {O.mul(F, O.mul(F, O.mul(F, O.ofz(~F, a), O.ofp(~F, d)), O.inv(F, O.ofp(~F, q))), O.mul(F, O.ofz(~F, z), O.inv(F, O.ofp(~F, d)))) == O.mul(F, _, O.inv(F, O.ofp(~F, q))) : O.C(F)}
  FO.eq_of_sub(~F, O.mul(F, O.mul(F, O.mul(F, O.ofz(~F, a), O.ofp(~F, d)), O.inv(F, O.ofp(~F, q))), O.mul(F, O.ofz(~F, z), O.inv(F, O.ofp(~F, d)))),
    O.mul(F, O.mul(F, O.ofz(~F, a), O.ofz(~F, z)), O.inv(F, O.ofp(~F, q))),
    FO.cert1(~F, O.sub(~F, O.mul(F, O.mul(F, O.mul(F, O.ofz(~F, a), O.ofp(~F, d)), O.inv(F, O.ofp(~F, q))), O.mul(F, O.ofz(~F, z), O.inv(F, O.ofp(~F, d)))),
        O.mul(F, O.mul(F, O.ofz(~F, a), O.ofz(~F, z)), O.inv(F, O.ofp(~F, q)))),
      O.mul(F, O.mul(F, O.ofz(~F, a), O.ofz(~F, z)), O.inv(F, O.ofp(~F, q))), O.sub(~F, O.mul(F, O.ofp(~F, d), O.inv(F, O.ofp(~F, d))), O.one(F)),
      FR.fring_eq(~F, [O.ofz(~F, a), O.ofp(~F, d), O.inv(F, O.ofp(~F, q)), O.ofz(~F, z), O.inv(F, O.ofp(~F, d))],
        E.ZSub{E.ZMul{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZMul{E.ZVar{3n}, E.ZVar{4n}}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZVar{2n}}},
        E.ZMul{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZVar{2n}}, E.ZSub{E.ZMul{E.ZVar{1n}, E.ZVar{4n}}, E.ZCst{S.Zpos{S.XH{}}}}}, {==}),
      QE.ofp_rel(~F, d)))

# the drop multipliers against the basis: -(cb . zv(m, B)) / (bt den(e))
def drop_sum(~F: O.OField, cb: List<&2, S.Z>, +bt: S.Pos, +e: E.QExpr, B: List<&2, E.QExpr>, +m: List<&2, Nat>)
  -> {fql(~F, dropls(cb, bt, e, B), B, m) == O.neg(F, O.mul(F, O.ofz(~F, EP.zdot(cb, EP.zv(m, B))), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e)))))) : O.C(F)}:
  match cb B:
    case Nil{} Nil{}:
      %Equal.sym(O.C(F), O.mul(F, O.zero(F), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e))))), O.zero(F), FL.zero_mul(~F, O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e))))))
        : {O.zero(F) == O.neg(F, _) : O.C(F)}
      FL.neg_zero(~F)
    case Nil{} Con{b, bs}:
      %Equal.sym(O.C(F), O.mul(F, O.zero(F), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e))))), O.zero(F), FL.zero_mul(~F, O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e))))))
        : {O.zero(F) == O.neg(F, _) : O.C(F)}
      FL.neg_zero(~F)
    case Con{c, ct} Nil{}:
      %Equal.sym(O.C(F), O.mul(F, O.zero(F), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e))))), O.zero(F), FL.zero_mul(~F, O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e))))))
        : {O.zero(F) == O.neg(F, _) : O.C(F)}
      FL.neg_zero(~F)
    case Con{+c, +ct} Con{+b, +bs}:
      %Equal.sym(O.C(F), O.mul(F, O.ofq(~F, S.Q{S.Z.mul(S.Z.neg(c), S.Zpos{QN.den(b)}), S.Pos.mul(bt, QN.den(e))}), O.ofq(~F, CF.coef(b, m))),
          O.ofq(~F, S.Q{S.Z.mul(S.Z.neg(c), EL.cz(m, EP.NE(b))), S.Pos.mul(bt, QN.den(e))}),
          cancel(~F, S.Z.neg(c), QN.den(b), S.Pos.mul(bt, QN.den(e)), EL.cz(m, EP.NE(b))))
        : {O.add(F, _, fql(~F, dropls(ct, bt, e, bs), bs, m)) == O.neg(F, O.mul(F, O.ofz(~F, EP.zdot(Con{c, ct}, EP.zv(m, Con{b, bs}))), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e)))))) : O.C(F)}
      %Equal.sym(O.C(F), fql(~F, dropls(ct, bt, e, bs), bs, m), O.neg(F, O.mul(F, O.ofz(~F, EP.zdot(ct, EP.zv(m, bs))), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e)))))), drop_sum(~F, ct, bt, e, bs, m))
        : {O.add(F, O.ofq(~F, S.Q{S.Z.mul(S.Z.neg(c), EL.cz(m, EP.NE(b))), S.Pos.mul(bt, QN.den(e))}), _) == O.neg(F, O.mul(F, O.ofz(~F, EP.zdot(Con{c, ct}, EP.zv(m, Con{b, bs}))), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e)))))) : O.C(F)}
      %FR.ofz_add(~F, S.Z.mul(c, EL.cz(m, EP.NE(b))), EP.zdot(ct, EP.zv(m, bs)))
        : {O.add(F, O.ofq(~F, S.Q{S.Z.mul(S.Z.neg(c), EL.cz(m, EP.NE(b))), S.Pos.mul(bt, QN.den(e))}), O.neg(F, O.mul(F, O.ofz(~F, EP.zdot(ct, EP.zv(m, bs))), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e)))))))
          == O.neg(F, O.mul(F, _, O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e)))))) : O.C(F)}
      %FR.ofz_mul(~F, c, EL.cz(m, EP.NE(b)))
        : {O.add(F, O.ofq(~F, S.Q{S.Z.mul(S.Z.neg(c), EL.cz(m, EP.NE(b))), S.Pos.mul(bt, QN.den(e))}), O.neg(F, O.mul(F, O.ofz(~F, EP.zdot(ct, EP.zv(m, bs))), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e)))))))
          == O.neg(F, O.mul(F, O.add(F, _, O.ofz(~F, EP.zdot(ct, EP.zv(m, bs)))), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e)))))) : O.C(F)}
      %FR.ofz_mul(~F, S.Z.neg(c), EL.cz(m, EP.NE(b)))
        : {O.add(F, O.mul(F, _, O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e))))), O.neg(F, O.mul(F, O.ofz(~F, EP.zdot(ct, EP.zv(m, bs))), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e)))))))
          == O.neg(F, O.mul(F, O.add(F, O.mul(F, O.ofz(~F, c), O.ofz(~F, EL.cz(m, EP.NE(b)))), O.ofz(~F, EP.zdot(ct, EP.zv(m, bs)))), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e)))))) : O.C(F)}
      %FR.ofz_neg(~F, c)
        : {O.add(F, O.mul(F, O.mul(F, _, O.ofz(~F, EL.cz(m, EP.NE(b)))), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e))))), O.neg(F, O.mul(F, O.ofz(~F, EP.zdot(ct, EP.zv(m, bs))), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e)))))))
          == O.neg(F, O.mul(F, O.add(F, O.mul(F, O.ofz(~F, c), O.ofz(~F, EL.cz(m, EP.NE(b)))), O.ofz(~F, EP.zdot(ct, EP.zv(m, bs)))), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e)))))) : O.C(F)}
      FR.fring_eq(~F, [O.ofz(~F, c), O.ofz(~F, EL.cz(m, EP.NE(b))), O.ofz(~F, EP.zdot(ct, EP.zv(m, bs))), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e))))],
        E.ZAdd{E.ZMul{E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZVar{1n}}, E.ZVar{3n}}, E.ZNeg{E.ZMul{E.ZVar{2n}, E.ZVar{3n}}}},
        E.ZNeg{E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZVar{3n}}}, {==})

# at m: e's coefficient is the multipliers' combination of B's
def drop_m(~F: O.OField, +cb: List<&2, S.Z>, +bt: S.Pos, +e: E.QExpr, +B: List<&2, E.QExpr>, +m: List<&2, Nat>,
  hz: {EP.zdot(cb, EP.zv(m, B)) == S.Z.neg(S.Z.mul(S.Zpos{bt}, EL.cz(m, EP.NE(e)))) : S.Z})
  -> {O.ofq(~F, S.Q.sub(CF.coef(e, m), CF.qlin(dropls(cb, bt, e, B), B, m))) == O.zero(F) : O.C(F)}:
  %Equal.sym(O.C(F), O.ofq(~F, S.Q.add(CF.coef(e, m), S.Q.neg(CF.qlin(dropls(cb, bt, e, B), B, m)))), O.add(F, O.ofq(~F, CF.coef(e, m)), O.ofq(~F, S.Q.neg(CF.qlin(dropls(cb, bt, e, B), B, m)))),
      QE.ofq_add(~F, CF.coef(e, m), S.Q.neg(CF.qlin(dropls(cb, bt, e, B), B, m)))) : {_ == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), O.ofq(~F, S.Q.neg(CF.qlin(dropls(cb, bt, e, B), B, m))), O.neg(F, O.ofq(~F, CF.qlin(dropls(cb, bt, e, B), B, m))), QE.ofq_neg(~F, CF.qlin(dropls(cb, bt, e, B), B, m)))
    : {O.add(F, O.ofq(~F, CF.coef(e, m)), _) == O.zero(F) : O.C(F)}
  %ofq_qlin(~F, dropls(cb, bt, e, B), B, m) : {O.add(F, O.ofq(~F, CF.coef(e, m)), O.neg(F, _)) == O.zero(F) : O.C(F)}
  %Equal.sym(O.C(F), fql(~F, dropls(cb, bt, e, B), B, m), O.neg(F, O.mul(F, O.ofz(~F, EP.zdot(cb, EP.zv(m, B))), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e)))))), drop_sum(~F, cb, bt, e, B, m))
    : {O.add(F, O.ofq(~F, CF.coef(e, m)), O.neg(F, _)) == O.zero(F) : O.C(F)}
  %Equal.sym(S.Z, EP.zdot(cb, EP.zv(m, B)), S.Z.neg(S.Z.mul(S.Zpos{bt}, EL.cz(m, EP.NE(e)))), hz)
    : {O.add(F, O.ofq(~F, CF.coef(e, m)), O.neg(F, O.neg(F, O.mul(F, O.ofz(~F, _), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e)))))))) == O.zero(F) : O.C(F)}
  %FR.ofz_neg(~F, S.Z.mul(S.Zpos{bt}, EL.cz(m, EP.NE(e))))
    : {O.add(F, O.ofq(~F, CF.coef(e, m)), O.neg(F, O.neg(F, O.mul(F, _, O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e)))))))) == O.zero(F) : O.C(F)}
  %FR.ofz_mul(~F, S.Zpos{bt}, EL.cz(m, EP.NE(e)))
    : {O.add(F, O.ofq(~F, CF.coef(e, m)), O.neg(F, O.neg(F, O.mul(F, O.neg(F, _), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e)))))))) == O.zero(F) : O.C(F)}
  FO.cert3(~F, O.add(F, O.mul(F, O.ofz(~F, EL.cz(m, EP.NE(e))), O.inv(F, O.ofp(~F, QN.den(e)))), O.neg(F, O.neg(F, O.mul(F, O.neg(F, O.mul(F, O.ofp(~F, bt), O.ofz(~F, EL.cz(m, EP.NE(e))))), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e)))))))),
    O.mul(F, O.mul(F, O.ofp(~F, bt), O.ofz(~F, EL.cz(m, EP.NE(e)))), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e))))), O.sub(~F, O.mul(F, O.ofp(~F, QN.den(e)), O.inv(F, O.ofp(~F, QN.den(e)))), O.one(F)),
    O.neg(F, O.mul(F, O.ofz(~F, EL.cz(m, EP.NE(e))), O.inv(F, O.ofp(~F, QN.den(e))))), O.sub(~F, O.mul(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e))), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e))))), O.one(F)),
    O.mul(F, O.mul(F, O.ofz(~F, EL.cz(m, EP.NE(e))), O.inv(F, O.ofp(~F, QN.den(e)))), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e))))), O.sub(~F, O.ofp(~F, S.Pos.mul(bt, QN.den(e))), O.mul(F, O.ofp(~F, bt), O.ofp(~F, QN.den(e)))),
    FR.fring_eq(~F, [O.ofz(~F, EL.cz(m, EP.NE(e))), O.inv(F, O.ofp(~F, QN.den(e))), O.ofp(~F, bt), O.inv(F, O.ofp(~F, S.Pos.mul(bt, QN.den(e)))), O.ofp(~F, QN.den(e)), O.ofp(~F, S.Pos.mul(bt, QN.den(e)))],
      E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZNeg{E.ZNeg{E.ZMul{E.ZNeg{E.ZMul{E.ZVar{2n}, E.ZVar{0n}}}, E.ZVar{3n}}}}},
      E.ZAdd{E.ZAdd{E.ZMul{E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{0n}}, E.ZVar{3n}}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{1n}}, E.ZCst{S.Zpos{S.XH{}}}}},
        E.ZMul{E.ZNeg{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, E.ZSub{E.ZMul{E.ZVar{5n}, E.ZVar{3n}}, E.ZCst{S.Zpos{S.XH{}}}}}},
        E.ZMul{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{3n}}, E.ZSub{E.ZVar{5n}, E.ZMul{E.ZVar{2n}, E.ZVar{4n}}}}}, {==}),
    QE.ofp_rel(~F, QN.den(e)), QE.ofp_rel(~F, S.Pos.mul(bt, QN.den(e))),
    FO.sub_of_eq(~F, O.ofp(~F, S.Pos.mul(bt, QN.den(e))), O.mul(F, O.ofp(~F, bt), O.ofp(~F, QN.den(e))),
      Equal.sym(O.C(F), O.mul(F, O.ofp(~F, bt), O.ofp(~F, QN.den(e))), O.ofp(~F, S.Pos.mul(bt, QN.den(e))), FR.ofz_mul(~F, S.Zpos{bt}, S.Zpos{QN.den(e)}))))

# a rational that is 0 in a field has numerator 0
def num_zero(~F: O.OField, +q: S.Q, h: {O.ofq(~F, q) == O.zero(F) : O.C(F)}) -> {S.Q.num(q) == S.Z0{} : S.Z}:
  Equal.trans(S.Z, S.Q.num(q), S.Z.mul(S.Q.num(q), S.Zpos{S.XH{}}), S.Z0{}, ZL.mul_one(S.Q.num(q)),
    QE.ofq_eq_rev(~F, q, S.Q{S.Z0{}, S.XH{}}, Equal.trans(O.C(F), O.ofq(~F, q), O.zero(F), O.ofq(~F, S.Q{S.Z0{}, S.XH{}}), h, Equal.sym(O.C(F), O.ofq(~F, S.Q{S.Z0{}, S.XH{}}), O.zero(F), QE.ofq_zero(~F)))))

def zneg(+x: S.Z, +y: S.Z, h: {S.Z0{} == S.Z.add(x, y) : S.Z}) -> {y == S.Z.neg(x) : S.Z}:
  Equal.trans(S.Z, y, S.Z.add(S.Z.add(x, y), S.Z.neg(x)), S.Z.neg(x),
    R.ring_eq([x, y], E.ZVar{1n}, E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZNeg{E.ZVar{0n}}}, {==}),
    (%h : {S.Z.add(_, S.Z.neg(x)) == S.Z.neg(x) : S.Z}
     {==}))

def drop_at(+cb: List<&2, S.Z>, +bt: S.Pos, +e: E.QExpr, +B: List<&2, E.QExpr>, +m: List<&2, Nat>,
  hrel: {S.Z0{} == S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, EP.NE(e))), EP.zdot(cb, EP.zv(m, B))) : S.Z})
  -> {EL.cz(m, R.norm(QN.clr(E.QSub{e, SV.lin(dropls(cb, bt, e, B), B)}))) == S.Z0{} : S.Z}:
  %CF.coef_sub(e, SV.lin(dropls(cb, bt, e, B), B), m) : {S.Q.num(_) == S.Z0{} : S.Z}
  %CF.coef_lin(dropls(cb, bt, e, B), B, m) : {S.Q.num(S.Q.sub(CF.coef(e, m), _)) == S.Z0{} : S.Z}
  num_zero(~QF.qfield(), S.Q.sub(CF.coef(e, m), CF.qlin(dropls(cb, bt, e, B), B, m)),
    drop_m(~QF.qfield(), cb, bt, e, B, m, zneg(S.Z.mul(S.Zpos{bt}, EL.cz(m, EP.NE(e))), EP.zdot(cb, EP.zv(m, B)), hrel)))

def qn_isnil(p: List<&2, R.ZTerm>, h: {EP.isnil(p) == True{} : Bool}) -> {QN.isnil(p) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{t, r}:
      absurd({QN.isnil(Con{t, r}) == True{} : Bool}, KA.ft(h))

def drop_fn(+cb: List<&2, S.Z>, +bt: S.Pos, +e: E.QExpr, +B: List<&2, E.QExpr>,
  hrel: @m: List<&2, Nat> -> {S.Z0{} == S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, EP.NE(e))), EP.zdot(cb, EP.zv(m, B))) : S.Z}, +m: List<&2, Nat>)
  -> {EL.cz(m, R.norm(QN.clr(E.QSub{e, SV.lin(dropls(cb, bt, e, B), B)}))) == S.Z0{} : S.Z}:
  drop_at(cb, bt, e, B, m, hrel(m))

# a combination whose coefficients vanish everywhere gives the identity
def drop_ident(+cb: List<&2, S.Z>, +bt: S.Pos, +e: E.QExpr, +B: List<&2, E.QExpr>,
  hrel: @m: List<&2, Nat> -> {S.Z0{} == S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, EP.NE(e))), EP.zdot(cb, EP.zv(m, B))) : S.Z})
  -> SV.Ident(e, SV.lin(dropls(cb, bt, e, B), B)):
  ID.ident_ok(e, SV.lin(dropls(cb, bt, e, B), B),
    qn_isnil(R.norm(QN.clr(E.QSub{e, SV.lin(dropls(cb, bt, e, B), B)})),
      EP.red_zero(R.norm(QN.clr(E.QSub{e, SV.lin(dropls(cb, bt, e, B), B)})), RP.norm_red(QN.clr(E.QSub{e, SV.lin(dropls(cb, bt, e, B), B)})),
        m => drop_fn(cb, bt, e, B, hrel, m))))

def rescb(r: EL.Res) -> List<&2, S.Z>:
  match r:
    case EL.Res{p, cb, bt}:
      cb

def resbt(r: EL.Res) -> S.Pos:
  match r:
    case EL.Res{p, cb, bt}:
      bt

def nil_rel(+m: List<&2, Nat>, +p: List<&2, R.ZTerm>, +cb: List<&2, S.Z>, +bt: S.Pos, +e: E.QExpr, +B: List<&2, E.QExpr>,
  hrel: @m2: List<&2, Nat> -> EP.Rel(m2, EL.Res{p, cb, bt}, e, B), hnil: {EP.isnil(p) == True{} : Bool})
  -> {S.Z0{} == S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, EP.NE(e))), EP.zdot(cb, EP.zv(m, B))) : S.Z}:
  %Equal.sym(List<&2, R.ZTerm>, Nil{}, p, EP.nil_of(p, hnil)) : {EL.cz(m, _) == S.Z.add(S.Z.mul(S.Zpos{bt}, EL.cz(m, EP.NE(e))), EP.zdot(cb, EP.zv(m, B))) : S.Z}
  hrel(m)

def derivable.r(+B: List<&2, E.QExpr>, +e: E.QExpr, r: EL.Res, hrel: @m: List<&2, Nat> -> EP.Rel(m, r, e, B), hnil: {EP.isnil(EP.resp(r)) == True{} : Bool})
  -> SV.Ident(e, SV.lin(dropls(rescb(r), resbt(r), e, B), B)):
  match r:
    case EL.Res{+p, +cb, +bt}:
      drop_ident(cb, bt, e, B, m => nil_rel(m, p, cb, bt, e, B, hrel, hnil))

# a zero residual: e is a constant combination of the basis
def derivable(+B: List<&2, E.QExpr>, +rows: List<&2, EL.Row>, +e: E.QExpr, +h: {EP.rinv(B, rows, 0n) == True{} : Bool}, hnil: {EP.isnil(EP.resp(EL.resid(rows, e))) == True{} : Bool})
  -> SV.Ident(e, SV.lin(dropls(rescb(EL.resid(rows, e)), resbt(EL.resid(rows, e)), e, B), B)):
  derivable.r(B, e, EL.resid(rows, e), m => EP.resid_rel(m, rows, e, B, EP.rinv_allok(B, rows, 0n, h)), hnil)
