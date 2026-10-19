# bend-cad: the structure's adjacency by dependence (PLAN-sk13a S2, Q30).
# dadj(e) is the variables e mentions whose derivative in e does not
# normalize to 0 (lib/identpf.bend: dep). It is exactly what e depends on:
# - every v in dadj(e) has Depends(e, v) (dadj_depends);
# - e depends only on dadj(e): DependsWithin(e, w) whenever dadj(e) is
#   within w (dadj_within). A variable e mentions but drops out of
#   (x - x + y) has a derivative that normalizes to 0; one e does not
#   mention has derivative 0 in every ordered field (deriv0).
# Proofs only, besides dadj itself.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/deriv.bend as DV
import ../spec/solve.bend as SV
import ./flaws.bend as FL
import ./qemb.bend as QE
import ./qfield.bend as QF
import ./karith.bend as KA
import ./listpf.bend as L
import ./struct.bend as ST
import ./dfspf.bend as D
import ./identpf.bend as ID

def absurd(-A: Type, x: Empty) -> A:
  match x:

# The adjacency
# -------------

def dfilt.dec(b: Bool, v: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      Con{v, r}
    case False{}:
      r

# the variables of vs that e depends on
def dfilt(+e: E.QExpr, vs: List<&2, Nat>) -> List<&2, Nat>:
  match vs:
    case Nil{}:
      Nil{}
    case Con{+v, t}:
      dfilt.dec(ID.dep(e, v), v, dfilt(e, t))

# the variables e mentions, in order of first occurrence
def cand(+e: E.QExpr) -> List<&2, Nat>:
  ST.rev(ST.evars(e, Nil{}))

# what e depends on
def dadj(+e: E.QExpr) -> List<&2, Nat>:
  dfilt(e, cand(e))

# A variable not mentioned has derivative 0
# -----------------------------------------

def deq_sv(a: Nat, b: Nat) -> {DV.eq(a, b) == SV.eq(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      {==}
    case 1n+i 1n+j:
      deq_sv(i, j)

def zz(~F: O.OField) -> {O.add(F, O.zero(F), O.zero(F)) == O.zero(F) : O.C(F)}:
  Equal.sym(O.C(F), O.zero(F), O.add(F, O.zero(F), O.zero(F)), FL.add_zero(~F, O.zero(F)))

# e within w, v not in w: d e / d x_v is 0 everywhere
def deriv0(~F: O.OField, e: E.QExpr, +v: Nat, +w: List<&2, Nat>, +hi: {SV.inside(e, w) == True{} : Bool}, +hv: {SV.mem(v, w) == False{} : Bool}, +env: List<&2, O.C(F)>)
  -> {O.eval(~F, env, DV.deriv(e, v)) == O.zero(F) : O.C(F)}:
  match e:
    case E.QVar{+i}:
      %Equal.sym(Bool, DV.eq(i, v), False{}, Equal.trans(Bool, DV.eq(i, v), SV.eq(i, v), False{}, deq_sv(i, v), L.mem_ne(i, v, w, hi, hv))) : {O.eval(~F, env, DV.dvar(_)) == O.zero(F) : O.C(F)}
      QE.ofq_zero(~F)
    case E.QCst{q}:
      QE.ofq_zero(~F)
    case E.QAdd{+a, +b}:
      %Equal.sym(O.C(F), O.eval(~F, env, DV.deriv(a, v)), O.zero(F), deriv0(~F, a, v, w, L.band_l(SV.inside(a, w), SV.inside(b, w), hi), hv, env))
        : {O.add(F, _, O.eval(~F, env, DV.deriv(b, v))) == O.zero(F) : O.C(F)}
      %Equal.sym(O.C(F), O.eval(~F, env, DV.deriv(b, v)), O.zero(F), deriv0(~F, b, v, w, L.band_r(SV.inside(a, w), SV.inside(b, w), hi), hv, env))
        : {O.add(F, O.zero(F), _) == O.zero(F) : O.C(F)}
      zz(~F)
    case E.QSub{+a, +b}:
      %Equal.sym(O.C(F), O.eval(~F, env, DV.deriv(a, v)), O.zero(F), deriv0(~F, a, v, w, L.band_l(SV.inside(a, w), SV.inside(b, w), hi), hv, env))
        : {O.add(F, _, O.neg(F, O.eval(~F, env, DV.deriv(b, v)))) == O.zero(F) : O.C(F)}
      %Equal.sym(O.C(F), O.eval(~F, env, DV.deriv(b, v)), O.zero(F), deriv0(~F, b, v, w, L.band_r(SV.inside(a, w), SV.inside(b, w), hi), hv, env))
        : {O.add(F, O.zero(F), O.neg(F, _)) == O.zero(F) : O.C(F)}
      %FL.neg_zero(~F) : {O.add(F, O.zero(F), _) == O.zero(F) : O.C(F)}
      zz(~F)
    case E.QMul{+a, +b}:
      %Equal.sym(O.C(F), O.eval(~F, env, DV.deriv(a, v)), O.zero(F), deriv0(~F, a, v, w, L.band_l(SV.inside(a, w), SV.inside(b, w), hi), hv, env))
        : {O.add(F, O.mul(F, _, O.eval(~F, env, b)), O.mul(F, O.eval(~F, env, a), O.eval(~F, env, DV.deriv(b, v)))) == O.zero(F) : O.C(F)}
      %Equal.sym(O.C(F), O.eval(~F, env, DV.deriv(b, v)), O.zero(F), deriv0(~F, b, v, w, L.band_r(SV.inside(a, w), SV.inside(b, w), hi), hv, env))
        : {O.add(F, O.mul(F, O.zero(F), O.eval(~F, env, b)), O.mul(F, O.eval(~F, env, a), _)) == O.zero(F) : O.C(F)}
      %Equal.sym(O.C(F), O.mul(F, O.zero(F), O.eval(~F, env, b)), O.zero(F), FL.zero_mul(~F, O.eval(~F, env, b)))
        : {O.add(F, _, O.mul(F, O.eval(~F, env, a), O.zero(F))) == O.zero(F) : O.C(F)}
      %FL.mul_zero(~F, O.eval(~F, env, a)) : {O.add(F, O.zero(F), _) == O.zero(F) : O.C(F)}
      zz(~F)
    case E.QNeg{a}:
      %Equal.sym(O.C(F), O.eval(~F, env, DV.deriv(a, v)), O.zero(F), deriv0(~F, a, v, w, hi, hv, env)) : {O.neg(F, _) == O.zero(F) : O.C(F)}
      Equal.sym(O.C(F), O.zero(F), O.neg(F, O.zero(F)), FL.neg_zero(~F))

def deriv0_at(~F: O.OField, +e: E.QExpr, +v: Nat, +w: List<&2, Nat>, +hi: {SV.inside(e, w) == True{} : Bool}, +hv: {SV.mem(v, w) == False{} : Bool}, +x: List<&2, S.Q>)
  -> S.Q.eq(E.qeval(x, DV.deriv(e, v)), SV.qzero()):
  QE.ofq_eq_rev(~F, E.qeval(x, DV.deriv(e, v)), SV.qzero(),
    (%ID.qbr(~F, x, DV.deriv(e, v)) : {_ == O.ofq(~F, SV.qzero()) : O.C(F)}
     %Equal.sym(O.C(F), O.ofq(~F, SV.qzero()), O.zero(F), QE.ofq_zero(~F)) : {O.eval(~F, ID.qmap(~F, x), DV.deriv(e, v)) == _ : O.C(F)}
     deriv0(~F, e, v, w, hi, hv, ID.qmap(~F, x))))

def deriv0_ident(+e: E.QExpr, +v: Nat, +w: List<&2, Nat>, +hi: {SV.inside(e, w) == True{} : Bool}, +hv: {SV.mem(v, w) == False{} : Bool}) -> SV.Ident(DV.deriv(e, v), E.QCst{SV.qzero()}):
  x => deriv0_at(~QF.qfield(), e, v, w, hi, hv, x)

# e mentions only its candidates
def cand_inside(+e: E.QExpr) -> {SV.inside(e, cand(e)) == True{} : Bool}:
  L.band_l(SV.inside(e, cand(e)), L.subl(Nil{}, cand(e)), D.ev_inside(e, Nil{}, cand(e), D.rev_subl(ST.evars(e, Nil{}), cand(e), L.subl_refl(cand(e)))))

# The adjacency is dependence
# ---------------------------

def dfilt_dep.eq(c: Bool, +e: E.QExpr, +u: Nat, +v: Nat, +r: List<&2, Nat>, ec: {c == SV.eq(u, v) : Bool}, eb: {True{} == ID.dep(e, v) : Bool},
  hm: {SV.bor(c, SV.mem(u, r)) == True{} : Bool}, rec: {SV.mem(u, r) == True{} : Bool} -> {ID.dep(e, u) == True{} : Bool}) -> {ID.dep(e, u) == True{} : Bool}:
  match c:
    case True{}:
      %Equal.sym(Nat, u, v, L.eq_ok(u, v, Equal.sym(Bool, True{}, SV.eq(u, v), ec))) : {ID.dep(e, _) == True{} : Bool}
      Equal.sym(Bool, True{}, ID.dep(e, v), eb)
    case False{}:
      rec(hm)

def dfilt_dep.dec(b: Bool, +e: E.QExpr, +v: Nat, +u: Nat, +r: List<&2, Nat>, eb: {b == ID.dep(e, v) : Bool},
  hm: {SV.mem(u, dfilt.dec(b, v, r)) == True{} : Bool}, rec: {SV.mem(u, r) == True{} : Bool} -> {ID.dep(e, u) == True{} : Bool}) -> {ID.dep(e, u) == True{} : Bool}:
  match b:
    case True{}:
      dfilt_dep.eq(SV.eq(u, v), e, u, v, r, {==}, eb, hm, rec)
    case False{}:
      rec(hm)


def dfilt_dep(+e: E.QExpr, vs: List<&2, Nat>, +u: Nat, hm: {SV.mem(u, dfilt(e, vs)) == True{} : Bool}) -> {ID.dep(e, u) == True{} : Bool}:
  match vs:
    case Nil{}:
      absurd({ID.dep(e, u) == True{} : Bool}, KA.ft(hm))
    case Con{+v, +t}:
      dfilt_dep.dec(ID.dep(e, v), e, v, u, dfilt(e, t), {==}, hm, k => dfilt_dep(e, t, u, k))

def dfilt_keep.r(b: Bool, +v: Nat, +u: Nat, +r: List<&2, Nat>, h: {SV.mem(u, r) == True{} : Bool}) -> {SV.mem(u, dfilt.dec(b, v, r)) == True{} : Bool}:
  match b:
    case True{}:
      L.mem_tl(u, v, r, h)
    case False{}:
      h

def dfilt_keep.go(c: Bool, +e: E.QExpr, +v: Nat, +u: Nat, +t: List<&2, Nat>, ec: {c == SV.eq(u, v) : Bool}, hm: {SV.bor(c, SV.mem(u, t)) == True{} : Bool},
  hd: {ID.dep(e, u) == True{} : Bool}, rec: {SV.mem(u, t) == True{} : Bool} -> {SV.mem(u, dfilt(e, t)) == True{} : Bool})
  -> {SV.mem(u, dfilt.dec(ID.dep(e, v), v, dfilt(e, t))) == True{} : Bool}:
  match c:
    case True{}:
      %L.eq_ok(u, v, Equal.sym(Bool, True{}, SV.eq(u, v), ec)) : {SV.mem(u, dfilt.dec(ID.dep(e, _), _, dfilt(e, t))) == True{} : Bool}
      %Equal.sym(Bool, ID.dep(e, u), True{}, hd) : {SV.mem(u, dfilt.dec(_, u, dfilt(e, t))) == True{} : Bool}
      L.mem_hd(u, dfilt(e, t))
    case False{}:
      dfilt_keep.r(ID.dep(e, v), v, u, dfilt(e, t), rec(hm))

# a variable of vs that e depends on is kept
def dfilt_keep(+e: E.QExpr, vs: List<&2, Nat>, +u: Nat, hm: {SV.mem(u, vs) == True{} : Bool}, +hd: {ID.dep(e, u) == True{} : Bool}) -> {SV.mem(u, dfilt(e, vs)) == True{} : Bool}:
  match vs:
    case Nil{}:
      absurd({SV.mem(u, Nil{}) == True{} : Bool}, KA.ft(hm))
    case Con{+v, +t}:
      dfilt_keep.go(SV.eq(u, v), e, v, u, t, {==}, hm, hd, k => dfilt_keep(e, t, u, k, hd))

# every variable of dadj(e) is one e depends on
def dadj_depends(+e: E.QExpr, +v: Nat, h: {SV.mem(v, dadj(e)) == True{} : Bool}) -> SV.Depends(e, v):
  ID.dep_ok(e, v, dfilt_dep(e, cand(e), v, h))

def within.dep(c: Bool, +e: E.QExpr, +v: Nat, +w: List<&2, Nat>, ec: {c == ID.dep(e, v) : Bool}, hc: {SV.mem(v, cand(e)) == True{} : Bool},
  hs: {L.subl(dadj(e), w) == True{} : Bool}, hv: {SV.mem(v, w) == False{} : Bool}) -> SV.Ident(DV.deriv(e, v), E.QCst{SV.qzero()}):
  match c:
    case True{}:
      absurd(SV.Ident(DV.deriv(e, v), E.QCst{SV.qzero()}), KA.tf(Equal.trans(Bool, True{}, SV.mem(v, w), False{},
        Equal.sym(Bool, SV.mem(v, w), True{}, L.subl_mem(v, dadj(e), w, dfilt_keep(e, cand(e), v, hc, Equal.sym(Bool, True{}, ID.dep(e, v), ec)), hs)), hv)))
    case False{}:
      ID.nodep_ok(e, v, Equal.sym(Bool, False{}, ID.dep(e, v), ec))

def within.go(b: Bool, +e: E.QExpr, +v: Nat, +w: List<&2, Nat>, eb: {b == SV.mem(v, cand(e)) : Bool},
  hs: {L.subl(dadj(e), w) == True{} : Bool}, hv: {SV.mem(v, w) == False{} : Bool}) -> SV.Ident(DV.deriv(e, v), E.QCst{SV.qzero()}):
  match b:
    case True{}:
      within.dep(ID.dep(e, v), e, v, w, {==}, Equal.sym(Bool, True{}, SV.mem(v, cand(e)), eb), hs, hv)
    case False{}:
      deriv0_ident(e, v, cand(e), cand_inside(e), Equal.sym(Bool, False{}, SV.mem(v, cand(e)), eb))

def within.at(+e: E.QExpr, +v: Nat, +w: List<&2, Nat>, +hs: {L.subl(dadj(e), w) == True{} : Bool}, hv: {SV.mem(v, w) == False{} : Bool}) -> SV.Ident(DV.deriv(e, v), E.QCst{SV.qzero()}):
  within.go(SV.mem(v, cand(e)), e, v, w, {==}, hs, hv)

# e depends only on dadj(e)
def dadj_within(+e: E.QExpr, +w: List<&2, Nat>, +hs: {L.subl(dadj(e), w) == True{} : Bool}) -> SV.DependsWithin(e, w):
  v => hv => within.at(e, v, w, hs, hv)
