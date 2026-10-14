# sk-05 probe (untrusted, not gated): can the checker be generic over its
# computing numbers K, with laws stated in every ordered field F that K maps
# into (DESIGN §16 Q17)? K is data and operations only; the map E : K -> F
# carries every law.

import Base
import ../spec/num.bend as S
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../lib/qemb.bend as QE
import ../lib/qord.bend as LQO
import ../lib/dmat.bend as DM

# Computing numbers
# -----------------

type Num is Type:
  Num{C: Data,
    zero: C,
    one: C,
    add: C -> C -> C,
    mul: C -> C -> C,
    neg: C -> C,
    cmp: C -> C -> Cmp}

def NC(K: Num) -> Data:
  match K:
    case Num{C, zero, one, add, mul, neg, cmp}:
      C

def nzero(K: Num) -> NC(K):
  match K:
    case Num{C, zero, one, add, mul, neg, cmp}:
      zero

def none(K: Num) -> NC(K):
  match K:
    case Num{C, zero, one, add, mul, neg, cmp}:
      one

def nadd(K: Num) -> NC(K) -> NC(K) -> NC(K):
  match K:
    case Num{C, zero, one, add, mul, neg, cmp}:
      add

def nmul(K: Num) -> NC(K) -> NC(K) -> NC(K):
  match K:
    case Num{C, zero, one, add, mul, neg, cmp}:
      mul

def nneg(K: Num) -> NC(K) -> NC(K):
  match K:
    case Num{C, zero, one, add, mul, neg, cmp}:
      neg

def ncmp(K: Num) -> NC(K) -> NC(K) -> Cmp:
  match K:
    case Num{C, zero, one, add, mul, neg, cmp}:
      cmp

# what a comparison verdict means in F
def cmeans(F: O.OField, c: Cmp, +x: O.C(F), +y: O.C(F)) -> Data:
  match c:
    case LT{}:
      O.lt(F, x, y)
    case EQ{}:
      {x == y : O.C(F)}
    case GT{}:
      O.lt(F, y, x)

# A map of K into F: a ring map whose comparisons are sound
type Emb<-K: Num, -F: O.OField> is Type:
  Emb{e: NC(K) -> O.C(F),
    e_zero: {e(nzero(K)) == O.zero(F) : O.C(F)},
    e_one: {e(none(K)) == O.one(F) : O.C(F)},
    e_add: @a: NC(K) -> @b: NC(K) -> {e(nadd(K, a, b)) == O.add(F, e(a), e(b)) : O.C(F)},
    e_mul: @a: NC(K) -> @b: NC(K) -> {e(nmul(K, a, b)) == O.mul(F, e(a), e(b)) : O.C(F)},
    e_neg: @a: NC(K) -> {e(nneg(K, a)) == O.neg(F, e(a)) : O.C(F)},
    e_cmp: @a: NC(K) -> @b: NC(K) -> cmeans(F, ncmp(K, a, b), e(a), e(b))}

def emap(-K: Num, -F: O.OField, E: Emb<K, F>) -> NC(K) -> O.C(F):
  match E:
    case Emb{e, e_zero, e_one, e_add, e_mul, e_neg, e_cmp}:
      e

def e_zero(-K: Num, -F: O.OField, E: Emb<K, F>) -> {emap(K, F, E, nzero(K)) == O.zero(F) : O.C(F)}:
  match E:
    case Emb{e, e_zero, e_one, e_add, e_mul, e_neg, e_cmp}:
      e_zero

def e_add(-K: Num, -F: O.OField, E: Emb<K, F>) -> @a: NC(K) -> @b: NC(K) -> {emap(K, F, E, nadd(K, a, b)) == O.add(F, emap(K, F, E, a), emap(K, F, E, b)) : O.C(F)}:
  match E:
    case Emb{e, e_zero, e_one, e_add, e_mul, e_neg, e_cmp}:
      e_add

def e_mul(-K: Num, -F: O.OField, E: Emb<K, F>) -> @a: NC(K) -> @b: NC(K) -> {emap(K, F, E, nmul(K, a, b)) == O.mul(F, emap(K, F, E, a), emap(K, F, E, b)) : O.C(F)}:
  match E:
    case Emb{e, e_zero, e_one, e_add, e_mul, e_neg, e_cmp}:
      e_mul

def e_cmp(-K: Num, -F: O.OField, E: Emb<K, F>) -> @a: NC(K) -> @b: NC(K) -> cmeans(F, ncmp(K, a, b), emap(K, F, E, a), emap(K, F, E, b)):
  match E:
    case Emb{e, e_zero, e_one, e_add, e_mul, e_neg, e_cmp}:
      e_cmp

# Generic vectors
# ---------------

def KVec(~K: Num) -> Data:
  List<&2, NC(K)>

def kdot(~K: Num, a: KVec(~K), v: KVec(~K)) -> NC(K):
  match a v:
    case Nil{} v:
      nzero(K)
    case Con{x, xs} Nil{}:
      nzero(K)
    case Con{x, xs} Con{y, ys}:
      nadd(K, nmul(K, x, y), kdot(~K, xs, ys))

def ofkv(~K: Num, ~F: O.OField, ~E: Emb<K, F>, v: KVec(~K)) -> M.Vec(~F):
  match v:
    case Nil{}:
      Nil{}
    case Con{x, xs}:
      Con{emap(K, F, E, x), ofkv(~K, ~F, ~E, xs)}

# one generic law: a K dot product is the F dot product of the images
def kdot_ofk(~K: Num, ~F: O.OField, ~E: Emb<K, F>, a: KVec(~K), v: KVec(~K)) -> {M.dot(~F, ofkv(~K, ~F, ~E, a), ofkv(~K, ~F, ~E, v)) == emap(K, F, E, kdot(~K, a, v)) : O.C(F)}:
  match a v:
    case Nil{} v:
      Equal.sym(O.C(F), emap(K, F, E, nzero(K)), O.zero(F), e_zero(K, F, E))
    case Con{+x, +xs} Nil{}:
      Equal.sym(O.C(F), emap(K, F, E, nzero(K)), O.zero(F), e_zero(K, F, E))
    case Con{+x, +xs} Con{+y, +ys}:
      %Equal.sym(O.C(F), emap(K, F, E, nadd(K, nmul(K, x, y), kdot(~K, xs, ys))), O.add(F, emap(K, F, E, nmul(K, x, y)), emap(K, F, E, kdot(~K, xs, ys))), e_add(K, F, E)(nmul(K, x, y), kdot(~K, xs, ys))) : {O.add(F, O.mul(F, emap(K, F, E, x), emap(K, F, E, y)), M.dot(~F, ofkv(~K, ~F, ~E, xs), ofkv(~K, ~F, ~E, ys))) == _ : O.C(F)}
      %Equal.sym(O.C(F), emap(K, F, E, nmul(K, x, y)), O.mul(F, emap(K, F, E, x), emap(K, F, E, y)), e_mul(K, F, E)(x, y)) : {O.add(F, O.mul(F, emap(K, F, E, x), emap(K, F, E, y)), M.dot(~F, ofkv(~K, ~F, ~E, xs), ofkv(~K, ~F, ~E, ys))) == O.add(F, _, emap(K, F, E, kdot(~K, xs, ys))) : O.C(F)}
      %kdot_ofk(~K, ~F, ~E, xs, ys) : {O.add(F, O.mul(F, emap(K, F, E, x), emap(K, F, E, y)), M.dot(~F, ofkv(~K, ~F, ~E, xs), ofkv(~K, ~F, ~E, ys))) == O.add(F, O.mul(F, emap(K, F, E, x), emap(K, F, E, y)), _) : O.C(F)}
      {==}

# a generic comparison fact: if K says a < b, then e(a) < e(b) in F
def klt_ofk(~K: Num, ~F: O.OField, ~E: Emb<K, F>, +a: NC(K), +b: NC(K), h: {ncmp(K, a, b) == LT{} : Cmp}) -> O.lt(F, emap(K, F, E, a), emap(K, F, E, b)):
  %h : cmeans(F, _, emap(K, F, E, a), emap(K, F, E, b))
  e_cmp(K, F, E)(a, b)

# The dyadic instance
# -------------------

def dcmp(+a: S.D, +b: S.D) -> Cmp:
  S.Q.cmp(S.D.toq(a), S.D.toq(b))

def dnum() -> Num:
  Num{S.D, M.d0(), M.d1(), a => b => S.D.add(a, b), a => b => S.D.mul(a, b), a => S.D.neg(a), a => b => dcmp(a, b)}

def dcmp_sound.go(~F: O.OField, +a: S.D, +b: S.D, c: Cmp, e: {dcmp(a, b) == c : Cmp}) -> cmeans(F, c, M.ofd(~F, a), M.ofd(~F, b)):
  match c:
    case LT{}:
      QE.ofq_lt(~F, S.D.toq(a), S.D.toq(b), e)
    case EQ{}:
      QE.ofq_eq(~F, S.D.toq(a), S.D.toq(b), LQO.q_cmp_eq(S.D.toq(a), S.D.toq(b), e))
    case GT{}:
      QE.ofq_lt(~F, S.D.toq(b), S.D.toq(a), LQO.q_cmp_gt(S.D.toq(a), S.D.toq(b), e))

def dcmp_sound(~F: O.OField, +a: S.D, +b: S.D) -> cmeans(F, dcmp(a, b), M.ofd(~F, a), M.ofd(~F, b)):
  dcmp_sound.go(~F, a, b, dcmp(a, b), {==})

def demb(~F: O.OField) -> Emb<dnum(), F>:
  Emb{x => M.ofd(~F, x),
    Equal.sym(O.C(F), O.zero(F), M.ofd(~F, M.d0()), DM.ofd_zero(~F)),
    Equal.sym(O.C(F), O.one(F), M.ofd(~F, M.d1()), DM.ofd_one(~F)),
    a => b => Equal.sym(O.C(F), O.add(F, M.ofd(~F, a), M.ofd(~F, b)), M.ofd(~F, S.D.add(a, b)), DM.ofd_add(~F, a, b)),
    a => b => Equal.sym(O.C(F), O.mul(F, M.ofd(~F, a), M.ofd(~F, b)), M.ofd(~F, S.D.mul(a, b)), DM.ofd_mul(~F, a, b)),
    a => Equal.sym(O.C(F), O.neg(F, M.ofd(~F, a)), M.ofd(~F, S.D.neg(a)), DM.ofd_neg(~F, a)),
    a => b => dcmp_sound(~F, a, b)}

# the generic law, used at K = D
def ddot_demo(~F: O.OField, a: M.DVec(), v: M.DVec()) -> {M.dot(~F, ofkv(~dnum(), ~F, ~demb(~F), a), ofkv(~dnum(), ~F, ~demb(~F), v)) == M.ofd(~F, kdot(~dnum(), a, v)) : O.C(F)}:
  kdot_ofk(~dnum(), ~F, ~demb(~F), a, v)

# and the generic code computes at K = D: [1, -2] . [3, 1/2] = 2
def dy(m: S.Z, e: Nat) -> S.D:
  S.D{m, e}

def run_ok() -> {dcmp(kdot(~dnum(), [dy(S.Zpos{S.XH{}}, 0n), dy(S.Zneg{S.XO{S.XH{}}}, 0n)], [dy(S.Zpos{S.XI{S.XH{}}}, 0n), dy(S.Zpos{S.XH{}}, 1n)]), dy(S.Zpos{S.XO{S.XH{}}}, 0n)) == EQ{} : Cmp}:
  {==}
