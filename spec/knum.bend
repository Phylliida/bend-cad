# bend-cad spec: the numbers a checker computes with (DESIGN §16 Q17).
# Trusted. A checker is written once, generic over its computing numbers K:
# data and operations only, with no laws of its own (the dyadics, for one,
# have no canonical form). Every law lives in an ordered field F, on a map
# E : K -> F that sends K's operations to F's and whose comparisons are
# sound there. So a certificate checked in K proves its claim in every F
# that K maps into: D and Q map into every ordered field, Q(sqrt d) into
# those with a positive sqrt d.

import Base
import ./field.bend as O

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

# Maps into an ordered field
# --------------------------

# what a comparison's verdict says in F
def cmeans(F: O.OField, c: Cmp, +x: O.C(F), +y: O.C(F)) -> Data:
  match c:
    case LT{}:
      O.lt(F, x, y)
    case EQ{}:
      {x == y : O.C(F)}
    case GT{}:
      O.lt(F, y, x)

# E : K -> F, a ring map whose comparisons are sound in F
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

def e_one(-K: Num, -F: O.OField, E: Emb<K, F>) -> {emap(K, F, E, none(K)) == O.one(F) : O.C(F)}:
  match E:
    case Emb{e, e_zero, e_one, e_add, e_mul, e_neg, e_cmp}:
      e_one

def e_add(-K: Num, -F: O.OField, E: Emb<K, F>) -> @a: NC(K) -> @b: NC(K) -> {emap(K, F, E, nadd(K, a, b)) == O.add(F, emap(K, F, E, a), emap(K, F, E, b)) : O.C(F)}:
  match E:
    case Emb{e, e_zero, e_one, e_add, e_mul, e_neg, e_cmp}:
      e_add

def e_mul(-K: Num, -F: O.OField, E: Emb<K, F>) -> @a: NC(K) -> @b: NC(K) -> {emap(K, F, E, nmul(K, a, b)) == O.mul(F, emap(K, F, E, a), emap(K, F, E, b)) : O.C(F)}:
  match E:
    case Emb{e, e_zero, e_one, e_add, e_mul, e_neg, e_cmp}:
      e_mul

def e_neg(-K: Num, -F: O.OField, E: Emb<K, F>) -> @a: NC(K) -> {emap(K, F, E, nneg(K, a)) == O.neg(F, emap(K, F, E, a)) : O.C(F)}:
  match E:
    case Emb{e, e_zero, e_one, e_add, e_mul, e_neg, e_cmp}:
      e_neg

def e_cmp(-K: Num, -F: O.OField, E: Emb<K, F>) -> @a: NC(K) -> @b: NC(K) -> cmeans(F, ncmp(K, a, b), emap(K, F, E, a), emap(K, F, E, b)):
  match E:
    case Emb{e, e_zero, e_one, e_add, e_mul, e_neg, e_cmp}:
      e_cmp

# Vectors and matrices of K, sent to F entry by entry
# ---------------------------------------------------

def KVec(~K: Num) -> Data:
  List<&2, NC(K)>

def KMat(~K: Num) -> Data:
  List<&2, List<&2, NC(K)>>

def ofkv(~K: Num, ~F: O.OField, ~E: Emb<K, F>, v: KVec(~K)) -> List<&2, O.C(F)>:
  match v:
    case Nil{}:
      Nil{}
    case Con{x, xs}:
      Con{emap(K, F, E, x), ofkv(~K, ~F, ~E, xs)}

def ofkm(~K: Num, ~F: O.OField, ~E: Emb<K, F>, a: KMat(~K)) -> List<&2, List<&2, O.C(F)>>:
  match a:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{ofkv(~K, ~F, ~E, r), ofkm(~K, ~F, ~E, rs)}
