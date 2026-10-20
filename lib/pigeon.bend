# bend-cad: the pigeonhole principle for bases (PLAN-sk13a S3): a list of
# distinct Bool lists, each of length n, has at most 2^n entries. By
# induction on n: split the list by first entry; the tails on each side
# are distinct lists of length n - 1.
#
# Generated from tools/drafts/pigeon.draft by tools/expand.py; edit the
# draft.

import Base
import ./karith.bend as KA
import ./nat.bend as LN

def absurd(-A: Type, x: Empty) -> A:
  match x:

def bnot(b: Bool) -> Bool:
  match b:
    case True{}:
      False{}
    case False{}:
      True{}

def bor(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      True{}
    case False{}:
      b

def beqb(a: Bool, b: Bool) -> Bool:
  match a b:
    case True{} True{}:
      True{}
    case True{} False{}:
      False{}
    case False{} True{}:
      False{}
    case False{} False{}:
      True{}

def beqb_eq(a: Bool, b: Bool, h: {beqb(a, b) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      absurd({True{} == False{} : Bool}, KA.ft(h))
    case False{} True{}:
      absurd({False{} == True{} : Bool}, KA.ft(h))
    case False{} False{}:
      {==}

def beqb_refl(a: Bool) -> {beqb(a, a) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def beqb_sym(a: Bool, b: Bool) -> {beqb(a, b) == beqb(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# two Bool lists are equal
def beq(u: List<&2, Bool>, w: List<&2, Bool>) -> Bool:
  match u w:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, s}:
      False{}
    case Con{x, t} Nil{}:
      False{}
    case Con{x, t} Con{y, s}:
      KA.band(beqb(x, y), beq(t, s))

def beq_eq(u: List<&2, Bool>, w: List<&2, Bool>, h: {beq(u, w) == True{} : Bool}) -> {u == w : List<&2, Bool>}:
  match u w:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, s}:
      absurd({Nil{} == Con{y, s} : List<&2, Bool>}, KA.ft(h))
    case Con{x, t} Nil{}:
      absurd({Con{x, t} == Nil{} : List<&2, Bool>}, KA.ft(h))
    case Con{+x, +t} Con{+y, +s}:
      +h2 = h
      %Equal.sym(Bool, x, y, beqb_eq(x, y, KA.band_l(beqb(x, y), beq(t, s), h2))) : {Con{_, t} == Con{y, s} : List<&2, Bool>}
      %Equal.sym(List<&2, Bool>, t, s, beq_eq(t, s, KA.band_r(beqb(x, y), beq(t, s), h2))) : {Con{y, _} == Con{y, s} : List<&2, Bool>}
      {==}

def beq_refl(u: List<&2, Bool>) -> {beq(u, u) == True{} : Bool}:
  match u:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      KA.band_i(beqb(x, x), beq(t, t), beqb_refl(x), beq_refl(t))

# x is in L
def memb(+x: List<&2, Bool>, L: List<&2, List<&2, Bool>>) -> Bool:
  match L:
    case Nil{}:
      False{}
    case Con{y, t}:
      bor(beq(x, y), memb(x, t))

# no entry twice
def nodup(L: List<&2, List<&2, Bool>>) -> Bool:
  match L:
    case Nil{}:
      True{}
    case Con{+x, +t}:
      KA.band(bnot(memb(x, t)), nodup(t))

def blen(u: List<&2, Bool>) -> Nat:
  match u:
    case Nil{}:
      0n
    case Con{x, t}:
      1n+blen(t)

# every entry has length n
def alllen(L: List<&2, List<&2, Bool>>, +n: Nat) -> Bool:
  match L:
    case Nil{}:
      True{}
    case Con{x, t}:
      KA.band(KA.nateq(blen(x), n), alllen(t, n))

def llen(L: List<&2, List<&2, Bool>>) -> Nat:
  match L:
    case Nil{}:
      0n
    case Con{x, t}:
      1n+llen(t)

def pow2(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n++k:
      Nat.add(pow2(k), pow2(k))

# Splitting by the first entry
# ----------------------------

def split.c(c: Bool, r: List<&2, Bool>, rest: List<&2, List<&2, Bool>>) -> List<&2, List<&2, Bool>>:
  match c:
    case True{}:
      Con{r, rest}
    case False{}:
      rest

# the tails of the entries whose first entry is b
def split(L: List<&2, List<&2, Bool>>, +b: Bool) -> List<&2, List<&2, Bool>>:
  match L:
    case Nil{}:
      Nil{}
    case Con{Nil{}, t}:
      split(t, b)
    case Con{Con{h, r}, t}:
      split.c(beqb(h, b), r, split(t, b))

def len_split.go(c: Bool, +r: List<&2, Bool>, +t: List<&2, List<&2, Bool>>, ih: {llen(t) == Nat.add(llen(split(t, True{})), llen(split(t, False{}))) : Nat}) -> {1n+llen(t) == Nat.add(llen(split.c(c, r, split(t, True{}))), llen(split.c(bnot(c), r, split(t, False{})))) : Nat}:
  match c:
    case True{}:
      %Equal.sym(Nat, llen(t), Nat.add(llen(split(t, True{})), llen(split(t, False{}))), ih) : {1n+_ == 1n+Nat.add(llen(split(t, True{})), llen(split(t, False{}))) : Nat}
      {==}
    case False{}:
      %Equal.sym(Nat, llen(t), Nat.add(llen(split(t, True{})), llen(split(t, False{}))), ih) : {1n+_ == Nat.add(llen(split(t, True{})), 1n+llen(split(t, False{}))) : Nat}
      LN.add_succ(llen(split(t, True{})), llen(split(t, False{})))

def bnot_beqb(h: Bool) -> {beqb(h, False{}) == bnot(beqb(h, True{})) : Bool}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

# both sides together have every entry (each has a first entry)
def len_split(L: List<&2, List<&2, Bool>>, +n: Nat, h: {alllen(L, 1n+n) == True{} : Bool}) -> {llen(L) == Nat.add(llen(split(L, True{})), llen(split(L, False{}))) : Nat}:
  match L:
    case Nil{}:
      {==}
    case Con{Nil{}, t}:
      absurd({llen(Con{Nil{}, t}) == Nat.add(llen(split(Con{Nil{}, t}, True{})), llen(split(Con{Nil{}, t}, False{}))) : Nat}, KA.ft(h))
    case Con{Con{+x, +r}, +t}:
      %Equal.sym(Bool, beqb(x, False{}), bnot(beqb(x, True{})), bnot_beqb(x)) : {1n+llen(t) == Nat.add(llen(split.c(beqb(x, True{}), r, split(t, True{}))), llen(split.c(_, r, split(t, False{})))) : Nat}
      len_split.go(beqb(x, True{}), r, t, len_split(t, n, KA.band_r(KA.nateq(blen(Con{x, r}), 1n+n), alllen(t, 1n+n), h)))

def alllen_c(c: Bool, +r: List<&2, Bool>, +rest: List<&2, List<&2, Bool>>, +n: Nat, hr: {KA.nateq(blen(r), n) == True{} : Bool}, h: {alllen(rest, n) == True{} : Bool}) -> {alllen(split.c(c, r, rest), n) == True{} : Bool}:
  match c:
    case True{}:
      KA.band_i(KA.nateq(blen(r), n), alllen(rest, n), hr, h)
    case False{}:
      h

# the tails have length n
def alllen_split(L: List<&2, List<&2, Bool>>, +n: Nat, +b: Bool, h: {alllen(L, 1n+n) == True{} : Bool}) -> {alllen(split(L, b), n) == True{} : Bool}:
  match L:
    case Nil{}:
      {==}
    case Con{Nil{}, t}:
      absurd({alllen(split(Con{Nil{}, t}, b), n) == True{} : Bool}, KA.ft(h))
    case Con{Con{+x, +r}, +t}:
      +h2 = h
      alllen_c(beqb(x, b), r, split(t, b), n, KA.band_l(KA.nateq(blen(Con{x, r}), 1n+n), alllen(t, 1n+n), h2), alllen_split(t, n, b, KA.band_r(KA.nateq(blen(Con{x, r}), 1n+n), alllen(t, 1n+n), h2)))

def bor_r(a: Bool, b: Bool, h: {b == True{} : Bool}) -> {bor(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def bnot_t(b: Bool, h: {bnot(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.ft(h))
    case False{}:
      {==}

def bor_l_or(a: Bool, +b: Bool, h: {bor(a, b) == True{} : Bool}, hf: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      absurd({b == True{} : Bool}, KA.tf(hf))
    case False{}:
      h

def ms.d(d: Bool, +y: List<&2, Bool>, +r: List<&2, Bool>, +x: Bool, +b: Bool, +t: List<&2, List<&2, Bool>>, hd: {d == beq(y, r) : Bool}, hxb: {beqb(x, b) == True{} : Bool}, h: {bor(beq(y, r), memb(y, split(t, b))) == True{} : Bool}, ih: {memb(y, split(t, b)) == True{} : Bool} -> {memb(Con{b, y}, t) == True{} : Bool}) -> {bor(KA.band(beqb(b, x), beq(y, r)), memb(Con{b, y}, t)) == True{} : Bool}:
  match d:
    case True{}:
      %hd : {bor(KA.band(beqb(b, x), _), memb(Con{b, y}, t)) == True{} : Bool}
      %beqb_sym(x, b) : {bor(KA.band(_, True{}), memb(Con{b, y}, t)) == True{} : Bool}
      %Equal.sym(Bool, beqb(x, b), True{}, hxb) : {bor(KA.band(_, True{}), memb(Con{b, y}, t)) == True{} : Bool}
      {==}
    case False{}:
      bor_r(KA.band(beqb(b, x), beq(y, r)), memb(Con{b, y}, t), ih(bor_l_or(beq(y, r), memb(y, split(t, b)), h, Equal.sym(Bool, False{}, beq(y, r), hd))))

def ms.go(c: Bool, +y: List<&2, Bool>, +r: List<&2, Bool>, +x: Bool, +b: Bool, +t: List<&2, List<&2, Bool>>, hc: {c == beqb(x, b) : Bool}, h: {memb(y, split.c(c, r, split(t, b))) == True{} : Bool}, ih: {memb(y, split(t, b)) == True{} : Bool} -> {memb(Con{b, y}, t) == True{} : Bool}) -> {bor(KA.band(beqb(b, x), beq(y, r)), memb(Con{b, y}, t)) == True{} : Bool}:
  match c:
    case False{}:
      bor_r(KA.band(beqb(b, x), beq(y, r)), memb(Con{b, y}, t), ih(h))
    case True{}:
      ms.d(beq(y, r), y, r, x, b, t, {==}, Equal.sym(Bool, True{}, beqb(x, b), hc), h, ih)

# a tail on the b side comes from the entry b :: tail
def memb_split(+y: List<&2, Bool>, L: List<&2, List<&2, Bool>>, +b: Bool, h: {memb(y, split(L, b)) == True{} : Bool}) -> {memb(Con{b, y}, L) == True{} : Bool}:
  match L:
    case Nil{}:
      absurd({memb(Con{b, y}, Nil{}) == True{} : Bool}, KA.ft(h))
    case Con{Nil{}, +t}:
      memb_split(y, t, b, h)
    case Con{Con{+x, +r}, +t}:
      ms.go(beqb(x, b), y, r, x, b, t, {==}, h, hh => memb_split(y, t, b, hh))

def ns.m(d: Bool, +r: List<&2, Bool>, +x: Bool, +b: Bool, +t: List<&2, List<&2, Bool>>, hd: {d == memb(r, split(t, b)) : Bool}, hxb: {x == b : Bool}, hm: {memb(Con{x, r}, t) == False{} : Bool}) -> {memb(r, split(t, b)) == False{} : Bool}:
  match d:
    case False{}:
      Equal.sym(Bool, False{}, memb(r, split(t, b)), hd)
    case True{}:
      absurd({memb(r, split(t, b)) == False{} : Bool}, KA.tf(Equal.trans(Bool, True{}, memb(Con{x, r}, t), False{},
        (%Equal.sym(Bool, x, b, hxb) : {True{} == memb(Con{_, r}, t) : Bool}
         Equal.sym(Bool, memb(Con{b, r}, t), True{}, memb_split(r, t, b, Equal.sym(Bool, True{}, memb(r, split(t, b)), hd)))), hm)))

def ns.go(c: Bool, +r: List<&2, Bool>, +x: Bool, +b: Bool, +t: List<&2, List<&2, Bool>>, hc: {c == beqb(x, b) : Bool}, hm: {memb(Con{x, r}, t) == False{} : Bool}, ih: {nodup(split(t, b)) == True{} : Bool}) -> {nodup(split.c(c, r, split(t, b))) == True{} : Bool}:
  match c:
    case False{}:
      ih
    case True{}:
      KA.band_i(bnot(memb(r, split(t, b))), nodup(split(t, b)), (%Equal.sym(Bool, memb(r, split(t, b)), False{}, ns.m(memb(r, split(t, b)), r, x, b, t, {==}, beqb_eq(x, b, Equal.sym(Bool, True{}, beqb(x, b), hc)), hm)) : {bnot(_) == True{} : Bool}
        {==}), ih)

# the tails on one side are distinct
def nodup_split(L: List<&2, List<&2, Bool>>, +n: Nat, +b: Bool, hl: {alllen(L, 1n+n) == True{} : Bool}, hd: {nodup(L) == True{} : Bool}) -> {nodup(split(L, b)) == True{} : Bool}:
  match L:
    case Nil{}:
      {==}
    case Con{Nil{}, t}:
      absurd({nodup(split(Con{Nil{}, t}, b)) == True{} : Bool}, KA.ft(hl))
    case Con{Con{+x, +r}, +t}:
      +hd2 = hd
      ns.go(beqb(x, b), r, x, b, t, {==}, bnot_t(memb(Con{x, r}, t), KA.band_l(bnot(memb(Con{x, r}, t)), nodup(t), hd2)),
        nodup_split(t, n, b, KA.band_r(KA.nateq(blen(Con{x, r}), 1n+n), alllen(t, 1n+n), hl), KA.band_r(bnot(memb(Con{x, r}, t)), nodup(t), hd2)))

def beq_len0(x: List<&2, Bool>, y: List<&2, Bool>, hx: {KA.nateq(blen(x), 0n) == True{} : Bool}, hy: {KA.nateq(blen(y), 0n) == True{} : Bool}) -> {beq(x, y) == True{} : Bool}:
  match x y:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, s}:
      absurd({beq(Nil{}, Con{b, s}) == True{} : Bool}, KA.ft(hy))
    case Con{a, t} y:
      absurd({beq(Con{a, t}, y) == True{} : Bool}, KA.ft(hx))

# at most 2^n distinct Bool lists of length n
def ph(n: Nat, L: List<&2, List<&2, Bool>>, hl: {alllen(L, n) == True{} : Bool}, hd: {nodup(L) == True{} : Bool}) -> {KA.natle(llen(L), pow2(n)) == True{} : Bool}:
  match n L:
    case 0n Nil{}:
      {==}
    case 0n Con{x, Nil{}}:
      {==}
    case 0n Con{+x, Con{+y, +t}}:
      +hl2 = hl
      absurd({KA.natle(llen(Con{x, Con{y, t}}), pow2(0n)) == True{} : Bool}, KA.tf(Equal.trans(Bool, True{}, memb(x, Con{y, t}), False{},
        Equal.sym(Bool, memb(x, Con{y, t}), True{}, (%Equal.sym(Bool, beq(x, y), True{}, beq_len0(x, y, KA.band_l(KA.nateq(blen(x), 0n), alllen(Con{y, t}, 0n), hl2), KA.band_l(KA.nateq(blen(y), 0n), alllen(t, 0n), KA.band_r(KA.nateq(blen(x), 0n), alllen(Con{y, t}, 0n), hl2)))) : {bor(_, memb(x, t)) == True{} : Bool}
          {==})),
        bnot_t(memb(x, Con{y, t}), KA.band_l(bnot(memb(x, Con{y, t})), nodup(Con{y, t}), hd)))))
    case 1n++k +L:
      +hl2 = hl
      +hd2 = hd
      %Equal.sym(Nat, llen(L), Nat.add(llen(split(L, True{})), llen(split(L, False{}))), len_split(L, k, hl2)) : {KA.natle(_, Nat.add(pow2(k), pow2(k))) == True{} : Bool}
      KA.natle_add2(llen(split(L, True{})), llen(split(L, False{})), pow2(k), pow2(k), ph(k, split(L, True{}), alllen_split(L, k, True{}, hl2), nodup_split(L, k, True{}, hl2, hd2)), ph(k, split(L, False{}), alllen_split(L, k, False{}, hl2), nodup_split(L, k, False{}, hl2, hd2)))
