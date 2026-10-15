# bend-cad: facts about lists of numbers, for the solver's totality
# (ROADMAP: solve_total). Proofs only. Membership, sublists, distinct
# lists, the pigeonhole principle, and the matching's map from variables to
# equations (lib/struct.bend: getm, setm, somes, look).
#
# Facts are Bool computations proven equal to True, so they can be used
# any number of times.

import Base
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./struct.bend as ST
import ./nat.bend as LN

def absurd(-A: Type, x: Empty) -> A:
  match x:

# Booleans
# --------

def ft(e: {False{} == True{} : Bool}) -> Empty:
  KA.ft(e)

def tf(e: {True{} == False{} : Bool}) -> Empty:
  KA.ft(Equal.sym(Bool, True{}, False{}, e))

def band_l(a: Bool, +b: Bool, h: {SV.band(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def band_r(a: Bool, +b: Bool, h: {SV.band(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      absurd({b == True{} : Bool}, ft(h))

def band_i(a: Bool, +b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {SV.band(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      absurd({False{} == True{} : Bool}, ft(ha))

def bor_l(a: Bool, +b: Bool, ha: {a == True{} : Bool}) -> {SV.bor(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      absurd({b == True{} : Bool}, ft(ha))

def bor_r(a: Bool, +b: Bool, hb: {b == True{} : Bool}) -> {SV.bor(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

# a or b, a false: b
def bor_rf(a: Bool, +b: Bool, h: {SV.bor(a, b) == True{} : Bool}, ha: {a == False{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      absurd({b == True{} : Bool}, tf(ha))
    case False{}:
      h

def bor_f(a: Bool, +b: Bool, ha: {a == False{} : Bool}, hb: {b == False{} : Bool}) -> {SV.bor(a, b) == False{} : Bool}:
  match a:
    case True{}:
      absurd({True{} == False{} : Bool}, tf(ha))
    case False{}:
      hb

def bnot_t(a: Bool, h: {a == False{} : Bool}) -> {SV.bnot(a) == True{} : Bool}:
  match a:
    case True{}:
      absurd({False{} == True{} : Bool}, tf(h))
    case False{}:
      {==}

def bnot_f(a: Bool, h: {SV.bnot(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      absurd({True{} == False{} : Bool}, ft(h))
    case False{}:
      {==}

# not true and false at once
def tnf(a: Bool, ht: {a == True{} : Bool}, hf: {a == False{} : Bool}) -> Empty:
  match a:
    case True{}:
      tf(hf)
    case False{}:
      ft(ht)

def bor_sv(a: Bool, +b: Bool) -> {SV.bor(a, b) == ST.bor(a, b) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def band_sv(a: Bool, +b: Bool) -> {SV.band(a, b) == KA.band(a, b) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

# Equality of numbers
# -------------------

def eq_refl(a: Nat) -> {SV.eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+b:
      eq_refl(b)

def eq_ok(a: Nat, b: Nat, h: {SV.eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      absurd({0n == 1n+j : Nat}, ft(h))
    case 1n+i 0n:
      absurd({1n+i == 0n : Nat}, ft(h))
    case 1n++i 1n+j:
      %eq_ok(i, j, h) : {1n+i == 1n+_ : Nat}
      {==}

def eq_sym(a: Nat, b: Nat) -> {SV.eq(a, b) == SV.eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      {==}
    case 1n+i 1n+j:
      eq_sym(i, j)

def eq_sv(a: Nat, b: Nat) -> {SV.eq(a, b) == KA.nateq(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      {==}
    case 1n+i 1n+j:
      eq_sv(i, j)

def eq_ne.h(+a: Nat, +b: Nat, e: {a == b : Nat}, h: {SV.eq(a, b) == False{} : Bool}) -> {SV.eq(a, a) == False{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {SV.eq(a, _) == False{} : Bool}
  h

# not a = b and a /= b
def eq_ne(+a: Nat, +b: Nat, e: {a == b : Nat}, h: {SV.eq(a, b) == False{} : Bool}) -> Empty:
  tnf(SV.eq(a, a), eq_refl(a), eq_ne.h(a, b, e, h))

def bor_fl(a: Bool, +b: Bool, h: {SV.bor(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      {==}

def bor_fr(a: Bool, +b: Bool, h: {SV.bor(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      absurd({b == False{} : Bool}, tf(h))
    case False{}:
      h

# Membership
# ----------

def mem_sv(+v: Nat, xs: List<&2, Nat>) -> {SV.mem(v, xs) == ST.mem(v, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      %bor_sv(KA.nateq(v, h), ST.mem(v, t)) : {SV.bor(SV.eq(v, h), SV.mem(v, t)) == _ : Bool}
      %eq_sv(v, h) : {SV.bor(SV.eq(v, h), SV.mem(v, t)) == SV.bor(_, ST.mem(v, t)) : Bool}
      %mem_sv(v, t) : {SV.bor(SV.eq(v, h), SV.mem(v, t)) == SV.bor(SV.eq(v, h), _) : Bool}
      {==}

def mem_hd(+v: Nat, +t: List<&2, Nat>) -> {SV.mem(v, Con{v, t}) == True{} : Bool}:
  bor_l(SV.eq(v, v), SV.mem(v, t), eq_refl(v))

def mem_tl(+v: Nat, +h: Nat, +t: List<&2, Nat>, hm: {SV.mem(v, t) == True{} : Bool}) -> {SV.mem(v, Con{h, t}) == True{} : Bool}:
  bor_r(SV.eq(v, h), SV.mem(v, t), hm)

# v in h :: t, v /= h: v in t
def mem_tl_inv(+v: Nat, +h: Nat, +t: List<&2, Nat>, hm: {SV.mem(v, Con{h, t}) == True{} : Bool}, hn: {SV.eq(v, h) == False{} : Bool}) -> {SV.mem(v, t) == True{} : Bool}:
  bor_rf(SV.eq(v, h), SV.mem(v, t), hm, hn)

def mem_nil(+v: Nat, h: {SV.mem(v, Nil{}) == True{} : Bool}) -> Empty:
  ft(h)

# x in xs and v not in xs: x /= v
def mem_ne.go(+x: Nat, +v: Nat, +xs: List<&2, Nat>, b: Bool, e: {SV.eq(x, v) == b : Bool}, hx: {SV.mem(x, xs) == True{} : Bool}, hv: {SV.mem(v, xs) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      +ex = eq_ok(x, v, e)
      absurd({True{} == False{} : Bool}, tnf(SV.mem(v, xs), %ex : {SV.mem(_, xs) == True{} : Bool}
        hx, hv))
    case False{}:
      {==}

# Sublists
# --------

# every entry of xs is in ys
def subl(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      SV.band(SV.mem(x, ys), subl(t, ys))

def subl_hd(+x: Nat, +t: List<&2, Nat>, +ys: List<&2, Nat>, h: {subl(Con{x, t}, ys) == True{} : Bool}) -> {SV.mem(x, ys) == True{} : Bool}:
  band_l(SV.mem(x, ys), subl(t, ys), h)

def subl_tl(+x: Nat, +t: List<&2, Nat>, +ys: List<&2, Nat>, h: {subl(Con{x, t}, ys) == True{} : Bool}) -> {subl(t, ys) == True{} : Bool}:
  band_r(SV.mem(x, ys), subl(t, ys), h)

def subl_con(+x: Nat, +t: List<&2, Nat>, +ys: List<&2, Nat>, hx: {SV.mem(x, ys) == True{} : Bool}, ht: {subl(t, ys) == True{} : Bool}) -> {subl(Con{x, t}, ys) == True{} : Bool}:
  band_i(SV.mem(x, ys), subl(t, ys), hx, ht)

def subl_mem.go(+x: Nat, +h: Nat, +t: List<&2, Nat>, +ys: List<&2, Nat>, b: Bool, e: {SV.eq(x, h) == b : Bool}, hx: {SV.bor(b, SV.mem(x, t)) == True{} : Bool}, +hs: {subl(Con{h, t}, ys) == True{} : Bool}, ih: {SV.mem(x, t) == True{} : Bool} -> {SV.mem(x, ys) == True{} : Bool}) -> {SV.mem(x, ys) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, x, h, eq_ok(x, h, e)) : {SV.mem(_, ys) == True{} : Bool}
      subl_hd(h, t, ys, hs)
    case False{}:
      ih(hx)

# x in xs, xs within ys: x in ys
def subl_mem(+x: Nat, xs: List<&2, Nat>, +ys: List<&2, Nat>, hx: {SV.mem(x, xs) == True{} : Bool}, +hs: {subl(xs, ys) == True{} : Bool}) -> {SV.mem(x, ys) == True{} : Bool}:
  match xs:
    case Nil{}:
      absurd({SV.mem(x, ys) == True{} : Bool}, ft(hx))
    case Con{+h, +t}:
      subl_mem.go(x, h, t, ys, SV.eq(x, h), {==}, hx, hs, k => subl_mem(x, t, ys, k, subl_tl(h, t, ys, hs)))

def subl_cons_r(xs: List<&2, Nat>, +y: Nat, +ys: List<&2, Nat>, +h: {subl(xs, ys) == True{} : Bool}) -> {subl(xs, Con{y, ys}) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      subl_con(x, t, Con{y, ys}, mem_tl(x, y, ys, subl_hd(x, t, ys, h)), subl_cons_r(t, y, ys, subl_tl(x, t, ys, h)))

def subl_refl(xs: List<&2, Nat>) -> {subl(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      subl_con(x, t, Con{x, t}, mem_hd(x, t), subl_cons_r(t, x, t, subl_refl(t)))

def subl_trans(xs: List<&2, Nat>, +ys: List<&2, Nat>, +zs: List<&2, Nat>, +h1: {subl(xs, ys) == True{} : Bool}, +h2: {subl(ys, zs) == True{} : Bool}) -> {subl(xs, zs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      subl_con(x, t, zs, subl_mem(x, ys, zs, subl_hd(x, t, ys, h1), h2), subl_trans(t, ys, zs, subl_tl(x, t, ys, h1), h2))

# Distinct lists
# --------------

def dist_hd(+h: Nat, +t: List<&2, Nat>, d: {SV.distinct(Con{h, t}) == True{} : Bool}) -> {SV.mem(h, t) == False{} : Bool}:
  bnot_f(SV.mem(h, t), band_l(SV.bnot(SV.mem(h, t)), SV.distinct(t), d))

def dist_tl(+h: Nat, +t: List<&2, Nat>, d: {SV.distinct(Con{h, t}) == True{} : Bool}) -> {SV.distinct(t) == True{} : Bool}:
  band_r(SV.bnot(SV.mem(h, t)), SV.distinct(t), d)

def dist_con(+h: Nat, +t: List<&2, Nat>, hn: {SV.mem(h, t) == False{} : Bool}, d: {SV.distinct(t) == True{} : Bool}) -> {SV.distinct(Con{h, t}) == True{} : Bool}:
  band_i(SV.bnot(SV.mem(h, t)), SV.distinct(t), bnot_t(SV.mem(h, t), hn), d)

# Order of numbers
# ----------------

def le_refl(a: Nat) -> {KA.natle(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+b:
      le_refl(b)

def le_trans(a: Nat, b: Nat, +c: Nat, h1: {KA.natle(a, b) == True{} : Bool}, h2: {KA.natle(b, c) == True{} : Bool}) -> {KA.natle(a, c) == True{} : Bool}:
  match a b c:
    case 0n b c:
      {==}
    case 1n+i 0n c:
      absurd({KA.natle(1n+i, c) == True{} : Bool}, ft(h1))
    case 1n+i 1n+j 0n:
      absurd({False{} == True{} : Bool}, ft(h2))
    case 1n+i 1n+j 1n+k:
      le_trans(i, j, k, h1, h2)

def le_succ(a: Nat, +b: Nat, h: {KA.natle(a, b) == True{} : Bool}) -> {KA.natle(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+i 0n:
      absurd({KA.natle(i, 0n) == True{} : Bool}, ft(h))
    case 1n+i 1n+j:
      le_succ(i, j, h)

# a + 1 <= b: a <= b
def le_pred(+a: Nat, +b: Nat, h: {KA.natle(1n+a, b) == True{} : Bool}) -> {KA.natle(a, b) == True{} : Bool}:
  le_trans(a, 1n+a, b, le_succ(a, a, le_refl(a)), h)

def le_add_r(a: Nat, +b: Nat) -> {KA.natle(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+i:
      le_add_r(i, b)

def le_add_l(a: Nat, +b: Nat) -> {KA.natle(b, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      le_refl(b)
    case 1n++i:
      le_succ(b, Nat.add(i, b), le_add_l(i, b))

# a <= b: c + a <= c + b
def le_add_mono(c: Nat, +a: Nat, +b: Nat, h: {KA.natle(a, b) == True{} : Bool}) -> {KA.natle(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}:
  match c:
    case 0n:
      h
    case 1n+i:
      le_add_mono(i, a, b, h)

# not a + 1 <= a
def lt_irr(a: Nat, h: {KA.natle(1n+a, a) == True{} : Bool}) -> Empty:
  match a:
    case 0n:
      ft(h)
    case 1n+b:
      lt_irr(b, h)

# The pigeonhole principle
# ------------------------

def rem.go(b: Bool, +y: Nat, rest: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      rest
    case False{}:
      Con{y, rest}

# ys without x
def rem(+x: Nat, ys: List<&2, Nat>) -> List<&2, Nat>:
  match ys:
    case Nil{}:
      Nil{}
    case Con{+y, t}:
      rem.go(SV.eq(y, x), y, rem(x, t))

def rem_le.go(b: Bool, +y: Nat, +r: List<&2, Nat>, +n: Nat, h: {KA.natle(SV.len(r), n) == True{} : Bool}) -> {KA.natle(SV.len(rem.go(b, y, r)), 1n+n) == True{} : Bool}:
  match b:
    case True{}:
      le_succ(SV.len(r), n, h)
    case False{}:
      h

def rem_le(+x: Nat, ys: List<&2, Nat>) -> {KA.natle(SV.len(rem(x, ys)), SV.len(ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      {==}
    case Con{+y, +t}:
      rem_le.go(SV.eq(y, x), y, rem(x, t), SV.len(t), rem_le(x, t))

def rem_len.go(+x: Nat, +y: Nat, +t: List<&2, Nat>, b: Bool, e: {SV.eq(y, x) == b : Bool}, hx: {SV.mem(x, Con{y, t}) == True{} : Bool}, ih: {SV.mem(x, t) == True{} : Bool} -> {KA.natle(1n+SV.len(rem(x, t)), SV.len(t)) == True{} : Bool}) -> {KA.natle(1n+SV.len(rem.go(b, y, rem(x, t))), 1n+SV.len(t)) == True{} : Bool}:
  match b:
    case True{}:
      rem_le(x, t)
    case False{}:
      ih(mem_tl_inv(x, y, t, hx, %eq_sym(y, x) : {_ == False{} : Bool}
        e))

# x in ys: removing it shortens ys
def rem_len(+x: Nat, ys: List<&2, Nat>, hx: {SV.mem(x, ys) == True{} : Bool}) -> {KA.natle(1n+SV.len(rem(x, ys)), SV.len(ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      absurd({KA.natle(1n+SV.len(rem(x, Nil{})), 0n) == True{} : Bool}, ft(hx))
    case Con{+y, +t}:
      rem_len.go(x, y, t, SV.eq(y, x), {==}, hx, k => rem_len(x, t, k))

def rem_mem.go2(+z: Nat, +y: Nat, +t: List<&2, Nat>, +r: List<&2, Nat>, c: Bool, e: {SV.eq(z, y) == c : Bool}, hz: {SV.mem(z, Con{y, t}) == True{} : Bool}, ih: {SV.mem(z, t) == True{} : Bool} -> {SV.mem(z, r) == True{} : Bool}) -> {SV.bor(c, SV.mem(z, r)) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      ih(mem_tl_inv(z, y, t, hz, e))

def rem_mem.go(+z: Nat, +x: Nat, +y: Nat, +t: List<&2, Nat>, b: Bool, e: {SV.eq(y, x) == b : Bool}, +hz: {SV.mem(z, Con{y, t}) == True{} : Bool}, hn: {SV.eq(z, x) == False{} : Bool}, ih: {SV.mem(z, t) == True{} : Bool} -> {SV.mem(z, rem(x, t)) == True{} : Bool}) -> {SV.mem(z, rem.go(b, y, rem(x, t))) == True{} : Bool}:
  match b:
    case True{}:
      ih(mem_tl_inv(z, y, t, hz, %Equal.sym(Nat, y, x, eq_ok(y, x, e)) : {SV.eq(z, _) == False{} : Bool}
        hn))
    case False{}:
      rem_mem.go2(z, y, t, rem(x, t), SV.eq(z, y), {==}, hz, ih)

# z in ys, z /= x: z in ys without x
def rem_mem(+z: Nat, +x: Nat, ys: List<&2, Nat>, hz: {SV.mem(z, ys) == True{} : Bool}, +hn: {SV.eq(z, x) == False{} : Bool}) -> {SV.mem(z, rem(x, ys)) == True{} : Bool}:
  match ys:
    case Nil{}:
      absurd({SV.mem(z, Nil{}) == True{} : Bool}, ft(hz))
    case Con{+y, +t}:
      rem_mem.go(z, x, y, t, SV.eq(y, x), {==}, hz, hn, k => rem_mem(z, x, t, k, hn))

# xs within ys, x not in xs: xs within ys without x
def subl_rem(xs: List<&2, Nat>, +x: Nat, +ys: List<&2, Nat>, +hs: {subl(xs, ys) == True{} : Bool}, +hn: {SV.mem(x, xs) == False{} : Bool}) -> {subl(xs, rem(x, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+z, +t}:
      subl_con(z, t, rem(x, ys), rem_mem(z, x, ys, subl_hd(z, t, ys, hs), %eq_sym(x, z) : {_ == False{} : Bool}
        bor_fl(SV.eq(x, z), SV.mem(x, t), hn)), subl_rem(t, x, ys, subl_tl(z, t, ys, hs), bor_fr(SV.eq(x, z), SV.mem(x, t), hn)))

# a distinct list within ys is no longer than ys
def pig(xs: List<&2, Nat>, +ys: List<&2, Nat>, +d: {SV.distinct(xs) == True{} : Bool}, +hs: {subl(xs, ys) == True{} : Bool}) -> {KA.natle(SV.len(xs), SV.len(ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      le_trans(1n+SV.len(t), 1n+SV.len(rem(x, ys)), SV.len(ys), pig(t, rem(x, ys), dist_tl(x, t, d), subl_rem(t, x, ys, subl_tl(x, t, ys, hs), dist_hd(x, t, d))), rem_len(x, ys, subl_hd(x, t, ys, hs)))

# a < b, two ways
def lt_sv(a: Nat, b: Nat) -> {SV.lt(a, b) == KA.natle(1n+a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      {==}
    case 1n+i 0n:
      {==}
    case 1n+i 1n+j:
      lt_sv(i, j)

# The matching's map
# ------------------
# vm sends each variable to its equation (None: free).

def mlen(vm: List<&2, Maybe<&2, Nat>>) -> Nat:
  match vm:
    case Nil{}:
      0n
    case Con{m, t}:
      1n+mlen(t)

def issome(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

# every variable of xs is matched
def allm(+vm: List<&2, Maybe<&2, Nat>>, xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{x, t}:
      SV.band(issome(ST.getm(vm, x)), allm(vm, t))

def none_some(+e: Nat, h: {None{} == Some{e} : Maybe<&2, Nat>}) -> Empty:
  ft(Equal.cong(Maybe<&2, Nat>, Bool, issome, None{}, Some{e}, h))

def some_inj(+a: Nat, +b: Nat, h: {Some{a} == Some{b} : Maybe<&2, Nat>}) -> {a == b : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, ST.look.of, Some{a}, Some{b}, h)

# a matched entry is Some of its mate
def some_of(m: Maybe<&2, Nat>, h: {issome(m) == True{} : Bool}) -> {m == Some{ST.look.of(m)} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      absurd({None{} == Some{0n} : Maybe<&2, Nat>}, ft(h))
    case Some{x}:
      {==}

def getm_lt(vm: List<&2, Maybe<&2, Nat>>, v: Nat, h: {issome(ST.getm(vm, v)) == True{} : Bool}) -> {KA.natle(1n+v, mlen(vm)) == True{} : Bool}:
  match vm v:
    case Nil{} v:
      absurd({KA.natle(1n+v, 0n) == True{} : Bool}, ft(h))
    case Con{m, t} 0n:
      {==}
    case Con{m, t} 1n+j:
      getm_lt(t, j, h)

def getm_set_eq(vm: List<&2, Maybe<&2, Nat>>, v: Nat, +x: Maybe<&2, Nat>, h: {KA.natle(1n+v, mlen(vm)) == True{} : Bool}) -> {ST.getm(ST.setm(vm, v, x), v) == x : Maybe<&2, Nat>}:
  match vm v:
    case Nil{} v:
      absurd({ST.getm(Nil{}, v) == x : Maybe<&2, Nat>}, ft(h))
    case Con{m, t} 0n:
      {==}
    case Con{m, t} 1n+j:
      getm_set_eq(t, j, x, h)

def getm_set_ne(vm: List<&2, Maybe<&2, Nat>>, v: Nat, w: Nat, +x: Maybe<&2, Nat>, h: {SV.eq(w, v) == False{} : Bool}) -> {ST.getm(ST.setm(vm, v, x), w) == ST.getm(vm, w) : Maybe<&2, Nat>}:
  match vm v w:
    case Nil{} v w:
      {==}
    case Con{m, t} 0n 0n:
      absurd({ST.getm(ST.setm(Con{m, t}, 0n, x), 0n) == m : Maybe<&2, Nat>}, tf(h))
    case Con{m, t} 0n 1n+k:
      {==}
    case Con{m, t} 1n+j 0n:
      {==}
    case Con{m, t} 1n+j 1n+k:
      getm_set_ne(t, j, k, x, h)

def mlen_set(vm: List<&2, Maybe<&2, Nat>>, v: Nat, +x: Maybe<&2, Nat>) -> {mlen(ST.setm(vm, v, x)) == mlen(vm) : Nat}:
  match vm v:
    case Nil{} v:
      {==}
    case Con{m, t} 0n:
      {==}
    case Con{m, t} 1n+j:
      %Equal.sym(Nat, mlen(ST.setm(t, j, x)), mlen(t), mlen_set(t, j, x)) : {1n+_ == 1n+mlen(t) : Nat}
      {==}

# x in xs, v not in xs: x /= v
def mem_ne(+x: Nat, +v: Nat, +xs: List<&2, Nat>, hx: {SV.mem(x, xs) == True{} : Bool}, hv: {SV.mem(v, xs) == False{} : Bool}) -> {SV.eq(x, v) == False{} : Bool}:
  mem_ne.go(x, v, xs, SV.eq(x, v), {==}, hx, hv)

def notin_subl.go(+x: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, c: Bool, e: {SV.mem(x, a) == c : Bool}, hb: {SV.mem(x, b) == False{} : Bool}, hs: {subl(a, b) == True{} : Bool}) -> {c == False{} : Bool}:
  match c:
    case True{}:
      absurd({True{} == False{} : Bool}, tnf(SV.mem(x, b), subl_mem(x, a, b, e, hs), hb))
    case False{}:
      {==}

# x not in b, a within b: x not in a
def notin_subl(+x: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, hb: {SV.mem(x, b) == False{} : Bool}, hs: {subl(a, b) == True{} : Bool}) -> {SV.mem(x, a) == False{} : Bool}:
  notin_subl.go(x, a, b, SV.mem(x, a), {==}, hb, hs)

# within a :: ys: within a :: b :: ys
def subl_ins(+xs: List<&2, Nat>, +a: Nat, +b: Nat, +ys: List<&2, Nat>, h: {subl(xs, Con{a, ys}) == True{} : Bool}) -> {subl(xs, Con{a, Con{b, ys}}) == True{} : Bool}:
  subl_trans(xs, Con{a, ys}, Con{a, Con{b, ys}}, h, subl_con(a, ys, Con{a, Con{b, ys}}, mem_hd(a, Con{b, ys}), subl_cons_r(ys, a, Con{b, ys}, subl_cons_r(ys, b, ys, subl_refl(ys)))))

# The matched equations
# ---------------------

# vm sends v to e: e is matched
def some_mem(vm: List<&2, Maybe<&2, Nat>>, v: Nat, +e: Nat, h: {ST.getm(vm, v) == Some{e} : Maybe<&2, Nat>}) -> {SV.mem(e, ST.somes(vm)) == True{} : Bool}:
  match vm v:
    case Nil{} v:
      absurd({SV.mem(e, Nil{}) == True{} : Bool}, none_some(e, h))
    case Con{None{}, t} 0n:
      absurd({SV.mem(e, ST.somes(t)) == True{} : Bool}, none_some(e, h))
    case Con{Some{+x}, +t} 0n:
      %Equal.sym(Nat, x, e, some_inj(x, e, h)) : {SV.mem(e, Con{_, ST.somes(t)}) == True{} : Bool}
      mem_hd(e, ST.somes(t))
    case Con{None{}, t} 1n+j:
      some_mem(t, j, e, h)
    case Con{Some{+x}, +t} 1n+j:
      mem_tl(e, x, ST.somes(t), some_mem(t, j, e, h))

def somes_tl(m: Maybe<&2, Nat>, +t: List<&2, Maybe<&2, Nat>>) -> {subl(ST.somes(t), ST.somes(Con{m, t})) == True{} : Bool}:
  match m:
    case None{}:
      subl_refl(ST.somes(t))
    case Some{+x}:
      subl_cons_r(ST.somes(t), x, ST.somes(t), subl_refl(ST.somes(t)))

# setting v to e: the matched equations are e and some of those before
def set_subl(vm: List<&2, Maybe<&2, Nat>>, v: Nat, +e: Nat) -> {subl(ST.somes(ST.setm(vm, v, Some{e})), Con{e, ST.somes(vm)}) == True{} : Bool}:
  match vm v:
    case Nil{} v:
      {==}
    case Con{+m, +t} 0n:
      subl_con(e, ST.somes(t), Con{e, ST.somes(Con{m, t})}, mem_hd(e, ST.somes(Con{m, t})), subl_cons_r(ST.somes(t), e, ST.somes(Con{m, t}), somes_tl(m, t)))
    case Con{None{}, t} 1n++j:
      set_subl(t, j, e)
    case Con{Some{+x}, +t} 1n++j:
      subl_con(x, ST.somes(ST.setm(t, j, Some{e})), Con{e, Con{x, ST.somes(t)}}, mem_tl(x, e, Con{x, ST.somes(t)}, mem_hd(x, ST.somes(t))), subl_ins(ST.somes(ST.setm(t, j, Some{e})), e, x, ST.somes(t), set_subl(t, j, e)))

# setting a free v to e: one more matched equation
def set_none_len(vm: List<&2, Maybe<&2, Nat>>, v: Nat, +e: Nat, hn: {ST.getm(vm, v) == None{} : Maybe<&2, Nat>}, hl: {KA.natle(1n+v, mlen(vm)) == True{} : Bool}) -> {SV.len(ST.somes(ST.setm(vm, v, Some{e}))) == 1n+SV.len(ST.somes(vm)) : Nat}:
  match vm v:
    case Nil{} v:
      absurd({0n == 1n : Nat}, ft(hl))
    case Con{None{}, t} 0n:
      {==}
    case Con{Some{+x}, t} 0n:
      absurd({SV.len(ST.somes(Con{Some{e}, t})) == 2n+SV.len(ST.somes(t)) : Nat}, none_some(x, Equal.sym(Maybe<&2, Nat>, Some{x}, None{}, hn)))
    case Con{None{}, t} 1n++j:
      set_none_len(t, j, e, hn, hl)
    case Con{Some{+x}, +t} 1n++j:
      %Equal.sym(Nat, SV.len(ST.somes(ST.setm(t, j, Some{e}))), 1n+SV.len(ST.somes(t)), set_none_len(t, j, e, hn, hl)) : {1n+_ == 2n+SV.len(ST.somes(t)) : Nat}
      {==}

# setting a matched v to e: as many matched equations
def set_some_len(vm: List<&2, Maybe<&2, Nat>>, v: Nat, +e: Nat, +e2: Nat, hs: {ST.getm(vm, v) == Some{e2} : Maybe<&2, Nat>}) -> {SV.len(ST.somes(ST.setm(vm, v, Some{e}))) == SV.len(ST.somes(vm)) : Nat}:
  match vm v:
    case Nil{} v:
      absurd({0n == 0n : Nat}, none_some(e2, hs))
    case Con{None{}, t} 0n:
      absurd({SV.len(ST.somes(Con{Some{e}, t})) == SV.len(ST.somes(t)) : Nat}, none_some(e2, hs))
    case Con{Some{x}, t} 0n:
      {==}
    case Con{None{}, t} 1n++j:
      set_some_len(t, j, e, e2, hs)
    case Con{Some{+x}, +t} 1n++j:
      %Equal.sym(Nat, SV.len(ST.somes(ST.setm(t, j, Some{e}))), SV.len(ST.somes(t)), set_some_len(t, j, e, e2, hs)) : {1n+_ == 1n+SV.len(ST.somes(t)) : Nat}
      {==}

# setting v to an unmatched e keeps the matched equations distinct
def set_dist(vm: List<&2, Maybe<&2, Nat>>, v: Nat, +e: Nat, +d: {SV.distinct(ST.somes(vm)) == True{} : Bool}, +hn: {SV.mem(e, ST.somes(vm)) == False{} : Bool}) -> {SV.distinct(ST.somes(ST.setm(vm, v, Some{e}))) == True{} : Bool}:
  match vm v:
    case Nil{} v:
      {==}
    case Con{None{}, +t} 0n:
      dist_con(e, ST.somes(t), hn, d)
    case Con{Some{+x}, +t} 0n:
      dist_con(e, ST.somes(t), bor_fr(SV.eq(e, x), SV.mem(e, ST.somes(t)), hn), dist_tl(x, ST.somes(t), d))
    case Con{None{}, t} 1n++j:
      set_dist(t, j, e, d, hn)
    case Con{Some{+x}, +t} 1n++j:
      +hx = bor_f(SV.eq(x, e), SV.mem(x, ST.somes(t)), %eq_sym(e, x) : {_ == False{} : Bool}
        bor_fl(SV.eq(e, x), SV.mem(e, ST.somes(t)), hn), dist_hd(x, ST.somes(t), d))
      dist_con(x, ST.somes(ST.setm(t, j, Some{e})), notin_subl(x, ST.somes(ST.setm(t, j, Some{e})), Con{e, ST.somes(t)}, hx, set_subl(t, j, e)), set_dist(t, j, e, dist_tl(x, ST.somes(t), d), bor_fr(SV.eq(e, x), SV.mem(e, ST.somes(t)), hn)))

# v went from e2 to e (e /= e2): e2 is no longer matched
def set_unm(vm: List<&2, Maybe<&2, Nat>>, v: Nat, +e: Nat, +e2: Nat, +hs: {ST.getm(vm, v) == Some{e2} : Maybe<&2, Nat>}, +d: {SV.distinct(ST.somes(vm)) == True{} : Bool}, +hne: {SV.eq(e2, e) == False{} : Bool}) -> {SV.mem(e2, ST.somes(ST.setm(vm, v, Some{e}))) == False{} : Bool}:
  match vm v:
    case Nil{} v:
      absurd({False{} == False{} : Bool}, none_some(e2, hs))
    case Con{None{}, t} 0n:
      absurd({SV.mem(e2, Con{e, ST.somes(t)}) == False{} : Bool}, none_some(e2, hs))
    case Con{Some{+x}, +t} 0n:
      bor_f(SV.eq(e2, e), SV.mem(e2, ST.somes(t)), hne, %some_inj(x, e2, hs) : {SV.mem(_, ST.somes(t)) == False{} : Bool}
        dist_hd(x, ST.somes(t), d))
    case Con{None{}, t} 1n++j:
      set_unm(t, j, e, e2, hs, d, hne)
    case Con{Some{+x}, +t} 1n++j:
      bor_f(SV.eq(e2, x), SV.mem(e2, ST.somes(ST.setm(t, j, Some{e}))), mem_ne(e2, x, ST.somes(t), some_mem(t, j, e2, hs), dist_hd(x, ST.somes(t), d)), set_unm(t, j, e, e2, hs, dist_tl(x, ST.somes(t), d), hne))

# two variables matched to one equation are one variable
def inj(vm: List<&2, Maybe<&2, Nat>>, a: Nat, b: Nat, +e: Nat, ha: {ST.getm(vm, a) == Some{e} : Maybe<&2, Nat>}, hb: {ST.getm(vm, b) == Some{e} : Maybe<&2, Nat>}, +d: {SV.distinct(ST.somes(vm)) == True{} : Bool}) -> {SV.eq(a, b) == True{} : Bool}:
  match vm a b:
    case Nil{} a b:
      absurd({SV.eq(a, b) == True{} : Bool}, none_some(e, ha))
    case Con{None{}, t} 0n b:
      absurd({SV.eq(0n, b) == True{} : Bool}, none_some(e, ha))
    case Con{Some{x}, t} 0n 0n:
      {==}
    case Con{Some{+x}, +t} 0n 1n+k:
      absurd({False{} == True{} : Bool}, tnf(SV.mem(e, ST.somes(t)), some_mem(t, k, e, hb), %some_inj(x, e, ha) : {SV.mem(_, ST.somes(t)) == False{} : Bool}
        dist_hd(x, ST.somes(t), d)))
    case Con{None{}, t} 1n+j 0n:
      absurd({False{} == True{} : Bool}, none_some(e, hb))
    case Con{Some{+x}, +t} 1n+j 0n:
      absurd({False{} == True{} : Bool}, tnf(SV.mem(e, ST.somes(t)), some_mem(t, j, e, ha), %some_inj(x, e, hb) : {SV.mem(_, ST.somes(t)) == False{} : Bool}
        dist_hd(x, ST.somes(t), d)))
    case Con{None{}, t} 1n+j 1n+k:
      inj(t, j, k, e, ha, hb, d)
    case Con{Some{+x}, +t} 1n+j 1n+k:
      inj(t, j, k, e, ha, hb, dist_tl(x, ST.somes(t), d))

# The mates of visited variables
# ------------------------------

def look_len(+vm: List<&2, Maybe<&2, Nat>>, xs: List<&2, Nat>) -> {SV.len(ST.look(vm, xs)) == SV.len(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat, SV.len(ST.look(vm, t)), SV.len(t), look_len(vm, t)) : {1n+_ == 1n+SV.len(t) : Nat}
      {==}

# the mates of matched variables are matched equations
def look_subl(+vm: List<&2, Maybe<&2, Nat>>, xs: List<&2, Nat>, +h: {allm(vm, xs) == True{} : Bool}) -> {subl(ST.look(vm, xs), ST.somes(vm)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      subl_con(ST.look.of(ST.getm(vm, x)), ST.look(vm, t), ST.somes(vm), some_mem(vm, x, ST.look.of(ST.getm(vm, x)), some_of(ST.getm(vm, x), band_l(issome(ST.getm(vm, x)), allm(vm, t), h))), look_subl(vm, t, band_r(issome(ST.getm(vm, x)), allm(vm, t), h)))

def look_dist.hw(+vm: List<&2, Maybe<&2, Nat>>, +w: Nat, +mx: Nat, e: {SV.eq(mx, ST.look.of(ST.getm(vm, w))) == True{} : Bool}, hw: {issome(ST.getm(vm, w)) == True{} : Bool}) -> {ST.getm(vm, w) == Some{mx} : Maybe<&2, Nat>}:
  %Equal.sym(Nat, mx, ST.look.of(ST.getm(vm, w)), eq_ok(mx, ST.look.of(ST.getm(vm, w)), e)) : {ST.getm(vm, w) == Some{_} : Maybe<&2, Nat>}
  some_of(ST.getm(vm, w), hw)

def look_dist.go(+vm: List<&2, Maybe<&2, Nat>>, +x: Nat, +w: Nat, +mx: Nat, b: Bool, e: {SV.eq(mx, ST.look.of(ST.getm(vm, w))) == b : Bool}, hx: {ST.getm(vm, x) == Some{mx} : Maybe<&2, Nat>}, hw: {issome(ST.getm(vm, w)) == True{} : Bool}, hn: {SV.eq(x, w) == False{} : Bool}, d: {SV.distinct(ST.somes(vm)) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, tnf(SV.eq(x, w), inj(vm, x, w, mx, hx, look_dist.hw(vm, w, mx, e, hw), d), hn))
    case False{}:
      {==}

def look_dist.aux(+vm: List<&2, Maybe<&2, Nat>>, +x: Nat, t: List<&2, Nat>, +mx: Nat, +hx: {ST.getm(vm, x) == Some{mx} : Maybe<&2, Nat>}, +hn: {SV.mem(x, t) == False{} : Bool}, +h: {allm(vm, t) == True{} : Bool}, +d: {SV.distinct(ST.somes(vm)) == True{} : Bool}) -> {SV.mem(mx, ST.look(vm, t)) == False{} : Bool}:
  match t:
    case Nil{}:
      {==}
    case Con{+w, +r}:
      +mw = ST.look.of(ST.getm(vm, w))
      bor_f(SV.eq(mx, mw), SV.mem(mx, ST.look(vm, r)), look_dist.go(vm, x, w, mx, SV.eq(mx, mw), {==}, hx, band_l(issome(ST.getm(vm, w)), allm(vm, r), h), bor_fl(SV.eq(x, w), SV.mem(x, r), hn), d), look_dist.aux(vm, x, r, mx, hx, bor_fr(SV.eq(x, w), SV.mem(x, r), hn), band_r(issome(ST.getm(vm, w)), allm(vm, r), h), d))

# distinct matched variables have distinct mates
def look_dist(+vm: List<&2, Maybe<&2, Nat>>, xs: List<&2, Nat>, +dx: {SV.distinct(xs) == True{} : Bool}, +h: {allm(vm, xs) == True{} : Bool}, +d: {SV.distinct(ST.somes(vm)) == True{} : Bool}) -> {SV.distinct(ST.look(vm, xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +mx = ST.look.of(ST.getm(vm, x))
      dist_con(mx, ST.look(vm, t), look_dist.aux(vm, x, t, mx, some_of(ST.getm(vm, x), band_l(issome(ST.getm(vm, x)), allm(vm, t), h)), dist_hd(x, t, dx), band_r(issome(ST.getm(vm, x)), allm(vm, t), h), d), look_dist(vm, t, dist_tl(x, t, dx), band_r(issome(ST.getm(vm, x)), allm(vm, t), h), d))

# The free variables
# ------------------

def holes_len(vm: List<&2, Maybe<&2, Nat>>, +k: Nat) -> {Nat.add(SV.len(ST.somes(vm)), SV.len(ST.holes(vm, k))) == mlen(vm) : Nat}:
  match vm:
    case Nil{}:
      {==}
    case Con{None{}, +t}:
      %LN.add_succ(SV.len(ST.somes(t)), SV.len(ST.holes(t, 1n+k))) : {_ == 1n+mlen(t) : Nat}
      %Equal.sym(Nat, Nat.add(SV.len(ST.somes(t)), SV.len(ST.holes(t, 1n+k))), mlen(t), holes_len(t, 1n+k)) : {1n+_ == 1n+mlen(t) : Nat}
      {==}
    case Con{Some{x}, +t}:
      %Equal.sym(Nat, Nat.add(SV.len(ST.somes(t)), SV.len(ST.holes(t, 1n+k))), mlen(t), holes_len(t, 1n+k)) : {1n+_ == 1n+mlen(t) : Nat}
      {==}

def holes_ge.go(+x: Nat, +k: Nat, +r: List<&2, Nat>, b: Bool, e: {SV.eq(x, k) == b : Bool}, h: {SV.bor(b, SV.mem(x, r)) == True{} : Bool}, ih: {SV.mem(x, r) == True{} : Bool} -> {KA.natle(1n+k, x) == True{} : Bool}) -> {KA.natle(k, x) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, x, k, eq_ok(x, k, e)) : {KA.natle(k, _) == True{} : Bool}
      le_refl(k)
    case False{}:
      le_pred(k, x, ih(h))

# the free variables from k are at least k
def holes_ge(vm: List<&2, Maybe<&2, Nat>>, +k: Nat, +x: Nat, h: {SV.mem(x, ST.holes(vm, k)) == True{} : Bool}) -> {KA.natle(k, x) == True{} : Bool}:
  match vm:
    case Nil{}:
      absurd({KA.natle(k, x) == True{} : Bool}, ft(h))
    case Con{None{}, +t}:
      holes_ge.go(x, k, ST.holes(t, 1n+k), SV.eq(x, k), {==}, h, q => holes_ge(t, 1n+k, x, q))
    case Con{Some{y}, +t}:
      le_pred(k, x, holes_ge(t, 1n+k, x, h))

def holes_dist.go(+k: Nat, +t: List<&2, Maybe<&2, Nat>>, b: Bool, e: {SV.mem(k, ST.holes(t, 1n+k)) == b : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, lt_irr(k, holes_ge(t, 1n+k, k, e)))
    case False{}:
      {==}

def holes_dist(vm: List<&2, Maybe<&2, Nat>>, +k: Nat) -> {SV.distinct(ST.holes(vm, k)) == True{} : Bool}:
  match vm:
    case Nil{}:
      {==}
    case Con{None{}, +t}:
      dist_con(k, ST.holes(t, 1n+k), holes_dist.go(k, t, SV.mem(k, ST.holes(t, 1n+k)), {==}), holes_dist(t, 1n+k))
    case Con{Some{y}, +t}:
      holes_dist(t, 1n+k)

# k + 1 + m <= n: k < n
def lt_of(+k: Nat, +m: Nat, +n: Nat, h: {KA.natle(Nat.add(k, 1n+m), n) == True{} : Bool}) -> {SV.lt(k, n) == True{} : Bool}:
  %Equal.sym(Bool, SV.lt(k, n), KA.natle(1n+k, n), lt_sv(k, n)) : {_ == True{} : Bool}
  le_trans(1n+k, Nat.add(k, 1n+m), n, %LN.add_succ(k, m) : {KA.natle(1n+k, _) == True{} : Bool}
    le_add_r(k, m), h)

def hb_step(+k: Nat, +m: Nat, +n: Nat, h: {KA.natle(Nat.add(k, 1n+m), n) == True{} : Bool}) -> {KA.natle(Nat.add(1n+k, m), n) == True{} : Bool}:
  %Equal.sym(Nat, 1n+Nat.add(k, m), Nat.add(k, 1n+m), LN.add_succ(k, m)) : {KA.natle(_, n) == True{} : Bool}
  h

# the free variables from k are below n, when k + |vm| <= n
def holes_below(vm: List<&2, Maybe<&2, Nat>>, +k: Nat, +n: Nat, +h: {KA.natle(Nat.add(k, mlen(vm)), n) == True{} : Bool}) -> {SV.below(ST.holes(vm, k), n) == True{} : Bool}:
  match vm:
    case Nil{}:
      {==}
    case Con{None{}, +t}:
      band_i(SV.lt(k, n), SV.below(ST.holes(t, 1n+k), n), lt_of(k, mlen(t), n, h), holes_below(t, 1n+k, n, hb_step(k, mlen(t), n, h)))
    case Con{Some{y}, +t}:
      holes_below(t, 1n+k, n, hb_step(k, mlen(t), n, h))
