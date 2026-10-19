# bend-cad: the non-root lemma (PLAN-sk13a S1). A reduced integer polynomial
# (RP.red) other than the zero polynomial is nonzero at an integer point:
# R.epoly(witness(p), p) is not 0 (nonroot).
#
# By induction on variables. Split p at the variable h (split_ok):
# p = A + x_h B, where A is the terms not beginning with h and B the terms
# beginning with h, h taken off. Every variable of p is at least h, so A
# does not mention x_h.
# - A is not zero: by induction A(y) = a is not 0 at some y; setting
#   x_h = 2a, p = a + 2a B = a (1 + 2B), not 0 since 1 + 2B is odd.
# - A is zero: p = x_h B with B not zero, and every coordinate of the
#   witness is nonzero.
# Proofs only.

import Base
import ./nat.bend as N
import ./natring.bend as NR
import ./zring.bend as R
import ./zlaws.bend as ZL
import ./karith.bend as KA
import ./redpoly.bend as RP
import ../spec/num.bend as S
import ../spec/ring.bend as E

def absurd(-A: Type, x: Empty) -> A:
  match x:

def isnil(p: List<&2, R.ZTerm>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{t, r}:
      False{}

def nil_of(p: List<&2, R.ZTerm>, h: {isnil(p) == True{} : Bool}) -> {Nil{} == p : List<&2, R.ZTerm>}:
  match p:
    case Nil{}:
      {==}
    case Con{t, r}:
      absurd({Nil{} == Con{t, r} : List<&2, R.ZTerm>}, KA.ft(h))

# Splitting at a variable
# -----------------------

# m begins with the variable h
def hd(+h: Nat, m: List<&2, Nat>) -> Bool:
  match m:
    case Nil{}:
      False{}
    case Con{x, xs}:
      KA.nateq(x, h)

def mtail(m: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case Nil{}:
      Nil{}
    case Con{x, xs}:
      xs

def noh.dec(b: Bool, c: S.Z, m: List<&2, Nat>, r: List<&2, R.ZTerm>) -> List<&2, R.ZTerm>:
  match b:
    case True{}:
      r
    case False{}:
      Con{R.ZTerm{c, m}, r}

# the terms of p not beginning with h
def noh(+h: Nat, p: List<&2, R.ZTerm>) -> List<&2, R.ZTerm>:
  match p:
    case Nil{}:
      Nil{}
    case Con{R.ZTerm{c, +m}, rest}:
      noh.dec(hd(h, m), c, m, noh(h, rest))

def tl.dec(b: Bool, c: S.Z, m: List<&2, Nat>, r: List<&2, R.ZTerm>) -> List<&2, R.ZTerm>:
  match b:
    case True{}:
      Con{R.ZTerm{c, mtail(m)}, r}
    case False{}:
      r

# the terms of p beginning with h, h taken off
def tl(+h: Nat, p: List<&2, R.ZTerm>) -> List<&2, R.ZTerm>:
  match p:
    case Nil{}:
      Nil{}
    case Con{R.ZTerm{c, +m}, rest}:
      tl.dec(hd(h, m), c, m, tl(h, rest))

def assoc_r(+x: S.Z, +y: S.Z, +z: S.Z) -> {S.Z.add(S.Z.add(x, y), z) == S.Z.add(x, S.Z.add(y, z)) : S.Z}:
  Equal.sym(S.Z, S.Z.add(x, S.Z.add(y, z)), S.Z.add(S.Z.add(x, y), z), ZL.add_assoc(x, y, z))

def split_x(b: Bool, +env: List<&2, S.Z>, +h: Nat, +c: S.Z, +x: Nat, +xs: List<&2, Nat>, +nr: List<&2, R.ZTerm>, +tr: List<&2, R.ZTerm>,
  eb: {b == KA.nateq(x, h) : Bool})
  -> {S.Z.add(R.epoly(env, noh.dec(b, c, Con{x, xs}, nr)), S.Z.mul(E.lookup(env, h), R.epoly(env, tl.dec(b, c, Con{x, xs}, tr))))
      == S.Z.add(S.Z.mul(c, R.emono(env, Con{x, xs})), S.Z.add(R.epoly(env, nr), S.Z.mul(E.lookup(env, h), R.epoly(env, tr)))) : S.Z}:
  match b:
    case True{}:
      %Equal.sym(Nat, x, h, KA.nateq_ok(x, h, Equal.sym(Bool, True{}, KA.nateq(x, h), eb))) : {S.Z.add(R.epoly(env, nr), S.Z.mul(E.lookup(env, h), S.Z.add(S.Z.mul(c, R.emono(env, xs)), R.epoly(env, tr))))
        == S.Z.add(S.Z.mul(c, S.Z.mul(E.lookup(env, _), R.emono(env, xs))), S.Z.add(R.epoly(env, nr), S.Z.mul(E.lookup(env, h), R.epoly(env, tr)))) : S.Z}
      R.ring_eq([c, E.lookup(env, h), R.emono(env, xs), R.epoly(env, nr), R.epoly(env, tr)],
        E.ZAdd{E.ZVar{3n}, E.ZMul{E.ZVar{1n}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{4n}}}},
        E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}, E.ZAdd{E.ZVar{3n}, E.ZMul{E.ZVar{1n}, E.ZVar{4n}}}}, {==})
    case False{}:
      assoc_r(S.Z.mul(c, R.emono(env, Con{x, xs})), R.epoly(env, nr), S.Z.mul(E.lookup(env, h), R.epoly(env, tr)))

def split_m(+env: List<&2, S.Z>, +h: Nat, +c: S.Z, m: List<&2, Nat>, +nr: List<&2, R.ZTerm>, +tr: List<&2, R.ZTerm>)
  -> {S.Z.add(R.epoly(env, noh.dec(hd(h, m), c, m, nr)), S.Z.mul(E.lookup(env, h), R.epoly(env, tl.dec(hd(h, m), c, m, tr))))
      == S.Z.add(S.Z.mul(c, R.emono(env, m)), S.Z.add(R.epoly(env, nr), S.Z.mul(E.lookup(env, h), R.epoly(env, tr)))) : S.Z}:
  match m:
    case Nil{}:
      assoc_r(S.Z.mul(c, R.emono(env, Nil{})), R.epoly(env, nr), S.Z.mul(E.lookup(env, h), R.epoly(env, tr)))
    case Con{+x, +xs}:
      split_x(KA.nateq(x, h), env, h, c, x, xs, nr, tr, {==})

# p is noh(h, p) + x_h tl(h, p)
def split_ok(+env: List<&2, S.Z>, +h: Nat, p: List<&2, R.ZTerm>) -> {S.Z.add(R.epoly(env, noh(h, p)), S.Z.mul(E.lookup(env, h), R.epoly(env, tl(h, p)))) == R.epoly(env, p) : S.Z}:
  match p:
    case Nil{}:
      Equal.sym(S.Z, S.Z0{}, S.Z.mul(E.lookup(env, h), S.Z0{}), ZL.mul_zero(E.lookup(env, h)))
    case Con{R.ZTerm{+c, +m}, +rest}:
      %split_ok(env, h, rest) : {S.Z.add(R.epoly(env, noh(h, Con{R.ZTerm{c, m}, rest})), S.Z.mul(E.lookup(env, h), R.epoly(env, tl(h, Con{R.ZTerm{c, m}, rest}))))
        == S.Z.add(S.Z.mul(c, R.emono(env, m)), _) : S.Z}
      split_m(env, h, c, m, noh(h, rest), tl(h, rest))

# The split keeps polynomials reduced
# -----------------------------------

def lts_noh.dec(b: Bool, +k: List<&2, Nat>, d: S.Z, +n: List<&2, Nat>, +r: List<&2, R.ZTerm>,
  hn: {RP.islt(NR.mcmp(k, n)) == True{} : Bool}, hr: {RP.mlts(k, r) == True{} : Bool}) -> {RP.mlts(k, noh.dec(b, d, n, r)) == True{} : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      KA.band_i(RP.islt(NR.mcmp(k, n)), RP.mlts(k, r), hn, hr)

def lts_noh(+k: List<&2, Nat>, +h: Nat, p: List<&2, R.ZTerm>, +hp: {RP.mlts(k, p) == True{} : Bool}) -> {RP.mlts(k, noh(h, p)) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{d, +n}, +rest}:
      lts_noh.dec(hd(h, n), k, d, n, noh(h, rest), KA.band_l(RP.islt(NR.mcmp(k, n)), RP.mlts(k, rest), hp),
        lts_noh(k, h, rest, KA.band_r(RP.islt(NR.mcmp(k, n)), RP.mlts(k, rest), hp)))

def red_noh.dec(b: Bool, +c: S.Z, +m: List<&2, Nat>, +r: List<&2, R.ZTerm>, hc: {RP.nz(c) == True{} : Bool}, hm: {RP.msort(m) == True{} : Bool},
  hl: {RP.mlts(m, r) == True{} : Bool}, hr: {RP.red(r) == True{} : Bool}) -> {RP.red(noh.dec(b, c, m, r)) == True{} : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      RP.red_mk(c, m, r, hc, hm, hl, hr)

def red_noh(+h: Nat, p: List<&2, R.ZTerm>, +hp: {RP.red(p) == True{} : Bool}) -> {RP.red(noh(h, p)) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{+c, +m}, +rest}:
      red_noh.dec(hd(h, m), c, m, noh(h, rest), RP.red_c(c, m, rest, hp), RP.red_m(c, m, rest, hp),
        lts_noh(m, h, rest, RP.red_l(c, m, rest, hp)), red_noh(h, rest, RP.red_r(c, m, rest, hp)))

# with x = y, comparing x::xs with y::ys is comparing xs with ys
def dec_eq(+x: Nat, +y: Nat, e: {x == y : Nat}, +r: Cmp) -> {NR.mcmp.dec(Nat.cmp(x, y), r) == r : Cmp}:
  %e : {NR.mcmp.dec(Nat.cmp(x, _), r) == r : Cmp}
  %RP.ncmp_refl(x) : {NR.mcmp.dec(_, r) == r : Cmp}
  {==}

def lt_dec(+x: Nat, +y: Nat, e: {x == y : Nat}, +r: Cmp, h: {RP.islt(NR.mcmp.dec(Nat.cmp(x, y), r)) == True{} : Bool}) -> {RP.islt(r) == True{} : Bool}:
  %dec_eq(x, y, e, r) : {RP.islt(_) == True{} : Bool}
  h

def lts_tl.y(b: Bool, +h: Nat, +x: Nat, +xs: List<&2, Nat>, d: S.Z, +y: Nat, +ys: List<&2, Nat>, +r: List<&2, R.ZTerm>,
  eb: {b == KA.nateq(y, h) : Bool}, hx: {x == h : Nat},
  hn: {RP.islt(NR.mcmp(Con{x, xs}, Con{y, ys})) == True{} : Bool}, rec: {RP.mlts(xs, r) == True{} : Bool})
  -> {RP.mlts(xs, tl.dec(b, d, Con{y, ys}, r)) == True{} : Bool}:
  match b:
    case True{}:
      +hy = KA.nateq_ok(y, h, Equal.sym(Bool, True{}, KA.nateq(y, h), eb))
      KA.band_i(RP.islt(NR.mcmp(xs, ys)), RP.mlts(xs, r), lt_dec(x, y, Equal.trans(Nat, x, h, y, hx, Equal.sym(Nat, y, h, hy)), NR.mcmp(xs, ys), hn), rec)
    case False{}:
      rec

def lts_tl.n(+h: Nat, +x: Nat, +xs: List<&2, Nat>, d: S.Z, n: List<&2, Nat>, +r: List<&2, R.ZTerm>, hx: {x == h : Nat},
  hn: {RP.islt(NR.mcmp(Con{x, xs}, n)) == True{} : Bool}, rec: {RP.mlts(xs, r) == True{} : Bool})
  -> {RP.mlts(xs, tl.dec(hd(h, n), d, n, r)) == True{} : Bool}:
  match n:
    case Nil{}:
      rec
    case Con{+y, +ys}:
      lts_tl.y(KA.nateq(y, h), h, x, xs, d, y, ys, r, {==}, hx, hn, rec)

# a monomial below every monomial of p, beginning with h, stays below in tl
def lts_tl(+h: Nat, +x: Nat, +xs: List<&2, Nat>, p: List<&2, R.ZTerm>, +hx: {x == h : Nat}, +hp: {RP.mlts(Con{x, xs}, p) == True{} : Bool}) -> {RP.mlts(xs, tl(h, p)) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{d, +n}, +rest}:
      lts_tl.n(h, x, xs, d, n, tl(h, rest), hx, KA.band_l(RP.islt(NR.mcmp(Con{x, xs}, n)), RP.mlts(Con{x, xs}, rest), hp),
        lts_tl(h, x, xs, rest, hx, KA.band_r(RP.islt(NR.mcmp(Con{x, xs}, n)), RP.mlts(Con{x, xs}, rest), hp)))

def red_tl.x(b: Bool, +h: Nat, +c: S.Z, +x: Nat, +xs: List<&2, Nat>, +rest: List<&2, R.ZTerm>, eb: {b == KA.nateq(x, h) : Bool},
  hc: {RP.nz(c) == True{} : Bool}, hm: {RP.msort(Con{x, xs}) == True{} : Bool}, hl: {RP.mlts(Con{x, xs}, rest) == True{} : Bool},
  hr: {RP.red(tl(h, rest)) == True{} : Bool}) -> {RP.red(tl.dec(b, c, Con{x, xs}, tl(h, rest))) == True{} : Bool}:
  match b:
    case True{}:
      RP.red_mk(c, xs, tl(h, rest), hc, KA.band_r(RP.mge(x, xs), RP.msort(xs), hm),
        lts_tl(h, x, xs, rest, KA.nateq_ok(x, h, Equal.sym(Bool, True{}, KA.nateq(x, h), eb)), hl), hr)
    case False{}:
      hr

def red_tl.m(+h: Nat, +c: S.Z, m: List<&2, Nat>, +rest: List<&2, R.ZTerm>,
  hc: {RP.nz(c) == True{} : Bool}, hm: {RP.msort(m) == True{} : Bool}, hl: {RP.mlts(m, rest) == True{} : Bool},
  hr: {RP.red(tl(h, rest)) == True{} : Bool}) -> {RP.red(tl.dec(hd(h, m), c, m, tl(h, rest))) == True{} : Bool}:
  match m:
    case Nil{}:
      hr
    case Con{+x, +xs}:
      red_tl.x(KA.nateq(x, h), h, c, x, xs, rest, {==}, hc, hm, hl, hr)

def red_tl(+h: Nat, p: List<&2, R.ZTerm>, +hp: {RP.red(p) == True{} : Bool}) -> {RP.red(tl(h, p)) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{+c, +m}, +rest}:
      red_tl.m(h, c, m, rest, RP.red_c(c, m, rest, hp), RP.red_m(c, m, rest, hp), RP.red_l(c, m, rest, hp), red_tl(h, rest, RP.red_r(c, m, rest, hp)))

# Bounds on the variables and the degrees
# ---------------------------------------

# every variable of p is at least h
def abv(+h: Nat, p: List<&2, R.ZTerm>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{R.ZTerm{c, m}, rest}:
      KA.band(RP.mge(h, m), abv(h, rest))

# every variable of m is below n
def mbl(+n: Nat, m: List<&2, Nat>) -> Bool:
  match m:
    case Nil{}:
      True{}
    case Con{v, vs}:
      KA.band(KA.natle(1n+v, n), mbl(n, vs))

def blw(+n: Nat, p: List<&2, R.ZTerm>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{R.ZTerm{c, m}, rest}:
      KA.band(mbl(n, m), blw(n, rest))

def mlen(m: List<&2, Nat>) -> Nat:
  match m:
    case Nil{}:
      0n
    case Con{v, vs}:
      1n+mlen(vs)

# every monomial of p has at most d variables
def mln(+d: Nat, p: List<&2, R.ZTerm>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{R.ZTerm{c, m}, rest}:
      KA.band(KA.natle(mlen(m), d), mln(d, rest))

def mnil(m: List<&2, Nat>) -> Bool:
  match m:
    case Nil{}:
      True{}
    case Con{v, vs}:
      False{}

# every monomial of p is 1
def allc(p: List<&2, R.ZTerm>) -> Bool:
  match p:
    case Nil{}:
      True{}
    case Con{R.ZTerm{c, m}, rest}:
      KA.band(mnil(m), allc(rest))

def blw_noh.dec(b: Bool, +n: Nat, c: S.Z, +m: List<&2, Nat>, +r: List<&2, R.ZTerm>, hm: {mbl(n, m) == True{} : Bool}, hr: {blw(n, r) == True{} : Bool}) -> {blw(n, noh.dec(b, c, m, r)) == True{} : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      KA.band_i(mbl(n, m), blw(n, r), hm, hr)

def blw_noh(+n: Nat, +h: Nat, p: List<&2, R.ZTerm>, +hp: {blw(n, p) == True{} : Bool}) -> {blw(n, noh(h, p)) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{c, +m}, +rest}:
      blw_noh.dec(hd(h, m), n, c, m, noh(h, rest), KA.band_l(mbl(n, m), blw(n, rest), hp), blw_noh(n, h, rest, KA.band_r(mbl(n, m), blw(n, rest), hp)))

def mbl_tail(+n: Nat, m: List<&2, Nat>, h: {mbl(n, m) == True{} : Bool}) -> {mbl(n, mtail(m)) == True{} : Bool}:
  match m:
    case Nil{}:
      {==}
    case Con{+v, +vs}:
      KA.band_r(KA.natle(1n+v, n), mbl(n, vs), h)

def blw_tl.dec(b: Bool, +n: Nat, c: S.Z, +m: List<&2, Nat>, +r: List<&2, R.ZTerm>, hm: {mbl(n, m) == True{} : Bool}, hr: {blw(n, r) == True{} : Bool}) -> {blw(n, tl.dec(b, c, m, r)) == True{} : Bool}:
  match b:
    case True{}:
      KA.band_i(mbl(n, mtail(m)), blw(n, r), mbl_tail(n, m, hm), hr)
    case False{}:
      hr

def blw_tl(+n: Nat, +h: Nat, p: List<&2, R.ZTerm>, +hp: {blw(n, p) == True{} : Bool}) -> {blw(n, tl(h, p)) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{c, +m}, +rest}:
      blw_tl.dec(hd(h, m), n, c, m, tl(h, rest), KA.band_l(mbl(n, m), blw(n, rest), hp), blw_tl(n, h, rest, KA.band_r(mbl(n, m), blw(n, rest), hp)))

def mln_noh.dec(b: Bool, +d: Nat, c: S.Z, +m: List<&2, Nat>, +r: List<&2, R.ZTerm>, hm: {KA.natle(mlen(m), d) == True{} : Bool}, hr: {mln(d, r) == True{} : Bool}) -> {mln(d, noh.dec(b, c, m, r)) == True{} : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      KA.band_i(KA.natle(mlen(m), d), mln(d, r), hm, hr)

def mln_noh(+d: Nat, +h: Nat, p: List<&2, R.ZTerm>, +hp: {mln(d, p) == True{} : Bool}) -> {mln(d, noh(h, p)) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{c, +m}, +rest}:
      mln_noh.dec(hd(h, m), d, c, m, noh(h, rest), KA.band_l(KA.natle(mlen(m), d), mln(d, rest), hp), mln_noh(d, h, rest, KA.band_r(KA.natle(mlen(m), d), mln(d, rest), hp)))

def mlen_tail(m: List<&2, Nat>, +e: Nat, h: {KA.natle(mlen(m), 1n+e) == True{} : Bool}) -> {KA.natle(mlen(mtail(m)), e) == True{} : Bool}:
  match m:
    case Nil{}:
      {==}
    case Con{v, vs}:
      h

def mln_tl.dec(b: Bool, +e: Nat, c: S.Z, +m: List<&2, Nat>, +r: List<&2, R.ZTerm>, hm: {KA.natle(mlen(m), 1n+e) == True{} : Bool}, hr: {mln(e, r) == True{} : Bool}) -> {mln(e, tl.dec(b, c, m, r)) == True{} : Bool}:
  match b:
    case True{}:
      KA.band_i(KA.natle(mlen(mtail(m)), e), mln(e, r), mlen_tail(m, e, hm), hr)
    case False{}:
      hr

def mln_tl(+e: Nat, +h: Nat, p: List<&2, R.ZTerm>, +hp: {mln(1n+e, p) == True{} : Bool}) -> {mln(e, tl(h, p)) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{c, +m}, +rest}:
      mln_tl.dec(hd(h, m), e, c, m, tl(h, rest), KA.band_l(KA.natle(mlen(m), 1n+e), mln(1n+e, rest), hp), mln_tl(e, h, rest, KA.band_r(KA.natle(mlen(m), 1n+e), mln(1n+e, rest), hp)))

def mge_tail(+h: Nat, m: List<&2, Nat>, hm: {RP.mge(h, m) == True{} : Bool}) -> {RP.mge(h, mtail(m)) == True{} : Bool}:
  match m:
    case Nil{}:
      {==}
    case Con{+v, +vs}:
      KA.band_r(KA.natle(h, v), RP.mge(h, vs), hm)

def abv_tl.dec(b: Bool, +h: Nat, c: S.Z, +m: List<&2, Nat>, +r: List<&2, R.ZTerm>, hm: {RP.mge(h, m) == True{} : Bool}, hr: {abv(h, r) == True{} : Bool}) -> {abv(h, tl.dec(b, c, m, r)) == True{} : Bool}:
  match b:
    case True{}:
      KA.band_i(RP.mge(h, mtail(m)), abv(h, r), mge_tail(h, m, hm), hr)
    case False{}:
      hr

def abv_tl(+h: Nat, p: List<&2, R.ZTerm>, +hp: {abv(h, p) == True{} : Bool}) -> {abv(h, tl(h, p)) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{c, +m}, +rest}:
      abv_tl.dec(hd(h, m), h, c, m, tl(h, rest), KA.band_l(RP.mge(h, m), abv(h, rest), hp), abv_tl(h, rest, KA.band_r(RP.mge(h, m), abv(h, rest), hp)))

def lt_of_ne(h: Nat, x: Nat, h1: {KA.natle(h, x) == True{} : Bool}, h2: {False{} == KA.nateq(x, h) : Bool}) -> {KA.natle(1n+h, x) == True{} : Bool}:
  match h x:
    case 0n 0n:
      absurd({KA.natle(1n, 0n) == True{} : Bool}, KA.ft(h2))
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      absurd({KA.natle(2n+p, 0n) == True{} : Bool}, KA.ft(h1))
    case 1n+p 1n+q:
      lt_of_ne(p, q, h1, h2)

def abv_noh.x(b: Bool, +h: Nat, +c: S.Z, +x: Nat, +xs: List<&2, Nat>, +r: List<&2, R.ZTerm>, eb: {b == KA.nateq(x, h) : Bool},
  +ha: {RP.mge(h, Con{x, xs}) == True{} : Bool}, hs: {RP.msort(Con{x, xs}) == True{} : Bool}, hr: {abv(1n+h, r) == True{} : Bool})
  -> {abv(1n+h, noh.dec(b, c, Con{x, xs}, r)) == True{} : Bool}:
  match b:
    case True{}:
      hr
    case False{}:
      +hx = lt_of_ne(h, x, KA.band_l(KA.natle(h, x), RP.mge(h, xs), ha), eb)
      KA.band_i(RP.mge(1n+h, Con{x, xs}), abv(1n+h, r),
        KA.band_i(KA.natle(1n+h, x), RP.mge(1n+h, xs), hx, RP.mge_trans(1n+h, x, xs, hx, KA.band_l(RP.mge(x, xs), RP.msort(xs), hs))), hr)

def abv_noh.m(+h: Nat, +c: S.Z, m: List<&2, Nat>, +r: List<&2, R.ZTerm>,
  ha: {RP.mge(h, m) == True{} : Bool}, hs: {RP.msort(m) == True{} : Bool}, hr: {abv(1n+h, r) == True{} : Bool})
  -> {abv(1n+h, noh.dec(hd(h, m), c, m, r)) == True{} : Bool}:
  match m:
    case Nil{}:
      hr
    case Con{+x, +xs}:
      abv_noh.x(KA.nateq(x, h), h, c, x, xs, r, {==}, ha, hs, hr)

# the terms without h: every variable is above h
def abv_noh(+h: Nat, p: List<&2, R.ZTerm>, +ha: {abv(h, p) == True{} : Bool}, +hr: {RP.red(p) == True{} : Bool}) -> {abv(1n+h, noh(h, p)) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{+c, +m}, +rest}:
      abv_noh.m(h, c, m, noh(h, rest), KA.band_l(RP.mge(h, m), abv(h, rest), ha), RP.red_m(c, m, rest, hr),
        abv_noh(h, rest, KA.band_r(RP.mge(h, m), abv(h, rest), ha), RP.red_r(c, m, rest, hr)))

# No variables left: a reduced polynomial is one nonzero constant
# ---------------------------------------------------------------

def mnil0(m: List<&2, Nat>, h: {KA.natle(mlen(m), 0n) == True{} : Bool}) -> {mnil(m) == True{} : Bool}:
  match m:
    case Nil{}:
      {==}
    case Con{v, vs}:
      absurd({mnil(Con{v, vs}) == True{} : Bool}, KA.ft(h))

def allc_mln(p: List<&2, R.ZTerm>, +h: {mln(0n, p) == True{} : Bool}) -> {allc(p) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{c, +m}, +rest}:
      KA.band_i(mnil(m), allc(rest), mnil0(m, KA.band_l(KA.natle(mlen(m), 0n), mln(0n, rest), h)), allc_mln(rest, KA.band_r(KA.natle(mlen(m), 0n), mln(0n, rest), h)))

def mnil_bnd(+h: Nat, +n: Nat, m: List<&2, Nat>, hle: {KA.natle(n, h) == True{} : Bool}, ha: {RP.mge(h, m) == True{} : Bool}, hb: {mbl(n, m) == True{} : Bool}) -> {mnil(m) == True{} : Bool}:
  match m:
    case Nil{}:
      {==}
    case Con{+v, +vs}:
      absurd({mnil(Con{v, vs}) == True{} : Bool}, KA.natlt_irr(v,
        KA.natle_trans(1n+v, h, v, KA.natle_trans(1n+v, n, h, KA.band_l(KA.natle(1n+v, n), mbl(n, vs), hb), hle), KA.band_l(KA.natle(h, v), RP.mge(h, vs), ha))))

def allc_bnd(+h: Nat, +n: Nat, p: List<&2, R.ZTerm>, +hle: {KA.natle(n, h) == True{} : Bool}, +ha: {abv(h, p) == True{} : Bool}, +hb: {blw(n, p) == True{} : Bool}) -> {allc(p) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{c, +m}, +rest}:
      KA.band_i(mnil(m), allc(rest), mnil_bnd(h, n, m, hle, KA.band_l(RP.mge(h, m), abv(h, rest), ha), KA.band_l(mbl(n, m), blw(n, rest), hb)),
        allc_bnd(h, n, rest, hle, KA.band_r(RP.mge(h, m), abv(h, rest), ha), KA.band_r(mbl(n, m), blw(n, rest), hb)))

def const_n(+z: List<&2, S.Z>, +c: S.Z, +d: S.Z, n: List<&2, Nat>, +r2: List<&2, R.ZTerm>,
  hr: {RP.red(Con{R.ZTerm{c, Nil{}}, Con{R.ZTerm{d, n}, r2}}) == True{} : Bool}, hc: {allc(Con{R.ZTerm{d, n}, r2}) == True{} : Bool})
  -> {RP.nz(R.epoly(z, Con{R.ZTerm{c, Nil{}}, Con{R.ZTerm{d, n}, r2}})) == True{} : Bool}:
  match n:
    case Nil{}:
      absurd({RP.nz(R.epoly(z, Con{R.ZTerm{c, Nil{}}, Con{R.ZTerm{d, Nil{}}, r2}})) == True{} : Bool},
        KA.ft(KA.band_l(RP.islt(NR.mcmp(Nil{}, Nil{})), RP.mlts(Nil{}, r2), RP.red_l(c, Nil{}, Con{R.ZTerm{d, Nil{}}, r2}, hr))))
    case Con{v, vs}:
      absurd({RP.nz(R.epoly(z, Con{R.ZTerm{c, Nil{}}, Con{R.ZTerm{d, Con{v, vs}}, r2}})) == True{} : Bool},
        KA.ft(KA.band_l(mnil(Con{v, vs}), allc(r2), hc)))

def const_r(+z: List<&2, S.Z>, +c: S.Z, rest: List<&2, R.ZTerm>, hr: {RP.red(Con{R.ZTerm{c, Nil{}}, rest}) == True{} : Bool}, hc: {allc(rest) == True{} : Bool})
  -> {RP.nz(R.epoly(z, Con{R.ZTerm{c, Nil{}}, rest})) == True{} : Bool}:
  match rest:
    case Nil{}:
      %ZL.add_zero(S.Z.mul(c, S.Zpos{S.XH{}})) : {RP.nz(_) == True{} : Bool}
      %ZL.mul_one(c) : {RP.nz(_) == True{} : Bool}
      RP.red_c(c, Nil{}, Nil{}, hr)
    case Con{R.ZTerm{+d, +n}, +r2}:
      const_n(z, c, d, n, r2, hr, hc)

def const_m(+z: List<&2, S.Z>, +c: S.Z, m: List<&2, Nat>, +rest: List<&2, R.ZTerm>, hr: {RP.red(Con{R.ZTerm{c, m}, rest}) == True{} : Bool}, hc: {allc(Con{R.ZTerm{c, m}, rest}) == True{} : Bool})
  -> {RP.nz(R.epoly(z, Con{R.ZTerm{c, m}, rest})) == True{} : Bool}:
  match m:
    case Nil{}:
      const_r(z, c, rest, hr, KA.band_r(mnil(Nil{}), allc(rest), hc))
    case Con{v, vs}:
      absurd({RP.nz(R.epoly(z, Con{R.ZTerm{c, Con{v, vs}}, rest})) == True{} : Bool}, KA.ft(KA.band_l(mnil(Con{v, vs}), allc(rest), hc)))

# a reduced polynomial with no variables, not zero, is nonzero everywhere
def const_ok(+z: List<&2, S.Z>, p: List<&2, R.ZTerm>, hr: {RP.red(p) == True{} : Bool}, hc: {allc(p) == True{} : Bool}, hne: {isnil(p) == False{} : Bool}) -> {RP.nz(R.epoly(z, p)) == True{} : Bool}:
  match p:
    case Nil{}:
      absurd({RP.nz(R.epoly(z, Nil{})) == True{} : Bool}, KA.tf(hne))
    case Con{R.ZTerm{+c, +m}, +rest}:
      const_m(z, c, m, rest, hr, hc)

# Points
# ------

def one() -> S.Z:
  S.Zpos{S.XH{}}

def ones(n: Nat) -> List<&2, S.Z>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{one(), ones(k)}

# z with coordinate h set to t (padded with ones)
def zset(h: Nat, z: List<&2, S.Z>, t: S.Z) -> List<&2, S.Z>:
  match h z:
    case 0n Nil{}:
      Con{t, Nil{}}
    case 0n Con{x, xs}:
      Con{t, xs}
    case 1n+g Nil{}:
      Con{one(), zset(g, Nil{}, t)}
    case 1n+g Con{x, xs}:
      Con{x, zset(g, xs, t)}

def set_at(h: Nat, z: List<&2, S.Z>, +t: S.Z) -> {t == E.lookup(zset(h, z, t), h) : S.Z}:
  match h z:
    case 0n Nil{}:
      {==}
    case 0n Con{x, xs}:
      {==}
    case 1n+g Nil{}:
      set_at(g, Nil{}, t)
    case 1n+g Con{x, xs}:
      set_at(g, xs, t)

# a nonzero coordinate other than h is unchanged
def set_other(h: Nat, z: List<&2, S.Z>, +t: S.Z, v: Nat, hne: {KA.nateq(v, h) == False{} : Bool}, hz: {RP.nz(E.lookup(z, v)) == True{} : Bool}) -> {E.lookup(z, v) == E.lookup(zset(h, z, t), v) : S.Z}:
  match h z v:
    case 0n Nil{} 0n:
      absurd({E.lookup(Nil{}, 0n) == E.lookup(zset(0n, Nil{}, t), 0n) : S.Z}, KA.tf(hne))
    case 0n Nil{} 1n+w:
      absurd({E.lookup(Nil{}, 1n+w) == E.lookup(zset(0n, Nil{}, t), 1n+w) : S.Z}, KA.ft(hz))
    case 0n Con{x, xs} 0n:
      absurd({E.lookup(Con{x, xs}, 0n) == E.lookup(zset(0n, Con{x, xs}, t), 0n) : S.Z}, KA.tf(hne))
    case 0n Con{x, xs} 1n+w:
      {==}
    case 1n+g Nil{} 0n:
      absurd({E.lookup(Nil{}, 0n) == E.lookup(zset(1n+g, Nil{}, t), 0n) : S.Z}, KA.ft(hz))
    case 1n+g Nil{} 1n+w:
      absurd({E.lookup(Nil{}, 1n+w) == E.lookup(zset(1n+g, Nil{}, t), 1n+w) : S.Z}, KA.ft(hz))
    case 1n+g Con{x, xs} 0n:
      {==}
    case 1n+g Con{x, xs} 1n+w:
      set_other(g, xs, t, w, hne, hz)

# every coordinate below n is nonzero
def nzb(+z: List<&2, S.Z>, n: Nat) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n++k:
      KA.band(RP.nz(E.lookup(z, k)), nzb(z, k))

def nzb_at.dec(b: Bool, +z: List<&2, S.Z>, +k: Nat, +v: Nat, eb: {b == KA.natle(1n+v, k) : Bool}, hv: {KA.natle(1n+v, 1n+k) == True{} : Bool},
  hk: {RP.nz(E.lookup(z, k)) == True{} : Bool}, rec: {KA.natle(1n+v, k) == True{} : Bool} -> {RP.nz(E.lookup(z, v)) == True{} : Bool})
  -> {RP.nz(E.lookup(z, v)) == True{} : Bool}:
  match b:
    case True{}:
      rec(Equal.sym(Bool, True{}, KA.natle(1n+v, k), eb))
    case False{}:
      %Equal.sym(Nat, v, k, KA.natle_antisym(v, k, hv, KA.natle_of_nlt(v, k, Equal.sym(Bool, False{}, KA.natle(1n+v, k), eb)))) : {RP.nz(E.lookup(z, _)) == True{} : Bool}
      hk

def nzb_at(+z: List<&2, S.Z>, n: Nat, +v: Nat, +hb: {nzb(z, n) == True{} : Bool}, hv: {KA.natle(1n+v, n) == True{} : Bool}) -> {RP.nz(E.lookup(z, v)) == True{} : Bool}:
  match n:
    case 0n:
      absurd({RP.nz(E.lookup(z, v)) == True{} : Bool}, KA.ft(hv))
    case 1n++k:
      nzb_at.dec(KA.natle(1n+v, k), z, k, v, {==}, hv, KA.band_l(RP.nz(E.lookup(z, k)), nzb(z, k), hb), hk2 => nzb_at(z, k, v, KA.band_r(RP.nz(E.lookup(z, k)), nzb(z, k), hb), hk2))

def nz_set.dec(b: Bool, +h: Nat, +z: List<&2, S.Z>, +t: S.Z, +k: Nat, eb: {b == KA.nateq(k, h) : Bool}, ht: {RP.nz(t) == True{} : Bool}, +hk: {RP.nz(E.lookup(z, k)) == True{} : Bool})
  -> {RP.nz(E.lookup(zset(h, z, t), k)) == True{} : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, k, h, KA.nateq_ok(k, h, Equal.sym(Bool, True{}, KA.nateq(k, h), eb))) : {RP.nz(E.lookup(zset(h, z, t), _)) == True{} : Bool}
      %set_at(h, z, t) : {RP.nz(_) == True{} : Bool}
      ht
    case False{}:
      %set_other(h, z, t, k, Equal.sym(Bool, False{}, KA.nateq(k, h), eb), hk) : {RP.nz(_) == True{} : Bool}
      hk

def nzb_set(+h: Nat, +z: List<&2, S.Z>, +t: S.Z, n: Nat, +ht: {RP.nz(t) == True{} : Bool}, +hb: {nzb(z, n) == True{} : Bool}) -> {nzb(zset(h, z, t), n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++k:
      KA.band_i(RP.nz(E.lookup(zset(h, z, t), k)), nzb(zset(h, z, t), k),
        nz_set.dec(KA.nateq(k, h), h, z, t, k, {==}, ht, KA.band_l(RP.nz(E.lookup(z, k)), nzb(z, k), hb)),
        nzb_set(h, z, t, k, ht, KA.band_r(RP.nz(E.lookup(z, k)), nzb(z, k), hb)))

def ones_at(m: Nat, k: Nat, h: {KA.natle(1n+k, m) == True{} : Bool}) -> {RP.nz(E.lookup(ones(m), k)) == True{} : Bool}:
  match m k:
    case 0n 0n:
      absurd({RP.nz(E.lookup(ones(0n), 0n)) == True{} : Bool}, KA.ft(h))
    case 0n 1n+j:
      absurd({RP.nz(E.lookup(ones(0n), 1n+j)) == True{} : Bool}, KA.ft(h))
    case 1n+i 0n:
      {==}
    case 1n+i 1n+j:
      ones_at(i, j, h)

def nzb_ones(+m: Nat, n: Nat, h: {KA.natle(n, m) == True{} : Bool}) -> {nzb(ones(m), n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n++k:
      +h2 = h
      KA.band_i(RP.nz(E.lookup(ones(m), k)), nzb(ones(m), k), ones_at(m, k, h2), nzb_ones(m, k, KA.natle_trans(k, 1n+k, m, KA.natle_succ(k, k, KA.natle_refl(k)), h2)))

# Changing a coordinate the polynomial does not read
def emono_frame(+h: Nat, +t: S.Z, +y: List<&2, S.Z>, +n: Nat, m: List<&2, Nat>,
  ha: {RP.mge(1n+h, m) == True{} : Bool}, hb: {mbl(n, m) == True{} : Bool}, +hy: {nzb(y, n) == True{} : Bool})
  -> {R.emono(y, m) == R.emono(zset(h, y, t), m) : S.Z}:
  match m:
    case Nil{}:
      {==}
    case Con{+v, +vs}:
      +ha2 = ha
      +hb2 = hb
      %set_other(h, y, t, v, Equal.trans(Bool, KA.nateq(v, h), KA.nateq(h, v), False{}, KA.nateq_sym(v, h), KA.natlt_ne(h, v, KA.band_l(KA.natle(1n+h, v), RP.mge(1n+h, vs), ha2))),
          nzb_at(y, n, v, hy, KA.band_l(KA.natle(1n+v, n), mbl(n, vs), hb2)))
        : {S.Z.mul(E.lookup(y, v), R.emono(y, vs)) == S.Z.mul(_, R.emono(zset(h, y, t), vs)) : S.Z}
      %emono_frame(h, t, y, n, vs, KA.band_r(KA.natle(1n+h, v), RP.mge(1n+h, vs), ha2), KA.band_r(KA.natle(1n+v, n), mbl(n, vs), hb2), hy)
        : {S.Z.mul(E.lookup(y, v), R.emono(y, vs)) == S.Z.mul(E.lookup(y, v), _) : S.Z}
      {==}

def epoly_frame(+h: Nat, +t: S.Z, +y: List<&2, S.Z>, +n: Nat, p: List<&2, R.ZTerm>,
  +ha: {abv(1n+h, p) == True{} : Bool}, +hb: {blw(n, p) == True{} : Bool}, +hy: {nzb(y, n) == True{} : Bool})
  -> {R.epoly(y, p) == R.epoly(zset(h, y, t), p) : S.Z}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{+c, +m}, +rest}:
      %emono_frame(h, t, y, n, m, KA.band_l(RP.mge(1n+h, m), abv(1n+h, rest), ha), KA.band_l(mbl(n, m), blw(n, rest), hb), hy)
        : {S.Z.add(S.Z.mul(c, R.emono(y, m)), R.epoly(y, rest)) == S.Z.add(S.Z.mul(c, _), R.epoly(zset(h, y, t), rest)) : S.Z}
      %epoly_frame(h, t, y, n, rest, KA.band_r(RP.mge(1n+h, m), abv(1n+h, rest), ha), KA.band_r(mbl(n, m), blw(n, rest), hb), hy)
        : {S.Z.add(S.Z.mul(c, R.emono(y, m)), R.epoly(y, rest)) == S.Z.add(S.Z.mul(c, R.emono(y, m)), _) : S.Z}
      {==}

# Integers
# --------

def two() -> S.Z:
  S.Zpos{S.XO{S.XH{}}}

def mul_nz(a: S.Z, b: S.Z, ha: {RP.nz(a) == True{} : Bool}, hb: {RP.nz(b) == True{} : Bool}) -> {RP.nz(S.Z.mul(a, b)) == True{} : Bool}:
  match a b:
    case S.Z0{} b:
      absurd({RP.nz(S.Z.mul(S.Z0{}, b)) == True{} : Bool}, KA.ft(ha))
    case S.Zpos{p} S.Z0{}:
      absurd({RP.nz(S.Z.mul(S.Zpos{p}, S.Z0{})) == True{} : Bool}, KA.ft(hb))
    case S.Zpos{p} S.Zpos{q}:
      {==}
    case S.Zpos{p} S.Zneg{q}:
      {==}
    case S.Zneg{p} S.Z0{}:
      absurd({RP.nz(S.Z.mul(S.Zneg{p}, S.Z0{})) == True{} : Bool}, KA.ft(hb))
    case S.Zneg{p} S.Zpos{q}:
      {==}
    case S.Zneg{p} S.Zneg{q}:
      {==}

# 1 + 2b is odd, so not 0
def odd_nz(b: S.Z) -> {RP.nz(S.Z.add(one(), S.Z.mul(two(), b))) == True{} : Bool}:
  match b:
    case S.Z0{}:
      {==}
    case S.Zpos{q}:
      {==}
    case S.Zneg{q}:
      {==}

# a + 2a b = a (1 + 2b)
def odd_id(+a: S.Z, +b: S.Z) -> {S.Z.mul(a, S.Z.add(one(), S.Z.mul(two(), b))) == S.Z.add(a, S.Z.mul(S.Z.mul(two(), a), b)) : S.Z}:
  R.ring_eq([a, b], E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZCst{one()}, E.ZMul{E.ZCst{two()}, E.ZVar{1n}}}},
    E.ZAdd{E.ZVar{0n}, E.ZMul{E.ZMul{E.ZCst{two()}, E.ZVar{0n}}, E.ZVar{1n}}}, {==})

# The split's sides
# -----------------

def tl_lt.x(b: Bool, +h: Nat, +n: Nat, c: S.Z, +x: Nat, +xs: List<&2, Nat>, r: List<&2, R.ZTerm>, eb: {b == KA.nateq(x, h) : Bool},
  hm: {mbl(n, Con{x, xs}) == True{} : Bool}, hne: {isnil(tl.dec(b, c, Con{x, xs}, r)) == False{} : Bool},
  rec: {isnil(r) == False{} : Bool} -> {KA.natle(1n+h, n) == True{} : Bool}) -> {KA.natle(1n+h, n) == True{} : Bool}:
  match b:
    case True{}:
      %KA.nateq_ok(x, h, Equal.sym(Bool, True{}, KA.nateq(x, h), eb)) : {KA.natle(1n+_, n) == True{} : Bool}
      KA.band_l(KA.natle(1n+x, n), mbl(n, xs), hm)
    case False{}:
      rec(hne)

def tl_lt.m(+h: Nat, +n: Nat, c: S.Z, m: List<&2, Nat>, r: List<&2, R.ZTerm>, hm: {mbl(n, m) == True{} : Bool},
  hne: {isnil(tl.dec(hd(h, m), c, m, r)) == False{} : Bool},
  rec: {isnil(r) == False{} : Bool} -> {KA.natle(1n+h, n) == True{} : Bool}) -> {KA.natle(1n+h, n) == True{} : Bool}:
  match m:
    case Nil{}:
      rec(hne)
    case Con{+x, +xs}:
      tl_lt.x(KA.nateq(x, h), h, n, c, x, xs, r, {==}, hm, hne, rec)

# a term beginning with h has h below the bound
def tl_lt(+h: Nat, +n: Nat, p: List<&2, R.ZTerm>, hb: {blw(n, p) == True{} : Bool}, hne: {isnil(tl(h, p)) == False{} : Bool}) -> {KA.natle(1n+h, n) == True{} : Bool}:
  match p:
    case Nil{}:
      absurd({KA.natle(1n+h, n) == True{} : Bool}, KA.tf(hne))
    case Con{R.ZTerm{c, +m}, +rest}:
      +hb2 = hb
      tl_lt.m(h, n, c, m, tl(h, rest), KA.band_l(mbl(n, m), blw(n, rest), hb2), hne, e => tl_lt(h, n, rest, KA.band_r(mbl(n, m), blw(n, rest), hb2), e))

def split_ne.dec(b: Bool, c: S.Z, m: List<&2, Nat>, +nr: List<&2, R.ZTerm>, +tr: List<&2, R.ZTerm>,
  hn: {isnil(noh.dec(b, c, m, nr)) == True{} : Bool}) -> {isnil(tl.dec(b, c, m, tr)) == False{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      absurd({isnil(tl.dec(False{}, c, m, tr)) == False{} : Bool}, KA.ft(hn))

# p is not zero and has no terms without h: it has terms with h
def split_ne(+h: Nat, p: List<&2, R.ZTerm>, hne: {isnil(p) == False{} : Bool}, hn: {isnil(noh(h, p)) == True{} : Bool}) -> {isnil(tl(h, p)) == False{} : Bool}:
  match p:
    case Nil{}:
      absurd({isnil(tl(h, Nil{})) == False{} : Bool}, KA.tf(hne))
    case Con{R.ZTerm{+c, +m}, +rest}:
      split_ne.dec(hd(h, m), c, m, noh(h, rest), tl(h, rest), hn)

# The witness
# -----------

def wit.step(b: Bool, +h: Nat, +wa: List<&2, S.Z>, wb: List<&2, S.Z>, a: List<&2, R.ZTerm>) -> List<&2, S.Z>:
  match b:
    case True{}:
      wb
    case False{}:
      zset(h, wa, S.Z.mul(two(), R.epoly(wa, a)))

# k bounds n - h, d the monomials' lengths
def wit.go(k: Nat, d: Nat, +h: Nat, +n: Nat, +p: List<&2, R.ZTerm>) -> List<&2, S.Z>:
  match k d:
    case 0n 0n:
      ones(n)
    case 0n 1n++e:
      ones(n)
    case 1n++j 0n:
      ones(n)
    case 1n++j 1n++e:
      wit.step(isnil(noh(h, p)), h, wit.go(j, 1n+e, 1n+h, n, noh(h, p)), wit.go(1n+j, e, h, n, tl(h, p)), noh(h, p))

# A is not zero: x_h = 2a
def wit_nz(+h: Nat, +n: Nat, +p: List<&2, R.ZTerm>, +wa: List<&2, S.Z>,
  +hr: {RP.red(p) == True{} : Bool}, +ha: {abv(h, p) == True{} : Bool}, +hb: {blw(n, p) == True{} : Bool},
  hz: {RP.nz(R.epoly(wa, noh(h, p))) == True{} : Bool}, hy: {nzb(wa, n) == True{} : Bool})
  -> {RP.nz(R.epoly(zset(h, wa, S.Z.mul(two(), R.epoly(wa, noh(h, p)))), p)) == True{} : Bool}:
  %split_ok(zset(h, wa, S.Z.mul(two(), R.epoly(wa, noh(h, p)))), h, p) : {RP.nz(_) == True{} : Bool}
  %epoly_frame(h, S.Z.mul(two(), R.epoly(wa, noh(h, p))), wa, n, noh(h, p), abv_noh(h, p, ha, hr), blw_noh(n, h, p, hb), hy)
    : {RP.nz(S.Z.add(_, S.Z.mul(E.lookup(zset(h, wa, S.Z.mul(two(), R.epoly(wa, noh(h, p)))), h), R.epoly(zset(h, wa, S.Z.mul(two(), R.epoly(wa, noh(h, p)))), tl(h, p))))) == True{} : Bool}
  %set_at(h, wa, S.Z.mul(two(), R.epoly(wa, noh(h, p))))
    : {RP.nz(S.Z.add(R.epoly(wa, noh(h, p)), S.Z.mul(_, R.epoly(zset(h, wa, S.Z.mul(two(), R.epoly(wa, noh(h, p)))), tl(h, p))))) == True{} : Bool}
  %odd_id(R.epoly(wa, noh(h, p)), R.epoly(zset(h, wa, S.Z.mul(two(), R.epoly(wa, noh(h, p)))), tl(h, p))) : {RP.nz(_) == True{} : Bool}
  mul_nz(R.epoly(wa, noh(h, p)), S.Z.add(one(), S.Z.mul(two(), R.epoly(zset(h, wa, S.Z.mul(two(), R.epoly(wa, noh(h, p)))), tl(h, p)))), hz,
    odd_nz(R.epoly(zset(h, wa, S.Z.mul(two(), R.epoly(wa, noh(h, p)))), tl(h, p))))

def wit_ok.a(+h: Nat, +n: Nat, +p: List<&2, R.ZTerm>, +wa: List<&2, S.Z>,
  +hr: {RP.red(p) == True{} : Bool}, +ha: {abv(h, p) == True{} : Bool}, +hb: {blw(n, p) == True{} : Bool},
  +ra: {KA.band(RP.nz(R.epoly(wa, noh(h, p))), nzb(wa, n)) == True{} : Bool})
  -> {KA.band(RP.nz(R.epoly(zset(h, wa, S.Z.mul(two(), R.epoly(wa, noh(h, p)))), p)), nzb(zset(h, wa, S.Z.mul(two(), R.epoly(wa, noh(h, p)))), n)) == True{} : Bool}:
  KA.band_i(RP.nz(R.epoly(zset(h, wa, S.Z.mul(two(), R.epoly(wa, noh(h, p)))), p)), nzb(zset(h, wa, S.Z.mul(two(), R.epoly(wa, noh(h, p)))), n),
    wit_nz(h, n, p, wa, hr, ha, hb, KA.band_l(RP.nz(R.epoly(wa, noh(h, p))), nzb(wa, n), ra), KA.band_r(RP.nz(R.epoly(wa, noh(h, p))), nzb(wa, n), ra)),
    nzb_set(h, wa, S.Z.mul(two(), R.epoly(wa, noh(h, p))), n, mul_nz(two(), R.epoly(wa, noh(h, p)), {==}, KA.band_l(RP.nz(R.epoly(wa, noh(h, p))), nzb(wa, n), ra)),
      KA.band_r(RP.nz(R.epoly(wa, noh(h, p))), nzb(wa, n), ra)))

# A is zero: p = x_h B
def wit_ok.b(+h: Nat, +n: Nat, +p: List<&2, R.ZTerm>, +wb: List<&2, S.Z>, ea: {Nil{} == noh(h, p) : List<&2, R.ZTerm>},
  hb: {blw(n, p) == True{} : Bool}, ht: {isnil(tl(h, p)) == False{} : Bool},
  +rb: {KA.band(RP.nz(R.epoly(wb, tl(h, p))), nzb(wb, n)) == True{} : Bool})
  -> {KA.band(RP.nz(R.epoly(wb, p)), nzb(wb, n)) == True{} : Bool}:
  KA.band_i(RP.nz(R.epoly(wb, p)), nzb(wb, n),
    (%split_ok(wb, h, p) : {RP.nz(_) == True{} : Bool}
     %ea : {RP.nz(S.Z.add(R.epoly(wb, _), S.Z.mul(E.lookup(wb, h), R.epoly(wb, tl(h, p))))) == True{} : Bool}
     mul_nz(E.lookup(wb, h), R.epoly(wb, tl(h, p)), nzb_at(wb, n, h, KA.band_r(RP.nz(R.epoly(wb, tl(h, p))), nzb(wb, n), rb), tl_lt(h, n, p, hb, ht)),
       KA.band_l(RP.nz(R.epoly(wb, tl(h, p))), nzb(wb, n), rb))),
    KA.band_r(RP.nz(R.epoly(wb, tl(h, p))), nzb(wb, n), rb))

def wit_ok.step(b: Bool, +h: Nat, +n: Nat, +p: List<&2, R.ZTerm>, +wa: List<&2, S.Z>, +wb: List<&2, S.Z>,
  +eb: {b == isnil(noh(h, p)) : Bool},
  +hr: {RP.red(p) == True{} : Bool}, +ha: {abv(h, p) == True{} : Bool}, +hb: {blw(n, p) == True{} : Bool}, hne: {isnil(p) == False{} : Bool},
  iha: {isnil(noh(h, p)) == False{} : Bool} -> {KA.band(RP.nz(R.epoly(wa, noh(h, p))), nzb(wa, n)) == True{} : Bool},
  ihb: {isnil(tl(h, p)) == False{} : Bool} -> {KA.band(RP.nz(R.epoly(wb, tl(h, p))), nzb(wb, n)) == True{} : Bool})
  -> {KA.band(RP.nz(R.epoly(wit.step(b, h, wa, wb, noh(h, p)), p)), nzb(wit.step(b, h, wa, wb, noh(h, p)), n)) == True{} : Bool}:
  match b:
    case True{}:
      +ht = split_ne(h, p, hne, Equal.sym(Bool, True{}, isnil(noh(h, p)), eb))
      wit_ok.b(h, n, p, wb, nil_of(noh(h, p), Equal.sym(Bool, True{}, isnil(noh(h, p)), eb)), hb, ht, ihb(ht))
    case False{}:
      wit_ok.a(h, n, p, wa, hr, ha, hb, iha(Equal.sym(Bool, False{}, isnil(noh(h, p)), eb)))

def wit_base(+n: Nat, +p: List<&2, R.ZTerm>, hr: {RP.red(p) == True{} : Bool}, hc: {allc(p) == True{} : Bool}, hne: {isnil(p) == False{} : Bool})
  -> {KA.band(RP.nz(R.epoly(ones(n), p)), nzb(ones(n), n)) == True{} : Bool}:
  KA.band_i(RP.nz(R.epoly(ones(n), p)), nzb(ones(n), n), const_ok(ones(n), p, hr, hc, hne), nzb_ones(n, n, KA.natle_refl(n)))

def wit_ok(k: Nat, d: Nat, +h: Nat, +n: Nat, +p: List<&2, R.ZTerm>,
  +hr: {RP.red(p) == True{} : Bool}, +ha: {abv(h, p) == True{} : Bool}, +hb: {blw(n, p) == True{} : Bool}, +hd: {mln(d, p) == True{} : Bool},
  +hk: {KA.natle(n, Nat.add(h, k)) == True{} : Bool}, +hne: {isnil(p) == False{} : Bool})
  -> {KA.band(RP.nz(R.epoly(wit.go(k, d, h, n, p), p)), nzb(wit.go(k, d, h, n, p), n)) == True{} : Bool}:
  match k d:
    case 0n 0n:
      wit_base(n, p, hr, allc_mln(p, hd), hne)
    case 0n 1n++e:
      wit_base(n, p, hr, allc_bnd(h, n, p, KA.natle_rw(n, Nat.add(h, 0n), h, Equal.sym(Nat, h, Nat.add(h, 0n), N.add_zero(h)), hk), ha, hb), hne)
    case 1n++j 0n:
      wit_base(n, p, hr, allc_mln(p, hd), hne)
    case 1n++j 1n++e:
      wit_ok.step(isnil(noh(h, p)), h, n, p, wit.go(j, 1n+e, 1n+h, n, noh(h, p)), wit.go(1n+j, e, h, n, tl(h, p)), {==}, hr, ha, hb, hne,
        ea => wit_ok(j, 1n+e, 1n+h, n, noh(h, p), red_noh(h, p, hr), abv_noh(h, p, ha, hr), blw_noh(n, h, p, hb), mln_noh(1n+e, h, p, hd),
          KA.natle_rw(n, Nat.add(h, 1n+j), 1n+Nat.add(h, j), Equal.sym(Nat, 1n+Nat.add(h, j), Nat.add(h, 1n+j), N.add_succ(h, j)), hk), ea),
        eb => wit_ok(1n+j, e, h, n, tl(h, p), red_tl(h, p, hr), abv_tl(h, p, ha), blw_tl(n, h, p, hb), mln_tl(e, h, p, hd), hk, eb))

# Bounds of a polynomial
# ----------------------

def mbnd(m: List<&2, Nat>) -> Nat:
  match m:
    case Nil{}:
      0n
    case Con{v, vs}:
      Nat.add(1n+v, mbnd(vs))

def pbnd(p: List<&2, R.ZTerm>) -> Nat:
  match p:
    case Nil{}:
      0n
    case Con{R.ZTerm{c, m}, rest}:
      Nat.add(mbnd(m), pbnd(rest))

def psz(p: List<&2, R.ZTerm>) -> Nat:
  match p:
    case Nil{}:
      0n
    case Con{R.ZTerm{c, m}, rest}:
      Nat.add(mlen(m), psz(rest))

def mbl_mono(+n: Nat, +n2: Nat, m: List<&2, Nat>, +h: {KA.natle(n, n2) == True{} : Bool}, +hm: {mbl(n, m) == True{} : Bool}) -> {mbl(n2, m) == True{} : Bool}:
  match m:
    case Nil{}:
      {==}
    case Con{+v, +vs}:
      KA.band_i(KA.natle(1n+v, n2), mbl(n2, vs), KA.natle_trans(1n+v, n, n2, KA.band_l(KA.natle(1n+v, n), mbl(n, vs), hm), h),
        mbl_mono(n, n2, vs, h, KA.band_r(KA.natle(1n+v, n), mbl(n, vs), hm)))

def mbl_bnd(m: List<&2, Nat>) -> {mbl(mbnd(m), m) == True{} : Bool}:
  match m:
    case Nil{}:
      {==}
    case Con{+v, +vs}:
      KA.band_i(KA.natle(1n+v, Nat.add(1n+v, mbnd(vs))), mbl(Nat.add(1n+v, mbnd(vs)), vs), KA.natle_add_r(1n+v, mbnd(vs)),
        mbl_mono(mbnd(vs), Nat.add(1n+v, mbnd(vs)), vs, KA.natle_add_l(1n+v, mbnd(vs)), mbl_bnd(vs)))

def blw_mono(+n: Nat, +n2: Nat, p: List<&2, R.ZTerm>, +h: {KA.natle(n, n2) == True{} : Bool}, +hp: {blw(n, p) == True{} : Bool}) -> {blw(n2, p) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{c, +m}, +rest}:
      KA.band_i(mbl(n2, m), blw(n2, rest), mbl_mono(n, n2, m, h, KA.band_l(mbl(n, m), blw(n, rest), hp)), blw_mono(n, n2, rest, h, KA.band_r(mbl(n, m), blw(n, rest), hp)))

def blw_bnd(p: List<&2, R.ZTerm>) -> {blw(pbnd(p), p) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{c, +m}, +rest}:
      KA.band_i(mbl(Nat.add(mbnd(m), pbnd(rest)), m), blw(Nat.add(mbnd(m), pbnd(rest)), rest),
        mbl_mono(mbnd(m), Nat.add(mbnd(m), pbnd(rest)), m, KA.natle_add_r(mbnd(m), pbnd(rest)), mbl_bnd(m)),
        blw_mono(pbnd(rest), Nat.add(mbnd(m), pbnd(rest)), rest, KA.natle_add_l(mbnd(m), pbnd(rest)), blw_bnd(rest)))

def mln_mono(+d: Nat, +d2: Nat, p: List<&2, R.ZTerm>, +h: {KA.natle(d, d2) == True{} : Bool}, +hp: {mln(d, p) == True{} : Bool}) -> {mln(d2, p) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{c, +m}, +rest}:
      KA.band_i(KA.natle(mlen(m), d2), mln(d2, rest), KA.natle_trans(mlen(m), d, d2, KA.band_l(KA.natle(mlen(m), d), mln(d, rest), hp), h),
        mln_mono(d, d2, rest, h, KA.band_r(KA.natle(mlen(m), d), mln(d, rest), hp)))

def mln_sz(p: List<&2, R.ZTerm>) -> {mln(psz(p), p) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{c, +m}, +rest}:
      KA.band_i(KA.natle(mlen(m), Nat.add(mlen(m), psz(rest))), mln(Nat.add(mlen(m), psz(rest)), rest), KA.natle_add_r(mlen(m), psz(rest)),
        mln_mono(psz(rest), Nat.add(mlen(m), psz(rest)), rest, KA.natle_add_l(mlen(m), psz(rest)), mln_sz(rest)))

def mge0(m: List<&2, Nat>) -> {RP.mge(0n, m) == True{} : Bool}:
  match m:
    case Nil{}:
      {==}
    case Con{v, vs}:
      mge0(vs)

def abv0(p: List<&2, R.ZTerm>) -> {abv(0n, p) == True{} : Bool}:
  match p:
    case Nil{}:
      {==}
    case Con{R.ZTerm{c, +m}, +rest}:
      KA.band_i(RP.mge(0n, m), abv(0n, rest), mge0(m), abv0(rest))

def ne_isnil(p: List<&2, R.ZTerm>, hne: {Nil{} == p : List<&2, R.ZTerm>} -> Empty) -> {isnil(p) == False{} : Bool}:
  match p:
    case Nil{}:
      absurd({isnil(Nil{}) == False{} : Bool}, hne({==}))
    case Con{t, r}:
      {==}

# The non-root lemma
# ------------------

def witness(+p: List<&2, R.ZTerm>) -> List<&2, S.Z>:
  wit.go(pbnd(p), psz(p), 0n, pbnd(p), p)

# a reduced polynomial other than 0 is not 0 at its witness
def nonroot(+p: List<&2, R.ZTerm>, hr: {RP.red(p) == True{} : Bool}, hne: {Nil{} == p : List<&2, R.ZTerm>} -> Empty) -> {RP.nz(R.epoly(witness(p), p)) == True{} : Bool}:
  KA.band_l(RP.nz(R.epoly(witness(p), p)), nzb(witness(p), pbnd(p)),
    wit_ok(pbnd(p), psz(p), 0n, pbnd(p), p, hr, abv0(p), blw_bnd(p), mln_sz(p), KA.natle_refl(pbnd(p)), ne_isnil(p, hne)))
