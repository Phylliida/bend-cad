# bend-cad: an over-determined constraint in one honest classification is
# over-determined in any other (PLAN-sk13a S6, law 5 step 5). Proofs only.
#
# Say c is Over{j, s, w} in one classification (red list R1, dropped list
# D1, c's own drops dO) and kept or amber in another, with the same solved
# equations before c in both, so the same drops of c's own equations
# (lib/agreepf.bend: drops_ag).
# - Amber: every equation of c is dropped there, and so in dO; but j is
#   c's, in s, and s holds only equations of c not in dO (over_amber).
# - Kept: its matchable list is the solved equations before c and c's own
#   undropped ones. Read through the first classification (red list R1
#   less c, dropped list dO then D1) it is one ordered filter of the
#   sketch's equations (ml_eq). Every equation of s passes that filter
#   (pk_of, from clean), and depends only on variables in w (AllWithin,
#   put in the sketch's order: aw_ord). Walking the equations (wk), the
#   matching gives the equations of s distinct variables, each in w: as
#   many as s has (L.pig twice), and w has fewer (over_kept).
#
# Generated from tools/drafts/overpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as L
import ./kbpf.bend as KB
import ./ownpf.bend as OW
import ./solvedpf.bend as SP
import ./clslpf.bend as CL
import ./agreepf.bend as AG
import ./hreadpf.bend as HR

def absurd(-A: Type, x: Empty) -> A:
  match x:


# Small facts
# -----------

def mu_ne.c(b: Bool, +h: Nat, +t: List<&2, Nat>, +c: Nat, +o: Nat, e: {SV.eq(h, c) == b : Bool}, +hne: {SV.eq(o, c) == False{} : Bool}, +ih: {SV.mem(o, SV.unmark(c, t)) == SV.mem(o, t) : Bool})
  -> {SV.mem(o, SV.unmark.go(b, h, SV.unmark(c, t))) == SV.bor(SV.eq(o, h), SV.mem(o, t)) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Nat, h, c, L.eq_ok(h, c, e)) : {SV.mem(o, SV.unmark(c, t)) == SV.bor(SV.eq(o, _), SV.mem(o, t)) : Bool}
      %Equal.sym(Bool, SV.eq(o, c), False{}, hne) : {SV.mem(o, SV.unmark(c, t)) == SV.bor(_, SV.mem(o, t)) : Bool}
      ih
    case False{}:
      %Equal.sym(Bool, SV.mem(o, SV.unmark(c, t)), SV.mem(o, t), ih) : {SV.bor(SV.eq(o, h), _) == SV.bor(SV.eq(o, h), SV.mem(o, t)) : Bool}
      {==}

# o is not c: o is in xs less c exactly when in xs
def mu_ne(+c: Nat, xs: List<&2, Nat>, +o: Nat, +hne: {SV.eq(o, c) == False{} : Bool}) -> {SV.mem(o, SV.unmark(c, xs)) == SV.mem(o, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      mu_ne.c(SV.eq(h, c), h, t, c, o, {==}, hne, mu_ne(c, t, o, hne))

def mu_self.c(b: Bool, +h: Nat, +t: List<&2, Nat>, +c: Nat, e: {SV.eq(h, c) == b : Bool}, +ih: {SV.mem(c, SV.unmark(c, t)) == False{} : Bool}) -> {SV.mem(c, SV.unmark.go(b, h, SV.unmark(c, t))) == False{} : Bool}:
  match b:
    case True{}:
      ih
    case False{}:
      L.bor_f(SV.eq(c, h), SV.mem(c, SV.unmark(c, t)), Equal.trans(Bool, SV.eq(c, h), SV.eq(h, c), False{}, L.eq_sym(c, h), e), ih)

# c is not in xs less c
def mu_self(+c: Nat, xs: List<&2, Nat>) -> {SV.mem(c, SV.unmark(c, xs)) == False{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      mu_self.c(SV.eq(h, c), h, t, c, {==}, mu_self(c, t))

# not in a: in a then b exactly when in b
def mc_drop(+k: Nat, +a: List<&2, Nat>, +b: List<&2, Nat>, +hn: {SV.mem(k, a) == False{} : Bool}) -> {SV.mem(k, SV.cat(a, b)) == SV.mem(k, b) : Bool}:
  %Equal.sym(Bool, SV.mem(k, SV.cat(a, b)), SV.bor(SV.mem(k, a), SV.mem(k, b)), SP.mem_cat(k, a, b)) : {_ == SV.mem(k, b) : Bool}
  %Equal.sym(Bool, SV.mem(k, a), False{}, hn) : {SV.bor(_, SV.mem(k, b)) == SV.mem(k, b) : Bool}
  {==}

def band_fl(+a: Bool, +b: Bool, +h: {a == False{} : Bool}) -> {SV.band(a, b) == False{} : Bool}:
  %Equal.sym(Bool, a, False{}, h) : {SV.band(_, b) == False{} : Bool}
  {==}

def blw_mem.c(b: Bool, +x: Nat, +y: Nat, +t: List<&2, Nat>, +n: Nat, e: {SV.eq(x, y) == b : Bool}, hm: {SV.bor(b, SV.mem(x, t)) == True{} : Bool}, +hb: {SV.below(Con{y, t}, n) == True{} : Bool},
  ih: {SV.mem(x, t) == True{} : Bool} -> {SV.lt(x, n) == True{} : Bool}) -> {SV.lt(x, n) == True{} : Bool}:
  match b:
    case True{}:
      (%Equal.sym(Nat, x, y, L.eq_ok(x, y, e)) : {SV.lt(_, n) == True{} : Bool}
        L.band_l(SV.lt(y, n), SV.below(t, n), hb))
    case False{}:
      ih(hm)

# an entry of a list below n is below n
def blw_mem(+x: Nat, ys: List<&2, Nat>, +n: Nat, hm: {SV.mem(x, ys) == True{} : Bool}, +hb: {SV.below(ys, n) == True{} : Bool}) -> {SV.lt(x, n) == True{} : Bool}:
  match ys:
    case Nil{}:
      absurd({SV.lt(x, n) == True{} : Bool}, KA.ft(hm))
    case Con{+y, +t}:
      blw_mem.c(SV.eq(x, y), x, y, t, n, {==}, hm, hb, h2 => blw_mem(x, t, n, h2, L.band_r(SV.lt(y, n), SV.below(t, n), hb)))

# Reading lists at a position
# ---------------------------


def cl_at.c(b: Bool, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +d: List<&2, Nat>, +c: Nat, +x: Nat, +t: List<&2, Nat>, +k: Nat, e: {SV.eq(k, x) == b : Bool},
  hm: {SV.bor(b, SV.mem(k, t)) == True{} : Bool}, +h: {SV.clean(own, R, D, d, c, Con{x, t}) == True{} : Bool}, ih: {SV.mem(k, t) == True{} : Bool} -> {SV.bor(SV.band(SV.eq(SV.nth(own, k), c), SV.bnot(SV.mem(k, d))), SV.band(SV.lt(SV.nth(own, k), c), SV.band(SV.bnot(SV.mem(SV.nth(own, k), R)), SV.bnot(SV.mem(k, D))))) == True{} : Bool}) -> {SV.bor(SV.band(SV.eq(SV.nth(own, k), c), SV.bnot(SV.mem(k, d))), SV.band(SV.lt(SV.nth(own, k), c), SV.band(SV.bnot(SV.mem(SV.nth(own, k), R)), SV.bnot(SV.mem(k, D))))) == True{} : Bool}:
  match b:
    case True{}:
      (%Equal.sym(Nat, k, x, L.eq_ok(k, x, e)) : {SV.bor(SV.band(SV.eq(SV.nth(own, _), c), SV.bnot(SV.mem(_, d))), SV.band(SV.lt(SV.nth(own, _), c), SV.band(SV.bnot(SV.mem(SV.nth(own, _), R)), SV.bnot(SV.mem(_, D))))) == True{} : Bool}
        L.band_l(SV.bor(SV.band(SV.eq(SV.nth(own, x), c), SV.bnot(SV.mem(x, d))), SV.band(SV.lt(SV.nth(own, x), c), SV.band(SV.bnot(SV.mem(SV.nth(own, x), R)), SV.bnot(SV.mem(x, D))))), SV.clean(own, R, D, d, c, t), h))
    case False{}:
      ih(hm)

# clean at one of s's equations
def cl_at(+own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +d: List<&2, Nat>, +c: Nat, s: List<&2, Nat>, +k: Nat, +h: {SV.clean(own, R, D, d, c, s) == True{} : Bool}, hm: {SV.mem(k, s) == True{} : Bool}) -> {SV.bor(SV.band(SV.eq(SV.nth(own, k), c), SV.bnot(SV.mem(k, d))), SV.band(SV.lt(SV.nth(own, k), c), SV.band(SV.bnot(SV.mem(SV.nth(own, k), R)), SV.bnot(SV.mem(k, D))))) == True{} : Bool}:
  match s:
    case Nil{}:
      absurd({SV.bor(SV.band(SV.eq(SV.nth(own, k), c), SV.bnot(SV.mem(k, d))), SV.band(SV.lt(SV.nth(own, k), c), SV.band(SV.bnot(SV.mem(SV.nth(own, k), R)), SV.bnot(SV.mem(k, D))))) == True{} : Bool}, KA.ft(hm))
    case Con{+x, +t}:
      cl_at.c(SV.eq(k, x), own, R, D, d, c, x, t, k, {==}, hm, h, h2 => cl_at(own, R, D, d, c, t, k, L.band_r(SV.bor(SV.band(SV.eq(SV.nth(own, x), c), SV.bnot(SV.mem(x, d))), SV.band(SV.lt(SV.nth(own, x), c), SV.band(SV.bnot(SV.mem(SV.nth(own, x), R)), SV.bnot(SV.mem(x, D))))), SV.clean(own, R, D, d, c, t), h), h2))

# agree and alldrop at the x-th equation from k
def ag_at(own_s: List<&2, Nat>, +d1: List<&2, Nat>, +d2: List<&2, Nat>, +c: Nat, +k: Nat, x: Nat, h: {SP.agree(own_s, d1, d2, c, k) == True{} : Bool}, hx: {SV.lt(x, SV.len(own_s)) == True{} : Bool})
  -> {SV.bor(SV.bnot(SV.eq(SV.nth(own_s, x), c)), SP.beq(SV.mem(Nat.add(x, k), d1), SV.mem(Nat.add(x, k), d2))) == True{} : Bool}:
  match own_s x:
    case Nil{} x:
      absurd({SV.bor(SV.bnot(SV.eq(SV.nth(Nil{}, x), c)), SP.beq(SV.mem(Nat.add(x, k), d1), SV.mem(Nat.add(x, k), d2))) == True{} : Bool}, KA.ft(KB.lt_zero(x, hx)))
    case Con{+o, +t} 0n:
      L.band_l(SV.bor(SV.bnot(SV.eq(o, c)), SP.beq(SV.mem(k, d1), SV.mem(k, d2))), SP.agree(t, d1, d2, c, 1n+k), h)
    case Con{+o, +t} 1n++y:
      (%Equal.sym(Nat, 1n+Nat.add(y, k), Nat.add(y, 1n+k), LN.add_succ(y, k)) : {SV.bor(SV.bnot(SV.eq(SV.nth(t, y), c)), SP.beq(SV.mem(_, d1), SV.mem(_, d2))) == True{} : Bool}
        ag_at(t, d1, d2, c, 1n+k, y, L.band_r(SV.bor(SV.bnot(SV.eq(o, c)), SP.beq(SV.mem(k, d1), SV.mem(k, d2))), SP.agree(t, d1, d2, c, 1n+k), h), hx))

def ad_at(own_s: List<&2, Nat>, +d: List<&2, Nat>, +c: Nat, +k: Nat, x: Nat, h: {SV.alldrop.go(own_s, d, c, k) == True{} : Bool}, hx: {SV.lt(x, SV.len(own_s)) == True{} : Bool})
  -> {SV.bor(SV.bnot(SV.eq(SV.nth(own_s, x), c)), SV.mem(Nat.add(x, k), d)) == True{} : Bool}:
  match own_s x:
    case Nil{} x:
      absurd({SV.bor(SV.bnot(SV.eq(SV.nth(Nil{}, x), c)), SV.mem(Nat.add(x, k), d)) == True{} : Bool}, KA.ft(KB.lt_zero(x, hx)))
    case Con{+o, +t} 0n:
      L.band_l(SV.bor(SV.bnot(SV.eq(o, c)), SV.mem(k, d)), SV.alldrop.go(t, d, c, 1n+k), h)
    case Con{+o, +t} 1n++y:
      (%Equal.sym(Nat, 1n+Nat.add(y, k), Nat.add(y, 1n+k), LN.add_succ(y, k)) : {SV.bor(SV.bnot(SV.eq(SV.nth(t, y), c)), SV.mem(_, d)) == True{} : Bool}
        ad_at(t, d, c, 1n+k, y, L.band_r(SV.bor(SV.bnot(SV.eq(o, c)), SV.mem(k, d)), SV.alldrop.go(t, d, c, 1n+k), h), hx))

# Over against Amber
# ------------------


def oa_drop(+sk: SK.Sketch, +R1: List<&2, Nat>, +D1: List<&2, Nat>, +dO: List<&2, Nat>, +c: Nat, +j: Nat, +hj: {SV.eq(SV.nth(SV.owners(sk), j), c) == True{} : Bool},
  +hk: {SV.bor(SV.band(SV.eq(SV.nth(SV.owners(sk), j), c), SV.bnot(SV.mem(j, dO))), SV.band(SV.lt(SV.nth(SV.owners(sk), j), c), SV.band(SV.bnot(SV.mem(SV.nth(SV.owners(sk), j), R1)), SV.bnot(SV.mem(j, D1))))) == True{} : Bool}) -> {SV.mem(j, dO) == False{} : Bool}:
  L.bnot_f(SV.mem(j, dO), (%hj : {SV.band(_, SV.bnot(SV.mem(j, dO))) == True{} : Bool}
    HR.borl(SV.band(SV.eq(SV.nth(SV.owners(sk), j), c), SV.bnot(SV.mem(j, dO))), SV.band(SV.lt(SV.nth(SV.owners(sk), j), c), SV.band(SV.bnot(SV.mem(SV.nth(SV.owners(sk), j), R1)), SV.bnot(SV.mem(j, D1)))), hk,
      band_fl(SV.lt(SV.nth(SV.owners(sk), j), c), SV.band(SV.bnot(SV.mem(SV.nth(SV.owners(sk), j), R1)), SV.bnot(SV.mem(j, D1))), KB.eq_lt(SV.nth(SV.owners(sk), j), c, hj)))))

def oa_jo(+sk: SK.Sketch, +j: Nat, +h: {SV.lt(j, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}) -> {SV.lt(j, SV.len(SV.owners(sk))) == True{} : Bool}:
  %Equal.sym(Nat, SV.len(SV.owners(sk)), SV.neqs(SK.Sketch.eqs(sk)), OW.len_owners(sk)) : {SV.lt(j, _) == True{} : Bool}
  h

def oa_da(+sk: SK.Sketch, +dA: List<&2, Nat>, +c: Nat, +j: Nat, +hj: {SV.eq(SV.nth(SV.owners(sk), j), c) == True{} : Bool}, +ham: {SV.is_amberable(sk, c, dA) == True{} : Bool}, +hjo: {SV.lt(j, SV.len(SV.owners(sk))) == True{} : Bool}) -> {SV.mem(j, dA) == True{} : Bool}:
  (%hj : {SV.bor(SV.bnot(_), SV.mem(j, dA)) == True{} : Bool}
    (%Equal.sym(Nat, j, Nat.add(j, 0n), LN.add_zero(j)) : {SV.bor(SV.bnot(SV.eq(SV.nth(SV.owners(sk), j), c)), SV.mem(_, dA)) == True{} : Bool}
      ad_at(SV.owners(sk), dA, c, 0n, j, ham, hjo)))

def oa_eq(+sk: SK.Sketch, +dO: List<&2, Nat>, +dA: List<&2, Nat>, +c: Nat, +j: Nat, +hj: {SV.eq(SV.nth(SV.owners(sk), j), c) == True{} : Bool}, +hag: {SP.agree(SV.owners(sk), dO, dA, c, 0n) == True{} : Bool}, +hjo: {SV.lt(j, SV.len(SV.owners(sk))) == True{} : Bool}) -> {SV.mem(j, dO) == SV.mem(j, dA) : Bool}:
  AG.ag_hd(SV.nth(SV.owners(sk), j), c, j, dO, dA, (%Equal.sym(Nat, j, Nat.add(j, 0n), LN.add_zero(j)) : {SV.bor(SV.bnot(SV.eq(SV.nth(SV.owners(sk), j), c)), SP.beq(SV.mem(_, dO), SV.mem(_, dA))) == True{} : Bool}
    ag_at(SV.owners(sk), dO, dA, c, 0n, j, hag, hjo)), hj)

# j is c's, in s, and s is clean: j is not in dO; but every equation of c
# is in dA, and dO and dA agree at c's
def over_amber(+sk: SK.Sketch, +R1: List<&2, Nat>, +D1: List<&2, Nat>, +dO: List<&2, Nat>, +dA: List<&2, Nat>, +c: Nat, +j: Nat, +s: List<&2, Nat>,
  +hbO: {SV.band(SV.eq(SV.nth(SV.owners(sk), j), c), SV.band(SV.mem(j, s), SV.clean(SV.owners(sk), R1, D1, dO, c, s))) == True{} : Bool}, +hbs: {SV.below(s, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool},
  +hag: {SP.agree(SV.owners(sk), dO, dA, c, 0n) == True{} : Bool}, +ham: {SV.is_amberable(sk, c, dA) == True{} : Bool}) -> Empty:
  +hj = L.band_l(SV.eq(SV.nth(SV.owners(sk), j), c), SV.band(SV.mem(j, s), SV.clean(SV.owners(sk), R1, D1, dO, c, s)), hbO)
  +hr = L.band_r(SV.eq(SV.nth(SV.owners(sk), j), c), SV.band(SV.mem(j, s), SV.clean(SV.owners(sk), R1, D1, dO, c, s)), hbO)
  +hms = L.band_l(SV.mem(j, s), SV.clean(SV.owners(sk), R1, D1, dO, c, s), hr)
  +hjo = oa_jo(sk, j, blw_mem(j, s, SV.neqs(SK.Sketch.eqs(sk)), hms, hbs))
  +hnd = oa_drop(sk, R1, D1, dO, c, j, hj, cl_at(SV.owners(sk), R1, D1, dO, c, s, j, L.band_r(SV.mem(j, s), SV.clean(SV.owners(sk), R1, D1, dO, c, s), hr), hms))
  KA.ft(Equal.trans(Bool, False{}, SV.mem(j, dO), True{}, Equal.sym(Bool, SV.mem(j, dO), False{}, hnd), Equal.trans(Bool, SV.mem(j, dO), SV.mem(j, dA), True{}, oa_eq(sk, dO, dA, c, j, hj, hag, hjo), oa_da(sk, dA, c, j, hj, ham, hjo))))

# Over against Kept: the matchable list as one filter
# ---------------------------------------------------


def pq_hd(+own: List<&2, Nat>, +R1: List<&2, Nat>, +D1: List<&2, Nat>, +dO: List<&2, Nat>, +c: Nat, +k: Nat, +ha: {KB.allo(own, dO, c) == True{} : Bool}, +hl: {SV.lt(SV.nth(own, k), c) == True{} : Bool})
  -> {SV.band(SV.bnot(SV.mem(SV.nth(own, k), R1)), SV.bnot(SV.mem(k, D1))) == SV.band(SV.bnot(SV.mem(SV.nth(own, k), SV.unmark(c, R1))), SV.bnot(SV.mem(k, SV.cat(dO, D1)))) : Bool}:
  +hne = Equal.trans(Bool, SV.eq(SV.nth(own, k), c), SV.eq(c, SV.nth(own, k)), False{}, L.eq_sym(SV.nth(own, k), c), KB.ne_of_lt(SV.nth(own, k), c, hl))
  AG.band_cong(SV.bnot(SV.mem(SV.nth(own, k), R1)), SV.bnot(SV.mem(SV.nth(own, k), SV.unmark(c, R1))), SV.bnot(SV.mem(k, D1)), SV.bnot(SV.mem(k, SV.cat(dO, D1))),
    Equal.cong(Bool, Bool, z => SV.bnot(z), SV.mem(SV.nth(own, k), R1), SV.mem(SV.nth(own, k), SV.unmark(c, R1)), Equal.sym(Bool, SV.mem(SV.nth(own, k), SV.unmark(c, R1)), SV.mem(SV.nth(own, k), R1), mu_ne(c, R1, SV.nth(own, k), hne))),
    Equal.cong(Bool, Bool, z => SV.bnot(z), SV.mem(k, D1), SV.mem(k, SV.cat(dO, D1)), Equal.sym(Bool, SV.mem(k, SV.cat(dO, D1)), SV.mem(k, D1), mc_drop(k, dO, D1, CL.allo_nm(own, dO, c, k, ha, hne)))))

def pq(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R1: List<&2, Nat>, +D1: List<&2, Nat>, +dO: List<&2, Nat>, +c: Nat, +k: Nat, +ha: {KB.allo(own, dO, c) == True{} : Bool})
  -> {SV.presolved.go(es, own, R1, D1, c, k) == SV.presolved.go(es, own, SV.unmark(c, R1), SV.cat(dO, D1), c, k) : List<&2, E.QExpr>}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      AG.pick_cong(SV.band(SV.lt(SV.nth(own, k), c), SV.band(SV.bnot(SV.mem(SV.nth(own, k), R1)), SV.bnot(SV.mem(k, D1)))), SV.band(SV.lt(SV.nth(own, k), c), SV.band(SV.bnot(SV.mem(SV.nth(own, k), SV.unmark(c, R1))), SV.bnot(SV.mem(k, SV.cat(dO, D1))))), e,
        SV.presolved.go(t, own, R1, D1, c, 1n+k), SV.presolved.go(t, own, SV.unmark(c, R1), SV.cat(dO, D1), c, 1n+k),
        SP.band_ag(SV.lt(SV.nth(own, k), c), SV.band(SV.bnot(SV.mem(SV.nth(own, k), R1)), SV.bnot(SV.mem(k, D1))), SV.band(SV.bnot(SV.mem(SV.nth(own, k), SV.unmark(c, R1))), SV.bnot(SV.mem(k, SV.cat(dO, D1)))), hl => pq_hd(own, R1, D1, dO, c, k, ha, hl)),
        pq(t, own, R1, D1, dO, c, 1n+k, ha))

# the solved equations before c are the same with c taken out of the red
# list and dO (all c's own) put in front of the dropped one
def presolved_rd(+sk: SK.Sketch, +R1: List<&2, Nat>, +D1: List<&2, Nat>, +dO: List<&2, Nat>, +c: Nat, +ha: {KB.allo(SV.owners(sk), dO, c) == True{} : Bool})
  -> {SV.presolved(sk, R1, D1, c) == SV.presolved(sk, SV.unmark(c, R1), SV.cat(dO, D1), c) : List<&2, E.QExpr>}:
  pq(SK.Sketch.eqs(sk), SV.owners(sk), R1, D1, dO, c, 0n, ha)

def agc_hd(+k: Nat, +dO: List<&2, Nat>, +D1: List<&2, Nat>, +hz: {SP.beq(SV.mem(k, D1), False{}) == True{} : Bool}) -> {SP.beq(SV.mem(k, SV.cat(dO, D1)), SV.mem(k, dO)) == SP.beq(SV.mem(k, D1), False{}) : Bool}:
  %Equal.sym(Bool, SV.mem(k, SV.cat(dO, D1)), SV.bor(SV.mem(k, dO), SV.mem(k, D1)), SP.mem_cat(k, dO, D1)) : {SP.beq(_, SV.mem(k, dO)) == SP.beq(SV.mem(k, D1), False{}) : Bool}
  %Equal.sym(Bool, SV.mem(k, D1), False{}, SP.beq_eq(SV.mem(k, D1), False{}, hz)) : {SP.beq(SV.bor(SV.mem(k, dO), _), SV.mem(k, dO)) == SP.beq(_, False{}) : Bool}
  %Equal.sym(Bool, SV.bor(SV.mem(k, dO), False{}), SV.mem(k, dO), KB.bor_f(SV.mem(k, dO))) : {SP.beq(_, SV.mem(k, dO)) == True{} : Bool}
  AG.beq_refl(SV.mem(k, dO))

# D1 has none of c's equations: dO then D1 agrees with dO at them
def agc(own_s: List<&2, Nat>, +dO: List<&2, Nat>, +D1: List<&2, Nat>, +c: Nat, +k: Nat, +h: {SP.agree(own_s, D1, Nil{}, c, k) == True{} : Bool}) -> {SP.agree(own_s, SV.cat(dO, D1), dO, c, k) == True{} : Bool}:
  match own_s:
    case Nil{}:
      {==}
    case Con{+o, +t}:
      +hh = L.band_l(SV.bor(SV.bnot(SV.eq(o, c)), SP.beq(SV.mem(k, D1), SV.mem(k, Nil{}))), SP.agree(t, D1, Nil{}, c, 1n+k), h)
      L.band_i(SV.bor(SV.bnot(SV.eq(o, c)), SP.beq(SV.mem(k, SV.cat(dO, D1)), SV.mem(k, dO))), SP.agree(t, SV.cat(dO, D1), dO, c, 1n+k),
        Equal.trans(Bool, SV.bor(SV.bnot(SV.eq(o, c)), SP.beq(SV.mem(k, SV.cat(dO, D1)), SV.mem(k, dO))), SV.bor(SV.bnot(SV.eq(o, c)), SP.beq(SV.mem(k, D1), False{})), True{},
          AG.bnb_ag(SV.eq(o, c), SP.beq(SV.mem(k, SV.cat(dO, D1)), SV.mem(k, dO)), SP.beq(SV.mem(k, D1), False{}), hc => agc_hd(k, dO, D1, (%hc : {SV.bor(SV.bnot(_), SP.beq(SV.mem(k, D1), False{})) == True{} : Bool}
            hh))),
          hh),
        agc(t, dO, D1, c, 1n+k, L.band_r(SV.bor(SV.bnot(SV.eq(o, c)), SP.beq(SV.mem(k, D1), SV.mem(k, Nil{}))), SP.agree(t, D1, Nil{}, c, 1n+k), h)))

# Kept's matchable list, read through the Over side: one ordered filter
def ml_eq(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +R2: List<&2, Nat>, +D2: List<&2, Nat>, +c: Nat, +dO: List<&2, Nat>, +dK: List<&2, Nat>,
  +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hkd: {SV.kdrops(SV.class_at(cls1, c)) == Nil{} : List<&2, Nat>}, +ha: {KB.allo(SV.owners(sk), dO, c) == True{} : Bool},
  +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, R2, D2, c) : List<&2, E.QExpr>}, +hag: {SP.agree(SV.owners(sk), dO, dK, c, 0n) == True{} : Bool})
  -> {SK.cat(SV.presolved(sk, R2, D2, c), SV.own_rest(sk, c, dK, SV.neqs(SK.Sketch.eqs(sk)))) == SV.presolved(sk, SV.unmark(c, SV.reds(cls1)), SV.cat(dO, SV.dropped(cls1)), 1n+c) : List<&2, E.QExpr>}:
  %hps : {SK.cat(_, SV.own_rest(sk, c, dK, SV.neqs(SK.Sketch.eqs(sk)))) == SV.presolved(sk, SV.unmark(c, SV.reds(cls1)), SV.cat(dO, SV.dropped(cls1)), 1n+c) : List<&2, E.QExpr>}
  %AG.or_cong(sk, c, dO, dK, SV.neqs(SK.Sketch.eqs(sk)), hag) : {SK.cat(SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c), _) == SV.presolved(sk, SV.unmark(c, SV.reds(cls1)), SV.cat(dO, SV.dropped(cls1)), 1n+c) : List<&2, E.QExpr>}
  %Equal.sym(List<&2, E.QExpr>, SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c), SV.presolved(sk, SV.unmark(c, SV.reds(cls1)), SV.cat(dO, SV.dropped(cls1)), c), presolved_rd(sk, SV.reds(cls1), SV.dropped(cls1), dO, c, ha)) : {SK.cat(_, SV.own_rest(sk, c, dO, SV.neqs(SK.Sketch.eqs(sk)))) == SV.presolved(sk, SV.unmark(c, SV.reds(cls1)), SV.cat(dO, SV.dropped(cls1)), 1n+c) : List<&2, E.QExpr>}
  Equal.sym(List<&2, E.QExpr>, SV.presolved(sk, SV.unmark(c, SV.reds(cls1)), SV.cat(dO, SV.dropped(cls1)), 1n+c), SK.cat(SV.presolved(sk, SV.unmark(c, SV.reds(cls1)), SV.cat(dO, SV.dropped(cls1)), c), SV.own_rest(sk, c, dO, SV.neqs(SK.Sketch.eqs(sk)))),
    SP.presolved_kept(sk, SV.unmark(c, SV.reds(cls1)), SV.cat(dO, SV.dropped(cls1)), dO, c, mu_self(c, SV.reds(cls1)), agc(SV.owners(sk), dO, SV.dropped(cls1), c, 0n, (%hkd : {SP.agree(SV.owners(sk), SV.dropped(cls1), _, c, 0n) == True{} : Bool}
      AG.agree_dropped(sk, cls1, c, L.band_l(CL.downs(SV.owners(sk), cls1, 0n), SV.below(SV.dropped(cls1), SV.neqs(SK.Sketch.eqs(sk))), hf1))))))

# Every equation of s passes the filter
# -------------------------------------


# c's own equation k: not in D1, which has the Over class's drops (none)
def d1_c(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +c: Nat, +k: Nat, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hkd: {SV.kdrops(SV.class_at(cls1, c)) == Nil{} : List<&2, Nat>}, +hc: {SV.eq(SV.nth(SV.owners(sk), k), c) == True{} : Bool})
  -> {SV.mem(k, SV.dropped(cls1)) == False{} : Bool}:
  Equal.trans(Bool, SV.mem(k, SV.dropped(cls1)), SV.mem(k, SV.kdrops(SV.class_at(cls1, SV.nth(SV.owners(sk), k)))), False{}, HR.mem_dropped(sk, cls1, k, hf1),
    (%Equal.sym(Nat, SV.nth(SV.owners(sk), k), c, L.eq_ok(SV.nth(SV.owners(sk), k), c, hc)) : {SV.mem(k, SV.kdrops(SV.class_at(cls1, _))) == False{} : Bool}
      (%Equal.sym(List<&2, Nat>, SV.kdrops(SV.class_at(cls1, c)), Nil{}, hkd) : {SV.mem(k, _) == False{} : Bool}
        {==})))

def pk.c(b: Bool, +sk: SK.Sketch, +cls1: List<&2, SV.Class>, +c: Nat, +dO: List<&2, Nat>, +k: Nat, +e: {SV.eq(SV.nth(SV.owners(sk), k), c) == b : Bool},
  +hk: {SV.bor(SV.band(b, SV.bnot(SV.mem(k, dO))), SV.band(SV.lt(SV.nth(SV.owners(sk), k), c), SV.band(SV.bnot(SV.mem(SV.nth(SV.owners(sk), k), SV.reds(cls1))), SV.bnot(SV.mem(k, SV.dropped(cls1)))))) == True{} : Bool},
  +ha: {KB.allo(SV.owners(sk), dO, c) == True{} : Bool}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hkd: {SV.kdrops(SV.class_at(cls1, c)) == Nil{} : List<&2, Nat>}) -> {SV.band(SV.lt(SV.nth(SV.owners(sk), k), 1n+c), SV.band(SV.bnot(SV.mem(SV.nth(SV.owners(sk), k), SV.unmark(c, SV.reds(cls1)))), SV.bnot(SV.mem(k, SV.cat(dO, SV.dropped(cls1)))))) == True{} : Bool}:
  match b:
    case True{}:
      +hdo = L.bnot_f(SV.mem(k, dO), HR.borl(SV.bnot(SV.mem(k, dO)), SV.band(SV.lt(SV.nth(SV.owners(sk), k), c), SV.band(SV.bnot(SV.mem(SV.nth(SV.owners(sk), k), SV.reds(cls1))), SV.bnot(SV.mem(k, SV.dropped(cls1))))), hk,
        band_fl(SV.lt(SV.nth(SV.owners(sk), k), c), SV.band(SV.bnot(SV.mem(SV.nth(SV.owners(sk), k), SV.reds(cls1))), SV.bnot(SV.mem(k, SV.dropped(cls1)))), KB.eq_lt(SV.nth(SV.owners(sk), k), c, e))))
      +hd1 = d1_c(sk, cls1, c, k, hf1, hkd, e)
      %Equal.sym(Nat, SV.nth(SV.owners(sk), k), c, L.eq_ok(SV.nth(SV.owners(sk), k), c, e)) : {SV.band(SV.lt(_, 1n+c), SV.band(SV.bnot(SV.mem(_, SV.unmark(c, SV.reds(cls1)))), SV.bnot(SV.mem(k, SV.cat(dO, SV.dropped(cls1)))))) == True{} : Bool}
      %Equal.sym(Bool, SV.lt(c, 1n+c), True{}, KB.lt_succ(c)) : {SV.band(_, SV.band(SV.bnot(SV.mem(c, SV.unmark(c, SV.reds(cls1)))), SV.bnot(SV.mem(k, SV.cat(dO, SV.dropped(cls1)))))) == True{} : Bool}
      %Equal.sym(Bool, SV.mem(c, SV.unmark(c, SV.reds(cls1))), False{}, mu_self(c, SV.reds(cls1))) : {SV.band(True{}, SV.band(SV.bnot(_), SV.bnot(SV.mem(k, SV.cat(dO, SV.dropped(cls1)))))) == True{} : Bool}
      %Equal.sym(Bool, SV.mem(k, SV.cat(dO, SV.dropped(cls1))), False{}, Equal.trans(Bool, SV.mem(k, SV.cat(dO, SV.dropped(cls1))), SV.mem(k, SV.dropped(cls1)), False{}, mc_drop(k, dO, SV.dropped(cls1), hdo), hd1)) : {SV.band(True{}, SV.band(SV.bnot(False{}), SV.bnot(_))) == True{} : Bool}
      {==}
    case False{}:
      +hlt = L.band_l(SV.lt(SV.nth(SV.owners(sk), k), c), SV.band(SV.bnot(SV.mem(SV.nth(SV.owners(sk), k), SV.reds(cls1))), SV.bnot(SV.mem(k, SV.dropped(cls1)))), hk)
      +hr = L.band_r(SV.lt(SV.nth(SV.owners(sk), k), c), SV.band(SV.bnot(SV.mem(SV.nth(SV.owners(sk), k), SV.reds(cls1))), SV.bnot(SV.mem(k, SV.dropped(cls1)))), hk)
      L.band_i(SV.lt(SV.nth(SV.owners(sk), k), 1n+c), SV.band(SV.bnot(SV.mem(SV.nth(SV.owners(sk), k), SV.unmark(c, SV.reds(cls1)))), SV.bnot(SV.mem(k, SV.cat(dO, SV.dropped(cls1))))), KB.lt_up(SV.nth(SV.owners(sk), k), c, hlt),
        L.band_i(SV.bnot(SV.mem(SV.nth(SV.owners(sk), k), SV.unmark(c, SV.reds(cls1)))), SV.bnot(SV.mem(k, SV.cat(dO, SV.dropped(cls1)))),
          (%Equal.sym(Bool, SV.mem(SV.nth(SV.owners(sk), k), SV.unmark(c, SV.reds(cls1))), SV.mem(SV.nth(SV.owners(sk), k), SV.reds(cls1)), mu_ne(c, SV.reds(cls1), SV.nth(SV.owners(sk), k), e)) : {SV.bnot(_) == True{} : Bool}
            L.band_l(SV.bnot(SV.mem(SV.nth(SV.owners(sk), k), SV.reds(cls1))), SV.bnot(SV.mem(k, SV.dropped(cls1))), hr)),
          (%Equal.sym(Bool, SV.mem(k, SV.cat(dO, SV.dropped(cls1))), SV.mem(k, SV.dropped(cls1)), mc_drop(k, dO, SV.dropped(cls1), CL.allo_nm(SV.owners(sk), dO, c, k, ha, e))) : {SV.bnot(_) == True{} : Bool}
            L.band_r(SV.bnot(SV.mem(SV.nth(SV.owners(sk), k), SV.reds(cls1))), SV.bnot(SV.mem(k, SV.dropped(cls1))), hr))))

# an equation of s passes the filter
def pk_of(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +c: Nat, +dO: List<&2, Nat>, +s: List<&2, Nat>, +k: Nat, +hcl: {SV.clean(SV.owners(sk), SV.reds(cls1), SV.dropped(cls1), dO, c, s) == True{} : Bool},
  +ha: {KB.allo(SV.owners(sk), dO, c) == True{} : Bool}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hkd: {SV.kdrops(SV.class_at(cls1, c)) == Nil{} : List<&2, Nat>}, hm: {SV.mem(k, s) == True{} : Bool}) -> {SV.band(SV.lt(SV.nth(SV.owners(sk), k), 1n+c), SV.band(SV.bnot(SV.mem(SV.nth(SV.owners(sk), k), SV.unmark(c, SV.reds(cls1)))), SV.bnot(SV.mem(k, SV.cat(dO, SV.dropped(cls1)))))) == True{} : Bool}:
  pk.c(SV.eq(SV.nth(SV.owners(sk), k), c), sk, cls1, c, dO, k, {==}, cl_at(SV.owners(sk), SV.reds(cls1), SV.dropped(cls1), dO, c, s, k, hcl, hm), ha, hf1, hkd)

# at each equation from k: not in s, or it passes the filter R, D before c1
def PC(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c1: Nat, +k: Nat, +s: List<&2, Nat>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, t}:
      SV.band(SV.bor(SV.bnot(SV.mem(k, s)), SV.band(SV.lt(SV.nth(own, k), c1), SV.band(SV.bnot(SV.mem(SV.nth(own, k), R)), SV.bnot(SV.mem(k, D))))), PC(t, own, R, D, c1, 1n+k, s))

def pc_hd(b: Bool, +sk: SK.Sketch, +cls1: List<&2, SV.Class>, +c: Nat, +dO: List<&2, Nat>, +s: List<&2, Nat>, +k: Nat, e: {SV.mem(k, s) == b : Bool}, +hcl: {SV.clean(SV.owners(sk), SV.reds(cls1), SV.dropped(cls1), dO, c, s) == True{} : Bool},
  +ha: {KB.allo(SV.owners(sk), dO, c) == True{} : Bool}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hkd: {SV.kdrops(SV.class_at(cls1, c)) == Nil{} : List<&2, Nat>}) -> {SV.bor(SV.bnot(b), SV.band(SV.lt(SV.nth(SV.owners(sk), k), 1n+c), SV.band(SV.bnot(SV.mem(SV.nth(SV.owners(sk), k), SV.unmark(c, SV.reds(cls1)))), SV.bnot(SV.mem(k, SV.cat(dO, SV.dropped(cls1))))))) == True{} : Bool}:
  match b:
    case True{}:
      pk_of(sk, cls1, c, dO, s, k, hcl, ha, hf1, hkd, e)
    case False{}:
      {==}

def pc_of(es: List<&2, E.QExpr>, +sk: SK.Sketch, +cls1: List<&2, SV.Class>, +c: Nat, +dO: List<&2, Nat>, +s: List<&2, Nat>, +k: Nat, +hcl: {SV.clean(SV.owners(sk), SV.reds(cls1), SV.dropped(cls1), dO, c, s) == True{} : Bool},
  +ha: {KB.allo(SV.owners(sk), dO, c) == True{} : Bool}, +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hkd: {SV.kdrops(SV.class_at(cls1, c)) == Nil{} : List<&2, Nat>}) -> {PC(es, SV.owners(sk), SV.unmark(c, SV.reds(cls1)), SV.cat(dO, SV.dropped(cls1)), 1n+c, k, s) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{e, +t}:
      L.band_i(SV.bor(SV.bnot(SV.mem(k, s)), SV.band(SV.lt(SV.nth(SV.owners(sk), k), 1n+c), SV.band(SV.bnot(SV.mem(SV.nth(SV.owners(sk), k), SV.unmark(c, SV.reds(cls1)))), SV.bnot(SV.mem(k, SV.cat(dO, SV.dropped(cls1))))))), PC(t, SV.owners(sk), SV.unmark(c, SV.reds(cls1)), SV.cat(dO, SV.dropped(cls1)), 1n+c, 1n+k, s), pc_hd(SV.mem(k, s), sk, cls1, c, dO, s, k, {==}, hcl, ha, hf1, hkd), pc_of(t, sk, cls1, c, dO, s, 1n+k, hcl, ha, hf1, hkd))

# AllWithin in the sketch's order
# -------------------------------

def AWo.pick(b: Bool, +e: E.QExpr, +w: List<&2, Nat>) -> Type:
  match b:
    case True{}:
      SV.DependsWithin(e, w)
    case False{}:
      Unit

# at each equation from k that is in s: it depends only on variables in w
def AWo(es: List<&2, E.QExpr>, +k: Nat, +s: List<&2, Nat>, +w: List<&2, Nat>) -> Type:
  match es:
    case Nil{}:
      Unit
    case Con{+e, t}:
      AWo.pick(SV.mem(k, s), e, w) & AWo(t, 1n+k, s, w)

def aw_nil(es: List<&2, E.QExpr>, +k: Nat, +w: List<&2, Nat>) -> AWo(es, k, Nil{}, w):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      (Unit{}, aw_nil(t, 1n+k, w))

# past x, adding x to s changes nothing
def aw_skip(es: List<&2, E.QExpr>, +k: Nat, +x: Nat, +t: List<&2, Nat>, +w: List<&2, Nat>, +hlt: {SV.lt(x, k) == True{} : Bool}, h: AWo(es, k, t, w)) -> AWo(es, k, Con{x, t}, w):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +u}:
      (a, r) = h
      ((%Equal.sym(Bool, SV.eq(k, x), False{}, KB.ne_of_lt(x, k, hlt)) : AWo.pick(SV.bor(_, SV.mem(k, t)), e, w)
        a), aw_skip(u, 1n+k, x, t, w, KB.lt_up(x, k, hlt), r))

def eqx(+ES: List<&2, E.QExpr>, +k: Nat, +x: Nat, +e: E.QExpr, +u: List<&2, E.QExpr>, +eb: {SV.eq(k, x) == True{} : Bool}, +hq: {OW.qdrop(k, ES) == Con{e, u} : List<&2, E.QExpr>}) -> {SV.eqat(ES, x) == e : E.QExpr}:
  %L.eq_ok(k, x, eb) : {SV.eqat(ES, _) == e : E.QExpr}
  OW.eqat_of(ES, k, e, u, hq)

def aw_ins.c(b: Bool, +e: E.QExpr, +u: List<&2, E.QExpr>, +ES: List<&2, E.QExpr>, +k: Nat, +x: Nat, +t: List<&2, Nat>, +w: List<&2, Nat>, +eb: {SV.eq(k, x) == b : Bool},
  +hq: {OW.qdrop(k, ES) == Con{e, u} : List<&2, E.QExpr>}, a: AWo.pick(SV.mem(k, t), e, w), r: AWo(u, 1n+k, t, w), dw: SV.DependsWithin(SV.eqat(ES, x), w),
  ih: AWo(u, 1n+k, t, w) -> SV.DependsWithin(SV.eqat(ES, x), w) -> AWo(u, 1n+k, Con{x, t}, w)) -> (AWo.pick(SV.bor(b, SV.mem(k, t)), e, w) & AWo(u, 1n+k, Con{x, t}, w)):
  match b:
    case True{}:
      ((%eqx(ES, k, x, e, u, eb, hq) : SV.DependsWithin(_, w)
        dw), aw_skip(u, 1n+k, x, t, w, (%L.eq_ok(k, x, eb) : {SV.lt(_, 1n+k) == True{} : Bool}
          KB.lt_succ(k)), r))
    case False{}:
      (a, ih(r, dw))

def aw_ins(es: List<&2, E.QExpr>, +ES: List<&2, E.QExpr>, +k: Nat, +x: Nat, +t: List<&2, Nat>, +w: List<&2, Nat>, +hq: {OW.qdrop(k, ES) == es : List<&2, E.QExpr>},
  h: AWo(es, k, t, w), dw: SV.DependsWithin(SV.eqat(ES, x), w)) -> AWo(es, k, Con{x, t}, w):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +u}:
      (a, r) = h
      aw_ins.c(SV.eq(k, x), e, u, ES, k, x, t, w, {==}, hq, a, r, dw, r2 => d2 => aw_ins(u, ES, 1n+k, x, t, w, OW.qdrop_step(k, ES, e, u, hq), r2, d2))

# AllWithin, in the sketch's order
def aw_ord(+ES: List<&2, E.QExpr>, s: List<&2, Nat>, +w: List<&2, Nat>, h: SV.AllWithin(ES, s, w)) -> AWo(ES, 0n, s, w):
  match s:
    case Nil{}:
      aw_nil(ES, 0n, w)
    case Con{+x, +t}:
      (dw, ht) = h
      aw_ins(ES, ES, 0n, x, t, w, {==}, aw_ord(ES, t, w, ht), dw)

# The positions of s, in order
# ----------------------------

def K(es: List<&2, E.QExpr>, +k: Nat, +s: List<&2, Nat>) -> List<&2, Nat>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      SV.pos.pick(SV.mem(k, s), k, K(t, 1n+k, s))

def pp_mem(b: Bool, +k: Nat, +ks: List<&2, Nat>, +x: Nat, +h: {SV.mem(x, ks) == True{} : Bool}) -> {SV.mem(x, SV.pos.pick(b, k, ks)) == True{} : Bool}:
  match b:
    case True{}:
      L.bor_r(SV.eq(x, k), SV.mem(x, ks), h)
    case False{}:
      h

def mk.c(b: Bool, +t: List<&2, E.QExpr>, +k: Nat, +x: Nat, +s: List<&2, Nat>, +eb: {SV.eq(x, k) == b : Bool}, +hkx: {SV.lt(x, k) == False{} : Bool}, +hm: {SV.mem(x, s) == True{} : Bool},
  ih: {SV.lt(x, 1n+k) == False{} : Bool} -> {SV.mem(x, K(t, 1n+k, s)) == True{} : Bool}) -> {SV.mem(x, SV.pos.pick(SV.mem(k, s), k, K(t, 1n+k, s))) == True{} : Bool}:
  match b:
    case True{}:
      %L.eq_ok(x, k, eb) : {SV.mem(x, SV.pos.pick(SV.mem(_, s), _, K(t, 1n+k, s))) == True{} : Bool}
      %Equal.sym(Bool, SV.mem(x, s), True{}, hm) : {SV.mem(x, SV.pos.pick(_, x, K(t, 1n+k, s))) == True{} : Bool}
      L.bor_l(SV.eq(x, x), SV.mem(x, K(t, 1n+k, s)), L.eq_refl(x))
    case False{}:
      pp_mem(SV.mem(k, s), k, K(t, 1n+k, s), x, ih(SP.nlt_succ(x, k, hkx, eb)))

def mem_K(es: List<&2, E.QExpr>, +ES: List<&2, E.QExpr>, +k: Nat, +x: Nat, +s: List<&2, Nat>, +hq: {OW.qdrop(k, ES) == es : List<&2, E.QExpr>}, +hkx: {SV.lt(x, k) == False{} : Bool},
  +hx: {SV.lt(x, SV.neqs(ES)) == True{} : Bool}, +hm: {SV.mem(x, s) == True{} : Bool}) -> {SV.mem(x, K(es, k, s)) == True{} : Bool}:
  match es:
    case Nil{}:
      absurd({SV.mem(x, Nil{}) == True{} : Bool}, KA.ft(Equal.trans(Bool, False{}, SV.lt(x, SV.neqs(ES)), True{}, Equal.sym(Bool, SV.lt(x, SV.neqs(ES)), False{}, KB.nlt_le(k, x, SV.neqs(ES), SP.nlt_qdrop(ES, k, hq), hkx)), hx)))
    case Con{+e, +t}:
      mk.c(SV.eq(x, k), t, k, x, s, {==}, hkx, hm, h2 => mem_K(t, ES, 1n+k, x, s, OW.qdrop_step(k, ES, e, t, hq), h2, hx, hm))

# every entry of s2 (inside s, below the number of equations) is among s's
# positions
def sub_K(s2: List<&2, Nat>, +ES: List<&2, E.QExpr>, +s: List<&2, Nat>, +hb: {SV.below(s2, SV.neqs(ES)) == True{} : Bool}, +hs: {L.subl(s2, s) == True{} : Bool}) -> {L.subl(s2, K(ES, 0n, s)) == True{} : Bool}:
  match s2:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.band_i(SV.mem(x, K(ES, 0n, s)), L.subl(t, K(ES, 0n, s)), mem_K(ES, ES, 0n, x, s, {==}, KB.lt_z(x), L.band_l(SV.lt(x, SV.neqs(ES)), SV.below(t, SV.neqs(ES)), hb), L.subl_hd(x, t, s, hs)),
        sub_K(t, ES, s, L.band_r(SV.lt(x, SV.neqs(ES)), SV.below(t, SV.neqs(ES)), hb), L.subl_tl(x, t, s, hs)))

# The walk
# --------

# the matched variables of s's equations: inside m, distinct, in w, one
# for each position of s
def WR(+m: List<&2, Nat>, +w: List<&2, Nat>, +ks: List<&2, Nat>) -> Type:
  &xs: List<&2, Nat> -> ({L.subl(xs, m) == True{} : Bool} & ({SV.distinct(xs) == True{} : Bool} & ({L.subl(xs, w) == True{} : Bool} & {SV.len(xs) == SV.len(ks) : Nat})))

def in_w.c(b: Bool, +e: E.QExpr, +v: Nat, +w: List<&2, Nat>, eb: {SV.mem(v, w) == b : Bool}, dep: SV.Depends(e, v), dw: SV.DependsWithin(e, w)) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      absurd({False{} == True{} : Bool}, dep(dw(v, eb)))

# e depends on v, and only on variables in w: v is in w
def in_w(+e: E.QExpr, +v: Nat, +w: List<&2, Nat>, dep: SV.Depends(e, v), dw: SV.DependsWithin(e, w)) -> {SV.mem(v, w) == True{} : Bool}:
  in_w.c(SV.mem(v, w), e, v, w, {==}, dep, dw)

def wk.add(+v: Nat, +m2: List<&2, Nat>, +k: Nat, +ks: List<&2, Nat>, +w: List<&2, Nat>, +hdm: {SV.distinct(Con{v, m2}) == True{} : Bool}, +hv: {SV.mem(v, w) == True{} : Bool}, r: WR(m2, w, ks)) -> WR(Con{v, m2}, w, Con{k, ks}):
  (+xs, f) = r
  (+h1, f2) = f
  (+h2, f3) = f2
  (+h3, h4) = f3
  (Con{v, xs}, (L.band_i(SV.mem(v, Con{v, m2}), L.subl(xs, Con{v, m2}), L.mem_hd(v, m2), L.subl_cons_r(xs, v, m2, h1)),
    (L.dist_con(v, xs, L.notin_subl(v, xs, m2, L.dist_hd(v, m2, hdm), h1), h2),
    (L.band_i(SV.mem(v, w), L.subl(xs, w), hv, h3), Equal.cong(Nat, Nat, n => 1n+n, SV.len(xs), SV.len(ks), h4)))))

def wk.skip(+v: Nat, +m2: List<&2, Nat>, +ks: List<&2, Nat>, +w: List<&2, Nat>, r: WR(m2, w, ks)) -> WR(Con{v, m2}, w, ks):
  (+xs, f) = r
  (+h1, f2) = f
  (xs, (L.subl_cons_r(xs, v, m2, h1), f2))


def wk.c(b: Bool, bs: Bool, +e: E.QExpr, +t: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c1: Nat, +k: Nat, +s: List<&2, Nat>, +w: List<&2, Nat>,
  m: List<&2, Nat>, +hdm: {SV.distinct(m) == True{} : Bool}, dep: SV.DepAll(SV.solved.pick(b, e, SV.presolved.go(t, own, R, D, c1, 1n+k)), m), a: AWo.pick(bs, e, w), +hpc: {SV.bor(SV.bnot(bs), b) == True{} : Bool},
  ih: @m2: List<&2, Nat> -> {SV.distinct(m2) == True{} : Bool} -> SV.DepAll(SV.presolved.go(t, own, R, D, c1, 1n+k), m2) -> WR(m2, w, K(t, 1n+k, s))) -> WR(m, w, SV.pos.pick(bs, k, K(t, 1n+k, s))):
  match b bs:
    case True{} True{}:
      match m:
        case Nil{}:
          absurd(WR(Nil{}, w, Con{k, K(t, 1n+k, s)}), dep)
        case Con{+v, +m2}:
          (d1, d2) = dep
          wk.add(v, m2, k, K(t, 1n+k, s), w, hdm, in_w(e, v, w, d1, a), ih(m2, L.dist_tl(v, m2, hdm), d2))
    case True{} False{}:
      match m:
        case Nil{}:
          absurd(WR(Nil{}, w, K(t, 1n+k, s)), dep)
        case Con{+v, +m2}:
          (d1, d2) = dep
          wk.skip(v, m2, K(t, 1n+k, s), w, ih(m2, L.dist_tl(v, m2, hdm), d2))
    case False{} True{}:
      absurd(WR(m, w, Con{k, K(t, 1n+k, s)}), KA.ft(hpc))
    case False{} False{}:
      ih(m, hdm, dep)

# walk the equations from k with the filter R, D before c1, the matching m
# of what it keeps, and s's AllWithin
def wk(es: List<&2, E.QExpr>, +own: List<&2, Nat>, +R: List<&2, Nat>, +D: List<&2, Nat>, +c1: Nat, +k: Nat, +s: List<&2, Nat>, +w: List<&2, Nat>,
  m: List<&2, Nat>, +hdm: {SV.distinct(m) == True{} : Bool}, dep: SV.DepAll(SV.presolved.go(es, own, R, D, c1, k), m), aw: AWo(es, k, s, w), +hpc: {PC(es, own, R, D, c1, k, s) == True{} : Bool}) -> WR(m, w, K(es, k, s)):
  match es:
    case Nil{}:
      (Nil{}, ({==}, ({==}, ({==}, {==}))))
    case Con{+e, +t}:
      (a, awt) = aw
      wk.c(SV.band(SV.lt(SV.nth(own, k), c1), SV.band(SV.bnot(SV.mem(SV.nth(own, k), R)), SV.bnot(SV.mem(k, D)))), SV.mem(k, s), e, t, own, R, D, c1, k, s, w, m, hdm, dep, a, L.band_l(SV.bor(SV.bnot(SV.mem(k, s)), SV.band(SV.lt(SV.nth(own, k), c1), SV.band(SV.bnot(SV.mem(SV.nth(own, k), R)), SV.bnot(SV.mem(k, D))))), PC(t, own, R, D, c1, 1n+k, s), hpc),
        m2 => h2 => d2 => wk(t, own, R, D, c1, 1n+k, s, w, m2, h2, d2, awt, L.band_r(SV.bor(SV.bnot(SV.mem(k, s)), SV.band(SV.lt(SV.nth(own, k), c1), SV.band(SV.bnot(SV.mem(SV.nth(own, k), R)), SV.bnot(SV.mem(k, D))))), PC(t, own, R, D, c1, 1n+k, s), hpc)))

# Over against Kept
# -----------------

def ok_fin(+sk: SK.Sketch, +s: List<&2, Nat>, +w: List<&2, Nat>, +m: List<&2, Nat>, +hds: {SV.distinct(s) == True{} : Bool}, +hbs: {SV.below(s, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +hlw: {SV.lt(SV.len(w), SV.len(s)) == True{} : Bool},
  r: WR(m, w, K(SK.Sketch.eqs(sk), 0n, s))) -> Empty:
  (+xs, f) = r
  (+h1, f2) = f
  (+h2, f3) = f2
  (+h3, h4) = f3
  +hxw = L.pig(xs, w, h2, h3)
  +hsk = L.pig(s, K(SK.Sketch.eqs(sk), 0n, s), hds, sub_K(s, SK.Sketch.eqs(sk), s, hbs, L.subl_refl(s)))
  +hsw = KA.natle_trans(SV.len(s), SV.len(xs), SV.len(w), KA.natle_rw(SV.len(s), SV.len(K(SK.Sketch.eqs(sk), 0n, s)), SV.len(xs), Equal.sym(Nat, SV.len(xs), SV.len(K(SK.Sketch.eqs(sk), 0n, s)), h4), hsk), hxw)
  KA.natlt_irr(SV.len(w), KA.natle_trans(1n+SV.len(w), SV.len(s), SV.len(w), (%L.lt_sv(SV.len(w), SV.len(s)) : {_ == True{} : Bool}
    hlw), hsw))

def ok_m(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +c: Nat, +dO: List<&2, Nat>, +s: List<&2, Nat>, +w: List<&2, Nat>, mt: SV.Matchable(SV.presolved(sk, SV.unmark(c, SV.reds(cls1)), SV.cat(dO, SV.dropped(cls1)), 1n+c)), aw: AWo(SK.Sketch.eqs(sk), 0n, s, w),
  +hpc: {PC(SK.Sketch.eqs(sk), SV.owners(sk), SV.unmark(c, SV.reds(cls1)), SV.cat(dO, SV.dropped(cls1)), 1n+c, 0n, s) == True{} : Bool}, +hds: {SV.distinct(s) == True{} : Bool}, +hbs: {SV.below(s, SV.neqs(SK.Sketch.eqs(sk))) == True{} : Bool}, +hlw: {SV.lt(SV.len(w), SV.len(s)) == True{} : Bool}) -> Empty:
  (+m, r) = mt
  (+hdm, dep) = r
  ok_fin(sk, s, w, m, hds, hbs, hlw, wk(SK.Sketch.eqs(sk), SV.owners(sk), SV.unmark(c, SV.reds(cls1)), SV.cat(dO, SV.dropped(cls1)), 1n+c, 0n, s, w, m, hdm, dep, aw, hpc))

# c over in one classification (its own drops dO), kept in another (its
# drops dK, its matchable list), the same solved equations before c and
# so the same drops: s's equations get distinct variables, all in w
def over_kept(+sk: SK.Sketch, +cls1: List<&2, SV.Class>, +R2: List<&2, Nat>, +D2: List<&2, Nat>, +c: Nat, +j: Nat, +s: List<&2, Nat>, +w: List<&2, Nat>, +dO: List<&2, Nat>, +dK: List<&2, Nat>,
  +hbO: {SV.band(SV.eq(SV.nth(SV.owners(sk), j), c), SV.band(SV.mem(j, s), SV.clean(SV.owners(sk), SV.reds(cls1), SV.dropped(cls1), dO, c, s))) == True{} : Bool}, ovd: SV.Overdet(SK.Sketch.eqs(sk), s, w),
  +hf1: {HR.hfacts(sk, cls1) == True{} : Bool}, +hkd: {SV.kdrops(SV.class_at(cls1, c)) == Nil{} : List<&2, Nat>}, +ha: {KB.allo(SV.owners(sk), dO, c) == True{} : Bool},
  +hps: {SV.presolved(sk, SV.reds(cls1), SV.dropped(cls1), c) == SV.presolved(sk, R2, D2, c) : List<&2, E.QExpr>}, +hag: {SP.agree(SV.owners(sk), dO, dK, c, 0n) == True{} : Bool},
  mt: SV.Matchable(SK.cat(SV.presolved(sk, R2, D2, c), SV.own_rest(sk, c, dK, SV.neqs(SK.Sketch.eqs(sk)))))) -> Empty:
  (+hov, haw) = ovd
  +hds = L.band_l(SV.distinct(s), SV.band(SV.below(s, SV.neqs(SK.Sketch.eqs(sk))), SV.lt(SV.len(w), SV.len(s))), hov)
  +hr = L.band_r(SV.distinct(s), SV.band(SV.below(s, SV.neqs(SK.Sketch.eqs(sk))), SV.lt(SV.len(w), SV.len(s))), hov)
  +hcl = L.band_r(SV.mem(j, s), SV.clean(SV.owners(sk), SV.reds(cls1), SV.dropped(cls1), dO, c, s), L.band_r(SV.eq(SV.nth(SV.owners(sk), j), c), SV.band(SV.mem(j, s), SV.clean(SV.owners(sk), SV.reds(cls1), SV.dropped(cls1), dO, c, s)), hbO))
  ok_m(sk, cls1, c, dO, s, w, (%ml_eq(sk, cls1, R2, D2, c, dO, dK, hf1, hkd, ha, hps, hag) : SV.Matchable(_)
    mt), aw_ord(SK.Sketch.eqs(sk), s, w, haw), pc_of(SK.Sketch.eqs(sk), sk, cls1, c, dO, s, 0n, hcl, ha, hf1, hkd), hds,
    L.band_l(SV.below(s, SV.neqs(SK.Sketch.eqs(sk))), SV.lt(SV.len(w), SV.len(s)), hr), L.band_r(SV.below(s, SV.neqs(SK.Sketch.eqs(sk))), SV.lt(SV.len(w), SV.len(s)), hr))
