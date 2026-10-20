# bend-cad: a constraint's equations matched as a unit, by dependence, for
# the single pass (PLAN-sk13a S4). Proofs only.
#
# The adjacency is what each equation depends on (lib/pass.bend: dadjs, by
# lib/deppf.bend's dadj). Searching from each of c's equations us in turn
# (lib/pass.bend: grpl), from a matching whose matched equations are Z:
# - if every search finds a path, the matching is valid and its matched
#   equations are Z followed by us;
# - if the one from j fails, its visited variables W and the equations S =
#   j and the mates of W are over-determined (the spec's Overdet, by
#   dependence: each equation of S depends only on W, and |W| < |S|), and
#   S is within Z and us.
# A valid matching gives the equations at positions P, all matched, a
# matching of its own (the spec's Matchable): each its variable.
#
# Generated from tools/drafts/gmpf.draft by tools/expand.py; edit the
# draft.

import Base
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/deriv.bend as DV
import ./karith.bend as KA
import ./nat.bend as LN
import ./listpf.bend as L
import ./struct.bend as ST
import ./dfspf.bend as D
import ./maxpf.bend as MX
import ./identpf.bend as ID
import ./deppf.bend as DP
import ./redpf.bend as RP
import ./conflict.bend as CO
import ./cwpf.bend as CW
import ./pass.bend as PA
import ./kbpf.bend as KB
import ./solvedpf.bend as SP

def absurd(-A: Type, x: Empty) -> A:
  match x:


# The adjacency by dependence
# ---------------------------

def nthl_dadjs(es: List<&2, E.QExpr>, k: Nat) -> {ST.nthl(PA.dadjs(es), k) == DP.dadj(SV.eqat(es, k)) : List<&2, Nat>}:
  match es k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{e, t} 0n:
      {==}
    case Con{e, t} 1n+j:
      nthl_dadjs(t, j)

def dfilt_sub.d(b: Bool, +v: Nat, +r: List<&2, Nat>, +t: List<&2, Nat>, +h: {L.subl(r, t) == True{} : Bool}) -> {L.subl(DP.dfilt.dec(b, v, r), Con{v, t}) == True{} : Bool}:
  match b:
    case True{}:
      L.subl_con(v, r, Con{v, t}, L.mem_hd(v, t), L.subl_cons_r(r, v, t, h))
    case False{}:
      L.subl_cons_r(r, v, t, h)

def dfilt_sub(+e: E.QExpr, vs: List<&2, Nat>) -> {L.subl(DP.dfilt(e, vs), vs) == True{} : Bool}:
  match vs:
    case Nil{}:
      {==}
    case Con{+v, +t}:
      dfilt_sub.d(ID.dep(e, v), v, DP.dfilt(e, t), t, dfilt_sub(e, t))

def nthl_adj(es: List<&2, E.QExpr>, k: Nat) -> {ST.nthl(ST.adj(es), k) == DP.cand(SV.eqat(es, k)) : List<&2, Nat>}:
  match es k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+j:
      {==}
    case Con{e, t} 0n:
      {==}
    case Con{e, t} 1n+j:
      nthl_adj(t, j)

# every variable an equation depends on is a variable of the sketch
def adjb_dadjs(es: List<&2, E.QExpr>, +n: Nat, +h: {D.adjb(ST.adj(es), n) == True{} : Bool}) -> {D.adjb(PA.dadjs(es), n) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, +t}:
      L.band_i(SV.below(DP.dadj(e), n), D.adjb(PA.dadjs(t), n),
        D.below_subl(DP.dadj(e), DP.cand(e), n, dfilt_sub(e, DP.cand(e)), L.band_l(SV.below(DP.cand(e), n), D.adjb(ST.adj(t), n), h)),
        adjb_dadjs(t, n, L.band_r(SV.below(DP.cand(e), n), D.adjb(ST.adj(t), n), h)))

# The witness, by dependence
# --------------------------

def within_at(+es: List<&2, E.QExpr>, +k: Nat, +w: List<&2, Nat>, h: {L.subl(ST.nthl(PA.dadjs(es), k), w) == True{} : Bool}) -> SV.DependsWithin(SV.eqat(es, k), w):
  DP.dadj_within(SV.eqat(es, k), w, (%nthl_dadjs(es, k) : {L.subl(_, w) == True{} : Bool}
    h))

# the mates of xs (closed over the base Nil) depend only on w
def look_within(+es: List<&2, E.QExpr>, +vm: List<&2, Maybe<&2, Nat>>, xs: List<&2, Nat>, +w: List<&2, Nat>, +h: {D.closed(vm, PA.dadjs(es), Nil{}, w, xs) == True{} : Bool}) -> SV.AllWithin(es, ST.look(vm, xs), w):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+v, +t}:
      (within_at(es, D.mate(vm, v), w, L.band_l(L.subl(ST.nthl(PA.dadjs(es), D.mate(vm, v)), w), D.closed(vm, PA.dadjs(es), Nil{}, w, t), h)),
        look_within(es, vm, t, w, L.band_r(L.subl(ST.nthl(PA.dadjs(es), D.mate(vm, v)), w), D.closed(vm, PA.dadjs(es), Nil{}, w, t), h)))

# a failed search from j: its witness is over-determined, by dependence
def wit_dep(+es: List<&2, E.QExpr>, +vm: List<&2, Maybe<&2, Nat>>, +j: Nat, +f: Nat, +vis: List<&2, Nat>, +h1: {SV.mem(j, ST.somes(vm)) == False{} : Bool}, +h2: {SV.distinct(ST.somes(vm)) == True{} : Bool}, +hb: {SV.below(ST.somes(vm), SV.neqs(es)) == True{} : Bool},
  +hj: {SV.lt(j, SV.neqs(es)) == True{} : Bool}, +hv: {D.vis_ok(vm, PA.dadjs(es), Nil{}, f, vis) == True{} : Bool}, +hn: {L.subl(ST.nthl(PA.dadjs(es), j), vis) == True{} : Bool})
  -> SV.Overdet(es, Con{j, ST.look(vm, vis)}, vis):
  +adj = PA.dadjs(es)
  +lk = ST.look(vm, vis)
  +ha = D.vo_a(vm, adj, Nil{}, f, vis, hv)
  (L.band_i(SV.distinct(Con{j, lk}), SV.band(SV.below(Con{j, lk}, SV.neqs(es)), SV.lt(SV.len(vis), SV.len(Con{j, lk}))),
    L.dist_con(j, lk, L.notin_subl(j, lk, ST.somes(vm), h1, L.look_subl(vm, vis, ha)), L.look_dist(vm, vis, D.vo_d(vm, adj, Nil{}, f, vis, hv), ha, h2)),
    L.band_i(SV.below(Con{j, lk}, SV.neqs(es)), SV.lt(SV.len(vis), SV.len(Con{j, lk})),
      L.band_i(SV.lt(j, SV.neqs(es)), SV.below(lk, SV.neqs(es)), hj, D.below_subl(lk, ST.somes(vm), SV.neqs(es), L.look_subl(vm, vis, ha), hb)),
      (%Equal.sym(Nat, SV.len(ST.look(vm, vis)), SV.len(vis), L.look_len(vm, vis)) : {SV.lt(SV.len(vis), 1n+_) == True{} : Bool}
        KB.lt_succ(SV.len(vis))))),
   (within_at(es, j, vis, hn), look_within(es, vm, vis, vis, D.vo_c(vm, adj, Nil{}, f, vis, hv))))

# Lists
# -----

def pigc.one(+y: Nat, +xs: List<&2, Nat>, +ys: List<&2, Nat>, b: Bool, e: {SV.mem(y, xs) == b : Bool}, hy: {SV.mem(y, ys) == True{} : Bool}, dx: {SV.distinct(xs) == True{} : Bool}, hs: {L.subl(xs, ys) == True{} : Bool}, hl: {KA.natle(SV.len(ys), SV.len(xs)) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      absurd({False{} == True{} : Bool}, KA.natlt_irr(SV.len(xs), KA.natle_trans(1n+SV.len(xs), 1n+SV.len(L.rem(y, ys)), SV.len(xs), L.pig(xs, L.rem(y, ys), dx, L.subl_rem(xs, y, ys, hs, e)), KA.natle_trans(1n+SV.len(L.rem(y, ys)), SV.len(ys), SV.len(xs), L.rem_len(y, ys, hy), hl))))

def pigc.go(zs: List<&2, Nat>, +xs: List<&2, Nat>, +ys: List<&2, Nat>, +hz: {L.subl(zs, ys) == True{} : Bool}, +dx: {SV.distinct(xs) == True{} : Bool}, +hs: {L.subl(xs, ys) == True{} : Bool}, +hl: {KA.natle(SV.len(ys), SV.len(xs)) == True{} : Bool}) -> {L.subl(zs, xs) == True{} : Bool}:
  match zs:
    case Nil{}:
      {==}
    case Con{+z, +t}:
      L.subl_con(z, t, xs, pigc.one(z, xs, ys, SV.mem(z, xs), {==}, L.subl_hd(z, t, ys, hz), dx, hs, hl), pigc.go(t, xs, ys, L.subl_tl(z, t, ys, hz), dx, hs, hl))

# xs within ys, distinct and no shorter: ys within xs
def pigc(+xs: List<&2, Nat>, +ys: List<&2, Nat>, dx: {SV.distinct(xs) == True{} : Bool}, hs: {L.subl(xs, ys) == True{} : Bool}, hl: {KA.natle(SV.len(ys), SV.len(xs)) == True{} : Bool}) -> {L.subl(ys, xs) == True{} : Bool}:
  pigc.go(ys, xs, ys, L.subl_refl(ys), dx, hs, hl)

def subl_snoc(xs: List<&2, Nat>, +u: Nat) -> {L.subl(CO.lsnoc(xs, u), Con{u, xs}) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.subl_con(u, Nil{}, Con{u, Nil{}}, L.mem_hd(u, Nil{}), {==})
    case Con{+x, +t}:
      L.subl_con(x, CO.lsnoc(t, u), Con{u, Con{x, t}}, L.mem_tl(x, u, Con{x, t}, L.mem_hd(x, t)), L.subl_ins(CO.lsnoc(t, u), u, x, t, subl_snoc(t, u)))

def subl_ext(xs: List<&2, Nat>, +u: Nat) -> {L.subl(xs, CO.lsnoc(xs, u)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.subl_con(x, t, Con{x, CO.lsnoc(t, u)}, L.mem_hd(x, CO.lsnoc(t, u)), L.subl_cons_r(t, x, CO.lsnoc(t, u), subl_ext(t, u)))

# u after Z, distinctly: u is not in Z

def snoc_subl(+xs: List<&2, Nat>, +u: Nat) -> {L.subl(Con{u, xs}, CO.lsnoc(xs, u)) == True{} : Bool}:
  L.subl_con(u, xs, CO.lsnoc(xs, u), Equal.trans(Bool, SV.mem(u, CO.lsnoc(xs, u)), SV.bor(SV.mem(u, xs), SV.eq(u, u)), True{}, KB.mem_snoc(u, xs, u), L.bor_r(SV.mem(u, xs), SV.eq(u, u), L.eq_refl(u))), subl_ext(xs, u))

def ne_left(a: Bool, +b: Bool, h: {a == False{} : Bool}) -> {SV.bor(a, b) == b : Bool}:
  match a:
    case True{}:
      absurd({SV.bor(True{}, b) == b : Bool}, KA.tf(h))
    case False{}:
      {==}

def subl_catl(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {L.subl(xs, SV.cat(xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      L.subl_con(x, t, Con{x, SV.cat(t, ys)}, L.mem_hd(x, SV.cat(t, ys)), L.subl_cons_r(t, x, SV.cat(t, ys), subl_catl(t, ys)))

def notin_cat(Z: List<&2, Nat>, +u: Nat, +t: List<&2, Nat>, +h: {SV.distinct(SV.cat(Z, Con{u, t})) == True{} : Bool}) -> {SV.mem(u, Z) == False{} : Bool}:
  match Z:
    case Nil{}:
      {==}
    case Con{+z, +zt}:
      +hn = KB.bnot_t(SV.mem(z, SV.cat(zt, Con{u, t})), L.band_l(SV.bnot(SV.mem(z, SV.cat(zt, Con{u, t}))), SV.distinct(SV.cat(zt, Con{u, t})), h))
      +hu = Equal.trans(Bool, SV.mem(z, Con{u, t}), SV.bor(SV.mem(z, zt), SV.mem(z, Con{u, t})), False{}, Equal.sym(Bool, SV.bor(SV.mem(z, zt), SV.mem(z, Con{u, t})), SV.mem(z, Con{u, t}), ne_left(SV.mem(z, zt), SV.mem(z, Con{u, t}), L.notin_subl(z, zt, SV.cat(zt, Con{u, t}), hn, subl_catl(zt, Con{u, t})))), Equal.trans(Bool, SV.bor(SV.mem(z, zt), SV.mem(z, Con{u, t})), SV.mem(z, SV.cat(zt, Con{u, t})), False{}, Equal.sym(Bool, SV.mem(z, SV.cat(zt, Con{u, t})), SV.bor(SV.mem(z, zt), SV.mem(z, Con{u, t})), SP.mem_cat(z, zt, Con{u, t})), hn))
      L.bor_f(SV.eq(u, z), SV.mem(u, zt), Equal.trans(Bool, SV.eq(u, z), SV.eq(z, u), False{}, L.eq_sym(u, z), L.bor_fl(SV.eq(z, u), SV.mem(z, t), hu)),
        notin_cat(zt, u, t, L.band_r(SV.bnot(SV.mem(z, SV.cat(zt, Con{u, t}))), SV.distinct(SV.cat(zt, Con{u, t})), h)))

def subl_catr(xs: List<&2, Nat>, +ys: List<&2, Nat>) -> {L.subl(ys, SV.cat(xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      L.subl_refl(ys)
    case Con{+x, +t}:
      L.subl_cons_r(ys, x, SV.cat(t, ys), subl_catr(t, ys))

# Matching a constraint's equations as a unit
# --------------------------------------------
# The matching vm has matched equations Z (as sets), the ones still to
# match are rest; Z then rest are distinct equations.

def gli(+es: List<&2, E.QExpr>, +nv: Nat, +Z: List<&2, Nat>, +rest: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>) -> Bool:
  SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))))))))

def gli_dist(+es: List<&2, E.QExpr>, +nv: Nat, +Z: List<&2, Nat>, +rest: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {gli(es, nv, Z, rest, vm) == True{} : Bool}) -> {SV.distinct(ST.somes(vm)) == True{} : Bool}:
  L.band_l(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))))))), h)

def gli_mlen(+es: List<&2, E.QExpr>, +nv: Nat, +Z: List<&2, Nat>, +rest: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {gli(es, nv, Z, rest, vm) == True{} : Bool}) -> {SV.eq(L.mlen(vm), nv) == True{} : Bool}:
  L.band_l(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv)))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))))))), h))

def gli_valid(+es: List<&2, E.QExpr>, +nv: Nat, +Z: List<&2, Nat>, +rest: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {gli(es, nv, Z, rest, vm) == True{} : Bool}) -> {MX.valid(PA.dadjs(es), vm) == True{} : Bool}:
  L.band_l(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))))), L.band_r(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv)))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))))))), h)))

def gli_s1(+es: List<&2, E.QExpr>, +nv: Nat, +Z: List<&2, Nat>, +rest: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {gli(es, nv, Z, rest, vm) == True{} : Bool}) -> {L.subl(ST.somes(vm), Z) == True{} : Bool}:
  L.band_l(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv)))), L.band_r(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))))), L.band_r(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv)))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))))))), h))))

def gli_s2(+es: List<&2, E.QExpr>, +nv: Nat, +Z: List<&2, Nat>, +rest: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {gli(es, nv, Z, rest, vm) == True{} : Bool}) -> {L.subl(Z, ST.somes(vm)) == True{} : Bool}:
  L.band_l(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))), L.band_r(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv)))), L.band_r(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))))), L.band_r(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv)))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))))))), h)))))

def gli_zd(+es: List<&2, E.QExpr>, +nv: Nat, +Z: List<&2, Nat>, +rest: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {gli(es, nv, Z, rest, vm) == True{} : Bool}) -> {SV.distinct(SV.cat(Z, rest)) == True{} : Bool}:
  L.band_l(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv)), L.band_r(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))), L.band_r(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv)))), L.band_r(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))))), L.band_r(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv)))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))))))), h))))))

def gli_zb(+es: List<&2, E.QExpr>, +nv: Nat, +Z: List<&2, Nat>, +rest: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {gli(es, nv, Z, rest, vm) == True{} : Bool}) -> {SV.below(SV.cat(Z, rest), SV.neqs(es)) == True{} : Bool}:
  L.band_l(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv), L.band_r(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv)), L.band_r(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))), L.band_r(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv)))), L.band_r(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))))), L.band_r(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv)))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))))))), h)))))))

def gli_adjb(+es: List<&2, E.QExpr>, +nv: Nat, +Z: List<&2, Nat>, +rest: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {gli(es, nv, Z, rest, vm) == True{} : Bool}) -> {D.adjb(PA.dadjs(es), nv) == True{} : Bool}:
  L.band_r(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv), L.band_r(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv)), L.band_r(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))), L.band_r(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv)))), L.band_r(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))))), L.band_r(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv)))))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))))))), h)))))))

def gli_mk(+es: List<&2, E.QExpr>, +nv: Nat, +Z: List<&2, Nat>, +rest: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h_dist: {SV.distinct(ST.somes(vm)) == True{} : Bool}, h_mlen: {SV.eq(L.mlen(vm), nv) == True{} : Bool}, h_valid: {MX.valid(PA.dadjs(es), vm) == True{} : Bool}, h_s1: {L.subl(ST.somes(vm), Z) == True{} : Bool}, h_s2: {L.subl(Z, ST.somes(vm)) == True{} : Bool}, h_zd: {SV.distinct(SV.cat(Z, rest)) == True{} : Bool}, h_zb: {SV.below(SV.cat(Z, rest), SV.neqs(es)) == True{} : Bool}, h_adjb: {D.adjb(PA.dadjs(es), nv) == True{} : Bool}) -> {gli(es, nv, Z, rest, vm) == True{} : Bool}:
  L.band_i(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))))))), h_dist, L.band_i(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv)))))), h_mlen, L.band_i(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))))), h_valid, L.band_i(L.subl(ST.somes(vm), Z), SV.band(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv)))), h_s1, L.band_i(L.subl(Z, ST.somes(vm)), SV.band(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv))), h_s2, L.band_i(SV.distinct(SV.cat(Z, rest)), SV.band(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv)), h_zd, L.band_i(SV.below(SV.cat(Z, rest), SV.neqs(es)), D.adjb(PA.dadjs(es), nv), h_zb, h_adjb)))))))

def gok(+es: List<&2, E.QExpr>, +nv: Nat, +Zf: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>) -> Bool:
  SV.band(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm))))))

def gok_dist(+es: List<&2, E.QExpr>, +nv: Nat, +Zf: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {gok(es, nv, Zf, vm) == True{} : Bool}) -> {SV.distinct(ST.somes(vm)) == True{} : Bool}:
  L.band_l(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm))))), h)

def gok_mlen(+es: List<&2, E.QExpr>, +nv: Nat, +Zf: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {gok(es, nv, Zf, vm) == True{} : Bool}) -> {SV.eq(L.mlen(vm), nv) == True{} : Bool}:
  L.band_l(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm)))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm))))), h))

def gok_valid(+es: List<&2, E.QExpr>, +nv: Nat, +Zf: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {gok(es, nv, Zf, vm) == True{} : Bool}) -> {MX.valid(PA.dadjs(es), vm) == True{} : Bool}:
  L.band_l(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm))), L.band_r(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm)))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm))))), h)))

def gok_s1(+es: List<&2, E.QExpr>, +nv: Nat, +Zf: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {gok(es, nv, Zf, vm) == True{} : Bool}) -> {L.subl(ST.somes(vm), Zf) == True{} : Bool}:
  L.band_l(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm)), L.band_r(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm))), L.band_r(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm)))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm))))), h))))

def gok_s2(+es: List<&2, E.QExpr>, +nv: Nat, +Zf: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h: {gok(es, nv, Zf, vm) == True{} : Bool}) -> {L.subl(Zf, ST.somes(vm)) == True{} : Bool}:
  L.band_r(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm)), L.band_r(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm))), L.band_r(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm)))), L.band_r(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm))))), h))))

def gok_mk(+es: List<&2, E.QExpr>, +nv: Nat, +Zf: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, h_dist: {SV.distinct(ST.somes(vm)) == True{} : Bool}, h_mlen: {SV.eq(L.mlen(vm), nv) == True{} : Bool}, h_valid: {MX.valid(PA.dadjs(es), vm) == True{} : Bool}, h_s1: {L.subl(ST.somes(vm), Zf) == True{} : Bool}, h_s2: {L.subl(Zf, ST.somes(vm)) == True{} : Bool}) -> {gok(es, nv, Zf, vm) == True{} : Bool}:
  L.band_i(SV.distinct(ST.somes(vm)), SV.band(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm))))), h_dist, L.band_i(SV.eq(L.mlen(vm), nv), SV.band(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm)))), h_mlen, L.band_i(MX.valid(PA.dadjs(es), vm), SV.band(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm))), h_valid, L.band_i(L.subl(ST.somes(vm), Zf), L.subl(Zf, ST.somes(vm)), h_s1, h_s2))))


# what matching rest from Z gives
def GRes(+es: List<&2, E.QExpr>, +nv: Nat, +Z: List<&2, Nat>, +rest: List<&2, Nat>, g: ST.GS) -> Type:
  match g:
    case ST.GOk{+vm2}:
      {gok(es, nv, SV.cat(Z, rest), vm2) == True{} : Bool}
    case ST.GFail{ST.Red{+j, +s, +w}}:
      {SV.band(SV.mem(j, rest), L.subl(s, SV.cat(Z, rest))) == True{} : Bool} & SV.Overdet(es, s, w)

def gres_shift(g: ST.GS, +es: List<&2, E.QExpr>, +nv: Nat, +Z: List<&2, Nat>, +u: Nat, +t: List<&2, Nat>, h: GRes(es, nv, CO.lsnoc(Z, u), t, g)) -> GRes(es, nv, Z, Con{u, t}, g):
  match g:
    case ST.GOk{+vm2}:
      (%Equal.sym(List<&2, Nat>, SV.cat(Z, Con{u, t}), SV.cat(CO.lsnoc(Z, u), t), CW.catcons_snoc(Z, u, t)) : {gok(es, nv, _, vm2) == True{} : Bool}
        h)
    case ST.GFail{ST.Red{+j, +s, +w}}:
      (+hb, ho) = h
      (L.band_i(SV.mem(j, Con{u, t}), L.subl(s, SV.cat(Z, Con{u, t})), L.mem_tl(j, u, t, L.band_l(SV.mem(j, t), L.subl(s, SV.cat(CO.lsnoc(Z, u), t)), hb)),
        (%Equal.sym(List<&2, Nat>, SV.cat(Z, Con{u, t}), SV.cat(CO.lsnoc(Z, u), t), CW.catcons_snoc(Z, u, t)) : {L.subl(s, _) == True{} : Bool}
          L.band_r(SV.mem(j, t), L.subl(s, SV.cat(CO.lsnoc(Z, u), t)), hb))), ho)

def grpl_fail(t: List<&2, Nat>, +adj: List<&2, List<&2, Nat>>, +f: Nat, +r: ST.Red) -> {PA.grpl(t, adj, f, ST.GFail{r}) == ST.GFail{r} : ST.GS}:
  match t:
    case Nil{}:
      {==}
    case Con{u, tt}:
      {==}

# a found path from u: the matching for Z then u
def gli_next(+es: List<&2, E.QExpr>, +nv: Nat, +Z: List<&2, Nat>, +u: Nat, +t: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +vm2: List<&2, Maybe<&2, Nat>>, +hg: {gli(es, nv, Z, Con{u, t}, vm) == True{} : Bool}, +hs: {D.succ_ok(vm, u, vm2) == True{} : Bool}, +hv: {MX.valid(PA.dadjs(es), vm2) == True{} : Bool})
  -> {gli(es, nv, CO.lsnoc(Z, u), t, vm2) == True{} : Bool}:
  +sd = L.band_l(SV.distinct(ST.somes(vm2)), SV.band(SV.eq(SV.len(ST.somes(vm2)), 1n+SV.len(ST.somes(vm))), SV.band(L.subl(ST.somes(vm2), Con{u, ST.somes(vm)}), SV.eq(L.mlen(vm2), L.mlen(vm)))), hs)
  +r1 = L.band_r(SV.distinct(ST.somes(vm2)), SV.band(SV.eq(SV.len(ST.somes(vm2)), 1n+SV.len(ST.somes(vm))), SV.band(L.subl(ST.somes(vm2), Con{u, ST.somes(vm)}), SV.eq(L.mlen(vm2), L.mlen(vm)))), hs)
  +sl = L.band_l(SV.eq(SV.len(ST.somes(vm2)), 1n+SV.len(ST.somes(vm))), SV.band(L.subl(ST.somes(vm2), Con{u, ST.somes(vm)}), SV.eq(L.mlen(vm2), L.mlen(vm))), r1)
  +r2 = L.band_r(SV.eq(SV.len(ST.somes(vm2)), 1n+SV.len(ST.somes(vm))), SV.band(L.subl(ST.somes(vm2), Con{u, ST.somes(vm)}), SV.eq(L.mlen(vm2), L.mlen(vm))), r1)
  +ss = L.band_l(L.subl(ST.somes(vm2), Con{u, ST.somes(vm)}), SV.eq(L.mlen(vm2), L.mlen(vm)), r2)
  +sm = L.band_r(L.subl(ST.somes(vm2), Con{u, ST.somes(vm)}), SV.eq(L.mlen(vm2), L.mlen(vm)), r2)
  +zs = snoc_subl(Z, u)
  gli_mk(es, nv, CO.lsnoc(Z, u), t, vm2, sd,
    (%Equal.sym(Nat, L.mlen(vm2), L.mlen(vm), L.eq_ok(L.mlen(vm2), L.mlen(vm), sm)) : {SV.eq(_, nv) == True{} : Bool}
      gli_mlen(es, nv, Z, Con{u, t}, vm, hg)),
    hv,
    L.subl_trans(ST.somes(vm2), Con{u, ST.somes(vm)}, CO.lsnoc(Z, u), ss, L.subl_con(u, ST.somes(vm), CO.lsnoc(Z, u), L.subl_hd(u, Z, CO.lsnoc(Z, u), zs), L.subl_trans(ST.somes(vm), Z, CO.lsnoc(Z, u), gli_s1(es, nv, Z, Con{u, t}, vm, hg), subl_ext(Z, u)))),
    L.subl_trans(CO.lsnoc(Z, u), Con{u, Z}, ST.somes(vm2), subl_snoc(Z, u), L.subl_trans(Con{u, Z}, Con{u, ST.somes(vm)}, ST.somes(vm2), L.subl_con(u, Z, Con{u, ST.somes(vm)}, L.mem_hd(u, ST.somes(vm)), L.subl_cons_r(Z, u, ST.somes(vm), gli_s2(es, nv, Z, Con{u, t}, vm, hg))),
      pigc(ST.somes(vm2), Con{u, ST.somes(vm)}, sd, ss, (%L.eq_ok(SV.len(ST.somes(vm2)), 1n+SV.len(ST.somes(vm)), sl) : {KA.natle(_, SV.len(ST.somes(vm2))) == True{} : Bool}
        KA.natle_refl(SV.len(ST.somes(vm2))))))),
    (%CW.catcons_snoc(Z, u, t) : {SV.distinct(_) == True{} : Bool}
      gli_zd(es, nv, Z, Con{u, t}, vm, hg)),
    (%CW.catcons_snoc(Z, u, t) : {SV.below(_, SV.neqs(es)) == True{} : Bool}
      gli_zb(es, nv, Z, Con{u, t}, vm, hg)),
    gli_adjb(es, nv, Z, Con{u, t}, vm, hg))


def gl_step(a: ST.DS, +es: List<&2, E.QExpr>, +nv: Nat, +Z: List<&2, Nat>, +u: Nat, +t: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +hg: {gli(es, nv, Z, Con{u, t}, vm) == True{} : Bool}, +hres: {D.res(1n+nv, u, PA.dadjs(es), vm, Nil{}, ST.DS{False{}, vm, Nil{}}, ST.nthl(PA.dadjs(es), u), a) == True{} : Bool},
  hfr: {MX.fres(vm, PA.dadjs(es), Nil{}, ST.DS{False{}, vm, Nil{}}, a) == True{} : Bool},
  ih: @vm2: List<&2, Maybe<&2, Nat>> -> {gli(es, nv, CO.lsnoc(Z, u), t, vm2) == True{} : Bool} -> GRes(es, nv, CO.lsnoc(Z, u), t, PA.grpl(t, PA.dadjs(es), 1n+nv, ST.GOk{vm2})))
  -> GRes(es, nv, Z, Con{u, t}, PA.grpl(t, PA.dadjs(es), 1n+nv, ST.gstep(u, a, vm))):
  match a:
    case ST.DS{True{}, +vm2, vis}:
      gres_shift(PA.grpl(t, PA.dadjs(es), 1n+nv, ST.GOk{vm2}), es, nv, Z, u, t, ih(vm2, gli_next(es, nv, Z, u, t, vm, vm2, hg, hres, L.band_r(MX.agree(vm2, vm, Nil{}), MX.valid(PA.dadjs(es), vm2), hfr))))
    case ST.DS{False{}, vm2, +vis}:
      +AD = PA.dadjs(es)
      +hv = L.band_l(D.vis_ok(vm, AD, Nil{}, 1n+nv, vis), SV.band(L.subl(ST.nthl(AD, u), vis), SV.band(L.subl(Nil{}, vis), SV.bnot(False{}))), hres)
      +hn = L.band_l(L.subl(ST.nthl(AD, u), vis), SV.band(L.subl(Nil{}, vis), SV.bnot(False{})), L.band_r(D.vis_ok(vm, AD, Nil{}, 1n+nv, vis), SV.band(L.subl(ST.nthl(AD, u), vis), SV.band(L.subl(Nil{}, vis), SV.bnot(False{}))), hres))
      +ha = D.vo_a(vm, AD, Nil{}, 1n+nv, vis, hv)
      +hzs = gli_s1(es, nv, Z, Con{u, t}, vm, hg)
      +hzb = gli_zb(es, nv, Z, Con{u, t}, vm, hg)
      +hu = L.subl_hd(u, t, SV.cat(Z, Con{u, t}), subl_catr(Z, Con{u, t}))
      %Equal.sym(ST.GS, PA.grpl(t, AD, 1n+nv, ST.GFail{ST.Red{u, Con{u, ST.look(vm, vis)}, vis}}), ST.GFail{ST.Red{u, Con{u, ST.look(vm, vis)}, vis}}, grpl_fail(t, AD, 1n+nv, ST.Red{u, Con{u, ST.look(vm, vis)}, vis})) : GRes(es, nv, Z, Con{u, t}, _)
      (L.band_i(SV.mem(u, Con{u, t}), L.subl(Con{u, ST.look(vm, vis)}, SV.cat(Z, Con{u, t})), L.mem_hd(u, t),
         L.subl_con(u, ST.look(vm, vis), SV.cat(Z, Con{u, t}), hu, L.subl_trans(ST.look(vm, vis), ST.somes(vm), SV.cat(Z, Con{u, t}), L.look_subl(vm, vis, ha), L.subl_trans(ST.somes(vm), Z, SV.cat(Z, Con{u, t}), hzs, subl_catl(Z, Con{u, t}))))),
        wit_dep(es, vm, u, 1n+nv, vis, L.notin_subl(u, ST.somes(vm), Z, notin_cat(Z, u, t, gli_zd(es, nv, Z, Con{u, t}, vm, hg)), hzs), gli_dist(es, nv, Z, Con{u, t}, vm, hg),
          D.below_subl(ST.somes(vm), Z, SV.neqs(es), hzs, D.below_subl(Z, SV.cat(Z, Con{u, t}), SV.neqs(es), subl_catl(Z, Con{u, t}), hzb)),
          D.below_mem(u, SV.cat(Z, Con{u, t}), SV.neqs(es), hu, hzb), hv, hn))

# matching rest in turn, from Z
def gl_ok(rest: List<&2, Nat>, +es: List<&2, E.QExpr>, +nv: Nat, +Z: List<&2, Nat>, +vm: List<&2, Maybe<&2, Nat>>, +hg: {gli(es, nv, Z, rest, vm) == True{} : Bool}) -> GRes(es, nv, Z, rest, PA.grpl(rest, PA.dadjs(es), 1n+nv, ST.GOk{vm})):
  match rest:
    case Nil{}:
      (%CW.ncat_nil(Z) : {gok(es, nv, _, vm) == True{} : Bool}
        gok_mk(es, nv, Z, vm, gli_dist(es, nv, Z, Nil{}, vm, hg), gli_mlen(es, nv, Z, Nil{}, vm, hg), gli_valid(es, nv, Z, Nil{}, vm, hg), gli_s1(es, nv, Z, Nil{}, vm, hg), gli_s2(es, nv, Z, Nil{}, vm, hg)))
    case Con{+u, +t}:
      +AD = PA.dadjs(es)
      +hm = L.eq_ok(L.mlen(vm), nv, gli_mlen(es, nv, Z, Con{u, t}, vm, hg))
      gl_step(ST.search(1n+nv, AD, vm, u), es, nv, Z, u, t, vm, hg,
        D.search_ok(1n+nv, AD, vm, u, L.notin_subl(u, ST.somes(vm), Z, notin_cat(Z, u, t, gli_zd(es, nv, Z, Con{u, t}, vm, hg)), gli_s1(es, nv, Z, Con{u, t}, vm, hg)), gli_dist(es, nv, Z, Con{u, t}, vm, hg), RP.adjb_vm(AD, vm, nv, hm, gli_adjb(es, nv, Z, Con{u, t}, vm, hg)),
          (%Equal.sym(Nat, L.mlen(vm), nv, hm) : {KA.natle(1n+_, 1n+nv) == True{} : Bool}
            KA.natle_refl(1n+nv))),
        MX.frame(1n+nv, ST.nthl(AD, u), ST.cls(vm, Nil{}, ST.nthl(AD, u)), u, AD, vm, ST.DS{False{}, vm, Nil{}}, Nil{}, {==}, L.subl_refl(ST.nthl(AD, u)), gli_valid(es, nv, Z, Con{u, t}, vm, hg), {==}),
        vm2 => h2 => gl_ok(t, es, nv, CO.lsnoc(Z, u), vm2, h2))

# Matchable
# ---------
# Each matched equation p's variable: the first v with vm(v) = p.

def vfind.pick(b: Bool, r: Nat) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      1n+r

def vfind(vm: List<&2, Maybe<&2, Nat>>, +p: Nat) -> Nat:
  match vm:
    case Nil{}:
      0n
    case Con{None{}, t}:
      1n+vfind(t, p)
    case Con{Some{e}, t}:
      vfind.pick(SV.eq(e, p), vfind(t, p))

def vmap(+vm: List<&2, Maybe<&2, Nat>>, ps: List<&2, Nat>) -> List<&2, Nat>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{p, t}:
      Con{vfind(vm, p), vmap(vm, t)}

def some_inj(+p: Nat, +q: Nat, h: {Some{p} == Some{q} : Maybe<&2, Nat>}) -> {p == q : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, x => ST.look.of(x), Some{p}, Some{q}, h)

def getm_vfind.s(b: Bool, +e: Nat, +t: List<&2, Maybe<&2, Nat>>, +p: Nat, eb: {SV.eq(e, p) == b : Bool}, hm: {SV.bor(SV.eq(p, e), SV.mem(p, ST.somes(t))) == True{} : Bool},
  ih: {SV.mem(p, ST.somes(t)) == True{} : Bool} -> {ST.getm(t, vfind(t, p)) == Some{p} : Maybe<&2, Nat>}) -> {ST.getm(Con{Some{e}, t}, vfind.pick(b, vfind(t, p))) == Some{p} : Maybe<&2, Nat>}:
  match b:
    case True{}:
      Equal.cong(Nat, Maybe<&2, Nat>, x => Some{x}, e, p, L.eq_ok(e, p, eb))
    case False{}:
      ih(L.bor_rf(SV.eq(p, e), SV.mem(p, ST.somes(t)), hm, Equal.trans(Bool, SV.eq(p, e), SV.eq(e, p), False{}, L.eq_sym(p, e), eb)))

# p matched: vm sends its variable to p
def getm_vfind(vm: List<&2, Maybe<&2, Nat>>, +p: Nat, h: {SV.mem(p, ST.somes(vm)) == True{} : Bool}) -> {ST.getm(vm, vfind(vm, p)) == Some{p} : Maybe<&2, Nat>}:
  match vm:
    case Nil{}:
      absurd({ST.getm(Nil{}, 0n) == Some{p} : Maybe<&2, Nat>}, KA.ft(h))
    case Con{None{}, +t}:
      getm_vfind(t, p, h)
    case Con{Some{+e}, +t}:
      getm_vfind.s(SV.eq(e, p), e, t, p, {==}, h, q => getm_vfind(t, p, q))

def vmem.c(b: Bool, +vm: List<&2, Maybe<&2, Nat>>, +p: Nat, +q: Nat, +t: List<&2, Nat>, +hp: {SV.mem(p, ST.somes(vm)) == True{} : Bool}, +hq: {SV.mem(q, ST.somes(vm)) == True{} : Bool}, eb: {SV.eq(vfind(vm, p), vfind(vm, q)) == b : Bool},
  h: {SV.bor(b, SV.mem(vfind(vm, p), vmap(vm, t))) == True{} : Bool}, ih: {SV.mem(vfind(vm, p), vmap(vm, t)) == True{} : Bool} -> {SV.mem(p, t) == True{} : Bool}) -> {SV.mem(p, Con{q, t}) == True{} : Bool}:
  match b:
    case True{}:
      +pq = some_inj(p, q, Equal.trans(Maybe<&2, Nat>, Some{p}, ST.getm(vm, vfind(vm, p)), Some{q}, Equal.sym(Maybe<&2, Nat>, ST.getm(vm, vfind(vm, p)), Some{p}, getm_vfind(vm, p, hp)),
        (%Equal.sym(Nat, vfind(vm, p), vfind(vm, q), L.eq_ok(vfind(vm, p), vfind(vm, q), eb)) : {ST.getm(vm, _) == Some{q} : Maybe<&2, Nat>}
          getm_vfind(vm, q, hq))))
      L.bor_l(SV.eq(p, q), SV.mem(p, t), (%pq : {SV.eq(p, _) == True{} : Bool}
        L.eq_refl(p)))
    case False{}:
      L.mem_tl(p, q, t, ih(h))

# p's variable among t's: p among t
def vmem(+vm: List<&2, Maybe<&2, Nat>>, +p: Nat, t: List<&2, Nat>, +hp: {SV.mem(p, ST.somes(vm)) == True{} : Bool}, +ht: {L.subl(t, ST.somes(vm)) == True{} : Bool}, h: {SV.mem(vfind(vm, p), vmap(vm, t)) == True{} : Bool}) -> {SV.mem(p, t) == True{} : Bool}:
  match t:
    case Nil{}:
      absurd({SV.mem(p, Nil{}) == True{} : Bool}, KA.ft(h))
    case Con{+q, +tt}:
      vmem.c(SV.eq(vfind(vm, p), vfind(vm, q)), vm, p, q, tt, hp, L.subl_hd(q, tt, ST.somes(vm), ht), {==}, h, x => vmem(vm, p, tt, hp, L.subl_tl(q, tt, ST.somes(vm), ht), x))

def vnot.c(b: Bool, +vm: List<&2, Maybe<&2, Nat>>, +p: Nat, +t: List<&2, Nat>, +hp: {SV.mem(p, ST.somes(vm)) == True{} : Bool}, +ht: {L.subl(t, ST.somes(vm)) == True{} : Bool}, e: {SV.mem(vfind(vm, p), vmap(vm, t)) == b : Bool},
  hn: {SV.mem(p, t) == False{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      absurd({True{} == False{} : Bool}, KA.tf(Equal.trans(Bool, True{}, SV.mem(p, t), False{}, Equal.sym(Bool, SV.mem(p, t), True{}, vmem(vm, p, t, hp, ht, e)), hn)))
    case False{}:
      {==}

def vmap_dist(+vm: List<&2, Maybe<&2, Nat>>, ps: List<&2, Nat>, +hd: {SV.distinct(ps) == True{} : Bool}, +hs: {L.subl(ps, ST.somes(vm)) == True{} : Bool}) -> {SV.distinct(vmap(vm, ps)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case Con{+p, +t}:
      L.band_i(SV.bnot(SV.mem(vfind(vm, p), vmap(vm, t))), SV.distinct(vmap(vm, t)),
        KB.bnot_f(SV.mem(vfind(vm, p), vmap(vm, t)), vnot.c(SV.mem(vfind(vm, p), vmap(vm, t)), vm, p, t, L.subl_hd(p, t, ST.somes(vm), hs), L.subl_tl(p, t, ST.somes(vm), hs), {==},
          KB.bnot_t(SV.mem(p, t), L.band_l(SV.bnot(SV.mem(p, t)), SV.distinct(t), hd)))),
        vmap_dist(vm, t, L.band_r(SV.bnot(SV.mem(p, t)), SV.distinct(t), hd), L.subl_tl(p, t, ST.somes(vm), hs)))

# each equation at ps depends on its variable
def depall(+es: List<&2, E.QExpr>, +vm: List<&2, Maybe<&2, Nat>>, ps: List<&2, Nat>, +hv: {MX.valid(PA.dadjs(es), vm) == True{} : Bool}, +hs: {L.subl(ps, ST.somes(vm)) == True{} : Bool}) -> SV.DepAll(SV.picked(es, ps), vmap(vm, ps)):
  match ps:
    case Nil{}:
      Unit{}
    case Con{+p, +t}:
      (DP.dadj_depends(SV.eqat(es, p), vfind(vm, p), (%nthl_dadjs(es, p) : {SV.mem(vfind(vm, p), _) == True{} : Bool}
        MX.valid_get(PA.dadjs(es), vm, vfind(vm, p), 0n, p, hv, getm_vfind(vm, p, L.subl_hd(p, t, ST.somes(vm), hs))))),
       depall(es, vm, t, hv, L.subl_tl(p, t, ST.somes(vm), hs)))

# the equations at distinct matched positions ps can be matched
def matchable_of(+es: List<&2, E.QExpr>, +vm: List<&2, Maybe<&2, Nat>>, +ps: List<&2, Nat>, +hv: {MX.valid(PA.dadjs(es), vm) == True{} : Bool}, +hs: {L.subl(ps, ST.somes(vm)) == True{} : Bool}, +hd: {SV.distinct(ps) == True{} : Bool}) -> SV.Matchable(SV.picked(es, ps)):
  (vmap(vm, ps), (vmap_dist(vm, ps, hd, hs), depall(es, vm, ps, hv, hs)))
