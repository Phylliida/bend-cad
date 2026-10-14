# Proofs of the plan laws (DESIGN §8.4, §8.6; stated in ROADMAP.bend while
# sk-06 is open). Untrusted: proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../spec/cert.bend as C
import ../spec/sketch.bend as SK
import ../spec/box.bend as BX
import ./fring.bend as FR
import ./ford.bend as FO
import ./fvec.bend as FV
import ./karith.bend as KA
import ./kball.bend as KB
import ./cert.bend as CK
import ./certpf.bend as CP
import ./real.bend as RL
import ./dmat.bend as DM
import ./banach.bend as BA
import ./plan.bend as PL
import ./slope.bend as SL

# Side conditions
# ---------------

# H c - H r = H (c - r)
def es_lt(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: N.NC(K), +r: N.NC(K), hk: {KA.klt(~K, N.nzero(K), KA.ksub(~K, c, r)) == True{} : Bool}) -> O.lt(F, O.zero(F), O.sub(~F, N.emap(K, F, H, c), N.emap(K, F, H, r))):
  RL.lt_rw_r(~F, O.zero(F), N.emap(K, F, H, KA.ksub(~K, c, r)), O.sub(~F, N.emap(K, F, H, c), N.emap(K, F, H, r)), Equal.sym(O.C(F), O.sub(~F, N.emap(K, F, H, c), N.emap(K, F, H, r)), N.emap(K, F, H, KA.ksub(~K, c, r)), KA.es(~K, ~F, ~H, c, r)), FO.lt_subst_l(~F, N.emap(K, F, H, N.nzero(K)), O.zero(F), N.emap(K, F, H, KA.ksub(~K, c, r)), N.e_zero(K, F, H), KA.klt_ok(~K, ~F, ~H, N.nzero(K), KA.ksub(~K, c, r), hk)))

def es_le(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: N.NC(K), +r: N.NC(K), hk: {KA.kle(~K, N.nzero(K), KA.ksub(~K, c, r)) == True{} : Bool}) -> O.le(~F, O.zero(F), O.sub(~F, N.emap(K, F, H, c), N.emap(K, F, H, r))):
  FV.le_rw_r(~F, O.zero(F), N.emap(K, F, H, KA.ksub(~K, c, r)), O.sub(~F, N.emap(K, F, H, c), N.emap(K, F, H, r)), Equal.sym(O.C(F), O.sub(~F, N.emap(K, F, H, c), N.emap(K, F, H, r)), N.emap(K, F, H, KA.ksub(~K, c, r)), KA.es(~K, ~F, ~H, c, r)), RL.le_rw_l(~F, N.emap(K, F, H, N.nzero(K)), O.zero(F), N.emap(K, F, H, KA.ksub(~K, c, r)), N.e_zero(K, F, H), KA.kle_ok(~K, ~F, ~H, N.nzero(K), KA.ksub(~K, c, r), hk)))

# v in the ball (c, r) with c - r > 0 (or >= 0) is positive (not negative)
def bin_pos(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +v: O.C(F), b: KB.KB<K>, hb: KB.bin(~K, ~F, ~H, v, b), hk: {KA.klt(~K, N.nzero(K), KA.ksub(~K, KB.KB.c(K, b), KB.KB.r(K, b))) == True{} : Bool}) -> O.lt(F, O.zero(F), v):
  match b:
    case KB.KB{+c, +r}:
      FO.lt_le_trans(~F, O.zero(F), O.sub(~F, N.emap(K, F, H, c), N.emap(K, F, H, r)), v, es_lt(~K, ~F, ~H, c, r, hk), BA.box_lo(~F, v, N.emap(K, F, H, c), N.emap(K, F, H, r), hb))

def bin_nn(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +v: O.C(F), b: KB.KB<K>, hb: KB.bin(~K, ~F, ~H, v, b), hk: {KA.kle(~K, N.nzero(K), KA.ksub(~K, KB.KB.c(K, b), KB.KB.r(K, b))) == True{} : Bool}) -> O.le(~F, O.zero(F), v):
  match b:
    case KB.KB{+c, +r}:
      DM.le_trans(~F, O.zero(F), O.sub(~F, N.emap(K, F, H, c), N.emap(K, F, H, r)), v, es_le(~K, ~F, ~H, c, r, hk), BA.box_lo(~F, v, N.emap(K, F, H, c), N.emap(K, F, H, r), hb))

def sides_pf(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x: M.Vec(~F), +box: List<&2, KB.KB<K>>, +hx: KB.inbox(~K, ~F, ~H, x, box), ss: List<&2, SK.Side>, +ok: {PL.sides_ok(~K, box, ss) == True{} : Bool}) -> SK.Sides(~F, x, ss):
  match ss:
    case Nil{}:
      Unit{}
    case Con{SK.Gt0{+e}, +t}:
      +h1 = KA.band_l(PL.side_ok(~K, box, SK.Gt0{e}), PL.sides_ok(~K, box, t), ok)
      +hh = KA.band_l(KB.held(~K, e), KA.klt(~K, N.nzero(K), KA.ksub(~K, KB.KB.c(K, KB.kball(~K, box, e)), KB.KB.r(K, KB.kball(~K, box, e)))), h1)
      (bin_pos(~K, ~F, ~H, O.eval(~F, x, e), KB.kball(~K, box, e), KB.ball_ok(~K, ~F, ~H, x, box, e, hh, hx), KA.band_r(KB.held(~K, e), KA.klt(~K, N.nzero(K), KA.ksub(~K, KB.KB.c(K, KB.kball(~K, box, e)), KB.KB.r(K, KB.kball(~K, box, e)))), h1)), sides_pf(~K, ~F, ~H, x, box, hx, t, KA.band_r(PL.side_ok(~K, box, SK.Gt0{e}), PL.sides_ok(~K, box, t), ok)))
    case Con{SK.Ge0{+e}, +t}:
      +h1 = KA.band_l(PL.side_ok(~K, box, SK.Ge0{e}), PL.sides_ok(~K, box, t), ok)
      +hh = KA.band_l(KB.held(~K, e), KA.kle(~K, N.nzero(K), KA.ksub(~K, KB.KB.c(K, KB.kball(~K, box, e)), KB.KB.r(K, KB.kball(~K, box, e)))), h1)
      (bin_nn(~K, ~F, ~H, O.eval(~F, x, e), KB.kball(~K, box, e), KB.ball_ok(~K, ~F, ~H, x, box, e, hh, hx), KA.band_r(KB.held(~K, e), KA.kle(~K, N.nzero(K), KA.ksub(~K, KB.KB.c(K, KB.kball(~K, box, e)), KB.KB.r(K, KB.kball(~K, box, e)))), h1)), sides_pf(~K, ~F, ~H, x, box, hx, t, KA.band_r(PL.side_ok(~K, box, SK.Ge0{e}), PL.sides_ok(~K, box, t), ok)))

def box_sides.go(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +sides: List<&2, SK.Side>, +gc: N.KVec(~K), +gr: N.KVec(~K), +ok: {PL.check_sides(~K, sides, gc, gr) == True{} : Bool}, +x: M.Vec(~F), h: BX.inbox(~K, ~F, ~H, gc, gr, x)) -> SK.Sides(~F, x, sides):
  (hl, hr) = h
  +box = CK.zipb(~K, gc, gr)
  sides_pf(~K, ~F, ~H, x, box, CP.rbnd_inbox(~K, ~F, ~H, x, gc, gr, hr, KA.kvle_ok(~K, ~F, ~H, Nil{}, gr, KA.band_l(KA.kvle(~K, Nil{}, gr), PL.sides_ok(~K, box, sides), ok))), sides, KA.band_r(KA.kvle(~K, Nil{}, gr), PL.sides_ok(~K, box, sides), ok))

# LAW box_sides: every point of the box meets the certified side conditions
def box_sides(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +sides: List<&2, SK.Side>, +gc: N.KVec(~K), +gr: N.KVec(~K), ok: {PL.check_sides(~K, sides, gc, gr) == True{} : Bool}, +x: M.Vec(~F), h: BX.inbox(~K, ~F, ~H, gc, gr, x)) -> SK.Sides(~F, x, sides):
  box_sides.go(~K, ~F, ~H, sides, gc, gr, ok, x, h)

# Lookups in appended assignments
# -------------------------------

def la_l(~F: O.OField, p: M.Vec(~F), +y: M.Vec(~F), v: Nat, h: {KA.natle(1n+v, M.len(~F, p)) == True{} : Bool}) -> {O.lookup(~F, C.app(~F, p, y), v) == O.lookup(~F, p, v) : O.C(F)}:
  match p v:
    case Nil{} v:
      FO.absurd({O.lookup(~F, y, v) == O.zero(F) : O.C(F)}, KA.ft(h))
    case Con{a, ps} 0n:
      {==}
    case Con{a, ps} 1n+w:
      la_l(~F, ps, y, w, h)

def la_r(~F: O.OField, p: M.Vec(~F), +y: M.Vec(~F), v: Nat, h: {KA.natle(1n+v, M.len(~F, p)) == False{} : Bool}) -> {O.lookup(~F, C.app(~F, p, y), v) == O.lookup(~F, y, PL.minus(M.len(~F, p), v)) : O.C(F)}:
  match p v:
    case Nil{} v:
      {==}
    case Con{a, ps} 0n:
      FO.absurd({O.lookup(~F, C.app(~F, Con{a, ps}, y), 0n) == O.lookup(~F, y, PL.minus(M.len(~F, Con{a, ps}), 0n)) : O.C(F)}, KA.ft(Equal.sym(Bool, KA.natle(0n, M.len(~F, ps)), False{}, h)))
    case Con{a, ps} 1n+w:
      la_r(~F, ps, y, w, h)

# Numbers
# -------

def minus_add(n: Nat, +k: Nat) -> {PL.minus(n, Nat.add(n, k)) == k : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      minus_add(m, k)

def natle_add_f(n: Nat, +k: Nat) -> {KA.natle(1n+Nat.add(n, k), n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      natle_add_f(m, k)

def natle_add_c(n: Nat, +a: Nat, +b: Nat, h: {KA.natle(1n+Nat.add(n, a), Nat.add(n, b)) == True{} : Bool}) -> {KA.natle(1n+a, b) == True{} : Bool}:
  match n:
    case 0n:
      h
    case 1n+m:
      natle_add_c(m, a, b, h)

# v - o < n, for v < o + n and v not below o
def natle_minus(o: Nat, v: Nat, +n: Nat, h1: {KA.natle(1n+v, Nat.add(o, n)) == True{} : Bool}, h2: {KA.natle(1n+v, o) == False{} : Bool}) -> {KA.natle(1n+PL.minus(o, v), n) == True{} : Bool}:
  match o v:
    case 0n v:
      h1
    case 1n+k 0n:
      FO.absurd({KA.natle(1n+PL.minus(1n+k, 0n), n) == True{} : Bool}, KA.ft(Equal.sym(Bool, KA.natle(0n, k), False{}, h2)))
    case 1n+k 1n+w:
      natle_minus(k, w, n, h1, h2)

def pos_nth.go(+v: Nat, +h: Nat, +t: List<&2, Nat>, b: Bool, e: {KA.nateq(v, h) == b : Bool}, hh: {KA.natle(1n+PL.pos.go(b, PL.pos(v, t)), 1n+PL.nlen(t)) == True{} : Bool}, ih: {KA.natle(1n+PL.pos(v, t), PL.nlen(t)) == True{} : Bool} -> {PL.nthn(t, PL.pos(v, t)) == v : Nat}) -> {PL.nthn(Con{h, t}, PL.pos.go(b, PL.pos(v, t))) == v : Nat}:
  match b:
    case True{}:
      Equal.sym(Nat, v, h, CP.nateq_ok(v, h, e))
    case False{}:
      ih(hh)

# the entry at v's position is v, when v is present
def pos_nth(+v: Nat, xs: List<&2, Nat>, h: {KA.natle(1n+PL.pos(v, xs), PL.nlen(xs)) == True{} : Bool}) -> {PL.nthn(xs, PL.pos(v, xs)) == v : Nat}:
  match xs:
    case Nil{}:
      FO.absurd({0n == v : Nat}, KA.ft(h))
    case Con{+hd, +t}:
      pos_nth.go(v, hd, t, KA.nateq(v, hd), {==}, h, hi => pos_nth(v, t, hi))

# The substitution law
# --------------------

# the parameters' values: x_v for each listed v
def zmap(~F: O.OField, +p: M.Vec(~F), pars: List<&2, Nat>) -> M.Vec(~F):
  match pars:
    case Nil{}:
      Nil{}
    case Con{v, t}:
      Con{O.lookup(~F, p, v), zmap(~F, p, t)}

def look_zmap(~F: O.OField, +p: M.Vec(~F), pars: List<&2, Nat>, k: Nat, h: {KA.natle(1n+k, PL.nlen(pars)) == True{} : Bool}) -> {O.lookup(~F, zmap(~F, p, pars), k) == O.lookup(~F, p, PL.nthn(pars, k)) : O.C(F)}:
  match pars k:
    case Nil{} k:
      FO.absurd({O.zero(F) == O.lookup(~F, p, 0n) : O.C(F)}, KA.ft(h))
    case Con{v, t} 0n:
      {==}
    case Con{v, t} 1n+j:
      look_zmap(~F, p, t, j, h)

def len_zmap(~F: O.OField, +p: M.Vec(~F), pars: List<&2, Nat>) -> {M.len(~F, zmap(~F, p, pars)) == PL.nlen(pars) : Nat}:
  match pars:
    case Nil{}:
      {==}
    case Con{v, t}:
      %Equal.sym(Nat, M.len(~F, zmap(~F, p, t)), PL.nlen(t), len_zmap(~F, p, t)) : {1n+_ == 1n+PL.nlen(t) : Nat}
      {==}

def look_rw(~F: O.OField, +x: M.Vec(~F), +i: Nat, +j: Nat, e: {i == j : Nat}) -> {O.lookup(~F, x, i) == O.lookup(~F, x, j) : O.C(F)}:
  %e : {O.lookup(~F, x, i) == O.lookup(~F, x, _) : O.C(F)}
  {==}

def natle_rw(+a: Nat, +b: Nat, +b2: Nat, e: {b == b2 : Nat}, h: {KA.natle(a, b) == True{} : Bool}) -> {KA.natle(a, b2) == True{} : Bool}:
  %e : {KA.natle(a, _) == True{} : Bool}
  h

def natlef_rw(+a: Nat, +b: Nat, +b2: Nat, e: {b == b2 : Nat}, h: {KA.natle(a, b) == False{} : Bool}) -> {KA.natle(a, b2) == False{} : Bool}:
  %e : {KA.natle(a, _) == False{} : Bool}
  h

def mrw(+a: Nat, +b: Nat, +v: Nat, e: {a == b : Nat}) -> {PL.minus(a, v) == PL.minus(b, v) : Nat}:
  %e : {PL.minus(a, v) == PL.minus(_, v) : Nat}
  {==}

# a parameter: lookup at n + its position in (y ++ z) is x_v
def subst.par(~F: O.OField, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +p: M.Vec(~F), +y: M.Vec(~F), +v: Nat, +hp: {M.len(~F, p) == o : Nat}, +hy: {M.len(~F, y) == n : Nat}, hv: {KA.natle(1n+v, o) == True{} : Bool}, hl: {KA.natle(1n+Nat.add(n, PL.pos(v, pars)), Nat.add(n, PL.nlen(pars))) == True{} : Bool}) -> {O.lookup(~F, C.app(~F, y, zmap(~F, p, pars)), Nat.add(n, PL.pos(v, pars))) == O.lookup(~F, C.app(~F, p, y), v) : O.C(F)}:
  +k = PL.pos(v, pars)
  +z = zmap(~F, p, pars)
  +hk = natle_add_c(n, k, PL.nlen(pars), hl)
  +e1 = la_r(~F, y, z, Nat.add(n, k), natlef_rw(1n+Nat.add(n, k), n, M.len(~F, y), Equal.sym(Nat, M.len(~F, y), n, hy), natle_add_f(n, k)))
  +e2 = Equal.trans(Nat, PL.minus(M.len(~F, y), Nat.add(n, k)), PL.minus(n, Nat.add(n, k)), k, mrw(M.len(~F, y), n, Nat.add(n, k), hy), minus_add(n, k))
  +e3 = Equal.trans(O.C(F), O.lookup(~F, z, k), O.lookup(~F, p, PL.nthn(pars, k)), O.lookup(~F, p, v), look_zmap(~F, p, pars, k, hk), look_rw(~F, p, PL.nthn(pars, k), v, pos_nth(v, pars, hk)))
  +e4 = Equal.sym(O.C(F), O.lookup(~F, C.app(~F, p, y), v), O.lookup(~F, p, v), la_l(~F, p, y, v, natle_rw(1n+v, o, M.len(~F, p), Equal.sym(Nat, M.len(~F, p), o, hp), hv)))
  Equal.trans(O.C(F), O.lookup(~F, C.app(~F, y, z), Nat.add(n, k)), O.lookup(~F, z, PL.minus(M.len(~F, y), Nat.add(n, k))), O.lookup(~F, C.app(~F, p, y), v), e1,
    Equal.trans(O.C(F), O.lookup(~F, z, PL.minus(M.len(~F, y), Nat.add(n, k))), O.lookup(~F, z, k), O.lookup(~F, C.app(~F, p, y), v), look_rw(~F, z, PL.minus(M.len(~F, y), Nat.add(n, k)), k, e2),
      Equal.trans(O.C(F), O.lookup(~F, z, k), O.lookup(~F, p, v), O.lookup(~F, C.app(~F, p, y), v), e3, e4)))

# an unknown: lookup at v - o in (y ++ z) is x_v
def subst.unk(~F: O.OField, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +p: M.Vec(~F), +y: M.Vec(~F), +v: Nat, +hp: {M.len(~F, p) == o : Nat}, +hy: {M.len(~F, y) == n : Nat}, +hv: {KA.natle(1n+v, o) == False{} : Bool}, hb: {KA.natle(1n+v, Nat.add(o, n)) == True{} : Bool}) -> {O.lookup(~F, C.app(~F, y, zmap(~F, p, pars)), PL.minus(o, v)) == O.lookup(~F, C.app(~F, p, y), v) : O.C(F)}:
  +z = zmap(~F, p, pars)
  +e1 = la_l(~F, y, z, PL.minus(o, v), natle_rw(1n+PL.minus(o, v), n, M.len(~F, y), Equal.sym(Nat, M.len(~F, y), n, hy), natle_minus(o, v, n, hb, hv)))
  +e2 = la_r(~F, p, y, v, natlef_rw(1n+v, o, M.len(~F, p), Equal.sym(Nat, M.len(~F, p), o, hp), hv))
  Equal.trans(O.C(F), O.lookup(~F, C.app(~F, y, z), PL.minus(o, v)), O.lookup(~F, y, PL.minus(o, v)), O.lookup(~F, C.app(~F, p, y), v), e1, Equal.sym(O.C(F), O.lookup(~F, C.app(~F, p, y), v), O.lookup(~F, y, PL.minus(o, v)), Equal.trans(O.C(F), O.lookup(~F, C.app(~F, p, y), v), O.lookup(~F, y, PL.minus(M.len(~F, p), v)), O.lookup(~F, y, PL.minus(o, v)), e2, look_rw(~F, y, PL.minus(M.len(~F, p), v), PL.minus(o, v), mrw(M.len(~F, p), o, v, hp)))))

def cadd(~F: O.OField, +a1: O.C(F), +a2: O.C(F), +b1: O.C(F), +b2: O.C(F), ea: {a1 == a2 : O.C(F)}, eb: {b1 == b2 : O.C(F)}) -> {O.add(F, a1, b1) == O.add(F, a2, b2) : O.C(F)}:
  %ea : {O.add(F, a1, b1) == O.add(F, _, b2) : O.C(F)}
  %eb : {O.add(F, a1, b1) == O.add(F, a1, _) : O.C(F)}
  {==}

def csub(~F: O.OField, +a1: O.C(F), +a2: O.C(F), +b1: O.C(F), +b2: O.C(F), ea: {a1 == a2 : O.C(F)}, eb: {b1 == b2 : O.C(F)}) -> {O.sub(~F, a1, b1) == O.sub(~F, a2, b2) : O.C(F)}:
  %ea : {O.sub(~F, a1, b1) == O.sub(~F, _, b2) : O.C(F)}
  %eb : {O.sub(~F, a1, b1) == O.sub(~F, a1, _) : O.C(F)}
  {==}

def cmul(~F: O.OField, +a1: O.C(F), +a2: O.C(F), +b1: O.C(F), +b2: O.C(F), ea: {a1 == a2 : O.C(F)}, eb: {b1 == b2 : O.C(F)}) -> {O.mul(F, a1, b1) == O.mul(F, a2, b2) : O.C(F)}:
  %ea : {O.mul(F, a1, b1) == O.mul(F, _, b2) : O.C(F)}
  %eb : {O.mul(F, a1, b1) == O.mul(F, a1, _) : O.C(F)}
  {==}

def cneg(~F: O.OField, +a1: O.C(F), +a2: O.C(F), ea: {a1 == a2 : O.C(F)}) -> {O.neg(F, a1) == O.neg(F, a2) : O.C(F)}:
  %ea : {O.neg(F, a1) == O.neg(F, _) : O.C(F)}
  {==}

def subst.var(~F: O.OField, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +p: M.Vec(~F), +y: M.Vec(~F), +v: Nat, +hp: {M.len(~F, p) == o : Nat}, +hy: {M.len(~F, y) == n : Nat}, b: Bool, e: {KA.natle(1n+v, o) == b : Bool}, hb: {KA.natle(1n+v, Nat.add(o, n)) == True{} : Bool}, hl: {SL.below(Nat.add(n, PL.nlen(pars)), E.QVar{PL.loc.go(b, o, n, pars, v)}) == True{} : Bool}) -> {O.eval(~F, C.app(~F, y, zmap(~F, p, pars)), E.QVar{PL.loc.go(b, o, n, pars, v)}) == O.eval(~F, C.app(~F, p, y), E.QVar{v}) : O.C(F)}:
  match b:
    case True{}:
      subst.par(~F, o, n, pars, p, y, v, hp, hy, e, hl)
    case False{}:
      subst.unk(~F, o, n, pars, p, y, v, hp, hy, e, hb)

# a block's renumbered equation at (y ++ z) is the equation at (p ++ y),
# for p of length o, y of length n and z the parameters' values in p
def subst(~F: O.OField, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +p: M.Vec(~F), +y: M.Vec(~F), e: E.QExpr, +hp: {M.len(~F, p) == o : Nat}, +hy: {M.len(~F, y) == n : Nat}, +hb: {SL.below(Nat.add(o, n), e) == True{} : Bool}, +hl: {SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, e)) == True{} : Bool}) -> {O.eval(~F, C.app(~F, y, zmap(~F, p, pars)), PL.rename(o, n, pars, e)) == O.eval(~F, C.app(~F, p, y), e) : O.C(F)}:
  match e:
    case E.QVar{+v}:
      subst.var(~F, o, n, pars, p, y, v, hp, hy, KA.natle(1n+v, o), {==}, hb, hl)
    case E.QCst{q}:
      {==}
    case E.QAdd{+a, +b}:
      cadd(~F, O.eval(~F, C.app(~F, y, zmap(~F, p, pars)), PL.rename(o, n, pars, a)), O.eval(~F, C.app(~F, p, y), a), O.eval(~F, C.app(~F, y, zmap(~F, p, pars)), PL.rename(o, n, pars, b)), O.eval(~F, C.app(~F, p, y), b), subst(~F, o, n, pars, p, y, a, hp, hy, KA.band_l(SL.below(Nat.add(o, n), a), SL.below(Nat.add(o, n), b), hb), KA.band_l(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, a)), SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, b)), hl)), subst(~F, o, n, pars, p, y, b, hp, hy, KA.band_r(SL.below(Nat.add(o, n), a), SL.below(Nat.add(o, n), b), hb), KA.band_r(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, a)), SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, b)), hl)))
    case E.QSub{+a, +b}:
      csub(~F, O.eval(~F, C.app(~F, y, zmap(~F, p, pars)), PL.rename(o, n, pars, a)), O.eval(~F, C.app(~F, p, y), a), O.eval(~F, C.app(~F, y, zmap(~F, p, pars)), PL.rename(o, n, pars, b)), O.eval(~F, C.app(~F, p, y), b), subst(~F, o, n, pars, p, y, a, hp, hy, KA.band_l(SL.below(Nat.add(o, n), a), SL.below(Nat.add(o, n), b), hb), KA.band_l(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, a)), SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, b)), hl)), subst(~F, o, n, pars, p, y, b, hp, hy, KA.band_r(SL.below(Nat.add(o, n), a), SL.below(Nat.add(o, n), b), hb), KA.band_r(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, a)), SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, b)), hl)))
    case E.QMul{+a, +b}:
      cmul(~F, O.eval(~F, C.app(~F, y, zmap(~F, p, pars)), PL.rename(o, n, pars, a)), O.eval(~F, C.app(~F, p, y), a), O.eval(~F, C.app(~F, y, zmap(~F, p, pars)), PL.rename(o, n, pars, b)), O.eval(~F, C.app(~F, p, y), b), subst(~F, o, n, pars, p, y, a, hp, hy, KA.band_l(SL.below(Nat.add(o, n), a), SL.below(Nat.add(o, n), b), hb), KA.band_l(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, a)), SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, b)), hl)), subst(~F, o, n, pars, p, y, b, hp, hy, KA.band_r(SL.below(Nat.add(o, n), a), SL.below(Nat.add(o, n), b), hb), KA.band_r(SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, a)), SL.below(Nat.add(n, PL.nlen(pars)), PL.rename(o, n, pars, b)), hl)))
    case E.QNeg{+a}:
      cneg(~F, O.eval(~F, C.app(~F, y, zmap(~F, p, pars)), PL.rename(o, n, pars, a)), O.eval(~F, C.app(~F, p, y), a), subst(~F, o, n, pars, p, y, a, hp, hy, hb, hl))
