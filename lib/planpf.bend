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
import ../spec/real.bend as CR
import ./fring.bend as FR
import ./ford.bend as FO
import ./fvec.bend as FV
import ./fmat.bend as FM
import ./karith.bend as KA
import ./kball.bend as KB
import ./cert.bend as CK
import ./certpf.bend as CP
import ./real.bend as RL
import ./dmat.bend as DM
import ./banach.bend as BA
import ./plan.bend as PL
import ./meaning.bend as MN
import ./slope.bend as SL
import ./nat.bend as LN

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

# Lists of K
# ----------

def ktake_nil(~K: N.Num, n: Nat) -> {PL.ktake(~K, n, Nil{}) == Nil{} : N.KVec(~K)}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      {==}

def keq_ok.go(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), +b: N.NC(K), c: Cmp, e: {N.ncmp(K, a, b) == c : Cmp}, h: {PL.keq.go(c) == True{} : Bool}) -> {N.emap(K, F, H, a) == N.emap(K, F, H, b) : O.C(F)}:
  match c:
    case LT{}:
      FO.absurd({N.emap(K, F, H, a) == N.emap(K, F, H, b) : O.C(F)}, KA.ft(h))
    case EQ{}:
      KA.kcmp_ok(~K, ~F, ~H, a, b, EQ{}, e)
    case GT{}:
      FO.absurd({N.emap(K, F, H, a) == N.emap(K, F, H, b) : O.C(F)}, KA.ft(h))

# K says a = b, so H a = H b
def keq_ok(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), +b: N.NC(K), h: {PL.keq(~K, a, b) == True{} : Bool}) -> {N.emap(K, F, H, a) == N.emap(K, F, H, b) : O.C(F)}:
  keq_ok.go(~K, ~F, ~H, a, b, N.ncmp(K, a, b), {==}, h)

def klen_ktake(~K: N.Num, n: Nat, u: N.KVec(~K), h: {KA.natle(n, KA.klen(~K, u)) == True{} : Bool}) -> {KA.klen(~K, PL.ktake(~K, n, u)) == n : Nat}:
  match n u:
    case 0n u:
      {==}
    case 1n+k Nil{}:
      FO.absurd({0n == 1n+k : Nat}, KA.ft(h))
    case 1n++k Con{a, t}:
      %Equal.sym(Nat, KA.klen(~K, PL.ktake(~K, k, t)), k, klen_ktake(~K, k, t, h)) : {1n+_ == 1n+k : Nat}
      {==}

def ktake_split(~K: N.Num, o: Nat, +n: Nat, u: N.KVec(~K)) -> {PL.ktake(~K, Nat.add(o, n), u) == KA.kapp(~K, PL.ktake(~K, o, u), PL.ktake(~K, n, PL.kdrop(~K, o, u))) : N.KVec(~K)}:
  match o u:
    case 0n u:
      {==}
    case 1n+k Nil{}:
      Equal.sym(N.KVec(~K), PL.ktake(~K, n, Nil{}), Nil{}, ktake_nil(~K, n))
    case 1n+k Con{+a, +t}:
      %ktake_split(~K, k, n, t) : {Con{a, PL.ktake(~K, Nat.add(k, n), t)} == Con{a, _} : N.KVec(~K)}
      {==}

def ktake_all(~K: N.Num, u: N.KVec(~K)) -> {PL.ktake(~K, KA.klen(~K, u), u) == u : N.KVec(~K)}:
  match u:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      %Equal.sym(N.KVec(~K), PL.ktake(~K, KA.klen(~K, t), t), t, ktake_all(~K, t)) : {Con{a, _} == Con{a, t} : N.KVec(~K)}
      {==}

def klook_ktake(~K: N.Num, o: Nat, u: N.KVec(~K), v: Nat, h: {KA.natle(1n+v, o) == True{} : Bool}) -> {KB.klook(~K, PL.ktake(~K, o, u), v) == KB.klook(~K, u, v) : N.NC(K)}:
  match o u v:
    case 0n u v:
      FO.absurd({KB.klook(~K, Nil{}, v) == KB.klook(~K, u, v) : N.NC(K)}, KA.ft(h))
    case 1n+k Nil{} v:
      {==}
    case 1n+k Con{a, t} 0n:
      {==}
    case 1n+k Con{a, t} 1n+w:
      klook_ktake(~K, k, t, w, h)

# K says two lists agree, so they agree in F
def kveq_ok(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, u: N.KVec(~K), w: N.KVec(~K), +h: {PL.kveq(~K, u, w) == True{} : Bool}) -> {N.ofkv(~K, ~F, ~H, u) == N.ofkv(~K, ~F, ~H, w) : M.Vec(~F)}:
  match u w:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{b, ws}:
      FO.absurd({Nil{} == N.ofkv(~K, ~F, ~H, Con{b, ws}) : M.Vec(~F)}, KA.ft(h))
    case Con{a, us} Nil{}:
      FO.absurd({N.ofkv(~K, ~F, ~H, Con{a, us}) == Nil{} : M.Vec(~F)}, KA.ft(h))
    case Con{+a, +us} Con{+b, +ws}:
      +e1 = keq_ok(~K, ~F, ~H, a, b, KA.band_l(PL.keq(~K, a, b), PL.kveq(~K, us, ws), h))
      %e1 : {Con{N.emap(K, F, H, a), N.ofkv(~K, ~F, ~H, us)} == Con{_, N.ofkv(~K, ~F, ~H, ws)} : M.Vec(~F)}
      %kveq_ok(~K, ~F, ~H, us, ws, KA.band_r(PL.keq(~K, a, b), PL.kveq(~K, us, ws), h)) : {Con{N.emap(K, F, H, a), N.ofkv(~K, ~F, ~H, us)} == Con{N.emap(K, F, H, a), _} : M.Vec(~F)}
      {==}

# Appended vectors
# ----------------

def app_nil(~F: O.OField, p: M.Vec(~F)) -> {C.app(~F, p, Nil{}) == p : M.Vec(~F)}:
  match p:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      %Equal.sym(M.Vec(~F), C.app(~F, t, Nil{}), t, app_nil(~F, t)) : {Con{a, _} == Con{a, t} : M.Vec(~F)}
      {==}

def app_assoc(~F: O.OField, p: M.Vec(~F), +y: M.Vec(~F), +r: M.Vec(~F)) -> {C.app(~F, C.app(~F, p, y), r) == C.app(~F, p, C.app(~F, y, r)) : M.Vec(~F)}:
  match p:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      %app_assoc(~F, t, y, r) : {Con{a, C.app(~F, C.app(~F, t, y), r)} == Con{a, _} : M.Vec(~F)}
      {==}

def len_app(~F: O.OField, p: M.Vec(~F), +y: M.Vec(~F)) -> {M.len(~F, C.app(~F, p, y)) == Nat.add(M.len(~F, p), M.len(~F, y)) : Nat}:
  match p:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      %Equal.sym(Nat, M.len(~F, C.app(~F, t, y)), Nat.add(M.len(~F, t), M.len(~F, y)), len_app(~F, t, y)) : {1n+_ == 1n+Nat.add(M.len(~F, t), M.len(~F, y)) : Nat}
      {==}

# bounds on two pieces bound the appended vector, when the first piece's
# bound is as long as it
def rbnd_app(~F: O.OField, d1: M.Vec(~F), +d2: M.Vec(~F), r1: M.Vec(~F), +r2: M.Vec(~F), h1: C.rbnd(~F, d1, r1), +h2: C.rbnd(~F, d2, r2), hl: {M.len(~F, d1) == M.len(~F, r1) : Nat}) -> C.rbnd(~F, C.app(~F, d1, d2), C.app(~F, r1, r2)):
  match d1 r1:
    case Nil{} Nil{}:
      h2
    case Nil{} Con{+s, +rs}:
      FO.absurd(C.rbnd(~F, d2, Con{s, C.app(~F, rs, r2)}), FV.zero_ne(M.len(~F, rs), hl))
    case Con{+a, +ds} Nil{}:
      FO.absurd(C.rbnd(~F, Con{a, C.app(~F, ds, d2)}, r2), FV.succ_ne(M.len(~F, ds), hl))
    case Con{+a, +ds} Con{+s, +rs}:
      (ha, hs) = h1
      (ha, rbnd_app(~F, ds, d2, rs, r2, hs, h2, FV.succ_inj(M.len(~F, ds), M.len(~F, rs), hl)))

# and back
def rbnd_l(~F: O.OField, d1: M.Vec(~F), +d2: M.Vec(~F), r1: M.Vec(~F), +r2: M.Vec(~F), +h: C.rbnd(~F, C.app(~F, d1, d2), C.app(~F, r1, r2)), hl: {M.len(~F, d1) == M.len(~F, r1) : Nat}) -> C.rbnd(~F, d1, r1):
  match d1 r1:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} Con{+s, +rs}:
      Unit{}
    case Con{+a, +ds} Nil{}:
      FO.absurd(C.rbnd(~F, Con{a, ds}, Nil{}), FV.succ_ne(M.len(~F, ds), hl))
    case Con{+a, +ds} Con{+s, +rs}:
      (ha, hs) = h
      (ha, rbnd_l(~F, ds, d2, rs, r2, hs, FV.succ_inj(M.len(~F, ds), M.len(~F, rs), hl)))

def rbnd_r(~F: O.OField, d1: M.Vec(~F), +d2: M.Vec(~F), r1: M.Vec(~F), +r2: M.Vec(~F), +h: C.rbnd(~F, C.app(~F, d1, d2), C.app(~F, r1, r2)), hl: {M.len(~F, d1) == M.len(~F, r1) : Nat}) -> C.rbnd(~F, d2, r2):
  match d1 r1:
    case Nil{} Nil{}:
      h
    case Nil{} Con{+s, +rs}:
      FO.absurd(C.rbnd(~F, d2, r2), FV.zero_ne(M.len(~F, rs), hl))
    case Con{+a, +ds} Nil{}:
      FO.absurd(C.rbnd(~F, d2, r2), FV.succ_ne(M.len(~F, ds), hl))
    case Con{+a, +ds} Con{+s, +rs}:
      (ha, hs) = h
      rbnd_r(~F, ds, d2, rs, r2, hs, FV.succ_inj(M.len(~F, ds), M.len(~F, rs), hl))

# Equations at appended assignments
# ---------------------------------

# an equation below the length of p reads only p
def eval_prefix(~F: O.OField, +p: M.Vec(~F), +r: M.Vec(~F), e: E.QExpr, +hb: {SL.below(M.len(~F, p), e) == True{} : Bool}) -> {O.eval(~F, C.app(~F, p, r), e) == O.eval(~F, p, e) : O.C(F)}:
  match e:
    case E.QVar{+v}:
      la_l(~F, p, r, v, hb)
    case E.QCst{q}:
      {==}
    case E.QAdd{+a, +b}:
      cadd(~F, O.eval(~F, C.app(~F, p, r), a), O.eval(~F, p, a), O.eval(~F, C.app(~F, p, r), b), O.eval(~F, p, b), eval_prefix(~F, p, r, a, KA.band_l(SL.below(M.len(~F, p), a), SL.below(M.len(~F, p), b), hb)), eval_prefix(~F, p, r, b, KA.band_r(SL.below(M.len(~F, p), a), SL.below(M.len(~F, p), b), hb)))
    case E.QSub{+a, +b}:
      csub(~F, O.eval(~F, C.app(~F, p, r), a), O.eval(~F, p, a), O.eval(~F, C.app(~F, p, r), b), O.eval(~F, p, b), eval_prefix(~F, p, r, a, KA.band_l(SL.below(M.len(~F, p), a), SL.below(M.len(~F, p), b), hb)), eval_prefix(~F, p, r, b, KA.band_r(SL.below(M.len(~F, p), a), SL.below(M.len(~F, p), b), hb)))
    case E.QMul{+a, +b}:
      cmul(~F, O.eval(~F, C.app(~F, p, r), a), O.eval(~F, p, a), O.eval(~F, C.app(~F, p, r), b), O.eval(~F, p, b), eval_prefix(~F, p, r, a, KA.band_l(SL.below(M.len(~F, p), a), SL.below(M.len(~F, p), b), hb)), eval_prefix(~F, p, r, b, KA.band_r(SL.below(M.len(~F, p), a), SL.below(M.len(~F, p), b), hb)))
    case E.QNeg{+a}:
      cneg(~F, O.eval(~F, C.app(~F, p, r), a), O.eval(~F, p, a), eval_prefix(~F, p, r, a, hb))

def zero_rw(~F: O.OField, +a: O.C(F), +b: O.C(F), e: {a == b : O.C(F)}, h: {b == O.zero(F) : O.C(F)}) -> {a == O.zero(F) : O.C(F)}:
  Equal.trans(O.C(F), a, b, O.zero(F), e, h)

def zeros_prefix(~F: O.OField, +p: M.Vec(~F), +r: M.Vec(~F), es: List<&2, E.QExpr>, +hb: {PL.eqs_below(M.len(~F, p), es) == True{} : Bool}, h: SK.Zeros(~F, p, es)) -> SK.Zeros(~F, C.app(~F, p, r), es):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      (h0, ht) = h
      (zero_rw(~F, O.eval(~F, C.app(~F, p, r), e), O.eval(~F, p, e), eval_prefix(~F, p, r, e, KA.band_l(SL.below(M.len(~F, p), e), PL.eqs_below(M.len(~F, p), t), hb)), h0), zeros_prefix(~F, p, r, t, KA.band_r(SL.below(M.len(~F, p), e), PL.eqs_below(M.len(~F, p), t), hb), ht))

def zeros_unprefix(~F: O.OField, +p: M.Vec(~F), +r: M.Vec(~F), es: List<&2, E.QExpr>, +hb: {PL.eqs_below(M.len(~F, p), es) == True{} : Bool}, h: SK.Zeros(~F, C.app(~F, p, r), es)) -> SK.Zeros(~F, p, es):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      (h0, ht) = h
      (zero_rw(~F, O.eval(~F, p, e), O.eval(~F, C.app(~F, p, r), e), Equal.sym(O.C(F), O.eval(~F, C.app(~F, p, r), e), O.eval(~F, p, e), eval_prefix(~F, p, r, e, KA.band_l(SL.below(M.len(~F, p), e), PL.eqs_below(M.len(~F, p), t), hb))), h0), zeros_unprefix(~F, p, r, t, KA.band_r(SL.below(M.len(~F, p), e), PL.eqs_below(M.len(~F, p), t), hb), ht))

def zeros_split(~F: O.OField, +x: M.Vec(~F), n: Nat, es: List<&2, E.QExpr>, h1: SK.Zeros(~F, x, PL.takeq(n, es)), h2: SK.Zeros(~F, x, PL.dropq(n, es))) -> SK.Zeros(~F, x, es):
  match n es:
    case 0n es:
      h2
    case 1n+k Nil{}:
      Unit{}
    case 1n+k Con{+e, +t}:
      (h0, ht) = h1
      (h0, zeros_split(~F, x, k, t, ht, h2))

def zeros_take(~F: O.OField, +x: M.Vec(~F), n: Nat, es: List<&2, E.QExpr>, +h: SK.Zeros(~F, x, es)) -> SK.Zeros(~F, x, PL.takeq(n, es)):
  match n es:
    case 0n es:
      Unit{}
    case 1n+k Nil{}:
      Unit{}
    case 1n+k Con{+e, +t}:
      (h0, ht) = h
      (h0, zeros_take(~F, x, k, t, ht))

def zeros_drop(~F: O.OField, +x: M.Vec(~F), n: Nat, es: List<&2, E.QExpr>, +h: SK.Zeros(~F, x, es)) -> SK.Zeros(~F, x, PL.dropq(n, es)):
  match n es:
    case 0n es:
      h
    case 1n+k Nil{}:
      Unit{}
    case 1n+k Con{+e, +t}:
      (h0, ht) = h
      zeros_drop(~F, x, k, t, ht)

# A block's zeros, locally and globally
# -------------------------------------

# |0| ≤ 0, for a = 0
def bnd_of_zero(~F: O.OField, +a: O.C(F), h: {a == O.zero(F) : O.C(F)}) -> M.bnd(~F, a, O.zero(F)):
  %Equal.sym(O.C(F), a, O.zero(F), h) : M.bnd(~F, _, O.zero(F))
  FM.bnd_zero(~F, O.zero(F), FO.le_refl(~F, O.zero(F)))

def zeros_of_vall(~F: O.OField, +env: M.Vec(~F), es: List<&2, E.QExpr>, h: M.vbnd.all(~F, C.fvals(~F, es, env), O.zero(F))) -> SK.Zeros(~F, env, es):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      (h0, ht) = h
      (RL.bnd0_eq(~F, O.eval(~F, env, e), h0), zeros_of_vall(~F, env, t, ht))

def vall_of_zeros(~F: O.OField, +env: M.Vec(~F), es: List<&2, E.QExpr>, h: SK.Zeros(~F, env, es)) -> M.vbnd.all(~F, C.fvals(~F, es, env), O.zero(F)):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      (h0, ht) = h
      (bnd_of_zero(~F, O.eval(~F, env, e), h0), vall_of_zeros(~F, env, t, ht))

def zeros_subst(~F: O.OField, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +p: M.Vec(~F), +y: M.Vec(~F), es: List<&2, E.QExpr>, +hp: {M.len(~F, p) == o : Nat}, +hy: {M.len(~F, y) == n : Nat}, +hb: {PL.eqs_below(Nat.add(o, n), es) == True{} : Bool}, +hl: {CK.allbelow(Nat.add(n, PL.nlen(pars)), PL.renames(o, n, pars, es)) == True{} : Bool}, h: SK.Zeros(~F, C.app(~F, y, zmap(~F, p, pars)), PL.renames(o, n, pars, es))) -> SK.Zeros(~F, C.app(~F, p, y), es):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      (h0, ht) = h
      +m1 = Nat.add(o, n)
      +m2 = Nat.add(n, PL.nlen(pars))
      +sb = subst(~F, o, n, pars, p, y, e, hp, hy, KA.band_l(SL.below(m1, e), PL.eqs_below(m1, t), hb), KA.band_l(SL.below(m2, PL.rename(o, n, pars, e)), CK.allbelow(m2, PL.renames(o, n, pars, t)), hl))
      (zero_rw(~F, O.eval(~F, C.app(~F, p, y), e), O.eval(~F, C.app(~F, y, zmap(~F, p, pars)), PL.rename(o, n, pars, e)), Equal.sym(O.C(F), O.eval(~F, C.app(~F, y, zmap(~F, p, pars)), PL.rename(o, n, pars, e)), O.eval(~F, C.app(~F, p, y), e), sb), h0), zeros_subst(~F, o, n, pars, p, y, t, hp, hy, KA.band_r(SL.below(m1, e), PL.eqs_below(m1, t), hb), KA.band_r(SL.below(m2, PL.rename(o, n, pars, e)), CK.allbelow(m2, PL.renames(o, n, pars, t)), hl), ht))

def zeros_unsubst(~F: O.OField, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +p: M.Vec(~F), +y: M.Vec(~F), es: List<&2, E.QExpr>, +hp: {M.len(~F, p) == o : Nat}, +hy: {M.len(~F, y) == n : Nat}, +hb: {PL.eqs_below(Nat.add(o, n), es) == True{} : Bool}, +hl: {CK.allbelow(Nat.add(n, PL.nlen(pars)), PL.renames(o, n, pars, es)) == True{} : Bool}, h: SK.Zeros(~F, C.app(~F, p, y), es)) -> SK.Zeros(~F, C.app(~F, y, zmap(~F, p, pars)), PL.renames(o, n, pars, es)):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      (h0, ht) = h
      +m1 = Nat.add(o, n)
      +m2 = Nat.add(n, PL.nlen(pars))
      +sb = subst(~F, o, n, pars, p, y, e, hp, hy, KA.band_l(SL.below(m1, e), PL.eqs_below(m1, t), hb), KA.band_l(SL.below(m2, PL.rename(o, n, pars, e)), CK.allbelow(m2, PL.renames(o, n, pars, t)), hl))
      (zero_rw(~F, O.eval(~F, C.app(~F, y, zmap(~F, p, pars)), PL.rename(o, n, pars, e)), O.eval(~F, C.app(~F, p, y), e), sb, h0), zeros_unsubst(~F, o, n, pars, p, y, t, hp, hy, KA.band_r(SL.below(m1, e), PL.eqs_below(m1, t), hb), KA.band_r(SL.below(m2, PL.rename(o, n, pars, e)), CK.allbelow(m2, PL.renames(o, n, pars, t)), hl), ht))

# The box, a prefix at a time
# ---------------------------

# p is the first o coordinates of a point of the box
def pbox(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +o: Nat, +p: M.Vec(~F)) -> Data:
  M.Both({M.len(~F, p) == o : Nat}, C.rbnd(~F, C.vsub(~F, p, N.ofkv(~K, ~F, ~H, PL.ktake(~K, o, gc))), N.ofkv(~K, ~F, ~H, PL.ktake(~K, o, gr))))

def natle_pred(a: Nat, +m: Nat, h: {KA.natle(1n+a, m) == True{} : Bool}) -> {KA.natle(a, m) == True{} : Bool}:
  match a m:
    case 0n m:
      {==}
    case 1n+k 0n:
      FO.absurd({KA.natle(1n+k, 0n) == True{} : Bool}, KA.ft(h))
    case 1n+k 1n+j:
      natle_pred(k, j, h)

def natle_rw2(+a: Nat, +a2: Nat, +m: Nat, e: {a == a2 : Nat}, h: {KA.natle(a, m) == True{} : Bool}) -> {KA.natle(a2, m) == True{} : Bool}:
  %e : {KA.natle(_, m) == True{} : Bool}
  h

def emap_rw(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: N.NC(K), +b: N.NC(K), e: {a == b : N.NC(K)}) -> {N.emap(K, F, H, a) == N.emap(K, F, H, b) : O.C(F)}:
  %e : {N.emap(K, F, H, a) == N.emap(K, F, H, _) : O.C(F)}
  {==}

def natle_addl(+o: Nat, n: Nat, +m: Nat, h: {KA.natle(Nat.add(o, n), m) == True{} : Bool}) -> {KA.natle(o, m) == True{} : Bool}:
  match n:
    case 0n:
      %Equal.sym(Nat, o, Nat.add(o, 0n), LN.add_zero(o)) : {KA.natle(_, m) == True{} : Bool}
      h
    case 1n++k:
      natle_addl(o, k, m, natle_pred(Nat.add(o, k), m, natle_rw2(Nat.add(o, 1n+k), 1n+Nat.add(o, k), m, Equal.sym(Nat, 1n+Nat.add(o, k), Nat.add(o, 1n+k), LN.add_succ(o, k)), h)))

def len_kt(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +o: Nat, +u: N.KVec(~K), h: {KA.natle(o, KA.klen(~K, u)) == True{} : Bool}) -> {M.len(~F, N.ofkv(~K, ~F, ~H, PL.ktake(~K, o, u))) == o : Nat}:
  Equal.trans(Nat, M.len(~F, N.ofkv(~K, ~F, ~H, PL.ktake(~K, o, u))), KA.klen(~K, PL.ktake(~K, o, u)), o, CP.len_ofkv(~K, ~F, ~H, PL.ktake(~K, o, u)), klen_ktake(~K, o, u, h))

# one coordinate of the prefix lies in its interval
def pbox_at(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +o: Nat, +p: M.Vec(~F), h: pbox(~K, ~F, ~H, gc, gr, o, p), +hgc: {KA.natle(o, KA.klen(~K, gc)) == True{} : Bool}, +v: Nat, +hv: {KA.natle(1n+v, o) == True{} : Bool}) -> M.bnd(~F, O.sub(~F, O.lookup(~F, p, v), N.emap(K, F, H, KB.klook(~K, gc, v))), N.emap(K, F, H, KB.klook(~K, gr, v))):
  (hl, hr) = h
  +ca = N.ofkv(~K, ~F, ~H, PL.ktake(~K, o, gc))
  +ra = N.ofkv(~K, ~F, ~H, PL.ktake(~K, o, gr))
  +b0 = BA.rbnd_look(~F, C.vsub(~F, p, ca), ra, hr, o, CP.len_vsub(~F, p, ca, o, hl, len_kt(~K, ~F, ~H, o, gc, hgc)), v, hv)
  +ec = Equal.trans(O.C(F), O.lookup(~F, ca, v), N.emap(K, F, H, KB.klook(~K, PL.ktake(~K, o, gc), v)), N.emap(K, F, H, KB.klook(~K, gc, v)), Equal.sym(O.C(F), N.emap(K, F, H, KB.klook(~K, PL.ktake(~K, o, gc), v)), O.lookup(~F, ca, v), CP.klook_ofk(~K, ~F, ~H, PL.ktake(~K, o, gc), v)), emap_rw(~K, ~F, ~H, KB.klook(~K, PL.ktake(~K, o, gc), v), KB.klook(~K, gc, v), klook_ktake(~K, o, gc, v, hv)))
  +er = Equal.trans(O.C(F), O.lookup(~F, ra, v), N.emap(K, F, H, KB.klook(~K, PL.ktake(~K, o, gr), v)), N.emap(K, F, H, KB.klook(~K, gr, v)), Equal.sym(O.C(F), N.emap(K, F, H, KB.klook(~K, PL.ktake(~K, o, gr), v)), O.lookup(~F, ra, v), CP.klook_ofk(~K, ~F, ~H, PL.ktake(~K, o, gr), v)), emap_rw(~K, ~F, ~H, KB.klook(~K, PL.ktake(~K, o, gr), v), KB.klook(~K, gr, v), klook_ktake(~K, o, gr, v, hv)))
  BA.bnd_rw_s(~F, O.sub(~F, O.lookup(~F, p, v), N.emap(K, F, H, KB.klook(~K, gc, v))), O.lookup(~F, ra, v), N.emap(K, F, H, KB.klook(~K, gr, v)), er,
    FV.bval(~F, O.lookup(~F, C.vsub(~F, p, ca), v), O.sub(~F, O.lookup(~F, p, v), N.emap(K, F, H, KB.klook(~K, gc, v))), O.lookup(~F, ra, v), Equal.trans(O.C(F), O.lookup(~F, C.vsub(~F, p, ca), v), O.sub(~F, O.lookup(~F, p, v), O.lookup(~F, ca, v)), O.sub(~F, O.lookup(~F, p, v), N.emap(K, F, H, KB.klook(~K, gc, v))), Equal.sym(O.C(F), O.sub(~F, O.lookup(~F, p, v), O.lookup(~F, ca, v)), O.lookup(~F, C.vsub(~F, p, ca), v), SL.lookup_vsub(~F, p, ca, v)), BA.sub_r(~F, O.lookup(~F, p, v), O.lookup(~F, ca, v), N.emap(K, F, H, KB.klook(~K, gc, v)), ec)), b0))

# The parameters are pinned
# -------------------------

def pcont_len(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), pars: List<&2, Nat>, pc: N.KVec(~K), pr: N.KVec(~K), +h: {PL.pcont(~K, gc, gr, pars, pc, pr) == True{} : Bool}) -> {KA.klen(~K, pc) == PL.nlen(pars) : Nat}:
  match pars pc pr:
    case Nil{} Nil{} Nil{}:
      {==}
    case Nil{} Nil{} Con{r, rs}:
      FO.absurd({0n == 0n : Nat}, KA.ft(h))
    case Nil{} Con{c, cs} pr:
      FO.absurd({KA.klen(~K, Con{c, cs}) == 0n : Nat}, KA.ft(h))
    case Con{v, vs} Nil{} pr:
      FO.absurd({0n == PL.nlen(Con{v, vs}) : Nat}, KA.ft(h))
    case Con{+v, +vs} Con{+c, +cs} Nil{}:
      FO.absurd({KA.klen(~K, Con{c, cs}) == PL.nlen(Con{v, vs}) : Nat}, KA.ft(h))
    case Con{+v, +vs} Con{+c, +cs} Con{+r, +rs}:
      %Equal.sym(Nat, KA.klen(~K, cs), PL.nlen(vs), pcont_len(~K, gc, gr, vs, cs, rs, KA.band_r(KA.kle(~K, N.nadd(K, KA.kabs(~K, KA.ksub(~K, KB.klook(~K, gc, v), c)), KB.klook(~K, gr, v)), r), PL.pcont(~K, gc, gr, vs, cs, rs), h))) : {1n+_ == 1n+PL.nlen(vs) : Nat}
      {==}

# |x - c| <= r from |x - g| <= s and K's |g - c| + s <= r
def pin1(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x: O.C(F), +g: N.NC(K), +s: N.NC(K), +c: N.NC(K), +r: N.NC(K), hx: M.bnd(~F, O.sub(~F, x, N.emap(K, F, H, g)), N.emap(K, F, H, s)), hk: {KA.kle(~K, N.nadd(K, KA.kabs(~K, KA.ksub(~K, g, c)), s), r) == True{} : Bool}) -> M.bnd(~F, O.sub(~F, x, N.emap(K, F, H, c)), N.emap(K, F, H, r)):
  +hg = N.emap(K, F, H, g)
  +hc = N.emap(K, F, H, c)
  +hs = N.emap(K, F, H, s)
  +ha = N.emap(K, F, H, KA.kabs(~K, KA.ksub(~K, g, c)))
  +hb = BA.bnd_rw_s(~F, O.sub(~F, hg, hc), N.emap(K, F, H, KA.kabs(~K, KA.ksub(~K, g, c))), ha, {==}, FV.bval(~F, N.emap(K, F, H, KA.ksub(~K, g, c)), O.sub(~F, hg, hc), ha, Equal.sym(O.C(F), O.sub(~F, hg, hc), N.emap(K, F, H, KA.ksub(~K, g, c)), KA.es(~K, ~F, ~H, g, c)), KA.kabs_bnd(~K, ~F, ~H, KA.ksub(~K, g, c))))
  +sum = FM.bnd_add(~F, O.sub(~F, x, hg), hs, O.sub(~F, hg, hc), ha, hx, hb)
  +v2 = FV.bval(~F, O.add(F, O.sub(~F, x, hg), O.sub(~F, hg, hc)), O.sub(~F, x, hc), O.add(F, hs, ha), FR.fring_eq(~F, [x, hg, hc], E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZVar{1n}, E.ZVar{2n}}}, E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, {==}), sum)
  +hle = RL.le_rw_l(~F, N.emap(K, F, H, N.nadd(K, KA.kabs(~K, KA.ksub(~K, g, c)), s)), O.add(F, hs, ha), N.emap(K, F, H, r), Equal.trans(O.C(F), N.emap(K, F, H, N.nadd(K, KA.kabs(~K, KA.ksub(~K, g, c)), s)), O.add(F, ha, hs), O.add(F, hs, ha), Equal.sym(O.C(F), O.add(F, ha, hs), N.emap(K, F, H, N.nadd(K, KA.kabs(~K, KA.ksub(~K, g, c)), s)), KA.ea(~K, ~F, ~H, KA.kabs(~K, KA.ksub(~K, g, c)), s)), O.add_comm(F)(ha, hs)), KA.kle_ok(~K, ~F, ~H, N.nadd(K, KA.kabs(~K, KA.ksub(~K, g, c)), s), r, hk))
  FM.bnd_mono(~F, O.sub(~F, x, hc), O.add(F, hs, ha), N.emap(K, F, H, r), v2, FM.sub_nonneg(~F, O.add(F, hs, ha), N.emap(K, F, H, r), hle))

# the parameters' values lie in the certificate's parameter box
def pin_pc(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +o: Nat, +p: M.Vec(~F), +hpb: pbox(~K, ~F, ~H, gc, gr, o, p), +hgc: {KA.natle(o, KA.klen(~K, gc)) == True{} : Bool}, pars: List<&2, Nat>, pc: N.KVec(~K), pr: N.KVec(~K), +hpo: {PL.pars_ok(o, pars) == True{} : Bool}, +hc: {PL.pcont(~K, gc, gr, pars, pc, pr) == True{} : Bool}) -> C.rbnd(~F, C.vsub(~F, zmap(~F, p, pars), N.ofkv(~K, ~F, ~H, pc)), N.ofkv(~K, ~F, ~H, pr)):
  match pars pc pr:
    case Nil{} Nil{} Nil{}:
      Unit{}
    case Nil{} Nil{} Con{r, rs}:
      Unit{}
    case Nil{} Con{+c, +cs} pr:
      FO.absurd(C.rbnd(~F, C.vsub(~F, Nil{}, N.ofkv(~K, ~F, ~H, Con{c, cs})), N.ofkv(~K, ~F, ~H, pr)), KA.ft(hc))
    case Con{+v, +vs} Nil{} pr:
      FO.absurd(C.rbnd(~F, C.vsub(~F, zmap(~F, p, Con{v, vs}), Nil{}), N.ofkv(~K, ~F, ~H, pr)), KA.ft(hc))
    case Con{+v, +vs} Con{+c, +cs} Nil{}:
      FO.absurd(C.rbnd(~F, C.vsub(~F, zmap(~F, p, Con{v, vs}), N.ofkv(~K, ~F, ~H, Con{c, cs})), Nil{}), KA.ft(hc))
    case Con{+v, +vs} Con{+c, +cs} Con{+r, +rs}:
      +hk = KA.kle(~K, N.nadd(K, KA.kabs(~K, KA.ksub(~K, KB.klook(~K, gc, v), c)), KB.klook(~K, gr, v)), r)
      (pin1(~K, ~F, ~H, O.lookup(~F, p, v), KB.klook(~K, gc, v), KB.klook(~K, gr, v), c, r, pbox_at(~K, ~F, ~H, gc, gr, o, p, hpb, hgc, v, KA.band_l(KA.natle(1n+v, o), PL.pars_ok(o, vs), hpo)), KA.band_l(hk, PL.pcont(~K, gc, gr, vs, cs, rs), hc)),
       pin_pc(~K, ~F, ~H, gc, gr, o, p, hpb, hgc, vs, cs, rs, KA.band_r(KA.natle(1n+v, o), PL.pars_ok(o, vs), hpo), KA.band_r(hk, PL.pcont(~K, gc, gr, vs, cs, rs), hc)))

# A block's ball is a stretch of the box
# --------------------------------------

def rbnd_rwd(~F: O.OField, +d: M.Vec(~F), +d2: M.Vec(~F), +r: M.Vec(~F), e: {d == d2 : M.Vec(~F)}, h: C.rbnd(~F, d, r)) -> C.rbnd(~F, d2, r):
  %e : C.rbnd(~F, _, r)
  h

def vsub_rw(~F: O.OField, +y: M.Vec(~F), +c: M.Vec(~F), +c2: M.Vec(~F), e: {c == c2 : M.Vec(~F)}) -> {C.vsub(~F, y, c) == C.vsub(~F, y, c2) : M.Vec(~F)}:
  %e : {C.vsub(~F, y, c) == C.vsub(~F, y, _) : M.Vec(~F)}
  {==}

def seg_of_ball(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +o: Nat, +n: Nat, +c: C.Cert<K>, +y: M.Vec(~F), hb: C.ball(~K, ~F, ~H, c, y), +hy: {M.len(~F, y) == n : Nat}, hyc: {PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))) == True{} : Bool}, hyr: {PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))) == True{} : Bool}) -> C.rbnd(~F, C.vsub(~F, y, N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gc)))), N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gr)))):
  (hl, hr) = hb
  +cen = C.center(~K, ~F, ~H, c)
  +h1 = CP.rbnd_kfit(~K, ~F, ~H, n, C.vsub(~F, y, cen), C.Cert.yr(K, c), hr, CP.len_vsub(~F, y, cen, n, hy, Equal.trans(Nat, M.len(~F, cen), M.len(~F, y), n, Equal.sym(Nat, M.len(~F, y), M.len(~F, cen), hl), hy)))
  +h2 = FV.rbnd_rw2(~F, C.vsub(~F, y, cen), N.ofkv(~K, ~F, ~H, KA.kfit(~K, n, C.Cert.yr(K, c))), N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gr))), kveq_ok(~K, ~F, ~H, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr)), hyr), h1)
  rbnd_rwd(~F, C.vsub(~F, y, cen), C.vsub(~F, y, N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gc)))), N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gr))), vsub_rw(~F, y, cen, N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gc))), kveq_ok(~K, ~F, ~H, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc)), hyc)), h2)

def ofkv_rw(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +u: N.KVec(~K), +u2: N.KVec(~K), e: {u == u2 : N.KVec(~K)}) -> {N.ofkv(~K, ~F, ~H, u) == N.ofkv(~K, ~F, ~H, u2) : M.Vec(~F)}:
  %e : {N.ofkv(~K, ~F, ~H, u) == N.ofkv(~K, ~F, ~H, _) : M.Vec(~F)}
  {==}

def add2(+a: Nat, +a2: Nat, +b: Nat, +b2: Nat, ea: {a == a2 : Nat}, eb: {b == b2 : Nat}) -> {Nat.add(a, b) == Nat.add(a2, b2) : Nat}:
  %ea : {Nat.add(a, b) == Nat.add(_, b2) : Nat}
  %eb : {Nat.add(a, b) == Nat.add(a, _) : Nat}
  {==}

# the prefix grows by the block's unknowns
def pbox_ext(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +o: Nat, +n: Nat, +p: M.Vec(~F), +y: M.Vec(~F), hpb: pbox(~K, ~F, ~H, gc, gr, o, p), +hseg: C.rbnd(~F, C.vsub(~F, y, N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gc)))), N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gr)))), +hy: {M.len(~F, y) == n : Nat}, +hgc: {KA.natle(o, KA.klen(~K, gc)) == True{} : Bool}, +hgr: {KA.klen(~K, gr) == KA.klen(~K, gc) : Nat}) -> pbox(~K, ~F, ~H, gc, gr, Nat.add(o, n), C.app(~F, p, y)):
  (+hl, hr) = hpb
  +ca = N.ofkv(~K, ~F, ~H, PL.ktake(~K, o, gc))
  +cb = N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gc)))
  +ra = N.ofkv(~K, ~F, ~H, PL.ktake(~K, o, gr))
  +rb = N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gr)))
  +hla = len_kt(~K, ~F, ~H, o, gc, hgc)
  +hlr = len_kt(~K, ~F, ~H, o, gr, natle_rw(o, KA.klen(~K, gc), KA.klen(~K, gr), Equal.sym(Nat, KA.klen(~K, gr), KA.klen(~K, gc), hgr), hgc))
  +ec = Equal.trans(M.Vec(~F), N.ofkv(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gc)), N.ofkv(~K, ~F, ~H, KA.kapp(~K, PL.ktake(~K, o, gc), PL.ktake(~K, n, PL.kdrop(~K, o, gc)))), C.app(~F, ca, cb), ofkv_rw(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gc), KA.kapp(~K, PL.ktake(~K, o, gc), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), ktake_split(~K, o, n, gc)), CP.kapp_ofk(~K, ~F, ~H, PL.ktake(~K, o, gc), PL.ktake(~K, n, PL.kdrop(~K, o, gc))))
  +er = Equal.trans(M.Vec(~F), N.ofkv(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gr)), N.ofkv(~K, ~F, ~H, KA.kapp(~K, PL.ktake(~K, o, gr), PL.ktake(~K, n, PL.kdrop(~K, o, gr)))), C.app(~F, ra, rb), ofkv_rw(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gr), KA.kapp(~K, PL.ktake(~K, o, gr), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), ktake_split(~K, o, n, gr)), CP.kapp_ofk(~K, ~F, ~H, PL.ktake(~K, o, gr), PL.ktake(~K, n, PL.kdrop(~K, o, gr))))
  +joined = rbnd_app(~F, C.vsub(~F, p, ca), C.vsub(~F, y, cb), ra, rb, hr, hseg, Equal.trans(Nat, M.len(~F, C.vsub(~F, p, ca)), o, M.len(~F, ra), CP.len_vsub(~F, p, ca, o, hl, hla), Equal.sym(Nat, M.len(~F, ra), o, hlr)))
  +ed = Equal.trans(M.Vec(~F), C.app(~F, C.vsub(~F, p, ca), C.vsub(~F, y, cb)), C.vsub(~F, C.app(~F, p, y), C.app(~F, ca, cb)), C.vsub(~F, C.app(~F, p, y), N.ofkv(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gc))), Equal.sym(M.Vec(~F), C.vsub(~F, C.app(~F, p, y), C.app(~F, ca, cb)), C.app(~F, C.vsub(~F, p, ca), C.vsub(~F, y, cb)), FV.vsub_app(~F, p, ca, y, cb, Equal.trans(Nat, M.len(~F, p), o, M.len(~F, ca), hl, Equal.sym(Nat, M.len(~F, ca), o, hla)))), vsub_rw(~F, C.app(~F, p, y), C.app(~F, ca, cb), N.ofkv(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gc)), Equal.sym(M.Vec(~F), N.ofkv(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gc)), C.app(~F, ca, cb), ec)))
  (Equal.trans(Nat, M.len(~F, C.app(~F, p, y)), Nat.add(M.len(~F, p), M.len(~F, y)), Nat.add(o, n), len_app(~F, p, y), add2(M.len(~F, p), o, M.len(~F, y), n, hl, hy)),
   FV.rbnd_rw2(~F, C.vsub(~F, C.app(~F, p, y), N.ofkv(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gc))), C.app(~F, ra, rb), N.ofkv(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gr)), Equal.sym(M.Vec(~F), N.ofkv(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gr)), C.app(~F, ra, rb), er), rbnd_rwd(~F, C.app(~F, C.vsub(~F, p, ca), C.vsub(~F, y, cb)), C.vsub(~F, C.app(~F, p, y), N.ofkv(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gc))), C.app(~F, ra, rb), ed, joined)))

# The checker's facts about a block
# ----------------------------------

def bo_r0(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +h: {PL.block_ok(~K, gc, gr, es, o, n, pars, c) == True{} : Bool}) -> {KA.band(KA.natle(n, CK.eqlen(es)), KA.band(KA.natle(Nat.add(o, n), KA.klen(~K, gc)), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~K, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, c), KA.band(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))))))) == True{} : Bool}:
  h

def bo_r1(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +h: {PL.block_ok(~K, gc, gr, es, o, n, pars, c) == True{} : Bool}) -> {KA.band(KA.natle(Nat.add(o, n), KA.klen(~K, gc)), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~K, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, c), KA.band(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c)))))))) == True{} : Bool}:
  KA.band_r(KA.natle(n, CK.eqlen(es)), KA.band(KA.natle(Nat.add(o, n), KA.klen(~K, gc)), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~K, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, c), KA.band(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c)))))))), bo_r0(~K, gc, gr, es, o, n, pars, c, h))

def bo_r2(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +h: {PL.block_ok(~K, gc, gr, es, o, n, pars, c) == True{} : Bool}) -> {KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~K, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, c), KA.band(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))))) == True{} : Bool}:
  KA.band_r(KA.natle(Nat.add(o, n), KA.klen(~K, gc)), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~K, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, c), KA.band(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))))), bo_r1(~K, gc, gr, es, o, n, pars, c, h))

def bo_r3(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +h: {PL.block_ok(~K, gc, gr, es, o, n, pars, c) == True{} : Bool}) -> {KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~K, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, c), KA.band(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c)))))) == True{} : Bool}:
  KA.band_r(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~K, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, c), KA.band(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c)))))), bo_r2(~K, gc, gr, es, o, n, pars, c, h))

def bo_r4(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +h: {PL.block_ok(~K, gc, gr, es, o, n, pars, c) == True{} : Bool}) -> {KA.band(CK.check(~K, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, c), KA.band(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))) == True{} : Bool}:
  KA.band_r(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~K, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, c), KA.band(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))), bo_r3(~K, gc, gr, es, o, n, pars, c, h))

def bo_r5(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +h: {PL.block_ok(~K, gc, gr, es, o, n, pars, c) == True{} : Bool}) -> {KA.band(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c)))) == True{} : Bool}:
  KA.band_r(CK.check(~K, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, c), KA.band(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c)))), bo_r4(~K, gc, gr, es, o, n, pars, c, h))

def bo_r6(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +h: {PL.block_ok(~K, gc, gr, es, o, n, pars, c) == True{} : Bool}) -> {KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))) == True{} : Bool}:
  KA.band_r(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))), bo_r5(~K, gc, gr, es, o, n, pars, c, h))

def bo_r7(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +h: {PL.block_ok(~K, gc, gr, es, o, n, pars, c) == True{} : Bool}) -> {PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c)) == True{} : Bool}:
  KA.band_r(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c)), bo_r6(~K, gc, gr, es, o, n, pars, c, h))

def bo_n_eqs(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +h: {PL.block_ok(~K, gc, gr, es, o, n, pars, c) == True{} : Bool}) -> {KA.natle(n, CK.eqlen(es)) == True{} : Bool}:
  KA.band_l(KA.natle(n, CK.eqlen(es)), KA.band(KA.natle(Nat.add(o, n), KA.klen(~K, gc)), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~K, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, c), KA.band(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c)))))))), bo_r0(~K, gc, gr, es, o, n, pars, c, h))

def bo_in_box(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +h: {PL.block_ok(~K, gc, gr, es, o, n, pars, c) == True{} : Bool}) -> {KA.natle(Nat.add(o, n), KA.klen(~K, gc)) == True{} : Bool}:
  KA.band_l(KA.natle(Nat.add(o, n), KA.klen(~K, gc)), KA.band(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~K, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, c), KA.band(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))))), bo_r1(~K, gc, gr, es, o, n, pars, c, h))

def bo_pars(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +h: {PL.block_ok(~K, gc, gr, es, o, n, pars, c) == True{} : Bool}) -> {PL.pars_ok(o, pars) == True{} : Bool}:
  KA.band_l(PL.pars_ok(o, pars), KA.band(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~K, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, c), KA.band(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c)))))), bo_r2(~K, gc, gr, es, o, n, pars, c, h))

def bo_below(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +h: {PL.block_ok(~K, gc, gr, es, o, n, pars, c) == True{} : Bool}) -> {PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)) == True{} : Bool}:
  KA.band_l(PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)), KA.band(CK.check(~K, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, c), KA.band(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))), bo_r3(~K, gc, gr, es, o, n, pars, c, h))

def bo_cert(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +h: {PL.block_ok(~K, gc, gr, es, o, n, pars, c) == True{} : Bool}) -> {CK.check(~K, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, c) == True{} : Bool}:
  KA.band_l(CK.check(~K, C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}, c), KA.band(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c)))), bo_r4(~K, gc, gr, es, o, n, pars, c, h))

def bo_yc(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +h: {PL.block_ok(~K, gc, gr, es, o, n, pars, c) == True{} : Bool}) -> {PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))) == True{} : Bool}:
  KA.band_l(PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), KA.band(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))), bo_r5(~K, gc, gr, es, o, n, pars, c, h))

def bo_yr(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +h: {PL.block_ok(~K, gc, gr, es, o, n, pars, c) == True{} : Bool}) -> {PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))) == True{} : Bool}:
  KA.band_l(PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c)), bo_r6(~K, gc, gr, es, o, n, pars, c, h))

def bo_pcont(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +h: {PL.block_ok(~K, gc, gr, es, o, n, pars, c) == True{} : Bool}) -> {PL.pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c)) == True{} : Bool}:
  bo_r7(~K, gc, gr, es, o, n, pars, c, h)

# a checked certificate has n centers, and its local equations read only
# its unknowns and parameters
def cert_lyc.go(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +ok: {CK.check.go(~K, eqs, n, yc, yr, q, ym, pc, pr) == True{} : Bool}) -> {KA.klen(~K, yc) == n : Nat}:
  CP.nateq_ok(KA.klen(~K, yc), n, CP.x_len_yc(~K, eqs, n, yc, yr, q, ym, pc, pr, ok))

def cert_lyc(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, c: C.Cert<K>, ok: {CK.check(~K, C.Block{eqs, n}, c) == True{} : Bool}) -> {KA.klen(~K, C.Cert.yc(K, c)) == n : Nat}:
  match c:
    case C.Cert{+yc, +yr, +q, +ym, +pc, +pr}:
      cert_lyc.go(~K, eqs, n, yc, yr, q, ym, pc, pr, ok)

def cert_bel(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, c: C.Cert<K>, ok: {CK.check(~K, C.Block{eqs, n}, c) == True{} : Bool}) -> {CK.allbelow(Nat.add(n, KA.klen(~K, C.Cert.pc(K, c))), eqs) == True{} : Bool}:
  match c:
    case C.Cert{+yc, +yr, +q, +ym, +pc, +pr}:
      CP.x_below(~K, eqs, n, yc, yr, q, ym, pc, pr, ok)

# Existence
# ---------

def inbox_rw(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +x: M.Vec(~F), +x2: M.Vec(~F), e: {x == x2 : M.Vec(~F)}, h: BX.inbox(~K, ~F, ~H, gc, gr, x)) -> BX.inbox(~K, ~F, ~H, gc, gr, x2):
  %e : BX.inbox(~K, ~F, ~H, gc, gr, _)
  h

def zeros_rw(~F: O.OField, +x: M.Vec(~F), +x2: M.Vec(~F), +es: List<&2, E.QExpr>, e: {x == x2 : M.Vec(~F)}, h: SK.Zeros(~F, x, es)) -> SK.Zeros(~F, x2, es):
  %e : SK.Zeros(~F, _, es)
  h

def eqsb_rw(+m: Nat, +m2: Nat, +es: List<&2, E.QExpr>, e: {m == m2 : Nat}, h: {PL.eqs_below(m, es) == True{} : Bool}) -> {PL.eqs_below(m2, es) == True{} : Bool}:
  %e : {PL.eqs_below(_, es) == True{} : Bool}
  h

def allb_rw(+m: Nat, +m2: Nat, +es: List<&2, E.QExpr>, e: {m == m2 : Nat}, h: {CK.allbelow(m, es) == True{} : Bool}) -> {CK.allbelow(m2, es) == True{} : Bool}:
  %e : {CK.allbelow(_, es) == True{} : Bool}
  h

def pbox_rw(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +o: Nat, +o2: Nat, +p: M.Vec(~F), e: {o == o2 : Nat}, h: pbox(~K, ~F, ~H, gc, gr, o, p)) -> pbox(~K, ~F, ~H, gc, gr, o2, p):
  %e : pbox(~K, ~F, ~H, gc, gr, _, p)
  h

def pbox_len(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +o: Nat, +p: M.Vec(~F), h: pbox(~K, ~F, ~H, gc, gr, o, p)) -> {M.len(~F, p) == o : Nat}:
  (hl, hr) = h
  hl

def fitn.a(~F: O.OField, +n: Nat, +y: M.Vec(~F), +z: M.Vec(~F), +es: List<&2, E.QExpr>, hy: {M.len(~F, y) == n : Nat}, h: M.vbnd.all(~F, C.fvals(~F, es, C.app(~F, C.fit(~F, n, y), z)), O.zero(F))) -> M.vbnd.all(~F, C.fvals(~F, es, C.app(~F, y, z)), O.zero(F)):
  %FV.fit_len(~F, n, y, hy) : M.vbnd.all(~F, C.fvals(~F, es, C.app(~F, _, z)), O.zero(F))
  h

def kt_all2(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), hgr: {KA.klen(~K, gr) == KA.klen(~K, gc) : Nat}) -> {PL.ktake(~K, KA.klen(~K, gc), gr) == gr : N.KVec(~K)}:
  %hgr : {PL.ktake(~K, _, gr) == gr : N.KVec(~K)}
  ktake_all(~K, gr)

def fitn(~F: O.OField, +n: Nat, +y: M.Vec(~F), +z: M.Vec(~F), +es: List<&2, E.QExpr>, hy: {M.len(~F, y) == n : Nat}, h: M.vbnd(~F, C.fvals(~F, es, C.app(~F, C.fit(~F, n, y), z)), O.zero(F))) -> M.vbnd.all(~F, C.fvals(~F, es, C.app(~F, y, z)), O.zero(F)):
  (h0, ha) = h
  fitn.a(~F, n, y, z, es, hy, ha)

# the whole prefix is the whole box
def pbox_full.k(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +p: M.Vec(~F), h: pbox(~K, ~F, ~H, gc, gr, KA.klen(~K, gc), p), +hgr: {KA.klen(~K, gr) == KA.klen(~K, gc) : Nat}) -> BX.inbox(~K, ~F, ~H, gc, gr, p):
  (hl, hr) = h
  (Equal.trans(Nat, M.len(~F, p), KA.klen(~K, gc), M.len(~F, N.ofkv(~K, ~F, ~H, gc)), hl, Equal.sym(Nat, M.len(~F, N.ofkv(~K, ~F, ~H, gc)), KA.klen(~K, gc), CP.len_ofkv(~K, ~F, ~H, gc))),
   FV.rbnd_rw2(~F, C.vsub(~F, p, N.ofkv(~K, ~F, ~H, gc)), N.ofkv(~K, ~F, ~H, PL.ktake(~K, KA.klen(~K, gc), gr)), N.ofkv(~K, ~F, ~H, gr), ofkv_rw(~K, ~F, ~H, PL.ktake(~K, KA.klen(~K, gc), gr), gr, kt_all2(~K, gc, gr, hgr)),
     rbnd_rwd(~F, C.vsub(~F, p, N.ofkv(~K, ~F, ~H, PL.ktake(~K, KA.klen(~K, gc), gc))), C.vsub(~F, p, N.ofkv(~K, ~F, ~H, gc)), N.ofkv(~K, ~F, ~H, PL.ktake(~K, KA.klen(~K, gc), gr)), vsub_rw(~F, p, N.ofkv(~K, ~F, ~H, PL.ktake(~K, KA.klen(~K, gc), gc)), N.ofkv(~K, ~F, ~H, gc), ofkv_rw(~K, ~F, ~H, PL.ktake(~K, KA.klen(~K, gc), gc), gc, ktake_all(~K, gc))), hr)))

def Ex(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +p: M.Vec(~F)) -> Data:
  Sigma<&2, &2, M.Vec(~F), r => M.Both(BX.inbox(~K, ~F, ~H, gc, gr, C.app(~F, p, r)), SK.Zeros(~F, C.app(~F, p, r), es))>

def walk_ex.nil(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), es: List<&2, E.QExpr>, +o: Nat, +p: M.Vec(~F), +ho: {o == KA.klen(~K, gc) : Nat}, hes: {PL.isnil(es) == True{} : Bool}, hpb: pbox(~K, ~F, ~H, gc, gr, o, p), +hgr: {KA.klen(~K, gr) == KA.klen(~K, gc) : Nat}) -> Ex(~K, ~F, ~H, gc, gr, es, p):
  match es:
    case Nil{}:
      (Nil{}, (inbox_rw(~K, ~F, ~H, gc, gr, p, C.app(~F, p, Nil{}), Equal.sym(M.Vec(~F), C.app(~F, p, Nil{}), p, app_nil(~F, p)), pbox_full.k(~K, ~F, ~H, gc, gr, p, pbox_rw(~K, ~F, ~H, gc, gr, o, KA.klen(~K, gc), p, ho, hpb), hgr)), Unit{}))
    case Con{e, t}:
      FO.absurd(Ex(~K, ~F, ~H, gc, gr, Con{e, t}, p), KA.ft(hes))

def walk_ex.fin(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +p: M.Vec(~F), +y: M.Vec(~F), +hlen: {M.len(~F, C.app(~F, p, y)) == Nat.add(o, n) : Nat}, +hbel: {PL.eqs_below(Nat.add(o, n), PL.takeq(n, es)) == True{} : Bool}, hglob: SK.Zeros(~F, C.app(~F, p, y), PL.takeq(n, es)), s: Ex(~K, ~F, ~H, gc, gr, PL.dropq(n, es), C.app(~F, p, y))) -> Ex(~K, ~F, ~H, gc, gr, es, p):
  (+r, h) = s
  (hin, hzs) = h
  +ea = app_assoc(~F, p, y, r)
  +x = C.app(~F, p, C.app(~F, y, r))
  (C.app(~F, y, r), (inbox_rw(~K, ~F, ~H, gc, gr, C.app(~F, C.app(~F, p, y), r), x, ea, hin), zeros_split(~F, x, n, es, zeros_rw(~F, C.app(~F, C.app(~F, p, y), r), x, PL.takeq(n, es), ea, zeros_prefix(~F, C.app(~F, p, y), r, PL.takeq(n, es), eqsb_rw(Nat.add(o, n), M.len(~F, C.app(~F, p, y)), PL.takeq(n, es), Equal.sym(Nat, M.len(~F, C.app(~F, p, y)), Nat.add(o, n), hlen), hbel), hglob)), zeros_rw(~F, C.app(~F, C.app(~F, p, y), r), x, PL.dropq(n, es), ea, hzs))))

# the blocks in order build a point of the box where every equation vanishes
def walk_ex(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), bs: List<&2, PL.PBlock<K>>, +es: List<&2, E.QExpr>, +o: Nat, +p: M.Vec(~F), +hw: {PL.walk(~K, gc, gr, bs, es, o) == True{} : Bool}, +hpb: pbox(~K, ~F, ~H, gc, gr, o, p), +hgr: {KA.klen(~K, gr) == KA.klen(~K, gc) : Nat}) -> Ex(~K, ~F, ~H, gc, gr, es, p):
  match bs:
    case Nil{}:
      walk_ex.nil(~K, ~F, ~H, gc, gr, es, o, p, CP.nateq_ok(o, KA.klen(~K, gc), KA.band_l(KA.nateq(o, KA.klen(~K, gc)), PL.isnil(es), hw)), KA.band_r(KA.nateq(o, KA.klen(~K, gc)), PL.isnil(es), hw), hpb, hgr)
    case Con{PL.PBlock{+n, +pars, +c}, +t}:
      +hbo = KA.band_l(PL.block_ok(~K, gc, gr, es, o, n, pars, c), PL.walk(~K, gc, gr, t, PL.dropq(n, es), Nat.add(o, n)), hw)
      +hrest = KA.band_r(PL.block_ok(~K, gc, gr, es, o, n, pars, c), PL.walk(~K, gc, gr, t, PL.dropq(n, es), Nat.add(o, n)), hw)
      +e1 = PL.takeq(n, es)
      +blk = {C.Block{PL.renames(o, n, pars, e1), n} : C.Block}
      +okc = bo_cert(~K, gc, gr, es, o, n, pars, c, hbo)
      +hgo = natle_addl(o, n, KA.klen(~K, gc), bo_in_box(~K, gc, gr, es, o, n, pars, c, hbo))
      +z = zmap(~F, p, pars)
      +hz = pin_pc(~K, ~F, ~H, gc, gr, o, p, hpb, hgo, pars, C.Cert.pc(K, c), C.Cert.pr(K, c), bo_pars(~K, gc, gr, es, o, n, pars, c, hbo), bo_pcont(~K, gc, gr, es, o, n, pars, c, hbo))
      +y = BA.ys(~K, ~F, ~R, ~H, blk, c, z)
      +hy = BA.ys_ball(~K, ~F, ~R, ~H, blk, c, okc, z, hz)
      +hly = Equal.trans(Nat, M.len(~F, y), M.len(~F, C.center(~K, ~F, ~H, c)), n, BA.ball_len(~K, ~F, ~H, c, y, hy), Equal.trans(Nat, M.len(~F, C.center(~K, ~F, ~H, c)), KA.klen(~K, C.Cert.yc(K, c)), n, CP.len_ofkv(~K, ~F, ~H, C.Cert.yc(K, c)), cert_lyc(~K, PL.renames(o, n, pars, e1), n, c, okc)))
      +hlp = pbox_len(~K, ~F, ~H, gc, gr, o, p, hpb)
      +hfx = CP.cert_fix(~K, ~F, ~H, blk, c, okc, z, y, hy, BA.ys_fix(~K, ~F, ~R, ~H, blk, c, okc, z, hz))
      +hloc = zeros_of_vall(~F, C.app(~F, y, z), PL.renames(o, n, pars, e1), fitn(~F, n, y, z, PL.renames(o, n, pars, e1), hly, hfx))
      +hbel = allb_rw(Nat.add(n, KA.klen(~K, C.Cert.pc(K, c))), Nat.add(n, PL.nlen(pars)), PL.renames(o, n, pars, e1), add2(n, n, KA.klen(~K, C.Cert.pc(K, c)), PL.nlen(pars), {==}, pcont_len(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c), bo_pcont(~K, gc, gr, es, o, n, pars, c, hbo))), cert_bel(~K, PL.renames(o, n, pars, e1), n, c, okc))
      +hglob = zeros_subst(~F, o, n, pars, p, y, e1, hlp, hly, bo_below(~K, gc, gr, es, o, n, pars, c, hbo), hbel, hloc)
      +hpb2 = pbox_ext(~K, ~F, ~H, gc, gr, o, n, p, y, hpb, seg_of_ball(~K, ~F, ~H, gc, gr, o, n, c, y, hy, hly, bo_yc(~K, gc, gr, es, o, n, pars, c, hbo), bo_yr(~K, gc, gr, es, o, n, pars, c, hbo)), hly, hgo, hgr)
      walk_ex.fin(~K, ~F, ~H, gc, gr, es, o, n, p, y, pbox_len(~K, ~F, ~H, gc, gr, Nat.add(o, n), C.app(~F, p, y), hpb2), bo_below(~K, gc, gr, es, o, n, pars, c, hbo), hglob, walk_ex(~K, ~F, ~R, ~H, gc, gr, t, PL.dropq(n, es), Nat.add(o, n), C.app(~F, p, y), hrest, hpb2, hgr))

def rnn_kt(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, n: Nat, u: N.KVec(~K), h: FV.rnn(~F, N.ofkv(~K, ~F, ~H, u))) -> FV.rnn(~F, N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, u))):
  match n u:
    case 0n u:
      Unit{}
    case 1n+k Nil{}:
      Unit{}
    case 1n+k Con{a, t}:
      (ha, ht) = h
      (ha, rnn_kt(~K, ~F, ~H, k, t, ht))

# the plan's top-level facts: check.p = c1 && (c2 && (c3 && (c4 && c5)))
def cp_r1(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.p(~K, eqs, gc, gr, np, bs) == True{} : Bool}) -> {KA.band(KA.kvle(~K, Nil{}, gr), KA.band(KA.natle(np, KA.klen(~K, gc)), KA.band(PL.pinz(~K, np, gr), PL.walk(~K, gc, gr, bs, eqs, np)))) == True{} : Bool}:
  KA.band_r(KA.nateq(KA.klen(~K, gr), KA.klen(~K, gc)), KA.band(KA.kvle(~K, Nil{}, gr), KA.band(KA.natle(np, KA.klen(~K, gc)), KA.band(PL.pinz(~K, np, gr), PL.walk(~K, gc, gr, bs, eqs, np)))), h)

def cp_r2(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.p(~K, eqs, gc, gr, np, bs) == True{} : Bool}) -> {KA.band(KA.natle(np, KA.klen(~K, gc)), KA.band(PL.pinz(~K, np, gr), PL.walk(~K, gc, gr, bs, eqs, np))) == True{} : Bool}:
  KA.band_r(KA.kvle(~K, Nil{}, gr), KA.band(KA.natle(np, KA.klen(~K, gc)), KA.band(PL.pinz(~K, np, gr), PL.walk(~K, gc, gr, bs, eqs, np))), cp_r1(~K, eqs, gc, gr, np, bs, h))

def cp_r3(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.p(~K, eqs, gc, gr, np, bs) == True{} : Bool}) -> {KA.band(PL.pinz(~K, np, gr), PL.walk(~K, gc, gr, bs, eqs, np)) == True{} : Bool}:
  KA.band_r(KA.natle(np, KA.klen(~K, gc)), KA.band(PL.pinz(~K, np, gr), PL.walk(~K, gc, gr, bs, eqs, np)), cp_r2(~K, eqs, gc, gr, np, bs, h))

def cp_len(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.p(~K, eqs, gc, gr, np, bs) == True{} : Bool}) -> {KA.klen(~K, gr) == KA.klen(~K, gc) : Nat}:
  CP.nateq_ok(KA.klen(~K, gr), KA.klen(~K, gc), KA.band_l(KA.nateq(KA.klen(~K, gr), KA.klen(~K, gc)), KA.band(KA.kvle(~K, Nil{}, gr), KA.band(KA.natle(np, KA.klen(~K, gc)), KA.band(PL.pinz(~K, np, gr), PL.walk(~K, gc, gr, bs, eqs, np)))), h))

def cp_nn(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.p(~K, eqs, gc, gr, np, bs) == True{} : Bool}) -> {KA.kvle(~K, Nil{}, gr) == True{} : Bool}:
  KA.band_l(KA.kvle(~K, Nil{}, gr), KA.band(KA.natle(np, KA.klen(~K, gc)), KA.band(PL.pinz(~K, np, gr), PL.walk(~K, gc, gr, bs, eqs, np))), cp_r1(~K, eqs, gc, gr, np, bs, h))

def cp_np(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.p(~K, eqs, gc, gr, np, bs) == True{} : Bool}) -> {KA.natle(np, KA.klen(~K, gc)) == True{} : Bool}:
  KA.band_l(KA.natle(np, KA.klen(~K, gc)), KA.band(PL.pinz(~K, np, gr), PL.walk(~K, gc, gr, bs, eqs, np)), cp_r2(~K, eqs, gc, gr, np, bs, h))

def cp_pinz(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.p(~K, eqs, gc, gr, np, bs) == True{} : Bool}) -> {PL.pinz(~K, np, gr) == True{} : Bool}:
  KA.band_l(PL.pinz(~K, np, gr), PL.walk(~K, gc, gr, bs, eqs, np), cp_r3(~K, eqs, gc, gr, np, bs, h))

def cp_walk(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.p(~K, eqs, gc, gr, np, bs) == True{} : Bool}) -> {PL.walk(~K, gc, gr, bs, eqs, np) == True{} : Bool}:
  KA.band_r(PL.pinz(~K, np, gr), PL.walk(~K, gc, gr, bs, eqs, np), cp_r3(~K, eqs, gc, gr, np, bs, h))

# the pinned prefix: the box's first np centers
def p0(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +np: Nat) -> M.Vec(~F):
  N.ofkv(~K, ~F, ~H, PL.ktake(~K, np, gc))

def pbox0(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.p(~K, eqs, gc, gr, np, bs) == True{} : Bool}) -> pbox(~K, ~F, ~H, gc, gr, np, p0(~K, ~F, ~H, gc, np)):
  (len_kt(~K, ~F, ~H, np, gc, cp_np(~K, eqs, gc, gr, np, bs, h)), FV.rbnd_self(~F, p0(~K, ~F, ~H, gc, np), N.ofkv(~K, ~F, ~H, PL.ktake(~K, np, gr)), rnn_kt(~K, ~F, ~H, np, gr, KA.kvle_ok(~K, ~F, ~H, Nil{}, gr, cp_nn(~K, eqs, gc, gr, np, bs, h)))))

def plan_exists.fin(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +p: M.Vec(~F), s: Ex(~K, ~F, ~H, gc, gr, eqs, p)) -> Sigma<&2, &2, M.Vec(~F), x => M.Both(BX.inbox(~K, ~F, ~H, gc, gr, x), SK.Zeros(~F, x, eqs))>:
  (+r, h) = s
  (C.app(~F, p, r), h)

def plan_exists.p(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +np: Nat, +bs: List<&2, PL.PBlock<K>>, +ok: {PL.check.p(~K, eqs, gc, gr, np, bs) == True{} : Bool}) -> Sigma<&2, &2, M.Vec(~F), x => M.Both(BX.inbox(~K, ~F, ~H, gc, gr, x), SK.Zeros(~F, x, eqs))>:
  plan_exists.fin(~K, ~F, ~H, eqs, gc, gr, p0(~K, ~F, ~H, gc, np), walk_ex(~K, ~F, ~R, ~H, gc, gr, bs, eqs, np, p0(~K, ~F, ~H, gc, np), cp_walk(~K, eqs, gc, gr, np, bs, ok), pbox0(~K, ~F, ~H, eqs, gc, gr, np, bs, ok), cp_len(~K, eqs, gc, gr, np, bs, ok)))

# Uniqueness
# ----------

def ftake(~F: O.OField, n: Nat, v: M.Vec(~F)) -> M.Vec(~F):
  match n v:
    case 0n v:
      Nil{}
    case 1n+k Nil{}:
      Nil{}
    case 1n+k Con{a, t}:
      Con{a, ftake(~F, k, t)}

def fdrop(~F: O.OField, n: Nat, v: M.Vec(~F)) -> M.Vec(~F):
  match n v:
    case 0n v:
      v
    case 1n+k Nil{}:
      Nil{}
    case 1n+k Con{a, t}:
      fdrop(~F, k, t)

def app_td(~F: O.OField, n: Nat, v: M.Vec(~F)) -> {C.app(~F, ftake(~F, n, v), fdrop(~F, n, v)) == v : M.Vec(~F)}:
  match n v:
    case 0n v:
      {==}
    case 1n+k Nil{}:
      {==}
    case 1n+k Con{+a, +t}:
      %Equal.sym(M.Vec(~F), C.app(~F, ftake(~F, k, t), fdrop(~F, k, t)), t, app_td(~F, k, t)) : {Con{a, _} == Con{a, t} : M.Vec(~F)}
      {==}

def len_ftake(~F: O.OField, n: Nat, v: M.Vec(~F), h: {KA.natle(n, M.len(~F, v)) == True{} : Bool}) -> {M.len(~F, ftake(~F, n, v)) == n : Nat}:
  match n v:
    case 0n v:
      {==}
    case 1n+k Nil{}:
      FO.absurd({0n == 1n+k : Nat}, KA.ft(h))
    case 1n++k Con{a, t}:
      %Equal.sym(Nat, M.len(~F, ftake(~F, k, t)), k, len_ftake(~F, k, t, h)) : {1n+_ == 1n+k : Nat}
      {==}

# n <= len r, for o + len r = m and o + n <= m
def natle_rest(o: Nat, +n: Nat, +lr: Nat, m: Nat, e: {Nat.add(o, lr) == m : Nat}, h: {KA.natle(Nat.add(o, n), m) == True{} : Bool}) -> {KA.natle(n, lr) == True{} : Bool}:
  match o m:
    case 0n m:
      %Equal.sym(Nat, lr, m, e) : {KA.natle(n, _) == True{} : Bool}
      h
    case 1n++k 0n:
      FO.absurd({KA.natle(n, lr) == True{} : Bool}, FV.succ_ne(Nat.add(k, lr), e))
    case 1n++k 1n++j:
      natle_rest(k, n, lr, j, FV.succ_inj(Nat.add(k, lr), j, e), h)

# u = w, from |u_i - w_i| <= 0 and equal lengths
def eq_of_vall(~F: O.OField, u: M.Vec(~F), w: M.Vec(~F), h: M.vbnd.all(~F, C.vsub(~F, u, w), O.zero(F)), hl: {M.len(~F, u) == M.len(~F, w) : Nat}) -> {u == w : M.Vec(~F)}:
  match u w:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+b, +ws}:
      FO.absurd({Nil{} == Con{b, ws} : M.Vec(~F)}, FV.zero_ne(M.len(~F, ws), hl))
    case Con{+a, +us} Nil{}:
      FO.absurd({Con{a, us} == Nil{} : M.Vec(~F)}, FV.succ_ne(M.len(~F, us), hl))
    case Con{+a, +us} Con{+b, +ws}:
      (h0, hs) = h
      %FO.eq_of_sub(~F, a, b, RL.bnd0_eq(~F, O.sub(~F, a, b), h0)) : {Con{a, us} == Con{_, ws} : M.Vec(~F)}
      %eq_of_vall(~F, us, ws, hs, FV.succ_inj(M.len(~F, us), M.len(~F, ws), hl)) : {Con{a, us} == Con{a, _} : M.Vec(~F)}
      {==}

def kt_kd(~K: N.Num, n: Nat, u: N.KVec(~K)) -> {KA.kapp(~K, PL.ktake(~K, n, u), PL.kdrop(~K, n, u)) == u : N.KVec(~K)}:
  match n u:
    case 0n u:
      {==}
    case 1n+k Nil{}:
      {==}
    case 1n+k Con{+a, +t}:
      %Equal.sym(N.KVec(~K), KA.kapp(~K, PL.ktake(~K, k, t), PL.kdrop(~K, k, t)), t, kt_kd(~K, k, t)) : {Con{a, _} == Con{a, t} : N.KVec(~K)}
      {==}

# the first m coordinates of a point of the box are a prefix of the box
def pbox_of_inbox(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +m: Nat, +q: M.Vec(~F), +r: M.Vec(~F), h: BX.inbox(~K, ~F, ~H, gc, gr, C.app(~F, q, r)), +hq: {M.len(~F, q) == m : Nat}, +hm: {KA.natle(m, KA.klen(~K, gc)) == True{} : Bool}, +hgr: {KA.klen(~K, gr) == KA.klen(~K, gc) : Nat}) -> pbox(~K, ~F, ~H, gc, gr, m, q):
  (hl, hr) = h
  +ca = N.ofkv(~K, ~F, ~H, PL.ktake(~K, m, gc))
  +cb = N.ofkv(~K, ~F, ~H, PL.kdrop(~K, m, gc))
  +ra = N.ofkv(~K, ~F, ~H, PL.ktake(~K, m, gr))
  +rb = N.ofkv(~K, ~F, ~H, PL.kdrop(~K, m, gr))
  +hla = len_kt(~K, ~F, ~H, m, gc, hm)
  +hlr = len_kt(~K, ~F, ~H, m, gr, natle_rw(m, KA.klen(~K, gc), KA.klen(~K, gr), Equal.sym(Nat, KA.klen(~K, gr), KA.klen(~K, gc), hgr), hm))
  +ec = Equal.trans(M.Vec(~F), N.ofkv(~K, ~F, ~H, gc), N.ofkv(~K, ~F, ~H, KA.kapp(~K, PL.ktake(~K, m, gc), PL.kdrop(~K, m, gc))), C.app(~F, ca, cb), ofkv_rw(~K, ~F, ~H, gc, KA.kapp(~K, PL.ktake(~K, m, gc), PL.kdrop(~K, m, gc)), Equal.sym(N.KVec(~K), KA.kapp(~K, PL.ktake(~K, m, gc), PL.kdrop(~K, m, gc)), gc, kt_kd(~K, m, gc))), CP.kapp_ofk(~K, ~F, ~H, PL.ktake(~K, m, gc), PL.kdrop(~K, m, gc)))
  +er = Equal.trans(M.Vec(~F), N.ofkv(~K, ~F, ~H, gr), N.ofkv(~K, ~F, ~H, KA.kapp(~K, PL.ktake(~K, m, gr), PL.kdrop(~K, m, gr))), C.app(~F, ra, rb), ofkv_rw(~K, ~F, ~H, gr, KA.kapp(~K, PL.ktake(~K, m, gr), PL.kdrop(~K, m, gr)), Equal.sym(N.KVec(~K), KA.kapp(~K, PL.ktake(~K, m, gr), PL.kdrop(~K, m, gr)), gr, kt_kd(~K, m, gr))), CP.kapp_ofk(~K, ~F, ~H, PL.ktake(~K, m, gr), PL.kdrop(~K, m, gr)))
  +ed = Equal.trans(M.Vec(~F), C.vsub(~F, C.app(~F, q, r), N.ofkv(~K, ~F, ~H, gc)), C.vsub(~F, C.app(~F, q, r), C.app(~F, ca, cb)), C.app(~F, C.vsub(~F, q, ca), C.vsub(~F, r, cb)), vsub_rw(~F, C.app(~F, q, r), N.ofkv(~K, ~F, ~H, gc), C.app(~F, ca, cb), ec), FV.vsub_app(~F, q, ca, r, cb, Equal.trans(Nat, M.len(~F, q), m, M.len(~F, ca), hq, Equal.sym(Nat, M.len(~F, ca), m, hla))))
  +hsplit = FV.rbnd_rw2(~F, C.app(~F, C.vsub(~F, q, ca), C.vsub(~F, r, cb)), N.ofkv(~K, ~F, ~H, gr), C.app(~F, ra, rb), er, rbnd_rwd(~F, C.vsub(~F, C.app(~F, q, r), N.ofkv(~K, ~F, ~H, gc)), C.app(~F, C.vsub(~F, q, ca), C.vsub(~F, r, cb)), N.ofkv(~K, ~F, ~H, gr), ed, hr))
  (hq, rbnd_l(~F, C.vsub(~F, q, ca), C.vsub(~F, r, cb), ra, rb, hsplit, Equal.trans(Nat, M.len(~F, C.vsub(~F, q, ca)), m, M.len(~F, ra), CP.len_vsub(~F, q, ca, m, hq, hla), Equal.sym(Nat, M.len(~F, ra), m, hlr))))

# the block's stretch of a prefix of the box
def seg_of_pbox(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +o: Nat, +n: Nat, +p: M.Vec(~F), +y: M.Vec(~F), h: pbox(~K, ~F, ~H, gc, gr, Nat.add(o, n), C.app(~F, p, y)), +hp: {M.len(~F, p) == o : Nat}, +hgo: {KA.natle(o, KA.klen(~K, gc)) == True{} : Bool}, +hgr: {KA.klen(~K, gr) == KA.klen(~K, gc) : Nat}) -> C.rbnd(~F, C.vsub(~F, y, N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gc)))), N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gr)))):
  (hl, hr) = h
  +ca = N.ofkv(~K, ~F, ~H, PL.ktake(~K, o, gc))
  +cb = N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gc)))
  +ra = N.ofkv(~K, ~F, ~H, PL.ktake(~K, o, gr))
  +rb = N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gr)))
  +hla = len_kt(~K, ~F, ~H, o, gc, hgo)
  +hlr = len_kt(~K, ~F, ~H, o, gr, natle_rw(o, KA.klen(~K, gc), KA.klen(~K, gr), Equal.sym(Nat, KA.klen(~K, gr), KA.klen(~K, gc), hgr), hgo))
  +ec = Equal.trans(M.Vec(~F), N.ofkv(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gc)), N.ofkv(~K, ~F, ~H, KA.kapp(~K, PL.ktake(~K, o, gc), PL.ktake(~K, n, PL.kdrop(~K, o, gc)))), C.app(~F, ca, cb), ofkv_rw(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gc), KA.kapp(~K, PL.ktake(~K, o, gc), PL.ktake(~K, n, PL.kdrop(~K, o, gc))), ktake_split(~K, o, n, gc)), CP.kapp_ofk(~K, ~F, ~H, PL.ktake(~K, o, gc), PL.ktake(~K, n, PL.kdrop(~K, o, gc))))
  +er = Equal.trans(M.Vec(~F), N.ofkv(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gr)), N.ofkv(~K, ~F, ~H, KA.kapp(~K, PL.ktake(~K, o, gr), PL.ktake(~K, n, PL.kdrop(~K, o, gr)))), C.app(~F, ra, rb), ofkv_rw(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gr), KA.kapp(~K, PL.ktake(~K, o, gr), PL.ktake(~K, n, PL.kdrop(~K, o, gr))), ktake_split(~K, o, n, gr)), CP.kapp_ofk(~K, ~F, ~H, PL.ktake(~K, o, gr), PL.ktake(~K, n, PL.kdrop(~K, o, gr))))
  +ed = Equal.trans(M.Vec(~F), C.vsub(~F, C.app(~F, p, y), N.ofkv(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gc))), C.vsub(~F, C.app(~F, p, y), C.app(~F, ca, cb)), C.app(~F, C.vsub(~F, p, ca), C.vsub(~F, y, cb)), vsub_rw(~F, C.app(~F, p, y), N.ofkv(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gc)), C.app(~F, ca, cb), ec), FV.vsub_app(~F, p, ca, y, cb, Equal.trans(Nat, M.len(~F, p), o, M.len(~F, ca), hp, Equal.sym(Nat, M.len(~F, ca), o, hla))))
  +hsplit = FV.rbnd_rw2(~F, C.app(~F, C.vsub(~F, p, ca), C.vsub(~F, y, cb)), N.ofkv(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gr)), C.app(~F, ra, rb), er, rbnd_rwd(~F, C.vsub(~F, C.app(~F, p, y), N.ofkv(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gc))), C.app(~F, C.vsub(~F, p, ca), C.vsub(~F, y, cb)), N.ofkv(~K, ~F, ~H, PL.ktake(~K, Nat.add(o, n), gr)), ed, hr))
  rbnd_r(~F, C.vsub(~F, p, ca), C.vsub(~F, y, cb), ra, rb, hsplit, Equal.trans(Nat, M.len(~F, C.vsub(~F, p, ca)), o, M.len(~F, ra), CP.len_vsub(~F, p, ca, o, hp, hla), Equal.sym(Nat, M.len(~F, ra), o, hlr)))

# radii fitted to n entries bound what the radii bound, for n entries
def rbnd_unkfit(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, n: Nat, d: M.Vec(~F), r: N.KVec(~K), h: C.rbnd(~F, d, N.ofkv(~K, ~F, ~H, KA.kfit(~K, n, r))), hl: {M.len(~F, d) == n : Nat}) -> C.rbnd(~F, d, N.ofkv(~K, ~F, ~H, r)):
  match n d r:
    case 0n Nil{} r:
      Unit{}
    case 0n Con{+a, +ds} r:
      FO.absurd(C.rbnd(~F, Con{a, ds}, N.ofkv(~K, ~F, ~H, r)), FV.succ_ne(M.len(~F, ds), hl))
    case 1n++k Nil{} r:
      FO.absurd(C.rbnd(~F, Nil{}, N.ofkv(~K, ~F, ~H, r)), FV.zero_ne(k, hl))
    case 1n+k Con{+a, +ds} Nil{}:
      (ha, hs) = h
      (BA.bnd_rw_s(~F, a, N.emap(K, F, H, N.nzero(K)), O.zero(F), N.e_zero(K, F, H), ha), rbnd_unkfit(~K, ~F, ~H, k, ds, Nil{}, hs, FV.succ_inj(M.len(~F, ds), k, hl)))
    case 1n+k Con{+a, +ds} Con{x, xs}:
      (ha, hs) = h
      (ha, rbnd_unkfit(~K, ~F, ~H, k, ds, xs, hs, FV.succ_inj(M.len(~F, ds), k, hl)))

# a stretch of the box is the certificate's ball
def ball_of_seg(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +o: Nat, +n: Nat, +c: C.Cert<K>, +y: M.Vec(~F), hs: C.rbnd(~F, C.vsub(~F, y, N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gc)))), N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gr)))), +hy: {M.len(~F, y) == n : Nat}, +hlc: {KA.klen(~K, C.Cert.yc(K, c)) == n : Nat}, hyc: {PL.kveq(~K, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc))) == True{} : Bool}, hyr: {PL.kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr))) == True{} : Bool}) -> C.ball(~K, ~F, ~H, c, y):
  +cen = C.center(~K, ~F, ~H, c)
  +ecen = Equal.sym(M.Vec(~F), cen, N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gc))), kveq_ok(~K, ~F, ~H, C.Cert.yc(K, c), PL.ktake(~K, n, PL.kdrop(~K, o, gc)), hyc))
  +h1 = rbnd_rwd(~F, C.vsub(~F, y, N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gc)))), C.vsub(~F, y, cen), N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gr))), vsub_rw(~F, y, N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gc))), cen, ecen), hs)
  +h2 = FV.rbnd_rw2(~F, C.vsub(~F, y, cen), N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gr))), N.ofkv(~K, ~F, ~H, KA.kfit(~K, n, C.Cert.yr(K, c))), Equal.sym(M.Vec(~F), N.ofkv(~K, ~F, ~H, KA.kfit(~K, n, C.Cert.yr(K, c))), N.ofkv(~K, ~F, ~H, PL.ktake(~K, n, PL.kdrop(~K, o, gr))), kveq_ok(~K, ~F, ~H, KA.kfit(~K, n, C.Cert.yr(K, c)), PL.ktake(~K, n, PL.kdrop(~K, o, gr)), hyr)), h1)
  +hlcen = Equal.trans(Nat, M.len(~F, cen), KA.klen(~K, C.Cert.yc(K, c)), n, CP.len_ofkv(~K, ~F, ~H, C.Cert.yc(K, c)), hlc)
  (Equal.trans(Nat, M.len(~F, y), n, M.len(~F, cen), hy, Equal.sym(Nat, M.len(~F, cen), n, hlcen)), rbnd_unkfit(~K, ~F, ~H, n, C.vsub(~F, y, cen), C.Cert.yr(K, c), h2, CP.len_vsub(~F, y, cen, n, hy, hlcen)))

def unfitn(~F: O.OField, +n: Nat, +y: M.Vec(~F), +z: M.Vec(~F), +es: List<&2, E.QExpr>, hy: {M.len(~F, y) == n : Nat}, h: M.vbnd.all(~F, C.fvals(~F, es, C.app(~F, y, z)), O.zero(F))) -> M.vbnd(~F, C.fvals(~F, es, C.app(~F, C.fit(~F, n, y), z)), O.zero(F)):
  %Equal.sym(M.Vec(~F), C.fit(~F, n, y), y, FV.fit_len(~F, n, y, hy)) : M.vbnd(~F, C.fvals(~F, es, C.app(~F, _, z)), O.zero(F))
  (FO.le_refl(~F, O.zero(F)), h)

def inbox_len(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +x: M.Vec(~F), h: BX.inbox(~K, ~F, ~H, gc, gr, x)) -> {M.len(~F, x) == M.len(~F, N.ofkv(~K, ~F, ~H, gc)) : Nat}:
  (hl, hr) = h
  hl

def blk(+o: Nat, +n: Nat, +pars: List<&2, Nat>, +es: List<&2, E.QExpr>) -> C.Block:
  C.Block{PL.renames(o, n, pars, PL.takeq(n, es)), n}

# what one solution says about the block: its stretch y = take n r is the
# certificate's ball and a zero of the block, and the rest r' = drop n r
# continues it
def Side(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +p: M.Vec(~F), +r: M.Vec(~F)) -> Data:
  M.Both({M.len(~F, ftake(~F, n, r)) == n : Nat},
  M.Both(C.ball(~K, ~F, ~H, c, ftake(~F, n, r)),
  M.Both(M.vbnd(~F, C.bfun(~F, blk(o, n, pars, es), ftake(~F, n, r), zmap(~F, p, pars)), O.zero(F)),
  M.Both(BX.inbox(~K, ~F, ~H, gc, gr, C.app(~F, C.app(~F, p, ftake(~F, n, r)), fdrop(~F, n, r))),
  SK.Zeros(~F, C.app(~F, C.app(~F, p, ftake(~F, n, r)), fdrop(~F, n, r)), PL.dropq(n, es))))))

def x_split(~F: O.OField, +p: M.Vec(~F), +n: Nat, +r: M.Vec(~F)) -> {C.app(~F, p, r) == C.app(~F, C.app(~F, p, ftake(~F, n, r)), fdrop(~F, n, r)) : M.Vec(~F)}:
  %app_td(~F, n, r) : {C.app(~F, p, _) == C.app(~F, C.app(~F, p, ftake(~F, n, r)), fdrop(~F, n, r)) : M.Vec(~F)}
  Equal.sym(M.Vec(~F), C.app(~F, C.app(~F, p, ftake(~F, n, r)), fdrop(~F, n, r)), C.app(~F, p, C.app(~F, ftake(~F, n, r), fdrop(~F, n, r))), app_assoc(~F, p, ftake(~F, n, r), fdrop(~F, n, r)))

def side_facts(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +hbo: {PL.block_ok(~K, gc, gr, es, o, n, pars, c) == True{} : Bool}, +p: M.Vec(~F), +hlp: {M.len(~F, p) == o : Nat}, +hgr: {KA.klen(~K, gr) == KA.klen(~K, gc) : Nat}, +r: M.Vec(~F), +hin: BX.inbox(~K, ~F, ~H, gc, gr, C.app(~F, p, r)), +hz: SK.Zeros(~F, C.app(~F, p, r), es)) -> Side(~K, ~F, ~H, gc, gr, es, o, n, pars, c, p, r):
  +y = ftake(~F, n, r)
  +r2 = fdrop(~F, n, r)
  +py = C.app(~F, p, y)
  +e1 = PL.takeq(n, es)
  +okc = bo_cert(~K, gc, gr, es, o, n, pars, c, hbo)
  +hgc = bo_in_box(~K, gc, gr, es, o, n, pars, c, hbo)
  +hgo = natle_addl(o, n, KA.klen(~K, gc), hgc)
  +hlx = Equal.trans(Nat, M.len(~F, C.app(~F, p, r)), M.len(~F, N.ofkv(~K, ~F, ~H, gc)), KA.klen(~K, gc), inbox_len(~K, ~F, ~H, gc, gr, C.app(~F, p, r), hin), CP.len_ofkv(~K, ~F, ~H, gc))
  +hly = len_ftake(~F, n, r, natle_rest(o, n, M.len(~F, r), KA.klen(~K, gc), Equal.trans(Nat, Nat.add(o, M.len(~F, r)), M.len(~F, C.app(~F, p, r)), KA.klen(~K, gc), Equal.sym(Nat, M.len(~F, C.app(~F, p, r)), Nat.add(o, M.len(~F, r)), Equal.trans(Nat, M.len(~F, C.app(~F, p, r)), Nat.add(M.len(~F, p), M.len(~F, r)), Nat.add(o, M.len(~F, r)), len_app(~F, p, r), add2(M.len(~F, p), o, M.len(~F, r), M.len(~F, r), hlp, {==}))), hlx), hgc))
  +ex = x_split(~F, p, n, r)
  +hin2 = inbox_rw(~K, ~F, ~H, gc, gr, C.app(~F, p, r), C.app(~F, py, r2), ex, hin)
  +hz2 = zeros_rw(~F, C.app(~F, p, r), C.app(~F, py, r2), es, ex, hz)
  +hlpy = Equal.trans(Nat, M.len(~F, py), Nat.add(M.len(~F, p), M.len(~F, y)), Nat.add(o, n), len_app(~F, p, y), add2(M.len(~F, p), o, M.len(~F, y), n, hlp, hly))
  +hpb = pbox_of_inbox(~K, ~F, ~H, gc, gr, Nat.add(o, n), py, r2, hin2, hlpy, hgc, hgr)
  +hball = ball_of_seg(~K, ~F, ~H, gc, gr, o, n, c, y, seg_of_pbox(~K, ~F, ~H, gc, gr, o, n, p, y, hpb, hlp, hgo, hgr), hly, cert_lyc(~K, PL.renames(o, n, pars, e1), n, c, okc), bo_yc(~K, gc, gr, es, o, n, pars, c, hbo), bo_yr(~K, gc, gr, es, o, n, pars, c, hbo))
  +hbel = allb_rw(Nat.add(n, KA.klen(~K, C.Cert.pc(K, c))), Nat.add(n, PL.nlen(pars)), PL.renames(o, n, pars, e1), add2(n, n, KA.klen(~K, C.Cert.pc(K, c)), PL.nlen(pars), {==}, pcont_len(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c), bo_pcont(~K, gc, gr, es, o, n, pars, c, hbo))), cert_bel(~K, PL.renames(o, n, pars, e1), n, c, okc))
  +hzl = zeros_unsubst(~F, o, n, pars, p, y, e1, hlp, hly, bo_below(~K, gc, gr, es, o, n, pars, c, hbo), hbel, zeros_unprefix(~F, py, r2, e1, eqsb_rw(Nat.add(o, n), M.len(~F, py), e1, Equal.sym(Nat, M.len(~F, py), Nat.add(o, n), hlpy), bo_below(~K, gc, gr, es, o, n, pars, c, hbo)), zeros_take(~F, C.app(~F, py, r2), n, es, hz2)))
  (hly, (hball, (unfitn(~F, n, y, zmap(~F, p, pars), PL.renames(o, n, pars, e1), hly, vall_of_zeros(~F, C.app(~F, y, zmap(~F, p, pars)), PL.renames(o, n, pars, e1), hzl)), (hin2, zeros_drop(~F, C.app(~F, py, r2), n, es, hz2)))))

def sd_len(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +p: M.Vec(~F), +r: M.Vec(~F), s: Side(~K, ~F, ~H, gc, gr, es, o, n, pars, c, p, r)) -> {M.len(~F, ftake(~F, n, r)) == n : Nat}:
  (a, t) = s
  a

def sd_ball(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +p: M.Vec(~F), +r: M.Vec(~F), s: Side(~K, ~F, ~H, gc, gr, es, o, n, pars, c, p, r)) -> C.ball(~K, ~F, ~H, c, ftake(~F, n, r)):
  (a, t) = s
  (b, u) = t
  b

def sd_zero(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +p: M.Vec(~F), +r: M.Vec(~F), s: Side(~K, ~F, ~H, gc, gr, es, o, n, pars, c, p, r)) -> M.vbnd(~F, C.bfun(~F, blk(o, n, pars, es), ftake(~F, n, r), zmap(~F, p, pars)), O.zero(F)):
  (a, t) = s
  (b, u) = t
  (d, w) = u
  d

def sd_in(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +p: M.Vec(~F), +r: M.Vec(~F), s: Side(~K, ~F, ~H, gc, gr, es, o, n, pars, c, p, r)) -> BX.inbox(~K, ~F, ~H, gc, gr, C.app(~F, C.app(~F, p, ftake(~F, n, r)), fdrop(~F, n, r))):
  (a, t) = s
  (b, u) = t
  (d, w) = u
  (f, g) = w
  f

def sd_zs(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>, +p: M.Vec(~F), +r: M.Vec(~F), s: Side(~K, ~F, ~H, gc, gr, es, o, n, pars, c, p, r)) -> SK.Zeros(~F, C.app(~F, C.app(~F, p, ftake(~F, n, r)), fdrop(~F, n, r)), PL.dropq(n, es)):
  (a, t) = s
  (b, u) = t
  (d, w) = u
  (f, g) = w
  g

def vall_of_vbnd(~F: O.OField, +v: M.Vec(~F), +s: O.C(F), h: M.vbnd(~F, v, s)) -> M.vbnd.all(~F, v, s):
  (h0, ha) = h
  ha

def app3_rw(~F: O.OField, +p: M.Vec(~F), +y: M.Vec(~F), +y2: M.Vec(~F), +r: M.Vec(~F), e: {y == y2 : M.Vec(~F)}) -> {C.app(~F, C.app(~F, p, y), r) == C.app(~F, C.app(~F, p, y2), r) : M.Vec(~F)}:
  %e : {C.app(~F, C.app(~F, p, y), r) == C.app(~F, C.app(~F, p, _), r) : M.Vec(~F)}
  {==}

# r = r2, from equal first n entries and equal rests
def td_eq(~F: O.OField, +n: Nat, +r: M.Vec(~F), +r2: M.Vec(~F), e1: {ftake(~F, n, r) == ftake(~F, n, r2) : M.Vec(~F)}, e2: {fdrop(~F, n, r) == fdrop(~F, n, r2) : M.Vec(~F)}) -> {r == r2 : M.Vec(~F)}:
  %app_td(~F, n, r2) : {r == _ : M.Vec(~F)}
  %app_td(~F, n, r) : {_ == C.app(~F, ftake(~F, n, r2), fdrop(~F, n, r2)) : M.Vec(~F)}
  %e1 : {C.app(~F, ftake(~F, n, r), fdrop(~F, n, r)) == C.app(~F, _, fdrop(~F, n, r2)) : M.Vec(~F)}
  %e2 : {C.app(~F, ftake(~F, n, r), fdrop(~F, n, r)) == C.app(~F, ftake(~F, n, r), _) : M.Vec(~F)}
  {==}

def rnil.r(~F: O.OField, r: M.Vec(~F), h: {M.len(~F, r) == 0n : Nat}) -> {r == Nil{} : M.Vec(~F)}:
  match r:
    case Nil{}:
      {==}
    case Con{+a, +t}:
      FO.absurd({Con{a, t} == Nil{} : M.Vec(~F)}, FV.succ_ne(M.len(~F, t), h))

# r is empty, for p of length o and p ++ r of length o
def rnil(~F: O.OField, p: M.Vec(~F), +r: M.Vec(~F), o: Nat, hp: {M.len(~F, p) == o : Nat}, h: {M.len(~F, C.app(~F, p, r)) == o : Nat}) -> {r == Nil{} : M.Vec(~F)}:
  match p o:
    case Nil{} 0n:
      rnil.r(~F, r, h)
    case Nil{} 1n++k:
      FO.absurd({r == Nil{} : M.Vec(~F)}, FV.zero_ne(k, hp))
    case Con{a, +ps} 0n:
      FO.absurd({r == Nil{} : M.Vec(~F)}, FV.succ_ne(M.len(~F, ps), hp))
    case Con{a, +ps} 1n++k:
      rnil(~F, ps, r, k, FV.succ_inj(M.len(~F, ps), k, hp), FV.succ_inj(M.len(~F, C.app(~F, ps, r)), k, h))

# two points of the box that solve the remaining equations and share the
# prefix p agree
def walk_un(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), bs: List<&2, PL.PBlock<K>>, +es: List<&2, E.QExpr>, +o: Nat, +p: M.Vec(~F), +hw: {PL.walk(~K, gc, gr, bs, es, o) == True{} : Bool}, +hpb: pbox(~K, ~F, ~H, gc, gr, o, p), +hgr: {KA.klen(~K, gr) == KA.klen(~K, gc) : Nat}, +r1: M.Vec(~F), +r2: M.Vec(~F), +h1: BX.inbox(~K, ~F, ~H, gc, gr, C.app(~F, p, r1)), +z1: SK.Zeros(~F, C.app(~F, p, r1), es), +h2: BX.inbox(~K, ~F, ~H, gc, gr, C.app(~F, p, r2)), +z2: SK.Zeros(~F, C.app(~F, p, r2), es)) -> {r1 == r2 : M.Vec(~F)}:
  match bs:
    case Nil{}:
      +ho = CP.nateq_ok(o, KA.klen(~K, gc), KA.band_l(KA.nateq(o, KA.klen(~K, gc)), PL.isnil(es), hw))
      +hlp = pbox_len(~K, ~F, ~H, gc, gr, o, p, hpb)
      +hv = Equal.sym(Nat, o, KA.klen(~K, gc), ho)
      +l1 = Equal.trans(Nat, M.len(~F, C.app(~F, p, r1)), KA.klen(~K, gc), o, Equal.trans(Nat, M.len(~F, C.app(~F, p, r1)), M.len(~F, N.ofkv(~K, ~F, ~H, gc)), KA.klen(~K, gc), inbox_len(~K, ~F, ~H, gc, gr, C.app(~F, p, r1), h1), CP.len_ofkv(~K, ~F, ~H, gc)), hv)
      +l2 = Equal.trans(Nat, M.len(~F, C.app(~F, p, r2)), KA.klen(~K, gc), o, Equal.trans(Nat, M.len(~F, C.app(~F, p, r2)), M.len(~F, N.ofkv(~K, ~F, ~H, gc)), KA.klen(~K, gc), inbox_len(~K, ~F, ~H, gc, gr, C.app(~F, p, r2), h2), CP.len_ofkv(~K, ~F, ~H, gc)), hv)
      Equal.trans(M.Vec(~F), r1, Nil{}, r2, rnil(~F, p, r1, o, hlp, l1), Equal.sym(M.Vec(~F), r2, Nil{}, rnil(~F, p, r2, o, hlp, l2)))
    case Con{PL.PBlock{+n, +pars, +c}, +t}:
      +hbo = KA.band_l(PL.block_ok(~K, gc, gr, es, o, n, pars, c), PL.walk(~K, gc, gr, t, PL.dropq(n, es), Nat.add(o, n)), hw)
      +hrest = KA.band_r(PL.block_ok(~K, gc, gr, es, o, n, pars, c), PL.walk(~K, gc, gr, t, PL.dropq(n, es), Nat.add(o, n)), hw)
      +hlp = pbox_len(~K, ~F, ~H, gc, gr, o, p, hpb)
      +hgc = bo_in_box(~K, gc, gr, es, o, n, pars, c, hbo)
      +hgo = natle_addl(o, n, KA.klen(~K, gc), hgc)
      +s1 = side_facts(~K, ~F, ~H, gc, gr, es, o, n, pars, c, hbo, p, hlp, hgr, r1, h1, z1)
      +s2 = side_facts(~K, ~F, ~H, gc, gr, es, o, n, pars, c, hbo, p, hlp, hgr, r2, h2, z2)
      +y1 = ftake(~F, n, r1)
      +y2 = ftake(~F, n, r2)
      +q1 = fdrop(~F, n, r1)
      +q2 = fdrop(~F, n, r2)
      +z = zmap(~F, p, pars)
      +hz = pin_pc(~K, ~F, ~H, gc, gr, o, p, hpb, hgo, pars, C.Cert.pc(K, c), C.Cert.pr(K, c), bo_pars(~K, gc, gr, es, o, n, pars, c, hbo), bo_pcont(~K, gc, gr, es, o, n, pars, c, hbo))
      +hu = CP.cert_unique(~K, ~F, ~H, blk(o, n, pars, es), c, bo_cert(~K, gc, gr, es, o, n, pars, c, hbo), z, hz, y1, sd_ball(~K, ~F, ~H, gc, gr, es, o, n, pars, c, p, r1, s1), sd_zero(~K, ~F, ~H, gc, gr, es, o, n, pars, c, p, r1, s1), y2, sd_ball(~K, ~F, ~H, gc, gr, es, o, n, pars, c, p, r2, s2), sd_zero(~K, ~F, ~H, gc, gr, es, o, n, pars, c, p, r2, s2))
      +eqy = eq_of_vall(~F, y1, y2, vall_of_vbnd(~F, C.vsub(~F, y1, y2), O.zero(F), hu), Equal.trans(Nat, M.len(~F, y1), n, M.len(~F, y2), sd_len(~K, ~F, ~H, gc, gr, es, o, n, pars, c, p, r1, s1), Equal.sym(Nat, M.len(~F, y2), n, sd_len(~K, ~F, ~H, gc, gr, es, o, n, pars, c, p, r2, s2))))
      +py = C.app(~F, p, y1)
      +hlpy = Equal.trans(Nat, M.len(~F, py), Nat.add(M.len(~F, p), M.len(~F, y1)), Nat.add(o, n), len_app(~F, p, y1), add2(M.len(~F, p), o, M.len(~F, y1), n, hlp, sd_len(~K, ~F, ~H, gc, gr, es, o, n, pars, c, p, r1, s1)))
      +hpb2 = pbox_of_inbox(~K, ~F, ~H, gc, gr, Nat.add(o, n), py, q1, sd_in(~K, ~F, ~H, gc, gr, es, o, n, pars, c, p, r1, s1), hlpy, hgc, hgr)
      +e2 = app3_rw(~F, p, y2, y1, q2, Equal.sym(M.Vec(~F), y1, y2, eqy))
      +rec = walk_un(~K, ~F, ~H, gc, gr, t, PL.dropq(n, es), Nat.add(o, n), py, hrest, hpb2, hgr, q1, q2, sd_in(~K, ~F, ~H, gc, gr, es, o, n, pars, c, p, r1, s1), sd_zs(~K, ~F, ~H, gc, gr, es, o, n, pars, c, p, r1, s1), inbox_rw(~K, ~F, ~H, gc, gr, C.app(~F, C.app(~F, p, y2), q2), C.app(~F, py, q2), e2, sd_in(~K, ~F, ~H, gc, gr, es, o, n, pars, c, p, r2, s2)), zeros_rw(~F, C.app(~F, C.app(~F, p, y2), q2), C.app(~F, py, q2), PL.dropq(n, es), e2, sd_zs(~K, ~F, ~H, gc, gr, es, o, n, pars, c, p, r2, s2)))
      td_eq(~F, n, r1, r2, eqy, rec)

# radius 0 pins a coordinate to its center
def pin_one(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +a: O.C(F), +g: N.NC(K), +r: N.NC(K), h: M.bnd(~F, O.sub(~F, a, N.emap(K, F, H, g)), N.emap(K, F, H, r)), hr: {PL.keq(~K, r, N.nzero(K)) == True{} : Bool}) -> {a == N.emap(K, F, H, g) : O.C(F)}:
  +e0 = Equal.trans(O.C(F), N.emap(K, F, H, r), N.emap(K, F, H, N.nzero(K)), O.zero(F), keq_ok(~K, ~F, ~H, r, N.nzero(K), hr), N.e_zero(K, F, H))
  FO.eq_of_sub(~F, a, N.emap(K, F, H, g), RL.bnd0_eq(~F, O.sub(~F, a, N.emap(K, F, H, g)), BA.bnd_rw_s(~F, O.sub(~F, a, N.emap(K, F, H, g)), N.emap(K, F, H, r), O.zero(F), e0, h)))

def pin_prefix.c(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +k: Nat, +g: N.NC(K), +gs: N.KVec(~K), x: M.Vec(~F), gr: N.KVec(~K), h: C.rbnd(~F, C.vsub(~F, x, N.ofkv(~K, ~F, ~H, Con{g, gs})), N.ofkv(~K, ~F, ~H, gr)), +hpz: {PL.pinz(~K, 1n+k, gr) == True{} : Bool}, hlx: {M.len(~F, x) == M.len(~F, N.ofkv(~K, ~F, ~H, Con{g, gs})) : Nat}, ih: @xs: M.Vec(~F) -> @rs: N.KVec(~K) -> C.rbnd(~F, C.vsub(~F, xs, N.ofkv(~K, ~F, ~H, gs)), N.ofkv(~K, ~F, ~H, rs)) -> {PL.pinz(~K, k, rs) == True{} : Bool} -> {M.len(~F, xs) == M.len(~F, N.ofkv(~K, ~F, ~H, gs)) : Nat} -> {ftake(~F, k, xs) == N.ofkv(~K, ~F, ~H, PL.ktake(~K, k, gs)) : M.Vec(~F)}) -> {ftake(~F, 1n+k, x) == N.ofkv(~K, ~F, ~H, PL.ktake(~K, 1n+k, Con{g, gs})) : M.Vec(~F)}:
  match x gr:
    case Nil{} gr:
      FO.absurd({Nil{} == N.ofkv(~K, ~F, ~H, PL.ktake(~K, 1n+k, Con{g, gs})) : M.Vec(~F)}, FV.zero_ne(M.len(~F, N.ofkv(~K, ~F, ~H, gs)), hlx))
    case Con{+a, +xs} Nil{}:
      FO.absurd({ftake(~F, 1n+k, Con{a, xs}) == N.ofkv(~K, ~F, ~H, PL.ktake(~K, 1n+k, Con{g, gs})) : M.Vec(~F)}, KA.ft(hpz))
    case Con{+a, +xs} Con{+r, +rs}:
      (ha, hs) = h
      %Equal.sym(O.C(F), a, N.emap(K, F, H, g), pin_one(~K, ~F, ~H, a, g, r, ha, KA.band_l(PL.keq(~K, r, N.nzero(K)), PL.pinz(~K, k, rs), hpz))) : {Con{_, ftake(~F, k, xs)} == Con{N.emap(K, F, H, g), N.ofkv(~K, ~F, ~H, PL.ktake(~K, k, gs))} : M.Vec(~F)}
      %Equal.sym(M.Vec(~F), ftake(~F, k, xs), N.ofkv(~K, ~F, ~H, PL.ktake(~K, k, gs)), ih(xs, rs, hs, KA.band_r(PL.keq(~K, r, N.nzero(K)), PL.pinz(~K, k, rs), hpz), FV.succ_inj(M.len(~F, xs), M.len(~F, N.ofkv(~K, ~F, ~H, gs)), hlx))) : {Con{N.emap(K, F, H, g), _} == Con{N.emap(K, F, H, g), N.ofkv(~K, ~F, ~H, PL.ktake(~K, k, gs))} : M.Vec(~F)}
      {==}

# a point of the box starts with the pinned centers
def pin_prefix(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, np: Nat, gc: N.KVec(~K), x: M.Vec(~F), gr: N.KVec(~K), h: C.rbnd(~F, C.vsub(~F, x, N.ofkv(~K, ~F, ~H, gc)), N.ofkv(~K, ~F, ~H, gr)), hpz: {PL.pinz(~K, np, gr) == True{} : Bool}, hn: {KA.natle(np, KA.klen(~K, gc)) == True{} : Bool}, hlx: {M.len(~F, x) == M.len(~F, N.ofkv(~K, ~F, ~H, gc)) : Nat}) -> {ftake(~F, np, x) == N.ofkv(~K, ~F, ~H, PL.ktake(~K, np, gc)) : M.Vec(~F)}:
  match np gc:
    case 0n gc:
      {==}
    case 1n+k Nil{}:
      FO.absurd({ftake(~F, 1n+k, x) == Nil{} : M.Vec(~F)}, KA.ft(hn))
    case 1n++k Con{+g, +gs}:
      pin_prefix.c(~K, ~F, ~H, k, g, gs, x, gr, h, hpz, hlx, xs => rs => hs => hz => hl => pin_prefix(~K, ~F, ~H, k, gs, xs, rs, hs, hz, hn, hl))

def inbox_rb(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +x: M.Vec(~F), h: BX.inbox(~K, ~F, ~H, gc, gr, x)) -> C.rbnd(~F, C.vsub(~F, x, N.ofkv(~K, ~F, ~H, gc)), N.ofkv(~K, ~F, ~H, gr)):
  (hl, hr) = h
  hr

# x = p0 ++ drop np x, for x in the box
def x_pins(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +np: Nat, +bs: List<&2, PL.PBlock<K>>, +ok: {PL.check.p(~K, eqs, gc, gr, np, bs) == True{} : Bool}, +x: M.Vec(~F), +h: BX.inbox(~K, ~F, ~H, gc, gr, x)) -> {x == C.app(~F, p0(~K, ~F, ~H, gc, np), fdrop(~F, np, x)) : M.Vec(~F)}:
  %pin_prefix(~K, ~F, ~H, np, gc, x, gr, inbox_rb(~K, ~F, ~H, gc, gr, x, h), cp_pinz(~K, eqs, gc, gr, np, bs, ok), cp_np(~K, eqs, gc, gr, np, bs, ok), inbox_len(~K, ~F, ~H, gc, gr, x, h)) : {x == C.app(~F, _, fdrop(~F, np, x)) : M.Vec(~F)}
  Equal.sym(M.Vec(~F), C.app(~F, ftake(~F, np, x), fdrop(~F, np, x)), x, app_td(~F, np, x))

def plan_unique.p(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +np: Nat, +bs: List<&2, PL.PBlock<K>>, +ok: {PL.check.p(~K, eqs, gc, gr, np, bs) == True{} : Bool}, +x1: M.Vec(~F), +h1: BX.inbox(~K, ~F, ~H, gc, gr, x1), z1: SK.Zeros(~F, x1, eqs), +x2: M.Vec(~F), +h2: BX.inbox(~K, ~F, ~H, gc, gr, x2), z2: SK.Zeros(~F, x2, eqs)) -> {x1 == x2 : M.Vec(~F)}:
  +pz = p0(~K, ~F, ~H, gc, np)
  +d1 = fdrop(~F, np, x1)
  +d2 = fdrop(~F, np, x2)
  +e1 = x_pins(~K, ~F, ~H, eqs, gc, gr, np, bs, ok, x1, h1)
  +e2 = x_pins(~K, ~F, ~H, eqs, gc, gr, np, bs, ok, x2, h2)
  +ed = walk_un(~K, ~F, ~H, gc, gr, bs, eqs, np, pz, cp_walk(~K, eqs, gc, gr, np, bs, ok), pbox0(~K, ~F, ~H, eqs, gc, gr, np, bs, ok), cp_len(~K, eqs, gc, gr, np, bs, ok), d1, d2, inbox_rw(~K, ~F, ~H, gc, gr, x1, C.app(~F, pz, d1), e1, h1), zeros_rw(~F, x1, C.app(~F, pz, d1), eqs, e1, z1), inbox_rw(~K, ~F, ~H, gc, gr, x2, C.app(~F, pz, d2), e2, h2), zeros_rw(~F, x2, C.app(~F, pz, d2), eqs, e2, z2))
  %Equal.sym(M.Vec(~F), x2, C.app(~F, pz, d2), e2) : {x1 == _ : M.Vec(~F)}
  %Equal.sym(M.Vec(~F), x1, C.app(~F, pz, d1), e1) : {_ == C.app(~F, pz, d2) : M.Vec(~F)}
  %ed : {C.app(~F, pz, d1) == C.app(~F, pz, _) : M.Vec(~F)}
  {==}

# Systems in another order
# ------------------------

def cr_r0(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}) -> {KA.band(PL.present(vp, KA.klen(~K, gc), 0n), KA.band(PL.pars_ok(KA.klen(~K, gc), vp), KA.band(PL.present(ep, CK.eqlen(eqs), 0n), KA.band(PL.pars_ok(CK.eqlen(eqs), ep), KA.band(PL.eqs_below(KA.klen(~K, gc), eqs), PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs)))))) == True{} : Bool}:
  h

def cr_r1(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}) -> {KA.band(PL.pars_ok(KA.klen(~K, gc), vp), KA.band(PL.present(ep, CK.eqlen(eqs), 0n), KA.band(PL.pars_ok(CK.eqlen(eqs), ep), KA.band(PL.eqs_below(KA.klen(~K, gc), eqs), PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs))))) == True{} : Bool}:
  KA.band_r(PL.present(vp, KA.klen(~K, gc), 0n), KA.band(PL.pars_ok(KA.klen(~K, gc), vp), KA.band(PL.present(ep, CK.eqlen(eqs), 0n), KA.band(PL.pars_ok(CK.eqlen(eqs), ep), KA.band(PL.eqs_below(KA.klen(~K, gc), eqs), PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs))))), cr_r0(~K, eqs, gc, gr, vp, ep, np, bs, h))

def cr_r2(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}) -> {KA.band(PL.present(ep, CK.eqlen(eqs), 0n), KA.band(PL.pars_ok(CK.eqlen(eqs), ep), KA.band(PL.eqs_below(KA.klen(~K, gc), eqs), PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs)))) == True{} : Bool}:
  KA.band_r(PL.pars_ok(KA.klen(~K, gc), vp), KA.band(PL.present(ep, CK.eqlen(eqs), 0n), KA.band(PL.pars_ok(CK.eqlen(eqs), ep), KA.band(PL.eqs_below(KA.klen(~K, gc), eqs), PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs)))), cr_r1(~K, eqs, gc, gr, vp, ep, np, bs, h))

def cr_r3(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}) -> {KA.band(PL.pars_ok(CK.eqlen(eqs), ep), KA.band(PL.eqs_below(KA.klen(~K, gc), eqs), PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs))) == True{} : Bool}:
  KA.band_r(PL.present(ep, CK.eqlen(eqs), 0n), KA.band(PL.pars_ok(CK.eqlen(eqs), ep), KA.band(PL.eqs_below(KA.klen(~K, gc), eqs), PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs))), cr_r2(~K, eqs, gc, gr, vp, ep, np, bs, h))

def cr_r4(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}) -> {KA.band(PL.eqs_below(KA.klen(~K, gc), eqs), PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs)) == True{} : Bool}:
  KA.band_r(PL.pars_ok(CK.eqlen(eqs), ep), KA.band(PL.eqs_below(KA.klen(~K, gc), eqs), PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs)), cr_r3(~K, eqs, gc, gr, vp, ep, np, bs, h))

def cr_r5(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}) -> {PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs) == True{} : Bool}:
  KA.band_r(PL.eqs_below(KA.klen(~K, gc), eqs), PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs), cr_r4(~K, eqs, gc, gr, vp, ep, np, bs, h))

def cr_vp_has(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}) -> {PL.present(vp, KA.klen(~K, gc), 0n) == True{} : Bool}:
  KA.band_l(PL.present(vp, KA.klen(~K, gc), 0n), KA.band(PL.pars_ok(KA.klen(~K, gc), vp), KA.band(PL.present(ep, CK.eqlen(eqs), 0n), KA.band(PL.pars_ok(CK.eqlen(eqs), ep), KA.band(PL.eqs_below(KA.klen(~K, gc), eqs), PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs))))), cr_r0(~K, eqs, gc, gr, vp, ep, np, bs, h))

def cr_vp_lt(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}) -> {PL.pars_ok(KA.klen(~K, gc), vp) == True{} : Bool}:
  KA.band_l(PL.pars_ok(KA.klen(~K, gc), vp), KA.band(PL.present(ep, CK.eqlen(eqs), 0n), KA.band(PL.pars_ok(CK.eqlen(eqs), ep), KA.band(PL.eqs_below(KA.klen(~K, gc), eqs), PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs)))), cr_r1(~K, eqs, gc, gr, vp, ep, np, bs, h))

def cr_ep_has(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}) -> {PL.present(ep, CK.eqlen(eqs), 0n) == True{} : Bool}:
  KA.band_l(PL.present(ep, CK.eqlen(eqs), 0n), KA.band(PL.pars_ok(CK.eqlen(eqs), ep), KA.band(PL.eqs_below(KA.klen(~K, gc), eqs), PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs))), cr_r2(~K, eqs, gc, gr, vp, ep, np, bs, h))

def cr_ep_lt(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}) -> {PL.pars_ok(CK.eqlen(eqs), ep) == True{} : Bool}:
  KA.band_l(PL.pars_ok(CK.eqlen(eqs), ep), KA.band(PL.eqs_below(KA.klen(~K, gc), eqs), PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs)), cr_r3(~K, eqs, gc, gr, vp, ep, np, bs, h))

def cr_below(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}) -> {PL.eqs_below(KA.klen(~K, gc), eqs) == True{} : Bool}:
  KA.band_l(PL.eqs_below(KA.klen(~K, gc), eqs), PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs), cr_r4(~K, eqs, gc, gr, vp, ep, np, bs, h))

def cr_inner(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +h: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}) -> {PL.check.p(~K, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs) == True{} : Bool}:
  cr_r5(~K, eqs, gc, gr, vp, ep, np, bs, h)

def present_at(+xs: List<&2, Nat>, cnt: Nat, +i0: Nat, k: Nat, h: {PL.present(xs, cnt, i0) == True{} : Bool}, hk: {KA.natle(1n+k, cnt) == True{} : Bool}) -> {KA.natle(1n+PL.pos(Nat.add(k, i0), xs), PL.nlen(xs)) == True{} : Bool}:
  match cnt k:
    case 0n k:
      FO.absurd({KA.natle(1n+PL.pos(Nat.add(k, i0), xs), PL.nlen(xs)) == True{} : Bool}, KA.ft(hk))
    case 1n++c 0n:
      KA.band_l(KA.natle(1n+PL.pos(i0, xs), PL.nlen(xs)), PL.present(xs, c, 1n+i0), h)
    case 1n++c 1n++j:
      %Equal.sym(Nat, 1n+Nat.add(j, i0), Nat.add(j, 1n+i0), LN.add_succ(j, i0)) : {KA.natle(1n+PL.pos(_, xs), PL.nlen(xs)) == True{} : Bool}
      present_at(xs, c, 1n+i0, j, KA.band_r(KA.natle(1n+PL.pos(i0, xs), PL.nlen(xs)), PL.present(xs, c, 1n+i0), h), hk)

# every v below cnt appears in xs
def present0(+xs: List<&2, Nat>, +cnt: Nat, +v: Nat, h: {PL.present(xs, cnt, 0n) == True{} : Bool}, hv: {KA.natle(1n+v, cnt) == True{} : Bool}) -> {KA.natle(1n+PL.pos(v, xs), PL.nlen(xs)) == True{} : Bool}:
  %Equal.sym(Nat, v, Nat.add(v, 0n), LN.add_zero(v)) : {KA.natle(1n+PL.pos(_, xs), PL.nlen(xs)) == True{} : Bool}
  present_at(xs, cnt, 0n, v, h, hv)

# every listed number is below o
def pars_at(+o: Nat, xs: List<&2, Nat>, k: Nat, h: {PL.pars_ok(o, xs) == True{} : Bool}, hk: {KA.natle(1n+k, PL.nlen(xs)) == True{} : Bool}) -> {KA.natle(1n+PL.nthn(xs, k), o) == True{} : Bool}:
  match xs k:
    case Nil{} k:
      FO.absurd({KA.natle(1n+PL.nthn(Nil{}, k), o) == True{} : Bool}, KA.ft(hk))
    case Con{+v, +t} 0n:
      KA.band_l(KA.natle(1n+v, o), PL.pars_ok(o, t), h)
    case Con{+v, +t} 1n+j:
      pars_at(o, t, j, KA.band_r(KA.natle(1n+v, o), PL.pars_ok(o, t), h), hk)

def below_at(+m: Nat, es: List<&2, E.QExpr>, j: Nat, h: {PL.eqs_below(m, es) == True{} : Bool}, hj: {KA.natle(1n+j, CK.eqlen(es)) == True{} : Bool}) -> {SL.below(m, PL.eqget(es, j)) == True{} : Bool}:
  match es j:
    case Nil{} j:
      FO.absurd({SL.below(m, PL.eqget(Nil{}, j)) == True{} : Bool}, KA.ft(hj))
    case Con{+e, +t} 0n:
      KA.band_l(SL.below(m, e), PL.eqs_below(m, t), h)
    case Con{+e, +t} 1n+k:
      below_at(m, t, k, KA.band_r(SL.below(m, e), PL.eqs_below(m, t), h), hj)

def eqget_reorder(+vp: List<&2, Nat>, +es: List<&2, E.QExpr>, ep: List<&2, Nat>, k: Nat, hk: {KA.natle(1n+k, PL.nlen(ep)) == True{} : Bool}) -> {PL.eqget(PL.reorder(vp, es, ep), k) == PL.rnv(vp, PL.eqget(es, PL.nthn(ep, k))) : E.QExpr}:
  match ep k:
    case Nil{} k:
      FO.absurd({PL.eqget(Nil{}, k) == PL.rnv(vp, PL.eqget(es, PL.nthn(Nil{}, k))) : E.QExpr}, KA.ft(hk))
    case Con{j, t} 0n:
      {==}
    case Con{j, t} 1n+i:
      eqget_reorder(vp, es, t, i, hk)

def len_reorder(+vp: List<&2, Nat>, +es: List<&2, E.QExpr>, ep: List<&2, Nat>) -> {CK.eqlen(PL.reorder(vp, es, ep)) == PL.nlen(ep) : Nat}:
  match ep:
    case Nil{}:
      {==}
    case Con{j, t}:
      %Equal.sym(Nat, CK.eqlen(PL.reorder(vp, es, t)), PL.nlen(t), len_reorder(vp, es, t)) : {1n+_ == 1n+PL.nlen(t) : Nat}
      {==}

def klook_kperm(~K: N.Num, +u: N.KVec(~K), vp: List<&2, Nat>, k: Nat, hk: {KA.natle(1n+k, PL.nlen(vp)) == True{} : Bool}) -> {KB.klook(~K, PL.kperm(~K, u, vp), k) == KB.klook(~K, u, PL.nthn(vp, k)) : N.NC(K)}:
  match vp k:
    case Nil{} k:
      FO.absurd({KB.klook(~K, Nil{}, k) == KB.klook(~K, u, PL.nthn(Nil{}, k)) : N.NC(K)}, KA.ft(hk))
    case Con{v, t} 0n:
      {==}
    case Con{v, t} 1n+i:
      klook_kperm(~K, u, t, i, hk)

def klen_kperm(~K: N.Num, +u: N.KVec(~K), vp: List<&2, Nat>) -> {KA.klen(~K, PL.kperm(~K, u, vp)) == PL.nlen(vp) : Nat}:
  match vp:
    case Nil{}:
      {==}
    case Con{v, t}:
      %Equal.sym(Nat, KA.klen(~K, PL.kperm(~K, u, t)), PL.nlen(t), klen_kperm(~K, u, t)) : {1n+_ == 1n+PL.nlen(t) : Nat}
      {==}

# renaming by positions in vp preserves evaluation, when x2 at v's position
# is x at v for every v below m
def ren_eval(~F: O.OField, ~x: M.Vec(~F), ~x2: M.Vec(~F), ~vp: List<&2, Nat>, ~m: Nat, ~f: @v: Nat -> {KA.natle(1n+v, m) == True{} : Bool} -> {O.lookup(~F, x2, PL.pos(v, vp)) == O.lookup(~F, x, v) : O.C(F)}, e: E.QExpr, +hb: {SL.below(m, e) == True{} : Bool}) -> {O.eval(~F, x2, PL.rnv(vp, e)) == O.eval(~F, x, e) : O.C(F)}:
  match e:
    case E.QVar{+v}:
      f(v, hb)
    case E.QCst{q}:
      {==}
    case E.QAdd{+a, +b}:
      cadd(~F, O.eval(~F, x2, PL.rnv(vp, a)), O.eval(~F, x, a), O.eval(~F, x2, PL.rnv(vp, b)), O.eval(~F, x, b), ren_eval(~F, ~x, ~x2, ~vp, ~m, ~f, a, KA.band_l(SL.below(m, a), SL.below(m, b), hb)), ren_eval(~F, ~x, ~x2, ~vp, ~m, ~f, b, KA.band_r(SL.below(m, a), SL.below(m, b), hb)))
    case E.QSub{+a, +b}:
      csub(~F, O.eval(~F, x2, PL.rnv(vp, a)), O.eval(~F, x, a), O.eval(~F, x2, PL.rnv(vp, b)), O.eval(~F, x, b), ren_eval(~F, ~x, ~x2, ~vp, ~m, ~f, a, KA.band_l(SL.below(m, a), SL.below(m, b), hb)), ren_eval(~F, ~x, ~x2, ~vp, ~m, ~f, b, KA.band_r(SL.below(m, a), SL.below(m, b), hb)))
    case E.QMul{+a, +b}:
      cmul(~F, O.eval(~F, x2, PL.rnv(vp, a)), O.eval(~F, x, a), O.eval(~F, x2, PL.rnv(vp, b)), O.eval(~F, x, b), ren_eval(~F, ~x, ~x2, ~vp, ~m, ~f, a, KA.band_l(SL.below(m, a), SL.below(m, b), hb)), ren_eval(~F, ~x, ~x2, ~vp, ~m, ~f, b, KA.band_r(SL.below(m, a), SL.below(m, b), hb)))
    case E.QNeg{+a}:
      cneg(~F, O.eval(~F, x2, PL.rnv(vp, a)), O.eval(~F, x, a), ren_eval(~F, ~x, ~x2, ~vp, ~m, ~f, a, hb))

# Zeros by index
# --------------

def zeros_at(~F: O.OField, +x: M.Vec(~F), es: List<&2, E.QExpr>, j: Nat, h: SK.Zeros(~F, x, es), hj: {KA.natle(1n+j, CK.eqlen(es)) == True{} : Bool}) -> {O.eval(~F, x, PL.eqget(es, j)) == O.zero(F) : O.C(F)}:
  match es j:
    case Nil{} j:
      FO.absurd({O.eval(~F, x, PL.eqget(Nil{}, j)) == O.zero(F) : O.C(F)}, KA.ft(hj))
    case Con{+e, +t} 0n:
      (h0, ht) = h
      h0
    case Con{+e, +t} 1n+k:
      (h0, ht) = h
      zeros_at(~F, x, t, k, ht, hj)

# equations cnt from i0 vanish
def zall(~F: O.OField, +x: M.Vec(~F), +es: List<&2, E.QExpr>, cnt: Nat, +i0: Nat) -> Data:
  match cnt:
    case 0n:
      Unit
    case 1n+c:
      M.Both({O.eval(~F, x, PL.eqget(es, i0)) == O.zero(F) : O.C(F)}, zall(~F, x, es, c, 1n+i0))

def zeros_build(~F: O.OField, ~x: M.Vec(~F), ~es: List<&2, E.QExpr>, ~f: @j: Nat -> {KA.natle(1n+j, CK.eqlen(es)) == True{} : Bool} -> {O.eval(~F, x, PL.eqget(es, j)) == O.zero(F) : O.C(F)}, cnt: Nat, +i0: Nat, +e: {Nat.add(cnt, i0) == CK.eqlen(es) : Nat}) -> zall(~F, x, es, cnt, i0):
  match cnt:
    case 0n:
      Unit{}
    case 1n++c:
      (f(i0, BA.natle_of(c, i0, CK.eqlen(es), e)), zeros_build(~F, ~x, ~es, ~f, c, 1n+i0, BA.lk_next(c, i0, CK.eqlen(es), e)))

def zall_shift(~F: O.OField, +x: M.Vec(~F), +e: E.QExpr, +t: List<&2, E.QExpr>, cnt: Nat, +i0: Nat, h: zall(~F, x, Con{e, t}, cnt, 1n+i0)) -> zall(~F, x, t, cnt, i0):
  match cnt:
    case 0n:
      Unit{}
    case 1n+c:
      (h0, hs) = h
      (h0, zall_shift(~F, x, e, t, c, 1n+i0, hs))

def zeros_of_zall(~F: O.OField, +x: M.Vec(~F), es: List<&2, E.QExpr>, h: zall(~F, x, es, CK.eqlen(es), 0n)) -> SK.Zeros(~F, x, es):
  match es:
    case Nil{}:
      Unit{}
    case Con{+e, +t}:
      (h0, hs) = h
      (h0, zeros_of_zall(~F, x, t, zall_shift(~F, x, e, t, CK.eqlen(t), 0n, hs)))

# The assignment in the original order
# ------------------------------------

# x2 read back: variable v of the system is x2 at v's position in vp
def upm(~F: O.OField, +x2: M.Vec(~F), +vp: List<&2, Nat>, cnt: Nat, +i0: Nat) -> M.Vec(~F):
  match cnt:
    case 0n:
      Nil{}
    case 1n+c:
      Con{O.lookup(~F, x2, PL.pos(i0, vp)), upm(~F, x2, vp, c, 1n+i0)}

def len_upm(~F: O.OField, +x2: M.Vec(~F), +vp: List<&2, Nat>, cnt: Nat, +i0: Nat) -> {M.len(~F, upm(~F, x2, vp, cnt, i0)) == cnt : Nat}:
  match cnt:
    case 0n:
      {==}
    case 1n++c:
      %Equal.sym(Nat, M.len(~F, upm(~F, x2, vp, c, 1n+i0)), c, len_upm(~F, x2, vp, c, 1n+i0)) : {1n+_ == 1n+c : Nat}
      {==}

def look_upm(~F: O.OField, +x2: M.Vec(~F), +vp: List<&2, Nat>, cnt: Nat, +i0: Nat, k: Nat, hk: {KA.natle(1n+k, cnt) == True{} : Bool}) -> {O.lookup(~F, upm(~F, x2, vp, cnt, i0), k) == O.lookup(~F, x2, PL.pos(Nat.add(k, i0), vp)) : O.C(F)}:
  match cnt k:
    case 0n k:
      FO.absurd({O.zero(F) == O.lookup(~F, x2, PL.pos(Nat.add(k, i0), vp)) : O.C(F)}, KA.ft(hk))
    case 1n+c 0n:
      {==}
    case 1n+c 1n++j:
      %Equal.sym(Nat, 1n+Nat.add(j, i0), Nat.add(j, 1n+i0), LN.add_succ(j, i0)) : {O.lookup(~F, upm(~F, x2, vp, c, 1n+i0), j) == O.lookup(~F, x2, PL.pos(_, vp)) : O.C(F)}
      look_upm(~F, x2, vp, c, 1n+i0, j, hk)

def look_upm0(~F: O.OField, +x2: M.Vec(~F), +vp: List<&2, Nat>, +cnt: Nat, +v: Nat, hv: {KA.natle(1n+v, cnt) == True{} : Bool}) -> {O.lookup(~F, x2, PL.pos(v, vp)) == O.lookup(~F, upm(~F, x2, vp, cnt, 0n), v) : O.C(F)}:
  %Equal.sym(Nat, v, Nat.add(v, 0n), LN.add_zero(v)) : {O.lookup(~F, x2, PL.pos(_, vp)) == O.lookup(~F, upm(~F, x2, vp, cnt, 0n), v) : O.C(F)}
  Equal.sym(O.C(F), O.lookup(~F, upm(~F, x2, vp, cnt, 0n), v), O.lookup(~F, x2, PL.pos(Nat.add(v, 0n), vp)), look_upm(~F, x2, vp, cnt, 0n, v, hv))

def klook_rw(~K: N.Num, +u: N.KVec(~K), +i: Nat, +j: Nat, e: {i == j : Nat}) -> {KB.klook(~K, u, i) == KB.klook(~K, u, j) : N.NC(K)}:
  %e : {KB.klook(~K, u, i) == KB.klook(~K, u, _) : N.NC(K)}
  {==}

def eval_rw(~F: O.OField, +x: M.Vec(~F), +a: E.QExpr, +b: E.QExpr, e: {a == b : E.QExpr}) -> {O.eval(~F, x, a) == O.eval(~F, x, b) : O.C(F)}:
  %e : {O.eval(~F, x, a) == O.eval(~F, x, _) : O.C(F)}
  {==}

def rnv_rw(+vp: List<&2, Nat>, +es: List<&2, E.QExpr>, +i: Nat, +j: Nat, e: {i == j : Nat}) -> {PL.rnv(vp, PL.eqget(es, i)) == PL.rnv(vp, PL.eqget(es, j)) : E.QExpr}:
  %e : {PL.rnv(vp, PL.eqget(es, i)) == PL.rnv(vp, PL.eqget(es, _)) : E.QExpr}
  {==}

# the reordered box at position k is the box at variable vp_k
def kperm_at(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +u: N.KVec(~K), +vp: List<&2, Nat>, +k: Nat, hk: {KA.natle(1n+k, PL.nlen(vp)) == True{} : Bool}) -> {O.lookup(~F, N.ofkv(~K, ~F, ~H, PL.kperm(~K, u, vp)), k) == O.lookup(~F, N.ofkv(~K, ~F, ~H, u), PL.nthn(vp, k)) : O.C(F)}:
  Equal.trans(O.C(F), O.lookup(~F, N.ofkv(~K, ~F, ~H, PL.kperm(~K, u, vp)), k), N.emap(K, F, H, KB.klook(~K, PL.kperm(~K, u, vp), k)), O.lookup(~F, N.ofkv(~K, ~F, ~H, u), PL.nthn(vp, k)), Equal.sym(O.C(F), N.emap(K, F, H, KB.klook(~K, PL.kperm(~K, u, vp), k)), O.lookup(~F, N.ofkv(~K, ~F, ~H, PL.kperm(~K, u, vp)), k), CP.klook_ofk(~K, ~F, ~H, PL.kperm(~K, u, vp), k)),
    Equal.trans(O.C(F), N.emap(K, F, H, KB.klook(~K, PL.kperm(~K, u, vp), k)), N.emap(K, F, H, KB.klook(~K, u, PL.nthn(vp, k))), O.lookup(~F, N.ofkv(~K, ~F, ~H, u), PL.nthn(vp, k)), emap_rw(~K, ~F, ~H, KB.klook(~K, PL.kperm(~K, u, vp), k), KB.klook(~K, u, PL.nthn(vp, k)), klook_kperm(~K, u, vp, k, hk)), CP.klook_ofk(~K, ~F, ~H, u, PL.nthn(vp, k))))

def look_vec_rw(~F: O.OField, +x: M.Vec(~F), +i: Nat, +j: Nat, e: {i == j : Nat}) -> {O.lookup(~F, x, i) == O.lookup(~F, x, j) : O.C(F)}:
  %e : {O.lookup(~F, x, i) == O.lookup(~F, x, _) : O.C(F)}
  {==}

# |a - c| <= r carried along equalities of a, c and r
def btr(~F: O.OField, +a: O.C(F), +a2: O.C(F), +c: O.C(F), +c2: O.C(F), +r: O.C(F), +r2: O.C(F), ea: {a == a2 : O.C(F)}, ec: {c == c2 : O.C(F)}, er: {r == r2 : O.C(F)}, h: M.bnd(~F, O.sub(~F, a, c), r)) -> M.bnd(~F, O.sub(~F, a2, c2), r2):
  BA.bnd_rw_s(~F, O.sub(~F, a2, c2), r, r2, er, FV.bval(~F, O.sub(~F, a, c), O.sub(~F, a2, c2), r, csub(~F, a, a2, c, c2, ea, ec), h))

# the entry of a box bound, as |x_i - c_i| <= r_i
def ent(~F: O.OField, +x: M.Vec(~F), +c: M.Vec(~F), +r: M.Vec(~F), +i: Nat, +n: Nat, h: C.rbnd(~F, C.vsub(~F, x, c), r), hl: {M.len(~F, C.vsub(~F, x, c)) == n : Nat}, hi: {KA.natle(1n+i, n) == True{} : Bool}) -> M.bnd(~F, O.sub(~F, O.lookup(~F, x, i), O.lookup(~F, c, i)), O.lookup(~F, r, i)):
  FV.bval(~F, O.lookup(~F, C.vsub(~F, x, c), i), O.sub(~F, O.lookup(~F, x, i), O.lookup(~F, c, i)), O.lookup(~F, r, i), Equal.sym(O.C(F), O.sub(~F, O.lookup(~F, x, i), O.lookup(~F, c, i)), O.lookup(~F, C.vsub(~F, x, c), i), SL.lookup_vsub(~F, x, c, i)), BA.rbnd_look(~F, C.vsub(~F, x, c), r, h, n, hl, i, hi))

# and back
def unent(~F: O.OField, +x: M.Vec(~F), +c: M.Vec(~F), +r: M.Vec(~F), +i: Nat, h: M.bnd(~F, O.sub(~F, O.lookup(~F, x, i), O.lookup(~F, c, i)), O.lookup(~F, r, i))) -> M.bnd(~F, O.lookup(~F, C.vsub(~F, x, c), i), O.lookup(~F, r, i)):
  FV.bval(~F, O.sub(~F, O.lookup(~F, x, i), O.lookup(~F, c, i)), O.lookup(~F, C.vsub(~F, x, c), i), O.lookup(~F, r, i), SL.lookup_vsub(~F, x, c, i), h)

def inbox_lr(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +gc: N.KVec(~K), +gr: N.KVec(~K), +x: M.Vec(~F), +h: BX.inbox(~K, ~F, ~H, gc, gr, x)) -> {M.len(~F, C.vsub(~F, x, N.ofkv(~K, ~F, ~H, gc))) == KA.klen(~K, gc) : Nat}:
  +lg = CP.len_ofkv(~K, ~F, ~H, gc)
  CP.len_vsub(~F, x, N.ofkv(~K, ~F, ~H, gc), KA.klen(~K, gc), Equal.trans(Nat, M.len(~F, x), M.len(~F, N.ofkv(~K, ~F, ~H, gc)), KA.klen(~K, gc), inbox_len(~K, ~F, ~H, gc, gr, x, h), lg), lg)

# equation j of the system vanishes at the read-back assignment
def ex_zero(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +ok: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}, +x2: M.Vec(~F), +hz: SK.Zeros(~F, x2, PL.reorder(vp, eqs, ep)), +j: Nat, +hj: {KA.natle(1n+j, CK.eqlen(eqs)) == True{} : Bool}) -> {O.eval(~F, upm(~F, x2, vp, KA.klen(~K, gc), 0n), PL.eqget(eqs, j)) == O.zero(F) : O.C(F)}:
  +nv = KA.klen(~K, gc)
  +x = upm(~F, x2, vp, nv, 0n)
  +e2 = PL.reorder(vp, eqs, ep)
  +k = PL.pos(j, ep)
  +hk = present0(ep, CK.eqlen(eqs), j, cr_ep_has(~K, eqs, gc, gr, vp, ep, np, bs, ok), hj)
  +eq1 = Equal.trans(E.QExpr, PL.eqget(e2, k), PL.rnv(vp, PL.eqget(eqs, PL.nthn(ep, k))), PL.rnv(vp, PL.eqget(eqs, j)), eqget_reorder(vp, eqs, ep, k, hk), rnv_rw(vp, eqs, PL.nthn(ep, k), j, pos_nth(j, ep, hk)))
  +z0 = zeros_at(~F, x2, e2, k, hz, natle_rw(1n+k, PL.nlen(ep), CK.eqlen(e2), Equal.sym(Nat, CK.eqlen(e2), PL.nlen(ep), len_reorder(vp, eqs, ep)), hk))
  +ren = ren_eval(~F, ~x, ~x2, ~vp, ~nv, ~(v => hv => look_upm0(~F, x2, vp, nv, v, hv)), PL.eqget(eqs, j), below_at(nv, eqs, j, cr_below(~K, eqs, gc, gr, vp, ep, np, bs, ok), hj))
  Equal.trans(O.C(F), O.eval(~F, x, PL.eqget(eqs, j)), O.eval(~F, x2, PL.eqget(e2, k)), O.zero(F), Equal.trans(O.C(F), O.eval(~F, x, PL.eqget(eqs, j)), O.eval(~F, x2, PL.rnv(vp, PL.eqget(eqs, j))), O.eval(~F, x2, PL.eqget(e2, k)), Equal.sym(O.C(F), O.eval(~F, x2, PL.rnv(vp, PL.eqget(eqs, j))), O.eval(~F, x, PL.eqget(eqs, j)), ren), Equal.sym(O.C(F), O.eval(~F, x2, PL.eqget(e2, k)), O.eval(~F, x2, PL.rnv(vp, PL.eqget(eqs, j))), eval_rw(~F, x2, PL.eqget(e2, k), PL.rnv(vp, PL.eqget(eqs, j)), eq1))), z0)

# coordinate v of the read-back assignment lies in the box
def ex_box(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +ok: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}, +x2: M.Vec(~F), +hb: BX.inbox(~K, ~F, ~H, PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), x2), +v: Nat, +hv: {KA.natle(1n+v, KA.klen(~K, gc)) == True{} : Bool}) -> M.bnd(~F, O.lookup(~F, C.vsub(~F, upm(~F, x2, vp, KA.klen(~K, gc), 0n), N.ofkv(~K, ~F, ~H, gc)), v), O.lookup(~F, N.ofkv(~K, ~F, ~H, gr), v)):
  +nv = KA.klen(~K, gc)
  +x = upm(~F, x2, vp, nv, 0n)
  +k = PL.pos(v, vp)
  +hk = present0(vp, nv, v, cr_vp_has(~K, eqs, gc, gr, vp, ep, np, bs, ok), hv)
  +gc2 = PL.kperm(~K, gc, vp)
  +gr2 = PL.kperm(~K, gr, vp)
  +hl2 = Equal.trans(Nat, M.len(~F, C.vsub(~F, x2, N.ofkv(~K, ~F, ~H, gc2))), KA.klen(~K, gc2), PL.nlen(vp), inbox_lr(~K, ~F, ~H, gc2, gr2, x2, hb), klen_kperm(~K, gc, vp))
  +b0 = ent(~F, x2, N.ofkv(~K, ~F, ~H, gc2), N.ofkv(~K, ~F, ~H, gr2), k, PL.nlen(vp), inbox_rb(~K, ~F, ~H, gc2, gr2, x2, hb), hl2, hk)
  +eg = Equal.trans(O.C(F), O.lookup(~F, N.ofkv(~K, ~F, ~H, gc2), k), O.lookup(~F, N.ofkv(~K, ~F, ~H, gc), PL.nthn(vp, k)), O.lookup(~F, N.ofkv(~K, ~F, ~H, gc), v), kperm_at(~K, ~F, ~H, gc, vp, k, hk), look_vec_rw(~F, N.ofkv(~K, ~F, ~H, gc), PL.nthn(vp, k), v, pos_nth(v, vp, hk)))
  +er = Equal.trans(O.C(F), O.lookup(~F, N.ofkv(~K, ~F, ~H, gr2), k), O.lookup(~F, N.ofkv(~K, ~F, ~H, gr), PL.nthn(vp, k)), O.lookup(~F, N.ofkv(~K, ~F, ~H, gr), v), kperm_at(~K, ~F, ~H, gr, vp, k, hk), look_vec_rw(~F, N.ofkv(~K, ~F, ~H, gr), PL.nthn(vp, k), v, pos_nth(v, vp, hk)))
  unent(~F, x, N.ofkv(~K, ~F, ~H, gc), N.ofkv(~K, ~F, ~H, gr), v, btr(~F, O.lookup(~F, x2, k), O.lookup(~F, x, v), O.lookup(~F, N.ofkv(~K, ~F, ~H, gc2), k), O.lookup(~F, N.ofkv(~K, ~F, ~H, gc), v), O.lookup(~F, N.ofkv(~K, ~F, ~H, gr2), k), O.lookup(~F, N.ofkv(~K, ~F, ~H, gr), v), look_upm0(~F, x2, vp, nv, v, hv), eg, er, b0))

def plan_exists.r2(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +ok: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}, s: Sigma<&2, &2, M.Vec(~F), x => M.Both(BX.inbox(~K, ~F, ~H, PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), x), SK.Zeros(~F, x, PL.reorder(vp, eqs, ep)))>) -> Sigma<&2, &2, M.Vec(~F), x => M.Both(BX.inbox(~K, ~F, ~H, gc, gr, x), SK.Zeros(~F, x, eqs))>:
  (+x2, h) = s
  (+hb, hz) = h
  +nv = KA.klen(~K, gc)
  +x = upm(~F, x2, vp, nv, 0n)
  +d = C.vsub(~F, x, N.ofkv(~K, ~F, ~H, gc))
  +hlx = Equal.trans(Nat, M.len(~F, x), nv, M.len(~F, N.ofkv(~K, ~F, ~H, gc)), len_upm(~F, x2, vp, nv, 0n), Equal.sym(Nat, M.len(~F, N.ofkv(~K, ~F, ~H, gc)), nv, CP.len_ofkv(~K, ~F, ~H, gc)))
  +hld = CP.len_vsub(~F, x, N.ofkv(~K, ~F, ~H, gc), nv, len_upm(~F, x2, vp, nv, 0n), CP.len_ofkv(~K, ~F, ~H, gc))
  (x, ((hlx, BA.rbnd_of_lk(~F, d, nv, N.ofkv(~K, ~F, ~H, gr), hld, BA.lk_build(~F, ~d, ~N.ofkv(~K, ~F, ~H, gr), ~nv, ~(v => hv => ex_box(~K, ~F, ~H, eqs, gc, gr, vp, ep, np, bs, ok, x2, hb, v, hv)), nv, 0n, BA.lk_end(nv)))),
       zeros_of_zall(~F, x, eqs, zeros_build(~F, ~x, ~eqs, ~(j => hj => ex_zero(~K, ~F, ~H, eqs, gc, gr, vp, ep, np, bs, ok, x2, hz, j, hj)), CK.eqlen(eqs), 0n, BA.lk_end(CK.eqlen(eqs))))))

def plan_exists.r(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +ok: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}) -> Sigma<&2, &2, M.Vec(~F), x => M.Both(BX.inbox(~K, ~F, ~H, gc, gr, x), SK.Zeros(~F, x, eqs))>:
  plan_exists.r2(~K, ~F, ~H, eqs, gc, gr, vp, ep, np, bs, ok, plan_exists.p(~K, ~F, ~R, ~H, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs, cr_inner(~K, eqs, gc, gr, vp, ep, np, bs, ok)))

# the reordered assignment's coordinate k lies in the reordered box
def un_box(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +ok: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}, +x: M.Vec(~F), +hb: BX.inbox(~K, ~F, ~H, gc, gr, x), +k: Nat, +hk: {KA.natle(1n+k, PL.nlen(vp)) == True{} : Bool}) -> M.bnd(~F, O.lookup(~F, C.vsub(~F, zmap(~F, x, vp), N.ofkv(~K, ~F, ~H, PL.kperm(~K, gc, vp))), k), O.lookup(~F, N.ofkv(~K, ~F, ~H, PL.kperm(~K, gr, vp)), k)):
  +v = PL.nthn(vp, k)
  +hv = pars_at(KA.klen(~K, gc), vp, k, cr_vp_lt(~K, eqs, gc, gr, vp, ep, np, bs, ok), hk)
  +b0 = ent(~F, x, N.ofkv(~K, ~F, ~H, gc), N.ofkv(~K, ~F, ~H, gr), v, KA.klen(~K, gc), inbox_rb(~K, ~F, ~H, gc, gr, x, hb), inbox_lr(~K, ~F, ~H, gc, gr, x, hb), hv)
  unent(~F, zmap(~F, x, vp), N.ofkv(~K, ~F, ~H, PL.kperm(~K, gc, vp)), N.ofkv(~K, ~F, ~H, PL.kperm(~K, gr, vp)), k, btr(~F, O.lookup(~F, x, v), O.lookup(~F, zmap(~F, x, vp), k), O.lookup(~F, N.ofkv(~K, ~F, ~H, gc), v), O.lookup(~F, N.ofkv(~K, ~F, ~H, PL.kperm(~K, gc, vp)), k), O.lookup(~F, N.ofkv(~K, ~F, ~H, gr), v), O.lookup(~F, N.ofkv(~K, ~F, ~H, PL.kperm(~K, gr, vp)), k), Equal.sym(O.C(F), O.lookup(~F, zmap(~F, x, vp), k), O.lookup(~F, x, v), look_zmap(~F, x, vp, k, hk)), Equal.sym(O.C(F), O.lookup(~F, N.ofkv(~K, ~F, ~H, PL.kperm(~K, gc, vp)), k), O.lookup(~F, N.ofkv(~K, ~F, ~H, gc), v), kperm_at(~K, ~F, ~H, gc, vp, k, hk)), Equal.sym(O.C(F), O.lookup(~F, N.ofkv(~K, ~F, ~H, PL.kperm(~K, gr, vp)), k), O.lookup(~F, N.ofkv(~K, ~F, ~H, gr), v), kperm_at(~K, ~F, ~H, gr, vp, k, hk)), b0))

# the reordered assignment, at v's position, is v's value
def zm_pos(~K: N.Num, ~F: O.OField, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +ok: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}, +x: M.Vec(~F), +v: Nat, +hv: {KA.natle(1n+v, KA.klen(~K, gc)) == True{} : Bool}) -> {O.lookup(~F, zmap(~F, x, vp), PL.pos(v, vp)) == O.lookup(~F, x, v) : O.C(F)}:
  +hk = present0(vp, KA.klen(~K, gc), v, cr_vp_has(~K, eqs, gc, gr, vp, ep, np, bs, ok), hv)
  Equal.trans(O.C(F), O.lookup(~F, zmap(~F, x, vp), PL.pos(v, vp)), O.lookup(~F, x, PL.nthn(vp, PL.pos(v, vp))), O.lookup(~F, x, v), look_zmap(~F, x, vp, PL.pos(v, vp), hk), look_vec_rw(~F, x, PL.nthn(vp, PL.pos(v, vp)), v, pos_nth(v, vp, hk)))

# equation k of the reordered system vanishes at the reordered assignment
def un_zero(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +ok: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}, +x: M.Vec(~F), +hz: SK.Zeros(~F, x, eqs), +k: Nat, +hk: {KA.natle(1n+k, CK.eqlen(PL.reorder(vp, eqs, ep))) == True{} : Bool}) -> {O.eval(~F, zmap(~F, x, vp), PL.eqget(PL.reorder(vp, eqs, ep), k)) == O.zero(F) : O.C(F)}:
  +nv = KA.klen(~K, gc)
  +x2 = zmap(~F, x, vp)
  +hk2 = natle_rw(1n+k, CK.eqlen(PL.reorder(vp, eqs, ep)), PL.nlen(ep), len_reorder(vp, eqs, ep), hk)
  +j = PL.nthn(ep, k)
  +hj = pars_at(CK.eqlen(eqs), ep, k, cr_ep_lt(~K, eqs, gc, gr, vp, ep, np, bs, ok), hk2)
  +ren = ren_eval(~F, ~x, ~x2, ~vp, ~nv, ~(v => hv => zm_pos(~K, ~F, eqs, gc, gr, vp, ep, np, bs, ok, x, v, hv)), PL.eqget(eqs, j), below_at(nv, eqs, j, cr_below(~K, eqs, gc, gr, vp, ep, np, bs, ok), hj))
  Equal.trans(O.C(F), O.eval(~F, x2, PL.eqget(PL.reorder(vp, eqs, ep), k)), O.eval(~F, x2, PL.rnv(vp, PL.eqget(eqs, j))), O.zero(F), eval_rw(~F, x2, PL.eqget(PL.reorder(vp, eqs, ep), k), PL.rnv(vp, PL.eqget(eqs, j)), eqget_reorder(vp, eqs, ep, k, hk2)), Equal.trans(O.C(F), O.eval(~F, x2, PL.rnv(vp, PL.eqget(eqs, j))), O.eval(~F, x, PL.eqget(eqs, j)), O.zero(F), ren, zeros_at(~F, x, eqs, j, hz, hj)))

def un_in(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +ok: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}, +x: M.Vec(~F), +hb: BX.inbox(~K, ~F, ~H, gc, gr, x)) -> BX.inbox(~K, ~F, ~H, PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), zmap(~F, x, vp)):
  +x2 = zmap(~F, x, vp)
  +gc2 = N.ofkv(~K, ~F, ~H, PL.kperm(~K, gc, vp))
  +lg2 = Equal.trans(Nat, M.len(~F, gc2), KA.klen(~K, PL.kperm(~K, gc, vp)), PL.nlen(vp), CP.len_ofkv(~K, ~F, ~H, PL.kperm(~K, gc, vp)), klen_kperm(~K, gc, vp))
  +d = C.vsub(~F, x2, gc2)
  (Equal.trans(Nat, M.len(~F, x2), PL.nlen(vp), M.len(~F, gc2), len_zmap(~F, x, vp), Equal.sym(Nat, M.len(~F, gc2), PL.nlen(vp), lg2)),
   BA.rbnd_of_lk(~F, d, PL.nlen(vp), N.ofkv(~K, ~F, ~H, PL.kperm(~K, gr, vp)), CP.len_vsub(~F, x2, gc2, PL.nlen(vp), len_zmap(~F, x, vp), lg2), BA.lk_build(~F, ~d, ~N.ofkv(~K, ~F, ~H, PL.kperm(~K, gr, vp)), ~PL.nlen(vp), ~(k => hk => un_box(~K, ~F, ~H, eqs, gc, gr, vp, ep, np, bs, ok, x, hb, k, hk)), PL.nlen(vp), 0n, BA.lk_end(PL.nlen(vp)))))

def un_zs(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +ok: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}, +x: M.Vec(~F), +hz: SK.Zeros(~F, x, eqs)) -> SK.Zeros(~F, zmap(~F, x, vp), PL.reorder(vp, eqs, ep)):
  +x2 = zmap(~F, x, vp)
  +e2 = PL.reorder(vp, eqs, ep)
  zeros_of_zall(~F, x2, e2, zeros_build(~F, ~x2, ~e2, ~(k => hk => un_zero(~K, ~F, ~H, eqs, gc, gr, vp, ep, np, bs, ok, x, hz, k, hk)), CK.eqlen(e2), 0n, BA.lk_end(CK.eqlen(e2))))

def lookv_rw(~F: O.OField, +x: M.Vec(~F), +y: M.Vec(~F), +i: Nat, e: {x == y : M.Vec(~F)}) -> {O.lookup(~F, x, i) == O.lookup(~F, y, i) : O.C(F)}:
  %e : {O.lookup(~F, x, i) == O.lookup(~F, _, i) : O.C(F)}
  {==}

# coordinate v agrees, from equal reordered assignments
def un_eq(~K: N.Num, ~F: O.OField, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +ok: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}, +x1: M.Vec(~F), +x2: M.Vec(~F), +e: {zmap(~F, x1, vp) == zmap(~F, x2, vp) : M.Vec(~F)}, +v: Nat, +hv: {KA.natle(1n+v, KA.klen(~K, gc)) == True{} : Bool}) -> M.bnd(~F, O.lookup(~F, C.vsub(~F, x1, x2), v), O.lookup(~F, Nil{}, v)):
  +a1 = O.lookup(~F, x1, v)
  +a2 = O.lookup(~F, x2, v)
  +eq = Equal.trans(O.C(F), a1, O.lookup(~F, zmap(~F, x1, vp), PL.pos(v, vp)), a2, Equal.sym(O.C(F), O.lookup(~F, zmap(~F, x1, vp), PL.pos(v, vp)), a1, zm_pos(~K, ~F, eqs, gc, gr, vp, ep, np, bs, ok, x1, v, hv)), Equal.trans(O.C(F), O.lookup(~F, zmap(~F, x1, vp), PL.pos(v, vp)), O.lookup(~F, zmap(~F, x2, vp), PL.pos(v, vp)), a2, lookv_rw(~F, zmap(~F, x1, vp), zmap(~F, x2, vp), PL.pos(v, vp), e), zm_pos(~K, ~F, eqs, gc, gr, vp, ep, np, bs, ok, x2, v, hv)))
  FV.bval(~F, O.sub(~F, a1, a2), O.lookup(~F, C.vsub(~F, x1, x2), v), O.zero(F), SL.lookup_vsub(~F, x1, x2, v), bnd_of_zero(~F, O.sub(~F, a1, a2), FO.sub_of_eq(~F, a1, a2, eq)))

def plan_unique.r(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, PL.PBlock<K>>, +ok: {PL.check.r(~K, eqs, gc, gr, vp, ep, np, bs) == True{} : Bool}, +x1: M.Vec(~F), +h1: BX.inbox(~K, ~F, ~H, gc, gr, x1), +z1: SK.Zeros(~F, x1, eqs), +x2: M.Vec(~F), +h2: BX.inbox(~K, ~F, ~H, gc, gr, x2), +z2: SK.Zeros(~F, x2, eqs)) -> {x1 == x2 : M.Vec(~F)}:
  +nv = KA.klen(~K, gc)
  +e = plan_unique.p(~K, ~F, ~H, PL.reorder(vp, eqs, ep), PL.kperm(~K, gc, vp), PL.kperm(~K, gr, vp), np, bs, cr_inner(~K, eqs, gc, gr, vp, ep, np, bs, ok), zmap(~F, x1, vp), un_in(~K, ~F, ~H, eqs, gc, gr, vp, ep, np, bs, ok, x1, h1), un_zs(~K, ~F, ~H, eqs, gc, gr, vp, ep, np, bs, ok, x1, z1), zmap(~F, x2, vp), un_in(~K, ~F, ~H, eqs, gc, gr, vp, ep, np, bs, ok, x2, h2), un_zs(~K, ~F, ~H, eqs, gc, gr, vp, ep, np, bs, ok, x2, z2))
  +l1 = Equal.trans(Nat, M.len(~F, x1), M.len(~F, N.ofkv(~K, ~F, ~H, gc)), nv, inbox_len(~K, ~F, ~H, gc, gr, x1, h1), CP.len_ofkv(~K, ~F, ~H, gc))
  +l2 = Equal.trans(Nat, M.len(~F, x2), M.len(~F, N.ofkv(~K, ~F, ~H, gc)), nv, inbox_len(~K, ~F, ~H, gc, gr, x2, h2), CP.len_ofkv(~K, ~F, ~H, gc))
  +d = C.vsub(~F, x1, x2)
  eq_of_vall(~F, x1, x2, BA.vall_of_rbnd(~F, d, BA.rbnd_of_lk(~F, d, nv, Nil{}, CP.len_vsub(~F, x1, x2, nv, l1, l2), BA.lk_build(~F, ~d, ~{Nil{} : M.Vec(~F)}, ~nv, ~(v => hv => un_eq(~K, ~F, eqs, gc, gr, vp, ep, np, bs, ok, x1, x2, e, v, hv)), nv, 0n, BA.lk_end(nv)))), Equal.trans(Nat, M.len(~F, x1), nv, M.len(~F, x2), l1, Equal.sym(Nat, M.len(~F, x2), nv, l2)))

# LAW plan_exists: in a complete ordered field, the box holds a solution
def plan_exists(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), p: PL.Plan<K>, ok: {PL.check(~K, eqs, gc, gr, p) == True{} : Bool}) -> Sigma<&2, &2, M.Vec(~F), x => M.Both(BX.inbox(~K, ~F, ~H, gc, gr, x), SK.Zeros(~F, x, eqs))>:
  match p:
    case PL.Plan{+vp, +ep, +np, +bs}:
      plan_exists.r(~K, ~F, ~R, ~H, eqs, gc, gr, vp, ep, np, bs, ok)

# LAW plan_unique: in every ordered field, the box holds at most one solution
def plan_unique(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), p: PL.Plan<K>, ok: {PL.check(~K, eqs, gc, gr, p) == True{} : Bool}, +x1: M.Vec(~F), h1: BX.inbox(~K, ~F, ~H, gc, gr, x1), z1: SK.Zeros(~F, x1, eqs), +x2: M.Vec(~F), h2: BX.inbox(~K, ~F, ~H, gc, gr, x2), z2: SK.Zeros(~F, x2, eqs)) -> {x1 == x2 : M.Vec(~F)}:
  match p:
    case PL.Plan{+vp, +ep, +np, +bs}:
      plan_unique.r(~K, ~F, ~H, eqs, gc, gr, vp, ep, np, bs, ok, x1, h1, z1, x2, h2, z2)


# Sketches
# --------

def sketch_exists.go(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +sk: SK.Sketch, w: SK.Sketch.wf(sk), +gc: N.KVec(~K), +gr: N.KVec(~K), +os: {PL.check_sides(~K, SK.Sketch.sides(sk), gc, gr) == True{} : Bool}, s: Sigma<&2, &2, M.Vec(~F), x => M.Both(BX.inbox(~K, ~F, ~H, gc, gr, x), SK.Zeros(~F, x, SK.Sketch.eqs(sk)))>) -> &x: M.Vec(~F) -> (BX.inbox(~K, ~F, ~H, gc, gr, x) & SK.Sketch.means(~F, x, sk)):
  (+x, h) = s
  (+hin, hz) = h
  (x, (hin, MN.sketch_sound(~F, x, sk, w, (hz, box_sides(~K, ~F, ~H, SK.Sketch.sides(sk), gc, gr, os, x, hin)))))

# LAW sketch_exists: in a complete ordered field the box holds a geometry
# meaning the sketch
def sketch_exists(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +sk: SK.Sketch, w: SK.Sketch.wf(sk), +gc: N.KVec(~K), +gr: N.KVec(~K), p: PL.Plan<K>, ok: {PL.check(~K, SK.Sketch.eqs(sk), gc, gr, p) == True{} : Bool}, os: {PL.check_sides(~K, SK.Sketch.sides(sk), gc, gr) == True{} : Bool}) -> &x: M.Vec(~F) -> (BX.inbox(~K, ~F, ~H, gc, gr, x) & SK.Sketch.means(~F, x, sk)):
  sketch_exists.go(~K, ~F, ~H, sk, w, gc, gr, os, plan_exists(~K, ~F, ~R, ~H, SK.Sketch.eqs(sk), gc, gr, p, ok))

def zeros_of_holds(~F: O.OField, +x: M.Vec(~F), +sk: SK.Sketch, h: SK.Sketch.holds(~F, x, sk)) -> SK.Zeros(~F, x, SK.Sketch.eqs(sk)):
  (a, b) = h
  a

# LAW sketch_unique: at most one geometry in the box means the sketch
def sketch_unique(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +sk: SK.Sketch, +gc: N.KVec(~K), +gr: N.KVec(~K), p: PL.Plan<K>, ok: {PL.check(~K, SK.Sketch.eqs(sk), gc, gr, p) == True{} : Bool}, +x1: M.Vec(~F), h1: BX.inbox(~K, ~F, ~H, gc, gr, x1), m1: SK.Sketch.means(~F, x1, sk), +x2: M.Vec(~F), h2: BX.inbox(~K, ~F, ~H, gc, gr, x2), m2: SK.Sketch.means(~F, x2, sk)) -> {x1 == x2 : M.Vec(~F)}:
  plan_unique(~K, ~F, ~H, SK.Sketch.eqs(sk), gc, gr, p, ok, x1, h1, zeros_of_holds(~F, x1, sk, MN.sketch_complete(~F, x1, sk, m1)), x2, h2, zeros_of_holds(~F, x2, sk, MN.sketch_complete(~F, x2, sk, m2)))
