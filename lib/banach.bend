# Banach's fixed point for a checked block certificate, in a complete
# ordered field (DESIGN §8.4, Q18). Iterate the Newton map from the center:
# by cert_self every iterate stays in the box, and by cert_contract any two
# points of the box (within 2 radii of each other) come q^k closer after k
# steps, so the iterates are Cauchy in each coordinate. Their limits form a
# point of the box (closed bounds pass to limits), within 2 q^k radii of
# the k-th iterate, which the Newton map moves by at most 4 q^(k+1) radii
# for every k: a fixed point, so a zero of the block (cert_fix).
# Untrusted: proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ./certdef.bend as C
import ../spec/real.bend as CR
import ../spec/box.bend as BX
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./fmat.bend as FM
import ./dmat.bend as DM
import ./fvec.bend as FV
import ./karith.bend as KA
import ./slope.bend as SL
import ./nat.bend as LN
import ./cert.bend as CK
import ./certpf.bend as CP
import ./real.bend as RL
import ./kball.bend as KB

# From coordinates to vectors
# ---------------------------

# |d_i| <= r_i for the cnt indices from i0
def lkall(~F: O.OField, +d: M.Vec(~F), +r: M.Vec(~F), cnt: Nat, +i0: Nat) -> Data:
  match cnt:
    case 0n:
      Unit
    case 1n+c:
      M.Both(M.bnd(~F, O.lookup(~F, d, i0), O.lookup(~F, r, i0)), lkall(~F, d, r, c, 1n+i0))

def natle_addl(i0: Nat, +c: Nat) -> {KA.natle(i0, Nat.add(c, i0)) == True{} : Bool}:
  match i0:
    case 0n:
      {==}
    case 1n+j:
      %LN.add_succ(c, j) : {KA.natle(1n+j, _) == True{} : Bool}
      natle_addl(j, c)

# i0 < n, for 1 + c + i0 = n
def natle_of(+c: Nat, +i0: Nat, +n: Nat, e: {1n+Nat.add(c, i0) == n : Nat}) -> {KA.natle(1n+i0, n) == True{} : Bool}:
  %e : {KA.natle(1n+i0, _) == True{} : Bool}
  natle_addl(i0, c)

def lk_next(+c: Nat, +i0: Nat, +n: Nat, e: {1n+Nat.add(c, i0) == n : Nat}) -> {Nat.add(c, 1n+i0) == n : Nat}:
  %LN.add_succ(c, i0) : {_ == n : Nat}
  e

# collect the facts f(i) for the cnt indices from i0 (cnt + i0 = n)
def lk_build(~F: O.OField, ~d: M.Vec(~F), ~r: M.Vec(~F), ~n: Nat, ~f: @i: Nat -> {KA.natle(1n+i, n) == True{} : Bool} -> M.bnd(~F, O.lookup(~F, d, i), O.lookup(~F, r, i)), cnt: Nat, +i0: Nat, +e: {Nat.add(cnt, i0) == n : Nat}) -> lkall(~F, d, r, cnt, i0):
  match cnt:
    case 0n:
      Unit{}
    case 1n++c:
      (f(i0, natle_of(c, i0, n, e)), lk_build(~F, ~d, ~r, ~n, ~f, c, 1n+i0, lk_next(c, i0, n, e)))

def lk_shift_nil(~F: O.OField, +x: O.C(F), +xs: M.Vec(~F), cnt: Nat, +i0: Nat, h: lkall(~F, Con{x, xs}, Nil{}, cnt, 1n+i0)) -> lkall(~F, xs, Nil{}, cnt, i0):
  match cnt:
    case 0n:
      Unit{}
    case 1n+c:
      (h0, hs) = h
      (h0, lk_shift_nil(~F, x, xs, c, 1n+i0, hs))

def lk_shift_con(~F: O.OField, +x: O.C(F), +xs: M.Vec(~F), +s: O.C(F), +rs: M.Vec(~F), cnt: Nat, +i0: Nat, h: lkall(~F, Con{x, xs}, Con{s, rs}, cnt, 1n+i0)) -> lkall(~F, xs, rs, cnt, i0):
  match cnt:
    case 0n:
      Unit{}
    case 1n+c:
      (h0, hs) = h
      (h0, lk_shift_con(~F, x, xs, s, rs, c, 1n+i0, hs))

# the facts for every index give the vector bound
def rbnd_of_lk(~F: O.OField, d: M.Vec(~F), n: Nat, r: M.Vec(~F), hl: {M.len(~F, d) == n : Nat}, h: lkall(~F, d, r, n, 0n)) -> BX.rbnd(~F, d, r):
  match d n r:
    case Nil{} 0n Nil{}:
      Unit{}
    case Nil{} 0n Con{s, rs}:
      Unit{}
    case Nil{} 1n+k Nil{}:
      Unit{}
    case Nil{} 1n+k Con{s, rs}:
      Unit{}
    case Con{+x, +xs} 0n Nil{}:
      FO.absurd(BX.rbnd(~F, Con{x, xs}, Nil{}), FV.succ_ne(M.len(~F, xs), hl))
    case Con{+x, +xs} 0n Con{+s, +rs}:
      FO.absurd(BX.rbnd(~F, Con{x, xs}, Con{s, rs}), FV.succ_ne(M.len(~F, xs), hl))
    case Con{+x, +xs} 1n++k Nil{}:
      (h0, hs) = h
      (h0, rbnd_of_lk(~F, xs, k, Nil{}, LN.succ_inj(M.len(~F, xs), k, hl), lk_shift_nil(~F, x, xs, k, 0n, hs)))
    case Con{+x, +xs} 1n++k Con{+s, +rs}:
      (h0, hs) = h
      (h0, rbnd_of_lk(~F, xs, k, rs, LN.succ_inj(M.len(~F, xs), k, hl), lk_shift_con(~F, x, xs, s, rs, k, 0n, hs)))

# bounds by nothing are bounds by 0
def vall_of_rbnd(~F: O.OField, d: M.Vec(~F), h: BX.rbnd(~F, d, Nil{})) -> M.vbnd.all(~F, d, O.zero(F)):
  match d:
    case Nil{}:
      Unit{}
    case Con{x, xs}:
      (h0, hs) = h
      (h0, vall_of_rbnd(~F, xs, hs))

def look_vtl(~F: O.OField, r: M.Vec(~F), +i: Nat) -> {O.lookup(~F, r, 1n+i) == O.lookup(~F, FV.vtl(~F, r), i) : O.C(F)}:
  match r:
    case Nil{}:
      {==}
    case Con{s, rs}:
      {==}

def look_vhd(~F: O.OField, r: M.Vec(~F)) -> {O.lookup(~F, r, 0n) == FV.vhd(~F, r) : O.C(F)}:
  match r:
    case Nil{}:
      {==}
    case Con{s, rs}:
      {==}

def bnd_rw_s(~F: O.OField, +a: O.C(F), +s: O.C(F), +s2: O.C(F), e: {s == s2 : O.C(F)}, h: M.bnd(~F, a, s)) -> M.bnd(~F, a, s2):
  %e : M.bnd(~F, a, _)
  h

# a vector bound gives each entry's bound, for indices below the length
def rbnd_look(~F: O.OField, d: M.Vec(~F), +r: M.Vec(~F), +h: BX.rbnd(~F, d, r), n: Nat, hl: {M.len(~F, d) == n : Nat}, i: Nat, hi: {KA.natle(1n+i, n) == True{} : Bool}) -> M.bnd(~F, O.lookup(~F, d, i), O.lookup(~F, r, i)):
  match d n i:
    case Nil{} 0n i:
      FO.absurd(M.bnd(~F, O.zero(F), O.lookup(~F, r, i)), KA.ft(hi))
    case Nil{} 1n+k i:
      FO.absurd(M.bnd(~F, O.zero(F), O.lookup(~F, r, i)), FV.zero_ne(k, hl))
    case Con{+x, +xs} 0n i:
      FO.absurd(M.bnd(~F, O.lookup(~F, Con{x, xs}, i), O.lookup(~F, r, i)), FV.succ_ne(M.len(~F, xs), hl))
    case Con{+x, +xs} 1n+k 0n:
      bnd_rw_s(~F, x, FV.vhd(~F, r), O.lookup(~F, r, 0n), Equal.sym(O.C(F), O.lookup(~F, r, 0n), FV.vhd(~F, r), look_vhd(~F, r)), FV.rbnd_head(~F, x, xs, r, h))
    case Con{+x, +xs} 1n++k 1n++j:
      bnd_rw_s(~F, O.lookup(~F, xs, j), O.lookup(~F, FV.vtl(~F, r), j), O.lookup(~F, r, 1n+j), Equal.sym(O.C(F), O.lookup(~F, r, 1n+j), O.lookup(~F, FV.vtl(~F, r), j), look_vtl(~F, r, j)), rbnd_look(~F, xs, FV.vtl(~F, r), FV.rbnd_tail(~F, x, xs, r, h), k, LN.succ_inj(M.len(~F, xs), k, hl), j, hi))

# The certificate's facts, unpacked
# ---------------------------------

def fac0(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, h: M.Both(O.le(~F, O.zero(F), C.factor(~K, ~F, ~H, c)), O.lt(F, C.factor(~K, ~F, ~H, c), O.one(F)))) -> O.le(~F, O.zero(F), C.factor(~K, ~F, ~H, c)):
  (h0, h1) = h
  h0

def fac1(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, h: M.Both(O.le(~F, O.zero(F), C.factor(~K, ~F, ~H, c)), O.lt(F, C.factor(~K, ~F, ~H, c), O.one(F)))) -> O.lt(F, C.factor(~K, ~F, ~H, c), O.one(F)):
  (h0, h1) = h
  h1

def ball_len(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, +y: M.Vec(~F), h: C.ball(~K, ~F, ~H, c, y)) -> {M.len(~F, y) == M.len(~F, C.center(~K, ~F, ~H, c)) : Nat}:
  (hl, hb) = h
  hl

def ball_rb(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, +y: M.Vec(~F), h: C.ball(~K, ~F, ~H, c, y)) -> BX.rbnd(~F, BX.vsub(~F, y, C.center(~K, ~F, ~H, c)), C.radii(~K, ~F, ~H, c)):
  (hl, hb) = h
  hb

# The iterates
# ------------

# k Newton steps from y
def itf(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +z: M.Vec(~F), k: Nat, +y: M.Vec(~F)) -> M.Vec(~F):
  match k:
    case 0n:
      y
    case 1n+j:
      itf(~K, ~F, ~H, b, c, z, j, C.newton(~K, ~F, ~H, b, c, z, y))

# k Newton steps from the center
def it(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +z: M.Vec(~F), +k: Nat) -> M.Vec(~F):
  itf(~K, ~F, ~H, b, c, z, k, C.center(~K, ~F, ~H, c))

def itf_ball(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +z: M.Vec(~F), +hz: C.pinned(~K, ~F, ~H, c, z), k: Nat, +y: M.Vec(~F), h: C.ball(~K, ~F, ~H, c, y)) -> C.ball(~K, ~F, ~H, c, itf(~K, ~F, ~H, b, c, z, k, y)):
  match k:
    case 0n:
      h
    case 1n+j:
      itf_ball(~K, ~F, ~H, b, c, ok, z, hz, j, C.newton(~K, ~F, ~H, b, c, z, y), CP.cert_self(~K, ~F, ~H, b, c, ok, z, hz, y, h))

def it_ball(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +z: M.Vec(~F), +hz: C.pinned(~K, ~F, ~H, c, z), +k: Nat) -> C.ball(~K, ~F, ~H, c, it(~K, ~F, ~H, b, c, z, k)):
  itf_ball(~K, ~F, ~H, b, c, ok, z, hz, k, C.center(~K, ~F, ~H, c), CP.cert_center(~K, ~F, ~H, b, c, ok))

# k steps bring points within s radii to within q^k s radii
def itf_near(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +z: M.Vec(~F), +hz: C.pinned(~K, ~F, ~H, c, z), k: Nat, +y1: M.Vec(~F), +y2: M.Vec(~F), +s: O.C(F), +hs0: O.le(~F, O.zero(F), s), +h1: C.ball(~K, ~F, ~H, c, y1), +h2: C.ball(~K, ~F, ~H, c, y2), hn: C.near(~K, ~F, ~H, c, s, y1, y2)) -> C.near(~K, ~F, ~H, c, O.mul(F, RL.pw(~F, C.factor(~K, ~F, ~H, c), k), s), itf(~K, ~F, ~H, b, c, z, k, y1), itf(~K, ~F, ~H, b, c, z, k, y2)):
  match k:
    case 0n:
      %FR.fring_eq(~F, [s], E.ZVar{0n}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZVar{0n}}, {==}) : C.near(~K, ~F, ~H, c, _, y1, y2)
      hn
    case 1n++j:
      +q = C.factor(~K, ~F, ~H, c)
      +hq0 = fac0(~K, ~F, ~H, c, CP.cert_factor(~K, ~F, ~H, b, c, ok))
      %Equal.sym(O.C(F), O.mul(F, O.mul(F, RL.pw(~F, q, j), q), s), O.mul(F, RL.pw(~F, q, j), O.mul(F, q, s)), O.mul_assoc(F)(RL.pw(~F, q, j), q, s)) : C.near(~K, ~F, ~H, c, _, itf(~K, ~F, ~H, b, c, z, 1n+j, y1), itf(~K, ~F, ~H, b, c, z, 1n+j, y2))
      itf_near(~K, ~F, ~H, b, c, ok, z, hz, j, C.newton(~K, ~F, ~H, b, c, z, y1), C.newton(~K, ~F, ~H, b, c, z, y2), O.mul(F, q, s), FO.mul_nonneg(~F, q, s, hq0, hs0), CP.cert_self(~K, ~F, ~H, b, c, ok, z, hz, y1, h1), CP.cert_self(~K, ~F, ~H, b, c, ok, z, hz, y2, h2), CP.cert_contract(~K, ~F, ~H, b, c, ok, z, hz, y1, h1, y2, h2, s, hs0, hn))

# j + k steps are k steps after j steps
def itf_comp(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +z: M.Vec(~F), j: Nat, +k: Nat, +y: M.Vec(~F)) -> {itf(~K, ~F, ~H, b, c, z, Nat.add(j, k), y) == itf(~K, ~F, ~H, b, c, z, k, itf(~K, ~F, ~H, b, c, z, j, y)) : M.Vec(~F)}:
  match j:
    case 0n:
      {==}
    case 1n+i:
      itf_comp(~K, ~F, ~H, b, c, z, i, k, C.newton(~K, ~F, ~H, b, c, z, y))

# iterate k + 1 is the Newton image of iterate k
def it_succ(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +z: M.Vec(~F), +k: Nat) -> {it(~K, ~F, ~H, b, c, z, 1n+k) == C.newton(~K, ~F, ~H, b, c, z, it(~K, ~F, ~H, b, c, z, k)) : M.Vec(~F)}:
  %LN.add_comm(k, 1n) : {itf(~K, ~F, ~H, b, c, z, _, C.center(~K, ~F, ~H, c)) == C.newton(~K, ~F, ~H, b, c, z, it(~K, ~F, ~H, b, c, z, k))  : M.Vec(~F)}
  itf_comp(~K, ~F, ~H, b, c, z, k, 1n, C.center(~K, ~F, ~H, c))

# iterates k + a and k are within 2 q^k radii
def inear(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +z: M.Vec(~F), +hz: C.pinned(~K, ~F, ~H, c, z), +k: Nat, +a: Nat) -> C.near(~K, ~F, ~H, c, O.mul(F, RL.pw(~F, C.factor(~K, ~F, ~H, c), k), O.two(~F)), it(~K, ~F, ~H, b, c, z, Nat.add(k, a)), it(~K, ~F, ~H, b, c, z, k)):
  +c0 = C.center(~K, ~F, ~H, c)
  +s = O.mul(F, RL.pw(~F, C.factor(~K, ~F, ~H, c), k), O.two(~F))
  %LN.add_comm(a, k) : C.near(~K, ~F, ~H, c, s, itf(~K, ~F, ~H, b, c, z, _, c0), it(~K, ~F, ~H, b, c, z, k))
  %Equal.sym(M.Vec(~F), itf(~K, ~F, ~H, b, c, z, Nat.add(a, k), c0), itf(~K, ~F, ~H, b, c, z, k, it(~K, ~F, ~H, b, c, z, a)), itf_comp(~K, ~F, ~H, b, c, z, a, k, c0)) : C.near(~K, ~F, ~H, c, s, _, it(~K, ~F, ~H, b, c, z, k))
  +ha = it_ball(~K, ~F, ~H, b, c, ok, z, hz, a)
  +hc = CP.cert_center(~K, ~F, ~H, b, c, ok)
  itf_near(~K, ~F, ~H, b, c, ok, z, hz, k, it(~K, ~F, ~H, b, c, z, a), c0, O.two(~F), FO.lt_le(~F, O.zero(F), O.two(~F), FO.two_pos(~F)), ha, hc, FV.two_ball(~F, it(~K, ~F, ~H, b, c, z, a), c0, c0, C.radii(~K, ~F, ~H, c), ball_len(~K, ~F, ~H, c, it(~K, ~F, ~H, b, c, z, a), ha), ball_len(~K, ~F, ~H, c, c0, hc), ball_rb(~K, ~F, ~H, c, it(~K, ~F, ~H, b, c, z, a), ha), ball_rb(~K, ~F, ~H, c, c0, hc)))

# Coordinates
# -----------

def look_vscale(~F: O.OField, +s: O.C(F), r: M.Vec(~F), i: Nat) -> {O.mul(F, s, O.lookup(~F, r, i)) == O.lookup(~F, M.vscale(~F, s, r), i) : O.C(F)}:
  match r i:
    case Nil{} i:
      Equal.sym(O.C(F), O.zero(F), O.mul(F, s, O.zero(F)), FL.mul_zero(~F, s))
    case Con{x, xs} 0n:
      {==}
    case Con{x, xs} 1n+j:
      look_vscale(~F, s, xs, j)

# entry i of a near bound, for points of the box
def coord(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, +u: M.Vec(~F), +v: M.Vec(~F), +s: O.C(F), +i: Nat, hn: C.near(~K, ~F, ~H, c, s, u, v), hlu: {M.len(~F, u) == M.len(~F, C.center(~K, ~F, ~H, c)) : Nat}, hlv: {M.len(~F, v) == M.len(~F, C.center(~K, ~F, ~H, c)) : Nat}, hi: {KA.natle(1n+i, M.len(~F, C.center(~K, ~F, ~H, c))) == True{} : Bool}) -> M.bnd(~F, O.sub(~F, O.lookup(~F, u, i), O.lookup(~F, v, i)), O.mul(F, s, O.lookup(~F, C.radii(~K, ~F, ~H, c), i))):
  +m0 = M.len(~F, C.center(~K, ~F, ~H, c))
  +rad = C.radii(~K, ~F, ~H, c)
  bnd_rw_s(~F, O.sub(~F, O.lookup(~F, u, i), O.lookup(~F, v, i)), O.lookup(~F, M.vscale(~F, s, rad), i), O.mul(F, s, O.lookup(~F, rad, i)), Equal.sym(O.C(F), O.mul(F, s, O.lookup(~F, rad, i)), O.lookup(~F, M.vscale(~F, s, rad), i), look_vscale(~F, s, rad, i)),
    FV.bval(~F, O.lookup(~F, BX.vsub(~F, u, v), i), O.sub(~F, O.lookup(~F, u, i), O.lookup(~F, v, i)), O.lookup(~F, M.vscale(~F, s, rad), i), Equal.sym(O.C(F), O.sub(~F, O.lookup(~F, u, i), O.lookup(~F, v, i)), O.lookup(~F, BX.vsub(~F, u, v), i), SL.lookup_vsub(~F, u, v, i)),
      rbnd_look(~F, BX.vsub(~F, u, v), M.vscale(~F, s, rad), hn, m0, CP.len_vsub(~F, u, v, m0, hlu, hlv), i, hi)))

# entry i of a point of the box
def coord1(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, +u: M.Vec(~F), +i: Nat, h: C.ball(~K, ~F, ~H, c, u), hi: {KA.natle(1n+i, M.len(~F, C.center(~K, ~F, ~H, c))) == True{} : Bool}) -> M.bnd(~F, O.sub(~F, O.lookup(~F, u, i), O.lookup(~F, C.center(~K, ~F, ~H, c), i)), O.lookup(~F, C.radii(~K, ~F, ~H, c), i)):
  (hl, hb) = h
  +c0 = C.center(~K, ~F, ~H, c)
  FV.bval(~F, O.lookup(~F, BX.vsub(~F, u, c0), i), O.sub(~F, O.lookup(~F, u, i), O.lookup(~F, c0, i)), O.lookup(~F, C.radii(~K, ~F, ~H, c), i), Equal.sym(O.C(F), O.sub(~F, O.lookup(~F, u, i), O.lookup(~F, c0, i)), O.lookup(~F, BX.vsub(~F, u, c0), i), SL.lookup_vsub(~F, u, c0, i)),
    rbnd_look(~F, BX.vsub(~F, u, c0), C.radii(~K, ~F, ~H, c), hb, M.len(~F, c0), CP.len_vsub(~F, u, c0, M.len(~F, c0), hl, {==}), i, hi))

# the radii are not negative (below the center's length)
def ri_nn(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +i: Nat, +hi: {KA.natle(1n+i, M.len(~F, C.center(~K, ~F, ~H, c))) == True{} : Bool}) -> O.le(~F, O.zero(F), O.lookup(~F, C.radii(~K, ~F, ~H, c), i)):
  +c0 = C.center(~K, ~F, ~H, c)
  FM.bnd_nonneg(~F, O.sub(~F, O.lookup(~F, c0, i), O.lookup(~F, c0, i)), O.lookup(~F, C.radii(~K, ~F, ~H, c), i), coord1(~K, ~F, ~H, c, c0, i, CP.cert_center(~K, ~F, ~H, b, c, ok), hi))

# coordinate i of the iterates
def sq(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +z: M.Vec(~F), +i: Nat) -> Nat -> O.C(F):
  t => O.lookup(~F, it(~K, ~F, ~H, b, c, z, t), i)

# the Cauchy constant 2 r_i + 2 r_i, and the modulus
def cc(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, +i: Nat) -> O.C(F):
  O.add(F, O.mul(F, O.two(~F), O.lookup(~F, C.radii(~K, ~F, ~H, c), i)), O.mul(F, O.two(~F), O.lookup(~F, C.radii(~K, ~F, ~H, c), i)))

def md(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +c: C.Cert<K>, +i: Nat) -> Nat -> Nat:
  k => RL.mk(~F, ~R, C.factor(~K, ~F, ~H, c), cc(~K, ~F, ~H, c, i), k)

def cy.k(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +z: M.Vec(~F), +hz: C.pinned(~K, ~F, ~H, c, z), +i: Nat, +hi: {KA.natle(1n+i, M.len(~F, C.center(~K, ~F, ~H, c))) == True{} : Bool}, +k: Nat, +a: Nat, +bb: Nat) -> M.bnd(~F, O.sub(~F, O.lookup(~F, it(~K, ~F, ~H, b, c, z, Nat.add(RL.mk(~F, ~R, C.factor(~K, ~F, ~H, c), cc(~K, ~F, ~H, c, i), k), a)), i), O.lookup(~F, it(~K, ~F, ~H, b, c, z, Nat.add(RL.mk(~F, ~R, C.factor(~K, ~F, ~H, c), cc(~K, ~F, ~H, c, i), k), bb)), i)), CR.eps(~F, k)):
  +q = C.factor(~K, ~F, ~H, c)
  +ri = O.lookup(~F, C.radii(~K, ~F, ~H, c), i)
  +cst = cc(~K, ~F, ~H, c, i)
  +m = RL.mk(~F, ~R, q, cst, k)
  +sm = O.mul(F, RL.pw(~F, q, m), O.two(~F))
  +x = O.mul(F, sm, ri)
  +xa = O.lookup(~F, it(~K, ~F, ~H, b, c, z, Nat.add(m, a)), i)
  +xb = O.lookup(~F, it(~K, ~F, ~H, b, c, z, Nat.add(m, bb)), i)
  +xm = O.lookup(~F, it(~K, ~F, ~H, b, c, z, m), i)
  +lm = ball_len(~K, ~F, ~H, c, it(~K, ~F, ~H, b, c, z, m), it_ball(~K, ~F, ~H, b, c, ok, z, hz, m))
  +ha = coord(~K, ~F, ~H, c, it(~K, ~F, ~H, b, c, z, Nat.add(m, a)), it(~K, ~F, ~H, b, c, z, m), sm, i, inear(~K, ~F, ~H, b, c, ok, z, hz, m, a), ball_len(~K, ~F, ~H, c, it(~K, ~F, ~H, b, c, z, Nat.add(m, a)), it_ball(~K, ~F, ~H, b, c, ok, z, hz, Nat.add(m, a))), lm, hi)
  +hb = coord(~K, ~F, ~H, c, it(~K, ~F, ~H, b, c, z, Nat.add(m, bb)), it(~K, ~F, ~H, b, c, z, m), sm, i, inear(~K, ~F, ~H, b, c, ok, z, hz, m, bb), ball_len(~K, ~F, ~H, c, it(~K, ~F, ~H, b, c, z, Nat.add(m, bb)), it_ball(~K, ~F, ~H, b, c, ok, z, hz, Nat.add(m, bb))), lm, hi)
  +hf = CP.cert_factor(~K, ~F, ~H, b, c, ok)
  +hri = ri_nn(~K, ~F, ~H, b, c, ok, i, hi)
  +two0 = FO.lt_le(~F, O.zero(F), O.two(~F), FO.two_pos(~F))
  +hcc = FO.nonneg_add(~F, O.mul(F, O.two(~F), ri), O.mul(F, O.two(~F), ri), FO.mul_nonneg(~F, O.two(~F), ri, two0, hri), FO.mul_nonneg(~F, O.two(~F), ri, two0, hri))
  +sum = FM.bnd_add(~F, O.sub(~F, xa, xm), x, O.neg(F, O.sub(~F, xb, xm)), x, ha, FM.bnd_neg(~F, O.sub(~F, xb, xm), x, hb))
  +sum2 = FV.bval(~F, O.add(F, O.sub(~F, xa, xm), O.neg(F, O.sub(~F, xb, xm))), O.sub(~F, xa, xb), O.add(F, x, x), FR.fring_eq(~F, [xa, xb, xm], E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, E.ZNeg{E.ZSub{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, {==}), sum)
  +sum3 = bnd_rw_s(~F, O.sub(~F, xa, xb), O.add(F, x, x), O.mul(F, RL.pw(~F, q, m), cst), FR.fring_eq(~F, [RL.pw(~F, q, m), ri], E.ZAdd{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}}, E.ZVar{1n}}}, E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{1n}}, E.ZMul{E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{1n}}}}, {==}), sum2)
  FM.bnd_mono(~F, O.sub(~F, xa, xb), O.mul(F, RL.pw(~F, q, m), cst), CR.eps(~F, k), sum3, FM.sub_nonneg(~F, O.mul(F, RL.pw(~F, q, m), cst), CR.eps(~F, k), RL.small(~F, ~R, q, fac0(~K, ~F, ~H, c, hf), fac1(~K, ~F, ~H, c, hf), cst, hcc, k)))

# coordinate i of the iterates is Cauchy
def cy(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +z: M.Vec(~F), +hz: C.pinned(~K, ~F, ~H, c, z), +i: Nat, +hi: {KA.natle(1n+i, M.len(~F, C.center(~K, ~F, ~H, c))) == True{} : Bool}) -> CR.cauchy(~F, sq(~K, ~F, ~H, b, c, z, i), md(~K, ~F, ~R, ~H, c, i)):
  k => a => bb => cy.k(~K, ~F, ~R, ~H, b, c, ok, z, hz, i, hi, k, a, bb)

# The limit point
# ---------------

# the limit of coordinate i
def lm(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +z: M.Vec(~F), +i: Nat) -> O.C(F):
  CR.lim(F, R, sq(~K, ~F, ~H, b, c, z, i), md(~K, ~F, ~R, ~H, c, i))

# it lies within r_i of the center's coordinate
def in_lim(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +z: M.Vec(~F), +hz: C.pinned(~K, ~F, ~H, c, z), +i: Nat, +hi: {KA.natle(1n+i, M.len(~F, C.center(~K, ~F, ~H, c))) == True{} : Bool}) -> M.bnd(~F, O.sub(~F, lm(~K, ~F, ~R, ~H, b, c, z, i), O.lookup(~F, C.center(~K, ~F, ~H, c), i)), O.lookup(~F, C.radii(~K, ~F, ~H, c), i)):
  RL.close(~F, ~R, ~sq(~K, ~F, ~H, b, c, z, i), ~md(~K, ~F, ~R, ~H, c, i), ~cy(~K, ~F, ~R, ~H, b, c, ok, z, hz, i, hi), ~0n, ~O.lookup(~F, C.center(~K, ~F, ~H, c), i), ~O.lookup(~F, C.radii(~K, ~F, ~H, c), i), ~(j => coord1(~K, ~F, ~H, c, it(~K, ~F, ~H, b, c, z, j), i, it_ball(~K, ~F, ~H, b, c, ok, z, hz, j), hi)))

# and within 2 q^k r_i of iterate k's
def near_lim(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +z: M.Vec(~F), +hz: C.pinned(~K, ~F, ~H, c, z), +i: Nat, +hi: {KA.natle(1n+i, M.len(~F, C.center(~K, ~F, ~H, c))) == True{} : Bool}, +k: Nat) -> M.bnd(~F, O.sub(~F, lm(~K, ~F, ~R, ~H, b, c, z, i), O.lookup(~F, it(~K, ~F, ~H, b, c, z, k), i)), O.mul(F, O.mul(F, RL.pw(~F, C.factor(~K, ~F, ~H, c), k), O.two(~F)), O.lookup(~F, C.radii(~K, ~F, ~H, c), i))):
  +sm = O.mul(F, RL.pw(~F, C.factor(~K, ~F, ~H, c), k), O.two(~F))
  RL.close(~F, ~R, ~sq(~K, ~F, ~H, b, c, z, i), ~md(~K, ~F, ~R, ~H, c, i), ~cy(~K, ~F, ~R, ~H, b, c, ok, z, hz, i, hi), ~k, ~O.lookup(~F, it(~K, ~F, ~H, b, c, z, k), i), ~O.mul(F, sm, O.lookup(~F, C.radii(~K, ~F, ~H, c), i)), ~(j => coord(~K, ~F, ~H, c, it(~K, ~F, ~H, b, c, z, Nat.add(k, j)), it(~K, ~F, ~H, b, c, z, k), sm, i, inear(~K, ~F, ~H, b, c, ok, z, hz, k, j), ball_len(~K, ~F, ~H, c, it(~K, ~F, ~H, b, c, z, Nat.add(k, j)), it_ball(~K, ~F, ~H, b, c, ok, z, hz, Nat.add(k, j))), ball_len(~K, ~F, ~H, c, it(~K, ~F, ~H, b, c, z, k), it_ball(~K, ~F, ~H, b, c, ok, z, hz, k)), hi)))

# the limits of the cnt coordinates from i0
def lims(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +z: M.Vec(~F), cnt: Nat, +i0: Nat) -> M.Vec(~F):
  match cnt:
    case 0n:
      Nil{}
    case 1n+k:
      Con{lm(~K, ~F, ~R, ~H, b, c, z, i0), lims(~K, ~F, ~R, ~H, b, c, z, k, 1n+i0)}

def len_lims(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +z: M.Vec(~F), cnt: Nat, +i0: Nat) -> {M.len(~F, lims(~K, ~F, ~R, ~H, b, c, z, cnt, i0)) == cnt : Nat}:
  match cnt:
    case 0n:
      {==}
    case 1n++k:
      %Equal.sym(Nat, M.len(~F, lims(~K, ~F, ~R, ~H, b, c, z, k, 1n+i0)), k, len_lims(~K, ~F, ~R, ~H, b, c, z, k, 1n+i0)) : {1n+_ == 1n+k : Nat}
      {==}

def look_lims(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +z: M.Vec(~F), cnt: Nat, +i0: Nat, i: Nat, hi: {KA.natle(1n+i, cnt) == True{} : Bool}) -> {O.lookup(~F, lims(~K, ~F, ~R, ~H, b, c, z, cnt, i0), i) == lm(~K, ~F, ~R, ~H, b, c, z, Nat.add(i, i0)) : O.C(F)}:
  match cnt i:
    case 0n i:
      FO.absurd({O.zero(F) == lm(~K, ~F, ~R, ~H, b, c, z, Nat.add(i, i0)) : O.C(F)}, KA.ft(hi))
    case 1n+k 0n:
      {==}
    case 1n+k 1n++j:
      %Equal.sym(Nat, 1n+Nat.add(j, i0), Nat.add(j, 1n+i0), LN.add_succ(j, i0)) : {O.lookup(~F, lims(~K, ~F, ~R, ~H, b, c, z, k, 1n+i0), j) == lm(~K, ~F, ~R, ~H, b, c, z, _) : O.C(F)}
      look_lims(~K, ~F, ~R, ~H, b, c, z, k, 1n+i0, j, hi)

# the limit point: one limit per coordinate of the center
def ys(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +z: M.Vec(~F)) -> M.Vec(~F):
  lims(~K, ~F, ~R, ~H, b, c, z, M.len(~F, C.center(~K, ~F, ~H, c)), 0n)

def look_ys(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +z: M.Vec(~F), +i: Nat, hi: {KA.natle(1n+i, M.len(~F, C.center(~K, ~F, ~H, c))) == True{} : Bool}) -> {O.lookup(~F, ys(~K, ~F, ~R, ~H, b, c, z), i) == lm(~K, ~F, ~R, ~H, b, c, z, i) : O.C(F)}:
  %Equal.sym(Nat, i, Nat.add(i, 0n), LN.add_zero(i)) : {O.lookup(~F, ys(~K, ~F, ~R, ~H, b, c, z), i) == lm(~K, ~F, ~R, ~H, b, c, z, _) : O.C(F)}
  look_lims(~K, ~F, ~R, ~H, b, c, z, M.len(~F, C.center(~K, ~F, ~H, c)), 0n, i, hi)

def len_ys(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +z: M.Vec(~F)) -> {M.len(~F, ys(~K, ~F, ~R, ~H, b, c, z)) == M.len(~F, C.center(~K, ~F, ~H, c)) : Nat}:
  len_lims(~K, ~F, ~R, ~H, b, c, z, M.len(~F, C.center(~K, ~F, ~H, c)), 0n)

# entry i of y* - v, for the limit point y*
def ys_sub(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +z: M.Vec(~F), +v: M.Vec(~F), +i: Nat, hi: {KA.natle(1n+i, M.len(~F, C.center(~K, ~F, ~H, c))) == True{} : Bool}) -> {O.sub(~F, lm(~K, ~F, ~R, ~H, b, c, z, i), O.lookup(~F, v, i)) == O.lookup(~F, BX.vsub(~F, ys(~K, ~F, ~R, ~H, b, c, z), v), i) : O.C(F)}:
  %look_ys(~K, ~F, ~R, ~H, b, c, z, i, hi) : {O.sub(~F, _, O.lookup(~F, v, i)) == O.lookup(~F, BX.vsub(~F, ys(~K, ~F, ~R, ~H, b, c, z), v), i) : O.C(F)}
  SL.lookup_vsub(~F, ys(~K, ~F, ~R, ~H, b, c, z), v, i)

def lk_end(+n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  Equal.sym(Nat, n, Nat.add(n, 0n), LN.add_zero(n))

# the limit point is in the box
def ys_in.f(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +z: M.Vec(~F), +hz: C.pinned(~K, ~F, ~H, c, z), +i: Nat, +hi: {KA.natle(1n+i, M.len(~F, C.center(~K, ~F, ~H, c))) == True{} : Bool}) -> M.bnd(~F, O.lookup(~F, BX.vsub(~F, ys(~K, ~F, ~R, ~H, b, c, z), C.center(~K, ~F, ~H, c)), i), O.lookup(~F, C.radii(~K, ~F, ~H, c), i)):
  +c0 = C.center(~K, ~F, ~H, c)
  FV.bval(~F, O.sub(~F, lm(~K, ~F, ~R, ~H, b, c, z, i), O.lookup(~F, c0, i)), O.lookup(~F, BX.vsub(~F, ys(~K, ~F, ~R, ~H, b, c, z), c0), i), O.lookup(~F, C.radii(~K, ~F, ~H, c), i), ys_sub(~K, ~F, ~R, ~H, b, c, z, c0, i, hi), in_lim(~K, ~F, ~R, ~H, b, c, ok, z, hz, i, hi))

def ys_ball(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +z: M.Vec(~F), +hz: C.pinned(~K, ~F, ~H, c, z)) -> C.ball(~K, ~F, ~H, c, ys(~K, ~F, ~R, ~H, b, c, z)):
  +c0 = C.center(~K, ~F, ~H, c)
  +m0 = M.len(~F, c0)
  +y = ys(~K, ~F, ~R, ~H, b, c, z)
  +d = BX.vsub(~F, y, c0)
  +rad = C.radii(~K, ~F, ~H, c)
  (len_ys(~K, ~F, ~R, ~H, b, c, z), rbnd_of_lk(~F, d, m0, rad, CP.len_vsub(~F, y, c0, m0, len_ys(~K, ~F, ~R, ~H, b, c, z), {==}), lk_build(~F, ~d, ~rad, ~m0, ~(i => hi => ys_in.f(~K, ~F, ~R, ~H, b, c, ok, z, hz, i, hi)), m0, 0n, lk_end(m0))))

# the limit point is within 2 q^k radii of iterate k
def ys_near.f(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +z: M.Vec(~F), +hz: C.pinned(~K, ~F, ~H, c, z), +k: Nat, +i: Nat, +hi: {KA.natle(1n+i, M.len(~F, C.center(~K, ~F, ~H, c))) == True{} : Bool}) -> M.bnd(~F, O.lookup(~F, BX.vsub(~F, ys(~K, ~F, ~R, ~H, b, c, z), it(~K, ~F, ~H, b, c, z, k)), i), O.lookup(~F, M.vscale(~F, O.mul(F, RL.pw(~F, C.factor(~K, ~F, ~H, c), k), O.two(~F)), C.radii(~K, ~F, ~H, c)), i)):
  +sm = O.mul(F, RL.pw(~F, C.factor(~K, ~F, ~H, c), k), O.two(~F))
  +rad = C.radii(~K, ~F, ~H, c)
  +itk = it(~K, ~F, ~H, b, c, z, k)
  bnd_rw_s(~F, O.lookup(~F, BX.vsub(~F, ys(~K, ~F, ~R, ~H, b, c, z), itk), i), O.mul(F, sm, O.lookup(~F, rad, i)), O.lookup(~F, M.vscale(~F, sm, rad), i), look_vscale(~F, sm, rad, i),
    FV.bval(~F, O.sub(~F, lm(~K, ~F, ~R, ~H, b, c, z, i), O.lookup(~F, itk, i)), O.lookup(~F, BX.vsub(~F, ys(~K, ~F, ~R, ~H, b, c, z), itk), i), O.mul(F, sm, O.lookup(~F, rad, i)), ys_sub(~K, ~F, ~R, ~H, b, c, z, itk, i, hi), near_lim(~K, ~F, ~R, ~H, b, c, ok, z, hz, i, hi, k)))

def ys_near(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +z: M.Vec(~F), +hz: C.pinned(~K, ~F, ~H, c, z), +k: Nat) -> C.near(~K, ~F, ~H, c, O.mul(F, RL.pw(~F, C.factor(~K, ~F, ~H, c), k), O.two(~F)), ys(~K, ~F, ~R, ~H, b, c, z), it(~K, ~F, ~H, b, c, z, k)):
  +c0 = C.center(~K, ~F, ~H, c)
  +m0 = M.len(~F, c0)
  +y = ys(~K, ~F, ~R, ~H, b, c, z)
  +itk = it(~K, ~F, ~H, b, c, z, k)
  +d = BX.vsub(~F, y, itk)
  +w = M.vscale(~F, O.mul(F, RL.pw(~F, C.factor(~K, ~F, ~H, c), k), O.two(~F)), C.radii(~K, ~F, ~H, c))
  rbnd_of_lk(~F, d, m0, w, CP.len_vsub(~F, y, itk, m0, len_ys(~K, ~F, ~R, ~H, b, c, z), ball_len(~K, ~F, ~H, c, itk, it_ball(~K, ~F, ~H, b, c, ok, z, hz, k))), lk_build(~F, ~d, ~w, ~m0, ~(i => hi => ys_near.f(~K, ~F, ~R, ~H, b, c, ok, z, hz, k, i, hi)), m0, 0n, lk_end(m0)))

# The fixed point
# ---------------

def ys_near_n(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +z: M.Vec(~F), +hz: C.pinned(~K, ~F, ~H, c, z), +k: Nat) -> C.near(~K, ~F, ~H, c, O.mul(F, RL.pw(~F, C.factor(~K, ~F, ~H, c), 1n+k), O.two(~F)), ys(~K, ~F, ~R, ~H, b, c, z), C.newton(~K, ~F, ~H, b, c, z, it(~K, ~F, ~H, b, c, z, k))):
  %it_succ(~K, ~F, ~H, b, c, z, k) : C.near(~K, ~F, ~H, c, O.mul(F, RL.pw(~F, C.factor(~K, ~F, ~H, c), 1n+k), O.two(~F)), ys(~K, ~F, ~R, ~H, b, c, z), _)
  ys_near(~K, ~F, ~R, ~H, b, c, ok, z, hz, 1n+k)

# the fixed-point constant 4 q r_i
def cfx(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, +i: Nat) -> O.C(F):
  O.mul(F, O.add(F, O.two(~F), O.two(~F)), O.mul(F, C.factor(~K, ~F, ~H, c), O.lookup(~F, C.radii(~K, ~F, ~H, c), i)))

# entry i of N(y*) - y* is within q^k (4 q r_i), for every k
def fixb(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +z: M.Vec(~F), +hz: C.pinned(~K, ~F, ~H, c, z), +i: Nat, +hi: {KA.natle(1n+i, M.len(~F, C.center(~K, ~F, ~H, c))) == True{} : Bool}, +k: Nat) -> M.bnd(~F, O.lookup(~F, BX.vsub(~F, C.newton(~K, ~F, ~H, b, c, z, ys(~K, ~F, ~R, ~H, b, c, z)), ys(~K, ~F, ~R, ~H, b, c, z)), i), O.mul(F, RL.pw(~F, C.factor(~K, ~F, ~H, c), k), cfx(~K, ~F, ~H, c, i))):
  +q = C.factor(~K, ~F, ~H, c)
  +p = RL.pw(~F, q, k)
  +ri = O.lookup(~F, C.radii(~K, ~F, ~H, c), i)
  +y = ys(~K, ~F, ~R, ~H, b, c, z)
  +ny = C.newton(~K, ~F, ~H, b, c, z, y)
  +itk = it(~K, ~F, ~H, b, c, z, k)
  +nitk = C.newton(~K, ~F, ~H, b, c, z, itk)
  +sm = O.mul(F, p, O.two(~F))
  +sm1 = O.mul(F, RL.pw(~F, q, 1n+k), O.two(~F))
  +hy = ys_ball(~K, ~F, ~R, ~H, b, c, ok, z, hz)
  +hit = it_ball(~K, ~F, ~H, b, c, ok, z, hz, k)
  +hq0 = fac0(~K, ~F, ~H, c, CP.cert_factor(~K, ~F, ~H, b, c, ok))
  +lnit = ball_len(~K, ~F, ~H, c, nitk, CP.cert_self(~K, ~F, ~H, b, c, ok, z, hz, itk, hit))
  +ca = coord(~K, ~F, ~H, c, ny, nitk, O.mul(F, q, sm), i, CP.cert_contract(~K, ~F, ~H, b, c, ok, z, hz, y, hy, itk, hit, sm, FO.mul_nonneg(~F, p, O.two(~F), RL.pw_nn(~F, q, hq0, k), FO.lt_le(~F, O.zero(F), O.two(~F), FO.two_pos(~F))), ys_near(~K, ~F, ~R, ~H, b, c, ok, z, hz, k)), ball_len(~K, ~F, ~H, c, ny, CP.cert_self(~K, ~F, ~H, b, c, ok, z, hz, y, hy)), lnit, hi)
  +cb = coord(~K, ~F, ~H, c, y, nitk, sm1, i, ys_near_n(~K, ~F, ~R, ~H, b, c, ok, z, hz, k), len_ys(~K, ~F, ~R, ~H, b, c, z), lnit, hi)
  +a1 = O.lookup(~F, ny, i)
  +a2 = O.lookup(~F, y, i)
  +w = O.lookup(~F, nitk, i)
  +ba = O.mul(F, O.mul(F, q, sm), ri)
  +bb = O.mul(F, sm1, ri)
  +sum = FM.bnd_add(~F, O.sub(~F, a1, w), ba, O.neg(F, O.sub(~F, a2, w)), bb, ca, FM.bnd_neg(~F, O.sub(~F, a2, w), bb, cb))
  +ev = Equal.trans(O.C(F), O.add(F, O.sub(~F, a1, w), O.neg(F, O.sub(~F, a2, w))), O.sub(~F, a1, a2), O.lookup(~F, BX.vsub(~F, ny, y), i), FR.fring_eq(~F, [a1, a2, w], E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, E.ZNeg{E.ZSub{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, {==}), SL.lookup_vsub(~F, ny, y, i))
  +two = {E.ZAdd{E.ZCst{S.Zpos{S.XH{}}}, E.ZCst{S.Zpos{S.XH{}}}} : E.ZExpr}
  +eb = FR.fring_eq(~F, [p, q, ri], E.ZAdd{E.ZMul{E.ZMul{E.ZVar{1n}, E.ZMul{E.ZVar{0n}, two}}, E.ZVar{2n}}, E.ZMul{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, two}, E.ZVar{2n}}}, E.ZMul{E.ZVar{0n}, E.ZMul{E.ZAdd{two, two}, E.ZMul{E.ZVar{1n}, E.ZVar{2n}}}}, {==})
  bnd_rw_s(~F, O.lookup(~F, BX.vsub(~F, ny, y), i), O.add(F, ba, bb), O.mul(F, p, cfx(~K, ~F, ~H, c, i)), eb, FV.bval(~F, O.add(F, O.sub(~F, a1, w), O.neg(F, O.sub(~F, a2, w))), O.lookup(~F, BX.vsub(~F, ny, y), i), O.add(F, ba, bb), ev, sum))

def cfx_nn(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +i: Nat, +hi: {KA.natle(1n+i, M.len(~F, C.center(~K, ~F, ~H, c))) == True{} : Bool}) -> O.le(~F, O.zero(F), cfx(~K, ~F, ~H, c, i)):
  +two0 = FO.lt_le(~F, O.zero(F), O.two(~F), FO.two_pos(~F))
  FO.mul_nonneg(~F, O.add(F, O.two(~F), O.two(~F)), O.mul(F, C.factor(~K, ~F, ~H, c), O.lookup(~F, C.radii(~K, ~F, ~H, c), i)), FO.nonneg_add(~F, O.two(~F), O.two(~F), two0, two0), FO.mul_nonneg(~F, C.factor(~K, ~F, ~H, c), O.lookup(~F, C.radii(~K, ~F, ~H, c), i), fac0(~K, ~F, ~H, c, CP.cert_factor(~K, ~F, ~H, b, c, ok)), ri_nn(~K, ~F, ~H, b, c, ok, i, hi)))

# so entry i of N(y*) - y* is 0
def fixz(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +z: M.Vec(~F), +hz: C.pinned(~K, ~F, ~H, c, z), +i: Nat, +hi: {KA.natle(1n+i, M.len(~F, C.center(~K, ~F, ~H, c))) == True{} : Bool}) -> M.bnd(~F, O.lookup(~F, BX.vsub(~F, C.newton(~K, ~F, ~H, b, c, z, ys(~K, ~F, ~R, ~H, b, c, z)), ys(~K, ~F, ~R, ~H, b, c, z)), i), O.zero(F)):
  +hf = CP.cert_factor(~K, ~F, ~H, b, c, ok)
  RL.pw_zero(~F, ~R, ~C.factor(~K, ~F, ~H, c), ~fac0(~K, ~F, ~H, c, hf), ~fac1(~K, ~F, ~H, c, hf), ~cfx(~K, ~F, ~H, c, i), ~cfx_nn(~K, ~F, ~H, b, c, ok, i, hi), ~O.lookup(~F, BX.vsub(~F, C.newton(~K, ~F, ~H, b, c, z, ys(~K, ~F, ~R, ~H, b, c, z)), ys(~K, ~F, ~R, ~H, b, c, z)), i), ~(k => fixb(~K, ~F, ~R, ~H, b, c, ok, z, hz, i, hi, k)))

# the limit point is a fixed point of the Newton map
def ys_fix(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +z: M.Vec(~F), +hz: C.pinned(~K, ~F, ~H, c, z)) -> M.vbnd(~F, BX.vsub(~F, C.newton(~K, ~F, ~H, b, c, z, ys(~K, ~F, ~R, ~H, b, c, z)), ys(~K, ~F, ~R, ~H, b, c, z)), O.zero(F)):
  +m0 = M.len(~F, C.center(~K, ~F, ~H, c))
  +y = ys(~K, ~F, ~R, ~H, b, c, z)
  +ny = C.newton(~K, ~F, ~H, b, c, z, y)
  +d = BX.vsub(~F, ny, y)
  +ln = CP.len_vsub(~F, ny, y, m0, ball_len(~K, ~F, ~H, c, ny, CP.cert_self(~K, ~F, ~H, b, c, ok, z, hz, y, ys_ball(~K, ~F, ~R, ~H, b, c, ok, z, hz))), len_ys(~K, ~F, ~R, ~H, b, c, z))
  (FO.le_refl(~F, O.zero(F)), vall_of_rbnd(~F, d, rbnd_of_lk(~F, d, m0, Nil{}, ln, lk_build(~F, ~d, ~{Nil{} : M.Vec(~F)}, ~m0, ~(i => hi => fixz(~K, ~F, ~R, ~H, b, c, ok, z, hz, i, hi)), m0, 0n, lk_end(m0)))))

# LAW cert_exists: in a complete ordered field the box holds a zero of the
# block, for every choice of the parameters in their box
def cert_exists(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +b: C.Block, +c: C.Cert<K>, +ok: {CK.check(~K, b, c) == True{} : Bool}, +z: M.Vec(~F), +hz: C.pinned(~K, ~F, ~H, c, z)) -> Sigma<&2, &2, M.Vec(~F), y => M.Both(C.ball(~K, ~F, ~H, c, y), M.vbnd(~F, C.bfun(~F, b, y, z), O.zero(F)))>:
  +y = ys(~K, ~F, ~R, ~H, b, c, z)
  +hy = ys_ball(~K, ~F, ~R, ~H, b, c, ok, z, hz)
  (y, (hy, CP.cert_fix(~K, ~F, ~H, b, c, ok, z, y, hy, ys_fix(~K, ~F, ~R, ~H, b, c, ok, z, hz))))

def sub_l(~F: O.OField, +a: O.C(F), +a2: O.C(F), +b: O.C(F), e: {a == a2 : O.C(F)}) -> {O.sub(~F, a, b) == O.sub(~F, a2, b) : O.C(F)}:
  %e : {O.sub(~F, a, b) == O.sub(~F, _, b) : O.C(F)}
  {==}

def sub_r(~F: O.OField, +a: O.C(F), +b: O.C(F), +b2: O.C(F), e: {b == b2 : O.C(F)}) -> {O.sub(~F, a, b) == O.sub(~F, a, b2) : O.C(F)}:
  %e : {O.sub(~F, a, b) == O.sub(~F, a, _) : O.C(F)}
  {==}

# Signs from the box
# ------------------

def box_lo(~F: O.OField, +x: O.C(F), +ci: O.C(F), +ri: O.C(F), h: M.bnd(~F, O.sub(~F, x, ci), ri)) -> O.le(~F, O.sub(~F, ci, ri), x):
  (h1, h2) = h
  RL.le_by(~F, O.sub(~F, ci, ri), x, O.add(F, ri, O.sub(~F, x, ci)), FR.fring_eq(~F, [ri, x, ci], E.ZAdd{E.ZVar{0n}, E.ZSub{E.ZVar{1n}, E.ZVar{2n}}}, E.ZSub{E.ZVar{1n}, E.ZSub{E.ZVar{2n}, E.ZVar{0n}}}, {==}), h2)

# coordinate i of every point of the box is positive, when the checker's
# numbers say center_i - radius_i > 0
def box_pos(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, +y: M.Vec(~F), +hy: C.ball(~K, ~F, ~H, c, y), +i: Nat, +hi: {KA.natle(1n+i, M.len(~F, C.center(~K, ~F, ~H, c))) == True{} : Bool}, hk: {KA.klt(~K, N.nzero(K), KA.ksub(~K, KB.klook(~K, C.Cert.yc(K, c), i), KB.klook(~K, C.Cert.yr(K, c), i))) == True{} : Bool}) -> O.lt(F, O.zero(F), O.lookup(~F, y, i)):
  +ck = KB.klook(~K, C.Cert.yc(K, c), i)
  +rk = KB.klook(~K, C.Cert.yr(K, c), i)
  +ci = O.lookup(~F, C.center(~K, ~F, ~H, c), i)
  +ri = O.lookup(~F, C.radii(~K, ~F, ~H, c), i)
  +h1 = FO.lt_subst_l(~F, N.emap(K, F, H, N.nzero(K)), O.zero(F), N.emap(K, F, H, KA.ksub(~K, ck, rk)), N.e_zero(K, F, H), KA.klt_ok(~K, ~F, ~H, N.nzero(K), KA.ksub(~K, ck, rk), hk))
  +h2 = RL.lt_rw_r(~F, O.zero(F), N.emap(K, F, H, KA.ksub(~K, ck, rk)), O.sub(~F, N.emap(K, F, H, ck), N.emap(K, F, H, rk)), Equal.sym(O.C(F), O.sub(~F, N.emap(K, F, H, ck), N.emap(K, F, H, rk)), N.emap(K, F, H, KA.ksub(~K, ck, rk)), KA.es(~K, ~F, ~H, ck, rk)), h1)
  +e = Equal.trans(O.C(F), O.sub(~F, N.emap(K, F, H, ck), N.emap(K, F, H, rk)), O.sub(~F, ci, N.emap(K, F, H, rk)), O.sub(~F, ci, ri), sub_l(~F, N.emap(K, F, H, ck), ci, N.emap(K, F, H, rk), CP.klook_ofk(~K, ~F, ~H, C.Cert.yc(K, c), i)), sub_r(~F, ci, N.emap(K, F, H, rk), ri, CP.klook_ofk(~K, ~F, ~H, C.Cert.yr(K, c), i)))
  FO.lt_le_trans(~F, O.zero(F), O.sub(~F, ci, ri), O.lookup(~F, y, i), RL.lt_rw_r(~F, O.zero(F), O.sub(~F, N.emap(K, F, H, ck), N.emap(K, F, H, rk)), O.sub(~F, ci, ri), e, h2), box_lo(~F, O.lookup(~F, y, i), ci, ri, coord1(~K, ~F, ~H, c, y, i, hy, hi)))
