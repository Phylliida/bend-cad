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
import ../spec/cert.bend as C
import ../spec/real.bend as CR
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
def rbnd_of_lk(~F: O.OField, d: M.Vec(~F), n: Nat, r: M.Vec(~F), hl: {M.len(~F, d) == n : Nat}, h: lkall(~F, d, r, n, 0n)) -> C.rbnd(~F, d, r):
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
      FO.absurd(C.rbnd(~F, Con{x, xs}, Nil{}), FV.succ_ne(M.len(~F, xs), hl))
    case Con{+x, +xs} 0n Con{+s, +rs}:
      FO.absurd(C.rbnd(~F, Con{x, xs}, Con{s, rs}), FV.succ_ne(M.len(~F, xs), hl))
    case Con{+x, +xs} 1n++k Nil{}:
      (h0, hs) = h
      (h0, rbnd_of_lk(~F, xs, k, Nil{}, FV.succ_inj(M.len(~F, xs), k, hl), lk_shift_nil(~F, x, xs, k, 0n, hs)))
    case Con{+x, +xs} 1n++k Con{+s, +rs}:
      (h0, hs) = h
      (h0, rbnd_of_lk(~F, xs, k, rs, FV.succ_inj(M.len(~F, xs), k, hl), lk_shift_con(~F, x, xs, s, rs, k, 0n, hs)))

# bounds by nothing are bounds by 0
def vall_of_rbnd(~F: O.OField, d: M.Vec(~F), h: C.rbnd(~F, d, Nil{})) -> M.vbnd.all(~F, d, O.zero(F)):
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
def rbnd_look(~F: O.OField, d: M.Vec(~F), +r: M.Vec(~F), +h: C.rbnd(~F, d, r), n: Nat, hl: {M.len(~F, d) == n : Nat}, i: Nat, hi: {KA.natle(1n+i, n) == True{} : Bool}) -> M.bnd(~F, O.lookup(~F, d, i), O.lookup(~F, r, i)):
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
      bnd_rw_s(~F, O.lookup(~F, xs, j), O.lookup(~F, FV.vtl(~F, r), j), O.lookup(~F, r, 1n+j), Equal.sym(O.C(F), O.lookup(~F, r, 1n+j), O.lookup(~F, FV.vtl(~F, r), j), look_vtl(~F, r, j)), rbnd_look(~F, xs, FV.vtl(~F, r), FV.rbnd_tail(~F, x, xs, r, h), k, FV.succ_inj(M.len(~F, xs), k, hl), j, hi))

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

def ball_rb(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, +y: M.Vec(~F), h: C.ball(~K, ~F, ~H, c, y)) -> C.rbnd(~F, C.vsub(~F, y, C.center(~K, ~F, ~H, c)), C.radii(~K, ~F, ~H, c)):
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
