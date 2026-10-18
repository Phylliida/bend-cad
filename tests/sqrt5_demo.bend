# The existence law at work: in every complete ordered field, 5 has a
# positive square root. The circle-circle certificate (tests/cc_data.bend,
# checked over the dyadics) and cert_exists give a point (a, b) of its box
# with |P - A|^2 = 9 and |P - B|^2 = 9 for A = (0, 0), B = (4, 0). Then
# 8(a - 2) = 0, so a = 2 and b^2 = 9 - a^2 = 5; and b > 0, because the
# certificate's box lies above 0 (a comparison the checker's numbers make).
# ℚ has no such b (lean/BendCad/Axioms.lean shows ℚ is not complete).

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ../lib/certdef.bend as C
import ../spec/real.bend as CR
import ../lib/fring.bend as FR
import ../lib/ford.bend as FO
import ../lib/qemb.bend as QE
import ../lib/fvec.bend as FV
import ../lib/karith.bend as KA
import ../lib/kball.bend as KB
import ../lib/kinst.bend as KI
import ../lib/real.bend as RL
import ../lib/banach.bend as BA
import ../lib/cert.bend as CK
import ../lib/certpf.bend as CP
import ./cc_data.bend as D
import ../lib/nat.bend as LN

# The block's two equations at (a, b), as integer expressions in a, b and
# w = 1/1 (how a constant n/1 reads in F)
# -----------------------------------------------------------------------

def zw() -> E.ZExpr:
  E.ZVar{2n}

def zk(c: S.Z) -> E.ZExpr:
  E.ZMul{E.ZCst{c}, zw()}

def zsq(+x: E.ZExpr) -> E.ZExpr:
  E.ZMul{x, x}

def p2() -> S.Pos:
  S.XO{S.XH{}}

def p4() -> S.Pos:
  S.XO{S.XO{S.XH{}}}

def p5() -> S.Pos:
  S.XI{S.XO{S.XH{}}}

def p8() -> S.Pos:
  S.XO{S.XO{S.XO{S.XH{}}}}

def p9() -> S.Pos:
  S.XI{S.XO{S.XO{S.XH{}}}}

# (a - 0)^2 + (b - 0)^2 - 9
def ze1() -> E.ZExpr:
  E.ZSub{E.ZAdd{zsq(E.ZSub{E.ZVar{0n}, zk(S.Z0{})}), zsq(E.ZSub{E.ZVar{1n}, zk(S.Z0{})})}, zk(S.Zpos{p9()})}

# (a - 4)^2 + (b - 0)^2 - 9
def ze2() -> E.ZExpr:
  E.ZSub{E.ZAdd{zsq(E.ZSub{E.ZVar{0n}, zk(S.Zpos{p4()})}), zsq(E.ZSub{E.ZVar{1n}, zk(S.Z0{})})}, zk(S.Zpos{p9()})}

# a - 2
def zd() -> E.ZExpr:
  E.ZSub{E.ZVar{0n}, zk(S.Zpos{p2()})}

# 1 w - 1
def zr() -> E.ZExpr:
  E.ZSub{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, zw()}, E.ZCst{S.Zpos{S.XH{}}}}

def env(~F: O.OField, +a: O.C(F), +b: O.C(F)) -> List<&2, O.C(F)>:
  [a, b, O.inv(F, O.one(F))]

def zv(~F: O.OField, +a: O.C(F), +b: O.C(F), e: E.ZExpr) -> O.C(F):
  FR.zeval(~F, env(~F, a, b), e)

# The algebra
# -----------

def one_ne(~F: O.OField) -> {O.one(F) == O.zero(F) : O.C(F)} -> Empty:
  FO.ne_of_gt(~F, O.one(F), O.zero(F), O.zero_lt_one(F))

# a = 2 (times w): 8 w (a - 2 w) is the first equation minus the second
def alg_a(~F: O.OField, +a: O.C(F), +b: O.C(F), h1: {zv(~F, a, b, ze1()) == O.zero(F) : O.C(F)}, h2: {zv(~F, a, b, ze2()) == O.zero(F) : O.C(F)}) -> {zv(~F, a, b, zd()) == O.zero(F) : O.C(F)}:
  +w = O.inv(F, O.one(F))
  +k8 = O.mul(F, O.ofp(~F, p8()), w)
  +x = O.mul(F, k8, zv(~F, a, b, zd()))
  +hk8 = O.lt_mul(F)(O.ofp(~F, p8()), w, QE.ofp_pos(~F, p8()), FO.inv_pos(~F, O.one(F), O.zero_lt_one(F)))
  FO.mul_eq_zero(~F, k8, zv(~F, a, b, zd()), FO.ne_of_gt(~F, k8, O.zero(F), hk8),
    FO.cert2(~F, x, O.one(F), zv(~F, a, b, ze1()), O.neg(F, O.one(F)), zv(~F, a, b, ze2()),
      FR.fring_eq(~F, env(~F, a, b), E.ZMul{zk(S.Zpos{p8()}), zd()}, E.ZAdd{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, ze1()}, E.ZMul{E.ZNeg{E.ZCst{S.Zpos{S.XH{}}}}, ze2()}}, {==}),
      h1, h2))

# b^2 = 5: b^2 - 5 = e1 - (a + 2w)(a - 2w) + (5 - 4w)(w - 1)
def alg_b(~F: O.OField, +a: O.C(F), +b: O.C(F), h1: {zv(~F, a, b, ze1()) == O.zero(F) : O.C(F)}, hd: {zv(~F, a, b, zd()) == O.zero(F) : O.C(F)}) -> {O.mul(F, b, b) == O.ofp(~F, p5()) : O.C(F)}:
  +x = O.sub(~F, O.mul(F, b, b), O.ofp(~F, p5()))
  +c2 = zv(~F, a, b, E.ZNeg{E.ZAdd{E.ZVar{0n}, zk(S.Zpos{p2()})}})
  +c3 = zv(~F, a, b, E.ZSub{E.ZCst{S.Zpos{p5()}}, zk(S.Zpos{p4()})})
  FO.eq_of_sub(~F, O.mul(F, b, b), O.ofp(~F, p5()),
    FO.cert3(~F, x, O.one(F), zv(~F, a, b, ze1()), c2, zv(~F, a, b, zd()), c3, zv(~F, a, b, zr()),
      FR.fring_eq(~F, env(~F, a, b), E.ZSub{zsq(E.ZVar{1n}), E.ZCst{S.Zpos{p5()}}}, E.ZAdd{E.ZAdd{E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, ze1()}, E.ZMul{E.ZNeg{E.ZAdd{E.ZVar{0n}, zk(S.Zpos{p2()})}}, zd()}}, E.ZMul{E.ZSub{E.ZCst{S.Zpos{p5()}}, zk(S.Zpos{p4()})}, zr()}}, {==}),
      h1, hd, FO.inv_rel(~F, O.one(F), one_ne(~F))))

# The zero of the block, for any computing numbers K and certificate c
# with the facts Hk (checked by computation in K when c is given)
# ---------------------------------------------------------------------

def q0() -> S.Q:
  S.Q{S.Z0{}, S.XH{}}

def q4() -> S.Q:
  S.Q{S.Zpos{p4()}, S.XH{}}

def Hk5(~K: N.Num, +c: C.Cert<K>) -> Data:
  M.Both({KA.klt(~K, N.nzero(K), KA.ksub(~K, KB.klook(~K, C.Cert.yc(K, c), 1n), KB.klook(~K, C.Cert.yr(K, c), 1n))) == True{} : Bool},
  M.Both({N.nofq(K, q0()) == Some{KB.klook(~K, C.Cert.pc(K, c), 0n)} : Maybe<&2, N.NC(K)>},
  M.Both({N.nofq(K, q0()) == Some{KB.klook(~K, C.Cert.pc(K, c), 1n)} : Maybe<&2, N.NC(K)>},
  M.Both({N.nofq(K, q4()) == Some{KB.klook(~K, C.Cert.pc(K, c), 2n)} : Maybe<&2, N.NC(K)>},
  {N.nofq(K, q0()) == Some{KB.klook(~K, C.Cert.pc(K, c), 3n)} : Maybe<&2, N.NC(K)>}))))

def Hk(~K: N.Num, +c: C.Cert<K>) -> Data:
  M.Both({CK.check(~K, D.cc_block(), c) == True{} : Bool},
  M.Both({KA.kvle(~K, Nil{}, C.Cert.pr(K, c)) == True{} : Bool},
  M.Both({KA.klen(~K, C.Cert.yc(K, c)) == 2n : Nat}, Hk5(~K, c))))

def hk5_lt(~K: N.Num, +c: C.Cert<K>, h: Hk5(~K, c)) -> {KA.klt(~K, N.nzero(K), KA.ksub(~K, KB.klook(~K, C.Cert.yc(K, c), 1n), KB.klook(~K, C.Cert.yr(K, c), 1n))) == True{} : Bool}:
  (x, t) = h
  x

def hk5_e0(~K: N.Num, +c: C.Cert<K>, h: Hk5(~K, c)) -> {N.nofq(K, q0()) == Some{KB.klook(~K, C.Cert.pc(K, c), 0n)} : Maybe<&2, N.NC(K)>}:
  (x, t) = h
  (y, u) = t
  y

def hk5_e1(~K: N.Num, +c: C.Cert<K>, h: Hk5(~K, c)) -> {N.nofq(K, q0()) == Some{KB.klook(~K, C.Cert.pc(K, c), 1n)} : Maybe<&2, N.NC(K)>}:
  (x, t) = h
  (y, u) = t
  (v, w) = u
  v

def hk5_e2(~K: N.Num, +c: C.Cert<K>, h: Hk5(~K, c)) -> {N.nofq(K, q4()) == Some{KB.klook(~K, C.Cert.pc(K, c), 2n)} : Maybe<&2, N.NC(K)>}:
  (x, t) = h
  (y, u) = t
  (v, w) = u
  (g, r) = w
  g

def hk5_e3(~K: N.Num, +c: C.Cert<K>, h: Hk5(~K, c)) -> {N.nofq(K, q0()) == Some{KB.klook(~K, C.Cert.pc(K, c), 3n)} : Maybe<&2, N.NC(K)>}:
  (x, t) = h
  (y, u) = t
  (v, w) = u
  (g, r) = w
  r

# the parameters: the certificate's own parameter centers
def zp(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>) -> M.Vec(~F):
  C.pcenter(~K, ~F, ~H, c)

def hz(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, +hpr: {KA.kvle(~K, Nil{}, C.Cert.pr(K, c)) == True{} : Bool}) -> C.pinned(~K, ~F, ~H, c, zp(~K, ~F, ~H, c)):
  FV.rbnd_self(~F, zp(~K, ~F, ~H, c), C.pradii(~K, ~F, ~H, c), KA.kvle_ok(~K, ~F, ~H, Nil{}, C.Cert.pr(K, c), hpr))

# parameter i, held exactly by K as the rational q
def pval(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, +q: S.Q, +i: Nat, h: {N.nofq(K, q) == Some{KB.klook(~K, C.Cert.pc(K, c), i)} : Maybe<&2, N.NC(K)>}) -> {O.lookup(~F, zp(~K, ~F, ~H, c), i) == O.ofq(~F, q) : O.C(F)}:
  Equal.trans(O.C(F), O.lookup(~F, zp(~K, ~F, ~H, c), i), N.emap(K, F, H, KB.klook(~K, C.Cert.pc(K, c), i)), O.ofq(~F, q), Equal.sym(O.C(F), N.emap(K, F, H, KB.klook(~K, C.Cert.pc(K, c), i)), O.lookup(~F, zp(~K, ~F, ~H, c), i), CP.klook_ofk(~K, ~F, ~H, C.Cert.pc(K, c), i)), N.e_ofq(K, F, H)(q, KB.klook(~K, C.Cert.pc(K, c), i), h))

# |P - Z|^2 - 9 = 0 at Z = (u, v) gives it at Z = (u2, v2), for u = u2, v = v2
def eq_sub(~F: O.OField, +a: O.C(F), +b: O.C(F), +nine: O.C(F), +u: O.C(F), +v: O.C(F), +u2: O.C(F), +v2: O.C(F), eu: {u == u2 : O.C(F)}, ev: {v == v2 : O.C(F)}, h: {O.sub(~F, O.add(F, O.mul(F, O.sub(~F, a, u), O.sub(~F, a, u)), O.mul(F, O.sub(~F, b, v), O.sub(~F, b, v))), nine) == O.zero(F) : O.C(F)}) -> {O.sub(~F, O.add(F, O.mul(F, O.sub(~F, a, u2), O.sub(~F, a, u2)), O.mul(F, O.sub(~F, b, v2), O.sub(~F, b, v2))), nine) == O.zero(F) : O.C(F)}:
  %eu : {O.sub(~F, O.add(F, O.mul(F, O.sub(~F, a, _), O.sub(~F, a, _)), O.mul(F, O.sub(~F, b, v2), O.sub(~F, b, v2))), nine) == O.zero(F) : O.C(F)}
  %ev : {O.sub(~F, O.add(F, O.mul(F, O.sub(~F, a, u), O.sub(~F, a, u)), O.mul(F, O.sub(~F, b, _), O.sub(~F, b, _))), nine) == O.zero(F) : O.C(F)}
  h

def bfun2(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, +a: O.C(F), +b: O.C(F)) -> M.Vec(~F):
  C.bfun(~F, D.cc_block(), [a, b], zp(~K, ~F, ~H, c))

def eqs2.b(~F: O.OField, +x: O.C(F), h: M.Both(M.bnd(~F, x, O.zero(F)), Unit)) -> {x == O.zero(F) : O.C(F)}:
  (h2, hu) = h
  RL.bnd0_eq(~F, x, h2)

def eqs2.a(~F: O.OField, +x: O.C(F), +y: O.C(F), h: M.Both(M.bnd(~F, x, O.zero(F)), M.Both(M.bnd(~F, y, O.zero(F)), Unit))) -> M.Both({x == O.zero(F) : O.C(F)}, {y == O.zero(F) : O.C(F)}):
  (h1, ht) = h
  (RL.bnd0_eq(~F, x, h1), eqs2.b(~F, y, ht))

def nine(~F: O.OField) -> O.C(F):
  O.ofq(~F, S.Q{S.Zpos{p9()}, S.XH{}})

def L(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, +i: Nat) -> O.C(F):
  O.lookup(~F, zp(~K, ~F, ~H, c), i)

def E(~F: O.OField, +a: O.C(F), +b: O.C(F), +u: O.C(F), +v: O.C(F)) -> O.C(F):
  O.sub(~F, O.add(F, O.mul(F, O.sub(~F, a, u), O.sub(~F, a, u)), O.mul(F, O.sub(~F, b, v), O.sub(~F, b, v))), nine(~F))

# the block's equations vanish at (a, b): |P - A|^2 = 9, |P - B|^2 = 9
def eqs2(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, +a: O.C(F), +b: O.C(F), h: M.vbnd(~F, bfun2(~K, ~F, ~H, c, a, b), O.zero(F))) -> M.Both({E(~F, a, b, L(~K, ~F, ~H, c, 0n), L(~K, ~F, ~H, c, 1n)) == O.zero(F) : O.C(F)}, {E(~F, a, b, L(~K, ~F, ~H, c, 2n), L(~K, ~F, ~H, c, 3n)) == O.zero(F) : O.C(F)}):
  (h0, ha) = h
  eqs2.a(~F, E(~F, a, b, L(~K, ~F, ~H, c, 0n), L(~K, ~F, ~H, c, 1n)), E(~F, a, b, L(~K, ~F, ~H, c, 2n), L(~K, ~F, ~H, c, 3n)), ha)

# with A = (0, 0) and B = (4, 0): b^2 = 5
def sq5(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, +a: O.C(F), +b: O.C(F), +e0: {N.nofq(K, q0()) == Some{KB.klook(~K, C.Cert.pc(K, c), 0n)} : Maybe<&2, N.NC(K)>}, +e1: {N.nofq(K, q0()) == Some{KB.klook(~K, C.Cert.pc(K, c), 1n)} : Maybe<&2, N.NC(K)>}, +e2: {N.nofq(K, q4()) == Some{KB.klook(~K, C.Cert.pc(K, c), 2n)} : Maybe<&2, N.NC(K)>}, +e3: {N.nofq(K, q0()) == Some{KB.klook(~K, C.Cert.pc(K, c), 3n)} : Maybe<&2, N.NC(K)>}, h: M.Both({E(~F, a, b, L(~K, ~F, ~H, c, 0n), L(~K, ~F, ~H, c, 1n)) == O.zero(F) : O.C(F)}, {E(~F, a, b, L(~K, ~F, ~H, c, 2n), L(~K, ~F, ~H, c, 3n)) == O.zero(F) : O.C(F)})) -> {O.mul(F, b, b) == O.ofp(~F, p5()) : O.C(F)}:
  (h1, h2) = h
  +g1 = eq_sub(~F, a, b, nine(~F), L(~K, ~F, ~H, c, 0n), L(~K, ~F, ~H, c, 1n), O.ofq(~F, q0()), O.ofq(~F, q0()), pval(~K, ~F, ~H, c, q0(), 0n, e0), pval(~K, ~F, ~H, c, q0(), 1n, e1), h1)
  +g2 = eq_sub(~F, a, b, nine(~F), L(~K, ~F, ~H, c, 2n), L(~K, ~F, ~H, c, 3n), O.ofq(~F, q4()), O.ofq(~F, q0()), pval(~K, ~F, ~H, c, q4(), 2n, e2), pval(~K, ~F, ~H, c, q0(), 3n, e3), h2)
  alg_b(~F, a, b, g1, alg_a(~F, a, b, g1, g2))

# the center has two coordinates
def len2(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, hyc: {KA.klen(~K, C.Cert.yc(K, c)) == 2n : Nat}) -> {M.len(~F, C.center(~K, ~F, ~H, c)) == 2n : Nat}:
  Equal.trans(Nat, M.len(~F, C.center(~K, ~F, ~H, c)), KA.klen(~K, C.Cert.yc(K, c)), 2n, CP.len_ofkv(~K, ~F, ~H, C.Cert.yc(K, c)), hyc)

def lt2(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, hyc: {KA.klen(~K, C.Cert.yc(K, c)) == 2n : Nat}) -> {KA.natle(2n, M.len(~F, C.center(~K, ~F, ~H, c))) == True{} : Bool}:
  %Equal.sym(Nat, M.len(~F, C.center(~K, ~F, ~H, c)), 2n, len2(~K, ~F, ~H, c, hyc)) : {KA.natle(2n, _) == True{} : Bool}
  {==}

def Zero(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, +y: M.Vec(~F)) -> Data:
  M.Both(C.ball(~K, ~F, ~H, c, y), M.vbnd(~F, C.bfun(~F, D.cc_block(), y, zp(~K, ~F, ~H, c)), O.zero(F)))

# The theorem
# -----------

def Root5(~F: O.OField) -> Data:
  Sigma<&2, &2, O.C(F), x => M.Both(O.lt(F, O.zero(F), x), {O.mul(F, x, x) == O.ofp(~F, p5()) : O.C(F)})>

def hk_yc(~K: N.Num, +c: C.Cert<K>, hk: Hk(~K, c)) -> {KA.klen(~K, C.Cert.yc(K, c)) == 2n : Nat}:
  (ok, h1) = hk
  (hpr, h2) = h1
  (hyc, h3) = h2
  hyc

def hk_ok(~K: N.Num, +c: C.Cert<K>, hk: Hk(~K, c)) -> {CK.check(~K, D.cc_block(), c) == True{} : Bool}:
  (ok, h1) = hk
  ok

def hk_pr.1(~K: N.Num, +c: C.Cert<K>, h1: M.Both({KA.kvle(~K, Nil{}, C.Cert.pr(K, c)) == True{} : Bool}, M.Both({KA.klen(~K, C.Cert.yc(K, c)) == 2n : Nat}, Hk5(~K, c)))) -> {KA.kvle(~K, Nil{}, C.Cert.pr(K, c)) == True{} : Bool}:
  (hpr, h2) = h1
  hpr

def hk_pr(~K: N.Num, +c: C.Cert<K>, hk: Hk(~K, c)) -> {KA.kvle(~K, Nil{}, C.Cert.pr(K, c)) == True{} : Bool}:
  (ok, h1) = hk
  hk_pr.1(~K, c, h1)

def hk5(~K: N.Num, +c: C.Cert<K>, hk: Hk(~K, c)) -> Hk5(~K, c):
  (ok, h1) = hk
  (hpr, h2) = h1
  (hyc, h3) = h2
  h3

def hk_lt(~K: N.Num, +c: C.Cert<K>, +hk: Hk(~K, c)) -> {KA.klt(~K, N.nzero(K), KA.ksub(~K, KB.klook(~K, C.Cert.yc(K, c), 1n), KB.klook(~K, C.Cert.yr(K, c), 1n))) == True{} : Bool}:
  hk5_lt(~K, c, hk5(~K, c, hk))

def hk_e0(~K: N.Num, +c: C.Cert<K>, +hk: Hk(~K, c)) -> {N.nofq(K, q0()) == Some{KB.klook(~K, C.Cert.pc(K, c), 0n)} : Maybe<&2, N.NC(K)>}:
  hk5_e0(~K, c, hk5(~K, c, hk))

def hk_e1(~K: N.Num, +c: C.Cert<K>, +hk: Hk(~K, c)) -> {N.nofq(K, q0()) == Some{KB.klook(~K, C.Cert.pc(K, c), 1n)} : Maybe<&2, N.NC(K)>}:
  hk5_e1(~K, c, hk5(~K, c, hk))

def hk_e2(~K: N.Num, +c: C.Cert<K>, +hk: Hk(~K, c)) -> {N.nofq(K, q4()) == Some{KB.klook(~K, C.Cert.pc(K, c), 2n)} : Maybe<&2, N.NC(K)>}:
  hk5_e2(~K, c, hk5(~K, c, hk))

def hk_e3(~K: N.Num, +c: C.Cert<K>, +hk: Hk(~K, c)) -> {N.nofq(K, q0()) == Some{KB.klook(~K, C.Cert.pc(K, c), 3n)} : Maybe<&2, N.NC(K)>}:
  hk5_e3(~K, c, hk5(~K, c, hk))

def root.ab(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, +hk: Hk(~K, c), +a: O.C(F), +b: O.C(F), h: Zero(~K, ~F, ~H, c, [a, b])) -> Root5(~F):
  (+hb, hf) = h
  (b, (BA.box_pos(~K, ~F, ~H, c, [a, b], hb, 1n, lt2(~K, ~F, ~H, c, hk_yc(~K, c, hk)), hk_lt(~K, c, hk)), sq5(~K, ~F, ~H, c, a, b, hk_e0(~K, c, hk), hk_e1(~K, c, hk), hk_e2(~K, c, hk), hk_e3(~K, c, hk), eqs2(~K, ~F, ~H, c, a, b, hf))))

def blen(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, hyc: {KA.klen(~K, C.Cert.yc(K, c)) == 2n : Nat}, +y: M.Vec(~F), h: Zero(~K, ~F, ~H, c, y)) -> {M.len(~F, y) == 2n : Nat}:
  (hb, hf) = h
  Equal.trans(Nat, M.len(~F, y), M.len(~F, C.center(~K, ~F, ~H, c)), 2n, BA.ball_len(~K, ~F, ~H, c, y, hb), len2(~K, ~F, ~H, c, hyc))

# the zero has two coordinates (its box's dimension)
def root.y(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, +hk: Hk(~K, c), y: M.Vec(~F), h: Zero(~K, ~F, ~H, c, y)) -> Root5(~F):
  match y:
    case Nil{}:
      FO.absurd(Root5(~F), FV.zero_ne(1n, blen(~K, ~F, ~H, c, hk_yc(~K, c, hk), Nil{}, h)))
    case Con{+a, Nil{}}:
      FO.absurd(Root5(~F), FV.zero_ne(0n, LN.succ_inj(0n, 1n, blen(~K, ~F, ~H, c, hk_yc(~K, c, hk), [a], h))))
    case Con{+a, Con{+b, Nil{}}}:
      root.ab(~K, ~F, ~H, c, hk, a, b, h)
    case Con{+a, Con{+b, Con{+x, +rest}}}:
      FO.absurd(Root5(~F), FV.succ_ne(M.len(~F, rest), LN.succ_inj(1n+M.len(~F, rest), 0n, LN.succ_inj(2n+M.len(~F, rest), 1n, blen(~K, ~F, ~H, c, hk_yc(~K, c, hk), Con{a, Con{b, Con{x, rest}}}, h)))))

def root.ex(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: C.Cert<K>, +hk: Hk(~K, c), s: Sigma<&2, &2, M.Vec(~F), y => Zero(~K, ~F, ~H, c, y)>) -> Root5(~F):
  (y, h) = s
  root.y(~K, ~F, ~H, c, hk, y, h)

def root.go(~K: N.Num, ~F: O.OField, ~R: CR.Complete<F>, ~H: N.Emb<K, F>, +c: C.Cert<K>, +hk: Hk(~K, c)) -> Root5(~F):
  root.ex(~K, ~F, ~H, c, hk, BA.cert_exists(~K, ~F, ~R, ~H, D.cc_block(), c, hk_ok(~K, c, hk), zp(~K, ~F, ~H, c), hz(~K, ~F, ~H, c, hk_pr(~K, c, hk))))

# In every complete ordered field, 5 has a positive square root
def sqrt5(~F: O.OField, ~R: CR.Complete<F>) -> Root5(~F):
  root.go(~KI.dnum(), ~F, ~R, ~KI.demb(~F), D.cc_cert(), ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, ({==}, {==}))))))))
