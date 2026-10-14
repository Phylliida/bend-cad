# Entrywise bounds on vectors and matrices in every ordered field (the
# certificate's box arithmetic in F). Vectors are lists read with trailing
# zeros. Untrusted: proofs only.
#   C.rbnd(d, r): |d_i| <= r_i            (spec/cert.bend)
#   rle(u, w):    u_i <= w_i
#   rnn(w):       0 <= w_i
#   mbnd(M, B):   |M_ij| <= B_ij
#   mnn(B):       0 <= B_ij

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/cert.bend as C
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./fmat.bend as FM
import ./dmat.bend as DM
import ./nat.bend as LN
import ./qemb.bend as QE

# Definitions
# -----------

# u_i <= w_i for every i
def rle(~F: O.OField, u: M.Vec(~F), w: M.Vec(~F)) -> Data:
  match u w:
    case Nil{} Nil{}:
      Unit
    case Nil{} Con{b, ws}:
      M.Both(O.le(~F, O.zero(F), b), rle(~F, Nil{}, ws))
    case Con{a, us} Nil{}:
      M.Both(O.le(~F, a, O.zero(F)), rle(~F, us, Nil{}))
    case Con{a, us} Con{b, ws}:
      M.Both(O.le(~F, a, b), rle(~F, us, ws))

# 0 <= w_i for every i
def rnn(~F: O.OField, w: M.Vec(~F)) -> Data:
  rle(~F, Nil{}, w)

# |M_ij| <= B_ij for every i, j
def mbnd(~F: O.OField, m: M.Mat(~F), b: M.Mat(~F)) -> Data:
  match m b:
    case Nil{} b:
      Unit
    case Con{r, rs} Nil{}:
      M.Both(C.rbnd(~F, r, Nil{}), mbnd(~F, rs, Nil{}))
    case Con{r, rs} Con{t, ts}:
      M.Both(C.rbnd(~F, r, t), mbnd(~F, rs, ts))

# 0 <= B_ij for every i, j
def mnn(~F: O.OField, b: M.Mat(~F)) -> Data:
  match b:
    case Nil{}:
      Unit
    case Con{r, rs}:
      M.Both(rnn(~F, r), mnn(~F, rs))

# the first entry and the rest (zero and empty past the end)
def vhd(~F: O.OField, v: M.Vec(~F)) -> O.C(F):
  match v:
    case Nil{}:
      O.zero(F)
    case Con{a, t}:
      a

def vtl(~F: O.OField, v: M.Vec(~F)) -> M.Vec(~F):
  match v:
    case Nil{}:
      Nil{}
    case Con{a, t}:
      t

# Taking vectors apart
# --------------------

def rbnd_head(~F: O.OField, +a: O.C(F), +ds: M.Vec(~F), r: M.Vec(~F), h: C.rbnd(~F, Con{a, ds}, r)) -> M.bnd(~F, a, vhd(~F, r)):
  match r:
    case Nil{}:
      (ha, hs) = h
      ha
    case Con{s, rs}:
      (ha, hs) = h
      ha

def rbnd_tail(~F: O.OField, +a: O.C(F), +ds: M.Vec(~F), r: M.Vec(~F), h: C.rbnd(~F, Con{a, ds}, r)) -> C.rbnd(~F, ds, vtl(~F, r)):
  match r:
    case Nil{}:
      (ha, hs) = h
      hs
    case Con{s, rs}:
      (ha, hs) = h
      hs

def rnn_head(~F: O.OField, w: M.Vec(~F), h: rnn(~F, w)) -> O.le(~F, O.zero(F), vhd(~F, w)):
  match w:
    case Nil{}:
      FO.le_refl(~F, O.zero(F))
    case Con{b, ws}:
      (hb, hs) = h
      hb

def rnn_tail(~F: O.OField, w: M.Vec(~F), h: rnn(~F, w)) -> rnn(~F, vtl(~F, w)):
  match w:
    case Nil{}:
      Unit{}
    case Con{b, ws}:
      (hb, hs) = h
      hs

def dot_nil_r(~F: O.OField, xs: M.Vec(~F)) -> {O.zero(F) == M.dot(~F, xs, Nil{}) : O.C(F)}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

# dot(b, w) = b_0 w_0 + dot(tail b, tail w)
def dot_cons(~F: O.OField, b: M.Vec(~F), +w: M.Vec(~F)) -> {M.dot(~F, b, w) == O.add(F, O.mul(F, vhd(~F, b), vhd(~F, w)), M.dot(~F, vtl(~F, b), vtl(~F, w))) : O.C(F)}:
  match b w:
    case Nil{} w:
      FR.fring_eq(~F, [vhd(~F, w)], E.ZCst{S.Z0{}}, E.ZAdd{E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZCst{S.Z0{}}}, {==})
    case Con{+x, +xs} Nil{}:
      %dot_nil_r(~F, xs) : {O.zero(F) == O.add(F, O.mul(F, x, O.zero(F)), _) : O.C(F)}
      FR.fring_eq(~F, [x], E.ZCst{S.Z0{}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}}, {==})
    case Con{x, xs} Con{y, ys}:
      {==}

def rle_head(~F: O.OField, u: M.Vec(~F), w: M.Vec(~F), h: rle(~F, u, w)) -> O.le(~F, vhd(~F, u), vhd(~F, w)):
  match u w:
    case Nil{} Nil{}:
      FO.le_refl(~F, O.zero(F))
    case Nil{} Con{b, ws}:
      (hb, hs) = h
      hb
    case Con{a, us} Nil{}:
      (hb, hs) = h
      hb
    case Con{a, us} Con{b, ws}:
      (hb, hs) = h
      hb

def rle_tail(~F: O.OField, u: M.Vec(~F), w: M.Vec(~F), h: rle(~F, u, w)) -> rle(~F, vtl(~F, u), vtl(~F, w)):
  match u w:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} Con{b, ws}:
      (hb, hs) = h
      hs
    case Con{a, us} Nil{}:
      (hb, hs) = h
      hs
    case Con{a, us} Con{b, ws}:
      (hb, hs) = h
      hs

# a box bound, put together from its head and tail
def rbnd_mk(~F: O.OField, +a: O.C(F), +ds: M.Vec(~F), r: M.Vec(~F), h1: M.bnd(~F, a, vhd(~F, r)), h2: C.rbnd(~F, ds, vtl(~F, r))) -> C.rbnd(~F, Con{a, ds}, r):
  match r:
    case Nil{}:
      (h1, h2)
    case Con{s, rs}:
      (h1, h2)

# Sums and products of nonnegatives
# ---------------------------------

def dot_nonneg(~F: O.OField, b: M.Vec(~F), w: M.Vec(~F), hb: rnn(~F, b), hw: rnn(~F, w)) -> O.le(~F, O.zero(F), M.dot(~F, b, w)):
  match b w:
    case Nil{} w:
      FO.le_refl(~F, O.zero(F))
    case Con{x, xs} Nil{}:
      FO.le_refl(~F, O.zero(F))
    case Con{+x, +xs} Con{+y, +ys}:
      (hx, hxs) = hb
      (hy, hys) = hw
      FO.nonneg_add(~F, O.mul(F, x, y), M.dot(~F, xs, ys), FO.mul_nonneg(~F, x, y, hx, hy), dot_nonneg(~F, xs, ys, hxs, hys))

def matvec_nonneg(~F: O.OField, b: M.Mat(~F), +w: M.Vec(~F), hb: mnn(~F, b), +hw: rnn(~F, w)) -> rnn(~F, M.matvec(~F, b, w)):
  match b:
    case Nil{}:
      Unit{}
    case Con{+r, +rs}:
      (hr, hrs) = hb
      (dot_nonneg(~F, r, w, hr, hw), matvec_nonneg(~F, rs, w, hrs, hw))

# Products of bounded things
# --------------------------

# |r . d| <= b . w, for |r| <= b and |d| <= w
def dot_bnd(~F: O.OField, r: M.Vec(~F), +b: M.Vec(~F), d: M.Vec(~F), +w: M.Vec(~F), +hr: C.rbnd(~F, r, b), +hd: C.rbnd(~F, d, w), +hb: rnn(~F, b), +hw: rnn(~F, w)) -> M.bnd(~F, M.dot(~F, r, d), M.dot(~F, b, w)):
  match r d:
    case Nil{} d:
      FM.bnd_zero(~F, M.dot(~F, b, w), dot_nonneg(~F, b, w, hb, hw))
    case Con{x, xs} Nil{}:
      FM.bnd_zero(~F, M.dot(~F, b, w), dot_nonneg(~F, b, w, hb, hw))
    case Con{+x, +xs} Con{+y, +ys}:
      FM.bnd_eq(~F, M.dot(~F, Con{x, xs}, Con{y, ys}), O.add(F, O.mul(F, vhd(~F, b), vhd(~F, w)), M.dot(~F, vtl(~F, b), vtl(~F, w))), M.dot(~F, b, w),
        Equal.sym(O.C(F), M.dot(~F, b, w), O.add(F, O.mul(F, vhd(~F, b), vhd(~F, w)), M.dot(~F, vtl(~F, b), vtl(~F, w))), dot_cons(~F, b, w)),
        FM.bnd_add(~F, O.mul(F, x, y), O.mul(F, vhd(~F, b), vhd(~F, w)), M.dot(~F, xs, ys), M.dot(~F, vtl(~F, b), vtl(~F, w)),
          FM.bnd_mul(~F, x, vhd(~F, b), y, vhd(~F, w), rbnd_head(~F, x, xs, b, hr), rbnd_head(~F, y, ys, w, hd)),
          dot_bnd(~F, xs, vtl(~F, b), ys, vtl(~F, w), rbnd_tail(~F, x, xs, b, hr), rbnd_tail(~F, y, ys, w, hd), rnn_tail(~F, b, hb), rnn_tail(~F, w, hw))))

# |M d| <= B w, for |M| <= B and |d| <= w (B, w not negative)
def mbnd_matvec(~F: O.OField, m: M.Mat(~F), b: M.Mat(~F), +d: M.Vec(~F), +w: M.Vec(~F), hm: mbnd(~F, m, b), +hd: C.rbnd(~F, d, w), hb: mnn(~F, b), +hw: rnn(~F, w)) -> C.rbnd(~F, M.matvec(~F, m, d), M.matvec(~F, b, w)):
  match m b:
    case Nil{} b:
      Unit{}
    case Con{+r, +rs} Nil{}:
      (hr, hrs) = hm
      (dot_bnd(~F, r, Nil{}, d, w, hr, hd, Unit{}, hw), mbnd_matvec(~F, rs, Nil{}, d, w, hrs, hd, Unit{}, hw))
    case Con{+r, +rs} Con{+t, +ts}:
      (hr, hrs) = hm
      (ht, hts) = hb
      (dot_bnd(~F, r, t, d, w, hr, hd, ht, hw), mbnd_matvec(~F, rs, ts, d, w, hrs, hd, hts, hw))

# Monotonicity, negation, sums
# ----------------------------

def rbnd_mono(~F: O.OField, d: M.Vec(~F), +r: M.Vec(~F), +t: M.Vec(~F), +h: C.rbnd(~F, d, r), +hrt: rle(~F, r, t)) -> C.rbnd(~F, d, t):
  match d:
    case Nil{}:
      Unit{}
    case Con{+a, +ds}:
      rbnd_mk(~F, a, ds, t, FM.bnd_mono(~F, a, vhd(~F, r), vhd(~F, t), rbnd_head(~F, a, ds, r, h), FM.sub_nonneg(~F, vhd(~F, r), vhd(~F, t), rle_head(~F, r, t, hrt))), rbnd_mono(~F, ds, vtl(~F, r), vtl(~F, t), rbnd_tail(~F, a, ds, r, h), rle_tail(~F, r, t, hrt)))

def rbnd_neg(~F: O.OField, u: M.Vec(~F), +r: M.Vec(~F), +h: C.rbnd(~F, u, r)) -> C.rbnd(~F, M.vneg(~F, u), r):
  match u:
    case Nil{}:
      Unit{}
    case Con{+a, +us}:
      rbnd_mk(~F, O.neg(F, a), M.vneg(~F, us), r, FM.bnd_neg(~F, a, vhd(~F, r), rbnd_head(~F, a, us, r, h)), rbnd_neg(~F, us, vtl(~F, r), rbnd_tail(~F, a, us, r, h)))

# |a - a| <= s, for 0 <= s
def bnd_sself(~F: O.OField, +a: O.C(F), +s: O.C(F), +hs: O.le(~F, O.zero(F), s)) -> M.bnd(~F, O.sub(~F, a, a), s):
  %Equal.sym(O.C(F), O.sub(~F, a, a), O.zero(F), O.add_neg(F)(a)) : M.bnd(~F, _, s)
  FM.bnd_zero(~F, s, hs)

# |u_i - u_i| <= r_i, for r not negative
def rbnd_self(~F: O.OField, u: M.Vec(~F), +r: M.Vec(~F), +h: rnn(~F, r)) -> C.rbnd(~F, C.vsub(~F, u, u), r):
  match u:
    case Nil{}:
      Unit{}
    case Con{+a, +us}:
      rbnd_mk(~F, O.sub(~F, a, a), C.vsub(~F, us, us), r, bnd_sself(~F, a, vhd(~F, r), rnn_head(~F, r, h)), rbnd_self(~F, us, vtl(~F, r), rnn_tail(~F, r, h)))

# Lengths
# -------

def succ_inj(+a: Nat, +b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  %e : {a == LN.pred(_) : Nat}
  {==}

def natp(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+k:
      Empty

# 0 is not 1 + k
def zero_ne(+k: Nat, e: {0n == 1n+k : Nat}) -> Empty:
  %e : natp(_)
  Unit{}

def succ_ne(+k: Nat, e: {1n+k == 0n : Nat}) -> Empty:
  zero_ne(k, Equal.sym(Nat, 1n+k, 0n, e))

# the number of rows
def rows(~F: O.OField, a: M.Mat(~F)) -> Nat:
  match a:
    case Nil{}:
      0n
    case Con{r, rs}:
      1n+rows(~F, rs)

# y fitted to its own length is y
def fit_len(~F: O.OField, n: Nat, y: M.Vec(~F), h: {M.len(~F, y) == n : Nat}) -> {C.fit(~F, n, y) == y : M.Vec(~F)}:
  match n y:
    case 0n Nil{}:
      {==}
    case 0n Con{+a, +rest}:
      FO.absurd({C.fit(~F, 0n, Con{a, rest}) == Con{a, rest} : M.Vec(~F)}, succ_ne(M.len(~F, rest), h))
    case 1n++k Nil{}:
      FO.absurd({C.fit(~F, 1n+k, Nil{}) == Nil{} : M.Vec(~F)}, zero_ne(k, h))
    case 1n+k Con{+a, +rest}:
      %fit_len(~F, k, rest, succ_inj(M.len(~F, rest), k, h)) : {Con{a, C.fit(~F, k, rest)} == Con{a, _} : M.Vec(~F)}
      {==}

# Concatenations
# --------------

# (u1 ++ w1) - (u2 ++ w2) = (u1 - u2) ++ (w1 - w2), for u1, u2 of equal length
def vsub_app(~F: O.OField, u1: M.Vec(~F), u2: M.Vec(~F), +w1: M.Vec(~F), +w2: M.Vec(~F), h: {M.len(~F, u1) == M.len(~F, u2) : Nat}) -> {C.vsub(~F, C.app(~F, u1, w1), C.app(~F, u2, w2)) == C.app(~F, C.vsub(~F, u1, u2), C.vsub(~F, w1, w2)) : M.Vec(~F)}:
  match u1 u2:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+b, +bs}:
      FO.absurd({C.vsub(~F, w1, C.app(~F, Con{b, bs}, w2)) == C.app(~F, C.vsub(~F, Nil{}, Con{b, bs}), C.vsub(~F, w1, w2)) : M.Vec(~F)}, zero_ne(M.len(~F, bs), h))
    case Con{+a, +as} Nil{}:
      FO.absurd({C.vsub(~F, C.app(~F, Con{a, as}, w1), w2) == C.app(~F, C.vsub(~F, Con{a, as}, Nil{}), C.vsub(~F, w1, w2)) : M.Vec(~F)}, succ_ne(M.len(~F, as), h))
    case Con{+a, +as} Con{+b, +bs}:
      %vsub_app(~F, as, bs, w1, w2, succ_inj(M.len(~F, as), M.len(~F, bs), h)) : {Con{O.sub(~F, a, b), C.vsub(~F, C.app(~F, as, w1), C.app(~F, bs, w2))} == Con{O.sub(~F, a, b), _} : M.Vec(~F)}
      {==}

# (u ++ w) . (a ++ b) = u . a + w . b, for u, a of equal length
def dot_app(~F: O.OField, u: M.Vec(~F), +w: M.Vec(~F), a: M.Vec(~F), +b: M.Vec(~F), h: {M.len(~F, u) == M.len(~F, a) : Nat}) -> {M.dot(~F, C.app(~F, u, w), C.app(~F, a, b)) == O.add(F, M.dot(~F, u, a), M.dot(~F, w, b)) : O.C(F)}:
  match u a:
    case Nil{} Nil{}:
      FR.fring_eq(~F, [M.dot(~F, w, b)], E.ZVar{0n}, E.ZAdd{E.ZCst{S.Z0{}}, E.ZVar{0n}}, {==})
    case Nil{} Con{+y, +ys}:
      FO.absurd({M.dot(~F, w, C.app(~F, Con{y, ys}, b)) == O.add(F, O.zero(F), M.dot(~F, w, b)) : O.C(F)}, zero_ne(M.len(~F, ys), h))
    case Con{+x, +xs} Nil{}:
      FO.absurd({M.dot(~F, C.app(~F, Con{x, xs}, w), b) == O.add(F, O.zero(F), M.dot(~F, w, b)) : O.C(F)}, succ_ne(M.len(~F, xs), h))
    case Con{+x, +xs} Con{+y, +ys}:
      %Equal.sym(O.C(F), M.dot(~F, C.app(~F, xs, w), C.app(~F, ys, b)), O.add(F, M.dot(~F, xs, ys), M.dot(~F, w, b)), dot_app(~F, xs, w, ys, b, succ_inj(M.len(~F, xs), M.len(~F, ys), h))) : {O.add(F, O.mul(F, x, y), _) == O.add(F, O.add(F, O.mul(F, x, y), M.dot(~F, xs, ys)), M.dot(~F, w, b)) : O.C(F)}
      FR.fring_eq(~F, [O.mul(F, x, y), M.dot(~F, xs, ys), M.dot(~F, w, b)], E.ZAdd{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}, E.ZAdd{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, {==})

# w . (z - z) = 0
def dot_self0(~F: O.OField, w: M.Vec(~F), z: M.Vec(~F)) -> {O.zero(F) == M.dot(~F, w, C.vsub(~F, z, z)) : O.C(F)}:
  match w z:
    case Nil{} z:
      {==}
    case Con{x, xs} Nil{}:
      {==}
    case Con{+x, xs} Con{+y, ys}:
      %dot_self0(~F, xs, ys) : {O.zero(F) == O.add(F, O.mul(F, x, O.sub(~F, y, y)), _) : O.C(F)}
      FR.fring_eq(~F, [x, y], E.ZCst{S.Z0{}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZSub{E.ZVar{1n}, E.ZVar{1n}}}, E.ZCst{S.Z0{}}}, {==})

# Linearity of dot in its second argument
# ---------------------------------------

# r . u - r . v = r . (u - v)
def dot_r_vsub(~F: O.OField, r: M.Vec(~F), u: M.Vec(~F), v: M.Vec(~F)) -> {O.sub(~F, M.dot(~F, r, u), M.dot(~F, r, v)) == M.dot(~F, r, C.vsub(~F, u, v)) : O.C(F)}:
  match r u v:
    case Nil{} u v:
      FR.fring_eq(~F, Nil{}, E.ZSub{E.ZCst{S.Z0{}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})
    case Con{x, xs} Nil{} Nil{}:
      FR.fring_eq(~F, Nil{}, E.ZSub{E.ZCst{S.Z0{}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})
    case Con{+x, +xs} Nil{} Con{+b, +bs}:
      %dot_r_vsub(~F, xs, Nil{}, bs) : {O.sub(~F, O.zero(F), O.add(F, O.mul(F, x, b), M.dot(~F, xs, bs))) == O.add(F, O.mul(F, x, O.neg(F, b)), _) : O.C(F)}
      %dot_nil_r(~F, xs) : {O.sub(~F, O.zero(F), O.add(F, O.mul(F, x, b), M.dot(~F, xs, bs))) == O.add(F, O.mul(F, x, O.neg(F, b)), O.sub(~F, _, M.dot(~F, xs, bs))) : O.C(F)}
      FR.fring_eq(~F, [x, b, M.dot(~F, xs, bs)], E.ZSub{E.ZCst{S.Z0{}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZNeg{E.ZVar{1n}}}, E.ZSub{E.ZCst{S.Z0{}}, E.ZVar{2n}}}, {==})
    case Con{+x, +xs} Con{+a, +as} Nil{}:
      FR.fring_eq(~F, [M.dot(~F, Con{x, xs}, Con{a, as})], E.ZSub{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZVar{0n}, {==})
    case Con{+x, +xs} Con{+a, +as} Con{+b, +bs}:
      %dot_r_vsub(~F, xs, as, bs) : {O.sub(~F, O.add(F, O.mul(F, x, a), M.dot(~F, xs, as)), O.add(F, O.mul(F, x, b), M.dot(~F, xs, bs))) == O.add(F, O.mul(F, x, O.sub(~F, a, b)), _) : O.C(F)}
      FR.fring_eq(~F, [x, a, b, M.dot(~F, xs, as), M.dot(~F, xs, bs)], E.ZSub{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{3n}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{4n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZSub{E.ZVar{1n}, E.ZVar{2n}}}, E.ZSub{E.ZVar{3n}, E.ZVar{4n}}}, {==})

# Heads and tails of sums
# -----------------------

def vadd_nil_r(~F: O.OField, u: M.Vec(~F)) -> {u == M.vadd(~F, u, Nil{}) : M.Vec(~F)}:
  match u:
    case Nil{}:
      {==}
    case Con{a, us}:
      {==}

def vhd_vadd(~F: O.OField, u: M.Vec(~F), w: M.Vec(~F)) -> {O.add(F, vhd(~F, u), vhd(~F, w)) == vhd(~F, M.vadd(~F, u, w)) : O.C(F)}:
  match u w:
    case Nil{} w:
      FR.fring_eq(~F, [vhd(~F, w)], E.ZAdd{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZVar{0n}, {==})
    case Con{+a, us} Nil{}:
      FR.fring_eq(~F, [a], E.ZAdd{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZVar{0n}, {==})
    case Con{a, us} Con{b, ws}:
      {==}

def vtl_vadd(~F: O.OField, u: M.Vec(~F), w: M.Vec(~F)) -> {M.vadd(~F, vtl(~F, u), vtl(~F, w)) == vtl(~F, M.vadd(~F, u, w)) : M.Vec(~F)}:
  match u w:
    case Nil{} w:
      {==}
    case Con{a, +us} Nil{}:
      Equal.sym(M.Vec(~F), us, M.vadd(~F, us, Nil{}), vadd_nil_r(~F, us))
    case Con{a, us} Con{b, ws}:
      {==}

# Scaling
# -------

def rnn_scale(~F: O.OField, +s: O.C(F), +hs: O.le(~F, O.zero(F), s), r: M.Vec(~F), h: rnn(~F, r)) -> rnn(~F, M.vscale(~F, s, r)):
  match r:
    case Nil{}:
      Unit{}
    case Con{+x, xs}:
      (hx, hxs) = h
      (FO.mul_nonneg(~F, s, x, hs, hx), rnn_scale(~F, s, hs, xs, hxs))

# r . (s w) = s (r . w)
def dot_vscale_r(~F: O.OField, r: M.Vec(~F), +s: O.C(F), w: M.Vec(~F)) -> {O.mul(F, s, M.dot(~F, r, w)) == M.dot(~F, r, M.vscale(~F, s, w)) : O.C(F)}:
  match r w:
    case Nil{} w:
      FR.fring_eq(~F, [s], E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})
    case Con{x, xs} Nil{}:
      FR.fring_eq(~F, [s], E.ZMul{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})
    case Con{+x, +xs} Con{+y, +ys}:
      %dot_vscale_r(~F, xs, s, ys) : {O.mul(F, s, O.add(F, O.mul(F, x, y), M.dot(~F, xs, ys))) == O.add(F, O.mul(F, x, O.mul(F, s, y)), _) : O.C(F)}
      FR.fring_eq(~F, [s, x, y, M.dot(~F, xs, ys)], E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZVar{2n}}, E.ZVar{3n}}}, E.ZAdd{E.ZMul{E.ZVar{1n}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}, {==})

# B (s w) = s (B w)
def matvec_vscale(~F: O.OField, b: M.Mat(~F), +s: O.C(F), +w: M.Vec(~F)) -> {M.vscale(~F, s, M.matvec(~F, b, w)) == M.matvec(~F, b, M.vscale(~F, s, w)) : M.Vec(~F)}:
  match b:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %dot_vscale_r(~F, r, s, w) : {Con{O.mul(F, s, M.dot(~F, r, w)), M.vscale(~F, s, M.matvec(~F, rs, w))} == Con{_, M.matvec(~F, rs, M.vscale(~F, s, w))} : M.Vec(~F)}
      %matvec_vscale(~F, rs, s, w) : {Con{O.mul(F, s, M.dot(~F, r, w)), M.vscale(~F, s, M.matvec(~F, rs, w))} == Con{O.mul(F, s, M.dot(~F, r, w)), _} : M.Vec(~F)}
      {==}

# s u + s w = s (u + w)
def vadd_vscale(~F: O.OField, +s: O.C(F), u: M.Vec(~F), w: M.Vec(~F)) -> {M.vadd(~F, M.vscale(~F, s, u), M.vscale(~F, s, w)) == M.vscale(~F, s, M.vadd(~F, u, w)) : M.Vec(~F)}:
  match u w:
    case Nil{} w:
      {==}
    case Con{a, us} Nil{}:
      {==}
    case Con{+a, +us} Con{+b, +ws}:
      %vadd_vscale(~F, s, us, ws) : {Con{O.add(F, O.mul(F, s, a), O.mul(F, s, b)), M.vadd(~F, M.vscale(~F, s, us), M.vscale(~F, s, ws))} == Con{O.mul(F, s, O.add(F, a, b)), _} : M.Vec(~F)}
      %Equal.sym(O.C(F), O.mul(F, s, O.add(F, a, b)), O.add(F, O.mul(F, s, a), O.mul(F, s, b)), O.mul_add(F)(s, a, b)) : {Con{O.add(F, O.mul(F, s, a), O.mul(F, s, b)), M.vadd(~F, M.vscale(~F, s, us), M.vscale(~F, s, ws))} == Con{_, M.vadd(~F, M.vscale(~F, s, us), M.vscale(~F, s, ws))} : M.Vec(~F)}
      {==}

# s (q r) = (q s) r
def vscale2(~F: O.OField, +q: O.C(F), +s: O.C(F), r: M.Vec(~F)) -> {M.vscale(~F, s, M.vscale(~F, q, r)) == M.vscale(~F, O.mul(F, q, s), r) : M.Vec(~F)}:
  match r:
    case Nil{}:
      {==}
    case Con{+x, +xs}:
      %vscale2(~F, q, s, xs) : {Con{O.mul(F, s, O.mul(F, q, x)), M.vscale(~F, s, M.vscale(~F, q, xs))} == Con{O.mul(F, O.mul(F, q, s), x), _} : M.Vec(~F)}
      %FR.fring_eq(~F, [q, s, x], E.ZMul{E.ZVar{1n}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, {==}) : {Con{O.mul(F, s, O.mul(F, q, x)), M.vscale(~F, s, M.vscale(~F, q, xs))} == Con{_, M.vscale(~F, s, M.vscale(~F, q, xs))} : M.Vec(~F)}
      {==}

# a <= b from 0 <= b - a
def le_of_sub(~F: O.OField, +a: O.C(F), +b: O.C(F), h: O.le(~F, O.zero(F), O.sub(~F, b, a))) -> O.le(~F, a, b):
  match h:
    case Inl{l}:
      Inl{QE.lt_of_sub(~F, a, b, l)}
    case Inr{e}:
      Inr{Equal.sym(O.C(F), b, a, FO.eq_of_sub(~F, b, a, Equal.sym(O.C(F), O.zero(F), O.sub(~F, b, a), e)))}

# s a <= s b for a <= b and s >= 0
def mul_le(~F: O.OField, +s: O.C(F), +a: O.C(F), +b: O.C(F), hs: O.le(~F, O.zero(F), s), h: O.le(~F, a, b)) -> O.le(~F, O.mul(F, s, a), O.mul(F, s, b)):
  le_of_sub(~F, O.mul(F, s, a), O.mul(F, s, b), FM.nn_eq(~F, O.sub(~F, O.mul(F, s, b), O.mul(F, s, a)), O.sub(~F, O.mul(F, b, s), O.mul(F, a, s)), FR.fring_eq(~F, [s, a, b], E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{0n}}, E.ZMul{E.ZVar{1n}, E.ZVar{0n}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, {==}), FM.mono_mul(~F, a, b, s, h, hs)))

# s a <= 0 for a <= 0 and s >= 0
def sle0(~F: O.OField, +s: O.C(F), +a: O.C(F), hs: O.le(~F, O.zero(F), s), h: O.le(~F, a, O.zero(F))) -> O.le(~F, O.mul(F, s, a), O.zero(F)):
  %Equal.sym(O.C(F), O.zero(F), O.mul(F, s, O.zero(F)), FL.mul_zero(~F, s)) : O.le(~F, O.mul(F, s, a), _)
  mul_le(~F, s, a, O.zero(F), hs, h)

# s u <= s w for u <= w and s >= 0
def rle_scale(~F: O.OField, +s: O.C(F), +hs: O.le(~F, O.zero(F), s), u: M.Vec(~F), w: M.Vec(~F), h: rle(~F, u, w)) -> rle(~F, M.vscale(~F, s, u), M.vscale(~F, s, w)):
  match u w:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} Con{+b, ws}:
      (hb, hs2) = h
      (FO.mul_nonneg(~F, s, b, hs, hb), rle_scale(~F, s, hs, Nil{}, ws, hs2))
    case Con{+a, us} Nil{}:
      (ha, hs2) = h
      (sle0(~F, s, a, hs, ha), rle_scale(~F, s, hs, us, Nil{}, hs2))
    case Con{+a, us} Con{+b, ws}:
      (hab, hs2) = h
      (mul_le(~F, s, a, b, hs, hab), rle_scale(~F, s, hs, us, ws, hs2))

# The Newton map's differences
# ----------------------------

def bval(~F: O.OField, +a: O.C(F), +a2: O.C(F), +s: O.C(F), e: {a == a2 : O.C(F)}, h: M.bnd(~F, a, s)) -> M.bnd(~F, a2, s):
  %e : M.bnd(~F, _, s)
  h

def nd_eq(~F: O.OField, +a: O.C(F), +b: O.C(F), +w: M.Vec(~F), +f1: M.Vec(~F), +f2: M.Vec(~F)) -> {O.sub(~F, O.sub(~F, a, b), M.dot(~F, w, C.vsub(~F, f1, f2))) == O.sub(~F, O.sub(~F, a, M.dot(~F, w, f1)), O.sub(~F, b, M.dot(~F, w, f2))) : O.C(F)}:
  %dot_r_vsub(~F, w, f1, f2) : {O.sub(~F, O.sub(~F, a, b), _) == O.sub(~F, O.sub(~F, a, M.dot(~F, w, f1)), O.sub(~F, b, M.dot(~F, w, f2))) : O.C(F)}
  FR.fring_eq(~F, [a, b, M.dot(~F, w, f1), M.dot(~F, w, f2)], E.ZSub{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZSub{E.ZVar{2n}, E.ZVar{3n}}}, E.ZSub{E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, E.ZSub{E.ZVar{1n}, E.ZVar{3n}}}, {==})

# (y1 - Y f1) - (y2 - Y f2) has the bounds of (y1 - y2) - Y (f1 - f2)
def newton_diff(~F: O.OField, y1: M.Vec(~F), y2: M.Vec(~F), ym: M.Mat(~F), +f1: M.Vec(~F), +f2: M.Vec(~F), +r: M.Vec(~F), hl1: {M.len(~F, y1) == M.len(~F, y2) : Nat}, hl2: {M.len(~F, y2) == rows(~F, ym) : Nat}, +h: C.rbnd(~F, C.vsub(~F, C.vsub(~F, y1, y2), M.matvec(~F, ym, C.vsub(~F, f1, f2))), r)) -> C.rbnd(~F, C.vsub(~F, C.vsub(~F, y1, M.matvec(~F, ym, f1)), C.vsub(~F, y2, M.matvec(~F, ym, f2))), r):
  match y1 y2 ym:
    case Nil{} Nil{} Nil{}:
      Unit{}
    case Nil{} Nil{} Con{+w, +ws}:
      FO.absurd(C.rbnd(~F, C.vsub(~F, C.vsub(~F, Nil{}, M.matvec(~F, Con{w, ws}, f1)), C.vsub(~F, Nil{}, M.matvec(~F, Con{w, ws}, f2))), r), zero_ne(rows(~F, ws), hl2))
    case Nil{} Con{+b, +bs} ym:
      FO.absurd(C.rbnd(~F, C.vsub(~F, C.vsub(~F, Nil{}, M.matvec(~F, ym, f1)), C.vsub(~F, Con{b, bs}, M.matvec(~F, ym, f2))), r), zero_ne(M.len(~F, bs), hl1))
    case Con{+a, +as} Nil{} ym:
      FO.absurd(C.rbnd(~F, C.vsub(~F, C.vsub(~F, Con{a, as}, M.matvec(~F, ym, f1)), C.vsub(~F, Nil{}, M.matvec(~F, ym, f2))), r), succ_ne(M.len(~F, as), hl1))
    case Con{+a, +as} Con{+b, +bs} Nil{}:
      FO.absurd(C.rbnd(~F, C.vsub(~F, C.vsub(~F, Con{a, as}, Nil{}), C.vsub(~F, Con{b, bs}, Nil{})), r), succ_ne(M.len(~F, bs), hl2))
    case Con{+a, +as} Con{+b, +bs} Con{+w, +ws}:
      rbnd_mk(~F, O.sub(~F, O.sub(~F, a, M.dot(~F, w, f1)), O.sub(~F, b, M.dot(~F, w, f2))), C.vsub(~F, C.vsub(~F, as, M.matvec(~F, ws, f1)), C.vsub(~F, bs, M.matvec(~F, ws, f2))), r,
        bval(~F, O.sub(~F, O.sub(~F, a, b), M.dot(~F, w, C.vsub(~F, f1, f2))), O.sub(~F, O.sub(~F, a, M.dot(~F, w, f1)), O.sub(~F, b, M.dot(~F, w, f2))), vhd(~F, r), nd_eq(~F, a, b, w, f1, f2),
          rbnd_head(~F, O.sub(~F, O.sub(~F, a, b), M.dot(~F, w, C.vsub(~F, f1, f2))), C.vsub(~F, C.vsub(~F, as, bs), M.matvec(~F, ws, C.vsub(~F, f1, f2))), r, h)),
        newton_diff(~F, as, bs, ws, f1, f2, vtl(~F, r), succ_inj(M.len(~F, as), M.len(~F, bs), hl1), succ_inj(M.len(~F, bs), rows(~F, ws), hl2),
          rbnd_tail(~F, O.sub(~F, O.sub(~F, a, b), M.dot(~F, w, C.vsub(~F, f1, f2))), C.vsub(~F, C.vsub(~F, as, bs), M.matvec(~F, ws, C.vsub(~F, f1, f2))), r, h)))

def split_eq(~F: O.OField, +x: O.C(F), +w: M.Vec(~F), +u: M.Vec(~F), +v: M.Vec(~F)) -> {O.add(F, O.sub(~F, x, M.dot(~F, w, v)), O.neg(F, M.dot(~F, w, C.vsub(~F, u, v)))) == O.sub(~F, x, M.dot(~F, w, u)) : O.C(F)}:
  %dot_r_vsub(~F, w, u, v) : {O.add(F, O.sub(~F, x, M.dot(~F, w, v)), O.neg(F, _)) == O.sub(~F, x, M.dot(~F, w, u)) : O.C(F)}
  FR.fring_eq(~F, [x, M.dot(~F, w, u), M.dot(~F, w, v)], E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, E.ZNeg{E.ZSub{E.ZVar{1n}, E.ZVar{2n}}}}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, {==})

def rbnd_vtl_vadd(~F: O.OField, +d: M.Vec(~F), +r1: M.Vec(~F), +r2: M.Vec(~F), h: C.rbnd(~F, d, M.vadd(~F, vtl(~F, r1), vtl(~F, r2)))) -> C.rbnd(~F, d, vtl(~F, M.vadd(~F, r1, r2))):
  %vtl_vadd(~F, r1, r2) : C.rbnd(~F, d, _)
  h

# d - Y u has the bounds r1 + r2 of d - Y v and Y (u - v)
def split_bnd(~F: O.OField, d: M.Vec(~F), ym: M.Mat(~F), +u: M.Vec(~F), +v: M.Vec(~F), +r1: M.Vec(~F), +r2: M.Vec(~F), hl: {M.len(~F, d) == rows(~F, ym) : Nat}, +h1: C.rbnd(~F, C.vsub(~F, d, M.matvec(~F, ym, v)), r1), +h2: C.rbnd(~F, M.matvec(~F, ym, C.vsub(~F, u, v)), r2)) -> C.rbnd(~F, C.vsub(~F, d, M.matvec(~F, ym, u)), M.vadd(~F, r1, r2)):
  match d ym:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} Con{+w, +ws}:
      FO.absurd(C.rbnd(~F, C.vsub(~F, Nil{}, M.matvec(~F, Con{w, ws}, u)), M.vadd(~F, r1, r2)), zero_ne(rows(~F, ws), hl))
    case Con{+x, +xs} Nil{}:
      FO.absurd(C.rbnd(~F, C.vsub(~F, Con{x, xs}, Nil{}), M.vadd(~F, r1, r2)), succ_ne(M.len(~F, xs), hl))
    case Con{+x, +xs} Con{+w, +ws}:
      rbnd_mk(~F, O.sub(~F, x, M.dot(~F, w, u)), C.vsub(~F, xs, M.matvec(~F, ws, u)), M.vadd(~F, r1, r2),
        FM.bnd_eq(~F, O.sub(~F, x, M.dot(~F, w, u)), O.add(F, vhd(~F, r1), vhd(~F, r2)), vhd(~F, M.vadd(~F, r1, r2)), vhd_vadd(~F, r1, r2),
          bval(~F, O.add(F, O.sub(~F, x, M.dot(~F, w, v)), O.neg(F, M.dot(~F, w, C.vsub(~F, u, v)))), O.sub(~F, x, M.dot(~F, w, u)), O.add(F, vhd(~F, r1), vhd(~F, r2)), split_eq(~F, x, w, u, v),
            FM.bnd_add(~F, O.sub(~F, x, M.dot(~F, w, v)), vhd(~F, r1), O.neg(F, M.dot(~F, w, C.vsub(~F, u, v))), vhd(~F, r2),
              rbnd_head(~F, O.sub(~F, x, M.dot(~F, w, v)), C.vsub(~F, xs, M.matvec(~F, ws, v)), r1, h1),
              FM.bnd_neg(~F, M.dot(~F, w, C.vsub(~F, u, v)), vhd(~F, r2), rbnd_head(~F, M.dot(~F, w, C.vsub(~F, u, v)), M.matvec(~F, ws, C.vsub(~F, u, v)), r2, h2))))),
        rbnd_vtl_vadd(~F, C.vsub(~F, xs, M.matvec(~F, ws, u)), r1, r2,
          split_bnd(~F, xs, ws, u, v, vtl(~F, r1), vtl(~F, r2), succ_inj(M.len(~F, xs), rows(~F, ws), hl),
            rbnd_tail(~F, O.sub(~F, x, M.dot(~F, w, v)), C.vsub(~F, xs, M.matvec(~F, ws, v)), r1, h1),
            rbnd_tail(~F, M.dot(~F, w, C.vsub(~F, u, v)), M.matvec(~F, ws, C.vsub(~F, u, v)), r2, h2))))

# More rewriting and lengths
# --------------------------

def rbnd_rw(~F: O.OField, +d: M.Vec(~F), +d2: M.Vec(~F), +r: M.Vec(~F), e: {d == d2 : M.Vec(~F)}, h: C.rbnd(~F, d, r)) -> C.rbnd(~F, d2, r):
  %e : C.rbnd(~F, _, r)
  h

def rle_rw(~F: O.OField, +u: M.Vec(~F), +u2: M.Vec(~F), +w: M.Vec(~F), +w2: M.Vec(~F), e1: {u == u2 : M.Vec(~F)}, e2: {w == w2 : M.Vec(~F)}, h: rle(~F, u, w)) -> rle(~F, u2, w2):
  %e1 : rle(~F, _, w2)
  %e2 : rle(~F, u, _)
  h

def len_fit(~F: O.OField, n: Nat, y: M.Vec(~F)) -> {M.len(~F, C.fit(~F, n, y)) == n : Nat}:
  match n y:
    case 0n y:
      {==}
    case 1n++k Nil{}:
      %Equal.sym(Nat, M.len(~F, C.fit(~F, k, Nil{})), k, len_fit(~F, k, Nil{})) : {1n+_ == 1n+k : Nat}
      {==}
    case 1n++k Con{a, rest}:
      %Equal.sym(Nat, M.len(~F, C.fit(~F, k, rest)), k, len_fit(~F, k, rest)) : {1n+_ == 1n+k : Nat}
      {==}

# A (s r) + Y (D (s r)) = s (A r + Y (D r))
def r12_ok(~F: O.OField, +s: O.C(F), +a: M.Mat(~F), +y: M.Mat(~F), +d: M.Mat(~F), +r: M.Vec(~F)) -> {M.vadd(~F, M.matvec(~F, a, M.vscale(~F, s, r)), M.matvec(~F, y, M.matvec(~F, d, M.vscale(~F, s, r)))) == M.vscale(~F, s, M.vadd(~F, M.matvec(~F, a, r), M.matvec(~F, y, M.matvec(~F, d, r)))) : M.Vec(~F)}:
  +rhs = M.vscale(~F, s, M.vadd(~F, M.matvec(~F, a, r), M.matvec(~F, y, M.matvec(~F, d, r))))
  %matvec_vscale(~F, a, s, r) : {M.vadd(~F, _, M.matvec(~F, y, M.matvec(~F, d, M.vscale(~F, s, r)))) == rhs : M.Vec(~F)}
  %matvec_vscale(~F, d, s, r) : {M.vadd(~F, M.vscale(~F, s, M.matvec(~F, a, r)), M.matvec(~F, y, _)) == rhs : M.Vec(~F)}
  %matvec_vscale(~F, y, s, M.matvec(~F, d, r)) : {M.vadd(~F, M.vscale(~F, s, M.matvec(~F, a, r)), _) == rhs : M.Vec(~F)}
  vadd_vscale(~F, s, M.matvec(~F, a, r), M.matvec(~F, y, M.matvec(~F, d, r)))

# r . u + r . v = r . (u + v)
def dot_r_vadd(~F: O.OField, r: M.Vec(~F), u: M.Vec(~F), v: M.Vec(~F)) -> {O.add(F, M.dot(~F, r, u), M.dot(~F, r, v)) == M.dot(~F, r, M.vadd(~F, u, v)) : O.C(F)}:
  match r u v:
    case Nil{} u v:
      FR.fring_eq(~F, Nil{}, E.ZAdd{E.ZCst{S.Z0{}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})
    case Con{x, xs} Nil{} Nil{}:
      FR.fring_eq(~F, Nil{}, E.ZAdd{E.ZCst{S.Z0{}}, E.ZCst{S.Z0{}}}, E.ZCst{S.Z0{}}, {==})
    case Con{+x, +xs} Nil{} Con{+b, +bs}:
      FR.fring_eq(~F, [M.dot(~F, Con{x, xs}, Con{b, bs})], E.ZAdd{E.ZCst{S.Z0{}}, E.ZVar{0n}}, E.ZVar{0n}, {==})
    case Con{+x, +xs} Con{+a, +as} Nil{}:
      FR.fring_eq(~F, [M.dot(~F, Con{x, xs}, Con{a, as})], E.ZAdd{E.ZVar{0n}, E.ZCst{S.Z0{}}}, E.ZVar{0n}, {==})
    case Con{+x, +xs} Con{+a, +as} Con{+b, +bs}:
      %dot_r_vadd(~F, xs, as, bs) : {O.add(F, O.add(F, O.mul(F, x, a), M.dot(~F, xs, as)), O.add(F, O.mul(F, x, b), M.dot(~F, xs, bs))) == O.add(F, O.mul(F, x, O.add(F, a, b)), _) : O.C(F)}
      FR.fring_eq(~F, [x, a, b, M.dot(~F, xs, as), M.dot(~F, xs, bs)], E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{3n}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{4n}}}, E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}, E.ZAdd{E.ZVar{3n}, E.ZVar{4n}}}, {==})

# (u - c) - Y f has the bounds of (u - Y f) - c, row by row
def shift(~F: O.OField, u: M.Vec(~F), c: M.Vec(~F), ym: M.Mat(~F), +f: M.Vec(~F), +r: M.Vec(~F), hl1: {M.len(~F, u) == M.len(~F, c) : Nat}, hl2: {M.len(~F, c) == rows(~F, ym) : Nat}, +h: C.rbnd(~F, C.vsub(~F, C.vsub(~F, u, c), M.matvec(~F, ym, f)), r)) -> C.rbnd(~F, C.vsub(~F, C.vsub(~F, u, M.matvec(~F, ym, f)), c), r):
  match u c ym:
    case Nil{} Nil{} Nil{}:
      Unit{}
    case Nil{} Nil{} Con{+w, +ws}:
      FO.absurd(C.rbnd(~F, C.vsub(~F, C.vsub(~F, Nil{}, M.matvec(~F, Con{w, ws}, f)), Nil{}), r), zero_ne(rows(~F, ws), hl2))
    case Nil{} Con{+b, +bs} ym:
      FO.absurd(C.rbnd(~F, C.vsub(~F, C.vsub(~F, Nil{}, M.matvec(~F, ym, f)), Con{b, bs}), r), zero_ne(M.len(~F, bs), hl1))
    case Con{+a, +as} Nil{} ym:
      FO.absurd(C.rbnd(~F, C.vsub(~F, C.vsub(~F, Con{a, as}, M.matvec(~F, ym, f)), Nil{}), r), succ_ne(M.len(~F, as), hl1))
    case Con{+a, +as} Con{+b, +bs} Nil{}:
      FO.absurd(C.rbnd(~F, C.vsub(~F, C.vsub(~F, Con{a, as}, Nil{}), Con{b, bs}), r), succ_ne(M.len(~F, bs), hl2))
    case Con{+a, +as} Con{+b, +bs} Con{+w, +ws}:
      rbnd_mk(~F, O.sub(~F, O.sub(~F, a, M.dot(~F, w, f)), b), C.vsub(~F, C.vsub(~F, as, M.matvec(~F, ws, f)), bs), r,
        bval(~F, O.sub(~F, O.sub(~F, a, b), M.dot(~F, w, f)), O.sub(~F, O.sub(~F, a, M.dot(~F, w, f)), b), vhd(~F, r), FR.fring_eq(~F, [a, b, M.dot(~F, w, f)], E.ZSub{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{2n}}, E.ZSub{E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, E.ZVar{1n}}, {==}),
          rbnd_head(~F, O.sub(~F, O.sub(~F, a, b), M.dot(~F, w, f)), C.vsub(~F, C.vsub(~F, as, bs), M.matvec(~F, ws, f)), r, h)),
        shift(~F, as, bs, ws, f, vtl(~F, r), succ_inj(M.len(~F, as), M.len(~F, bs), hl1), succ_inj(M.len(~F, bs), rows(~F, ws), hl2),
          rbnd_tail(~F, O.sub(~F, O.sub(~F, a, b), M.dot(~F, w, f)), C.vsub(~F, C.vsub(~F, as, bs), M.matvec(~F, ws, f)), r, h)))

def dot_cong(~F: O.OField, +w: M.Vec(~F), +u: M.Vec(~F), +u2: M.Vec(~F), e: {u == u2 : M.Vec(~F)}) -> {M.dot(~F, w, u) == M.dot(~F, w, u2) : O.C(F)}:
  %e : {M.dot(~F, w, u) == M.dot(~F, w, _) : O.C(F)}
  {==}

# fv = pv + q, for fv - pv = q
def split3(~F: O.OField, +fv: O.C(F), +pv: O.C(F), +q: O.C(F), e: {O.sub(~F, fv, pv) == q : O.C(F)}) -> {fv == O.add(F, pv, q) : O.C(F)}:
  %e : {fv == O.add(F, pv, _) : O.C(F)}
  FR.fring_eq(~F, [fv, pv], E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZSub{E.ZVar{0n}, E.ZVar{1n}}}, {==})

# x - w.f = -(w.ft) - w.t + (x - w.a), for f - ft = a + t
def self_eq(~F: O.OField, +x: O.C(F), +w: M.Vec(~F), +f: M.Vec(~F), +ft: M.Vec(~F), +a: M.Vec(~F), +t: M.Vec(~F), e: {C.vsub(~F, f, ft) == M.vadd(~F, a, t) : M.Vec(~F)}) -> {O.add(F, O.add(F, O.neg(F, M.dot(~F, w, ft)), O.neg(F, M.dot(~F, w, t))), O.sub(~F, x, M.dot(~F, w, a))) == O.sub(~F, x, M.dot(~F, w, f)) : O.C(F)}:
  +fv = M.dot(~F, w, f)
  +pv = M.dot(~F, w, ft)
  +av = M.dot(~F, w, a)
  +tv = M.dot(~F, w, t)
  +e1 = Equal.trans(O.C(F), O.sub(~F, fv, pv), M.dot(~F, w, C.vsub(~F, f, ft)), O.add(F, av, tv), dot_r_vsub(~F, w, f, ft), Equal.trans(O.C(F), M.dot(~F, w, C.vsub(~F, f, ft)), M.dot(~F, w, M.vadd(~F, a, t)), O.add(F, av, tv), dot_cong(~F, w, C.vsub(~F, f, ft), M.vadd(~F, a, t), e), Equal.sym(O.C(F), O.add(F, av, tv), M.dot(~F, w, M.vadd(~F, a, t)), dot_r_vadd(~F, w, a, t))))
  %Equal.sym(O.C(F), fv, O.add(F, pv, O.add(F, av, tv)), split3(~F, fv, pv, O.add(F, av, tv), e1)) : {O.add(F, O.add(F, O.neg(F, pv), O.neg(F, tv)), O.sub(~F, x, av)) == O.sub(~F, x, _) : O.C(F)}
  FR.fring_eq(~F, [x, pv, av, tv], E.ZAdd{E.ZAdd{E.ZNeg{E.ZVar{1n}}, E.ZNeg{E.ZVar{3n}}}, E.ZSub{E.ZVar{0n}, E.ZVar{2n}}}, E.ZSub{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZAdd{E.ZVar{2n}, E.ZVar{3n}}}}, {==})

def rbnd3_tail(~F: O.OField, +d: M.Vec(~F), +r3: M.Vec(~F), +r4: M.Vec(~F), +r1: M.Vec(~F), h: C.rbnd(~F, d, M.vadd(~F, M.vadd(~F, vtl(~F, r3), vtl(~F, r4)), vtl(~F, r1)))) -> C.rbnd(~F, d, vtl(~F, M.vadd(~F, M.vadd(~F, r3, r4), r1))):
  %vtl_vadd(~F, M.vadd(~F, r3, r4), r1) : C.rbnd(~F, d, _)
  %vtl_vadd(~F, r3, r4) : C.rbnd(~F, d, M.vadd(~F, _, vtl(~F, r1)))
  h

def vhd3(~F: O.OField, +r3: M.Vec(~F), +r4: M.Vec(~F), +r1: M.Vec(~F)) -> {O.add(F, O.add(F, vhd(~F, r3), vhd(~F, r4)), vhd(~F, r1)) == vhd(~F, M.vadd(~F, M.vadd(~F, r3, r4), r1)) : O.C(F)}:
  %vhd_vadd(~F, M.vadd(~F, r3, r4), r1) : {O.add(F, O.add(F, vhd(~F, r3), vhd(~F, r4)), vhd(~F, r1)) == _ : O.C(F)}
  %vhd_vadd(~F, r3, r4) : {O.add(F, O.add(F, vhd(~F, r3), vhd(~F, r4)), vhd(~F, r1)) == O.add(F, _, vhd(~F, r1)) : O.C(F)}
  {==}

# d - Y f has the bounds (r3 + r4) + r1 of Y ft, Y t and d - Y a, for f - ft = a + t
def self3(~F: O.OField, d: M.Vec(~F), ym: M.Mat(~F), +f: M.Vec(~F), +ft: M.Vec(~F), +a: M.Vec(~F), +t: M.Vec(~F), +r1: M.Vec(~F), +r3: M.Vec(~F), +r4: M.Vec(~F), hl: {M.len(~F, d) == rows(~F, ym) : Nat}, +e: {C.vsub(~F, f, ft) == M.vadd(~F, a, t) : M.Vec(~F)}, +ha: C.rbnd(~F, C.vsub(~F, d, M.matvec(~F, ym, a)), r1), +hb: C.rbnd(~F, M.matvec(~F, ym, ft), r3), +hc: C.rbnd(~F, M.matvec(~F, ym, t), r4)) -> C.rbnd(~F, C.vsub(~F, d, M.matvec(~F, ym, f)), M.vadd(~F, M.vadd(~F, r3, r4), r1)):
  match d ym:
    case Nil{} Nil{}:
      Unit{}
    case Nil{} Con{+w, +ws}:
      FO.absurd(C.rbnd(~F, C.vsub(~F, Nil{}, M.matvec(~F, Con{w, ws}, f)), M.vadd(~F, M.vadd(~F, r3, r4), r1)), zero_ne(rows(~F, ws), hl))
    case Con{+x, +xs} Nil{}:
      FO.absurd(C.rbnd(~F, C.vsub(~F, Con{x, xs}, Nil{}), M.vadd(~F, M.vadd(~F, r3, r4), r1)), succ_ne(M.len(~F, xs), hl))
    case Con{+x, +xs} Con{+w, +ws}:
      rbnd_mk(~F, O.sub(~F, x, M.dot(~F, w, f)), C.vsub(~F, xs, M.matvec(~F, ws, f)), M.vadd(~F, M.vadd(~F, r3, r4), r1),
        FM.bnd_eq(~F, O.sub(~F, x, M.dot(~F, w, f)), O.add(F, O.add(F, vhd(~F, r3), vhd(~F, r4)), vhd(~F, r1)), vhd(~F, M.vadd(~F, M.vadd(~F, r3, r4), r1)), vhd3(~F, r3, r4, r1),
          bval(~F, O.add(F, O.add(F, O.neg(F, M.dot(~F, w, ft)), O.neg(F, M.dot(~F, w, t))), O.sub(~F, x, M.dot(~F, w, a))), O.sub(~F, x, M.dot(~F, w, f)), O.add(F, O.add(F, vhd(~F, r3), vhd(~F, r4)), vhd(~F, r1)), self_eq(~F, x, w, f, ft, a, t, e),
            FM.bnd_add(~F, O.add(F, O.neg(F, M.dot(~F, w, ft)), O.neg(F, M.dot(~F, w, t))), O.add(F, vhd(~F, r3), vhd(~F, r4)), O.sub(~F, x, M.dot(~F, w, a)), vhd(~F, r1),
              FM.bnd_add(~F, O.neg(F, M.dot(~F, w, ft)), vhd(~F, r3), O.neg(F, M.dot(~F, w, t)), vhd(~F, r4),
                FM.bnd_neg(~F, M.dot(~F, w, ft), vhd(~F, r3), rbnd_head(~F, M.dot(~F, w, ft), M.matvec(~F, ws, ft), r3, hb)),
                FM.bnd_neg(~F, M.dot(~F, w, t), vhd(~F, r4), rbnd_head(~F, M.dot(~F, w, t), M.matvec(~F, ws, t), r4, hc))),
              rbnd_head(~F, O.sub(~F, x, M.dot(~F, w, a)), C.vsub(~F, xs, M.matvec(~F, ws, a)), r1, ha)))),
        rbnd3_tail(~F, C.vsub(~F, xs, M.matvec(~F, ws, f)), r3, r4, r1,
          self3(~F, xs, ws, f, ft, a, t, vtl(~F, r1), vtl(~F, r3), vtl(~F, r4), succ_inj(M.len(~F, xs), rows(~F, ws), hl), e,
            rbnd_tail(~F, O.sub(~F, x, M.dot(~F, w, a)), C.vsub(~F, xs, M.matvec(~F, ws, a)), r1, ha),
            rbnd_tail(~F, M.dot(~F, w, ft), M.matvec(~F, ws, ft), r3, hb),
            rbnd_tail(~F, M.dot(~F, w, t), M.matvec(~F, ws, t), r4, hc))))

def len_matvec(~F: O.OField, a: M.Mat(~F), +v: M.Vec(~F)) -> {M.len(~F, M.matvec(~F, a, v)) == rows(~F, a) : Nat}:
  match a:
    case Nil{}:
      {==}
    case Con{r, rs}:
      %Equal.sym(Nat, M.len(~F, M.matvec(~F, rs, v)), rows(~F, rs), len_matvec(~F, rs, v)) : {1n+_ == 1n+rows(~F, rs) : Nat}
      {==}
