# Ball arithmetic in a checker's computing numbers K (DESIGN §8.3, steps
# 2-3): enclosures of an expression's value and of its telescoping slope,
# as a center and a radius, over a box of variables. Exact in K (no
# rounding). Untrusted: the soundness lemmas below say what the balls mean
# in every ordered field F that K maps into.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ./karith.bend as KA
import ./flaws.bend as FL
import ./fring.bend as FR
import ./ford.bend as FO
import ./fmat.bend as FM
import ./slope.bend as SL

# Balls
# -----

# center c, radius r
type KB<-K: N.Num> is Data:
  KB{c: N.NC(K), r: N.NC(K)}

def KB.c(-K: N.Num, x: KB<K>) -> N.NC(K):
  match x:
    case KB{c, r}:
      c

def KB.r(-K: N.Num, x: KB<K>) -> N.NC(K):
  match x:
    case KB{c, r}:
      r

def bzero(~K: N.Num) -> KB<K>:
  KB{N.nzero(K), N.nzero(K)}

def badd(~K: N.Num, x: KB<K>, y: KB<K>) -> KB<K>:
  match x y:
    case KB{c1, r1} KB{c2, r2}:
      KB{N.nadd(K, c1, c2), N.nadd(K, r1, r2)}

def bneg(~K: N.Num, x: KB<K>) -> KB<K>:
  match x:
    case KB{c, r}:
      KB{N.nneg(K, c), r}

# (c1, r1)(c2, r2) = (c1 c2, |c1| r2 + |c2| r1 + r1 r2)
def bmul(~K: N.Num, x: KB<K>, y: KB<K>) -> KB<K>:
  match x y:
    case KB{+c1, +r1} KB{+c2, +r2}:
      KB{N.nmul(K, c1, c2), N.nadd(K, N.nadd(K, N.nmul(K, KA.kabs(~K, c1), r2), N.nmul(K, KA.kabs(~K, c2), r1)), N.nmul(K, r1, r2))}

# Lists of balls (zero balls past the end)
# ----------------------------------------

def blook(~K: N.Num, xs: List<&2, KB<K>>, i: Nat) -> KB<K>:
  match xs i:
    case Nil{} j:
      bzero(~K)
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      blook(~K, t, j)

def bcenters(~K: N.Num, u: List<&2, KB<K>>) -> List<&2, N.NC(K)>:
  match u:
    case Nil{}:
      Nil{}
    case Con{a, us}:
      Con{KB.c(K, a), bcenters(~K, us)}

def bradii(~K: N.Num, u: List<&2, KB<K>>) -> List<&2, N.NC(K)>:
  match u:
    case Nil{}:
      Nil{}
    case Con{a, us}:
      Con{KB.r(K, a), bradii(~K, us)}

# Expressions
# -----------

# K's copy of a constant (0 if K does not hold it; held rejects those)
def kcst.go(~K: N.Num, m: Maybe<&2, N.NC(K)>) -> N.NC(K):
  match m:
    case None{}:
      N.nzero(K)
    case Some{k}:
      k

def kcst(~K: N.Num, q: S.Q) -> N.NC(K):
  kcst.go(~K, N.nofq(K, q))

def held.go(~K: N.Num, m: Maybe<&2, N.NC(K)>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{k}:
      True{}

# every constant of e is held by K
def held(~K: N.Num, e: E.QExpr) -> Bool:
  match e:
    case E.QVar{i}:
      True{}
    case E.QCst{q}:
      held.go(~K, N.nofq(K, q))
    case E.QAdd{a, b}:
      KA.band(held(~K, a), held(~K, b))
    case E.QSub{a, b}:
      KA.band(held(~K, a), held(~K, b))
    case E.QMul{a, b}:
      KA.band(held(~K, a), held(~K, b))
    case E.QNeg{a}:
      held(~K, a)

def klook(~K: N.Num, xs: List<&2, N.NC(K)>, i: Nat) -> N.NC(K):
  match xs i:
    case Nil{} j:
      N.nzero(K)
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      klook(~K, t, j)

# e's value at env, in K
def keval(~K: N.Num, +env: List<&2, N.NC(K)>, e: E.QExpr) -> N.NC(K):
  match e:
    case E.QVar{i}:
      klook(~K, env, i)
    case E.QCst{q}:
      kcst(~K, q)
    case E.QAdd{a, b}:
      N.nadd(K, keval(~K, env, a), keval(~K, env, b))
    case E.QSub{a, b}:
      KA.ksub(~K, keval(~K, env, a), keval(~K, env, b))
    case E.QMul{a, b}:
      N.nmul(K, keval(~K, env, a), keval(~K, env, b))
    case E.QNeg{a}:
      N.nneg(K, keval(~K, env, a))

# an enclosure of e's value over the box
def kball(~K: N.Num, +box: List<&2, KB<K>>, e: E.QExpr) -> KB<K>:
  match e:
    case E.QVar{i}:
      blook(~K, box, i)
    case E.QCst{q}:
      KB{kcst(~K, q), N.nzero(K)}
    case E.QAdd{a, b}:
      badd(~K, kball(~K, box, a), kball(~K, box, b))
    case E.QSub{a, b}:
      badd(~K, kball(~K, box, a), bneg(~K, kball(~K, box, b)))
    case E.QMul{a, b}:
      bmul(~K, kball(~K, box, a), kball(~K, box, b))
    case E.QNeg{a}:
      bneg(~K, kball(~K, box, a))

# 1 if i = j, else 0
def kind(~K: N.Num, b: Bool) -> KB<K>:
  match b:
    case True{}:
      KB{N.none(K), N.nzero(K)}
    case False{}:
      bzero(~K)

# an enclosure of e's telescoping slope in variable i over the box:
# slope(a b) = a(X1) slope(b) + b(X2) slope(a)
def ksl(~K: N.Num, +i: Nat, +box: List<&2, KB<K>>, e: E.QExpr) -> KB<K>:
  match e:
    case E.QVar{j}:
      kind(~K, KA.nateq(i, j))
    case E.QCst{q}:
      bzero(~K)
    case E.QAdd{a, b}:
      badd(~K, ksl(~K, i, box, a), ksl(~K, i, box, b))
    case E.QSub{a, b}:
      badd(~K, ksl(~K, i, box, a), bneg(~K, ksl(~K, i, box, b)))
    case E.QMul{+a, +b}:
      badd(~K, bmul(~K, kball(~K, box, a), ksl(~K, i, box, b)), bmul(~K, kball(~K, box, b), ksl(~K, i, box, a)))
    case E.QNeg{a}:
      bneg(~K, ksl(~K, i, box, a))

# the slope enclosures in the cnt variables lo, lo + 1, ...
def krange(~K: N.Num, +box: List<&2, KB<K>>, +e: E.QExpr, cnt: Nat, +lo: Nat) -> List<&2, KB<K>>:
  match cnt:
    case 0n:
      Nil{}
    case 1n+k:
      Con{ksl(~K, lo, box, e), krange(~K, box, e, k, 1n+lo)}

# every variable of e is below m
def below(+m: Nat, e: E.QExpr) -> Bool:
  match e:
    case E.QVar{j}:
      KA.natle(1n+j, m)
    case E.QCst{q}:
      True{}
    case E.QAdd{a, b}:
      KA.band(below(m, a), below(m, b))
    case E.QSub{a, b}:
      KA.band(below(m, a), below(m, b))
    case E.QMul{a, b}:
      KA.band(below(m, a), below(m, b))
    case E.QNeg{a}:
      below(m, a)

# What the balls mean in F
# ------------------------

# x lies in ball b: |x - H c| <= H r
def bin(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x: O.C(F), b: KB<K>) -> Data:
  match b:
    case KB{c, r}:
      M.bnd(~F, O.sub(~F, x, N.emap(K, F, H, c)), N.emap(K, F, H, r))

# each X_i lies in box_i (X read with zeros, zero balls past the box's end)
def inbox(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, x: M.Vec(~F), box: List<&2, KB<K>>) -> Data:
  match x box:
    case Nil{} Nil{}:
      Unit
    case Nil{} Con{b, bs}:
      M.Both(bin(~K, ~F, ~H, O.zero(F), b), inbox(~K, ~F, ~H, Nil{}, bs))
    case Con{a, xs} Nil{}:
      M.Both(bin(~K, ~F, ~H, a, bzero(~K)), inbox(~K, ~F, ~H, xs, Nil{}))
    case Con{a, xs} Con{b, bs}:
      M.Both(bin(~K, ~F, ~H, a, b), inbox(~K, ~F, ~H, xs, bs))

def bnd_val(~F: O.OField, +a: O.C(F), +a2: O.C(F), +s: O.C(F), e: {a == a2 : O.C(F)}, h: M.bnd(~F, a, s)) -> M.bnd(~F, a2, s):
  %e : M.bnd(~F, _, s)
  h

# |a - a| <= s, for 0 <= s
def bnd_subself(~F: O.OField, +a: O.C(F), +s: O.C(F), +hs: O.le(~F, O.zero(F), s)) -> M.bnd(~F, O.sub(~F, a, a), s):
  bnd_val(~F, O.zero(F), O.sub(~F, a, a), s, Equal.sym(O.C(F), O.sub(~F, a, a), O.zero(F), O.add_neg(F)(a)), FM.bnd_zero(~F, s, hs))

def e0_nonneg(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>) -> O.le(~F, O.zero(F), N.emap(K, F, H, N.nzero(K))):
  Inr{KA.ez(~K, ~F, ~H)}

# x lies in (H x, 0)... for x = H c: c's own point ball
def bin_self(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: N.NC(K)) -> bin(~K, ~F, ~H, N.emap(K, F, H, c), KB{c, N.nzero(K)}):
  bnd_subself(~F, N.emap(K, F, H, c), N.emap(K, F, H, N.nzero(K)), e0_nonneg(~K, ~F, ~H))

# 0 lies in the zero ball
def bin_zz(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>) -> bin(~K, ~F, ~H, O.zero(F), bzero(~K)):
  %N.e_zero(K, F, H) : M.bnd(~F, O.sub(~F, _, N.emap(K, F, H, N.nzero(K))), N.emap(K, F, H, N.nzero(K)))
  bin_self(~K, ~F, ~H, N.nzero(K))

def bin_look(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, x: M.Vec(~F), box: List<&2, KB<K>>, i: Nat, h: inbox(~K, ~F, ~H, x, box)) -> bin(~K, ~F, ~H, O.lookup(~F, x, i), blook(~K, box, i)):
  match x box i:
    case Nil{} Nil{} j:
      bin_zz(~K, ~F, ~H)
    case Nil{} Con{b, bs} 0n:
      (hb, hs) = h
      hb
    case Nil{} Con{b, bs} 1n+j:
      (hb, hs) = h
      bin_look(~K, ~F, ~H, Nil{}, bs, j, hs)
    case Con{a, xs} Nil{} 0n:
      (hb, hs) = h
      hb
    case Con{a, xs} Nil{} 1n+j:
      (hb, hs) = h
      bin_look(~K, ~F, ~H, xs, Nil{}, j, hs)
    case Con{a, xs} Con{b, bs} 0n:
      (hb, hs) = h
      hb
    case Con{a, xs} Con{b, bs} 1n+j:
      (hb, hs) = h
      bin_look(~K, ~F, ~H, xs, bs, j, hs)

def bin_add(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x: O.C(F), a: KB<K>, +y: O.C(F), b: KB<K>, ha: bin(~K, ~F, ~H, x, a), hb: bin(~K, ~F, ~H, y, b)) -> bin(~K, ~F, ~H, O.add(F, x, y), badd(~K, a, b)):
  match a b:
    case KB{+ca, +ra} KB{+cb, +rb}:
      %KA.ea(~K, ~F, ~H, ra, rb) : M.bnd(~F, O.sub(~F, O.add(F, x, y), N.emap(K, F, H, N.nadd(K, ca, cb))), _)
      %KA.ea(~K, ~F, ~H, ca, cb) : M.bnd(~F, O.sub(~F, O.add(F, x, y), _), O.add(F, N.emap(K, F, H, ra), N.emap(K, F, H, rb)))
      bnd_val(~F, O.add(F, O.sub(~F, x, N.emap(K, F, H, ca)), O.sub(~F, y, N.emap(K, F, H, cb))), O.sub(~F, O.add(F, x, y), O.add(F, N.emap(K, F, H, ca), N.emap(K, F, H, cb))), O.add(F, N.emap(K, F, H, ra), N.emap(K, F, H, rb)),
        FR.fring_eq(~F, [x, y, N.emap(K, F, H, ca), N.emap(K, F, H, cb)], E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, E.ZSub{E.ZVar{1n}, E.ZVar{3n}}}, E.ZSub{E.ZAdd{E.ZVar{0n}, E.ZVar{1n}}, E.ZAdd{E.ZVar{2n}, E.ZVar{3n}}}, {==}),
        FM.bnd_add(~F, O.sub(~F, x, N.emap(K, F, H, ca)), N.emap(K, F, H, ra), O.sub(~F, y, N.emap(K, F, H, cb)), N.emap(K, F, H, rb), ha, hb))

def bin_neg(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x: O.C(F), a: KB<K>, h: bin(~K, ~F, ~H, x, a)) -> bin(~K, ~F, ~H, O.neg(F, x), bneg(~K, a)):
  match a:
    case KB{+c, +r}:
      %KA.en(~K, ~F, ~H, c) : M.bnd(~F, O.sub(~F, O.neg(F, x), _), N.emap(K, F, H, r))
      bnd_val(~F, O.neg(F, O.sub(~F, x, N.emap(K, F, H, c))), O.sub(~F, O.neg(F, x), O.neg(F, N.emap(K, F, H, c))), N.emap(K, F, H, r),
        FR.fring_eq(~F, [x, N.emap(K, F, H, c)], E.ZNeg{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}}, E.ZSub{E.ZNeg{E.ZVar{0n}}, E.ZNeg{E.ZVar{1n}}}, {==}),
        FM.bnd_neg(~F, O.sub(~F, x, N.emap(K, F, H, c)), N.emap(K, F, H, r), h))

# |x y - c1 c2| <= |c1| r2 + |c2| r1 + r1 r2, for |x - c1| <= r1, |y - c2| <= r2
def bin_mul(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x: O.C(F), a: KB<K>, +y: O.C(F), b: KB<K>, +ha: bin(~K, ~F, ~H, x, a), +hb: bin(~K, ~F, ~H, y, b)) -> bin(~K, ~F, ~H, O.mul(F, x, y), bmul(~K, a, b)):
  match a b:
    case KB{+ca, +ra} KB{+cb, +rb}:
      +c1 = N.emap(K, F, H, ca)
      +c2 = N.emap(K, F, H, cb)
      +r1 = N.emap(K, F, H, ra)
      +r2 = N.emap(K, F, H, rb)
      +k1 = N.emap(K, F, H, KA.kabs(~K, ca))
      +k2 = N.emap(K, F, H, KA.kabs(~K, cb))
      +u = O.sub(~F, x, c1)
      +v = O.sub(~F, y, c2)
      %KA.ea(~K, ~F, ~H, N.nadd(K, N.nmul(K, KA.kabs(~K, ca), rb), N.nmul(K, KA.kabs(~K, cb), ra)), N.nmul(K, ra, rb)) : M.bnd(~F, O.sub(~F, O.mul(F, x, y), N.emap(K, F, H, N.nmul(K, ca, cb))), _)
      %KA.ea(~K, ~F, ~H, N.nmul(K, KA.kabs(~K, ca), rb), N.nmul(K, KA.kabs(~K, cb), ra)) : M.bnd(~F, O.sub(~F, O.mul(F, x, y), N.emap(K, F, H, N.nmul(K, ca, cb))), O.add(F, _, N.emap(K, F, H, N.nmul(K, ra, rb))))
      %KA.em(~K, ~F, ~H, KA.kabs(~K, ca), rb) : M.bnd(~F, O.sub(~F, O.mul(F, x, y), N.emap(K, F, H, N.nmul(K, ca, cb))), O.add(F, O.add(F, _, N.emap(K, F, H, N.nmul(K, KA.kabs(~K, cb), ra))), N.emap(K, F, H, N.nmul(K, ra, rb))))
      %KA.em(~K, ~F, ~H, KA.kabs(~K, cb), ra) : M.bnd(~F, O.sub(~F, O.mul(F, x, y), N.emap(K, F, H, N.nmul(K, ca, cb))), O.add(F, O.add(F, O.mul(F, k1, r2), _), N.emap(K, F, H, N.nmul(K, ra, rb))))
      %KA.em(~K, ~F, ~H, ra, rb) : M.bnd(~F, O.sub(~F, O.mul(F, x, y), N.emap(K, F, H, N.nmul(K, ca, cb))), O.add(F, O.add(F, O.mul(F, k1, r2), O.mul(F, k2, r1)), _))
      %KA.em(~K, ~F, ~H, ca, cb) : M.bnd(~F, O.sub(~F, O.mul(F, x, y), _), O.add(F, O.add(F, O.mul(F, k1, r2), O.mul(F, k2, r1)), O.mul(F, r1, r2)))
      bnd_val(~F, O.add(F, O.add(F, O.mul(F, c1, v), O.mul(F, c2, u)), O.mul(F, u, v)), O.sub(~F, O.mul(F, x, y), O.mul(F, c1, c2)), O.add(F, O.add(F, O.mul(F, k1, r2), O.mul(F, k2, r1)), O.mul(F, r1, r2)),
        FR.fring_eq(~F, [x, y, c1, c2], E.ZAdd{E.ZAdd{E.ZMul{E.ZVar{2n}, E.ZSub{E.ZVar{1n}, E.ZVar{3n}}}, E.ZMul{E.ZVar{3n}, E.ZSub{E.ZVar{0n}, E.ZVar{2n}}}}, E.ZMul{E.ZSub{E.ZVar{0n}, E.ZVar{2n}}, E.ZSub{E.ZVar{1n}, E.ZVar{3n}}}}, E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{2n}, E.ZVar{3n}}}, {==}),
        FM.bnd_add(~F, O.add(F, O.mul(F, c1, v), O.mul(F, c2, u)), O.add(F, O.mul(F, k1, r2), O.mul(F, k2, r1)), O.mul(F, u, v), O.mul(F, r1, r2),
          FM.bnd_add(~F, O.mul(F, c1, v), O.mul(F, k1, r2), O.mul(F, c2, u), O.mul(F, k2, r1),
            FM.bnd_mul(~F, c1, k1, v, r2, KA.kabs_bnd(~K, ~F, ~H, ca), hb),
            FM.bnd_mul(~F, c2, k2, u, r1, KA.kabs_bnd(~K, ~F, ~H, cb), ha)),
          FM.bnd_mul(~F, u, r1, v, r2, ha, hb)))

# a held constant's copy in K means the constant
def kcst_ok.go(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +q: S.Q, m: Maybe<&2, N.NC(K)>, e: {N.nofq(K, q) == m : Maybe<&2, N.NC(K)>}, h: {held.go(~K, m) == True{} : Bool}) -> {N.emap(K, F, H, kcst.go(~K, m)) == O.ofq(~F, q) : O.C(F)}:
  match m:
    case None{}:
      FO.absurd({N.emap(K, F, H, N.nzero(K)) == O.ofq(~F, q) : O.C(F)}, KA.ft(h))
    case Some{k}:
      N.e_ofq(K, F, H)(q, k, e)

def kcst_ok(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +q: S.Q, h: {held(~K, E.QCst{q}) == True{} : Bool}) -> {N.emap(K, F, H, kcst(~K, q)) == O.ofq(~F, q) : O.C(F)}:
  kcst_ok.go(~K, ~F, ~H, q, N.nofq(K, q), {==}, h)

# e's value over the box lies in its ball
def ball_ok(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x: M.Vec(~F), +box: List<&2, KB<K>>, e: E.QExpr, +hh: {held(~K, e) == True{} : Bool}, +hx: inbox(~K, ~F, ~H, x, box)) -> bin(~K, ~F, ~H, O.eval(~F, x, e), kball(~K, box, e)):
  match e:
    case E.QVar{i}:
      bin_look(~K, ~F, ~H, x, box, i, hx)
    case E.QCst{+q}:
      %Equal.sym(O.C(F), N.emap(K, F, H, kcst(~K, q)), O.ofq(~F, q), kcst_ok(~K, ~F, ~H, q, hh)) : M.bnd(~F, O.sub(~F, O.ofq(~F, q), _), N.emap(K, F, H, N.nzero(K)))
      bnd_subself(~F, O.ofq(~F, q), N.emap(K, F, H, N.nzero(K)), e0_nonneg(~K, ~F, ~H))
    case E.QAdd{+a, +b}:
      bin_add(~K, ~F, ~H, O.eval(~F, x, a), kball(~K, box, a), O.eval(~F, x, b), kball(~K, box, b), ball_ok(~K, ~F, ~H, x, box, a, KA.band_l(held(~K, a), held(~K, b), hh), hx), ball_ok(~K, ~F, ~H, x, box, b, KA.band_r(held(~K, a), held(~K, b), hh), hx))
    case E.QSub{+a, +b}:
      bin_add(~K, ~F, ~H, O.eval(~F, x, a), kball(~K, box, a), O.neg(F, O.eval(~F, x, b)), bneg(~K, kball(~K, box, b)), ball_ok(~K, ~F, ~H, x, box, a, KA.band_l(held(~K, a), held(~K, b), hh), hx), bin_neg(~K, ~F, ~H, O.eval(~F, x, b), kball(~K, box, b), ball_ok(~K, ~F, ~H, x, box, b, KA.band_r(held(~K, a), held(~K, b), hh), hx)))
    case E.QMul{+a, +b}:
      bin_mul(~K, ~F, ~H, O.eval(~F, x, a), kball(~K, box, a), O.eval(~F, x, b), kball(~K, box, b), ball_ok(~K, ~F, ~H, x, box, a, KA.band_l(held(~K, a), held(~K, b), hh), hx), ball_ok(~K, ~F, ~H, x, box, b, KA.band_r(held(~K, a), held(~K, b), hh), hx))
    case E.QNeg{+a}:
      bin_neg(~K, ~F, ~H, O.eval(~F, x, a), kball(~K, box, a), ball_ok(~K, ~F, ~H, x, box, a, hh, hx))

# 1 or 0 lies in its point ball
def kind_ok(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, b: Bool) -> bin(~K, ~F, ~H, SL.find(~F, b), kind(~K, b)):
  match b:
    case True{}:
      %N.e_one(K, F, H) : M.bnd(~F, O.sub(~F, _, N.emap(K, F, H, N.none(K))), N.emap(K, F, H, N.nzero(K)))
      bin_self(~K, ~F, ~H, N.none(K))
    case False{}:
      bin_zz(~K, ~F, ~H)

# e's slope in variable i, between two points of the box, lies in its ball
def sl_ok(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +i: Nat, +x1: M.Vec(~F), +x2: M.Vec(~F), +box: List<&2, KB<K>>, e: E.QExpr, +hh: {held(~K, e) == True{} : Bool}, +h1: inbox(~K, ~F, ~H, x1, box), +h2: inbox(~K, ~F, ~H, x2, box)) -> bin(~K, ~F, ~H, SL.sl(~F, i, x1, x2, e), ksl(~K, i, box, e)):
  match e:
    case E.QVar{j}:
      kind_ok(~K, ~F, ~H, KA.nateq(i, j))
    case E.QCst{q}:
      bin_zz(~K, ~F, ~H)
    case E.QAdd{+a, +b}:
      bin_add(~K, ~F, ~H, SL.sl(~F, i, x1, x2, a), ksl(~K, i, box, a), SL.sl(~F, i, x1, x2, b), ksl(~K, i, box, b), sl_ok(~K, ~F, ~H, i, x1, x2, box, a, KA.band_l(held(~K, a), held(~K, b), hh), h1, h2), sl_ok(~K, ~F, ~H, i, x1, x2, box, b, KA.band_r(held(~K, a), held(~K, b), hh), h1, h2))
    case E.QSub{+a, +b}:
      bin_add(~K, ~F, ~H, SL.sl(~F, i, x1, x2, a), ksl(~K, i, box, a), O.neg(F, SL.sl(~F, i, x1, x2, b)), bneg(~K, ksl(~K, i, box, b)), sl_ok(~K, ~F, ~H, i, x1, x2, box, a, KA.band_l(held(~K, a), held(~K, b), hh), h1, h2), bin_neg(~K, ~F, ~H, SL.sl(~F, i, x1, x2, b), ksl(~K, i, box, b), sl_ok(~K, ~F, ~H, i, x1, x2, box, b, KA.band_r(held(~K, a), held(~K, b), hh), h1, h2)))
    case E.QMul{+a, +b}:
      +ha = KA.band_l(held(~K, a), held(~K, b), hh)
      +hb = KA.band_r(held(~K, a), held(~K, b), hh)
      bin_add(~K, ~F, ~H, O.mul(F, O.eval(~F, x1, a), SL.sl(~F, i, x1, x2, b)), bmul(~K, kball(~K, box, a), ksl(~K, i, box, b)), O.mul(F, O.eval(~F, x2, b), SL.sl(~F, i, x1, x2, a)), bmul(~K, kball(~K, box, b), ksl(~K, i, box, a)),
        bin_mul(~K, ~F, ~H, O.eval(~F, x1, a), kball(~K, box, a), SL.sl(~F, i, x1, x2, b), ksl(~K, i, box, b), ball_ok(~K, ~F, ~H, x1, box, a, ha, h1), sl_ok(~K, ~F, ~H, i, x1, x2, box, b, hb, h1, h2)),
        bin_mul(~K, ~F, ~H, O.eval(~F, x2, b), kball(~K, box, b), SL.sl(~F, i, x1, x2, a), ksl(~K, i, box, a), ball_ok(~K, ~F, ~H, x2, box, b, hb, h2), sl_ok(~K, ~F, ~H, i, x1, x2, box, a, ha, h1, h2)))
    case E.QNeg{+a}:
      bin_neg(~K, ~F, ~H, SL.sl(~F, i, x1, x2, a), ksl(~K, i, box, a), sl_ok(~K, ~F, ~H, i, x1, x2, box, a, hh, h1, h2))

# the whole range of slopes lies in the range of balls
def range_ok(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x1: M.Vec(~F), +x2: M.Vec(~F), +box: List<&2, KB<K>>, +e: E.QExpr, +hh: {held(~K, e) == True{} : Bool}, +h1: inbox(~K, ~F, ~H, x1, box), +h2: inbox(~K, ~F, ~H, x2, box), cnt: Nat, +lo: Nat) -> inbox(~K, ~F, ~H, SL.srange(~F, x1, x2, e, cnt, lo), krange(~K, box, e, cnt, lo)):
  match cnt:
    case 0n:
      Unit{}
    case 1n+k:
      (sl_ok(~K, ~F, ~H, lo, x1, x2, box, e, hh, h1, h2), range_ok(~K, ~F, ~H, x1, x2, box, e, hh, h1, h2, k, 1n+lo))
