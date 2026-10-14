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
