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

def bvadd(~K: N.Num, u: List<&2, KB<K>>, w: List<&2, KB<K>>) -> List<&2, KB<K>>:
  match u w:
    case Nil{} w:
      w
    case Con{a, us} Nil{}:
      Con{a, us}
    case Con{a, us} Con{b, ws}:
      Con{badd(~K, a, b), bvadd(~K, us, ws)}

def bvneg(~K: N.Num, u: List<&2, KB<K>>) -> List<&2, KB<K>>:
  match u:
    case Nil{}:
      Nil{}
    case Con{a, us}:
      Con{bneg(~K, a), bvneg(~K, us)}

def bvscale(~K: N.Num, +x: KB<K>, u: List<&2, KB<K>>) -> List<&2, KB<K>>:
  match u:
    case Nil{}:
      Nil{}
    case Con{a, us}:
      Con{bmul(~K, x, a), bvscale(~K, x, us)}

# the slope of variable i: 1 at i, 0 elsewhere
def bunit(~K: N.Num, i: Nat) -> List<&2, KB<K>>:
  match i:
    case 0n:
      [KB{N.none(K), N.nzero(K)}]
    case 1n+j:
      Con{bzero(~K), bunit(~K, j)}

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

# an enclosure of e's telescoping slope over the box, one ball per variable:
# slope(a b) = a(X1) slope(b) + b(X2) slope(a)
def kslope(~K: N.Num, +box: List<&2, KB<K>>, e: E.QExpr) -> List<&2, KB<K>>:
  match e:
    case E.QVar{i}:
      bunit(~K, i)
    case E.QCst{q}:
      Nil{}
    case E.QAdd{a, b}:
      bvadd(~K, kslope(~K, box, a), kslope(~K, box, b))
    case E.QSub{a, b}:
      bvadd(~K, kslope(~K, box, a), bvneg(~K, kslope(~K, box, b)))
    case E.QMul{+a, +b}:
      bvadd(~K, bvscale(~K, kball(~K, box, a), kslope(~K, box, b)), bvscale(~K, kball(~K, box, b), kslope(~K, box, a)))
    case E.QNeg{a}:
      bvneg(~K, kslope(~K, box, a))
