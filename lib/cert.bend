# bend-cad: the block certificate checker (DESIGN §8.3). Untrusted: only the
# cert_* laws say what a passing check means. Generic over the computing
# numbers K; everything is exact in K.
#
# With n unknowns and p parameters, center X̃ = ỹ ++ z̃ and box radii
# R = r ++ rho over all of the block's variables, each equation's slope
# enclosures in the unknowns (variables 0..n-1) give the rows of J0y
# (centers) and Dy (radii), and in the parameters (n..n+p-1) J0z and Dz. With G r = |I - Y J0y| r + |Y| (Dy r), the checker requires:
#   shape:  n equations, Y with n rows, ỹ with n entries, at most n radii,
#           a radius for each parameter center, no negative radius, every
#           constant held by K, every variable an unknown or a parameter;
#   factor: 0 <= q < 1;
#   contraction: G r <= q r;
#   self-map: |Y f(X̃)| + |Y| ((|J0z| + Dz) rho) + G r <= r;
#   positive radii: n of them, each above 0.
# With the radii positive, the contraction bounds |I - Y J| r <= q r for
# every Jacobian J in the box, so Y J, Y and J are invertible: the
# inclusion theorem (Krawczyk, Rump; lib/certpf.bend).

import Base
import ../spec/ring.bend as E
import ../spec/knum.bend as N
import ./certdef.bend as C
import ./karith.bend as KA
import ./kball.bend as KB
import ./slope.bend as SL

# Pieces
# ------

# the box: a ball per variable (radius 0 past the radii's end)
def zipb(~K: N.Num, cs: N.KVec(~K), rs: N.KVec(~K)) -> List<&2, KB.KB<K>>:
  match cs rs:
    case Nil{} Nil{}:
      Nil{}
    case Nil{} Con{r, rt}:
      Con{KB.KB{N.nzero(K), r}, zipb(~K, Nil{}, rt)}
    case Con{c, ct} Nil{}:
      Con{KB.KB{c, N.nzero(K)}, zipb(~K, ct, Nil{})}
    case Con{c, ct} Con{r, rt}:
      Con{KB.KB{c, r}, zipb(~K, ct, rt)}

# each equation's slope enclosures in the cnt variables from lo
def srows(~K: N.Num, +box: List<&2, KB.KB<K>>, +cnt: Nat, +lo: Nat, eqs: List<&2, E.QExpr>) -> List<&2, List<&2, KB.KB<K>>>:
  match eqs:
    case Nil{}:
      Nil{}
    case Con{e, es}:
      Con{KB.krange(~K, box, e, cnt, lo), srows(~K, box, cnt, lo, es)}

def mcenters(~K: N.Num, rows: List<&2, List<&2, KB.KB<K>>>) -> N.KMat(~K):
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{KB.bcenters(~K, r), mcenters(~K, rs)}

def mradii(~K: N.Num, rows: List<&2, List<&2, KB.KB<K>>>) -> N.KMat(~K):
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{KB.bradii(~K, r), mradii(~K, rs)}

def allbelow(+m: Nat, eqs: List<&2, E.QExpr>) -> Bool:
  match eqs:
    case Nil{}:
      True{}
    case Con{e, es}:
      KA.band(SL.below(m, e), allbelow(m, es))

# the equations' values at env
def kvals(~K: N.Num, +env: N.KVec(~K), eqs: List<&2, E.QExpr>) -> N.KVec(~K):
  match eqs:
    case Nil{}:
      Nil{}
    case Con{e, es}:
      Con{KB.keval(~K, env, e), kvals(~K, env, es)}

def allheld(~K: N.Num, eqs: List<&2, E.QExpr>) -> Bool:
  match eqs:
    case Nil{}:
      True{}
    case Con{e, es}:
      KA.band(KB.held(~K, e), allheld(~K, es))

def eqlen(eqs: List<&2, E.QExpr>) -> Nat:
  match eqs:
    case Nil{}:
      0n
    case Con{e, es}:
      1n+eqlen(es)

def mlen(~K: N.Num, a: N.KMat(~K)) -> Nat:
  match a:
    case Nil{}:
      0n
    case Con{r, rs}:
      1n+mlen(~K, rs)

# The conditions
# --------------

def shape(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> Bool:
  KA.band(KA.nateq(eqlen(eqs), n), KA.band(KA.nateq(mlen(~K, ym), n), KA.band(KA.nateq(KA.klen(~K, yc), n), KA.band(KA.natle(KA.klen(~K, yr), n), KA.band(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), KA.band(allheld(~K, eqs), allbelow(Nat.add(n, KA.klen(~K, pc)), eqs)))))))))

def factor(~K: N.Num, +q: N.NC(K)) -> Bool:
  KA.band(KA.kle(~K, N.nzero(K), q), KA.klt(~K, q, N.none(K)))

# the box: centers ỹ ++ z̃, radii r (fitted to n) ++ rho
def box(~K: N.Num, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> List<&2, KB.KB<K>>:
  zipb(~K, KA.kapp(~K, yc, pc), KA.kapp(~K, KA.kfit(~K, n, yr), pr))

# slope enclosures in the unknowns and in the parameters
def rowsy(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> List<&2, List<&2, KB.KB<K>>>:
  srows(~K, box(~K, n, yc, yr, pc, pr), n, 0n, eqs)

def rowsz(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> List<&2, List<&2, KB.KB<K>>>:
  srows(~K, box(~K, n, yc, yr, pc, pr), KA.klen(~K, pc), n, eqs)

# I - A B
def imm(~K: N.Num, +n: Nat, +a: N.KMat(~K), +b: N.KMat(~K)) -> N.KMat(~K):
  KA.kmadd(~K, KA.kident(~K, n), KA.kmneg(~K, KA.kmatmul(~K, a, b)))

# G r = |I - Y J0y| r + |Y| (Dy r)
def gvec(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> N.KVec(~K):
  KA.kvadd(~K, KA.kmatvec(~K, KA.kmabs(~K, imm(~K, n, ym, mcenters(~K, rowsy(~K, eqs, n, yc, yr, pc, pr)))), yr), KA.kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, mradii(~K, rowsy(~K, eqs, n, yc, yr, pc, pr)), yr)))

# |Y f(X̃)| + |Y| ((|J0z| + Dz) rho) + G r
def svec(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> N.KVec(~K):
  KA.kvadd(~K, KA.kvadd(~K, KA.kvabs(~K, KA.kmatvec(~K, ym, kvals(~K, KA.kapp(~K, yc, pc), eqs))), KA.kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, KA.kmadd(~K, KA.kmabs(~K, mcenters(~K, rowsz(~K, eqs, n, yc, yr, pc, pr))), mradii(~K, rowsz(~K, eqs, n, yc, yr, pc, pr))), pr))), gvec(~K, eqs, n, yc, yr, ym, pc, pr))

# the bound conditions
def ccon(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> Bool:
  KA.kvle(~K, gvec(~K, eqs, n, yc, yr, ym, pc, pr), KA.kvscale(~K, q, yr))

def cself(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> Bool:
  KA.kvle(~K, svec(~K, eqs, n, yc, yr, ym, pc, pr), yr)

# n radii, each above 0
def cpos(~K: N.Num, +n: Nat, +yr: N.KVec(~K)) -> Bool:
  KA.band(KA.nateq(KA.klen(~K, yr), n), KA.kvlt(~K, Nil{}, yr))

# everything after the shape
def rest3(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> Bool:
  KA.band(cself(~K, eqs, n, yc, yr, ym, pc, pr), cpos(~K, n, yr))

def rest2(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> Bool:
  KA.band(ccon(~K, eqs, n, yc, yr, q, ym, pc, pr), rest3(~K, eqs, n, yc, yr, ym, pc, pr))

def rest1(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> Bool:
  KA.band(factor(~K, q), rest2(~K, eqs, n, yc, yr, q, ym, pc, pr))

def check.go(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> Bool:
  KA.band(shape(~K, eqs, n, yc, yr, ym, pc, pr), rest1(~K, eqs, n, yc, yr, q, ym, pc, pr))

def check.c(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, c: C.Cert<K>) -> Bool:
  match c:
    case C.Cert{yc, yr, q, ym, pc, pr}:
      check.go(~K, eqs, n, yc, yr, q, ym, pc, pr)

def check(~K: N.Num, b: C.Block, c: C.Cert<K>) -> Bool:
  match b:
    case C.Block{eqs, n}:
      check.c(~K, eqs, n, c)
