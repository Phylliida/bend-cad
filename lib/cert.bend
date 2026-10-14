# bend-cad: the block certificate checker (DESIGN §8.3). Untrusted: only the
# cert_* laws say what a passing check means. Generic over the computing
# numbers K; everything is exact in K.
#
# With n unknowns, center X̃ = ỹ ++ z̃ and box radii R = r ++ rho over all
# of the block's variables, the slope enclosure of each equation gives
# J0 (centers) and D (radii), split into unknown columns (y) and parameter
# columns (z). With G r = |I - Y J0y| r + |Y| (Dy r), the checker requires:
#   shape:  n equations, Y with n rows, ỹ with n entries, at most n radii,
#           a radius for each parameter center, no negative radius, every
#           constant held by K;
#   factor: 0 <= q < 1;
#   contraction: G r <= q r;
#   self-map: |Y f(X̃)| + |Y| ((|J0z| + Dz) rho) + G r <= r;
#   injectivity: each row of |I - J0y Y| sums to less than 1.

import Base
import ../spec/ring.bend as E
import ../spec/knum.bend as N
import ../spec/cert.bend as C
import ./karith.bend as KA
import ./kball.bend as KB

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

# each equation's slope enclosure
def slopes(~K: N.Num, +box: List<&2, KB.KB<K>>, eqs: List<&2, E.QExpr>) -> List<&2, List<&2, KB.KB<K>>>:
  match eqs:
    case Nil{}:
      Nil{}
    case Con{e, es}:
      Con{KB.kslope(~K, box, e), slopes(~K, box, es)}

# the centers of each row, fitted to its first n columns
def jy(~K: N.Num, +n: Nat, rows: List<&2, List<&2, KB.KB<K>>>) -> N.KMat(~K):
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{KA.kfit(~K, n, KB.bcenters(~K, r)), jy(~K, n, rs)}

def dy(~K: N.Num, +n: Nat, rows: List<&2, List<&2, KB.KB<K>>>) -> N.KMat(~K):
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{KA.kfit(~K, n, KB.bradii(~K, r)), dy(~K, n, rs)}

# the centers of each row past its first n columns
def jz(~K: N.Num, +n: Nat, rows: List<&2, List<&2, KB.KB<K>>>) -> N.KMat(~K):
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{KA.kdrop(~K, n, KB.bcenters(~K, r)), jz(~K, n, rs)}

def dz(~K: N.Num, +n: Nat, rows: List<&2, List<&2, KB.KB<K>>>) -> N.KMat(~K):
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{KA.kdrop(~K, n, KB.bradii(~K, r)), dz(~K, n, rs)}

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
  KA.band(KA.nateq(eqlen(eqs), n), KA.band(KA.nateq(mlen(~K, ym), n), KA.band(KA.nateq(KA.klen(~K, yc), n), KA.band(KA.natle(KA.klen(~K, yr), n), KA.band(KA.nateq(KA.klen(~K, pc), KA.klen(~K, pr)), KA.band(KA.kvle(~K, Nil{}, yr), KA.band(KA.kvle(~K, Nil{}, pr), allheld(~K, eqs))))))))

def factor(~K: N.Num, +q: N.NC(K)) -> Bool:
  KA.band(KA.kle(~K, N.nzero(K), q), KA.klt(~K, q, N.none(K)))

# G r = |I - Y J0y| r + |Y| (Dy r)
def gr(~K: N.Num, +n: Nat, +ym: N.KMat(~K), +j0y: N.KMat(~K), +d0y: N.KMat(~K), +r: N.KVec(~K)) -> N.KVec(~K):
  KA.kvadd(~K, KA.kmatvec(~K, KA.kmabs(~K, KA.kmadd(~K, KA.kident(~K, n), KA.kmneg(~K, KA.kmatmul(~K, ym, j0y)))), r), KA.kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, d0y, r)))

def check.go(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +yr: N.KVec(~K), +q: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> Bool:
  +box = zipb(~K, KA.kapp(~K, yc, pc), KA.kapp(~K, KA.kfit(~K, n, yr), pr))
  +rows = slopes(~K, box, eqs)
  +r = KA.kfit(~K, n, yr)
  +g = gr(~K, n, ym, jy(~K, n, rows), dy(~K, n, rows), r)
  +self = KA.kvadd(~K, KA.kvadd(~K, KA.kvabs(~K, KA.kmatvec(~K, ym, kvals(~K, KA.kapp(~K, yc, pc), eqs))), KA.kmatvec(~K, KA.kmabs(~K, ym), KA.kmatvec(~K, KA.kmadd(~K, KA.kmabs(~K, jz(~K, n, rows)), dz(~K, n, rows)), pr))), g)
  +inj = KA.kmatvec(~K, KA.kmabs(~K, KA.kmadd(~K, KA.kident(~K, n), KA.kmneg(~K, KA.kmatmul(~K, jy(~K, n, rows), ym)))), KA.kones(~K, n))
  KA.band(shape(~K, eqs, n, yc, yr, ym, pc, pr), KA.band(factor(~K, q), KA.band(KA.kvle(~K, g, KA.kvscale(~K, q, r)), KA.band(KA.kvle(~K, self, r), KA.kvlt(~K, inj, KA.kones(~K, n))))))

def check.c(~K: N.Num, +eqs: List<&2, E.QExpr>, +n: Nat, c: C.Cert<K>) -> Bool:
  match c:
    case C.Cert{yc, yr, q, ym, pc, pr}:
      check.go(~K, eqs, n, yc, yr, q, ym, pc, pr)

def check(~K: N.Num, b: C.Block, c: C.Cert<K>) -> Bool:
  match b:
    case C.Block{eqs, n}:
      check.c(~K, eqs, n, c)
