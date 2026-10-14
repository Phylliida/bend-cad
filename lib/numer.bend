# bend-cad: the numbers of a plan (DESIGN §10.1, stage 3). Part of the
# verified proposer: nothing computed here is believed. Each block's
# certificate goes through the block checker as it is built, and the whole
# plan through lib/plan.bend's checker before anything is reported
# (lib/solve.bend); that a regular solution is always reached is the
# completeness law (ROADMAP: solve_complete).
#
# Per block, in block order: Newton at a working precision P (every
# iterate rounded to P fractional bits), from the drawing's values, with
# the parameters at their centers; the Jacobian is the checker's own slope
# enclosure at a box of radius 0 (so exactly the derivative), inverted
# exactly over ℚ by Gauss-Jordan; Y is that inverse at the final center,
# rounded to 32 significant bits; the radius is the first of
# R0 (17/16)^k (k < 64) the block checker accepts, R0 the largest entry
# of the self-map bound at radius 0 times 65/64. A block that fails sinks the
# plan at this precision; lib/solve.bend retries at 2P.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/knum.bend as N
import ./certdef.bend as C
import ./karith.bend as KA
import ./kball.bend as KB
import ./cert.bend as CK
import ./kinst.bend as KI
import ./qreduce.bend as QRD
import ./plan.bend as PL
import ./struct.bend as ST

# Rationals
# ---------

def zpos(z: S.Z) -> S.Pos:
  match z:
    case S.Z0{}:
      S.XH{}
    case S.Zpos{p}:
      p
    case S.Zneg{p}:
      p

def qz() -> S.Q:
  S.Q{S.Z0{}, S.XH{}}

def qone() -> S.Q:
  S.Q{S.Zpos{S.XH{}}, S.XH{}}

def qadd(+a: S.Q, +b: S.Q) -> S.Q:
  QRD.reduce(S.Q.add(a, b))

def qsub(+a: S.Q, +b: S.Q) -> S.Q:
  QRD.reduce(S.Q.sub(a, b))

def qmul(+a: S.Q, +b: S.Q) -> S.Q:
  QRD.reduce(S.Q.mul(a, b))

def qinv(+a: S.Q) -> S.Q:
  QRD.reduce(S.Q.inv(a))

def qzero(x: S.Q) -> Bool:
  match x:
    case S.Q{S.Z0{}, d}:
      True{}
    case S.Q{S.Zpos{p}, d}:
      False{}
    case S.Q{S.Zneg{p}, d}:
      False{}

# Rounding to dyadics
# -------------------

# floor(n / d)
def zfloor.neg(dv: QRD.Dv) -> S.Z:
  match dv:
    case QRD.Dv{q, S.Z0{}}:
      S.Z.neg(q)
    case QRD.Dv{q, S.Zpos{r}}:
      S.Z.neg(S.Z.add(q, S.Zpos{S.XH{}}))
    case QRD.Dv{q, S.Zneg{r}}:
      S.Z.neg(q)

def zfloor(n: S.Z, +d: S.Pos) -> S.Z:
  match n:
    case S.Z0{}:
      S.Z0{}
    case S.Zpos{p}:
      QRD.Dv.q(QRD.div(p, d))
    case S.Zneg{p}:
      zfloor.neg(QRD.div(p, d))

# x rounded to the nearest multiple of 2^-e
def qround(+x: S.Q, +e: Nat) -> S.D:
  S.D{zfloor(S.Z.add(S.Z.double(S.Z.mul(S.Q.num(x), S.Zpos{S.Pos.pow2(e)})), S.Zpos{S.Q.den(x)}), S.XO{S.Q.den(x)}), e}

# x rounded to about b significant bits
def qsig.go(+x: S.Q, +b: Nat, n: S.Z) -> S.D:
  match n:
    case S.Z0{}:
      S.D{S.Z0{}, 0n}
    case S.Zpos{p}:
      qround(x, Nat.sub(Nat.add(b, QRD.size(S.Q.den(x))), QRD.size(p)))
    case S.Zneg{p}:
      qround(x, Nat.sub(Nat.add(b, QRD.size(S.Q.den(x))), QRD.size(p)))

def qsig(+x: S.Q, +b: Nat) -> S.D:
  qsig.go(x, b, S.Q.num(x))

# x rounded up to a multiple of 2^-e
def qceil(+x: S.Q, +e: Nat) -> S.D:
  S.D{S.Z.neg(zfloor(S.Z.neg(S.Z.mul(S.Q.num(x), S.Zpos{S.Pos.pow2(e)})), S.Q.den(x))), e}

# x >= 0 rounded up to about b significant bits
def qsigup.go(+x: S.Q, +b: Nat, n: S.Z) -> S.D:
  match n:
    case S.Z0{}:
      S.D{S.Z0{}, 0n}
    case S.Zpos{p}:
      qceil(x, Nat.sub(Nat.add(b, QRD.size(S.Q.den(x))), QRD.size(p)))
    case S.Zneg{p}:
      qceil(x, Nat.sub(Nat.add(b, QRD.size(S.Q.den(x))), QRD.size(p)))

def dsigup(+x: S.D, +b: Nat) -> S.D:
  qsigup.go(S.D.toq(x), b, S.D.man(x))

def dzero() -> S.D:
  S.D{S.Z0{}, 0n}

def dmax.go(c: Cmp, a: S.D, b: S.D) -> S.D:
  match c:
    case LT{}:
      b
    case EQ{}:
      a
    case GT{}:
      a

def dmax(+a: S.D, +b: S.D) -> S.D:
  dmax.go(KI.dcmp(a, b), a, b)

def dvmax(xs: List<&2, S.D>) -> S.D:
  match xs:
    case Nil{}:
      dzero()
    case Con{x, t}:
      dmax(x, dvmax(t))

def deq.go(c: Cmp) -> Bool:
  match c:
    case LT{}:
      False{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

def dveq(xs: List<&2, S.D>, ys: List<&2, S.D>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, yt}:
      False{}
    case Con{x, xt} Nil{}:
      False{}
    case Con{+x, xt} Con{+y, yt}:
      KA.band(deq.go(KI.dcmp(x, y)), dveq(xt, yt))

def dreps(n: Nat, +x: S.D) -> List<&2, S.D>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{x, dreps(m, x)}

# Vectors and matrices over ℚ
# ---------------------------

def qv(xs: List<&2, S.D>) -> List<&2, S.Q>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{S.D.toq(x), qv(t)}

def qm(a: List<&2, List<&2, S.D>>) -> List<&2, List<&2, S.Q>>:
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{qv(r), qm(t)}

def qget(xs: List<&2, S.Q>, k: Nat) -> S.Q:
  match xs k:
    case Nil{} k:
      qz()
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      qget(t, j)

def qrow(xs: List<&2, List<&2, S.Q>>, k: Nat) -> List<&2, S.Q>:
  match xs k:
    case Nil{} k:
      Nil{}
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      qrow(t, j)

def qset(xs: List<&2, List<&2, S.Q>>, k: Nat, +r: List<&2, S.Q>) -> List<&2, List<&2, S.Q>>:
  match xs k:
    case Nil{} k:
      Nil{}
    case Con{h, t} 0n:
      Con{r, t}
    case Con{h, t} 1n+j:
      Con{h, qset(t, j, r)}

def qscale(+c: S.Q, xs: List<&2, S.Q>) -> List<&2, S.Q>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{qmul(c, x), qscale(c, t)}

# xs - c ys
def qaxpy(xs: List<&2, S.Q>, +c: S.Q, ys: List<&2, S.Q>) -> List<&2, S.Q>:
  match xs ys:
    case Nil{} ys:
      Nil{}
    case Con{x, t} Nil{}:
      Con{x, t}
    case Con{+x, t} Con{+y, u}:
      Con{qsub(x, qmul(c, y)), qaxpy(t, c, u)}

def qdot(xs: List<&2, S.Q>, ys: List<&2, S.Q>) -> S.Q:
  match xs ys:
    case Nil{} ys:
      qz()
    case Con{x, t} Nil{}:
      qz()
    case Con{+x, t} Con{+y, u}:
      qadd(qmul(x, y), qdot(t, u))

def qmatvec(a: List<&2, List<&2, S.Q>>, +v: List<&2, S.Q>) -> List<&2, S.Q>:
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{qdot(r, v), qmatvec(t, v)}

# Gauss-Jordan
# ------------
# On the rows of [J | I]; a column with no nonzero entry at or below the
# diagonal means J is singular (no inverse).

def qzeros(n: Nat) -> List<&2, S.Q>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{qz(), qzeros(m)}

def qapp(xs: List<&2, S.Q>, ys: List<&2, S.Q>) -> List<&2, S.Q>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, qapp(t, ys)}

def qdrop(n: Nat, xs: List<&2, S.Q>) -> List<&2, S.Q>:
  match n xs:
    case 0n xs:
      xs
    case 1n+m Nil{}:
      Nil{}
    case 1n+m Con{h, t}:
      qdrop(m, t)

# the k-th unit vector of length n
def unit(n: Nat, +k: Nat) -> List<&2, S.Q>:
  match n k:
    case 0n k:
      Nil{}
    case 1n+m 0n:
      Con{qone(), qzeros(m)}
    case 1n+m 1n+j:
      Con{qz(), unit(m, j)}

def augment(a: List<&2, List<&2, S.Q>>, +n: Nat, +k: Nat) -> List<&2, List<&2, S.Q>>:
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{qapp(r, unit(n, k)), augment(t, n, 1n+k)}

# the first row at or after k (counting from i) with a nonzero entry in
# column c
def pivot.go(b: Bool, +i: Nat, rest: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{i}
    case False{}:
      rest

def pivot(rows: List<&2, List<&2, S.Q>>, +c: Nat, +k: Nat, +i: Nat) -> Maybe<&2, Nat>:
  match rows:
    case Nil{}:
      None{}
    case Con{r, t}:
      pivot.go(KA.band(KA.natle(k, i), ST.bnot(qzero(qget(r, c)))), i, pivot(t, c, k, 1n+i))

def swap(+rows: List<&2, List<&2, S.Q>>, +a: Nat, +b: Nat) -> List<&2, List<&2, S.Q>>:
  qset(qset(rows, a, qrow(rows, b)), b, qrow(rows, a))

# clear column c from every row but the pivot row p (already scaled)
def clear.ax(+r: List<&2, S.Q>, +p: List<&2, S.Q>, +c: Nat) -> List<&2, S.Q>:
  qaxpy(r, qget(r, c), p)

def clear.go(b: Bool, r: List<&2, S.Q>, +p: List<&2, S.Q>, +c: Nat) -> List<&2, S.Q>:
  match b:
    case True{}:
      p
    case False{}:
      clear.ax(r, p, c)

def clear(rows: List<&2, List<&2, S.Q>>, +p: List<&2, S.Q>, +c: Nat, +i: Nat) -> List<&2, List<&2, S.Q>>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{clear.go(KA.nateq(i, c), r, p, c), clear(t, p, c, 1n+i)}

def elim(+rows: List<&2, List<&2, S.Q>>, +c: Nat) -> List<&2, List<&2, S.Q>>:
  clear(rows, qscale(qinv(qget(qrow(rows, c), c)), qrow(rows, c)), c, 0n)

def gj(k: Nat, +c: Nat, piv: Maybe<&2, Nat>, +rows: List<&2, List<&2, S.Q>>) -> Maybe<&2, List<&2, List<&2, S.Q>>>:
  match k piv:
    case 0n piv:
      Some{rows}
    case 1n+m None{}:
      None{}
    case 1n+m Some{r}:
      +rows2 = elim(swap(rows, c, r), c)
      gj(m, 1n+c, pivot(rows2, 1n+c, 1n+c, 0n), rows2)

def rights(+n: Nat, rows: List<&2, List<&2, S.Q>>) -> List<&2, List<&2, S.Q>>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{qdrop(n, r), rights(n, t)}

def inv.of(+n: Nat, m: Maybe<&2, List<&2, List<&2, S.Q>>>) -> Maybe<&2, List<&2, List<&2, S.Q>>>:
  match m:
    case None{}:
      None{}
    case Some{rows}:
      Some{rights(n, rows)}

def qgj(+n: Nat, +rows: List<&2, List<&2, S.Q>>) -> Maybe<&2, List<&2, List<&2, S.Q>>>:
  gj(n, 0n, pivot(rows, 0n, 0n, 0n), rows)

# J^-1 for an n x n matrix J, or None when J is singular
def qinverse(+n: Nat, a: List<&2, List<&2, S.Q>>) -> Maybe<&2, List<&2, List<&2, S.Q>>>:
  inv.of(n, qgj(n, augment(a, n, 0n)))


# Dyadic elimination
# ------------------
# Exact ℚ elimination reduces by a gcd after every operation, and the
# gcd's long division is slow at a hundred bits and more. Newton and Y
# need only an approximate inverse, so they eliminate over D with every
# result rounded to B significant bits and partial pivoting (the largest
# entry). Nothing here is believed: the block checker judges the result.

# p / 2^k, rounded down
def pshr(x: S.Pos, k: Nat) -> S.Z:
  match x k:
    case S.XH{} 0n:
      S.Zpos{S.XH{}}
    case S.XH{} 1n+j:
      S.Z0{}
    case S.XO{q} 0n:
      S.Zpos{S.XO{q}}
    case S.XO{q} 1n+j:
      pshr(q, j)
    case S.XI{q} 0n:
      S.Zpos{S.XI{q}}
    case S.XI{q} 1n+j:
      pshr(q, j)

# p / 2^k rounded to nearest (k >= 1)
def pshr_round(+p: S.Pos, +k: Nat) -> S.Z:
  pshr(S.Pos.add(p, S.Pos.pow2(Nat.sub(k, 1n))), k)

def zshr_round(m: S.Z, +k: Nat) -> S.Z:
  match m:
    case S.Z0{}:
      S.Z0{}
    case S.Zpos{p}:
      pshr_round(p, k)
    case S.Zneg{p}:
      S.Z.neg(pshr_round(p, k))

# x rounded to a multiple of 2^-p
def dround.go(le: Bool, x: S.D, +p: Nat) -> S.D:
  match le x:
    case True{} x:
      x
    case False{} S.D{m, +e}:
      S.D{zshr_round(m, Nat.sub(e, p)), p}

def dround(+x: S.D, +p: Nat) -> S.D:
  dround.go(KA.natle(S.D.exp(x), p), x, p)

# x rounded to about b significant bits
def dsig.sh(le: Bool, m: S.Z, +e: Nat, +k: Nat) -> S.D:
  match le:
    case True{}:
      S.D{zshr_round(m, k), Nat.sub(e, k)}
    case False{}:
      S.D{S.Z.mul(zshr_round(m, k), S.Zpos{S.Pos.pow2(Nat.sub(k, e))}), 0n}

def dsig.go(le: Bool, x: S.D, +k: Nat) -> S.D:
  match le x:
    case True{} x:
      x
    case False{} S.D{m, +e}:
      dsig.sh(KA.natle(k, e), m, e, k)

def dsig(+x: S.D, +b: Nat) -> S.D:
  dsig.go(KA.natle(QRD.size(zpos(S.D.man(x))), b), x, Nat.sub(QRD.size(zpos(S.D.man(x))), b))

def dabs(+x: S.D) -> S.D:
  KA.kabs(~KI.dnum(), x)

def dnz(x: S.D) -> Bool:
  match x:
    case S.D{S.Z0{}, e}:
      False{}
    case S.D{S.Zpos{p}, e}:
      True{}
    case S.D{S.Zneg{p}, e}:
      True{}

def bits() -> Nat:
  64n

def dsadd(+a: S.D, +b: S.D) -> S.D:
  dsig(S.D.add(a, b), bits())

def dsmul(+a: S.D, +b: S.D) -> S.D:
  dsig(S.D.mul(a, b), bits())

def dsdiv(+a: S.D, +b: S.D) -> S.D:
  qsig(S.Q.div(S.D.toq(a), S.D.toq(b)), bits())

def dget(xs: List<&2, S.D>, k: Nat) -> S.D:
  match xs k:
    case Nil{} k:
      dzero()
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      dget(t, j)

def drow(xs: List<&2, List<&2, S.D>>, k: Nat) -> List<&2, S.D>:
  match xs k:
    case Nil{} k:
      Nil{}
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      drow(t, j)

def dset(xs: List<&2, List<&2, S.D>>, k: Nat, +r: List<&2, S.D>) -> List<&2, List<&2, S.D>>:
  match xs k:
    case Nil{} k:
      Nil{}
    case Con{h, t} 0n:
      Con{r, t}
    case Con{h, t} 1n+j:
      Con{h, dset(t, j, r)}

def dscale(+c: S.D, xs: List<&2, S.D>) -> List<&2, S.D>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{dsmul(c, x), dscale(c, t)}

# xs - c ys
def daxpy(xs: List<&2, S.D>, +c: S.D, ys: List<&2, S.D>) -> List<&2, S.D>:
  match xs ys:
    case Nil{} ys:
      Nil{}
    case Con{x, t} Nil{}:
      Con{x, t}
    case Con{+x, t} Con{+y, u}:
      Con{dsadd(x, S.D.neg(dsmul(c, y))), daxpy(t, c, u)}

def dzeros(n: Nat) -> List<&2, S.D>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{dzero(), dzeros(m)}

def done() -> S.D:
  S.D{S.Zpos{S.XH{}}, 0n}

def dunit(n: Nat, +k: Nat) -> List<&2, S.D>:
  match n k:
    case 0n k:
      Nil{}
    case 1n+m 0n:
      Con{done(), dzeros(m)}
    case 1n+m 1n+j:
      Con{dzero(), dunit(m, j)}

def dapp(xs: List<&2, S.D>, ys: List<&2, S.D>) -> List<&2, S.D>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, dapp(t, ys)}

def daugment(a: List<&2, List<&2, S.D>>, +n: Nat, +k: Nat) -> List<&2, List<&2, S.D>>:
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{dapp(r, dunit(n, k)), daugment(t, n, 1n+k)}

def ddrop(n: Nat, xs: List<&2, S.D>) -> List<&2, S.D>:
  match n xs:
    case 0n xs:
      xs
    case 1n+m Nil{}:
      Nil{}
    case 1n+m Con{h, t}:
      ddrop(m, t)

def dpivot.best(le: Bool, c: Cmp, +i: Nat, best: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match le c:
    case False{} c:
      best
    case True{} GT{}:
      Some{i}
    case True{} EQ{}:
      best
    case True{} LT{}:
      best

def dpivot.bx(le: Bool, +bx: S.D, +x: S.D) -> S.D:
  match le:
    case False{}:
      bx
    case True{}:
      dmax(bx, x)

# the row at or after k (counting from i) whose entry in column c is
# largest in size (None: all zero); bx is the best size so far
def dpivot(rows: List<&2, List<&2, S.D>>, +c: Nat, +k: Nat, +i: Nat, best: Maybe<&2, Nat>, +bx: S.D) -> Maybe<&2, Nat>:
  match rows:
    case Nil{}:
      best
    case Con{+r, t}:
      dpivot(t, c, k, 1n+i, dpivot.best(KA.natle(k, i), KI.dcmp(dabs(dget(r, c)), bx), i, best), dpivot.bx(KA.natle(k, i), bx, dabs(dget(r, c))))

def dswap(+rows: List<&2, List<&2, S.D>>, +a: Nat, +b: Nat) -> List<&2, List<&2, S.D>>:
  dset(dset(rows, a, drow(rows, b)), b, drow(rows, a))

def dclear.ax(+r: List<&2, S.D>, +p: List<&2, S.D>, +c: Nat) -> List<&2, S.D>:
  daxpy(r, dget(r, c), p)

def dclear.go(b: Bool, +r: List<&2, S.D>, +p: List<&2, S.D>, +c: Nat) -> List<&2, S.D>:
  match b:
    case True{}:
      p
    case False{}:
      dclear.ax(r, p, c)

def dclear(rows: List<&2, List<&2, S.D>>, +p: List<&2, S.D>, +c: Nat, +i: Nat) -> List<&2, List<&2, S.D>>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{dclear.go(KA.nateq(i, c), r, p, c), dclear(t, p, c, 1n+i)}

def delim(+rows: List<&2, List<&2, S.D>>, +c: Nat) -> List<&2, List<&2, S.D>>:
  dclear(rows, dscale(dsdiv(done(), dget(drow(rows, c), c)), drow(rows, c)), c, 0n)

def dgj(k: Nat, +c: Nat, piv: Maybe<&2, Nat>, +rows: List<&2, List<&2, S.D>>) -> Maybe<&2, List<&2, List<&2, S.D>>>:
  match k piv:
    case 0n piv:
      Some{rows}
    case 1n+m None{}:
      None{}
    case 1n+m Some{r}:
      +rows2 = delim(dswap(rows, c, r), c)
      dgj(m, 1n+c, dpivot(rows2, 1n+c, 1n+c, 0n, None{}, dzero()), rows2)

def drights(+n: Nat, rows: List<&2, List<&2, S.D>>) -> List<&2, List<&2, S.D>>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{ddrop(n, r), drights(n, t)}

def dinv.of(+n: Nat, m: Maybe<&2, List<&2, List<&2, S.D>>>) -> Maybe<&2, List<&2, List<&2, S.D>>>:
  match m:
    case None{}:
      None{}
    case Some{rows}:
      Some{drights(n, rows)}

def dgj0(+n: Nat, +rows: List<&2, List<&2, S.D>>) -> Maybe<&2, List<&2, List<&2, S.D>>>:
  dgj(n, 0n, dpivot(rows, 0n, 0n, 0n, None{}, dzero()), rows)

# an approximate J^-1 (None when elimination meets an all-zero column)
def dinverse(+n: Nat, a: List<&2, List<&2, S.D>>) -> Maybe<&2, List<&2, List<&2, S.D>>>:
  dinv.of(n, dgj0(n, daugment(a, n, 0n)))

def ddot(xs: List<&2, S.D>, ys: List<&2, S.D>) -> S.D:
  match xs ys:
    case Nil{} ys:
      dzero()
    case Con{x, t} Nil{}:
      dzero()
    case Con{+x, t} Con{+y, u}:
      S.D.add(S.D.mul(x, y), ddot(t, u))

def dmatvec(a: List<&2, List<&2, S.D>>, +v: List<&2, S.D>) -> List<&2, S.D>:
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{ddot(r, v), dmatvec(t, v)}

# A block at precision P
# ----------------------
# eqs are the block's equations numbered locally (unknowns 0 .. n-1, then
# the parameters), pc the parameters' centers. Every vector is in D.

def dn() -> N.Num:
  KI.dnum()

# J at y ++ pc: the slope enclosure over a box of radius 0
def jac(+eqs: List<&2, E.QExpr>, +n: Nat, +env: List<&2, S.D>) -> List<&2, List<&2, S.D>>:
  CK.mcenters(~KI.dnum(), CK.srows(~KI.dnum(), CK.zipb(~KI.dnum(), env, Nil{}), n, 0n, eqs))

def vals(+eqs: List<&2, E.QExpr>, +env: List<&2, S.D>) -> List<&2, S.D>:
  CK.kvals(~KI.dnum(), env, eqs)

# y - d rounded to P fractional bits
def nstep.round(ys: List<&2, S.D>, ds: List<&2, S.D>, +p: Nat) -> List<&2, S.D>:
  match ys ds:
    case Nil{} ds:
      Nil{}
    case Con{+y, yt} Nil{}:
      Con{dround(y, p), nstep.round(yt, Nil{}, p)}
    case Con{+y, yt} Con{+d, dt}:
      Con{dround(S.D.sub(y, d), p), nstep.round(yt, dt, p)}

def nstep.of(+ys: List<&2, S.D>, m: Maybe<&2, List<&2, List<&2, S.D>>>, +f: List<&2, S.D>, +p: Nat) -> Maybe<&2, List<&2, S.D>>:
  match m:
    case None{}:
      None{}
    case Some{inv}:
      Some{nstep.round(ys, dmatvec(inv, f), p)}

# one Newton step (None: elimination met an all-zero column)
def nstep(+eqs: List<&2, E.QExpr>, +n: Nat, +pc: List<&2, S.D>, +p: Nat, +ys: List<&2, S.D>) -> Maybe<&2, List<&2, S.D>>:
  nstep.of(ys, dinverse(n, jac(eqs, n, dapp(ys, pc))), vals(eqs, dapp(ys, pc)), p)

# a Newton step's outcome: moved, settled (the step changed nothing), or
# singular
type NS is Data:
  NMore{y: List<&2, S.D>}
  NDone{y: List<&2, S.D>}
  NSing{}

def classify.go(same: Bool, y2: List<&2, S.D>) -> NS:
  match same:
    case True{}:
      NDone{y2}
    case False{}:
      NMore{y2}

def classify(+ys: List<&2, S.D>, m: Maybe<&2, List<&2, S.D>>) -> NS:
  match m:
    case None{}:
      NSing{}
    case Some{+y2}:
      classify.go(dveq(ys, y2), y2)

# at most k steps
def newton(k: Nat, +eqs: List<&2, E.QExpr>, +n: Nat, +pc: List<&2, S.D>, +p: Nat, st: NS) -> Maybe<&2, List<&2, S.D>>:
  match k st:
    case k NSing{}:
      None{}
    case k NDone{y}:
      Some{y}
    case 0n NMore{y}:
      None{}
    case 1n+j NMore{+y}:
      newton(j, eqs, n, pc, p, classify(y, nstep(eqs, n, pc, p, y)))

# Y: J^-1 at the center, 32 significant bits
def ysigv(xs: List<&2, S.D>) -> List<&2, S.D>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{dsig(x, 32n), ysigv(t)}

def ysig(a: List<&2, List<&2, S.D>>) -> List<&2, List<&2, S.D>>:
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{ysigv(r), ysig(t)}

def dsigv(xs: List<&2, S.Q>) -> List<&2, S.D>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{qsig(x, 32n), dsigv(t)}

def dsigm(a: List<&2, List<&2, S.Q>>) -> List<&2, List<&2, S.D>>:
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{dsigv(r), dsigm(t)}

def half() -> S.D:
  S.D{S.Zpos{S.XH{}}, 1n}

def mkcert(+n: Nat, yc: List<&2, S.D>, +r: S.D, ym: List<&2, List<&2, S.D>>, pc: List<&2, S.D>, pr: List<&2, S.D>) -> C.Cert<KI.dnum()>:
  C.Cert{yc, dreps(n, r), half(), ym, pc, pr}

def okr(+eqs: List<&2, E.QExpr>, +n: Nat, +yc: List<&2, S.D>, +r: S.D, +ym: List<&2, List<&2, S.D>>, +pc: List<&2, S.D>, +pr: List<&2, S.D>) -> Bool:
  CK.check(~KI.dnum(), C.Block{eqs, n}, mkcert(n, yc, r, ym, pc, pr))

# r (17/16), at about 8 significant bits
def grow(+r: S.D) -> S.D:
  dsigup(S.D.mul(r, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n}), 8n)

# the first radius r (9/8)^i, i < k, that the block checker accepts
def rsearch(k: Nat, ok: Bool, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: List<&2, S.D>, +r: S.D, +ym: List<&2, List<&2, S.D>>, +pc: List<&2, S.D>, +pr: List<&2, S.D>) -> Maybe<&2, S.D>:
  match k ok:
    case k True{}:
      Some{r}
    case 0n False{}:
      None{}
    case 1n+j False{}:
      rsearch(j, okr(eqs, n, yc, grow(r), ym, pc, pr), eqs, n, yc, grow(r), ym, pc, pr)

# the largest entry of |Y f| + |Y| (|J0z| + Dz) rho, times 65/64, at
# about 8 bits
def r0(+eqs: List<&2, E.QExpr>, +n: Nat, +yc: List<&2, S.D>, +ym: List<&2, List<&2, S.D>>, +pc: List<&2, S.D>, +pr: List<&2, S.D>) -> S.D:
  dsigup(S.D.mul(dvmax(CK.svec(~KI.dnum(), eqs, n, yc, Nil{}, ym, pc, pr)), S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n}), 8n)

# a block's outcome: a certificate; no radius found (a higher precision
# may help); or Newton did not settle, or the Jacobian looked singular
# (stop: more precision will not help)
type BR is Data:
  BOk{c: C.Cert<KI.dnum()>}
  BRetry{}
  BStop{}

def block.r(m: Maybe<&2, S.D>, +n: Nat, +yc: List<&2, S.D>, +ym: List<&2, List<&2, S.D>>, +pc: List<&2, S.D>, +pr: List<&2, S.D>) -> BR:
  match m:
    case None{}:
      BRetry{}
    case Some{+r}:
      BOk{mkcert(n, yc, r, ym, pc, pr)}

def block.ym(+ym: List<&2, List<&2, S.D>>, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>) -> BR:
  block.r(rsearch(64n, okr(eqs, n, yc, r0(eqs, n, yc, ym, pc, pr), ym, pc, pr), eqs, n, yc, r0(eqs, n, yc, ym, pc, pr), ym, pc, pr), n, yc, ym, pc, pr)

def block.y2(m: Maybe<&2, List<&2, List<&2, S.D>>>, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: List<&2, S.D>, +pc: List<&2, S.D>, +pr: List<&2, S.D>) -> BR:
  match m:
    case None{}:
      BStop{}
    case Some{inv}:
      block.ym(ysig(inv), eqs, n, yc, pc, pr)

def block.y(m: Maybe<&2, List<&2, S.D>>, +eqs: List<&2, E.QExpr>, +n: Nat, +pc: List<&2, S.D>, +pr: List<&2, S.D>) -> BR:
  match m:
    case None{}:
      BStop{}
    case Some{+yc}:
      block.y2(dinverse(n, jac(eqs, n, dapp(yc, pc))), eqs, n, yc, pc, pr)

# a block's certificate at precision p, from the drawing's values y0
def block(+eqs: List<&2, E.QExpr>, +n: Nat, +pc: List<&2, S.D>, +pr: List<&2, S.D>, y0: List<&2, S.D>, +p: Nat) -> BR:
  block.y(newton(Nat.add(p, 8n), eqs, n, pc, p, NMore{y0}), eqs, n, pc, pr)

# A plan at precision P
# ---------------------
# The box is built in block order (pins first, at the drawing's values,
# radius 0); each block reads its parameters' centers and radii from what
# is built so far and appends its own.

def dlook(xs: List<&2, S.D>, k: Nat) -> S.D:
  match xs k:
    case Nil{} k:
      dzero()
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      dlook(t, j)

def dpick(+xs: List<&2, S.D>, ks: List<&2, Nat>) -> List<&2, S.D>:
  match ks:
    case Nil{}:
      Nil{}
    case Con{k, t}:
      Con{dlook(xs, k), dpick(xs, t)}

def dtake(n: Nat, xs: List<&2, S.D>) -> List<&2, S.D>:
  match n xs:
    case 0n xs:
      Nil{}
    case 1n+m Nil{}:
      Nil{}
    case 1n+m Con{h, t}:
      Con{h, dtake(m, t)}

# the first block's outcome (stop for no block)
def bcert.n(+n: Nat, +pars: List<&2, Nat>, +sys: List<&2, E.QExpr>, +g0b: List<&2, S.D>, +p: Nat, +o: Nat, +gc: List<&2, S.D>, +gr: List<&2, S.D>) -> BR:
  block(PL.renames(o, n, pars, PL.takeq(n, sys)), n, dpick(gc, pars), dpick(gr, pars), dtake(n, ddrop(o, g0b)), p)

def bcert(bs: List<&2, ST.SkB>, +sys: List<&2, E.QExpr>, +g0b: List<&2, S.D>, +p: Nat, +o: Nat, +gc: List<&2, S.D>, +gr: List<&2, S.D>) -> BR:
  match bs:
    case Nil{}:
      BStop{}
    case Con{ST.SkB{es, vs, +pars}, t}:
      bcert.n(ST.len(es), pars, sys, g0b, p, o, gc, gr)

type PB is Data:
  PB{bs: List<&2, PL.PBlock<KI.dnum()>>, gc: List<&2, S.D>, gr: List<&2, S.D>}

type PBR is Data:
  PBOk{pb: PB}
  PBRetry{}
  PBStop{}

def revpb.go(xs: List<&2, PL.PBlock<KI.dnum()>>, acc: List<&2, PL.PBlock<KI.dnum()>>) -> List<&2, PL.PBlock<KI.dnum()>>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      revpb.go(t, Con{h, acc})

def cert.yc(c: C.Cert<KI.dnum()>) -> List<&2, S.D>:
  match c:
    case C.Cert{yc, yr, q, ym, pc, pr}:
      yc

def cert.yr(c: C.Cert<KI.dnum()>) -> List<&2, S.D>:
  match c:
    case C.Cert{yc, yr, q, ym, pc, pr}:
      yr

# the blocks in turn (cur: the first block's certificate)
def pblocks(bs: List<&2, ST.SkB>, cur: BR, +sys: List<&2, E.QExpr>, +g0b: List<&2, S.D>, +p: Nat, +o: Nat, +gc: List<&2, S.D>, +gr: List<&2, S.D>, acc: List<&2, PL.PBlock<KI.dnum()>>) -> PBR:
  match bs cur:
    case Nil{} cur:
      PBOk{PB{revpb.go(acc, Nil{}), gc, gr}}
    case Con{b, t} BRetry{}:
      PBRetry{}
    case Con{b, t} BStop{}:
      PBStop{}
    case Con{ST.SkB{es, vs, +pars}, +t} BOk{+c}:
      +n = ST.len(es)
      +sys2 = PL.dropq(n, sys)
      +gc2 = dapp(gc, cert.yc(c))
      +gr2 = dapp(gr, dtake(n, cert.yr(c)))
      pblocks(t, bcert(t, sys2, g0b, p, Nat.add(o, n), gc2, gr2), sys2, g0b, p, Nat.add(o, n), gc2, gr2, Con{PL.PBlock{n, pars, c}, acc})

# the box in the system's own order: variable v at its position in vp
def unperm(n: Nat, +k: Nat, +xs: List<&2, S.D>, +vp: List<&2, Nat>) -> List<&2, S.D>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{dlook(xs, ST.pos(k, vp)), unperm(m, 1n+k, xs, vp)}

# A certified plan for the system es over nv variables, from the drawing
# g0 (one value per variable) at precision p
type NP is Data:
  NP{plan: PL.Plan<KI.dnum()>, gc: List<&2, S.D>, gr: List<&2, S.D>}

# a plan, or retry at a higher precision, or stop
type PR is Data:
  POk{np: NP}
  PRetry{}
  PStop{}

def plan.fin(+vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +nv: Nat, m: PBR) -> PR:
  match m:
    case PBRetry{}:
      PRetry{}
    case PBStop{}:
      PStop{}
    case PBOk{PB{bs, +gc, +gr}}:
      POk{NP{PL.Plan{vp, ep, np, bs}, unperm(nv, 0n, gc, vp), unperm(nv, 0n, gr, vp)}}

def plan.go(+es: List<&2, E.QExpr>, +nv: Nat, +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, ST.SkB>, +g0b: List<&2, S.D>, +p: Nat) -> PR:
  plan.fin(vp, ep, np, nv, pblocks(bs, bcert(bs, PL.reorder(vp, es, ep), g0b, p, np, dtake(np, g0b), dreps(np, dzero())), PL.reorder(vp, es, ep), g0b, p, np, dtake(np, g0b), dreps(np, dzero()), Nil{}))

def plan(+es: List<&2, E.QExpr>, +nv: Nat, sk: ST.Skel, +g0: List<&2, S.D>, +p: Nat) -> PR:
  match sk:
    case ST.Skel{+vp, +ep, +np, +bs, red}:
      plan.go(es, nv, vp, ep, np, bs, dpick(g0, vp), p)
