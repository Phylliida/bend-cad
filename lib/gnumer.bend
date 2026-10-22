# bend-cad: lib/numer.bend's proposer (dyadic elimination, Newton, Y, the
# radius search, the plan) written once over any computing numbers K
# (spec/knum.bend) with the proposer's other operations W (lib/pops.bend:
# rounding, the rare operations, the conversions with S.D). Function by
# function it mirrors numer.bend, with S.D's operations as K's and numer's
# constants sent through W's ofd; numer's functions that compute with no
# numbers are used as they are. With laws relating K to KI.dnum(), it
# returns exactly numer's plan sent through the map (lib/gnumerpf.bend:
# plan_t), so nothing numer.bend's proofs say is reopened. At word dyadics
# (lib/wnum.bend: wnum, wops) it is the fast proposer (PLAN-sk13w W4).

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/knum.bend as N
import ./certdef.bend as C
import ./karith.bend as KA
import ./cert.bend as CK
import ./plan.bend as PL
import ./struct.bend as ST
import ./numer.bend as NU
import ./pops.bend as PO

# Constants and comparisons
# -------------------------

def dzero(~K: N.Num, ~W: PO.POps<K>) -> N.NC(K):
  PO.ofd(K, W, NU.dzero())

def done(~K: N.Num, ~W: PO.POps<K>) -> N.NC(K):
  PO.ofd(K, W, NU.done())

def dmax.go(~K: N.Num, ~W: PO.POps<K>, c: Cmp, a: N.NC(K), b: N.NC(K)) -> N.NC(K):
  match c:
    case LT{}:
      b
    case EQ{}:
      a
    case GT{}:
      a

def dmax(~K: N.Num, ~W: PO.POps<K>, +a: N.NC(K), +b: N.NC(K)) -> N.NC(K):
  dmax.go(~K, ~W, N.ncmp(K, a, b), a, b)

def dvmax(~K: N.Num, ~W: PO.POps<K>, xs: N.KVec(~K)) -> N.NC(K):
  match xs:
    case Nil{}:
      dzero(~K, ~W)
    case Con{x, t}:
      dmax(~K, ~W, x, dvmax(~K, ~W, t))

def dreps(~K: N.Num, ~W: PO.POps<K>, n: Nat, +x: N.NC(K)) -> N.KVec(~K):
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{x, dreps(~K, ~W, m, x)}

def dabs(~K: N.Num, ~W: PO.POps<K>, +x: N.NC(K)) -> N.NC(K):
  KA.kabs(~K, x)

# Dyadic elimination
# ------------------

def dsadd(~K: N.Num, ~W: PO.POps<K>, +w: Nat, +a: N.NC(K), +b: N.NC(K)) -> N.NC(K):
  PO.sig(K, W, N.nadd(K, a, b), w)

def dsmul(~K: N.Num, ~W: PO.POps<K>, +w: Nat, +a: N.NC(K), +b: N.NC(K)) -> N.NC(K):
  PO.sig(K, W, N.nmul(K, a, b), w)

def dget(~K: N.Num, ~W: PO.POps<K>, xs: N.KVec(~K), k: Nat) -> N.NC(K):
  match xs k:
    case Nil{} k:
      dzero(~K, ~W)
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      dget(~K, ~W, t, j)

def drow(~K: N.Num, ~W: PO.POps<K>, xs: N.KMat(~K), k: Nat) -> N.KVec(~K):
  match xs k:
    case Nil{} k:
      Nil{}
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      drow(~K, ~W, t, j)

def dset(~K: N.Num, ~W: PO.POps<K>, xs: N.KMat(~K), k: Nat, +r: N.KVec(~K)) -> N.KMat(~K):
  match xs k:
    case Nil{} k:
      Nil{}
    case Con{h, t} 0n:
      Con{r, t}
    case Con{h, t} 1n+j:
      Con{h, dset(~K, ~W, t, j, r)}

def dscale(~K: N.Num, ~W: PO.POps<K>, +w: Nat, +c: N.NC(K), xs: N.KVec(~K)) -> N.KVec(~K):
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{dsmul(~K, ~W, w, c, x), dscale(~K, ~W, w, c, t)}

# xs - c ys
def daxpy(~K: N.Num, ~W: PO.POps<K>, +w: Nat, xs: N.KVec(~K), +c: N.NC(K), ys: N.KVec(~K)) -> N.KVec(~K):
  match xs ys:
    case Nil{} ys:
      Nil{}
    case Con{x, t} Nil{}:
      Con{x, t}
    case Con{+x, t} Con{+y, u}:
      Con{dsadd(~K, ~W, w, x, N.nneg(K, dsmul(~K, ~W, w, c, y))), daxpy(~K, ~W, w, t, c, u)}

def dzeros(~K: N.Num, ~W: PO.POps<K>, n: Nat) -> N.KVec(~K):
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{dzero(~K, ~W), dzeros(~K, ~W, m)}

def dunit(~K: N.Num, ~W: PO.POps<K>, n: Nat, +k: Nat) -> N.KVec(~K):
  match n k:
    case 0n k:
      Nil{}
    case 1n+m 0n:
      Con{done(~K, ~W), dzeros(~K, ~W, m)}
    case 1n+m 1n+j:
      Con{dzero(~K, ~W), dunit(~K, ~W, m, j)}

def dapp(~K: N.Num, ~W: PO.POps<K>, xs: N.KVec(~K), ys: N.KVec(~K)) -> N.KVec(~K):
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, dapp(~K, ~W, t, ys)}

def daugment(~K: N.Num, ~W: PO.POps<K>, a: N.KMat(~K), +n: Nat, +k: Nat) -> N.KMat(~K):
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{dapp(~K, ~W, r, dunit(~K, ~W, n, k)), daugment(~K, ~W, t, n, 1n+k)}

def ddrop(~K: N.Num, ~W: PO.POps<K>, n: Nat, xs: N.KVec(~K)) -> N.KVec(~K):
  match n xs:
    case 0n xs:
      xs
    case 1n+m Nil{}:
      Nil{}
    case 1n+m Con{h, t}:
      ddrop(~K, ~W, m, t)

def dpivot.bx(~K: N.Num, ~W: PO.POps<K>, le: Bool, +bx: N.NC(K), +x: N.NC(K)) -> N.NC(K):
  match le:
    case False{}:
      bx
    case True{}:
      dmax(~K, ~W, bx, x)

# the row at or after k (counting from i) whose entry in column c is
# largest in size (None: all zero); bx is the best size so far
def dpivot(~K: N.Num, ~W: PO.POps<K>, rows: N.KMat(~K), +c: Nat, +k: Nat, +i: Nat, best: Maybe<&2, Nat>, +bx: N.NC(K)) -> Maybe<&2, Nat>:
  match rows:
    case Nil{}:
      best
    case Con{+r, t}:
      dpivot(~K, ~W, t, c, k, 1n+i, NU.dpivot.best(KA.natle(k, i), N.ncmp(K, dabs(~K, ~W, dget(~K, ~W, r, c)), bx), i, best), dpivot.bx(~K, ~W, KA.natle(k, i), bx, dabs(~K, ~W, dget(~K, ~W, r, c))))

def dswap(~K: N.Num, ~W: PO.POps<K>, +rows: N.KMat(~K), +a: Nat, +b: Nat) -> N.KMat(~K):
  dset(~K, ~W, dset(~K, ~W, rows, a, drow(~K, ~W, rows, b)), b, drow(~K, ~W, rows, a))

def dclear.ax(~K: N.Num, ~W: PO.POps<K>, +w: Nat, +r: N.KVec(~K), +p: N.KVec(~K), +c: Nat) -> N.KVec(~K):
  daxpy(~K, ~W, w, r, dget(~K, ~W, r, c), p)

def dclear.go(~K: N.Num, ~W: PO.POps<K>, b: Bool, +w: Nat, +r: N.KVec(~K), +p: N.KVec(~K), +c: Nat) -> N.KVec(~K):
  match b:
    case True{}:
      p
    case False{}:
      dclear.ax(~K, ~W, w, r, p, c)

def dclear(~K: N.Num, ~W: PO.POps<K>, rows: N.KMat(~K), +w: Nat, +p: N.KVec(~K), +c: Nat, +i: Nat) -> N.KMat(~K):
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{dclear.go(~K, ~W, KA.nateq(i, c), w, r, p, c), dclear(~K, ~W, t, w, p, c, 1n+i)}

def delim(~K: N.Num, ~W: PO.POps<K>, +w: Nat, +rows: N.KMat(~K), +c: Nat) -> N.KMat(~K):
  dclear(~K, ~W, rows, w, dscale(~K, ~W, w, PO.sdiv(K, W, w, done(~K, ~W), dget(~K, ~W, drow(~K, ~W, rows, c), c)), drow(~K, ~W, rows, c)), c, 0n)

def dgj(~K: N.Num, ~W: PO.POps<K>, k: Nat, +w: Nat, +c: Nat, piv: Maybe<&2, Nat>, +rows: N.KMat(~K)) -> Maybe<&2, N.KMat(~K)>:
  match k piv:
    case 0n piv:
      Some{rows}
    case 1n+m None{}:
      None{}
    case 1n+m Some{r}:
      +rows2 = delim(~K, ~W, w, dswap(~K, ~W, rows, c, r), c)
      dgj(~K, ~W, m, w, 1n+c, dpivot(~K, ~W, rows2, 1n+c, 1n+c, 0n, None{}, dzero(~K, ~W)), rows2)

def drights(~K: N.Num, ~W: PO.POps<K>, +n: Nat, rows: N.KMat(~K)) -> N.KMat(~K):
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{ddrop(~K, ~W, n, r), drights(~K, ~W, n, t)}

def dinv.of(~K: N.Num, ~W: PO.POps<K>, +n: Nat, m: Maybe<&2, N.KMat(~K)>) -> Maybe<&2, N.KMat(~K)>:
  match m:
    case None{}:
      None{}
    case Some{rows}:
      Some{drights(~K, ~W, n, rows)}

def dgj0(~K: N.Num, ~W: PO.POps<K>, +n: Nat, +w: Nat, +rows: N.KMat(~K)) -> Maybe<&2, N.KMat(~K)>:
  dgj(~K, ~W, n, w, 0n, dpivot(~K, ~W, rows, 0n, 0n, 0n, None{}, dzero(~K, ~W)), rows)

# an approximate J^-1 (None when elimination meets an all-zero column)
def dinverse(~K: N.Num, ~W: PO.POps<K>, +n: Nat, +w: Nat, a: N.KMat(~K)) -> Maybe<&2, N.KMat(~K)>:
  dinv.of(~K, ~W, n, dgj0(~K, ~W, n, w, daugment(~K, ~W, a, n, 0n)))

def ddot(~K: N.Num, ~W: PO.POps<K>, xs: N.KVec(~K), ys: N.KVec(~K)) -> N.NC(K):
  match xs ys:
    case Nil{} ys:
      dzero(~K, ~W)
    case Con{x, t} Nil{}:
      dzero(~K, ~W)
    case Con{+x, t} Con{+y, u}:
      N.nadd(K, N.nmul(K, x, y), ddot(~K, ~W, t, u))

def dmatvec(~K: N.Num, ~W: PO.POps<K>, a: N.KMat(~K), +v: N.KVec(~K)) -> N.KVec(~K):
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{ddot(~K, ~W, r, v), dmatvec(~K, ~W, t, v)}

# A block at precision P
# ----------------------

def jac(~K: N.Num, ~W: PO.POps<K>, +eqs: List<&2, E.QExpr>, +n: Nat, +env: N.KVec(~K)) -> N.KMat(~K):
  CK.mcenters(~K, CK.srows(~K, CK.zipb(~K, env, Nil{}), n, 0n, eqs))

def vals(~K: N.Num, ~W: PO.POps<K>, +eqs: List<&2, E.QExpr>, +env: N.KVec(~K)) -> N.KVec(~K):
  CK.kvals(~K, env, eqs)

# y - d rounded to P fractional bits
def nstep.round(~K: N.Num, ~W: PO.POps<K>, ys: N.KVec(~K), ds: N.KVec(~K), +p: Nat) -> N.KVec(~K):
  match ys ds:
    case Nil{} ds:
      Nil{}
    case Con{+y, yt} Nil{}:
      Con{PO.round(K, W, y, p), nstep.round(~K, ~W, yt, Nil{}, p)}
    case Con{+y, yt} Con{+d, dt}:
      Con{PO.round(K, W, KA.ksub(~K, y, d), p), nstep.round(~K, ~W, yt, dt, p)}

def nstep.of(~K: N.Num, ~W: PO.POps<K>, +ys: N.KVec(~K), m: Maybe<&2, N.KMat(~K)>, +f: N.KVec(~K), +p: Nat) -> Maybe<&2, N.KVec(~K)>:
  match m:
    case None{}:
      None{}
    case Some{inv}:
      Some{nstep.round(~K, ~W, ys, dmatvec(~K, ~W, inv, f), p)}

# one Newton step (None: elimination met an all-zero column)
def nstep(~K: N.Num, ~W: PO.POps<K>, +eqs: List<&2, E.QExpr>, +n: Nat, +pc: N.KVec(~K), +p: Nat, +ys: N.KVec(~K)) -> Maybe<&2, N.KVec(~K)>:
  nstep.of(~K, ~W, ys, dinverse(~K, ~W, n, NU.wbits(p), jac(~K, ~W, eqs, n, dapp(~K, ~W, ys, pc))), vals(~K, ~W, eqs, dapp(~K, ~W, ys, pc)), p)

# a Newton step's outcome: moved, settled, or singular
type GNS<-K: N.Num> is Data:
  GMore{y: List<&2, N.NC(K)>}
  GDone{y: List<&2, N.NC(K)>}
  GSing{}

def classify.go(~K: N.Num, ~W: PO.POps<K>, same: Bool, y2: N.KVec(~K)) -> GNS<K>:
  match same:
    case True{}:
      GDone{y2}
    case False{}:
      GMore{y2}

# every entry of xs and ys differs by at most t
def dclose(~K: N.Num, ~W: PO.POps<K>, xs: N.KVec(~K), ys: N.KVec(~K), +t: N.NC(K)) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, yt}:
      False{}
    case Con{x, xt} Nil{}:
      False{}
    case Con{+x, xt} Con{+y, yt}:
      KA.band(KA.kle(~K, dabs(~K, ~W, KA.ksub(~K, x, y)), t), dclose(~K, ~W, xt, yt, t))

def classify.far(~K: N.Num, ~W: PO.POps<K>, near: Bool, +ys: N.KVec(~K), +p: Nat, +y2: N.KVec(~K)) -> GNS<K>:
  match near:
    case False{}:
      GSing{}
    case True{}:
      classify.go(~K, ~W, dclose(~K, ~W, ys, y2, PO.ofd(K, W, S.D{S.Zpos{S.XH{}}, Nat.sub(p, 2n)})), y2)

def classify(~K: N.Num, ~W: PO.POps<K>, +ys: N.KVec(~K), +p: Nat, m: Maybe<&2, N.KVec(~K)>) -> GNS<K>:
  match m:
    case None{}:
      GSing{}
    case Some{+y2}:
      classify.far(~K, ~W, dclose(~K, ~W, ys, y2, PO.ofd(K, W, NU.far())), ys, p, y2)

# at most k steps
def newton(~K: N.Num, ~W: PO.POps<K>, k: Nat, +eqs: List<&2, E.QExpr>, +n: Nat, +pc: N.KVec(~K), +p: Nat, st: GNS<K>) -> Maybe<&2, N.KVec(~K)>:
  match k st:
    case k GSing{}:
      None{}
    case k GDone{y}:
      Some{y}
    case 0n GMore{y}:
      None{}
    case 1n+j GMore{+y}:
      newton(~K, ~W, j, eqs, n, pc, p, classify(~K, ~W, y, p, nstep(~K, ~W, eqs, n, pc, p, y)))

def ysigv(~K: N.Num, ~W: PO.POps<K>, +b: Nat, xs: N.KVec(~K)) -> N.KVec(~K):
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{PO.sig(K, W, x, b), ysigv(~K, ~W, b, t)}

def ysig(~K: N.Num, ~W: PO.POps<K>, +b: Nat, a: N.KMat(~K)) -> N.KMat(~K):
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{ysigv(~K, ~W, b, r), ysig(~K, ~W, b, t)}

def mkcert(~K: N.Num, ~W: PO.POps<K>, +n: Nat, yc: N.KVec(~K), +r: N.NC(K), ym: N.KMat(~K), pc: N.KVec(~K), pr: N.KVec(~K)) -> C.Cert<K>:
  C.Cert{yc, dreps(~K, ~W, n, r), PO.ofd(K, W, NU.half()), ym, pc, pr}

def okr(~K: N.Num, ~W: PO.POps<K>, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +r: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> Bool:
  CK.check(~K, C.Block{eqs, n}, mkcert(~K, ~W, n, yc, r, ym, pc, pr))

# r (17/16), at about 8 significant bits
def grow(~K: N.Num, ~W: PO.POps<K>, +r: N.NC(K)) -> N.NC(K):
  PO.sigup(K, W, N.nmul(K, r, PO.ofd(K, W, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XH{}}}}}}, 4n})), 8n)

# the first radius r (17/16)^i, i < k, that the block checker accepts
def rsearch(~K: N.Num, ~W: PO.POps<K>, k: Nat, ok: Bool, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +r: N.NC(K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> Maybe<&2, N.NC(K)>:
  match k ok:
    case k True{}:
      Some{r}
    case 0n False{}:
      None{}
    case 1n+j False{}:
      rsearch(~K, ~W, j, okr(~K, ~W, eqs, n, yc, grow(~K, ~W, r), ym, pc, pr), eqs, n, yc, grow(~K, ~W, r), ym, pc, pr)

# the largest entry of |Y f| + |Y| (|J0z| + Dz) rho, times 65/64, plus e,
# at about 8 bits
def r0(~K: N.Num, ~W: PO.POps<K>, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +e: N.NC(K)) -> N.NC(K):
  PO.sigup(K, W, N.nadd(K, N.nmul(K, dvmax(~K, ~W, CK.svec(~K, eqs, n, yc, Nil{}, ym, pc, pr)), PO.ofd(K, W, S.D{S.Zpos{S.XI{S.XO{S.XO{S.XO{S.XO{S.XO{S.XH{}}}}}}}}, 6n})), e), 8n)

# a block's outcome: a certificate; no radius found; or Newton did not
# settle, or the Jacobian looked singular
type GBR<-K: N.Num> is Data:
  GBOk{c: C.Cert<K>}
  GBRetry{}
  GBStop{}

def block.r(~K: N.Num, ~W: PO.POps<K>, m: Maybe<&2, N.NC(K)>, +n: Nat, +yc: N.KVec(~K), +ym: N.KMat(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> GBR<K>:
  match m:
    case None{}:
      GBRetry{}
    case Some{+r}:
      GBOk{mkcert(~K, ~W, n, yc, r, ym, pc, pr)}

def block.ym(~K: N.Num, ~W: PO.POps<K>, +ym: N.KMat(~K), +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +pc: N.KVec(~K), +pr: N.KVec(~K), +e: N.NC(K)) -> GBR<K>:
  block.r(~K, ~W, rsearch(~K, ~W, 64n, okr(~K, ~W, eqs, n, yc, r0(~K, ~W, eqs, n, yc, ym, pc, pr, e), ym, pc, pr), eqs, n, yc, r0(~K, ~W, eqs, n, yc, ym, pc, pr, e), ym, pc, pr), n, yc, ym, pc, pr)

def block.y2(~K: N.Num, ~W: PO.POps<K>, m: Maybe<&2, N.KMat(~K)>, +p: Nat, +eqs: List<&2, E.QExpr>, +n: Nat, +yc: N.KVec(~K), +pc: N.KVec(~K), +pr: N.KVec(~K)) -> GBR<K>:
  match m:
    case None{}:
      GBStop{}
    case Some{inv}:
      block.ym(~K, ~W, ysig(~K, ~W, Nat.div(p, 2n), inv), eqs, n, yc, pc, pr, PO.ofd(K, W, NU.eta(p)))

def block.y(~K: N.Num, ~W: PO.POps<K>, m: Maybe<&2, N.KVec(~K)>, +p: Nat, +eqs: List<&2, E.QExpr>, +n: Nat, +pc: N.KVec(~K), +pr: N.KVec(~K)) -> GBR<K>:
  match m:
    case None{}:
      GBStop{}
    case Some{+yc}:
      block.y2(~K, ~W, dinverse(~K, ~W, n, NU.wbits(p), jac(~K, ~W, eqs, n, dapp(~K, ~W, yc, pc))), p, eqs, n, yc, pc, pr)

# a block's certificate at precision p, from the drawing's values y0
def block(~K: N.Num, ~W: PO.POps<K>, +eqs: List<&2, E.QExpr>, +n: Nat, +pc: N.KVec(~K), +pr: N.KVec(~K), y0: N.KVec(~K), +p: Nat) -> GBR<K>:
  block.y(~K, ~W, newton(~K, ~W, 40n, eqs, n, pc, p, GMore{y0}), p, eqs, n, pc, pr)

# A plan at precision P
# ---------------------

def dlook(~K: N.Num, ~W: PO.POps<K>, xs: N.KVec(~K), k: Nat) -> N.NC(K):
  match xs k:
    case Nil{} k:
      dzero(~K, ~W)
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      dlook(~K, ~W, t, j)

def dpick(~K: N.Num, ~W: PO.POps<K>, +xs: N.KVec(~K), ks: List<&2, Nat>) -> N.KVec(~K):
  match ks:
    case Nil{}:
      Nil{}
    case Con{k, t}:
      Con{dlook(~K, ~W, xs, k), dpick(~K, ~W, xs, t)}

def dtake(~K: N.Num, ~W: PO.POps<K>, n: Nat, xs: N.KVec(~K)) -> N.KVec(~K):
  match n xs:
    case 0n xs:
      Nil{}
    case 1n+m Nil{}:
      Nil{}
    case 1n+m Con{h, t}:
      Con{h, dtake(~K, ~W, m, t)}

# the first block's outcome (stop for no block)
def bcert.n(~K: N.Num, ~W: PO.POps<K>, +n: Nat, +pars: List<&2, Nat>, +sys: List<&2, E.QExpr>, +g0b: N.KVec(~K), +p: Nat, +o: Nat, +gc: N.KVec(~K), +gr: N.KVec(~K)) -> GBR<K>:
  block(~K, ~W, PL.renames(o, n, pars, PL.takeq(n, sys)), n, dpick(~K, ~W, gc, pars), dpick(~K, ~W, gr, pars), dtake(~K, ~W, n, ddrop(~K, ~W, o, g0b)), p)

def bcert(~K: N.Num, ~W: PO.POps<K>, bs: List<&2, ST.SkB>, +sys: List<&2, E.QExpr>, +g0b: N.KVec(~K), +p: Nat, +o: Nat, +gc: N.KVec(~K), +gr: N.KVec(~K)) -> GBR<K>:
  match bs:
    case Nil{}:
      GBStop{}
    case Con{ST.SkB{es, vs, +pars}, t}:
      bcert.n(~K, ~W, ST.len(es), pars, sys, g0b, p, o, gc, gr)

type GPB<-K: N.Num> is Data:
  GPB{bs: List<&2, PL.PBlock<K>>, gc: List<&2, N.NC(K)>, gr: List<&2, N.NC(K)>}

type GPBR<-K: N.Num> is Data:
  GPBOk{pb: GPB<K>}
  GPBRetry{}
  GPBStop{}

def revpb.go(~K: N.Num, ~W: PO.POps<K>, xs: List<&2, PL.PBlock<K>>, acc: List<&2, PL.PBlock<K>>) -> List<&2, PL.PBlock<K>>:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      revpb.go(~K, ~W, t, Con{h, acc})

def cert.yc(~K: N.Num, ~W: PO.POps<K>, c: C.Cert<K>) -> N.KVec(~K):
  match c:
    case C.Cert{yc, yr, q, ym, pc, pr}:
      yc

def cert.yr(~K: N.Num, ~W: PO.POps<K>, c: C.Cert<K>) -> N.KVec(~K):
  match c:
    case C.Cert{yc, yr, q, ym, pc, pr}:
      yr

# the blocks in turn (cur: the first block's certificate)
def pblocks(~K: N.Num, ~W: PO.POps<K>, bs: List<&2, ST.SkB>, cur: GBR<K>, +sys: List<&2, E.QExpr>, +g0b: N.KVec(~K), +p: Nat, +o: Nat, +gc: N.KVec(~K), +gr: N.KVec(~K), acc: List<&2, PL.PBlock<K>>) -> GPBR<K>:
  match bs cur:
    case Nil{} cur:
      GPBOk{GPB{revpb.go(~K, ~W, acc, Nil{}), gc, gr}}
    case Con{b, t} GBRetry{}:
      GPBRetry{}
    case Con{b, t} GBStop{}:
      GPBStop{}
    case Con{ST.SkB{es, vs, +pars}, +t} GBOk{+c}:
      +n = ST.len(es)
      +sys2 = PL.dropq(n, sys)
      +gc2 = dapp(~K, ~W, gc, cert.yc(~K, ~W, c))
      +gr2 = dapp(~K, ~W, gr, dtake(~K, ~W, n, cert.yr(~K, ~W, c)))
      pblocks(~K, ~W, t, bcert(~K, ~W, t, sys2, g0b, p, Nat.add(o, n), gc2, gr2), sys2, g0b, p, Nat.add(o, n), gc2, gr2, Con{PL.PBlock{n, pars, c}, acc})

# the box in the system's own order: variable v at its position in vp
def unperm(~K: N.Num, ~W: PO.POps<K>, n: Nat, +k: Nat, +xs: N.KVec(~K), +vp: List<&2, Nat>) -> N.KVec(~K):
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{dlook(~K, ~W, xs, ST.pos(k, vp)), unperm(~K, ~W, m, 1n+k, xs, vp)}

# a certified plan for the system es over nv variables, and its box
type GNP<-K: N.Num> is Data:
  GNP{plan: PL.Plan<K>, gc: List<&2, N.NC(K)>, gr: List<&2, N.NC(K)>}

# a plan, or retry at a higher precision, or stop
type GPR<-K: N.Num> is Data:
  GPOk{np: GNP<K>}
  GPRetry{}
  GPStop{}

def plan.fin(~K: N.Num, ~W: PO.POps<K>, +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +nv: Nat, m: GPBR<K>) -> GPR<K>:
  match m:
    case GPBRetry{}:
      GPRetry{}
    case GPBStop{}:
      GPStop{}
    case GPBOk{GPB{bs, +gc, +gr}}:
      GPOk{GNP{PL.Plan{vp, ep, np, bs}, unperm(~K, ~W, nv, 0n, gc, vp), unperm(~K, ~W, nv, 0n, gr, vp)}}

def plan.go(~K: N.Num, ~W: PO.POps<K>, +es: List<&2, E.QExpr>, +nv: Nat, +vp: List<&2, Nat>, +ep: List<&2, Nat>, +np: Nat, +bs: List<&2, ST.SkB>, +g0b: N.KVec(~K), +p: Nat) -> GPR<K>:
  plan.fin(~K, ~W, vp, ep, np, nv, pblocks(~K, ~W, bs, bcert(~K, ~W, bs, PL.reorder(vp, es, ep), g0b, p, np, dtake(~K, ~W, np, g0b), dreps(~K, ~W, np, dzero(~K, ~W))), PL.reorder(vp, es, ep), g0b, p, np, dtake(~K, ~W, np, g0b), dreps(~K, ~W, np, dzero(~K, ~W)), Nil{}))

# a plan for the system es over nv variables from the drawing g0 (one
# value per variable, in K) at precision p
def plan(~K: N.Num, ~W: PO.POps<K>, +es: List<&2, E.QExpr>, +nv: Nat, sk: ST.Skel, +g0: N.KVec(~K), +p: Nat) -> GPR<K>:
  match sk:
    case ST.Skel{+vp, +ep, +np, +bs, red}:
      plan.go(~K, ~W, es, nv, vp, ep, np, bs, dpick(~K, ~W, g0, vp), p)
