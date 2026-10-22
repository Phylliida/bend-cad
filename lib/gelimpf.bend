# bend-cad: lib/gnumer.bend's elimination (the approximate inverse) and its
# list helpers return exactly lib/numer.bend's results sent through the map
# h : KI.dnum() -> K of the proposer's laws R (lib/pops.bend): for every S.D
# input, GN.f on the images is the image of NU.f. Untrusted; for the fast
# proposer (PLAN-sk13w W4).

# Generated from tools/drafts/gelimpf.draft by tools/expand.py; edit the
# draft.


import Base
import ../spec/num.bend as S
import ../spec/knum.bend as N
import ./kinst.bend as KI
import ./karith.bend as KA
import ./khom.bend as KH
import ./khompf.bend as KP
import ./numer.bend as NU
import ./gnumer.bend as GN
import ./gmap.bend as GM
import ./pops.bend as PO

# Constants and comparisons
# -------------------------

def dzero_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>) -> {GN.dzero(~K, ~W) == KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.dzero()) : N.NC(K)}:
  PO.l_ofd(K, W, R)(NU.dzero())

def done_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>) -> {GN.done(~K, ~W) == KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.done()) : N.NC(K)}:
  PO.l_ofd(K, W, R)(NU.done())

def dmax_go_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, c: Cmp, +a: S.D, +b: S.D) -> {GN.dmax.go(~K, ~W, c, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), a), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), b)) == KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.dmax.go(c, a, b)) : N.NC(K)}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def dmax_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +a: S.D, +b: S.D) -> {GN.dmax(~K, ~W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), a), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), b)) == KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.dmax(a, b)) : N.NC(K)}:
  %KH.h_cmp(KI.dnum(), K, PO.hom(K, W, R))(a, b) : {GN.dmax.go(~K, ~W, N.ncmp(K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), a), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), b)), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), a), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), b)) == KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.dmax.go(_, a, b)) : N.NC(K)}
  dmax_go_t(~K, ~W, ~R, N.ncmp(K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), a), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), b)), a, b)

def dvmax_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, xs: List<&2, S.D>) -> {GN.dvmax(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs)) == KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.dvmax(xs)) : N.NC(K)}:
  match xs:
    case Nil{}:
      dzero_t(~K, ~W, ~R)
    case Con{+x, +t}:
      %dmax_t(~K, ~W, ~R, x, NU.dvmax(t)) : {GN.dmax(~K, ~W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), GN.dvmax(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t))) == _ : N.NC(K)}
      %dvmax_t(~K, ~W, ~R, t) : {GN.dmax(~K, ~W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), GN.dvmax(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t))) == GN.dmax(~K, ~W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), _) : N.NC(K)}
      {==}

def dreps_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, n: Nat, +x: S.D) -> {GN.dreps(~K, ~W, n, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x)) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dreps(n, x)) : N.KVec(~K)}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      %dreps_t(~K, ~W, ~R, m, x) : {Con{KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), GN.dreps(~K, ~W, m, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x))} == Con{KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), _} : N.KVec(~K)}
      {==}

def dabs_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +x: S.D) -> {GN.dabs(~K, ~W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x)) == KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.dabs(x)) : N.NC(K)}:
  KP.kabs_h(~KI.dnum(), ~K, ~PO.hom(K, W, R), x)

# Arithmetic at w significant bits
# --------------------------------

def dsadd_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +w: Nat, +a: S.D, +b: S.D) -> {GN.dsadd(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), a), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), b)) == KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.dsadd(w, a, b)) : N.NC(K)}:
  %PO.l_sig(K, W, R)(N.nadd(KI.dnum(), a, b), w) : {PO.sig(K, W, N.nadd(K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), a), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), b)), w) == _ : N.NC(K)}
  %KH.h_add(KI.dnum(), K, PO.hom(K, W, R))(a, b) : {PO.sig(K, W, N.nadd(K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), a), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), b)), w) == PO.sig(K, W, _, w) : N.NC(K)}
  {==}

def dsmul_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +w: Nat, +a: S.D, +b: S.D) -> {GN.dsmul(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), a), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), b)) == KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.dsmul(w, a, b)) : N.NC(K)}:
  %PO.l_sig(K, W, R)(N.nmul(KI.dnum(), a, b), w) : {PO.sig(K, W, N.nmul(K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), a), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), b)), w) == _ : N.NC(K)}
  %KH.h_mul(KI.dnum(), K, PO.hom(K, W, R))(a, b) : {PO.sig(K, W, N.nmul(K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), a), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), b)), w) == PO.sig(K, W, _, w) : N.NC(K)}
  {==}

# Rows and entries
# ----------------

def dget_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, xs: List<&2, S.D>, k: Nat) -> {GN.dget(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), k) == KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.dget(xs, k)) : N.NC(K)}:
  match xs k:
    case Nil{} k:
      dzero_t(~K, ~W, ~R)
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+j:
      dget_t(~K, ~W, ~R, t, j)

def drow_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, xs: List<&2, List<&2, S.D>>, k: Nat) -> {GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), k) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.drow(xs, k)) : N.KVec(~K)}:
  match xs k:
    case Nil{} k:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+j:
      drow_t(~K, ~W, ~R, t, j)

def dset_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, xs: List<&2, List<&2, S.D>>, k: Nat, +r: List<&2, S.D>) -> {GN.dset(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), k, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r)) == KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dset(xs, k, r)) : N.KMat(~K)}:
  match xs k:
    case Nil{} k:
      {==}
    case Con{x, t} 0n:
      {==}
    case Con{+x, +t} 1n+j:
      %dset_t(~K, ~W, ~R, t, j, r) : {Con{KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), x), GN.dset(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), j, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r))} == Con{KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), x), _} : N.KMat(~K)}
      {==}

def dscale_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +w: Nat, +c: S.D, xs: List<&2, S.D>) -> {GN.dscale(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), c), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs)) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dscale(w, c, xs)) : N.KVec(~K)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %dsmul_t(~K, ~W, ~R, w, c, x) : {Con{GN.dsmul(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), c), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x)), GN.dscale(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), c), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t))} == Con{_, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dscale(w, c, t))} : N.KVec(~K)}
      %dscale_t(~K, ~W, ~R, w, c, t) : {Con{GN.dsmul(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), c), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x)), GN.dscale(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), c), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t))} == Con{GN.dsmul(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), c), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x)), _} : N.KVec(~K)}
      {==}


# xs - c ys
def daxpy_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +w: Nat, xs: List<&2, S.D>, +c: S.D, ys: List<&2, S.D>) -> {GN.daxpy(~K, ~W, w, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), c), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys)) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.daxpy(w, xs, c, ys)) : N.KVec(~K)}:
  match xs ys:
    case Nil{} ys:
      {==}
    case Con{x, t} Nil{}:
      {==}
    case Con{+x, +t} Con{+y, +u}:
      %dsadd_t(~K, ~W, ~R, w, x, S.D.neg(NU.dsmul(w, c, y))) : {Con{GN.dsadd(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), N.nneg(K, GN.dsmul(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), c), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y)))), GN.daxpy(~K, ~W, w, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), c), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), u))} == Con{_, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.daxpy(w, t, c, u))} : N.KVec(~K)}
      %KH.h_neg(KI.dnum(), K, PO.hom(K, W, R))(NU.dsmul(w, c, y)) : {Con{GN.dsadd(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), N.nneg(K, GN.dsmul(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), c), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y)))), GN.daxpy(~K, ~W, w, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), c), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), u))} == Con{GN.dsadd(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), _), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.daxpy(w, t, c, u))} : N.KVec(~K)}
      %dsmul_t(~K, ~W, ~R, w, c, y) : {Con{GN.dsadd(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), N.nneg(K, GN.dsmul(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), c), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y)))), GN.daxpy(~K, ~W, w, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), c), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), u))} == Con{GN.dsadd(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), N.nneg(K, _)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.daxpy(w, t, c, u))} : N.KVec(~K)}
      %daxpy_t(~K, ~W, ~R, w, t, c, u) : {Con{GN.dsadd(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), N.nneg(K, GN.dsmul(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), c), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y)))), GN.daxpy(~K, ~W, w, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), c), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), u))} == Con{GN.dsadd(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), N.nneg(K, GN.dsmul(~K, ~W, w, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), c), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y)))), _} : N.KVec(~K)}
      {==}

def dzeros_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, n: Nat) -> {GN.dzeros(~K, ~W, n) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dzeros(n)) : N.KVec(~K)}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      %dzero_t(~K, ~W, ~R) : {Con{GN.dzero(~K, ~W), GN.dzeros(~K, ~W, m)} == Con{_, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dzeros(m))} : N.KVec(~K)}
      %dzeros_t(~K, ~W, ~R, m) : {Con{GN.dzero(~K, ~W), GN.dzeros(~K, ~W, m)} == Con{GN.dzero(~K, ~W), _} : N.KVec(~K)}
      {==}

def dunit_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, n: Nat, +k: Nat) -> {GN.dunit(~K, ~W, n, k) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dunit(n, k)) : N.KVec(~K)}:
  match n k:
    case 0n k:
      {==}
    case 1n+m 0n:
      %done_t(~K, ~W, ~R) : {Con{GN.done(~K, ~W), GN.dzeros(~K, ~W, m)} == Con{_, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dzeros(m))} : N.KVec(~K)}
      %dzeros_t(~K, ~W, ~R, m) : {Con{GN.done(~K, ~W), GN.dzeros(~K, ~W, m)} == Con{GN.done(~K, ~W), _} : N.KVec(~K)}
      {==}
    case 1n+m 1n+j:
      %dzero_t(~K, ~W, ~R) : {Con{GN.dzero(~K, ~W), GN.dunit(~K, ~W, m, j)} == Con{_, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dunit(m, j))} : N.KVec(~K)}
      %dunit_t(~K, ~W, ~R, m, j) : {Con{GN.dzero(~K, ~W), GN.dunit(~K, ~W, m, j)} == Con{GN.dzero(~K, ~W), _} : N.KVec(~K)}
      {==}

def dapp_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, xs: List<&2, S.D>, +ys: List<&2, S.D>) -> {GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys)) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dapp(xs, ys)) : N.KVec(~K)}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %dapp_t(~K, ~W, ~R, t, ys) : {Con{KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys))} == Con{KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), _} : N.KVec(~K)}
      {==}

def daugment_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, a: List<&2, List<&2, S.D>>, +n: Nat, +k: Nat) -> {GN.daugment(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), a), n, k) == KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.daugment(a, n, k)) : N.KMat(~K)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      %dapp_t(~K, ~W, ~R, r, NU.dunit(n, k)) : {Con{GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), GN.dunit(~K, ~W, n, k)), GN.daugment(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), n, 1n+k)} == Con{_, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.daugment(t, n, 1n+k))} : N.KMat(~K)}
      %dunit_t(~K, ~W, ~R, n, k) : {Con{GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), GN.dunit(~K, ~W, n, k)), GN.daugment(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), n, 1n+k)} == Con{GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), _), KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.daugment(t, n, 1n+k))} : N.KMat(~K)}
      %daugment_t(~K, ~W, ~R, t, n, 1n+k) : {Con{GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), GN.dunit(~K, ~W, n, k)), GN.daugment(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), n, 1n+k)} == Con{GN.dapp(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), GN.dunit(~K, ~W, n, k)), _} : N.KMat(~K)}
      {==}

def ddrop_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, n: Nat, xs: List<&2, S.D>) -> {GN.ddrop(~K, ~W, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs)) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.ddrop(n, xs)) : N.KVec(~K)}:
  match n xs:
    case 0n xs:
      {==}
    case 1n+m Nil{}:
      {==}
    case 1n+m Con{x, t}:
      ddrop_t(~K, ~W, ~R, m, t)

# The pivot
# ---------

def dpivot_bx_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, le: Bool, +bx: S.D, +x: S.D) -> {GN.dpivot.bx(~K, ~W, le, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x)) == KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.dpivot.bx(le, bx, x)) : N.NC(K)}:
  match le:
    case False{}:
      {==}
    case True{}:
      dmax_t(~K, ~W, ~R, bx, x)


# the same pivot row: the comparisons are the same
def dpivot_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, rows: List<&2, List<&2, S.D>>, +c: Nat, +k: Nat, +i: Nat, best: Maybe<&2, Nat>, +bx: S.D) -> {GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c, k, i, best, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx)) == NU.dpivot(rows, c, k, i, best, bx) : Maybe<&2, Nat>}:
  match rows:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      %dpivot_t(~K, ~W, ~R, t, c, k, 1n+i, NU.dpivot.best(KA.natle(k, i), KI.dcmp(NU.dabs(NU.dget(r, c)), bx), i, best), NU.dpivot.bx(KA.natle(k, i), bx, NU.dabs(NU.dget(r, c)))) : {GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), c, k, 1n+i, NU.dpivot.best(KA.natle(k, i), N.ncmp(K, GN.dabs(~K, ~W, GN.dget(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), c)), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx)), i, best), GN.dpivot.bx(~K, ~W, KA.natle(k, i), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx), GN.dabs(~K, ~W, GN.dget(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), c)))) == _ : Maybe<&2, Nat>}
      %KH.h_cmp(KI.dnum(), K, PO.hom(K, W, R))(NU.dabs(NU.dget(r, c)), bx) : {GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), c, k, 1n+i, NU.dpivot.best(KA.natle(k, i), N.ncmp(K, GN.dabs(~K, ~W, GN.dget(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), c)), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx)), i, best), GN.dpivot.bx(~K, ~W, KA.natle(k, i), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx), GN.dabs(~K, ~W, GN.dget(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), c)))) == GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), c, k, 1n+i, NU.dpivot.best(KA.natle(k, i), _, i, best), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.dpivot.bx(KA.natle(k, i), bx, NU.dabs(NU.dget(r, c))))) : Maybe<&2, Nat>}
      %dpivot_bx_t(~K, ~W, ~R, KA.natle(k, i), bx, NU.dabs(NU.dget(r, c))) : {GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), c, k, 1n+i, NU.dpivot.best(KA.natle(k, i), N.ncmp(K, GN.dabs(~K, ~W, GN.dget(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), c)), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx)), i, best), GN.dpivot.bx(~K, ~W, KA.natle(k, i), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx), GN.dabs(~K, ~W, GN.dget(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), c)))) == GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), c, k, 1n+i, NU.dpivot.best(KA.natle(k, i), N.ncmp(K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.dabs(NU.dget(r, c))), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx)), i, best), _) : Maybe<&2, Nat>}
      %dabs_t(~K, ~W, ~R, NU.dget(r, c)) : {GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), c, k, 1n+i, NU.dpivot.best(KA.natle(k, i), N.ncmp(K, GN.dabs(~K, ~W, GN.dget(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), c)), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx)), i, best), GN.dpivot.bx(~K, ~W, KA.natle(k, i), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx), GN.dabs(~K, ~W, GN.dget(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), c)))) == GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), c, k, 1n+i, NU.dpivot.best(KA.natle(k, i), N.ncmp(K, _, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx)), i, best), GN.dpivot.bx(~K, ~W, KA.natle(k, i), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.dabs(NU.dget(r, c))))) : Maybe<&2, Nat>}
      %dabs_t(~K, ~W, ~R, NU.dget(r, c)) : {GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), c, k, 1n+i, NU.dpivot.best(KA.natle(k, i), N.ncmp(K, GN.dabs(~K, ~W, GN.dget(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), c)), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx)), i, best), GN.dpivot.bx(~K, ~W, KA.natle(k, i), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx), GN.dabs(~K, ~W, GN.dget(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), c)))) == GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), c, k, 1n+i, NU.dpivot.best(KA.natle(k, i), N.ncmp(K, GN.dabs(~K, ~W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.dget(r, c))), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx)), i, best), GN.dpivot.bx(~K, ~W, KA.natle(k, i), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx), _)) : Maybe<&2, Nat>}
      %dget_t(~K, ~W, ~R, r, c) : {GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), c, k, 1n+i, NU.dpivot.best(KA.natle(k, i), N.ncmp(K, GN.dabs(~K, ~W, GN.dget(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), c)), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx)), i, best), GN.dpivot.bx(~K, ~W, KA.natle(k, i), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx), GN.dabs(~K, ~W, GN.dget(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), c)))) == GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), c, k, 1n+i, NU.dpivot.best(KA.natle(k, i), N.ncmp(K, GN.dabs(~K, ~W, _), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx)), i, best), GN.dpivot.bx(~K, ~W, KA.natle(k, i), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx), GN.dabs(~K, ~W, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.dget(r, c))))) : Maybe<&2, Nat>}
      %dget_t(~K, ~W, ~R, r, c) : {GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), c, k, 1n+i, NU.dpivot.best(KA.natle(k, i), N.ncmp(K, GN.dabs(~K, ~W, GN.dget(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), c)), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx)), i, best), GN.dpivot.bx(~K, ~W, KA.natle(k, i), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx), GN.dabs(~K, ~W, GN.dget(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), c)))) == GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), c, k, 1n+i, NU.dpivot.best(KA.natle(k, i), N.ncmp(K, GN.dabs(~K, ~W, GN.dget(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), c)), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx)), i, best), GN.dpivot.bx(~K, ~W, KA.natle(k, i), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), bx), GN.dabs(~K, ~W, _))) : Maybe<&2, Nat>}
      {==}

# Elimination
# -----------

def dswap_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +rows: List<&2, List<&2, S.D>>, +a: Nat, +b: Nat) -> {GN.dswap(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), a, b) == KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dswap(rows, a, b)) : N.KMat(~K)}:
  %dset_t(~K, ~W, ~R, NU.dset(rows, a, NU.drow(rows, b)), b, NU.drow(rows, a)) : {GN.dset(~K, ~W, GN.dset(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), a, GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), b)), b, GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), a)) == _ : N.KMat(~K)}
  %dset_t(~K, ~W, ~R, rows, a, NU.drow(rows, b)) : {GN.dset(~K, ~W, GN.dset(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), a, GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), b)), b, GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), a)) == GN.dset(~K, ~W, _, b, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.drow(rows, a))) : N.KMat(~K)}
  %drow_t(~K, ~W, ~R, rows, b) : {GN.dset(~K, ~W, GN.dset(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), a, GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), b)), b, GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), a)) == GN.dset(~K, ~W, GN.dset(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), a, _), b, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.drow(rows, a))) : N.KMat(~K)}
  %drow_t(~K, ~W, ~R, rows, a) : {GN.dset(~K, ~W, GN.dset(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), a, GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), b)), b, GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), a)) == GN.dset(~K, ~W, GN.dset(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), a, GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), b)), b, _) : N.KMat(~K)}
  {==}

def dclear_ax_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +w: Nat, +r: List<&2, S.D>, +p: List<&2, S.D>, +c: Nat) -> {GN.dclear.ax(~K, ~W, w, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), p), c) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dclear.ax(w, r, p, c)) : N.KVec(~K)}:
  %daxpy_t(~K, ~W, ~R, w, r, NU.dget(r, c), p) : {GN.daxpy(~K, ~W, w, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), GN.dget(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), c), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)) == _ : N.KVec(~K)}
  %dget_t(~K, ~W, ~R, r, c) : {GN.daxpy(~K, ~W, w, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), GN.dget(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), c), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)) == GN.daxpy(~K, ~W, w, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), _, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), p)) : N.KVec(~K)}
  {==}

def dclear_go_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, b: Bool, +w: Nat, +r: List<&2, S.D>, +p: List<&2, S.D>, +c: Nat) -> {GN.dclear.go(~K, ~W, b, w, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), p), c) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dclear.go(b, w, r, p, c)) : N.KVec(~K)}:
  match b:
    case True{}:
      {==}
    case False{}:
      dclear_ax_t(~K, ~W, ~R, w, r, p, c)

def dclear_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, rows: List<&2, List<&2, S.D>>, +w: Nat, +p: List<&2, S.D>, +c: Nat, +i: Nat) -> {GN.dclear(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), w, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), p), c, i) == KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dclear(rows, w, p, c, i)) : N.KMat(~K)}:
  match rows:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      %dclear_go_t(~K, ~W, ~R, KA.nateq(i, c), w, r, p, c) : {Con{GN.dclear.go(~K, ~W, KA.nateq(i, c), w, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), p), c), GN.dclear(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), w, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), p), c, 1n+i)} == Con{_, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dclear(t, w, p, c, 1n+i))} : N.KMat(~K)}
      %dclear_t(~K, ~W, ~R, t, w, p, c, 1n+i) : {Con{GN.dclear.go(~K, ~W, KA.nateq(i, c), w, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), p), c), GN.dclear(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), w, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), p), c, 1n+i)} == Con{GN.dclear.go(~K, ~W, KA.nateq(i, c), w, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), p), c), _} : N.KMat(~K)}
      {==}


def delim_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +w: Nat, +rows: List<&2, List<&2, S.D>>, +c: Nat) -> {GN.delim(~K, ~W, w, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c) == KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.delim(w, rows, c)) : N.KMat(~K)}:
  %dclear_t(~K, ~W, ~R, rows, w, NU.dscale(w, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(rows, c), c)), NU.drow(rows, c)), c, 0n) : {GN.dclear(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), w, GN.dscale(~K, ~W, w, PO.sdiv(K, W, w, GN.done(~K, ~W), GN.dget(~K, ~W, GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c), c)), GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c)), c, 0n) == _ : N.KMat(~K)}
  %dscale_t(~K, ~W, ~R, w, NU.dsdiv(w, NU.done(), NU.dget(NU.drow(rows, c), c)), NU.drow(rows, c)) : {GN.dclear(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), w, GN.dscale(~K, ~W, w, PO.sdiv(K, W, w, GN.done(~K, ~W), GN.dget(~K, ~W, GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c), c)), GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c)), c, 0n) == GN.dclear(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), w, _, c, 0n) : N.KMat(~K)}
  %PO.l_sdiv(K, W, R)(w, NU.done(), NU.dget(NU.drow(rows, c), c)) : {GN.dclear(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), w, GN.dscale(~K, ~W, w, PO.sdiv(K, W, w, GN.done(~K, ~W), GN.dget(~K, ~W, GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c), c)), GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c)), c, 0n) == GN.dclear(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), w, GN.dscale(~K, ~W, w, _, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.drow(rows, c))), c, 0n) : N.KMat(~K)}
  %done_t(~K, ~W, ~R) : {GN.dclear(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), w, GN.dscale(~K, ~W, w, PO.sdiv(K, W, w, GN.done(~K, ~W), GN.dget(~K, ~W, GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c), c)), GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c)), c, 0n) == GN.dclear(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), w, GN.dscale(~K, ~W, w, PO.sdiv(K, W, w, _, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.dget(NU.drow(rows, c), c))), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.drow(rows, c))), c, 0n) : N.KMat(~K)}
  %dget_t(~K, ~W, ~R, NU.drow(rows, c), c) : {GN.dclear(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), w, GN.dscale(~K, ~W, w, PO.sdiv(K, W, w, GN.done(~K, ~W), GN.dget(~K, ~W, GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c), c)), GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c)), c, 0n) == GN.dclear(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), w, GN.dscale(~K, ~W, w, PO.sdiv(K, W, w, GN.done(~K, ~W), _), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.drow(rows, c))), c, 0n) : N.KMat(~K)}
  %drow_t(~K, ~W, ~R, rows, c) : {GN.dclear(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), w, GN.dscale(~K, ~W, w, PO.sdiv(K, W, w, GN.done(~K, ~W), GN.dget(~K, ~W, GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c), c)), GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c)), c, 0n) == GN.dclear(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), w, GN.dscale(~K, ~W, w, PO.sdiv(K, W, w, GN.done(~K, ~W), GN.dget(~K, ~W, _, c)), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.drow(rows, c))), c, 0n) : N.KMat(~K)}
  %drow_t(~K, ~W, ~R, rows, c) : {GN.dclear(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), w, GN.dscale(~K, ~W, w, PO.sdiv(K, W, w, GN.done(~K, ~W), GN.dget(~K, ~W, GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c), c)), GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c)), c, 0n) == GN.dclear(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), w, GN.dscale(~K, ~W, w, PO.sdiv(K, W, w, GN.done(~K, ~W), GN.dget(~K, ~W, GN.drow(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c), c)), _), c, 0n) : N.KMat(~K)}
  {==}


# the same pivots, so the same eliminations
def dgj_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, k: Nat, +w: Nat, +c: Nat, piv: Maybe<&2, Nat>, +rows: List<&2, List<&2, S.D>>) -> {GN.dgj(~K, ~W, k, w, c, piv, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows)) == GM.hmm(~K, ~PO.hom(K, W, R), NU.dgj(k, w, c, piv, rows)) : Maybe<&2, N.KMat(~K)>}:
  match k piv:
    case 0n piv:
      {==}
    case 1n+m None{}:
      {==}
    case 1n+m Some{+r}:
      %dgj_t(~K, ~W, ~R, m, w, 1n+c, NU.dpivot(NU.delim(w, NU.dswap(rows, c, r), c), 1n+c, 1n+c, 0n, None{}, NU.dzero()), NU.delim(w, NU.dswap(rows, c, r), c)) : {GN.dgj(~K, ~W, m, w, 1n+c, GN.dpivot(~K, ~W, GN.delim(~K, ~W, w, GN.dswap(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c, r), c), 1n+c, 1n+c, 0n, None{}, GN.dzero(~K, ~W)), GN.delim(~K, ~W, w, GN.dswap(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c, r), c)) == _ : Maybe<&2, N.KMat(~K)>}
      %dpivot_t(~K, ~W, ~R, NU.delim(w, NU.dswap(rows, c, r), c), 1n+c, 1n+c, 0n, None{}, NU.dzero()) : {GN.dgj(~K, ~W, m, w, 1n+c, GN.dpivot(~K, ~W, GN.delim(~K, ~W, w, GN.dswap(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c, r), c), 1n+c, 1n+c, 0n, None{}, GN.dzero(~K, ~W)), GN.delim(~K, ~W, w, GN.dswap(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c, r), c)) == GN.dgj(~K, ~W, m, w, 1n+c, _, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.delim(w, NU.dswap(rows, c, r), c))) : Maybe<&2, N.KMat(~K)>}
      %dzero_t(~K, ~W, ~R) : {GN.dgj(~K, ~W, m, w, 1n+c, GN.dpivot(~K, ~W, GN.delim(~K, ~W, w, GN.dswap(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c, r), c), 1n+c, 1n+c, 0n, None{}, GN.dzero(~K, ~W)), GN.delim(~K, ~W, w, GN.dswap(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c, r), c)) == GN.dgj(~K, ~W, m, w, 1n+c, GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.delim(w, NU.dswap(rows, c, r), c)), 1n+c, 1n+c, 0n, None{}, _), KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.delim(w, NU.dswap(rows, c, r), c))) : Maybe<&2, N.KMat(~K)>}
      %delim_t(~K, ~W, ~R, w, NU.dswap(rows, c, r), c) : {GN.dgj(~K, ~W, m, w, 1n+c, GN.dpivot(~K, ~W, GN.delim(~K, ~W, w, GN.dswap(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c, r), c), 1n+c, 1n+c, 0n, None{}, GN.dzero(~K, ~W)), GN.delim(~K, ~W, w, GN.dswap(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c, r), c)) == GN.dgj(~K, ~W, m, w, 1n+c, GN.dpivot(~K, ~W, _, 1n+c, 1n+c, 0n, None{}, GN.dzero(~K, ~W)), KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.delim(w, NU.dswap(rows, c, r), c))) : Maybe<&2, N.KMat(~K)>}
      %dswap_t(~K, ~W, ~R, rows, c, r) : {GN.dgj(~K, ~W, m, w, 1n+c, GN.dpivot(~K, ~W, GN.delim(~K, ~W, w, GN.dswap(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c, r), c), 1n+c, 1n+c, 0n, None{}, GN.dzero(~K, ~W)), GN.delim(~K, ~W, w, GN.dswap(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c, r), c)) == GN.dgj(~K, ~W, m, w, 1n+c, GN.dpivot(~K, ~W, GN.delim(~K, ~W, w, _, c), 1n+c, 1n+c, 0n, None{}, GN.dzero(~K, ~W)), KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.delim(w, NU.dswap(rows, c, r), c))) : Maybe<&2, N.KMat(~K)>}
      %delim_t(~K, ~W, ~R, w, NU.dswap(rows, c, r), c) : {GN.dgj(~K, ~W, m, w, 1n+c, GN.dpivot(~K, ~W, GN.delim(~K, ~W, w, GN.dswap(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c, r), c), 1n+c, 1n+c, 0n, None{}, GN.dzero(~K, ~W)), GN.delim(~K, ~W, w, GN.dswap(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c, r), c)) == GN.dgj(~K, ~W, m, w, 1n+c, GN.dpivot(~K, ~W, GN.delim(~K, ~W, w, GN.dswap(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c, r), c), 1n+c, 1n+c, 0n, None{}, GN.dzero(~K, ~W)), _) : Maybe<&2, N.KMat(~K)>}
      %dswap_t(~K, ~W, ~R, rows, c, r) : {GN.dgj(~K, ~W, m, w, 1n+c, GN.dpivot(~K, ~W, GN.delim(~K, ~W, w, GN.dswap(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c, r), c), 1n+c, 1n+c, 0n, None{}, GN.dzero(~K, ~W)), GN.delim(~K, ~W, w, GN.dswap(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c, r), c)) == GN.dgj(~K, ~W, m, w, 1n+c, GN.dpivot(~K, ~W, GN.delim(~K, ~W, w, GN.dswap(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), c, r), c), 1n+c, 1n+c, 0n, None{}, GN.dzero(~K, ~W)), GN.delim(~K, ~W, w, _, c)) : Maybe<&2, N.KMat(~K)>}
      {==}

def drights_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +n: Nat, rows: List<&2, List<&2, S.D>>) -> {GN.drights(~K, ~W, n, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows)) == KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.drights(n, rows)) : N.KMat(~K)}:
  match rows:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      %ddrop_t(~K, ~W, ~R, n, r) : {Con{GN.ddrop(~K, ~W, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r)), GN.drights(~K, ~W, n, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t))} == Con{_, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.drights(n, t))} : N.KMat(~K)}
      %drights_t(~K, ~W, ~R, n, t) : {Con{GN.ddrop(~K, ~W, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r)), GN.drights(~K, ~W, n, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t))} == Con{GN.ddrop(~K, ~W, n, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r)), _} : N.KMat(~K)}
      {==}

def dinv_of_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +n: Nat, m: Maybe<&2, List<&2, List<&2, S.D>>>) -> {GN.dinv.of(~K, ~W, n, GM.hmm(~K, ~PO.hom(K, W, R), m)) == GM.hmm(~K, ~PO.hom(K, W, R), NU.dinv.of(n, m)) : Maybe<&2, N.KMat(~K)>}:
  match m:
    case None{}:
      {==}
    case Some{+rows}:
      %drights_t(~K, ~W, ~R, n, rows) : {Some{GN.drights(~K, ~W, n, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows))} == Some{_} : Maybe<&2, N.KMat(~K)>}
      {==}

def dgj0_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +n: Nat, +w: Nat, +rows: List<&2, List<&2, S.D>>) -> {GN.dgj0(~K, ~W, n, w, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows)) == GM.hmm(~K, ~PO.hom(K, W, R), NU.dgj0(n, w, rows)) : Maybe<&2, N.KMat(~K)>}:
  %dgj_t(~K, ~W, ~R, n, w, 0n, NU.dpivot(rows, 0n, 0n, 0n, None{}, NU.dzero()), rows) : {GN.dgj(~K, ~W, n, w, 0n, GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), 0n, 0n, 0n, None{}, GN.dzero(~K, ~W)), KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows)) == _ : Maybe<&2, N.KMat(~K)>}
  %dpivot_t(~K, ~W, ~R, rows, 0n, 0n, 0n, None{}, NU.dzero()) : {GN.dgj(~K, ~W, n, w, 0n, GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), 0n, 0n, 0n, None{}, GN.dzero(~K, ~W)), KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows)) == GN.dgj(~K, ~W, n, w, 0n, _, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows)) : Maybe<&2, N.KMat(~K)>}
  %dzero_t(~K, ~W, ~R) : {GN.dgj(~K, ~W, n, w, 0n, GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), 0n, 0n, 0n, None{}, GN.dzero(~K, ~W)), KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows)) == GN.dgj(~K, ~W, n, w, 0n, GN.dpivot(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows), 0n, 0n, 0n, None{}, _), KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), rows)) : Maybe<&2, N.KMat(~K)>}
  {==}

# the approximate inverse
def dinverse_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, +n: Nat, +w: Nat, +a: List<&2, List<&2, S.D>>) -> {GN.dinverse(~K, ~W, n, w, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), a)) == GM.hmm(~K, ~PO.hom(K, W, R), NU.dinverse(n, w, a)) : Maybe<&2, N.KMat(~K)>}:
  %dinv_of_t(~K, ~W, ~R, n, NU.dgj0(n, w, NU.daugment(a, n, 0n))) : {GN.dinv.of(~K, ~W, n, GN.dgj0(~K, ~W, n, w, GN.daugment(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), a), n, 0n))) == _ : Maybe<&2, N.KMat(~K)>}
  %dgj0_t(~K, ~W, ~R, n, w, NU.daugment(a, n, 0n)) : {GN.dinv.of(~K, ~W, n, GN.dgj0(~K, ~W, n, w, GN.daugment(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), a), n, 0n))) == GN.dinv.of(~K, ~W, n, _) : Maybe<&2, N.KMat(~K)>}
  %daugment_t(~K, ~W, ~R, a, n, 0n) : {GN.dinv.of(~K, ~W, n, GN.dgj0(~K, ~W, n, w, GN.daugment(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), a), n, 0n))) == GN.dinv.of(~K, ~W, n, GN.dgj0(~K, ~W, n, w, _)) : Maybe<&2, N.KMat(~K)>}
  {==}

# Products
# --------

def ddot_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, xs: List<&2, S.D>, ys: List<&2, S.D>) -> {GN.ddot(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), xs), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), ys)) == KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.ddot(xs, ys)) : N.NC(K)}:
  match xs ys:
    case Nil{} ys:
      dzero_t(~K, ~W, ~R)
    case Con{x, t} Nil{}:
      dzero_t(~K, ~W, ~R)
    case Con{+x, +t} Con{+y, +u}:
      %KH.h_add(KI.dnum(), K, PO.hom(K, W, R))(S.D.mul(x, y), NU.ddot(t, u)) : {N.nadd(K, N.nmul(K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y)), GN.ddot(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), u))) == _ : N.NC(K)}
      %KH.h_mul(KI.dnum(), K, PO.hom(K, W, R))(x, y) : {N.nadd(K, N.nmul(K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y)), GN.ddot(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), u))) == N.nadd(K, _, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), NU.ddot(t, u))) : N.NC(K)}
      %ddot_t(~K, ~W, ~R, t, u) : {N.nadd(K, N.nmul(K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y)), GN.ddot(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), u))) == N.nadd(K, N.nmul(K, KH.hmap(KI.dnum(), K, PO.hom(K, W, R), x), KH.hmap(KI.dnum(), K, PO.hom(K, W, R), y)), _) : N.NC(K)}
      {==}

def dmatvec_t(~K: N.Num, ~W: PO.POps<K>, ~R: PO.PLaws<K, W>, a: List<&2, List<&2, S.D>>, +v: List<&2, S.D>) -> {GN.dmatvec(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), a), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), v)) == KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dmatvec(a, v)) : N.KVec(~K)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +t}:
      %ddot_t(~K, ~W, ~R, r, v) : {Con{GN.ddot(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), v)), GN.dmatvec(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), v))} == Con{_, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), NU.dmatvec(t, v))} : N.KVec(~K)}
      %dmatvec_t(~K, ~W, ~R, t, v) : {Con{GN.ddot(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), v)), GN.dmatvec(~K, ~W, KH.hm(~KI.dnum(), ~K, ~PO.hom(K, W, R), t), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), v))} == Con{GN.ddot(~K, ~W, KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), r), KH.hv(~KI.dnum(), ~K, ~PO.hom(K, W, R), v)), _} : N.KVec(~K)}
      {==}
