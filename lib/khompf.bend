# bend-cad: the checker's arithmetic (lib/karith.bend) and balls
# (lib/kball.bend) commute with a map of computing numbers h : K -> L
# (lib/khom.bend): each operation on the images is the image of the
# operation, and each verdict (an order, a length, a held constant) is the
# same. Untrusted; for the word verdict (PLAN-sk13w W5).


import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/knum.bend as N
import ./karith.bend as KA
import ./kball.bend as KB
import ./khom.bend as KH

# The map's laws, turned around
# -----------------------------

def hz_r(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>) -> {KH.hmap(K, L, H, N.nzero(K)) == N.nzero(L) : N.NC(L)}:
  Equal.sym(N.NC(L), N.nzero(L), KH.hmap(K, L, H, N.nzero(K)), KH.h_zero(K, L, H))

def ho_r(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>) -> {KH.hmap(K, L, H, N.none(K)) == N.none(L) : N.NC(L)}:
  Equal.sym(N.NC(L), N.none(L), KH.hmap(K, L, H, N.none(K)), KH.h_one(K, L, H))

# Scalars
# -------

def ksub_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +a: N.NC(K), +b: N.NC(K)) -> {KA.ksub(~L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b)) == KH.hmap(K, L, H, KA.ksub(~K, a, b)) : N.NC(L)}:
  %KH.h_add(K, L, H)(a, N.nneg(K, b)) : {N.nadd(L, KH.hmap(K, L, H, a), N.nneg(L, KH.hmap(K, L, H, b))) == _ : N.NC(L)}
  %KH.h_neg(K, L, H)(b) : {N.nadd(L, KH.hmap(K, L, H, a), N.nneg(L, KH.hmap(K, L, H, b))) == N.nadd(L, KH.hmap(K, L, H, a), _) : N.NC(L)}
  {==}

def kabs_go_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, c: Cmp, +a: N.NC(K)) -> {KA.kabs.go(~L, c, KH.hmap(K, L, H, a)) == KH.hmap(K, L, H, KA.kabs.go(~K, c, a)) : N.NC(L)}:
  match c:
    case LT{}:
      KH.h_neg(K, L, H)(a)
    case EQ{}:
      {==}
    case GT{}:
      {==}

def kabs_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +a: N.NC(K)) -> {KA.kabs(~L, KH.hmap(K, L, H, a)) == KH.hmap(K, L, H, KA.kabs(~K, a)) : N.NC(L)}:
  %KH.h_cmp(K, L, H)(a, N.nzero(K)) : {KA.kabs.go(~L, N.ncmp(L, KH.hmap(K, L, H, a), N.nzero(L)), KH.hmap(K, L, H, a)) == KH.hmap(K, L, H, KA.kabs.go(~K, _, a)) : N.NC(L)}
  %KH.h_zero(K, L, H) : {KA.kabs.go(~L, N.ncmp(L, KH.hmap(K, L, H, a), N.nzero(L)), KH.hmap(K, L, H, a)) == KH.hmap(K, L, H, KA.kabs.go(~K, N.ncmp(L, KH.hmap(K, L, H, a), _), a)) : N.NC(L)}
  kabs_go_h(~K, ~L, ~H, N.ncmp(L, KH.hmap(K, L, H, a), N.nzero(L)), a)

def kle_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +a: N.NC(K), +b: N.NC(K)) -> {KA.kle(~L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b)) == KA.kle(~K, a, b) : Bool}:
  %KH.h_cmp(K, L, H)(a, b) : {KA.kle.go(N.ncmp(L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b))) == KA.kle.go(_) : Bool}
  {==}

def klt_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +a: N.NC(K), +b: N.NC(K)) -> {KA.klt(~L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b)) == KA.klt(~K, a, b) : Bool}:
  %KH.h_cmp(K, L, H)(a, b) : {KA.klt.go(N.ncmp(L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b))) == KA.klt.go(_) : Bool}
  {==}

# with 0 or 1 on one side
def kle0_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +b: N.NC(K)) -> {KA.kle(~L, N.nzero(L), KH.hmap(K, L, H, b)) == KA.kle(~K, N.nzero(K), b) : Bool}:
  %hz_r(~K, ~L, ~H) : {KA.kle(~L, _, KH.hmap(K, L, H, b)) == KA.kle(~K, N.nzero(K), b) : Bool}
  kle_h(~K, ~L, ~H, N.nzero(K), b)

def kle0r_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +a: N.NC(K)) -> {KA.kle(~L, KH.hmap(K, L, H, a), N.nzero(L)) == KA.kle(~K, a, N.nzero(K)) : Bool}:
  %hz_r(~K, ~L, ~H) : {KA.kle(~L, KH.hmap(K, L, H, a), _) == KA.kle(~K, a, N.nzero(K)) : Bool}
  kle_h(~K, ~L, ~H, a, N.nzero(K))

def klt0_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +b: N.NC(K)) -> {KA.klt(~L, N.nzero(L), KH.hmap(K, L, H, b)) == KA.klt(~K, N.nzero(K), b) : Bool}:
  %hz_r(~K, ~L, ~H) : {KA.klt(~L, _, KH.hmap(K, L, H, b)) == KA.klt(~K, N.nzero(K), b) : Bool}
  klt_h(~K, ~L, ~H, N.nzero(K), b)

def klt1_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +a: N.NC(K)) -> {KA.klt(~L, KH.hmap(K, L, H, a), N.none(L)) == KA.klt(~K, a, N.none(K)) : Bool}:
  %ho_r(~K, ~L, ~H) : {KA.klt(~L, KH.hmap(K, L, H, a), _) == KA.klt(~K, a, N.none(K)) : Bool}
  klt_h(~K, ~L, ~H, a, N.none(K))

# Vectors and matrices
# --------------------

def kvadd_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, u: N.KVec(~K), w: N.KVec(~K)) -> {KA.kvadd(~L, KH.hv(~K, ~L, ~H, u), KH.hv(~K, ~L, ~H, w)) == KH.hv(~K, ~L, ~H, KA.kvadd(~K, u, w)) : N.KVec(~L)}:
  match u w:
    case Nil{} w:
      {==}
    case Con{+a, +us} Nil{}:
      {==}
    case Con{+a, +us} Con{+b, +ws}:
      %KH.h_add(K, L, H)(a, b) : {Con{N.nadd(L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b)), KA.kvadd(~L, KH.hv(~K, ~L, ~H, us), KH.hv(~K, ~L, ~H, ws))} == Con{_, KH.hv(~K, ~L, ~H, KA.kvadd(~K, us, ws))} : N.KVec(~L)}
      %kvadd_h(~K, ~L, ~H, us, ws) : {Con{N.nadd(L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b)), KA.kvadd(~L, KH.hv(~K, ~L, ~H, us), KH.hv(~K, ~L, ~H, ws))} == Con{N.nadd(L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b)), _} : N.KVec(~L)}
      {==}

def kvneg_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, u: N.KVec(~K)) -> {KA.kvneg(~L, KH.hv(~K, ~L, ~H, u)) == KH.hv(~K, ~L, ~H, KA.kvneg(~K, u)) : N.KVec(~L)}:
  match u:
    case Nil{}:
      {==}
    case Con{+a, +us}:
      %KH.h_neg(K, L, H)(a) : {Con{N.nneg(L, KH.hmap(K, L, H, a)), KA.kvneg(~L, KH.hv(~K, ~L, ~H, us))} == Con{_, KH.hv(~K, ~L, ~H, KA.kvneg(~K, us))} : N.KVec(~L)}
      %kvneg_h(~K, ~L, ~H, us) : {Con{N.nneg(L, KH.hmap(K, L, H, a)), KA.kvneg(~L, KH.hv(~K, ~L, ~H, us))} == Con{N.nneg(L, KH.hmap(K, L, H, a)), _} : N.KVec(~L)}
      {==}

def kvscale_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +c: N.NC(K), u: N.KVec(~K)) -> {KA.kvscale(~L, KH.hmap(K, L, H, c), KH.hv(~K, ~L, ~H, u)) == KH.hv(~K, ~L, ~H, KA.kvscale(~K, c, u)) : N.KVec(~L)}:
  match u:
    case Nil{}:
      {==}
    case Con{+a, +us}:
      %KH.h_mul(K, L, H)(c, a) : {Con{N.nmul(L, KH.hmap(K, L, H, c), KH.hmap(K, L, H, a)), KA.kvscale(~L, KH.hmap(K, L, H, c), KH.hv(~K, ~L, ~H, us))} == Con{_, KH.hv(~K, ~L, ~H, KA.kvscale(~K, c, us))} : N.KVec(~L)}
      %kvscale_h(~K, ~L, ~H, c, us) : {Con{N.nmul(L, KH.hmap(K, L, H, c), KH.hmap(K, L, H, a)), KA.kvscale(~L, KH.hmap(K, L, H, c), KH.hv(~K, ~L, ~H, us))} == Con{N.nmul(L, KH.hmap(K, L, H, c), KH.hmap(K, L, H, a)), _} : N.KVec(~L)}
      {==}

def kdot_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, a: N.KVec(~K), v: N.KVec(~K)) -> {KA.kdot(~L, KH.hv(~K, ~L, ~H, a), KH.hv(~K, ~L, ~H, v)) == KH.hmap(K, L, H, KA.kdot(~K, a, v)) : N.NC(L)}:
  match a v:
    case Nil{} v:
      KH.h_zero(K, L, H)
    case Con{+x, +xs} Nil{}:
      KH.h_zero(K, L, H)
    case Con{+x, +xs} Con{+y, +ys}:
      %KH.h_add(K, L, H)(N.nmul(K, x, y), KA.kdot(~K, xs, ys)) : {N.nadd(L, N.nmul(L, KH.hmap(K, L, H, x), KH.hmap(K, L, H, y)), KA.kdot(~L, KH.hv(~K, ~L, ~H, xs), KH.hv(~K, ~L, ~H, ys))) == _ : N.NC(L)}
      %KH.h_mul(K, L, H)(x, y) : {N.nadd(L, N.nmul(L, KH.hmap(K, L, H, x), KH.hmap(K, L, H, y)), KA.kdot(~L, KH.hv(~K, ~L, ~H, xs), KH.hv(~K, ~L, ~H, ys))) == N.nadd(L, _, KH.hmap(K, L, H, KA.kdot(~K, xs, ys))) : N.NC(L)}
      %kdot_h(~K, ~L, ~H, xs, ys) : {N.nadd(L, N.nmul(L, KH.hmap(K, L, H, x), KH.hmap(K, L, H, y)), KA.kdot(~L, KH.hv(~K, ~L, ~H, xs), KH.hv(~K, ~L, ~H, ys))) == N.nadd(L, N.nmul(L, KH.hmap(K, L, H, x), KH.hmap(K, L, H, y)), _) : N.NC(L)}
      {==}

def kmatvec_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, a: N.KMat(~K), +v: N.KVec(~K)) -> {KA.kmatvec(~L, KH.hm(~K, ~L, ~H, a), KH.hv(~K, ~L, ~H, v)) == KH.hv(~K, ~L, ~H, KA.kmatvec(~K, a, v)) : N.KVec(~L)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %kdot_h(~K, ~L, ~H, r, v) : {Con{KA.kdot(~L, KH.hv(~K, ~L, ~H, r), KH.hv(~K, ~L, ~H, v)), KA.kmatvec(~L, KH.hm(~K, ~L, ~H, rs), KH.hv(~K, ~L, ~H, v))} == Con{_, KH.hv(~K, ~L, ~H, KA.kmatvec(~K, rs, v))} : N.KVec(~L)}
      %kmatvec_h(~K, ~L, ~H, rs, v) : {Con{KA.kdot(~L, KH.hv(~K, ~L, ~H, r), KH.hv(~K, ~L, ~H, v)), KA.kmatvec(~L, KH.hm(~K, ~L, ~H, rs), KH.hv(~K, ~L, ~H, v))} == Con{KA.kdot(~L, KH.hv(~K, ~L, ~H, r), KH.hv(~K, ~L, ~H, v)), _} : N.KVec(~L)}
      {==}

def kvecmat_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, a: N.KVec(~K), b: N.KMat(~K)) -> {KA.kvecmat(~L, KH.hv(~K, ~L, ~H, a), KH.hm(~K, ~L, ~H, b)) == KH.hv(~K, ~L, ~H, KA.kvecmat(~K, a, b)) : N.KVec(~L)}:
  match a b:
    case Nil{} b:
      {==}
    case Con{+x, +xs} Nil{}:
      {==}
    case Con{+x, +xs} Con{+r, +rs}:
      %kvadd_h(~K, ~L, ~H, KA.kvscale(~K, x, r), KA.kvecmat(~K, xs, rs)) : {KA.kvadd(~L, KA.kvscale(~L, KH.hmap(K, L, H, x), KH.hv(~K, ~L, ~H, r)), KA.kvecmat(~L, KH.hv(~K, ~L, ~H, xs), KH.hm(~K, ~L, ~H, rs))) == _ : N.KVec(~L)}
      %kvscale_h(~K, ~L, ~H, x, r) : {KA.kvadd(~L, KA.kvscale(~L, KH.hmap(K, L, H, x), KH.hv(~K, ~L, ~H, r)), KA.kvecmat(~L, KH.hv(~K, ~L, ~H, xs), KH.hm(~K, ~L, ~H, rs))) == KA.kvadd(~L, _, KH.hv(~K, ~L, ~H, KA.kvecmat(~K, xs, rs))) : N.KVec(~L)}
      %kvecmat_h(~K, ~L, ~H, xs, rs) : {KA.kvadd(~L, KA.kvscale(~L, KH.hmap(K, L, H, x), KH.hv(~K, ~L, ~H, r)), KA.kvecmat(~L, KH.hv(~K, ~L, ~H, xs), KH.hm(~K, ~L, ~H, rs))) == KA.kvadd(~L, KA.kvscale(~L, KH.hmap(K, L, H, x), KH.hv(~K, ~L, ~H, r)), _) : N.KVec(~L)}
      {==}

def kmatmul_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, a: N.KMat(~K), +b: N.KMat(~K)) -> {KA.kmatmul(~L, KH.hm(~K, ~L, ~H, a), KH.hm(~K, ~L, ~H, b)) == KH.hm(~K, ~L, ~H, KA.kmatmul(~K, a, b)) : N.KMat(~L)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %kvecmat_h(~K, ~L, ~H, r, b) : {Con{KA.kvecmat(~L, KH.hv(~K, ~L, ~H, r), KH.hm(~K, ~L, ~H, b)), KA.kmatmul(~L, KH.hm(~K, ~L, ~H, rs), KH.hm(~K, ~L, ~H, b))} == Con{_, KH.hm(~K, ~L, ~H, KA.kmatmul(~K, rs, b))} : N.KMat(~L)}
      %kmatmul_h(~K, ~L, ~H, rs, b) : {Con{KA.kvecmat(~L, KH.hv(~K, ~L, ~H, r), KH.hm(~K, ~L, ~H, b)), KA.kmatmul(~L, KH.hm(~K, ~L, ~H, rs), KH.hm(~K, ~L, ~H, b))} == Con{KA.kvecmat(~L, KH.hv(~K, ~L, ~H, r), KH.hm(~K, ~L, ~H, b)), _} : N.KMat(~L)}
      {==}

def kmadd_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, a: N.KMat(~K), b: N.KMat(~K)) -> {KA.kmadd(~L, KH.hm(~K, ~L, ~H, a), KH.hm(~K, ~L, ~H, b)) == KH.hm(~K, ~L, ~H, KA.kmadd(~K, a, b)) : N.KMat(~L)}:
  match a b:
    case Nil{} b:
      {==}
    case Con{+r, +rs} Nil{}:
      {==}
    case Con{+r, +rs} Con{+t, +ts}:
      %kvadd_h(~K, ~L, ~H, r, t) : {Con{KA.kvadd(~L, KH.hv(~K, ~L, ~H, r), KH.hv(~K, ~L, ~H, t)), KA.kmadd(~L, KH.hm(~K, ~L, ~H, rs), KH.hm(~K, ~L, ~H, ts))} == Con{_, KH.hm(~K, ~L, ~H, KA.kmadd(~K, rs, ts))} : N.KMat(~L)}
      %kmadd_h(~K, ~L, ~H, rs, ts) : {Con{KA.kvadd(~L, KH.hv(~K, ~L, ~H, r), KH.hv(~K, ~L, ~H, t)), KA.kmadd(~L, KH.hm(~K, ~L, ~H, rs), KH.hm(~K, ~L, ~H, ts))} == Con{KA.kvadd(~L, KH.hv(~K, ~L, ~H, r), KH.hv(~K, ~L, ~H, t)), _} : N.KMat(~L)}
      {==}

def kmneg_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, a: N.KMat(~K)) -> {KA.kmneg(~L, KH.hm(~K, ~L, ~H, a)) == KH.hm(~K, ~L, ~H, KA.kmneg(~K, a)) : N.KMat(~L)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %kvneg_h(~K, ~L, ~H, r) : {Con{KA.kvneg(~L, KH.hv(~K, ~L, ~H, r)), KA.kmneg(~L, KH.hm(~K, ~L, ~H, rs))} == Con{_, KH.hm(~K, ~L, ~H, KA.kmneg(~K, rs))} : N.KMat(~L)}
      %kmneg_h(~K, ~L, ~H, rs) : {Con{KA.kvneg(~L, KH.hv(~K, ~L, ~H, r)), KA.kmneg(~L, KH.hm(~K, ~L, ~H, rs))} == Con{KA.kvneg(~L, KH.hv(~K, ~L, ~H, r)), _} : N.KMat(~L)}
      {==}

def kshift_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, a: N.KMat(~K)) -> {KA.kshift(~L, KH.hm(~K, ~L, ~H, a)) == KH.hm(~K, ~L, ~H, KA.kshift(~K, a)) : N.KMat(~L)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %KH.h_zero(K, L, H) : {Con{Con{N.nzero(L), KH.hv(~K, ~L, ~H, r)}, KA.kshift(~L, KH.hm(~K, ~L, ~H, rs))} == Con{Con{_, KH.hv(~K, ~L, ~H, r)}, KH.hm(~K, ~L, ~H, KA.kshift(~K, rs))} : N.KMat(~L)}
      %kshift_h(~K, ~L, ~H, rs) : {Con{Con{N.nzero(L), KH.hv(~K, ~L, ~H, r)}, KA.kshift(~L, KH.hm(~K, ~L, ~H, rs))} == Con{Con{N.nzero(L), KH.hv(~K, ~L, ~H, r)}, _} : N.KMat(~L)}
      {==}

def kident_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, n: Nat) -> {KA.kident(~L, n) == KH.hm(~K, ~L, ~H, KA.kident(~K, n)) : N.KMat(~L)}:
  match n:
    case 0n:
      {==}
    case 1n++k:
      %KH.h_one(K, L, H) : {Con{[N.none(L)], KA.kshift(~L, KA.kident(~L, k))} == Con{[_], KH.hm(~K, ~L, ~H, KA.kshift(~K, KA.kident(~K, k)))} : N.KMat(~L)}
      %kshift_h(~K, ~L, ~H, KA.kident(~K, k)) : {Con{[N.none(L)], KA.kshift(~L, KA.kident(~L, k))} == Con{[N.none(L)], _} : N.KMat(~L)}
      %kident_h(~K, ~L, ~H, k) : {Con{[N.none(L)], KA.kshift(~L, KA.kident(~L, k))} == Con{[N.none(L)], KA.kshift(~L, _)} : N.KMat(~L)}
      {==}

def kvabs_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, u: N.KVec(~K)) -> {KA.kvabs(~L, KH.hv(~K, ~L, ~H, u)) == KH.hv(~K, ~L, ~H, KA.kvabs(~K, u)) : N.KVec(~L)}:
  match u:
    case Nil{}:
      {==}
    case Con{+a, +us}:
      %kabs_h(~K, ~L, ~H, a) : {Con{KA.kabs(~L, KH.hmap(K, L, H, a)), KA.kvabs(~L, KH.hv(~K, ~L, ~H, us))} == Con{_, KH.hv(~K, ~L, ~H, KA.kvabs(~K, us))} : N.KVec(~L)}
      %kvabs_h(~K, ~L, ~H, us) : {Con{KA.kabs(~L, KH.hmap(K, L, H, a)), KA.kvabs(~L, KH.hv(~K, ~L, ~H, us))} == Con{KA.kabs(~L, KH.hmap(K, L, H, a)), _} : N.KVec(~L)}
      {==}

def kmabs_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, a: N.KMat(~K)) -> {KA.kmabs(~L, KH.hm(~K, ~L, ~H, a)) == KH.hm(~K, ~L, ~H, KA.kmabs(~K, a)) : N.KMat(~L)}:
  match a:
    case Nil{}:
      {==}
    case Con{+r, +rs}:
      %kvabs_h(~K, ~L, ~H, r) : {Con{KA.kvabs(~L, KH.hv(~K, ~L, ~H, r)), KA.kmabs(~L, KH.hm(~K, ~L, ~H, rs))} == Con{_, KH.hm(~K, ~L, ~H, KA.kmabs(~K, rs))} : N.KMat(~L)}
      %kmabs_h(~K, ~L, ~H, rs) : {Con{KA.kvabs(~L, KH.hv(~K, ~L, ~H, r)), KA.kmabs(~L, KH.hm(~K, ~L, ~H, rs))} == Con{KA.kvabs(~L, KH.hv(~K, ~L, ~H, r)), _} : N.KMat(~L)}
      {==}

def kfit_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, n: Nat, u: N.KVec(~K)) -> {KA.kfit(~L, n, KH.hv(~K, ~L, ~H, u)) == KH.hv(~K, ~L, ~H, KA.kfit(~K, n, u)) : N.KVec(~L)}:
  match n u:
    case 0n u:
      {==}
    case 1n++k Nil{}:
      %KH.h_zero(K, L, H) : {Con{N.nzero(L), KA.kfit(~L, k, Nil{})} == Con{_, KH.hv(~K, ~L, ~H, KA.kfit(~K, k, Nil{}))} : N.KVec(~L)}
      %kfit_h(~K, ~L, ~H, k, Nil{}) : {Con{N.nzero(L), KA.kfit(~L, k, Nil{})} == Con{N.nzero(L), _} : N.KVec(~L)}
      {==}
    case 1n++k Con{+a, +rest}:
      %kfit_h(~K, ~L, ~H, k, rest) : {Con{KH.hmap(K, L, H, a), KA.kfit(~L, k, KH.hv(~K, ~L, ~H, rest))} == Con{KH.hmap(K, L, H, a), _} : N.KVec(~L)}
      {==}

def kdrop_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, n: Nat, u: N.KVec(~K)) -> {KA.kdrop(~L, n, KH.hv(~K, ~L, ~H, u)) == KH.hv(~K, ~L, ~H, KA.kdrop(~K, n, u)) : N.KVec(~L)}:
  match n u:
    case 0n u:
      {==}
    case 1n+k Nil{}:
      {==}
    case 1n+k Con{a, rest}:
      kdrop_h(~K, ~L, ~H, k, rest)

def kapp_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, u: N.KVec(~K), +w: N.KVec(~K)) -> {KA.kapp(~L, KH.hv(~K, ~L, ~H, u), KH.hv(~K, ~L, ~H, w)) == KH.hv(~K, ~L, ~H, KA.kapp(~K, u, w)) : N.KVec(~L)}:
  match u:
    case Nil{}:
      {==}
    case Con{+a, +us}:
      %kapp_h(~K, ~L, ~H, us, w) : {Con{KH.hmap(K, L, H, a), KA.kapp(~L, KH.hv(~K, ~L, ~H, us), KH.hv(~K, ~L, ~H, w))} == Con{KH.hmap(K, L, H, a), _} : N.KVec(~L)}
      {==}

def kones_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, n: Nat) -> {KA.kones(~L, n) == KH.hv(~K, ~L, ~H, KA.kones(~K, n)) : N.KVec(~L)}:
  match n:
    case 0n:
      {==}
    case 1n++k:
      %KH.h_one(K, L, H) : {Con{N.none(L), KA.kones(~L, k)} == Con{_, KH.hv(~K, ~L, ~H, KA.kones(~K, k))} : N.KVec(~L)}
      %kones_h(~K, ~L, ~H, k) : {Con{N.none(L), KA.kones(~L, k)} == Con{N.none(L), _} : N.KVec(~L)}
      {==}

def kvle_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, u: N.KVec(~K), w: N.KVec(~K)) -> {KA.kvle(~L, KH.hv(~K, ~L, ~H, u), KH.hv(~K, ~L, ~H, w)) == KA.kvle(~K, u, w) : Bool}:
  match u w:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+b, +ws}:
      %kle0_h(~K, ~L, ~H, b) : {KA.band(KA.kle(~L, N.nzero(L), KH.hmap(K, L, H, b)), KA.kvle(~L, Nil{}, KH.hv(~K, ~L, ~H, ws))) == KA.band(_, KA.kvle(~K, Nil{}, ws)) : Bool}
      %kvle_h(~K, ~L, ~H, Nil{}, ws) : {KA.band(KA.kle(~L, N.nzero(L), KH.hmap(K, L, H, b)), KA.kvle(~L, Nil{}, KH.hv(~K, ~L, ~H, ws))) == KA.band(KA.kle(~L, N.nzero(L), KH.hmap(K, L, H, b)), _) : Bool}
      {==}
    case Con{+a, +us} Nil{}:
      %kle0r_h(~K, ~L, ~H, a) : {KA.band(KA.kle(~L, KH.hmap(K, L, H, a), N.nzero(L)), KA.kvle(~L, KH.hv(~K, ~L, ~H, us), Nil{})) == KA.band(_, KA.kvle(~K, us, Nil{})) : Bool}
      %kvle_h(~K, ~L, ~H, us, Nil{}) : {KA.band(KA.kle(~L, KH.hmap(K, L, H, a), N.nzero(L)), KA.kvle(~L, KH.hv(~K, ~L, ~H, us), Nil{})) == KA.band(KA.kle(~L, KH.hmap(K, L, H, a), N.nzero(L)), _) : Bool}
      {==}
    case Con{+a, +us} Con{+b, +ws}:
      %kle_h(~K, ~L, ~H, a, b) : {KA.band(KA.kle(~L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b)), KA.kvle(~L, KH.hv(~K, ~L, ~H, us), KH.hv(~K, ~L, ~H, ws))) == KA.band(_, KA.kvle(~K, us, ws)) : Bool}
      %kvle_h(~K, ~L, ~H, us, ws) : {KA.band(KA.kle(~L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b)), KA.kvle(~L, KH.hv(~K, ~L, ~H, us), KH.hv(~K, ~L, ~H, ws))) == KA.band(KA.kle(~L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b)), _) : Bool}
      {==}

def kvlt_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, u: N.KVec(~K), w: N.KVec(~K)) -> {KA.kvlt(~L, KH.hv(~K, ~L, ~H, u), KH.hv(~K, ~L, ~H, w)) == KA.kvlt(~K, u, w) : Bool}:
  match u w:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{+b, +ws}:
      %klt0_h(~K, ~L, ~H, b) : {KA.band(KA.klt(~L, N.nzero(L), KH.hmap(K, L, H, b)), KA.kvlt(~L, Nil{}, KH.hv(~K, ~L, ~H, ws))) == KA.band(_, KA.kvlt(~K, Nil{}, ws)) : Bool}
      %kvlt_h(~K, ~L, ~H, Nil{}, ws) : {KA.band(KA.klt(~L, N.nzero(L), KH.hmap(K, L, H, b)), KA.kvlt(~L, Nil{}, KH.hv(~K, ~L, ~H, ws))) == KA.band(KA.klt(~L, N.nzero(L), KH.hmap(K, L, H, b)), _) : Bool}
      {==}
    case Con{+a, +us} Nil{}:
      {==}
    case Con{+a, +us} Con{+b, +ws}:
      %klt_h(~K, ~L, ~H, a, b) : {KA.band(KA.klt(~L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b)), KA.kvlt(~L, KH.hv(~K, ~L, ~H, us), KH.hv(~K, ~L, ~H, ws))) == KA.band(_, KA.kvlt(~K, us, ws)) : Bool}
      %kvlt_h(~K, ~L, ~H, us, ws) : {KA.band(KA.klt(~L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b)), KA.kvlt(~L, KH.hv(~K, ~L, ~H, us), KH.hv(~K, ~L, ~H, ws))) == KA.band(KA.klt(~L, KH.hmap(K, L, H, a), KH.hmap(K, L, H, b)), _) : Bool}
      {==}

def klen_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, u: N.KVec(~K)) -> {KA.klen(~L, KH.hv(~K, ~L, ~H, u)) == KA.klen(~K, u) : Nat}:
  match u:
    case Nil{}:
      {==}
    case Con{+a, +us}:
      %klen_h(~K, ~L, ~H, us) : {1n+KA.klen(~L, KH.hv(~K, ~L, ~H, us)) == 1n+_ : Nat}
      {==}

# Balls
# -----

def bzero_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>) -> {KB.bzero(~L) == KH.hball(~K, ~L, ~H, KB.bzero(~K)) : KB.KB<L>}:
  %KH.h_zero(K, L, H) : {KB.KB{N.nzero(L), N.nzero(L)} == KB.KB{_, KH.hmap(K, L, H, N.nzero(K))} : KB.KB<L>}
  %KH.h_zero(K, L, H) : {KB.KB{N.nzero(L), N.nzero(L)} == KB.KB{N.nzero(L), _} : KB.KB<L>}
  {==}

def badd_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, x: KB.KB<K>, y: KB.KB<K>) -> {KB.badd(~L, KH.hball(~K, ~L, ~H, x), KH.hball(~K, ~L, ~H, y)) == KH.hball(~K, ~L, ~H, KB.badd(~K, x, y)) : KB.KB<L>}:
  match x y:
    case KB.KB{+c1, +r1} KB.KB{+c2, +r2}:
      %KH.h_add(K, L, H)(c1, c2) : {KB.KB{N.nadd(L, KH.hmap(K, L, H, c1), KH.hmap(K, L, H, c2)), N.nadd(L, KH.hmap(K, L, H, r1), KH.hmap(K, L, H, r2))} == KB.KB{_, KH.hmap(K, L, H, N.nadd(K, r1, r2))} : KB.KB<L>}
      %KH.h_add(K, L, H)(r1, r2) : {KB.KB{N.nadd(L, KH.hmap(K, L, H, c1), KH.hmap(K, L, H, c2)), N.nadd(L, KH.hmap(K, L, H, r1), KH.hmap(K, L, H, r2))} == KB.KB{N.nadd(L, KH.hmap(K, L, H, c1), KH.hmap(K, L, H, c2)), _} : KB.KB<L>}
      {==}

def bneg_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, x: KB.KB<K>) -> {KB.bneg(~L, KH.hball(~K, ~L, ~H, x)) == KH.hball(~K, ~L, ~H, KB.bneg(~K, x)) : KB.KB<L>}:
  match x:
    case KB.KB{+c, +r}:
      %KH.h_neg(K, L, H)(c) : {KB.KB{N.nneg(L, KH.hmap(K, L, H, c)), KH.hmap(K, L, H, r)} == KB.KB{_, KH.hmap(K, L, H, r)} : KB.KB<L>}
      {==}


# the product's radius
def bmr_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +c1: N.NC(K), +r1: N.NC(K), +c2: N.NC(K), +r2: N.NC(K)) -> {N.nadd(L, N.nadd(L, N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c1)), KH.hmap(K, L, H, r2)), N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c2)), KH.hmap(K, L, H, r1))), N.nmul(L, KH.hmap(K, L, H, r1), KH.hmap(K, L, H, r2))) == KH.hmap(K, L, H, N.nadd(K, N.nadd(K, N.nmul(K, KA.kabs(~K, c1), r2), N.nmul(K, KA.kabs(~K, c2), r1)), N.nmul(K, r1, r2))) : N.NC(L)}:
  %KH.h_add(K, L, H)(N.nadd(K, N.nmul(K, KA.kabs(~K, c1), r2), N.nmul(K, KA.kabs(~K, c2), r1)), N.nmul(K, r1, r2)) : {N.nadd(L, N.nadd(L, N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c1)), KH.hmap(K, L, H, r2)), N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c2)), KH.hmap(K, L, H, r1))), N.nmul(L, KH.hmap(K, L, H, r1), KH.hmap(K, L, H, r2))) == _ : N.NC(L)}
  %KH.h_add(K, L, H)(N.nmul(K, KA.kabs(~K, c1), r2), N.nmul(K, KA.kabs(~K, c2), r1)) : {N.nadd(L, N.nadd(L, N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c1)), KH.hmap(K, L, H, r2)), N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c2)), KH.hmap(K, L, H, r1))), N.nmul(L, KH.hmap(K, L, H, r1), KH.hmap(K, L, H, r2))) == N.nadd(L, _, KH.hmap(K, L, H, N.nmul(K, r1, r2))) : N.NC(L)}
  %KH.h_mul(K, L, H)(KA.kabs(~K, c1), r2) : {N.nadd(L, N.nadd(L, N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c1)), KH.hmap(K, L, H, r2)), N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c2)), KH.hmap(K, L, H, r1))), N.nmul(L, KH.hmap(K, L, H, r1), KH.hmap(K, L, H, r2))) == N.nadd(L, N.nadd(L, _, KH.hmap(K, L, H, N.nmul(K, KA.kabs(~K, c2), r1))), KH.hmap(K, L, H, N.nmul(K, r1, r2))) : N.NC(L)}
  %kabs_h(~K, ~L, ~H, c1) : {N.nadd(L, N.nadd(L, N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c1)), KH.hmap(K, L, H, r2)), N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c2)), KH.hmap(K, L, H, r1))), N.nmul(L, KH.hmap(K, L, H, r1), KH.hmap(K, L, H, r2))) == N.nadd(L, N.nadd(L, N.nmul(L, _, KH.hmap(K, L, H, r2)), KH.hmap(K, L, H, N.nmul(K, KA.kabs(~K, c2), r1))), KH.hmap(K, L, H, N.nmul(K, r1, r2))) : N.NC(L)}
  %KH.h_mul(K, L, H)(KA.kabs(~K, c2), r1) : {N.nadd(L, N.nadd(L, N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c1)), KH.hmap(K, L, H, r2)), N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c2)), KH.hmap(K, L, H, r1))), N.nmul(L, KH.hmap(K, L, H, r1), KH.hmap(K, L, H, r2))) == N.nadd(L, N.nadd(L, N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c1)), KH.hmap(K, L, H, r2)), _), KH.hmap(K, L, H, N.nmul(K, r1, r2))) : N.NC(L)}
  %kabs_h(~K, ~L, ~H, c2) : {N.nadd(L, N.nadd(L, N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c1)), KH.hmap(K, L, H, r2)), N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c2)), KH.hmap(K, L, H, r1))), N.nmul(L, KH.hmap(K, L, H, r1), KH.hmap(K, L, H, r2))) == N.nadd(L, N.nadd(L, N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c1)), KH.hmap(K, L, H, r2)), N.nmul(L, _, KH.hmap(K, L, H, r1))), KH.hmap(K, L, H, N.nmul(K, r1, r2))) : N.NC(L)}
  %KH.h_mul(K, L, H)(r1, r2) : {N.nadd(L, N.nadd(L, N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c1)), KH.hmap(K, L, H, r2)), N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c2)), KH.hmap(K, L, H, r1))), N.nmul(L, KH.hmap(K, L, H, r1), KH.hmap(K, L, H, r2))) == N.nadd(L, N.nadd(L, N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c1)), KH.hmap(K, L, H, r2)), N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c2)), KH.hmap(K, L, H, r1))), _) : N.NC(L)}
  {==}

def bmul_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, x: KB.KB<K>, y: KB.KB<K>) -> {KB.bmul(~L, KH.hball(~K, ~L, ~H, x), KH.hball(~K, ~L, ~H, y)) == KH.hball(~K, ~L, ~H, KB.bmul(~K, x, y)) : KB.KB<L>}:
  match x y:
    case KB.KB{+c1, +r1} KB.KB{+c2, +r2}:
      %KH.h_mul(K, L, H)(c1, c2) : {KB.KB{N.nmul(L, KH.hmap(K, L, H, c1), KH.hmap(K, L, H, c2)), N.nadd(L, N.nadd(L, N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c1)), KH.hmap(K, L, H, r2)), N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c2)), KH.hmap(K, L, H, r1))), N.nmul(L, KH.hmap(K, L, H, r1), KH.hmap(K, L, H, r2)))} == KB.KB{_, KH.hmap(K, L, H, N.nadd(K, N.nadd(K, N.nmul(K, KA.kabs(~K, c1), r2), N.nmul(K, KA.kabs(~K, c2), r1)), N.nmul(K, r1, r2)))} : KB.KB<L>}
      %bmr_h(~K, ~L, ~H, c1, r1, c2, r2) : {KB.KB{N.nmul(L, KH.hmap(K, L, H, c1), KH.hmap(K, L, H, c2)), N.nadd(L, N.nadd(L, N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c1)), KH.hmap(K, L, H, r2)), N.nmul(L, KA.kabs(~L, KH.hmap(K, L, H, c2)), KH.hmap(K, L, H, r1))), N.nmul(L, KH.hmap(K, L, H, r1), KH.hmap(K, L, H, r2)))} == KB.KB{N.nmul(L, KH.hmap(K, L, H, c1), KH.hmap(K, L, H, c2)), _} : KB.KB<L>}
      {==}

def blook_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, xs: List<&2, KB.KB<K>>, i: Nat) -> {KB.blook(~L, KH.hbv(~K, ~L, ~H, xs), i) == KH.hball(~K, ~L, ~H, KB.blook(~K, xs, i)) : KB.KB<L>}:
  match xs i:
    case Nil{} j:
      bzero_h(~K, ~L, ~H)
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+j:
      blook_h(~K, ~L, ~H, t, j)

def kbc_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, x: KB.KB<K>) -> {KB.KB.c(L, KH.hball(~K, ~L, ~H, x)) == KH.hmap(K, L, H, KB.KB.c(K, x)) : N.NC(L)}:
  match x:
    case KB.KB{c, r}:
      {==}

def kbr_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, x: KB.KB<K>) -> {KB.KB.r(L, KH.hball(~K, ~L, ~H, x)) == KH.hmap(K, L, H, KB.KB.r(K, x)) : N.NC(L)}:
  match x:
    case KB.KB{c, r}:
      {==}

def bcenters_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, u: List<&2, KB.KB<K>>) -> {KB.bcenters(~L, KH.hbv(~K, ~L, ~H, u)) == KH.hv(~K, ~L, ~H, KB.bcenters(~K, u)) : N.KVec(~L)}:
  match u:
    case Nil{}:
      {==}
    case Con{+a, +us}:
      %kbc_h(~K, ~L, ~H, a) : {Con{KB.KB.c(L, KH.hball(~K, ~L, ~H, a)), KB.bcenters(~L, KH.hbv(~K, ~L, ~H, us))} == Con{_, KH.hv(~K, ~L, ~H, KB.bcenters(~K, us))} : N.KVec(~L)}
      %bcenters_h(~K, ~L, ~H, us) : {Con{KB.KB.c(L, KH.hball(~K, ~L, ~H, a)), KB.bcenters(~L, KH.hbv(~K, ~L, ~H, us))} == Con{KB.KB.c(L, KH.hball(~K, ~L, ~H, a)), _} : N.KVec(~L)}
      {==}

def bradii_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, u: List<&2, KB.KB<K>>) -> {KB.bradii(~L, KH.hbv(~K, ~L, ~H, u)) == KH.hv(~K, ~L, ~H, KB.bradii(~K, u)) : N.KVec(~L)}:
  match u:
    case Nil{}:
      {==}
    case Con{+a, +us}:
      %kbr_h(~K, ~L, ~H, a) : {Con{KB.KB.r(L, KH.hball(~K, ~L, ~H, a)), KB.bradii(~L, KH.hbv(~K, ~L, ~H, us))} == Con{_, KH.hv(~K, ~L, ~H, KB.bradii(~K, us))} : N.KVec(~L)}
      %bradii_h(~K, ~L, ~H, us) : {Con{KB.KB.r(L, KH.hball(~K, ~L, ~H, a)), KB.bradii(~L, KH.hbv(~K, ~L, ~H, us))} == Con{KB.KB.r(L, KH.hball(~K, ~L, ~H, a)), _} : N.KVec(~L)}
      {==}

# Constants and values
# --------------------

# L's Maybe of a constant is the image of K's
def ofq_r(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +q: S.Q) -> {KH.mmap(~K, ~L, KH.hmap(K, L, H), N.nofq(K, q)) == N.nofq(L, q) : Maybe<&2, N.NC(L)>}:
  Equal.sym(Maybe<&2, N.NC(L)>, N.nofq(L, q), KH.mmap(~K, ~L, KH.hmap(K, L, H), N.nofq(K, q)), KH.h_ofq(K, L, H)(q))

def kcst_go_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, m: Maybe<&2, N.NC(K)>) -> {KB.kcst.go(~L, KH.mmap(~K, ~L, KH.hmap(K, L, H), m)) == KH.hmap(K, L, H, KB.kcst.go(~K, m)) : N.NC(L)}:
  match m:
    case None{}:
      KH.h_zero(K, L, H)
    case Some{x}:
      {==}

def kcst_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +q: S.Q) -> {KB.kcst(~L, q) == KH.hmap(K, L, H, KB.kcst(~K, q)) : N.NC(L)}:
  %ofq_r(~K, ~L, ~H, q) : {KB.kcst.go(~L, _) == KH.hmap(K, L, H, KB.kcst(~K, q)) : N.NC(L)}
  kcst_go_h(~K, ~L, ~H, N.nofq(K, q))

def held_go_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, m: Maybe<&2, N.NC(K)>) -> {KB.held.go(~L, KH.mmap(~K, ~L, KH.hmap(K, L, H), m)) == KB.held.go(~K, m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def held_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, e: E.QExpr) -> {KB.held(~L, e) == KB.held(~K, e) : Bool}:
  match e:
    case E.QVar{i}:
      {==}
    case E.QCst{+q}:
      %ofq_r(~K, ~L, ~H, q) : {KB.held.go(~L, _) == KB.held(~K, E.QCst{q}) : Bool}
      held_go_h(~K, ~L, ~H, N.nofq(K, q))
    case E.QAdd{+a, +b}:
      %held_h(~K, ~L, ~H, a) : {KA.band(KB.held(~L, a), KB.held(~L, b)) == KA.band(_, KB.held(~K, b)) : Bool}
      %held_h(~K, ~L, ~H, b) : {KA.band(KB.held(~L, a), KB.held(~L, b)) == KA.band(KB.held(~L, a), _) : Bool}
      {==}
    case E.QSub{+a, +b}:
      %held_h(~K, ~L, ~H, a) : {KA.band(KB.held(~L, a), KB.held(~L, b)) == KA.band(_, KB.held(~K, b)) : Bool}
      %held_h(~K, ~L, ~H, b) : {KA.band(KB.held(~L, a), KB.held(~L, b)) == KA.band(KB.held(~L, a), _) : Bool}
      {==}
    case E.QMul{+a, +b}:
      %held_h(~K, ~L, ~H, a) : {KA.band(KB.held(~L, a), KB.held(~L, b)) == KA.band(_, KB.held(~K, b)) : Bool}
      %held_h(~K, ~L, ~H, b) : {KA.band(KB.held(~L, a), KB.held(~L, b)) == KA.band(KB.held(~L, a), _) : Bool}
      {==}
    case E.QNeg{a}:
      held_h(~K, ~L, ~H, a)

def klook_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, xs: N.KVec(~K), i: Nat) -> {KB.klook(~L, KH.hv(~K, ~L, ~H, xs), i) == KH.hmap(K, L, H, KB.klook(~K, xs, i)) : N.NC(L)}:
  match xs i:
    case Nil{} j:
      KH.h_zero(K, L, H)
    case Con{x, t} 0n:
      {==}
    case Con{x, t} 1n+j:
      klook_h(~K, ~L, ~H, t, j)

def keval_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +env: N.KVec(~K), e: E.QExpr) -> {KB.keval(~L, KH.hv(~K, ~L, ~H, env), e) == KH.hmap(K, L, H, KB.keval(~K, env, e)) : N.NC(L)}:
  match e:
    case E.QVar{i}:
      klook_h(~K, ~L, ~H, env, i)
    case E.QCst{q}:
      kcst_h(~K, ~L, ~H, q)
    case E.QAdd{+a, +b}:
      %KH.h_add(K, L, H)(KB.keval(~K, env, a), KB.keval(~K, env, b)) : {N.nadd(L, KB.keval(~L, KH.hv(~K, ~L, ~H, env), a), KB.keval(~L, KH.hv(~K, ~L, ~H, env), b)) == _ : N.NC(L)}
      %keval_h(~K, ~L, ~H, env, a) : {N.nadd(L, KB.keval(~L, KH.hv(~K, ~L, ~H, env), a), KB.keval(~L, KH.hv(~K, ~L, ~H, env), b)) == N.nadd(L, _, KH.hmap(K, L, H, KB.keval(~K, env, b))) : N.NC(L)}
      %keval_h(~K, ~L, ~H, env, b) : {N.nadd(L, KB.keval(~L, KH.hv(~K, ~L, ~H, env), a), KB.keval(~L, KH.hv(~K, ~L, ~H, env), b)) == N.nadd(L, KB.keval(~L, KH.hv(~K, ~L, ~H, env), a), _) : N.NC(L)}
      {==}
    case E.QSub{+a, +b}:
      %ksub_h(~K, ~L, ~H, KB.keval(~K, env, a), KB.keval(~K, env, b)) : {KA.ksub(~L, KB.keval(~L, KH.hv(~K, ~L, ~H, env), a), KB.keval(~L, KH.hv(~K, ~L, ~H, env), b)) == _ : N.NC(L)}
      %keval_h(~K, ~L, ~H, env, a) : {KA.ksub(~L, KB.keval(~L, KH.hv(~K, ~L, ~H, env), a), KB.keval(~L, KH.hv(~K, ~L, ~H, env), b)) == KA.ksub(~L, _, KH.hmap(K, L, H, KB.keval(~K, env, b))) : N.NC(L)}
      %keval_h(~K, ~L, ~H, env, b) : {KA.ksub(~L, KB.keval(~L, KH.hv(~K, ~L, ~H, env), a), KB.keval(~L, KH.hv(~K, ~L, ~H, env), b)) == KA.ksub(~L, KB.keval(~L, KH.hv(~K, ~L, ~H, env), a), _) : N.NC(L)}
      {==}
    case E.QMul{+a, +b}:
      %KH.h_mul(K, L, H)(KB.keval(~K, env, a), KB.keval(~K, env, b)) : {N.nmul(L, KB.keval(~L, KH.hv(~K, ~L, ~H, env), a), KB.keval(~L, KH.hv(~K, ~L, ~H, env), b)) == _ : N.NC(L)}
      %keval_h(~K, ~L, ~H, env, a) : {N.nmul(L, KB.keval(~L, KH.hv(~K, ~L, ~H, env), a), KB.keval(~L, KH.hv(~K, ~L, ~H, env), b)) == N.nmul(L, _, KH.hmap(K, L, H, KB.keval(~K, env, b))) : N.NC(L)}
      %keval_h(~K, ~L, ~H, env, b) : {N.nmul(L, KB.keval(~L, KH.hv(~K, ~L, ~H, env), a), KB.keval(~L, KH.hv(~K, ~L, ~H, env), b)) == N.nmul(L, KB.keval(~L, KH.hv(~K, ~L, ~H, env), a), _) : N.NC(L)}
      {==}
    case E.QNeg{+a}:
      %KH.h_neg(K, L, H)(KB.keval(~K, env, a)) : {N.nneg(L, KB.keval(~L, KH.hv(~K, ~L, ~H, env), a)) == _ : N.NC(L)}
      %keval_h(~K, ~L, ~H, env, a) : {N.nneg(L, KB.keval(~L, KH.hv(~K, ~L, ~H, env), a)) == N.nneg(L, _) : N.NC(L)}
      {==}

# Balls of values and slopes
# --------------------------

def kball_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +box: List<&2, KB.KB<K>>, e: E.QExpr) -> {KB.kball(~L, KH.hbv(~K, ~L, ~H, box), e) == KH.hball(~K, ~L, ~H, KB.kball(~K, box, e)) : KB.KB<L>}:
  match e:
    case E.QVar{i}:
      blook_h(~K, ~L, ~H, box, i)
    case E.QCst{+q}:
      %kcst_h(~K, ~L, ~H, q) : {KB.KB{KB.kcst(~L, q), N.nzero(L)} == KB.KB{_, KH.hmap(K, L, H, N.nzero(K))} : KB.KB<L>}
      %KH.h_zero(K, L, H) : {KB.KB{KB.kcst(~L, q), N.nzero(L)} == KB.KB{KB.kcst(~L, q), _} : KB.KB<L>}
      {==}
    case E.QAdd{+a, +b}:
      %badd_h(~K, ~L, ~H, KB.kball(~K, box, a), KB.kball(~K, box, b)) : {KB.badd(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.kball(~L, KH.hbv(~K, ~L, ~H, box), b)) == _ : KB.KB<L>}
      %kball_h(~K, ~L, ~H, box, a) : {KB.badd(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.kball(~L, KH.hbv(~K, ~L, ~H, box), b)) == KB.badd(~L, _, KH.hball(~K, ~L, ~H, KB.kball(~K, box, b))) : KB.KB<L>}
      %kball_h(~K, ~L, ~H, box, b) : {KB.badd(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.kball(~L, KH.hbv(~K, ~L, ~H, box), b)) == KB.badd(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), _) : KB.KB<L>}
      {==}
    case E.QSub{+a, +b}:
      %badd_h(~K, ~L, ~H, KB.kball(~K, box, a), KB.bneg(~K, KB.kball(~K, box, b))) : {KB.badd(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.bneg(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), b))) == _ : KB.KB<L>}
      %kball_h(~K, ~L, ~H, box, a) : {KB.badd(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.bneg(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), b))) == KB.badd(~L, _, KH.hball(~K, ~L, ~H, KB.bneg(~K, KB.kball(~K, box, b)))) : KB.KB<L>}
      %bneg_h(~K, ~L, ~H, KB.kball(~K, box, b)) : {KB.badd(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.bneg(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), b))) == KB.badd(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), _) : KB.KB<L>}
      %kball_h(~K, ~L, ~H, box, b) : {KB.badd(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.bneg(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), b))) == KB.badd(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.bneg(~L, _)) : KB.KB<L>}
      {==}
    case E.QMul{+a, +b}:
      %bmul_h(~K, ~L, ~H, KB.kball(~K, box, a), KB.kball(~K, box, b)) : {KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.kball(~L, KH.hbv(~K, ~L, ~H, box), b)) == _ : KB.KB<L>}
      %kball_h(~K, ~L, ~H, box, a) : {KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.kball(~L, KH.hbv(~K, ~L, ~H, box), b)) == KB.bmul(~L, _, KH.hball(~K, ~L, ~H, KB.kball(~K, box, b))) : KB.KB<L>}
      %kball_h(~K, ~L, ~H, box, b) : {KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.kball(~L, KH.hbv(~K, ~L, ~H, box), b)) == KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), _) : KB.KB<L>}
      {==}
    case E.QNeg{+a}:
      %bneg_h(~K, ~L, ~H, KB.kball(~K, box, a)) : {KB.bneg(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a)) == _ : KB.KB<L>}
      %kball_h(~K, ~L, ~H, box, a) : {KB.bneg(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a)) == KB.bneg(~L, _) : KB.KB<L>}
      {==}

def kind_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, b: Bool) -> {KB.kind(~L, b) == KH.hball(~K, ~L, ~H, KB.kind(~K, b)) : KB.KB<L>}:
  match b:
    case True{}:
      %KH.h_one(K, L, H) : {KB.KB{N.none(L), N.nzero(L)} == KB.KB{_, KH.hmap(K, L, H, N.nzero(K))} : KB.KB<L>}
      %KH.h_zero(K, L, H) : {KB.KB{N.none(L), N.nzero(L)} == KB.KB{N.none(L), _} : KB.KB<L>}
      {==}
    case False{}:
      bzero_h(~K, ~L, ~H)


def ksl_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +i: Nat, +box: List<&2, KB.KB<K>>, e: E.QExpr) -> {KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), e) == KH.hball(~K, ~L, ~H, KB.ksl(~K, i, box, e)) : KB.KB<L>}:
  match e:
    case E.QVar{j}:
      kind_h(~K, ~L, ~H, KA.nateq(i, j))
    case E.QCst{q}:
      bzero_h(~K, ~L, ~H)
    case E.QAdd{+a, +b}:
      %badd_h(~K, ~L, ~H, KB.ksl(~K, i, box, a), KB.ksl(~K, i, box, b)) : {KB.badd(~L, KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), b)) == _ : KB.KB<L>}
      %ksl_h(~K, ~L, ~H, i, box, a) : {KB.badd(~L, KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), b)) == KB.badd(~L, _, KH.hball(~K, ~L, ~H, KB.ksl(~K, i, box, b))) : KB.KB<L>}
      %ksl_h(~K, ~L, ~H, i, box, b) : {KB.badd(~L, KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), b)) == KB.badd(~L, KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a), _) : KB.KB<L>}
      {==}
    case E.QSub{+a, +b}:
      %badd_h(~K, ~L, ~H, KB.ksl(~K, i, box, a), KB.bneg(~K, KB.ksl(~K, i, box, b))) : {KB.badd(~L, KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a), KB.bneg(~L, KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), b))) == _ : KB.KB<L>}
      %ksl_h(~K, ~L, ~H, i, box, a) : {KB.badd(~L, KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a), KB.bneg(~L, KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), b))) == KB.badd(~L, _, KH.hball(~K, ~L, ~H, KB.bneg(~K, KB.ksl(~K, i, box, b)))) : KB.KB<L>}
      %bneg_h(~K, ~L, ~H, KB.ksl(~K, i, box, b)) : {KB.badd(~L, KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a), KB.bneg(~L, KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), b))) == KB.badd(~L, KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a), _) : KB.KB<L>}
      %ksl_h(~K, ~L, ~H, i, box, b) : {KB.badd(~L, KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a), KB.bneg(~L, KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), b))) == KB.badd(~L, KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a), KB.bneg(~L, _)) : KB.KB<L>}
      {==}
    case E.QMul{+a, +b}:
      %badd_h(~K, ~L, ~H, KB.bmul(~K, KB.kball(~K, box, a), KB.ksl(~K, i, box, b)), KB.bmul(~K, KB.kball(~K, box, b), KB.ksl(~K, i, box, a))) : {KB.badd(~L, KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), b)), KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), b), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a))) == _ : KB.KB<L>}
      %bmul_h(~K, ~L, ~H, KB.kball(~K, box, a), KB.ksl(~K, i, box, b)) : {KB.badd(~L, KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), b)), KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), b), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a))) == KB.badd(~L, _, KH.hball(~K, ~L, ~H, KB.bmul(~K, KB.kball(~K, box, b), KB.ksl(~K, i, box, a)))) : KB.KB<L>}
      %kball_h(~K, ~L, ~H, box, a) : {KB.badd(~L, KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), b)), KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), b), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a))) == KB.badd(~L, KB.bmul(~L, _, KH.hball(~K, ~L, ~H, KB.ksl(~K, i, box, b))), KH.hball(~K, ~L, ~H, KB.bmul(~K, KB.kball(~K, box, b), KB.ksl(~K, i, box, a)))) : KB.KB<L>}
      %ksl_h(~K, ~L, ~H, i, box, b) : {KB.badd(~L, KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), b)), KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), b), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a))) == KB.badd(~L, KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), _), KH.hball(~K, ~L, ~H, KB.bmul(~K, KB.kball(~K, box, b), KB.ksl(~K, i, box, a)))) : KB.KB<L>}
      %bmul_h(~K, ~L, ~H, KB.kball(~K, box, b), KB.ksl(~K, i, box, a)) : {KB.badd(~L, KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), b)), KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), b), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a))) == KB.badd(~L, KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), b)), _) : KB.KB<L>}
      %kball_h(~K, ~L, ~H, box, b) : {KB.badd(~L, KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), b)), KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), b), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a))) == KB.badd(~L, KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), b)), KB.bmul(~L, _, KH.hball(~K, ~L, ~H, KB.ksl(~K, i, box, a)))) : KB.KB<L>}
      %ksl_h(~K, ~L, ~H, i, box, a) : {KB.badd(~L, KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), b)), KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), b), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a))) == KB.badd(~L, KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), a), KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), b)), KB.bmul(~L, KB.kball(~L, KH.hbv(~K, ~L, ~H, box), b), _)) : KB.KB<L>}
      {==}
    case E.QNeg{+a}:
      %bneg_h(~K, ~L, ~H, KB.ksl(~K, i, box, a)) : {KB.bneg(~L, KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a)) == _ : KB.KB<L>}
      %ksl_h(~K, ~L, ~H, i, box, a) : {KB.bneg(~L, KB.ksl(~L, i, KH.hbv(~K, ~L, ~H, box), a)) == KB.bneg(~L, _) : KB.KB<L>}
      {==}

def krange_h(~K: N.Num, ~L: N.Num, ~H: KH.Hom<K, L>, +box: List<&2, KB.KB<K>>, +e: E.QExpr, cnt: Nat, +lo: Nat) -> {KB.krange(~L, KH.hbv(~K, ~L, ~H, box), e, cnt, lo) == KH.hbv(~K, ~L, ~H, KB.krange(~K, box, e, cnt, lo)) : List<&2, KB.KB<L>>}:
  match cnt:
    case 0n:
      {==}
    case 1n+k:
      %ksl_h(~K, ~L, ~H, lo, box, e) : {Con{KB.ksl(~L, lo, KH.hbv(~K, ~L, ~H, box), e), KB.krange(~L, KH.hbv(~K, ~L, ~H, box), e, k, 1n+lo)} == Con{_, KH.hbv(~K, ~L, ~H, KB.krange(~K, box, e, k, 1n+lo))} : List<&2, KB.KB<L>>}
      %krange_h(~K, ~L, ~H, box, e, k, 1n+lo) : {Con{KB.ksl(~L, lo, KH.hbv(~K, ~L, ~H, box), e), KB.krange(~L, KH.hbv(~K, ~L, ~H, box), e, k, 1n+lo)} == Con{KB.ksl(~L, lo, KH.hbv(~K, ~L, ~H, box), e), _} : List<&2, KB.KB<L>>}
      {==}
