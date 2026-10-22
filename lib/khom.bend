# bend-cad: maps between two of the checker's computing numbers
# (spec/knum.bend) that commute exactly with every operation, and the
# checker's data (vectors, matrices, balls, certificates, plans) sent through
# one entry by entry. Untrusted. With such a map h : K -> L, the generic
# checker gives the same verdict on the mapped data in L as on the data in K
# (lib/khompf.bend, lib/certhpf.bend, lib/planhpf.bend): this is how the
# verdict runs on word dyadics (lib/wnum.bend) and still says exactly what
# it says on S.D (PLAN-sk13w W5).

import Base
import ../spec/num.bend as S
import ../spec/knum.bend as N
import ./kball.bend as KB
import ./certdef.bend as C
import ./plan.bend as PL

# a Maybe through a function
def mmap(~K: N.Num, ~L: N.Num, h: N.NC(K) -> N.NC(L), m: Maybe<&2, N.NC(K)>) -> Maybe<&2, N.NC(L)>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{h(x)}

# h : K -> L, sending each of K's operations to L's exactly (L's operation
# on the images is the image of K's), with the same comparisons, and L
# holding exactly the images of the rationals K holds
type Hom<-K: N.Num, -L: N.Num> is Type:
  Hom{h: N.NC(K) -> N.NC(L),
    h_zero: {N.nzero(L) == h(N.nzero(K)) : N.NC(L)},
    h_one: {N.none(L) == h(N.none(K)) : N.NC(L)},
    h_add: @a: N.NC(K) -> @b: N.NC(K) -> {N.nadd(L, h(a), h(b)) == h(N.nadd(K, a, b)) : N.NC(L)},
    h_mul: @a: N.NC(K) -> @b: N.NC(K) -> {N.nmul(L, h(a), h(b)) == h(N.nmul(K, a, b)) : N.NC(L)},
    h_neg: @a: N.NC(K) -> {N.nneg(L, h(a)) == h(N.nneg(K, a)) : N.NC(L)},
    h_cmp: @a: N.NC(K) -> @b: N.NC(K) -> {N.ncmp(L, h(a), h(b)) == N.ncmp(K, a, b) : Cmp},
    h_ofq: @q: S.Q -> {N.nofq(L, q) == mmap(~K, ~L, h, N.nofq(K, q)) : Maybe<&2, N.NC(L)>}}

def hmap(-K: N.Num, -L: N.Num, H: Hom<K, L>) -> N.NC(K) -> N.NC(L):
  match H:
    case Hom{h, h_zero, h_one, h_add, h_mul, h_neg, h_cmp, h_ofq}:
      h

def h_zero(-K: N.Num, -L: N.Num, H: Hom<K, L>) -> {N.nzero(L) == hmap(K, L, H, N.nzero(K)) : N.NC(L)}:
  match H:
    case Hom{h, h_zero, h_one, h_add, h_mul, h_neg, h_cmp, h_ofq}:
      h_zero

def h_one(-K: N.Num, -L: N.Num, H: Hom<K, L>) -> {N.none(L) == hmap(K, L, H, N.none(K)) : N.NC(L)}:
  match H:
    case Hom{h, h_zero, h_one, h_add, h_mul, h_neg, h_cmp, h_ofq}:
      h_one

def h_add(-K: N.Num, -L: N.Num, H: Hom<K, L>) -> @a: N.NC(K) -> @b: N.NC(K) -> {N.nadd(L, hmap(K, L, H, a), hmap(K, L, H, b)) == hmap(K, L, H, N.nadd(K, a, b)) : N.NC(L)}:
  match H:
    case Hom{h, h_zero, h_one, h_add, h_mul, h_neg, h_cmp, h_ofq}:
      h_add

def h_mul(-K: N.Num, -L: N.Num, H: Hom<K, L>) -> @a: N.NC(K) -> @b: N.NC(K) -> {N.nmul(L, hmap(K, L, H, a), hmap(K, L, H, b)) == hmap(K, L, H, N.nmul(K, a, b)) : N.NC(L)}:
  match H:
    case Hom{h, h_zero, h_one, h_add, h_mul, h_neg, h_cmp, h_ofq}:
      h_mul

def h_neg(-K: N.Num, -L: N.Num, H: Hom<K, L>) -> @a: N.NC(K) -> {N.nneg(L, hmap(K, L, H, a)) == hmap(K, L, H, N.nneg(K, a)) : N.NC(L)}:
  match H:
    case Hom{h, h_zero, h_one, h_add, h_mul, h_neg, h_cmp, h_ofq}:
      h_neg

def h_cmp(-K: N.Num, -L: N.Num, H: Hom<K, L>) -> @a: N.NC(K) -> @b: N.NC(K) -> {N.ncmp(L, hmap(K, L, H, a), hmap(K, L, H, b)) == N.ncmp(K, a, b) : Cmp}:
  match H:
    case Hom{h, h_zero, h_one, h_add, h_mul, h_neg, h_cmp, h_ofq}:
      h_cmp

def h_ofq(-K: N.Num, -L: N.Num, H: Hom<K, L>) -> @q: S.Q -> {N.nofq(L, q) == mmap(~K, ~L, hmap(K, L, H), N.nofq(K, q)) : Maybe<&2, N.NC(L)>}:
  match H:
    case Hom{h, h_zero, h_one, h_add, h_mul, h_neg, h_cmp, h_ofq}:
      h_ofq

# The checker's data through h
# ----------------------------

def hv(~K: N.Num, ~L: N.Num, ~H: Hom<K, L>, u: N.KVec(~K)) -> N.KVec(~L):
  match u:
    case Nil{}:
      Nil{}
    case Con{x, xs}:
      Con{hmap(K, L, H, x), hv(~K, ~L, ~H, xs)}

def hm(~K: N.Num, ~L: N.Num, ~H: Hom<K, L>, a: N.KMat(~K)) -> N.KMat(~L):
  match a:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{hv(~K, ~L, ~H, r), hm(~K, ~L, ~H, rs)}

def hball(~K: N.Num, ~L: N.Num, ~H: Hom<K, L>, x: KB.KB<K>) -> KB.KB<L>:
  match x:
    case KB.KB{c, r}:
      KB.KB{hmap(K, L, H, c), hmap(K, L, H, r)}

# a list of balls (a box, or one equation's slope enclosures)
def hbv(~K: N.Num, ~L: N.Num, ~H: Hom<K, L>, u: List<&2, KB.KB<K>>) -> List<&2, KB.KB<L>>:
  match u:
    case Nil{}:
      Nil{}
    case Con{x, xs}:
      Con{hball(~K, ~L, ~H, x), hbv(~K, ~L, ~H, xs)}

# a list of lists of balls (every equation's slope enclosures)
def hbm(~K: N.Num, ~L: N.Num, ~H: Hom<K, L>, a: List<&2, List<&2, KB.KB<K>>>) -> List<&2, List<&2, KB.KB<L>>>:
  match a:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{hbv(~K, ~L, ~H, r), hbm(~K, ~L, ~H, rs)}

def hcert(~K: N.Num, ~L: N.Num, ~H: Hom<K, L>, c: C.Cert<K>) -> C.Cert<L>:
  match c:
    case C.Cert{yc, yr, q, ym, pc, pr}:
      C.Cert{hv(~K, ~L, ~H, yc), hv(~K, ~L, ~H, yr), hmap(K, L, H, q), hm(~K, ~L, ~H, ym), hv(~K, ~L, ~H, pc), hv(~K, ~L, ~H, pr)}

def hpb(~K: N.Num, ~L: N.Num, ~H: Hom<K, L>, b: PL.PBlock<K>) -> PL.PBlock<L>:
  match b:
    case PL.PBlock{n, pars, c}:
      PL.PBlock{n, pars, hcert(~K, ~L, ~H, c)}

def hpbs(~K: N.Num, ~L: N.Num, ~H: Hom<K, L>, bs: List<&2, PL.PBlock<K>>) -> List<&2, PL.PBlock<L>>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      Con{hpb(~K, ~L, ~H, b), hpbs(~K, ~L, ~H, t)}

def hplan(~K: N.Num, ~L: N.Num, ~H: Hom<K, L>, p: PL.Plan<K>) -> PL.Plan<L>:
  match p:
    case PL.Plan{vp, ep, np, bs}:
      PL.Plan{vp, ep, np, hpbs(~K, ~L, ~H, bs)}
