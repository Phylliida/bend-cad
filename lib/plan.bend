# bend-cad: plans and the plan checker (DESIGN §8.2, §8.4). Untrusted: only
# the plan_* and box_sides laws say what a passing check means.
#
# A plan reads the system in block order: variables 0..np-1 are pinned
# (radius 0 in the box), and then each block in turn takes the next n
# variables as its unknowns and the next n equations as its own. A block
# names its parameters (pars: earlier variables its equations use) and
# carries a certificate (spec/cert.bend) for its equations renumbered
# locally: unknowns 0..n-1, then the parameters in the order listed. The
# checker requires, besides each certificate's check: every equation of a
# block uses only earlier variables and its own unknowns, the certificate's
# box is the plan's box on the block's unknowns, each parameter's ball
# contains the plan's box on that variable, the pinned variables have
# radius 0, and blocks and equations run out together at the last
# variable. (A system in another order is renumbered first; that layer is
# separate.)

import Base
import ../spec/ring.bend as E
import ../spec/knum.bend as N
import ../spec/cert.bend as C
import ../spec/sketch.bend as SK
import ./karith.bend as KA
import ./kball.bend as KB
import ./cert.bend as CK
import ./slope.bend as SL

type PBlock<-K: N.Num> is Data:
  PBlock{n: Nat, pars: List<&2, Nat>, cert: C.Cert<K>}

type Plan<-K: N.Num> is Data:
  Plan{np: Nat, blocks: List<&2, PBlock<K>>}

# Local numbering
# ---------------

def pred(v: Nat) -> Nat:
  match v:
    case 0n:
      0n
    case 1n+w:
      w

# v - o (0 when v < o)
def minus(o: Nat, v: Nat) -> Nat:
  match o:
    case 0n:
      v
    case 1n+k:
      minus(k, pred(v))

def pos.go(b: Bool, rest: Nat) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      1n+rest

# the position of v in pars (its length when v is absent)
def pos(+v: Nat, pars: List<&2, Nat>) -> Nat:
  match pars:
    case Nil{}:
      0n
    case Con{h, t}:
      pos.go(KA.nateq(v, h), pos(v, t))

# variable v's local number in a block with offset o, n unknowns and
# parameters pars: v - o for an unknown, n + its position for a parameter
def loc.go(b: Bool, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +v: Nat) -> Nat:
  match b:
    case True{}:
      Nat.add(n, pos(v, pars))
    case False{}:
      minus(o, v)

def loc(+o: Nat, +n: Nat, +pars: List<&2, Nat>, +v: Nat) -> Nat:
  loc.go(KA.natle(1n+v, o), o, n, pars, v)

def rename(+o: Nat, +n: Nat, +pars: List<&2, Nat>, e: E.QExpr) -> E.QExpr:
  match e:
    case E.QVar{v}:
      E.QVar{loc(o, n, pars, v)}
    case E.QCst{q}:
      E.QCst{q}
    case E.QAdd{a, b}:
      E.QAdd{rename(o, n, pars, a), rename(o, n, pars, b)}
    case E.QSub{a, b}:
      E.QSub{rename(o, n, pars, a), rename(o, n, pars, b)}
    case E.QMul{a, b}:
      E.QMul{rename(o, n, pars, a), rename(o, n, pars, b)}
    case E.QNeg{a}:
      E.QNeg{rename(o, n, pars, a)}

def renames(+o: Nat, +n: Nat, +pars: List<&2, Nat>, es: List<&2, E.QExpr>) -> List<&2, E.QExpr>:
  match es:
    case Nil{}:
      Nil{}
    case Con{e, t}:
      Con{rename(o, n, pars, e), renames(o, n, pars, t)}

# Lists of equations and of numbers
# ---------------------------------

def takeq(n: Nat, es: List<&2, E.QExpr>) -> List<&2, E.QExpr>:
  match n es:
    case 0n es:
      Nil{}
    case 1n+k Nil{}:
      Nil{}
    case 1n+k Con{e, t}:
      Con{e, takeq(k, t)}

def dropq(n: Nat, es: List<&2, E.QExpr>) -> List<&2, E.QExpr>:
  match n es:
    case 0n es:
      es
    case 1n+k Nil{}:
      Nil{}
    case 1n+k Con{e, t}:
      dropq(k, t)

def isnil(es: List<&2, E.QExpr>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, t}:
      False{}

def ktake(~K: N.Num, n: Nat, u: N.KVec(~K)) -> N.KVec(~K):
  match n u:
    case 0n u:
      Nil{}
    case 1n+k Nil{}:
      Nil{}
    case 1n+k Con{a, t}:
      Con{a, ktake(~K, k, t)}

def kdrop(~K: N.Num, n: Nat, u: N.KVec(~K)) -> N.KVec(~K):
  match n u:
    case 0n u:
      u
    case 1n+k Nil{}:
      Nil{}
    case 1n+k Con{a, t}:
      kdrop(~K, k, t)

# a = b in K
def keq.go(c: Cmp) -> Bool:
  match c:
    case LT{}:
      False{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

def keq(~K: N.Num, a: N.NC(K), b: N.NC(K)) -> Bool:
  keq.go(N.ncmp(K, a, b))

# the two lists are equal entry by entry, and as long
def kveq(~K: N.Num, u: N.KVec(~K), w: N.KVec(~K)) -> Bool:
  match u w:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{b, ws}:
      False{}
    case Con{a, us} Nil{}:
      False{}
    case Con{a, us} Con{b, ws}:
      KA.band(keq(~K, a, b), kveq(~K, us, ws))

# the first np radii are 0
def pinz(~K: N.Num, np: Nat, gr: N.KVec(~K)) -> Bool:
  match np gr:
    case 0n gr:
      True{}
    case 1n+k Nil{}:
      False{}
    case 1n+k Con{r, t}:
      KA.band(keq(~K, r, N.nzero(K)), pinz(~K, k, t))

# every parameter is an earlier variable
def pars_ok(+o: Nat, pars: List<&2, Nat>) -> Bool:
  match pars:
    case Nil{}:
      True{}
    case Con{v, t}:
      KA.band(KA.natle(1n+v, o), pars_ok(o, t))

# every equation uses only variables below m
def eqs_below(+m: Nat, es: List<&2, E.QExpr>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case Con{e, t}:
      KA.band(SL.below(m, e), eqs_below(m, t))

# each parameter's ball contains the plan's box on that variable:
# |c_v - pc_k| + r_v <= pr_k
def pcont(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), pars: List<&2, Nat>, pc: N.KVec(~K), pr: N.KVec(~K)) -> Bool:
  match pars pc pr:
    case Nil{} Nil{} Nil{}:
      True{}
    case Con{+v, vs} Con{c, cs} Con{r, rs}:
      KA.band(KA.kle(~K, N.nadd(K, KA.kabs(~K, KA.ksub(~K, KB.klook(~K, gc, v), c)), KB.klook(~K, gr, v)), r), pcont(~K, gc, gr, vs, cs, rs))
    case pars pc pr:
      False{}

# The checker
# -----------

def block_ok(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), +es: List<&2, E.QExpr>, +o: Nat, +n: Nat, +pars: List<&2, Nat>, +c: C.Cert<K>) -> Bool:
  +e1 = takeq(n, es)
  KA.band(KA.natle(n, CK.eqlen(es)),
  KA.band(pars_ok(o, pars),
  KA.band(eqs_below(Nat.add(o, n), e1),
  KA.band(CK.check(~K, C.Block{renames(o, n, pars, e1), n}, c),
  KA.band(kveq(~K, C.Cert.yc(K, c), ktake(~K, n, kdrop(~K, o, gc))),
  KA.band(kveq(~K, KA.kfit(~K, n, C.Cert.yr(K, c)), ktake(~K, n, kdrop(~K, o, gr))),
  pcont(~K, gc, gr, pars, C.Cert.pc(K, c), C.Cert.pr(K, c))))))))

def walk(~K: N.Num, +gc: N.KVec(~K), +gr: N.KVec(~K), bs: List<&2, PBlock<K>>, +es: List<&2, E.QExpr>, +o: Nat) -> Bool:
  match bs:
    case Nil{}:
      KA.band(KA.nateq(o, KA.klen(~K, gc)), isnil(es))
    case Con{PBlock{+n, +pars, +c}, t}:
      KA.band(block_ok(~K, gc, gr, es, o, n, pars, c), walk(~K, gc, gr, t, dropq(n, es), Nat.add(o, n)))

# the plan checks against the system and the box
def check.p(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), +np: Nat, bs: List<&2, PBlock<K>>) -> Bool:
  KA.band(KA.nateq(KA.klen(~K, gr), KA.klen(~K, gc)),
  KA.band(KA.kvle(~K, Nil{}, gr),
  KA.band(KA.natle(np, KA.klen(~K, gc)),
  KA.band(pinz(~K, np, gr),
  walk(~K, gc, gr, bs, eqs, np)))))

def check(~K: N.Num, +eqs: List<&2, E.QExpr>, +gc: N.KVec(~K), +gr: N.KVec(~K), p: Plan<K>) -> Bool:
  match p:
    case Plan{+np, bs}:
      check.p(~K, eqs, gc, gr, np, bs)

# Side conditions over the box
# -----------------------------

# the ball of e over the box lies above 0 (or not below it)
def side_ok(~K: N.Num, +box: List<&2, KB.KB<K>>, s: SK.Side) -> Bool:
  match s:
    case SK.Gt0{+e}:
      KA.band(KB.held(~K, e), KA.klt(~K, N.nzero(K), KA.ksub(~K, KB.KB.c(K, KB.kball(~K, box, e)), KB.KB.r(K, KB.kball(~K, box, e)))))
    case SK.Ge0{+e}:
      KA.band(KB.held(~K, e), KA.kle(~K, N.nzero(K), KA.ksub(~K, KB.KB.c(K, KB.kball(~K, box, e)), KB.KB.r(K, KB.kball(~K, box, e)))))

def sides_ok(~K: N.Num, +box: List<&2, KB.KB<K>>, ss: List<&2, SK.Side>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case Con{s, t}:
      KA.band(side_ok(~K, box, s), sides_ok(~K, box, t))

# every side condition holds over the box (radii not negative)
def check_sides(~K: N.Num, +sides: List<&2, SK.Side>, +gc: N.KVec(~K), +gr: N.KVec(~K)) -> Bool:
  KA.band(KA.kvle(~K, Nil{}, gr), sides_ok(~K, CK.zipb(~K, gc, gr), sides))

# Lists of numbers
# ----------------

def nlen(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+nlen(t)

def nthn(xs: List<&2, Nat>, k: Nat) -> Nat:
  match xs k:
    case Nil{} k:
      0n
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      nthn(t, j)
