# A reflective normalizer for Nat semiring identities, proven sound.
#
# An NExpr is a polynomial expression over variables numbered into an
# environment. norm turns it into a sorted list of terms (coefficient,
# sorted monomial) with like terms merged and zero terms dropped, so equal
# polynomials normalize to the same list. Only soundness is proven:
# ring_eq turns {norm(e1) == norm(e2)} (checked by {==}, i.e. computed) into
# {eval(env, e1) == eval(env, e2)}. Canonicity is not proven; it only decides
# whether {==} succeeds.
#
# This is the bootstrap normalizer: its coefficients are unary, so it is
# meant for small constants. The binary-coefficient normalizer over the spec
# integers is lib/zring.bend.

import Base
import ./nat.bend as N

# Expressions and their meaning
# -----------------------------

type NExpr is Data:
  NVar{i: Nat}
  NCst{c: Nat}
  NAdd{a: NExpr, b: NExpr}
  NMul{a: NExpr, b: NExpr}
  NDbl{a: NExpr}

# the i-th entry of env, 0n past its end
def lookup(env: List<&2, Nat>, i: Nat) -> Nat:
  match env i:
    case Nil{} j:
      0n
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      lookup(t, j)

def eval(+env: List<&2, Nat>, e: NExpr) -> Nat:
  match e:
    case NVar{i}:
      lookup(env, i)
    case NCst{c}:
      c
    case NAdd{a, b}:
      Nat.add(eval(env, a), eval(env, b))
    case NMul{a, b}:
      Nat.mul(eval(env, a), eval(env, b))
    case NDbl{a}:
      Nat.double(eval(env, a))

# Monomials: ascending lists of variable numbers
# ---------------------------------------------

def emono(+env: List<&2, Nat>, m: List<&2, Nat>) -> Nat:
  match m:
    case Nil{}:
      1n
    case Con{v, vs}:
      Nat.mul(lookup(env, v), emono(env, vs))

# where x goes against the head h, given b = x <= h; r is x inserted into t
def minsert.dec(b: Bool, x: Nat, h: Nat, t: List<&2, Nat>, r: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      Con{x, Con{h, t}}
    case False{}:
      Con{h, r}

def minsert(+x: Nat, m: List<&2, Nat>) -> List<&2, Nat>:
  match m:
    case Nil{}:
      Con{x, Nil{}}
    case Con{+h, +t}:
      minsert.dec(Nat.is_le(x, h), x, h, t, minsert(x, t))

def mmul(m1: List<&2, Nat>, m2: List<&2, Nat>) -> List<&2, Nat>:
  match m1:
    case Nil{}:
      m2
    case Con{v, vs}:
      minsert(v, mmul(vs, m2))

# lexicographic order on monomials
def mcmp.dec(o: Cmp, r: Cmp) -> Cmp:
  match o:
    case LT{}:
      LT{}
    case EQ{}:
      r
    case GT{}:
      GT{}

def mcmp(m: List<&2, Nat>, n: List<&2, Nat>) -> Cmp:
  match m n:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{y, ys}:
      LT{}
    case Con{x, xs} Nil{}:
      GT{}
    case Con{x, xs} Con{y, ys}:
      mcmp.dec(Nat.cmp(x, y), mcmp(xs, ys))

# Polynomials: lists of terms, ascending by monomial
# --------------------------------------------------

type NTerm is Data:
  NTerm{c: Nat, m: List<&2, Nat>}

def epoly(+env: List<&2, Nat>, p: List<&2, NTerm>) -> Nat:
  match p:
    case Nil{}:
      0n
    case Con{NTerm{c, m}, rest}:
      Nat.add(Nat.mul(c, emono(env, m)), epoly(env, rest))

# a merged term of coefficient s, dropped when s is zero
def pcoef(s: Nat, n: List<&2, Nat>, rest: List<&2, NTerm>) -> List<&2, NTerm>:
  match s:
    case 0n:
      rest
    case 1n+k:
      Con{NTerm{1n+k, n}, rest}

# where the term c*m goes against the head d*n, given o = mcmp(m, n); r is
# c*m inserted into rest
def pins.dec(o: Cmp, c: Nat, m: List<&2, Nat>, d: Nat, n: List<&2, Nat>, rest: List<&2, NTerm>, r: List<&2, NTerm>) -> List<&2, NTerm>:
  match o:
    case LT{}:
      Con{NTerm{c, m}, Con{NTerm{d, n}, rest}}
    case EQ{}:
      pcoef(Nat.add(c, d), n, rest)
    case GT{}:
      Con{NTerm{d, n}, r}

def pins(+c: Nat, +m: List<&2, Nat>, p: List<&2, NTerm>) -> List<&2, NTerm>:
  match p:
    case Nil{}:
      Con{NTerm{c, m}, Nil{}}
    case Con{NTerm{+d, +n}, +rest}:
      pins.dec(mcmp(m, n), c, m, d, n, rest, pins(c, m, rest))

# adds the term c*m to p, dropping it when c is zero
def pinsert(c: Nat, m: List<&2, Nat>, p: List<&2, NTerm>) -> List<&2, NTerm>:
  match c:
    case 0n:
      p
    case 1n+k:
      pins(1n+k, m, p)

def padd(p: List<&2, NTerm>, q: List<&2, NTerm>) -> List<&2, NTerm>:
  match p:
    case Nil{}:
      q
    case Con{NTerm{c, m}, rest}:
      pinsert(c, m, padd(rest, q))

# the product of the term c*m with q
def pscale(+c: Nat, +m: List<&2, Nat>, q: List<&2, NTerm>) -> List<&2, NTerm>:
  match q:
    case Nil{}:
      Nil{}
    case Con{NTerm{d, n}, rest}:
      pinsert(Nat.mul(c, d), mmul(m, n), pscale(c, m, rest))

def pmul(p: List<&2, NTerm>, +q: List<&2, NTerm>) -> List<&2, NTerm>:
  match p:
    case Nil{}:
      Nil{}
    case Con{NTerm{c, m}, rest}:
      padd(pscale(c, m, q), pmul(rest, q))

def pconst(c: Nat) -> List<&2, NTerm>:
  match c:
    case 0n:
      Nil{}
    case 1n+k:
      Con{NTerm{1n+k, Nil{}}, Nil{}}

def norm(e: NExpr) -> List<&2, NTerm>:
  match e:
    case NVar{i}:
      Con{NTerm{1n, Con{i, Nil{}}}, Nil{}}
    case NCst{c}:
      pconst(c)
    case NAdd{a, b}:
      padd(norm(a), norm(b))
    case NMul{a, b}:
      pmul(norm(a), norm(b))
    case NDbl{a}:
      pmul(pconst(2n), norm(a))

# Refutations
# -----------

# a type picked by a Cmp: a rewrite through it refutes EQ{} == LT{} and kin
def CmpD(o: Cmp, l: Type, e: Type, g: Type) -> Type:
  match o:
    case LT{}:
      l
    case EQ{}:
      e
    case GT{}:
      g

# Soundness
# ---------

def nat_cmp_eq(a: Nat, b: Nat, e: {EQ{} == Nat.cmp(a, b) : Cmp}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      %e : CmpD(_, {0n == 1n+q : Nat}, Unit, Unit)
      Unit{}
    case 1n+p 0n:
      %e : CmpD(_, Unit, Unit, {1n+p == 0n : Nat})
      Unit{}
    case 1n+p 1n+q:
      %nat_cmp_eq(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

# the cons case of mcmp_eq, given the verdict o of Nat.cmp(x, y)
def mcmp_eq.dec(o: Cmp, x: Nat, y: Nat, -xs: List<&2, Nat>, -ys: List<&2, Nat>,
  eo: {o == Nat.cmp(x, y) : Cmp}, e: {EQ{} == mcmp.dec(o, mcmp(xs, ys)) : Cmp},
  rec: {EQ{} == mcmp(xs, ys) : Cmp} -> {xs == ys : List<&2, Nat>})
  -> {Con{x, xs} == Con{y, ys} : List<&2, Nat>}:
  match o:
    case LT{}:
      %e : CmpD(_, {Con{x, xs} == Con{y, ys} : List<&2, Nat>}, Unit, Unit)
      Unit{}
    case EQ{}:
      %rec(e) : {Con{x, xs} == Con{y, _} : List<&2, Nat>}
      %nat_cmp_eq(x, y, eo) : {Con{x, xs} == Con{_, xs} : List<&2, Nat>}
      {==}
    case GT{}:
      %e : CmpD(_, Unit, Unit, {Con{x, xs} == Con{y, ys} : List<&2, Nat>})
      Unit{}

def mcmp_eq(m: List<&2, Nat>, n: List<&2, Nat>, e: {EQ{} == mcmp(m, n) : Cmp}) -> {m == n : List<&2, Nat>}:
  match m n:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      %e : CmpD(_, {Nil{} == Con{y, ys} : List<&2, Nat>}, Unit, Unit)
      Unit{}
    case Con{x, xs} Nil{}:
      %e : CmpD(_, Unit, Unit, {Con{x, xs} == Nil{} : List<&2, Nat>})
      Unit{}
    case Con{+x, +xs} Con{+y, +ys}:
      mcmp_eq.dec(Nat.cmp(x, y), x, y, xs, ys, {==}, e, ee => mcmp_eq(xs, ys, ee))

def minsert_ok.dec(+env: List<&2, Nat>, b: Bool, +x: Nat, +h: Nat, +t: List<&2, Nat>,
  rec: {Nat.mul(lookup(env, x), emono(env, t)) == emono(env, minsert(x, t)) : Nat})
  -> {Nat.mul(lookup(env, x), Nat.mul(lookup(env, h), emono(env, t))) == emono(env, minsert.dec(b, x, h, t, minsert(x, t))) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      %rec : {Nat.mul(lookup(env, x), Nat.mul(lookup(env, h), emono(env, t))) == Nat.mul(lookup(env, h), _) : Nat}
      N.mul_swap(lookup(env, x), lookup(env, h), emono(env, t))

def minsert_ok(+env: List<&2, Nat>, +x: Nat, m: List<&2, Nat>) -> {Nat.mul(lookup(env, x), emono(env, m)) == emono(env, minsert(x, m)) : Nat}:
  match m:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      minsert_ok.dec(env, Nat.is_le(x, h), x, h, t, minsert_ok(env, x, t))

def mmul_ok(+env: List<&2, Nat>, m1: List<&2, Nat>, +m2: List<&2, Nat>) -> {Nat.mul(emono(env, m1), emono(env, m2)) == emono(env, mmul(m1, m2)) : Nat}:
  match m1:
    case Nil{}:
      %N.add_zero(emono(env, m2)) : {_ == emono(env, m2) : Nat}
      {==}
    case Con{+v, +vs}:
      %minsert_ok(env, v, mmul(vs, m2)) : {Nat.mul(Nat.mul(lookup(env, v), emono(env, vs)), emono(env, m2)) == _ : Nat}
      %mmul_ok(env, vs, m2) : {Nat.mul(Nat.mul(lookup(env, v), emono(env, vs)), emono(env, m2)) == Nat.mul(lookup(env, v), _) : Nat}
      %N.mul_assoc(lookup(env, v), emono(env, vs), emono(env, m2)) : {_ == Nat.mul(lookup(env, v), Nat.mul(emono(env, vs), emono(env, m2))) : Nat}
      {==}

def pcoef_ok(+env: List<&2, Nat>, s: Nat, -n: List<&2, Nat>, -rest: List<&2, NTerm>) -> {Nat.add(Nat.mul(s, emono(env, n)), epoly(env, rest)) == epoly(env, pcoef(s, n, rest)) : Nat}:
  match s:
    case 0n:
      {==}
    case 1n+k:
      {==}

def pins_ok.dec(+env: List<&2, Nat>, o: Cmp, +c: Nat, +m: List<&2, Nat>, +d: Nat, +n: List<&2, Nat>, +rest: List<&2, NTerm>,
  e: {o == mcmp(m, n) : Cmp},
  rec: {Nat.add(Nat.mul(c, emono(env, m)), epoly(env, rest)) == epoly(env, pins(c, m, rest)) : Nat})
  -> {Nat.add(Nat.mul(c, emono(env, m)), Nat.add(Nat.mul(d, emono(env, n)), epoly(env, rest))) == epoly(env, pins.dec(o, c, m, d, n, rest, pins(c, m, rest))) : Nat}:
  match o:
    case LT{}:
      {==}
    case EQ{}:
      %pcoef_ok(env, Nat.add(c, d), n, rest) : {Nat.add(Nat.mul(c, emono(env, m)), Nat.add(Nat.mul(d, emono(env, n)), epoly(env, rest))) == _ : Nat}
      %N.mul_add_r(c, d, emono(env, n)) : {Nat.add(Nat.mul(c, emono(env, m)), Nat.add(Nat.mul(d, emono(env, n)), epoly(env, rest))) == Nat.add(_, epoly(env, rest)) : Nat}
      %N.add_assoc(Nat.mul(c, emono(env, n)), Nat.mul(d, emono(env, n)), epoly(env, rest)) : {Nat.add(Nat.mul(c, emono(env, m)), Nat.add(Nat.mul(d, emono(env, n)), epoly(env, rest))) == _ : Nat}
      %mcmp_eq(m, n, e) : {Nat.add(Nat.mul(c, emono(env, m)), Nat.add(Nat.mul(d, emono(env, n)), epoly(env, rest))) == Nat.add(Nat.mul(c, emono(env, _)), Nat.add(Nat.mul(d, emono(env, n)), epoly(env, rest))) : Nat}
      {==}
    case GT{}:
      %rec : {Nat.add(Nat.mul(c, emono(env, m)), Nat.add(Nat.mul(d, emono(env, n)), epoly(env, rest))) == Nat.add(Nat.mul(d, emono(env, n)), _) : Nat}
      N.add_swap(Nat.mul(c, emono(env, m)), Nat.mul(d, emono(env, n)), epoly(env, rest))

def pins_ok(+env: List<&2, Nat>, +c: Nat, +m: List<&2, Nat>, p: List<&2, NTerm>) -> {Nat.add(Nat.mul(c, emono(env, m)), epoly(env, p)) == epoly(env, pins(c, m, p)) : Nat}:
  match p:
    case Nil{}:
      {==}
    case Con{NTerm{+d, +n}, +rest}:
      pins_ok.dec(env, mcmp(m, n), c, m, d, n, rest, {==}, pins_ok(env, c, m, rest))

def pinsert_ok(+env: List<&2, Nat>, c: Nat, +m: List<&2, Nat>, +p: List<&2, NTerm>) -> {Nat.add(Nat.mul(c, emono(env, m)), epoly(env, p)) == epoly(env, pinsert(c, m, p)) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+k:
      pins_ok(env, 1n+k, m, p)

def padd_ok(+env: List<&2, Nat>, p: List<&2, NTerm>, +q: List<&2, NTerm>) -> {Nat.add(epoly(env, p), epoly(env, q)) == epoly(env, padd(p, q)) : Nat}:
  match p:
    case Nil{}:
      {==}
    case Con{NTerm{+c, +m}, +rest}:
      %pinsert_ok(env, c, m, padd(rest, q)) : {Nat.add(Nat.add(Nat.mul(c, emono(env, m)), epoly(env, rest)), epoly(env, q)) == _ : Nat}
      %padd_ok(env, rest, q) : {Nat.add(Nat.add(Nat.mul(c, emono(env, m)), epoly(env, rest)), epoly(env, q)) == Nat.add(Nat.mul(c, emono(env, m)), _) : Nat}
      %N.add_assoc(Nat.mul(c, emono(env, m)), epoly(env, rest), epoly(env, q)) : {_ == Nat.add(Nat.mul(c, emono(env, m)), Nat.add(epoly(env, rest), epoly(env, q))) : Nat}
      {==}

# (a * c) * (b * d) = (a * b) * (c * d)
def mul_shuffle(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.mul(Nat.mul(a, c), Nat.mul(b, d)) == Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) : Nat}:
  %N.mul_assoc(a, b, Nat.mul(c, d)) : {Nat.mul(Nat.mul(a, c), Nat.mul(b, d)) == _ : Nat}
  %N.mul_swap(c, b, d) : {Nat.mul(Nat.mul(a, c), Nat.mul(b, d)) == Nat.mul(a, _) : Nat}
  %N.mul_assoc(a, c, Nat.mul(b, d)) : {_ == Nat.mul(a, Nat.mul(c, Nat.mul(b, d))) : Nat}
  {==}

def pscale_ok(+env: List<&2, Nat>, +c: Nat, +m: List<&2, Nat>, q: List<&2, NTerm>) -> {Nat.mul(Nat.mul(c, emono(env, m)), epoly(env, q)) == epoly(env, pscale(c, m, q)) : Nat}:
  match q:
    case Nil{}:
      %N.mul_zero(Nat.mul(c, emono(env, m))) : {_ == 0n : Nat}
      {==}
    case Con{NTerm{+d, +n}, +rest}:
      %pinsert_ok(env, Nat.mul(c, d), mmul(m, n), pscale(c, m, rest)) : {Nat.mul(Nat.mul(c, emono(env, m)), Nat.add(Nat.mul(d, emono(env, n)), epoly(env, rest))) == _ : Nat}
      %pscale_ok(env, c, m, rest) : {Nat.mul(Nat.mul(c, emono(env, m)), Nat.add(Nat.mul(d, emono(env, n)), epoly(env, rest))) == Nat.add(Nat.mul(Nat.mul(c, d), emono(env, mmul(m, n))), _) : Nat}
      %mmul_ok(env, m, n) : {Nat.mul(Nat.mul(c, emono(env, m)), Nat.add(Nat.mul(d, emono(env, n)), epoly(env, rest))) == Nat.add(Nat.mul(Nat.mul(c, d), _), Nat.mul(Nat.mul(c, emono(env, m)), epoly(env, rest))) : Nat}
      %mul_shuffle(c, d, emono(env, m), emono(env, n)) : {Nat.mul(Nat.mul(c, emono(env, m)), Nat.add(Nat.mul(d, emono(env, n)), epoly(env, rest))) == Nat.add(_, Nat.mul(Nat.mul(c, emono(env, m)), epoly(env, rest))) : Nat}
      %N.mul_add_l(Nat.mul(c, emono(env, m)), Nat.mul(d, emono(env, n)), epoly(env, rest)) : {_ == Nat.add(Nat.mul(Nat.mul(c, emono(env, m)), Nat.mul(d, emono(env, n))), Nat.mul(Nat.mul(c, emono(env, m)), epoly(env, rest))) : Nat}
      {==}

def pmul_ok(+env: List<&2, Nat>, p: List<&2, NTerm>, +q: List<&2, NTerm>) -> {Nat.mul(epoly(env, p), epoly(env, q)) == epoly(env, pmul(p, q)) : Nat}:
  match p:
    case Nil{}:
      {==}
    case Con{NTerm{+c, +m}, +rest}:
      %padd_ok(env, pscale(c, m, q), pmul(rest, q)) : {Nat.mul(Nat.add(Nat.mul(c, emono(env, m)), epoly(env, rest)), epoly(env, q)) == _ : Nat}
      %pscale_ok(env, c, m, q) : {Nat.mul(Nat.add(Nat.mul(c, emono(env, m)), epoly(env, rest)), epoly(env, q)) == Nat.add(_, epoly(env, pmul(rest, q))) : Nat}
      %pmul_ok(env, rest, q) : {Nat.mul(Nat.add(Nat.mul(c, emono(env, m)), epoly(env, rest)), epoly(env, q)) == Nat.add(Nat.mul(Nat.mul(c, emono(env, m)), epoly(env, q)), _) : Nat}
      %N.mul_add_r(Nat.mul(c, emono(env, m)), epoly(env, rest), epoly(env, q)) : {_ == Nat.add(Nat.mul(Nat.mul(c, emono(env, m)), epoly(env, q)), Nat.mul(epoly(env, rest), epoly(env, q))) : Nat}
      {==}

def pconst_ok(-env: List<&2, Nat>, c: Nat) -> {epoly(env, pconst(c)) == c : Nat}:
  match c:
    case 0n:
      {==}
    case 1n++k:
      %N.add_zero(Nat.mul(1n+k, 1n)) : {_ == 1n+k : Nat}
      %N.mul_one(1n+k) : {_ == 1n+k : Nat}
      {==}

# Nat.double as a product, for the NDbl case
def double_mul(a: Nat) -> {Nat.mul(2n, a) == Nat.double(a) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %N.add_succ(p, Nat.add(p, 0n)) : {1n+_ == 2n+Nat.double(p) : Nat}
      %double_mul(p) : {2n+Nat.add(p, Nat.add(p, 0n)) == 2n+_ : Nat}
      {==}

def norm_ok(+env: List<&2, Nat>, e: NExpr) -> {epoly(env, norm(e)) == eval(env, e) : Nat}:
  match e:
    case NVar{+i}:
      %N.add_zero(Nat.mul(1n, Nat.mul(lookup(env, i), 1n))) : {_ == lookup(env, i) : Nat}
      %N.add_zero(Nat.mul(lookup(env, i), 1n)) : {_ == lookup(env, i) : Nat}
      %N.mul_one(lookup(env, i)) : {_ == lookup(env, i) : Nat}
      {==}
    case NCst{c}:
      pconst_ok(env, c)
    case NAdd{+a, +b}:
      %norm_ok(env, a) : {epoly(env, padd(norm(a), norm(b))) == Nat.add(_, eval(env, b)) : Nat}
      %norm_ok(env, b) : {epoly(env, padd(norm(a), norm(b))) == Nat.add(epoly(env, norm(a)), _) : Nat}
      %padd_ok(env, norm(a), norm(b)) : {_ == Nat.add(epoly(env, norm(a)), epoly(env, norm(b))) : Nat}
      {==}
    case NMul{+a, +b}:
      %norm_ok(env, a) : {epoly(env, pmul(norm(a), norm(b))) == Nat.mul(_, eval(env, b)) : Nat}
      %norm_ok(env, b) : {epoly(env, pmul(norm(a), norm(b))) == Nat.mul(epoly(env, norm(a)), _) : Nat}
      %pmul_ok(env, norm(a), norm(b)) : {_ == Nat.mul(epoly(env, norm(a)), epoly(env, norm(b))) : Nat}
      {==}
    case NDbl{+a}:
      %norm_ok(env, a) : {epoly(env, pmul(pconst(2n), norm(a))) == Nat.double(_) : Nat}
      %double_mul(epoly(env, norm(a))) : {epoly(env, pmul(pconst(2n), norm(a))) == _ : Nat}
      %pmul_ok(env, pconst(2n), norm(a)) : {_ == Nat.mul(2n, epoly(env, norm(a))) : Nat}
      {==}

# The normalizer's use: two expressions with equal normal forms are equal
# under every environment. The hypothesis is checked by computation, {==}.
def ring_eq(+env: List<&2, Nat>, +e1: NExpr, +e2: NExpr, h: {norm(e1) == norm(e2) : List<&2, NTerm>}) -> {eval(env, e1) == eval(env, e2) : Nat}:
  %norm_ok(env, e1) : {_ == eval(env, e2) : Nat}
  %norm_ok(env, e2) : {epoly(env, norm(e1)) == _ : Nat}
  %h : {epoly(env, norm(e1)) == epoly(env, _) : Nat}
  {==}
