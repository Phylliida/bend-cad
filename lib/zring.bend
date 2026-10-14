# A reflective normalizer for integer ring identities with binary
# coefficients, proven sound. The same algorithm as lib/natring.bend (whose
# monomial code it reuses: monomials are lists of variable numbers), over the
# spec integers, plus negation and subtraction. Its soundness uses the ring
# laws of lib/zlaws.bend.
#
# Use: ring_eq(env, e1, e2, {==}) proves {E.eval(env, e1) == E.eval(env, e2)}
# when e1 and e2 normalize alike; the {==} is checked by computation, with
# binary coefficients, so large constants stay small terms.

import Base
import ./natring.bend as NR
import ./zlaws.bend as ZL
import ../spec/num.bend as S
import ../spec/ring.bend as E

# Polynomials: lists of terms, ascending by monomial (NR.mcmp)
# ------------------------------------------------------------

def emono(+env: List<&2, S.Z>, m: List<&2, Nat>) -> S.Z:
  match m:
    case Nil{}:
      S.Zpos{S.XH{}}
    case Con{v, vs}:
      S.Z.mul(E.lookup(env, v), emono(env, vs))

type ZTerm is Data:
  ZTerm{c: S.Z, m: List<&2, Nat>}

def epoly(+env: List<&2, S.Z>, p: List<&2, ZTerm>) -> S.Z:
  match p:
    case Nil{}:
      S.Z0{}
    case Con{ZTerm{c, m}, rest}:
      S.Z.add(S.Z.mul(c, emono(env, m)), epoly(env, rest))

# a merged term of coefficient s, dropped when s is zero
def pcoef(s: S.Z, n: List<&2, Nat>, rest: List<&2, ZTerm>) -> List<&2, ZTerm>:
  match s:
    case S.Z0{}:
      rest
    case S.Zpos{p}:
      Con{ZTerm{S.Zpos{p}, n}, rest}
    case S.Zneg{p}:
      Con{ZTerm{S.Zneg{p}, n}, rest}

def pins.dec(o: Cmp, c: S.Z, m: List<&2, Nat>, d: S.Z, n: List<&2, Nat>, rest: List<&2, ZTerm>, r: List<&2, ZTerm>) -> List<&2, ZTerm>:
  match o:
    case LT{}:
      Con{ZTerm{c, m}, Con{ZTerm{d, n}, rest}}
    case EQ{}:
      pcoef(S.Z.add(c, d), n, rest)
    case GT{}:
      Con{ZTerm{d, n}, r}

def pins(+c: S.Z, +m: List<&2, Nat>, p: List<&2, ZTerm>) -> List<&2, ZTerm>:
  match p:
    case Nil{}:
      Con{ZTerm{c, m}, Nil{}}
    case Con{ZTerm{+d, +n}, +rest}:
      pins.dec(NR.mcmp(m, n), c, m, d, n, rest, pins(c, m, rest))

# adds the term c*m to p, dropping it when c is zero
def pinsert(c: S.Z, m: List<&2, Nat>, p: List<&2, ZTerm>) -> List<&2, ZTerm>:
  match c:
    case S.Z0{}:
      p
    case S.Zpos{q}:
      pins(S.Zpos{q}, m, p)
    case S.Zneg{q}:
      pins(S.Zneg{q}, m, p)

def padd(p: List<&2, ZTerm>, q: List<&2, ZTerm>) -> List<&2, ZTerm>:
  match p:
    case Nil{}:
      q
    case Con{ZTerm{c, m}, rest}:
      pinsert(c, m, padd(rest, q))

def pscale(+c: S.Z, +m: List<&2, Nat>, q: List<&2, ZTerm>) -> List<&2, ZTerm>:
  match q:
    case Nil{}:
      Nil{}
    case Con{ZTerm{d, n}, rest}:
      pinsert(S.Z.mul(c, d), NR.mmul(m, n), pscale(c, m, rest))

def pmul(p: List<&2, ZTerm>, +q: List<&2, ZTerm>) -> List<&2, ZTerm>:
  match p:
    case Nil{}:
      Nil{}
    case Con{ZTerm{c, m}, rest}:
      padd(pscale(c, m, q), pmul(rest, q))

def pneg(p: List<&2, ZTerm>) -> List<&2, ZTerm>:
  match p:
    case Nil{}:
      Nil{}
    case Con{ZTerm{c, m}, rest}:
      Con{ZTerm{S.Z.neg(c), m}, pneg(rest)}

def pconst(c: S.Z) -> List<&2, ZTerm>:
  match c:
    case S.Z0{}:
      Nil{}
    case S.Zpos{p}:
      Con{ZTerm{S.Zpos{p}, Nil{}}, Nil{}}
    case S.Zneg{p}:
      Con{ZTerm{S.Zneg{p}, Nil{}}, Nil{}}

def norm(e: E.ZExpr) -> List<&2, ZTerm>:
  match e:
    case E.ZVar{i}:
      Con{ZTerm{S.Zpos{S.XH{}}, Con{i, Nil{}}}, Nil{}}
    case E.ZCst{c}:
      pconst(c)
    case E.ZAdd{a, b}:
      padd(norm(a), norm(b))
    case E.ZSub{a, b}:
      padd(norm(a), pneg(norm(b)))
    case E.ZMul{a, b}:
      pmul(norm(a), norm(b))
    case E.ZNeg{a}:
      pneg(norm(a))

# Soundness
# ---------

def minsert_ok.dec(+env: List<&2, S.Z>, b: Bool, +x: Nat, +h: Nat, +t: List<&2, Nat>,
  rec: {S.Z.mul(E.lookup(env, x), emono(env, t)) == emono(env, NR.minsert(x, t)) : S.Z})
  -> {S.Z.mul(E.lookup(env, x), S.Z.mul(E.lookup(env, h), emono(env, t))) == emono(env, NR.minsert.dec(b, x, h, t, NR.minsert(x, t))) : S.Z}:
  match b:
    case True{}:
      {==}
    case False{}:
      %rec : {S.Z.mul(E.lookup(env, x), S.Z.mul(E.lookup(env, h), emono(env, t))) == S.Z.mul(E.lookup(env, h), _) : S.Z}
      ZL.mul_swap(E.lookup(env, x), E.lookup(env, h), emono(env, t))

def minsert_ok(+env: List<&2, S.Z>, +x: Nat, m: List<&2, Nat>) -> {S.Z.mul(E.lookup(env, x), emono(env, m)) == emono(env, NR.minsert(x, m)) : S.Z}:
  match m:
    case Nil{}:
      {==}
    case Con{+h, +t}:
      minsert_ok.dec(env, Nat.is_le(x, h), x, h, t, minsert_ok(env, x, t))

def mmul_ok(+env: List<&2, S.Z>, m1: List<&2, Nat>, +m2: List<&2, Nat>) -> {S.Z.mul(emono(env, m1), emono(env, m2)) == emono(env, NR.mmul(m1, m2)) : S.Z}:
  match m1:
    case Nil{}:
      %ZL.one_mul(emono(env, m2)) : {_ == emono(env, m2) : S.Z}
      {==}
    case Con{+v, +vs}:
      %minsert_ok(env, v, NR.mmul(vs, m2)) : {S.Z.mul(S.Z.mul(E.lookup(env, v), emono(env, vs)), emono(env, m2)) == _ : S.Z}
      %mmul_ok(env, vs, m2) : {S.Z.mul(S.Z.mul(E.lookup(env, v), emono(env, vs)), emono(env, m2)) == S.Z.mul(E.lookup(env, v), _) : S.Z}
      %ZL.mul_assoc(E.lookup(env, v), emono(env, vs), emono(env, m2)) : {_ == S.Z.mul(E.lookup(env, v), S.Z.mul(emono(env, vs), emono(env, m2))) : S.Z}
      {==}

def pcoef_ok(-env: List<&2, S.Z>, s: S.Z, -n: List<&2, Nat>, -rest: List<&2, ZTerm>) -> {S.Z.add(S.Z.mul(s, emono(env, n)), epoly(env, rest)) == epoly(env, pcoef(s, n, rest)) : S.Z}:
  match s:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      {==}
    case S.Zneg{p}:
      {==}

def pins_ok.dec(+env: List<&2, S.Z>, o: Cmp, +c: S.Z, +m: List<&2, Nat>, +d: S.Z, +n: List<&2, Nat>, +rest: List<&2, ZTerm>,
  e: {o == NR.mcmp(m, n) : Cmp},
  rec: {S.Z.add(S.Z.mul(c, emono(env, m)), epoly(env, rest)) == epoly(env, pins(c, m, rest)) : S.Z})
  -> {S.Z.add(S.Z.mul(c, emono(env, m)), S.Z.add(S.Z.mul(d, emono(env, n)), epoly(env, rest))) == epoly(env, pins.dec(o, c, m, d, n, rest, pins(c, m, rest))) : S.Z}:
  match o:
    case LT{}:
      {==}
    case EQ{}:
      %pcoef_ok(env, S.Z.add(c, d), n, rest) : {S.Z.add(S.Z.mul(c, emono(env, m)), S.Z.add(S.Z.mul(d, emono(env, n)), epoly(env, rest))) == _ : S.Z}
      %ZL.mul_add_r(c, d, emono(env, n)) : {S.Z.add(S.Z.mul(c, emono(env, m)), S.Z.add(S.Z.mul(d, emono(env, n)), epoly(env, rest))) == S.Z.add(_, epoly(env, rest)) : S.Z}
      %ZL.add_assoc(S.Z.mul(c, emono(env, n)), S.Z.mul(d, emono(env, n)), epoly(env, rest)) : {S.Z.add(S.Z.mul(c, emono(env, m)), S.Z.add(S.Z.mul(d, emono(env, n)), epoly(env, rest))) == _ : S.Z}
      %NR.mcmp_eq(m, n, e) : {S.Z.add(S.Z.mul(c, emono(env, m)), S.Z.add(S.Z.mul(d, emono(env, n)), epoly(env, rest))) == S.Z.add(S.Z.mul(c, emono(env, _)), S.Z.add(S.Z.mul(d, emono(env, n)), epoly(env, rest))) : S.Z}
      {==}
    case GT{}:
      %rec : {S.Z.add(S.Z.mul(c, emono(env, m)), S.Z.add(S.Z.mul(d, emono(env, n)), epoly(env, rest))) == S.Z.add(S.Z.mul(d, emono(env, n)), _) : S.Z}
      ZL.add_swap(S.Z.mul(c, emono(env, m)), S.Z.mul(d, emono(env, n)), epoly(env, rest))

def pins_ok(+env: List<&2, S.Z>, +c: S.Z, +m: List<&2, Nat>, p: List<&2, ZTerm>) -> {S.Z.add(S.Z.mul(c, emono(env, m)), epoly(env, p)) == epoly(env, pins(c, m, p)) : S.Z}:
  match p:
    case Nil{}:
      {==}
    case Con{ZTerm{+d, +n}, +rest}:
      pins_ok.dec(env, NR.mcmp(m, n), c, m, d, n, rest, {==}, pins_ok(env, c, m, rest))

def pinsert_ok(+env: List<&2, S.Z>, c: S.Z, +m: List<&2, Nat>, +p: List<&2, ZTerm>) -> {S.Z.add(S.Z.mul(c, emono(env, m)), epoly(env, p)) == epoly(env, pinsert(c, m, p)) : S.Z}:
  match c:
    case S.Z0{}:
      {==}
    case S.Zpos{q}:
      pins_ok(env, S.Zpos{q}, m, p)
    case S.Zneg{q}:
      pins_ok(env, S.Zneg{q}, m, p)

def padd_ok(+env: List<&2, S.Z>, p: List<&2, ZTerm>, +q: List<&2, ZTerm>) -> {S.Z.add(epoly(env, p), epoly(env, q)) == epoly(env, padd(p, q)) : S.Z}:
  match p:
    case Nil{}:
      {==}
    case Con{ZTerm{+c, +m}, +rest}:
      %pinsert_ok(env, c, m, padd(rest, q)) : {S.Z.add(S.Z.add(S.Z.mul(c, emono(env, m)), epoly(env, rest)), epoly(env, q)) == _ : S.Z}
      %padd_ok(env, rest, q) : {S.Z.add(S.Z.add(S.Z.mul(c, emono(env, m)), epoly(env, rest)), epoly(env, q)) == S.Z.add(S.Z.mul(c, emono(env, m)), _) : S.Z}
      %ZL.add_assoc(S.Z.mul(c, emono(env, m)), epoly(env, rest), epoly(env, q)) : {_ == S.Z.add(S.Z.mul(c, emono(env, m)), S.Z.add(epoly(env, rest), epoly(env, q))) : S.Z}
      {==}

def pscale_ok(+env: List<&2, S.Z>, +c: S.Z, +m: List<&2, Nat>, q: List<&2, ZTerm>) -> {S.Z.mul(S.Z.mul(c, emono(env, m)), epoly(env, q)) == epoly(env, pscale(c, m, q)) : S.Z}:
  match q:
    case Nil{}:
      %ZL.mul_zero(S.Z.mul(c, emono(env, m))) : {_ == S.Z0{} : S.Z}
      {==}
    case Con{ZTerm{+d, +n}, +rest}:
      %pinsert_ok(env, S.Z.mul(c, d), NR.mmul(m, n), pscale(c, m, rest)) : {S.Z.mul(S.Z.mul(c, emono(env, m)), S.Z.add(S.Z.mul(d, emono(env, n)), epoly(env, rest))) == _ : S.Z}
      %pscale_ok(env, c, m, rest) : {S.Z.mul(S.Z.mul(c, emono(env, m)), S.Z.add(S.Z.mul(d, emono(env, n)), epoly(env, rest))) == S.Z.add(S.Z.mul(S.Z.mul(c, d), emono(env, NR.mmul(m, n))), _) : S.Z}
      %mmul_ok(env, m, n) : {S.Z.mul(S.Z.mul(c, emono(env, m)), S.Z.add(S.Z.mul(d, emono(env, n)), epoly(env, rest))) == S.Z.add(S.Z.mul(S.Z.mul(c, d), _), S.Z.mul(S.Z.mul(c, emono(env, m)), epoly(env, rest))) : S.Z}
      %ZL.mul_shuffle(c, d, emono(env, m), emono(env, n)) : {S.Z.mul(S.Z.mul(c, emono(env, m)), S.Z.add(S.Z.mul(d, emono(env, n)), epoly(env, rest))) == S.Z.add(_, S.Z.mul(S.Z.mul(c, emono(env, m)), epoly(env, rest))) : S.Z}
      %ZL.mul_add_l(S.Z.mul(c, emono(env, m)), S.Z.mul(d, emono(env, n)), epoly(env, rest)) : {_ == S.Z.add(S.Z.mul(S.Z.mul(c, emono(env, m)), S.Z.mul(d, emono(env, n))), S.Z.mul(S.Z.mul(c, emono(env, m)), epoly(env, rest))) : S.Z}
      {==}

def pmul_ok(+env: List<&2, S.Z>, p: List<&2, ZTerm>, +q: List<&2, ZTerm>) -> {S.Z.mul(epoly(env, p), epoly(env, q)) == epoly(env, pmul(p, q)) : S.Z}:
  match p:
    case Nil{}:
      {==}
    case Con{ZTerm{+c, +m}, +rest}:
      %padd_ok(env, pscale(c, m, q), pmul(rest, q)) : {S.Z.mul(S.Z.add(S.Z.mul(c, emono(env, m)), epoly(env, rest)), epoly(env, q)) == _ : S.Z}
      %pscale_ok(env, c, m, q) : {S.Z.mul(S.Z.add(S.Z.mul(c, emono(env, m)), epoly(env, rest)), epoly(env, q)) == S.Z.add(_, epoly(env, pmul(rest, q))) : S.Z}
      %pmul_ok(env, rest, q) : {S.Z.mul(S.Z.add(S.Z.mul(c, emono(env, m)), epoly(env, rest)), epoly(env, q)) == S.Z.add(S.Z.mul(S.Z.mul(c, emono(env, m)), epoly(env, q)), _) : S.Z}
      %ZL.mul_add_r(S.Z.mul(c, emono(env, m)), epoly(env, rest), epoly(env, q)) : {_ == S.Z.add(S.Z.mul(S.Z.mul(c, emono(env, m)), epoly(env, q)), S.Z.mul(epoly(env, rest), epoly(env, q))) : S.Z}
      {==}

def pneg_ok(+env: List<&2, S.Z>, p: List<&2, ZTerm>) -> {S.Z.neg(epoly(env, p)) == epoly(env, pneg(p)) : S.Z}:
  match p:
    case Nil{}:
      {==}
    case Con{ZTerm{+c, +m}, +rest}:
      %pneg_ok(env, rest) : {S.Z.neg(S.Z.add(S.Z.mul(c, emono(env, m)), epoly(env, rest))) == S.Z.add(S.Z.mul(S.Z.neg(c), emono(env, m)), _) : S.Z}
      %ZL.neg_add(S.Z.mul(c, emono(env, m)), epoly(env, rest)) : {_ == S.Z.add(S.Z.mul(S.Z.neg(c), emono(env, m)), S.Z.neg(epoly(env, rest))) : S.Z}
      %ZL.neg_mul(c, emono(env, m)) : {S.Z.add(_, S.Z.neg(epoly(env, rest))) == S.Z.add(S.Z.mul(S.Z.neg(c), emono(env, m)), S.Z.neg(epoly(env, rest))) : S.Z}
      {==}

def pconst_ok(-env: List<&2, S.Z>, c: S.Z) -> {epoly(env, pconst(c)) == c : S.Z}:
  match c:
    case S.Z0{}:
      {==}
    case S.Zpos{+q}:
      %ZL.mul_one(S.Zpos{q}) : {_ == S.Zpos{q} : S.Z}
      {==}
    case S.Zneg{+q}:
      %ZL.mul_one(S.Zneg{q}) : {_ == S.Zneg{q} : S.Z}
      {==}

def norm_ok(+env: List<&2, S.Z>, e: E.ZExpr) -> {epoly(env, norm(e)) == E.eval(env, e) : S.Z}:
  match e:
    case E.ZVar{+i}:
      %ZL.add_zero(S.Z.mul(S.Zpos{S.XH{}}, S.Z.mul(E.lookup(env, i), S.Zpos{S.XH{}}))) : {_ == E.lookup(env, i) : S.Z}
      %ZL.one_mul(S.Z.mul(E.lookup(env, i), S.Zpos{S.XH{}})) : {_ == E.lookup(env, i) : S.Z}
      %ZL.mul_one(E.lookup(env, i)) : {_ == E.lookup(env, i) : S.Z}
      {==}
    case E.ZCst{c}:
      pconst_ok(env, c)
    case E.ZAdd{+a, +b}:
      %norm_ok(env, a) : {epoly(env, padd(norm(a), norm(b))) == S.Z.add(_, E.eval(env, b)) : S.Z}
      %norm_ok(env, b) : {epoly(env, padd(norm(a), norm(b))) == S.Z.add(epoly(env, norm(a)), _) : S.Z}
      %padd_ok(env, norm(a), norm(b)) : {_ == S.Z.add(epoly(env, norm(a)), epoly(env, norm(b))) : S.Z}
      {==}
    case E.ZSub{+a, +b}:
      %norm_ok(env, a) : {epoly(env, padd(norm(a), pneg(norm(b)))) == S.Z.add(_, S.Z.neg(E.eval(env, b))) : S.Z}
      %norm_ok(env, b) : {epoly(env, padd(norm(a), pneg(norm(b)))) == S.Z.add(epoly(env, norm(a)), S.Z.neg(_)) : S.Z}
      %padd_ok(env, norm(a), pneg(norm(b))) : {_ == S.Z.add(epoly(env, norm(a)), S.Z.neg(epoly(env, norm(b)))) : S.Z}
      %pneg_ok(env, norm(b)) : {S.Z.add(epoly(env, norm(a)), _) == S.Z.add(epoly(env, norm(a)), S.Z.neg(epoly(env, norm(b)))) : S.Z}
      {==}
    case E.ZMul{+a, +b}:
      %norm_ok(env, a) : {epoly(env, pmul(norm(a), norm(b))) == S.Z.mul(_, E.eval(env, b)) : S.Z}
      %norm_ok(env, b) : {epoly(env, pmul(norm(a), norm(b))) == S.Z.mul(epoly(env, norm(a)), _) : S.Z}
      %pmul_ok(env, norm(a), norm(b)) : {_ == S.Z.mul(epoly(env, norm(a)), epoly(env, norm(b))) : S.Z}
      {==}
    case E.ZNeg{+a}:
      %norm_ok(env, a) : {epoly(env, pneg(norm(a))) == S.Z.neg(_) : S.Z}
      %pneg_ok(env, norm(a)) : {_ == S.Z.neg(epoly(env, norm(a))) : S.Z}
      {==}

# The normalizer's use: two expressions with equal normal forms are equal
# under every environment. The hypothesis is checked by computation, {==}.
def ring_eq(+env: List<&2, S.Z>, +e1: E.ZExpr, +e2: E.ZExpr, h: {norm(e1) == norm(e2) : List<&2, ZTerm>}) -> {E.eval(env, e1) == E.eval(env, e2) : S.Z}:
  %norm_ok(env, e1) : {_ == E.eval(env, e2) : S.Z}
  %norm_ok(env, e2) : {epoly(env, norm(e1)) == _ : S.Z}
  %h : {epoly(env, norm(e1)) == epoly(env, _) : S.Z}
  {==}
