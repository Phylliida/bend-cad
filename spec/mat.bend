# bend-cad spec: vectors and matrices, the certificates' linear algebra
# (DESIGN §8.3). Trusted. A vector is a list read with implicit trailing
# zeros: a missing entry counts as 0, so sums and products need no shape
# conditions. A matrix is the list of its rows (missing rows are zero).
#
# Two parallel copies: over an ordered field F, where meanings live, and
# over the dyadics, which a checker computes with exactly. ofd sends a
# dyadic to F (through its rational); ofdv and ofdm map it over vectors and
# matrices. The infinity norm of a dyadic matrix is its largest row sum of
# absolute values. In F there are no norms, only bounds: bnd(a, s) is
# |a| <= s, vbnd(v, s) is ||v|| <= s, and mbnd(M, B) says every entry of M
# is at most the absolute value of B's entry in its place.

import Base
import ./num.bend as S
import ./field.bend as O

# Over an ordered field
# ---------------------

def Vec(~F: O.OField) -> Data:
  List<&2, O.C(F)>

def Mat(~F: O.OField) -> Data:
  List<&2, List<&2, O.C(F)>>

def vadd(~F: O.OField, u: Vec(~F), w: Vec(~F)) -> Vec(~F):
  match u w:
    case Nil{} w:
      w
    case Con{a, us} Nil{}:
      Con{a, us}
    case Con{a, us} Con{b, ws}:
      Con{O.add(F, a, b), vadd(~F, us, ws)}

def vneg(~F: O.OField, u: Vec(~F)) -> Vec(~F):
  match u:
    case Nil{}:
      Nil{}
    case Con{a, us}:
      Con{O.neg(F, a), vneg(~F, us)}

# c u
def vscale(~F: O.OField, +c: O.C(F), u: Vec(~F)) -> Vec(~F):
  match u:
    case Nil{}:
      Nil{}
    case Con{a, us}:
      Con{O.mul(F, c, a), vscale(~F, c, us)}

# the sum of a_j v_j
def dot(~F: O.OField, a: Vec(~F), v: Vec(~F)) -> O.C(F):
  match a v:
    case Nil{} v:
      O.zero(F)
    case Con{x, xs} Nil{}:
      O.zero(F)
    case Con{x, xs} Con{y, ys}:
      O.add(F, O.mul(F, x, y), dot(~F, xs, ys))

# A v
def matvec(~F: O.OField, a: Mat(~F), +v: Vec(~F)) -> Vec(~F):
  match a:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{dot(~F, r, v), matvec(~F, rs, v)}

# the row a times B: the sum of a_j times row j of B
def vecmat(~F: O.OField, a: Vec(~F), b: Mat(~F)) -> Vec(~F):
  match a b:
    case Nil{} b:
      Nil{}
    case Con{x, xs} Nil{}:
      Nil{}
    case Con{x, xs} Con{r, rs}:
      vadd(~F, vscale(~F, x, r), vecmat(~F, xs, rs))

# A B
def matmul(~F: O.OField, a: Mat(~F), +b: Mat(~F)) -> Mat(~F):
  match a:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{vecmat(~F, r, b), matmul(~F, rs, b)}

def madd(~F: O.OField, a: Mat(~F), b: Mat(~F)) -> Mat(~F):
  match a b:
    case Nil{} b:
      b
    case Con{r, rs} Nil{}:
      Con{r, rs}
    case Con{r, rs} Con{t, ts}:
      Con{vadd(~F, r, t), madd(~F, rs, ts)}

def mneg(~F: O.OField, a: Mat(~F)) -> Mat(~F):
  match a:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{vneg(~F, r), mneg(~F, rs)}

# each row with a 0 in front
def shift(~F: O.OField, a: Mat(~F)) -> Mat(~F):
  match a:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{Con{O.zero(F), r}, shift(~F, rs)}

# the n by n identity
def ident(~F: O.OField, n: Nat) -> Mat(~F):
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{[O.one(F)], shift(~F, ident(~F, k))}

def len(~F: O.OField, v: Vec(~F)) -> Nat:
  match v:
    case Nil{}:
      0n
    case Con{x, xs}:
      1n+len(~F, xs)

def Both(-A: Data, -B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

# |a| <= s: s - a and s + a are not negative
def bnd(~F: O.OField, +a: O.C(F), +s: O.C(F)) -> Data:
  Both(O.le(~F, O.zero(F), O.sub(~F, s, a)), O.le(~F, O.zero(F), O.add(F, s, a)))

def vbnd.all(~F: O.OField, v: Vec(~F), +s: O.C(F)) -> Data:
  match v:
    case Nil{}:
      Unit
    case Con{x, xs}:
      Both(bnd(~F, x, s), vbnd.all(~F, xs, s))

# ||v|| <= s (so s >= 0: v has zeros past its end)
def vbnd(~F: O.OField, +v: Vec(~F), +s: O.C(F)) -> Data:
  Both(O.le(~F, O.zero(F), s), vbnd.all(~F, v, s))

# Over the dyadics
# ----------------

def zabs(z: S.Z) -> S.Z:
  match z:
    case S.Z0{}:
      S.Z0{}
    case S.Zpos{p}:
      S.Zpos{p}
    case S.Zneg{p}:
      S.Zpos{p}

def d0() -> S.D:
  S.D{S.Z0{}, 0n}

def d1() -> S.D:
  S.D{S.Zpos{S.XH{}}, 0n}

def dabs(+x: S.D) -> S.D:
  S.D{zabs(S.D.man(x)), S.D.exp(x)}

def dmax.go(c: Cmp, +a: S.D, +b: S.D) -> S.D:
  match c:
    case LT{}:
      b
    case EQ{}:
      a
    case GT{}:
      a

def dmax(+a: S.D, +b: S.D) -> S.D:
  dmax.go(S.Q.cmp(S.D.toq(a), S.D.toq(b)), a, b)

def DVec() -> Data:
  List<&2, S.D>

def DMat() -> Data:
  List<&2, List<&2, S.D>>

def dvadd(u: DVec(), w: DVec()) -> DVec():
  match u w:
    case Nil{} w:
      w
    case Con{a, us} Nil{}:
      Con{a, us}
    case Con{a, us} Con{b, ws}:
      Con{S.D.add(a, b), dvadd(us, ws)}

def dvneg(u: DVec()) -> DVec():
  match u:
    case Nil{}:
      Nil{}
    case Con{a, us}:
      Con{S.D.neg(a), dvneg(us)}

def dvscale(+c: S.D, u: DVec()) -> DVec():
  match u:
    case Nil{}:
      Nil{}
    case Con{a, us}:
      Con{S.D.mul(c, a), dvscale(c, us)}

def ddot(a: DVec(), v: DVec()) -> S.D:
  match a v:
    case Nil{} v:
      d0()
    case Con{x, xs} Nil{}:
      d0()
    case Con{x, xs} Con{y, ys}:
      S.D.add(S.D.mul(x, y), ddot(xs, ys))

def dmatvec(a: DMat(), +v: DVec()) -> DVec():
  match a:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{ddot(r, v), dmatvec(rs, v)}

def dvecmat(a: DVec(), b: DMat()) -> DVec():
  match a b:
    case Nil{} b:
      Nil{}
    case Con{x, xs} Nil{}:
      Nil{}
    case Con{x, xs} Con{r, rs}:
      dvadd(dvscale(x, r), dvecmat(xs, rs))

def dmatmul(a: DMat(), +b: DMat()) -> DMat():
  match a:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{dvecmat(r, b), dmatmul(rs, b)}

def dmadd(a: DMat(), b: DMat()) -> DMat():
  match a b:
    case Nil{} b:
      b
    case Con{r, rs} Nil{}:
      Con{r, rs}
    case Con{r, rs} Con{t, ts}:
      Con{dvadd(r, t), dmadd(rs, ts)}

def dmneg(a: DMat()) -> DMat():
  match a:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{dvneg(r), dmneg(rs)}

def dshift(a: DMat()) -> DMat():
  match a:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{Con{d0(), r}, dshift(rs)}

def dident(n: Nat) -> DMat():
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      Con{[d1()], dshift(dident(k))}

# the sum of |r_j|
def drowabs(r: DVec()) -> S.D:
  match r:
    case Nil{}:
      d0()
    case Con{x, xs}:
      S.D.add(dabs(x), drowabs(xs))

# ||A||, the largest row sum of absolute values
def dnorm(a: DMat()) -> S.D:
  match a:
    case Nil{}:
      d0()
    case Con{r, rs}:
      dmax(drowabs(r), dnorm(rs))

# ||v||, the largest |v_i|
def dvnorm(v: DVec()) -> S.D:
  match v:
    case Nil{}:
      d0()
    case Con{x, xs}:
      dmax(dabs(x), dvnorm(xs))

# Dyadics in F
# ------------

def ofd(~F: O.OField, +x: S.D) -> O.C(F):
  O.ofq(~F, S.D.toq(x))

def ofdv(~F: O.OField, v: DVec()) -> Vec(~F):
  match v:
    case Nil{}:
      Nil{}
    case Con{x, xs}:
      Con{ofd(~F, x), ofdv(~F, xs)}

def ofdm(~F: O.OField, a: DMat()) -> Mat(~F):
  match a:
    case Nil{}:
      Nil{}
    case Con{r, rs}:
      Con{ofdv(~F, r), ofdm(~F, rs)}

# every entry of the row m is at most |b_j| (0 past b's end)
def vmaj(~F: O.OField, m: Vec(~F), b: DVec()) -> Data:
  match m b:
    case Nil{} b:
      Unit
    case Con{x, xs} Nil{}:
      Both(bnd(~F, x, O.zero(F)), vmaj(~F, xs, Nil{}))
    case Con{x, xs} Con{y, ys}:
      Both(bnd(~F, x, ofd(~F, dabs(y))), vmaj(~F, xs, ys))

# every entry of M is at most the absolute value of B's entry in its place
def mmaj(~F: O.OField, m: Mat(~F), b: DMat()) -> Data:
  match m b:
    case Nil{} b:
      Unit
    case Con{r, rs} Nil{}:
      Both(vmaj(~F, r, Nil{}), mmaj(~F, rs, Nil{}))
    case Con{r, rs} Con{t, ts}:
      Both(vmaj(~F, r, t), mmaj(~F, rs, ts))
