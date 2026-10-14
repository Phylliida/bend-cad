# bend-cad spec: what a block certificate claims (DESIGN §8.3). Trusted.
#
# A block is a square system of polynomial equations f(y; z) = 0 in its
# unknowns y, with parameters z (earlier blocks' variables, pinned values,
# constants) known only to lie in balls. A certificate, written in the
# checker's numbers K (spec/knum.bend), names a center ỹ and a radius r_i
# for each unknown, a factor q, an approximate inverse Y of the Jacobian,
# and each parameter's index, center and radius. What it claims holds in
# every ordered field F that K maps into: for every choice of the
# parameters in their balls, the Newton map y ↦ y − Y·f(y; z) sends the box
# B = {|y_i − ỹ_i| ≤ r_i} into itself and contracts it by q < 1, and its
# fixed points are zeros of f. (In a complete ordered field, Banach's
# theorem then gives exactly one zero in B; DESIGN §8.4, Q18.)
#
# Vectors are lists read with trailing zeros (spec/mat.bend). A radius past
# the end of the radius list is 0, so B fixes every coordinate past the
# last unknown at 0: B has exactly the block's dimension.

import Base
import ./ring.bend as E
import ./field.bend as O
import ./mat.bend as M
import ./knum.bend as N

# Blocks and certificates
# -----------------------

# eqs must vanish; ys are the unknowns (variable indices, as many as
# equations)
type Block is Data:
  Block{eqs: List<&2, E.QExpr>, ys: List<&2, Nat>}

def Block.eqs(b: Block) -> List<&2, E.QExpr>:
  match b:
    case Block{eqs, ys}:
      eqs

def Block.ys(b: Block) -> List<&2, Nat>:
  match b:
    case Block{eqs, ys}:
      ys

# a parameter: variable i lies within r of c
type Par<-K: N.Num> is Data:
  Par{i: Nat, c: N.NC(K), r: N.NC(K)}

# yc, yr: each unknown's center and radius; q: the contraction factor;
# ym: Y (a row per unknown); ps: the parameters
type Cert<-K: N.Num> is Data:
  Cert{yc: List<&2, N.NC(K)>, yr: List<&2, N.NC(K)>, q: N.NC(K), ym: List<&2, List<&2, N.NC(K)>>, ps: List<&2, Par<K>>}

def Cert.yc(-K: N.Num, c: Cert<K>) -> List<&2, N.NC(K)>:
  match c:
    case Cert{yc, yr, q, ym, ps}:
      yc

def Cert.yr(-K: N.Num, c: Cert<K>) -> List<&2, N.NC(K)>:
  match c:
    case Cert{yc, yr, q, ym, ps}:
      yr

def Cert.q(-K: N.Num, c: Cert<K>) -> N.NC(K):
  match c:
    case Cert{yc, yr, q, ym, ps}:
      q

def Cert.ym(-K: N.Num, c: Cert<K>) -> List<&2, List<&2, N.NC(K)>>:
  match c:
    case Cert{yc, yr, q, ym, ps}:
      ym

def Cert.ps(-K: N.Num, c: Cert<K>) -> List<&2, Par<K>>:
  match c:
    case Cert{yc, yr, q, ym, ps}:
      ps

# The certificate's numbers in F
# ------------------------------

def center(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, c: Cert<K>) -> M.Vec(~F):
  N.ofkv(~K, ~F, ~H, Cert.yc(K, c))

def radii(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, c: Cert<K>) -> M.Vec(~F):
  N.ofkv(~K, ~F, ~H, Cert.yr(K, c))

def factor(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, c: Cert<K>) -> O.C(F):
  N.emap(K, F, H, Cert.q(K, c))

def ymat(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, c: Cert<K>) -> M.Mat(~F):
  N.ofkm(~K, ~F, ~H, Cert.ym(K, c))

# The block in F
# --------------

def vsub(~F: O.OField, u: M.Vec(~F), w: M.Vec(~F)) -> M.Vec(~F):
  M.vadd(~F, u, M.vneg(~F, w))

# x with entry i set to v (zeros added past its end)
def vset(~F: O.OField, x: M.Vec(~F), i: Nat, +v: O.C(F)) -> M.Vec(~F):
  match x i:
    case Nil{} 0n:
      [v]
    case Nil{} 1n+j:
      Con{O.zero(F), vset(~F, Nil{}, j, v)}
    case Con{h, t} 0n:
      Con{v, t}
    case Con{h, t} 1n+j:
      Con{h, vset(~F, t, j, v)}

# x with the variables ys set to y (read with trailing zeros)
def setv(~F: O.OField, ys: List<&2, Nat>, y: M.Vec(~F), x: M.Vec(~F)) -> M.Vec(~F):
  match ys y:
    case Nil{} y:
      x
    case Con{i, ks} Nil{}:
      setv(~F, ks, Nil{}, vset(~F, x, i, O.zero(F)))
    case Con{i, ks} Con{v, vs}:
      setv(~F, ks, vs, vset(~F, x, i, v))

# the equations' values at env
def fvals(~F: O.OField, eqs: List<&2, E.QExpr>, +env: M.Vec(~F)) -> M.Vec(~F):
  match eqs:
    case Nil{}:
      Nil{}
    case Con{e, es}:
      Con{O.eval(~F, env, e), fvals(~F, es, env)}

# f(y; z): the block's equations at x, with its unknowns set to y
def bfun(~F: O.OField, +b: Block, x: M.Vec(~F), y: M.Vec(~F)) -> M.Vec(~F):
  fvals(~F, Block.eqs(b), setv(~F, Block.ys(b), y, x))

# What the certificate says
# -------------------------

# |d_i| <= r_i for every i, with r_i = 0 past r's end
def rbnd(~F: O.OField, d: M.Vec(~F), r: M.Vec(~F)) -> Data:
  match d r:
    case Nil{} r:
      Unit
    case Con{a, ds} Nil{}:
      M.Both(M.bnd(~F, a, O.zero(F)), rbnd(~F, ds, Nil{}))
    case Con{a, ds} Con{s, rs}:
      M.Both(M.bnd(~F, a, s), rbnd(~F, ds, rs))

# y lies in the box B: |y_i - ỹ_i| <= r_i
def ball(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: Cert<K>, y: M.Vec(~F)) -> Data:
  rbnd(~F, vsub(~F, y, center(~K, ~F, ~H, c)), radii(~K, ~F, ~H, c))

# u and v are within s radii of each other: |u_i - v_i| <= s r_i
def near(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, c: Cert<K>, +s: O.C(F), u: M.Vec(~F), v: M.Vec(~F)) -> Data:
  rbnd(~F, vsub(~F, u, v), M.vscale(~F, s, radii(~K, ~F, ~H, c)))

# parameter p holds at x: |x_i - c| <= r
def pin1(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x: M.Vec(~F), p: Par<K>) -> Data:
  match p:
    case Par{i, a, s}:
      M.bnd(~F, O.sub(~F, O.lookup(~F, x, i), N.emap(K, F, H, a)), N.emap(K, F, H, s))

def pin.go(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x: M.Vec(~F), ps: List<&2, Par<K>>) -> Data:
  match ps:
    case Nil{}:
      Unit
    case Con{p, rest}:
      M.Both(pin1(~K, ~F, ~H, x, p), pin.go(~K, ~F, ~H, x, rest))

# every parameter lies in its ball
def pinned(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, c: Cert<K>, x: M.Vec(~F)) -> Data:
  pin.go(~K, ~F, ~H, x, Cert.ps(K, c))

# x and x2 agree on parameter p
def agree1(~K: N.Num, ~F: O.OField, +x: M.Vec(~F), +x2: M.Vec(~F), p: Par<K>) -> Data:
  match p:
    case Par{i, a, s}:
      {O.lookup(~F, x, i) == O.lookup(~F, x2, i) : O.C(F)}

def agree.go(~K: N.Num, ~F: O.OField, +x: M.Vec(~F), +x2: M.Vec(~F), ps: List<&2, Par<K>>) -> Data:
  match ps:
    case Nil{}:
      Unit
    case Con{p, rest}:
      M.Both(agree1(~K, ~F, x, x2, p), agree.go(~K, ~F, x, x2, rest))

# x and x2 agree on every parameter
def agree(~K: N.Num, ~F: O.OField, c: Cert<K>, x: M.Vec(~F), x2: M.Vec(~F)) -> Data:
  agree.go(~K, ~F, x, x2, Cert.ps(K, c))

# the Newton map y - Y f(y; z)
def newton(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, b: Block, c: Cert<K>, x: M.Vec(~F), +y: M.Vec(~F)) -> M.Vec(~F):
  vsub(~F, y, M.matvec(~F, ymat(~K, ~F, ~H, c), bfun(~F, b, x, y)))
