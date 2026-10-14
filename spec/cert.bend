# bend-cad spec: what a block certificate claims (DESIGN §8.3). Trusted.
#
# A block is a square system of polynomial equations f(y; z) = 0 in its n
# unknowns y, with parameters z (earlier blocks' variables, pinned values,
# constants) known only to lie in balls. A block numbers its own variables:
# 0..n-1 are the unknowns, n, n+1, ... the parameters, so its equations are
# evaluated at the list y (fitted to n entries) followed by z. (Composition
# maps a block's numbering to the sketch's, DESIGN §8.4.)
#
# A certificate, written in the checker's numbers K (spec/knum.bend), names
# a center ỹ and a radius r_i for each unknown, a factor q, an approximate
# inverse Y of the Jacobian, and each parameter's center and radius. What
# it claims holds in every ordered field F that K maps into: for every z in
# the parameters' box, the Newton map y ↦ y − Y·f(y; z) sends the box
# B = {|y_i − ỹ_i| ≤ r_i} into itself and contracts it by q < 1, and its
# fixed points are zeros of f. (In a complete ordered field, Banach's
# theorem then gives exactly one zero in B; DESIGN §8.4, Q18.)
#
# Vectors are lists read with trailing zeros (spec/mat.bend). A point of B
# has exactly as many entries as the center, and a radius past the end of
# a radius list is 0 (a parameter past the last radius is fixed at 0).

import Base
import ./ring.bend as E
import ./field.bend as O
import ./mat.bend as M
import ./knum.bend as N

# Blocks and certificates
# -----------------------

# eqs must vanish; n is the number of unknowns (and of equations)
type Block is Data:
  Block{eqs: List<&2, E.QExpr>, n: Nat}

def Block.eqs(b: Block) -> List<&2, E.QExpr>:
  match b:
    case Block{eqs, n}:
      eqs

def Block.n(b: Block) -> Nat:
  match b:
    case Block{eqs, n}:
      n

# yc, yr: each unknown's center and radius; q: the contraction factor;
# ym: Y (a row per unknown); pc, pr: each parameter's center and radius
type Cert<-K: N.Num> is Data:
  Cert{yc: List<&2, N.NC(K)>, yr: List<&2, N.NC(K)>, q: N.NC(K), ym: List<&2, List<&2, N.NC(K)>>, pc: List<&2, N.NC(K)>, pr: List<&2, N.NC(K)>}

def Cert.yc(-K: N.Num, c: Cert<K>) -> List<&2, N.NC(K)>:
  match c:
    case Cert{yc, yr, q, ym, pc, pr}:
      yc

def Cert.yr(-K: N.Num, c: Cert<K>) -> List<&2, N.NC(K)>:
  match c:
    case Cert{yc, yr, q, ym, pc, pr}:
      yr

def Cert.q(-K: N.Num, c: Cert<K>) -> N.NC(K):
  match c:
    case Cert{yc, yr, q, ym, pc, pr}:
      q

def Cert.ym(-K: N.Num, c: Cert<K>) -> List<&2, List<&2, N.NC(K)>>:
  match c:
    case Cert{yc, yr, q, ym, pc, pr}:
      ym

def Cert.pc(-K: N.Num, c: Cert<K>) -> List<&2, N.NC(K)>:
  match c:
    case Cert{yc, yr, q, ym, pc, pr}:
      pc

def Cert.pr(-K: N.Num, c: Cert<K>) -> List<&2, N.NC(K)>:
  match c:
    case Cert{yc, yr, q, ym, pc, pr}:
      pr

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

def pcenter(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, c: Cert<K>) -> M.Vec(~F):
  N.ofkv(~K, ~F, ~H, Cert.pc(K, c))

def pradii(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, c: Cert<K>) -> M.Vec(~F):
  N.ofkv(~K, ~F, ~H, Cert.pr(K, c))

# The block in F
# --------------

def vsub(~F: O.OField, u: M.Vec(~F), w: M.Vec(~F)) -> M.Vec(~F):
  M.vadd(~F, u, M.vneg(~F, w))

# y's first n entries (zeros past its end)
def fit(~F: O.OField, n: Nat, y: M.Vec(~F)) -> M.Vec(~F):
  match n y:
    case 0n y:
      Nil{}
    case 1n+k Nil{}:
      Con{O.zero(F), fit(~F, k, Nil{})}
    case 1n+k Con{a, rest}:
      Con{a, fit(~F, k, rest)}

def app(~F: O.OField, u: M.Vec(~F), w: M.Vec(~F)) -> M.Vec(~F):
  match u:
    case Nil{}:
      w
    case Con{a, us}:
      Con{a, app(~F, us, w)}

# the equations' values at env
def fvals(~F: O.OField, eqs: List<&2, E.QExpr>, +env: M.Vec(~F)) -> M.Vec(~F):
  match eqs:
    case Nil{}:
      Nil{}
    case Con{e, es}:
      Con{O.eval(~F, env, e), fvals(~F, es, env)}

# f(y; z): the block's equations at its unknowns y and parameters z
def bfun(~F: O.OField, +b: Block, y: M.Vec(~F), z: M.Vec(~F)) -> M.Vec(~F):
  fvals(~F, Block.eqs(b), app(~F, fit(~F, Block.n(b), y), z))

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

# y lies in the box B: y has as many entries as the center ỹ, and
# |y_i - ỹ_i| <= r_i
def ball(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: Cert<K>, +y: M.Vec(~F)) -> Data:
  M.Both({M.len(~F, y) == M.len(~F, center(~K, ~F, ~H, c)) : Nat}, rbnd(~F, vsub(~F, y, center(~K, ~F, ~H, c)), radii(~K, ~F, ~H, c)))

# u and v are within s radii of each other: |u_i - v_i| <= s r_i
def near(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, c: Cert<K>, +s: O.C(F), u: M.Vec(~F), v: M.Vec(~F)) -> Data:
  rbnd(~F, vsub(~F, u, v), M.vscale(~F, s, radii(~K, ~F, ~H, c)))

# z lies in the parameters' box: |z_k - c_k| <= rho_k
def pinned(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: Cert<K>, z: M.Vec(~F)) -> Data:
  rbnd(~F, vsub(~F, z, pcenter(~K, ~F, ~H, c)), pradii(~K, ~F, ~H, c))

# the Newton map y - Y f(y; z)
def newton(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, b: Block, c: Cert<K>, z: M.Vec(~F), +y: M.Vec(~F)) -> M.Vec(~F):
  vsub(~F, y, M.matvec(~F, ymat(~K, ~F, ~H, c), bfun(~F, b, y, z)))
