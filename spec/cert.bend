# bend-cad spec: what a block certificate claims (DESIGN §8.3). Trusted.
#
# A block is a square system of polynomial equations f(y; z) = 0 in its
# unknowns y, with parameters z (earlier blocks' variables, pinned values,
# constants) known only to lie in balls. A certificate, written in the
# checker's numbers K (spec/knum.bend), names a center ỹ and radius r for
# the unknowns, a factor q, an approximate inverse Y of the Jacobian, and
# each parameter's center and radius. What it claims holds in every ordered
# field F that K maps into: for every choice of the parameters in their
# balls, the Newton map y ↦ y − Y·f(y; z) sends the ball B(ỹ, r) into
# itself and contracts it by q < 1, and its fixed points are zeros of f.
# (In ℝ, Banach's theorem then gives exactly one zero in the ball, DESIGN
# §8.4.) Norms are infinity norms; F has no norms, only bounds (spec/mat).

import Base
import ./ring.bend as E
import ./field.bend as O
import ./mat.bend as M
import ./knum.bend as N

# Blocks and certificates
# -----------------------

# eqs must vanish; ys are the unknowns (variable indices, as many as
# equations); ps are the parameters
type Block is Data:
  Block{eqs: List<&2, E.QExpr>, ys: List<&2, Nat>, ps: List<&2, Nat>}

def Block.eqs(b: Block) -> List<&2, E.QExpr>:
  match b:
    case Block{eqs, ys, ps}:
      eqs

def Block.ys(b: Block) -> List<&2, Nat>:
  match b:
    case Block{eqs, ys, ps}:
      ys

def Block.ps(b: Block) -> List<&2, Nat>:
  match b:
    case Block{eqs, ys, ps}:
      ps

# yc, r: the unknowns' ball; q: the contraction factor; ym: Y (a row per
# unknown); pc, pr: each parameter's center and radius, in ps's order
type Cert<-K: N.Num> is Data:
  Cert{yc: List<&2, N.NC(K)>, r: N.NC(K), q: N.NC(K), ym: List<&2, List<&2, N.NC(K)>>, pc: List<&2, N.NC(K)>, pr: List<&2, N.NC(K)>}

def Cert.yc(-K: N.Num, c: Cert<K>) -> List<&2, N.NC(K)>:
  match c:
    case Cert{yc, r, q, ym, pc, pr}:
      yc

def Cert.r(-K: N.Num, c: Cert<K>) -> N.NC(K):
  match c:
    case Cert{yc, r, q, ym, pc, pr}:
      r

def Cert.q(-K: N.Num, c: Cert<K>) -> N.NC(K):
  match c:
    case Cert{yc, r, q, ym, pc, pr}:
      q

def Cert.ym(-K: N.Num, c: Cert<K>) -> List<&2, List<&2, N.NC(K)>>:
  match c:
    case Cert{yc, r, q, ym, pc, pr}:
      ym

def Cert.pc(-K: N.Num, c: Cert<K>) -> List<&2, N.NC(K)>:
  match c:
    case Cert{yc, r, q, ym, pc, pr}:
      pc

def Cert.pr(-K: N.Num, c: Cert<K>) -> List<&2, N.NC(K)>:
  match c:
    case Cert{yc, r, q, ym, pc, pr}:
      pr

# The certificate's numbers in F
# ------------------------------

def center(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, c: Cert<K>) -> M.Vec(~F):
  N.ofkv(~K, ~F, ~H, Cert.yc(K, c))

def radius(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, c: Cert<K>) -> O.C(F):
  N.emap(K, F, H, Cert.r(K, c))

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

# each parameter x_i lies within its radius of its center
def pin.go(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +x: M.Vec(~F), ps: List<&2, Nat>, pc: List<&2, N.NC(K)>, pr: List<&2, N.NC(K)>) -> Data:
  match ps pc pr:
    case Nil{} pc pr:
      Unit
    case Con{i, ks} Nil{} pr:
      Unit
    case Con{i, ks} Con{a, cs} Nil{}:
      Unit
    case Con{i, ks} Con{a, cs} Con{s, ss}:
      M.Both(M.bnd(~F, O.sub(~F, O.lookup(~F, x, i), N.emap(K, F, H, a)), N.emap(K, F, H, s)), pin.go(~K, ~F, ~H, x, ks, cs, ss))

def pinned(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, b: Block, +c: Cert<K>, x: M.Vec(~F)) -> Data:
  pin.go(~K, ~F, ~H, x, Block.ps(b), Cert.pc(K, c), Cert.pr(K, c))

# ||y - ỹ|| <= r
def ball(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, +c: Cert<K>, y: M.Vec(~F)) -> Data:
  M.vbnd(~F, vsub(~F, y, center(~K, ~F, ~H, c)), radius(~K, ~F, ~H, c))

# the Newton map y - Y f(y; z)
def newton(~K: N.Num, ~F: O.OField, ~H: N.Emb<K, F>, b: Block, c: Cert<K>, x: M.Vec(~F), +y: M.Vec(~F)) -> M.Vec(~F):
  vsub(~F, y, M.matvec(~F, ymat(~K, ~F, ~H, c), bfun(~F, b, x, y)))
