# proto/chain.bend: sk-P1 spike for the depth-k circle chain. Untrusted.
#
# Each step places P_k at distance r from P_{k−2} and s from P_{k−1}, on a
# chosen side. A step is one block of the design's §8.3: unknown y = P_k,
# parameters z = (P_{k−2}, P_{k−1}) ranging over their certified balls.
#
# All certified quantities are integers at scale 2^−P nm (a "dyadic point").
# The proposer guesses in F32, refines by simplified Newton in exact integer
# arithmetic, and the certificate is checked exactly:
#   q  = ‖I − Y·J(ỹ)‖ + ‖Y‖·4(r + ρ) < 1
#   ‖Y·f(ỹ)‖ + ‖Y‖·max_i(2‖ỹ − c_i‖₁ρ + 2ρ²) ≤ (1 − q)·r
# (∞-norms on ℝ², ‖·‖₁ ≤ 2‖·‖∞), which proves a unique exact P_k within r of
# ỹ for every choice of parents within their balls.

import Base
import ./int.bend as I

# Integer shorthands
# ------------------

def zadd(a: I.Int, b: I.Int) -> I.Int:
  I.Int.add(a, b)

def zsub(a: I.Int, b: I.Int) -> I.Int:
  I.Int.sub(a, b)

def zmul(a: I.Int, b: I.Int) -> I.Int:
  I.Int.mul(a, b)

def zabs(a: I.Int) -> I.Int:
  I.Int.abs(a)

def zneg(a: I.Int) -> I.Int:
  I.Int.neg(a)

def zlit(n: Nat) -> I.Int:
  I.Int.from_nat(n)

def zmax.fin(c: Cmp, a: I.Int, b: I.Int) -> I.Int:
  match c:
    case LT{}:
      b
    case EQ{}:
      a
    case GT{}:
      a

def zmax(+a: I.Int, +b: I.Int) -> I.Int:
  zmax.fin(I.Int.cmp(a, b), a, b)

# a ≤ b
def zle.fin(c: Cmp) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

def zle(a: I.Int, b: I.Int) -> Bool:
  zle.fin(I.Int.cmp(a, b))

# Points, matrices, results
# -------------------------

type Pt is Data:
  Pt{x: I.Int, y: I.Int}

type PtF is Data:
  PtF{x: F32, y: F32}

# [[a, b], [c, d]]
type M2 is Data:
  M2{a: I.Int, b: I.Int, c: I.Int, d: I.Int}

# a certified point: center and radius, both at scale 2^−P
type Cert is Data:
  Cert{c: Pt, r: I.Int}

type Res is Data:
  CertOk{c: Cert}
  CertFail{step: Nat}

type Step is Data:
  Step{r: Nat, s: Nat, left: Bool}

# F32 guess
# ---------

def PtF.x(p: PtF) -> F32:
  match p:
    case PtF{x, _}:
      x

def PtF.y(p: PtF) -> F32:
  match p:
    case PtF{_, y}:
      y

# an integer at scale 2^−P as an F32 in nm
def tof(x: I.Int, +P: Nat) -> F32:
  I.Int.to_f32(I.Int.shr_floor(x, P))

def ptf(p: Pt, +P: Nat) -> PtF:
  match p:
    case Pt{x, y}:
      PtF{tof(x, P), tof(y, P)}

def sgn(left: Bool) -> F32:
  match left:
    case True{}:
      1.0
    case False{}:
      (0.0 - 1.0 : F32)

# closed-form circle∩circle in F32: distance r from A, s from B
def guess.go(+ax: F32, +ay: F32, +dx: F32, +dy: F32, +r: F32, +s: F32, +sg: F32) -> PtF:
  +D = (dx * dx + dy * dy : F32)
  +k = ((D + r * r - s * s) / (2.0 * D) : F32)
  +h = (F32.sqrt(F32.max((r * r - k * k * D : F32), 0.0)) / F32.sqrt(D) : F32)
  PtF{(ax + k * dx - sg * h * dy : F32), (ay + k * dy + sg * h * dx : F32)}

def guess(a: PtF, b: PtF, r: Nat, s: Nat, left: Bool) -> PtF:
  match a b:
    case PtF{+ax, +ay} PtF{bx, by}:
      guess.go(ax, ay, (bx - ax : F32), (by - ay : F32), F32.from_nat(r), F32.from_nat(s), sgn(left))

# an F32 in nm as an integer at scale 2^−P (|x| < 2^31)
def fromf(x: F32, +P: Nat) -> I.Int:
  I.Int.shl(I.Int.from_f32(x), P)

# an F32 entry of Y (~2^−20 to 2^−35) at scale 2^−P, through 2^50 (P ≥ 50)
def fromy(y: F32, +P: Nat) -> I.Int:
  I.Int.shl(I.Int.from_f32((y * 1125899906842624.0 : F32)), Nat.sub(P, 50n))

# Y ≈ J⁻¹ for J = 2[(y − a)ᵀ; (y − b)ᵀ], computed in F32
def ymat.go(+j11: F32, +j12: F32, +j21: F32, +j22: F32, +P: Nat) -> M2:
  +det = (j11 * j22 - j12 * j21 : F32)
  M2{fromy((j22 / det : F32), P), fromy((0.0 - j12 / det : F32), P), fromy((0.0 - j21 / det : F32), P), fromy((j11 / det : F32), P)}

def ymat(y: PtF, a: PtF, b: PtF, +P: Nat) -> M2:
  match y a b:
    case PtF{+yx, +yy} PtF{ax, ay} PtF{bx, by}:
      ymat.go((2.0 * (yx - ax) : F32), (2.0 * (yy - ay) : F32), (2.0 * (yx - bx) : F32), (2.0 * (yy - by) : F32), P)

# Exact refinement
# ----------------

# |p − c|²
def dist2(p: Pt, c: Pt) -> I.Int:
  match p c:
    case Pt{px, py} Pt{cx, cy}:
      +dx = zsub(px, cx)
      +dy = zsub(py, cy)
      zadd(zmul(dx, dx), zmul(dy, dy))

# Y·(f1, f2), as a point at scale 2^(−3P)
def ymul(Y: M2, +f1: I.Int, +f2: I.Int) -> Pt:
  match Y:
    case M2{a, b, c, d}:
      Pt{zadd(zmul(a, f1), zmul(b, f2)), zadd(zmul(c, f1), zmul(d, f2))}

# one simplified-Newton step y ← y − Y·f(y)
def newton.step(y: Pt, +d: Pt, +P: Nat) -> Pt:
  match y d:
    case Pt{yx, yy} Pt{dx, dy}:
      Pt{zsub(yx, I.Int.shr_floor(dx, Nat.mul(2n, P))), zsub(yy, I.Int.shr_floor(dy, Nat.mul(2n, P)))}

def newton(fuel: Nat, +y: Pt, +a: Pt, +b: Pt, +r2: I.Int, +s2: I.Int, +Y: M2, +P: Nat) -> Pt:
  match fuel:
    case 0n:
      y
    case 1n+f:
      newton(f, newton.step(y, ymul(Y, zsub(dist2(y, a), r2), zsub(dist2(y, b), s2)), P), a, b, r2, s2, Y, P)

# Certificate
# -----------

# ‖(u, v)‖₁ and ‖(u, v)‖∞
def n1(u: I.Int, v: I.Int) -> I.Int:
  zadd(zabs(u), zabs(v))

def ninf(u: I.Int, v: I.Int) -> I.Int:
  zmax(zabs(u), zabs(v))

def pt.sub(p: Pt, q: Pt) -> Pt:
  match p q:
    case Pt{px, py} Pt{qx, qy}:
      Pt{zsub(px, qx), zsub(py, qy)}

def pt.n1(p: Pt) -> I.Int:
  match p:
    case Pt{x, y}:
      n1(x, y)

def pt.ninf(p: Pt) -> I.Int:
  match p:
    case Pt{x, y}:
      ninf(x, y)

# ‖Y‖∞ at scale 2^−P
def m.ninf(Y: M2) -> I.Int:
  match Y:
    case M2{a, b, c, d}:
      zmax(n1(a, b), n1(c, d))

# ‖I − Y·J‖∞ at scale 2^(−2P); J rows are u = 2(ỹ − a), v = 2(ỹ − b)
def q0(Y: M2, u: Pt, v: Pt, +P: Nat) -> I.Int:
  match Y u v:
    case M2{+a, +b, +c, +d} Pt{+ux, +uy} Pt{+vx, +vy}:
      +one = I.Int.shl(zlit(1n), Nat.mul(2n, P))
      +e11 = zsub(one, zadd(zmul(a, ux), zmul(b, vx)))
      +e12 = zneg(zadd(zmul(a, uy), zmul(b, vy)))
      +e21 = zneg(zadd(zmul(c, ux), zmul(d, vx)))
      +e22 = zsub(one, zadd(zmul(c, uy), zmul(d, vy)))
      zmax(n1(e11, e12), n1(e21, e22))

# ‖Y·J_z‖∞ for f_1 = |y − a|² − r², f_2 = |y − b|² − s² against the parents:
# row i is |Y_i1|·2‖u‖₁ + |Y_i2|·2‖v‖₁ with u = ỹ − a, v = ỹ − b; scale 2^(−2P)
def yjz(Y: M2, +nu: I.Int, +nv: I.Int) -> I.Int:
  match Y:
    case M2{a, b, c, d}:
      I.Int.shl(zmax(zadd(zmul(zabs(a), nu), zmul(zabs(b), nv)), zadd(zmul(zabs(c), nu), zmul(zabs(d), nv))), 1n)

def twice(p: Pt) -> Pt:
  match p:
    case Pt{x, y}:
      Pt{I.Int.shl(x, 1n), I.Int.shl(y, 1n)}

# the conditions for radius r: q < 1 and A + B ≤ (1 − q)·r
def cert.cond(+r: I.Int, +q0v: I.Int, +nY: I.Int, +AB: I.Int, +rho: I.Int, +P: Nat) -> Bool:
  +q = zadd(q0v, zmul(nY, I.Int.shl(zadd(r, rho), 2n)))
  +one = I.Int.shl(zlit(1n), Nat.mul(2n, P))
  Bool.and(Bool.not(zle(one, q)), zle(AB, zmul(zsub(one, q), r)))

# tries r, then 2r, 4r, … while fuel lasts
def cert.ok(fuel: Nat, good: Bool, k: Nat, +r: I.Int, +q0v: I.Int, +nY: I.Int, +AB: I.Int, +rho: I.Int, +P: Nat, +y: Pt) -> Res:
  match fuel:
    case 0n:
      CertFail{k}
    case 1n+f:
      match good:
        case True{}:
          CertOk{Cert{y, r}}
        case False{}:
          cert.ok(f, cert.cond(I.Int.shl(r, 1n), q0v, nY, AB, rho, P), k, I.Int.shl(r, 1n), q0v, nY, AB, rho, P, y)

# one step: guess, refine, certify
def step.go(k: Nat, a: Cert, b: Cert, st: Step, +P: Nat, iters: Nat) -> Res:
  match a b st:
    case Cert{+ac, ar} Cert{+bc, br} Step{+r, +s, left}:
      +rho = zmax(ar, br)
      +af = ptf(ac, P)
      +bf = ptf(bc, P)
      +g = guess(af, bf, r, s, left)
      +Y = ymat(g, af, bf, P)
      +r2 = I.Int.shl(zmul(zlit(r), zlit(r)), Nat.mul(2n, P))
      +s2 = I.Int.shl(zmul(zlit(s), zlit(s)), Nat.mul(2n, P))
      +y = newton(iters, Pt{fromf(PtF.x(g), P), fromf(PtF.y(g), P)}, ac, bc, r2, s2, Y, P)
      +f1 = zsub(dist2(y, ac), r2)
      +f2 = zsub(dist2(y, bc), s2)
      +A = pt.ninf(ymul(Y, f1, f2))
      +nY = m.ninf(Y)
      +AB = zadd(A, zadd(zmul(yjz(Y, pt.n1(pt.sub(y, ac)), pt.n1(pt.sub(y, bc))), rho), zmul(nY, I.Int.shl(zmul(rho, rho), 1n))))
      +q0v = q0(Y, twice(pt.sub(y, ac)), twice(pt.sub(y, bc)), P)
      +r0 = zadd(I.Int.shr_ceil(zmul(AB, zlit(65537n)), Nat.add(16n, Nat.mul(2n, P))), zlit(1n))
      cert.ok(8n, cert.cond(r0, q0v, nY, AB, rho, P), k, r0, q0v, nY, AB, rho, P, y)


# Driver
# ------

# runs the chain from P_{k−2} = a and P_{k−1} = rb (the previous result);
# returns every result, stopping at the first failure
def chain.go(steps: List<&2, Step>, rb: Res, +k: Nat, +a: Cert, +P: Nat, +iters: Nat) -> List<&2, Res>:
  match steps:
    case Nil{}:
      Con{rb, Nil{}}
    case Con{st, rest}:
      match rb:
        case CertFail{j}:
          Con{CertFail{j}, Nil{}}
        case CertOk{+b}:
          Con{CertOk{b}, chain.go(rest, step.go(k, a, b, st, P, iters), 1n+k, b, P, iters)}

# P0 = (0, 0) and P1 = (L, 0), pinned exactly (radius 0)
def chain(steps: List<&2, Step>, +L: Nat, +P: Nat, +iters: Nat) -> List<&2, Res>:
  chain.go(steps, CertOk{Cert{Pt{I.Int.shl(zlit(L), P), zlit(0n)}, zlit(0n)}}, 2n, Cert{Pt{zlit(0n), zlit(0n)}, zlit(0n)}, P, iters)

def rexp.if(up: Bool, +b: Nat, +P: Nat) -> String:
  match up:
    case True{}:
      "+" ++ Nat.show(Nat.sub(b, P))
    case False{}:
      "-" ++ Nat.show(Nat.sub(P, b))

# log2 of a radius in nm, as bits(r) − P
def rexp(+r: I.Int, +P: Nat) -> String:
  rexp.if(Nat.is_le(P, I.Int.bits(r)), I.Int.bits(r), P)

def res.show(r: Res, +P: Nat) -> String:
  match r:
    case CertOk{c}:
      match c:
        case Cert{_, rr}:
          rexp(rr, P)
    case CertFail{k}:
      "FAIL@" ++ Nat.show(k)

def show.all(rs: List<&2, Res>, +P: Nat) -> String:
  match rs:
    case Nil{}:
      ""
    case Con{r, t}:
      res.show(r, P) ++ " " ++ show.all(t, P)

# the last result
def last.fin(m: Maybe<&2, Res>, +P: Nat) -> String:
  match m:
    case None{}:
      "none"
    case Some{r}:
      res.show(r, P)

def last(rs: List<&2, Res>, +P: Nat) -> String:
  last.fin(List.last(&2, Res, rs), P)
