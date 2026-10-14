# proto/block.bend: sk-P1 spike for one large cyclic block. Untrusted.
#
# Unknowns x (m coordinates at scale 2^−P nm; index m reads as a pinned 0),
# equations f_e = |P_u − P_v|² − d_e² for the m edges of a rigid framework.
# The proposer supplies x̃ (float64 quality) and Yᵀ (an F32-quality inverse of
# J, transposed). Bend refines x̃ by simplified Newton in exact arithmetic and
# checks the contraction certificate exactly (no parameters, ρ = 0):
#   q = ‖I − Y·J(x̃)‖∞ + ‖Y‖∞·16r < 1,   ‖Y·f(x̃)‖∞ ≤ (1 − q)·r
# (each J row has at most 4 entries ±2Δ, each moving by ≤ 4r over the ball).
# Y·J, Y·f and the row sums are sums of scaled Y columns (rows of Yᵀ), so the
# exact work is O(m²) bigint operations.

import Base
import ./int.bend as I

def zadd(a: I.Int, b: I.Int) -> I.Int:
  I.Int.add(a, b)

def zsub(a: I.Int, b: I.Int) -> I.Int:
  I.Int.sub(a, b)

def zmul(a: I.Int, b: I.Int) -> I.Int:
  I.Int.mul(a, b)

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

# decimal parsing (values may exceed the 2^48 Nat literal range)
def zdec.digits(cs: String, acc: List<&2, Nat>) -> List<&2, Nat>:
  match cs:
    case SNil{}:
      acc
    case SCon{c, t}:
      zdec.digits(t, I.Mag.add(I.Mag.norm(I.Mag.mul1(acc, 10n)), I.Mag.from_nat(Nat.sub(U32.to_nat(Char.to_u32(c)), 48n))))

def zdec.sign(neg: Bool, c: Char, t: String) -> I.Int:
  match neg:
    case True{}:
      I.Int.mk_neg(zdec.digits(t, Nil{}))
    case False{}:
      I.Pos{zdec.digits(SCon{c, t}, Nil{})}

def zdec(s: String) -> I.Int:
  match s:
    case SNil{}:
      zlit(0n)
    case SCon{+c, t}:
      zdec.sign(Char.is_eq(c, '-'), c, t)

# Data
# ----

type Edge is Data:
  Edge{iux: Nat, iuy: Nat, ivx: Nat, ivy: Nat, d: Nat}

# J[e][c] = ±2·Δ (Δ = dx or dy of edge e), + when the coordinate is on u
type JEnt is Data:
  JEnt{e: Nat, plus: Bool, isy: Bool}

type D2 is Data:
  D2{dx: I.Int, dy: I.Int}

# Vectors
# -------

def get0.fin(m: Maybe<&2, I.Int>) -> I.Int:
  match m:
    case None{}:
      zlit(0n)
    case Some{v}:
      v

def get0(xs: List<&2, I.Int>, i: Nat) -> I.Int:
  get0.fin(List.get(&2, I.Int, xs, i))

def vadd(a: List<&2, I.Int>, b: List<&2, I.Int>) -> List<&2, I.Int>:
  match a b:
    case Con{x, xs} Con{y, ys}:
      Con{zadd(x, y), vadd(xs, ys)}
    case _ _:
      Nil{}

def vscale(+k: I.Int, v: List<&2, I.Int>) -> List<&2, I.Int>:
  match v:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{zmul(k, x), vscale(k, t)}

def vabs(v: List<&2, I.Int>) -> List<&2, I.Int>:
  match v:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{I.Int.abs(x), vabs(t)}

def vmax(v: List<&2, I.Int>) -> I.Int:
  match v:
    case Nil{}:
      zlit(0n)
    case Con{x, t}:
      zmax(x, vmax(t))

def vzero(n: Nat) -> List<&2, I.Int>:
  List.replicate(I.Int, n, zlit(0n))

# |e_c·one − v|, entrywise, for the unit vector e_c
def vunit_abs(v: List<&2, I.Int>, c: Nat, +one: I.Int) -> List<&2, I.Int>:
  match v:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      match c:
        case 0n:
          Con{I.Int.abs(zsub(one, x)), vabs(t)}
        case 1n+cp:
          Con{I.Int.abs(x), vunit_abs(t, cp, one)}

# Σ_e s_e·Yᵀ[e]
def ycomb(s: List<&2, I.Int>, yt: List<&2, List<&2, I.Int>>, +acc: List<&2, I.Int>) -> List<&2, I.Int>:
  match s yt:
    case Con{se, st} Con{ye, yrest}:
      ycomb(st, yrest, vadd(acc, vscale(se, ye)))
    case _ _:
      acc

# Residuals and Jacobian
# ----------------------

def diffs(edges: List<&2, Edge>, +x: List<&2, I.Int>) -> List<&2, D2>:
  match edges:
    case Nil{}:
      Nil{}
    case Con{ed, t}:
      match ed:
        case Edge{iux, iuy, ivx, ivy, _}:
          Con{D2{zsub(get0(x, iux), get0(x, ivx)), zsub(get0(x, iuy), get0(x, ivy))}, diffs(t, x)}

# f_e at scale 2^(−2P)
def fvec(ds: List<&2, D2>, edges: List<&2, Edge>, +P: Nat) -> List<&2, I.Int>:
  match ds edges:
    case Con{D2{+dx, +dy}, dt} Con{Edge{_, _, _, _, +d}, et}:
      Con{zsub(zadd(zmul(dx, dx), zmul(dy, dy)), I.Int.shl(zmul(zlit(d), zlit(d)), Nat.mul(2n, P))), fvec(dt, et, P)}
    case _ _:
      Nil{}

def d2.get.fin(m: Maybe<&2, D2>) -> D2:
  match m:
    case None{}:
      D2{zlit(0n), zlit(0n)}
    case Some{v}:
      v

def jval.sign(plus: Bool, v: I.Int) -> I.Int:
  match plus:
    case True{}:
      v
    case False{}:
      I.Int.neg(v)

def jval.fin(d: D2, plus: Bool, isy: Bool) -> I.Int:
  match d isy:
    case D2{_, dy} True{}:
      jval.sign(plus, I.Int.shl(dy, 1n))
    case D2{dx, _} False{}:
      jval.sign(plus, I.Int.shl(dx, 1n))

def yrow.fin(m: Maybe<&2, List<&2, I.Int>>) -> List<&2, I.Int>:
  match m:
    case None{}:
      Nil{}
    case Some{v}:
      v

def yrow(yt: List<&2, List<&2, I.Int>>, e: Nat) -> List<&2, I.Int>:
  yrow.fin(List.get(&2, List<&2, I.Int>, yt, e))

# column c of Y·J: Σ over J's column entries of J[e][c]·Yᵀ[e]
def yjcol(col: List<&2, JEnt>, +ds: List<&2, D2>, +yt: List<&2, List<&2, I.Int>>, +acc: List<&2, I.Int>) -> List<&2, I.Int>:
  match col:
    case Nil{}:
      acc
    case Con{JEnt{e, plus, isy}, t}:
      +ee = e
      yjcol(t, ds, yt, vadd(acc, vscale(jval.fin(d2.get.fin(List.get(&2, D2, ds, ee)), plus, isy), yrow(yt, ee))))

# row sums of |I − Y·J|, accumulated column by column
def q0.go(cols: List<&2, List<&2, JEnt>>, c: Nat, +m: Nat, +ds: List<&2, D2>, +yt: List<&2, List<&2, I.Int>>, +one: I.Int, +acc: List<&2, I.Int>) -> List<&2, I.Int>:
  match cols:
    case Nil{}:
      acc
    case Con{col, t}:
      +cc = c
      q0.go(t, 1n+cc, m, ds, yt, one, vadd(acc, vunit_abs(yjcol(col, ds, yt, vzero(m)), cc, one)))

# Refinement and certificate
# --------------------------

def vshr(v: List<&2, I.Int>, +n: Nat) -> List<&2, I.Int>:
  match v:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      Con{I.Int.shr_floor(x, n), vshr(t, n)}

def vsub(a: List<&2, I.Int>, b: List<&2, I.Int>) -> List<&2, I.Int>:
  match a b:
    case Con{x, xs} Con{y, ys}:
      Con{zsub(x, y), vsub(xs, ys)}
    case _ _:
      Nil{}

# Y·f(x) at scale 2^(−3P)
def yf(+edges: List<&2, Edge>, +x: List<&2, I.Int>, +yt: List<&2, List<&2, I.Int>>, +m: Nat, +P: Nat) -> List<&2, I.Int>:
  ycomb(fvec(diffs(edges, x), edges, P), yt, vzero(m))

def newton(fuel: Nat, +x: List<&2, I.Int>, +edges: List<&2, Edge>, +yt: List<&2, List<&2, I.Int>>, +m: Nat, +P: Nat) -> List<&2, I.Int>:
  match fuel:
    case 0n:
      x
    case 1n+f:
      newton(f, vsub(x, vshr(yf(edges, x, yt, m, P), Nat.mul(2n, P))), edges, yt, m, P)

def cond(+r: I.Int, +q0v: I.Int, +nY: I.Int, +A: I.Int, +one: I.Int) -> Bool:
  +q = zadd(q0v, zmul(nY, I.Int.shl(r, 4n)))
  Bool.and(Bool.not(zle(one, q)), zle(A, zmul(zsub(one, q), r)))

type Out is Data:
  Out{ok: Bool, r: I.Int, q0: I.Int}

def search(fuel: Nat, good: Bool, +r: I.Int, +q0v: I.Int, +nY: I.Int, +A: I.Int, +one: I.Int) -> Out:
  match fuel:
    case 0n:
      Out{False{}, r, q0v}
    case 1n+f:
      match good:
        case True{}:
          Out{True{}, r, q0v}
        case False{}:
          search(f, cond(I.Int.shl(r, 1n), q0v, nY, A, one), I.Int.shl(r, 1n), q0v, nY, A, one)

def yabs(yt: List<&2, List<&2, I.Int>>) -> List<&2, List<&2, I.Int>>:
  match yt:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{vabs(r), yabs(t)}

# refine, then certify
def certify(+edges: List<&2, Edge>, x0: List<&2, I.Int>, +yt: List<&2, List<&2, I.Int>>, +cols: List<&2, List<&2, JEnt>>, +m: Nat, +P: Nat, iters: Nat) -> Out:
  +x = newton(iters, x0, edges, yt, m, P)
  +one = I.Int.shl(zlit(1n), Nat.mul(2n, P))
  +q0v = vmax(q0.go(cols, 0n, m, diffs(edges, x), yt, one, vzero(m)))
  +nY = vmax(ycomb(List.replicate(I.Int, m, zlit(1n)), yabs(yt), vzero(m)))
  +A = vmax(vabs(yf(edges, x, yt, m, P)))
  +r0 = zadd(I.Int.shr_ceil(zmul(A, zlit(65537n)), Nat.add(16n, Nat.mul(2n, P))), zlit(1n))
  search(12n, cond(r0, q0v, nY, A, one), r0, q0v, nY, A, one)

# log2 of a value at scale 2^−s, as a signed string
def lg.if(up: Bool, +b: Nat, +s: Nat) -> String:
  match up:
    case True{}:
      "+" ++ Nat.show(Nat.sub(b, s))
    case False{}:
      "-" ++ Nat.show(Nat.sub(s, b))

def lg(+v: I.Int, +s: Nat) -> String:
  lg.if(Nat.is_le(s, I.Int.bits(v)), I.Int.bits(v), s)

def Out.show(o: Out, +P: Nat) -> String:
  match o:
    case Out{ok, r, q0}:
      Bool.show(ok) ++ " log2(r/nm)=" ++ lg(r, P) ++ " log2(q0)=" ++ lg(q0, Nat.mul(2n, P))

# Loading (text files written by gen_block.py)
# -------

def toks(s: String) -> List<&2, String>:
  String.split(s, ' ')

def nat.fin(m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{n}:
      n

def tok.nat(s: String) -> Nat:
  nat.fin(Nat.read(s))

def ints(ts: List<&2, String>) -> List<&2, I.Int>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, rest}:
      Con{zdec(t), ints(rest)}

def nats(ts: List<&2, String>) -> List<&2, Nat>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, rest}:
      Con{tok.nat(t), nats(rest)}

def rows(ls: List<&2, String>) -> List<&2, List<&2, I.Int>>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      Con{ints(toks(l)), rows(rest)}

def edge.of(ns: List<&2, Nat>) -> List<&2, Edge>:
  match ns:
    case Con{a, Con{b, Con{c, Con{d, Con{e, _}}}}}:
      [Edge{a, b, c, d, e}]
    case _:
      Nil{}

def edges.of(ls: List<&2, String>) -> List<&2, Edge>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      List.append(&2, Edge, edge.of(nats(toks(l))), edges.of(rest))

def is1(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+_:
      True{}

def jents(ns: List<&2, Nat>) -> List<&2, JEnt>:
  match ns:
    case Con{e, Con{s, Con{a, rest}}}:
      Con{JEnt{e, is1(s), is1(a)}, jents(rest)}
    case _:
      Nil{}

def jcols.of(ls: List<&2, String>) -> List<&2, List<&2, JEnt>>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{l, rest}:
      Con{jents(nats(toks(l))), jcols.of(rest)}

def slurp.got(g: File & Result<&1, &1, U32 & String, String>) -> IO(String):
  (f, r) = g
  do IO<String>:
    data : String <- IO.pass(String, r)
    u : Unit <- File.close(f)
    return data

def slurp.sized(z: File & Result<&1, &1, U32 & String, U32>) -> IO(String):
  (f, r) = z
  do IO<String>:
    n : U32 <- IO.pass(U32, r)
    g : File & Result<&1, &1, U32 & String, String> <- File.read(f, n)
    slurp.got(g)

def slurp(path: String) -> IO(String):
  do IO<String>:
    f : File <- IO.try(File, File.open(path, "r"))
    z : File & Result<&1, &1, U32 & String, U32> <- File.size(f)
    slurp.sized(z)
