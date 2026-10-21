# W0 spike (PLAN-sk13w): dyadics with machine-word limbs against S.D, on a
# real matrix (slowsketches sketch(6)'s 32x32 block, its Jacobian from
# proto/probe_block stage 4). Untrusted and unverified: it only measures,
# and checks that the word results are the S.D results exactly (same
# mantissa, same exponent). Reads ./J.txt and ./mode.in (see run below).
# Build: bin/bend proto/w0bench.bend -o w0bench

import Base
import ../spec/num.bend as S
import ../spec/big.bend as SB
import ../rt/mag.bend as RM
import ../rt/big.bend as RB
import ../lib/numer.bend as NU
import ../lib/qreduce.bend as QRD
import ../lib/karith.bend as KA
import ../lib/kinst.bend as KI
import ../spec/knum.bend as N
import ./block.bend as B

# Native comparisons
# ------------------

def le.go(c: Cmp) -> Bool:
  match c:
    case LT{}:
      True{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

def le(a: Nat, b: Nat) -> Bool:
  le.go(Nat.cmp(a, b))

def eq.go(c: Cmp) -> Bool:
  match c:
    case LT{}:
      False{}
    case EQ{}:
      True{}
    case GT{}:
      False{}

def eq(a: Nat, b: Nat) -> Bool:
  eq.go(Nat.cmp(a, b))

def band(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      False{}

# Limbs in base 2^23
# ------------------

def bp() -> Nat:
  8388607n

# 2^j
def p2(j: Nat) -> Nat:
  match j:
    case 0n:
      1n
    case 1n+k:
      Nat.mul(2n, p2(k))

# n zero limbs below m
def zl(n: Nat, m: List<&2, Nat>) -> List<&2, Nat>:
  match n:
    case 0n:
      m
    case 1n+j:
      Con{0n, zl(j, m)}

# m 2^k
def mshl(m: List<&2, Nat>, +k: Nat) -> List<&2, Nat>:
  match m:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      zl(Nat.div(k, 23n), RM.Mag.mul1(bp(), Con{h, t}, p2(Nat.mod(k, 23n)), 0n))

def ldrop(n: Nat, m: List<&2, Nat>) -> List<&2, Nat>:
  match n m:
    case 0n m:
      m
    case 1n+j Nil{}:
      Nil{}
    case 1n+j Con{h, t}:
      ldrop(j, t)

# floor(m / d) for d = 2^s, s < 23, u = 2^(23 - s)
def msr(t: List<&2, Nat>, h: Nat, +d: Nat, +u: Nat) -> List<&2, Nat>:
  match t:
    case Nil{}:
      Con{Nat.div(h, d), Nil{}}
    case Con{+h2, t2}:
      Con{Nat.add(Nat.div(h, d), Nat.mul(Nat.mod(h2, d), u)), msr(t2, h2, d, u)}

def msr.go(m: List<&2, Nat>, +d: Nat, +u: Nat) -> List<&2, Nat>:
  match m:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      msr(t, h, d, u)

# floor(m / 2^k)
def mshr(m: List<&2, Nat>, +k: Nat) -> List<&2, Nat>:
  RM.Mag.norm(msr.go(ldrop(Nat.div(k, 23n), m), p2(Nat.mod(k, 23n)), p2(Nat.sub(23n, Nat.mod(k, 23n)))))

# floor((m + 2^(k-1)) / 2^k), k >= 1: nearest, halves up
def mround(m: List<&2, Nat>, +k: Nat) -> List<&2, Nat>:
  mshr(RM.Mag.add(bp(), m, mshl(Con{1n, Nil{}}, Nat.sub(k, 1n))), k)

# binary digits of a limb
def nb(f: Nat, x: Nat) -> Nat:
  match f x:
    case 0n x:
      0n
    case 1n+g 0n:
      0n
    case 1n+g 1n+j:
      1n+nb(g, Nat.div(Nat.add(j, 1n), 2n))

def nbits(x: Nat) -> Nat:
  nb(24n, x)

def mbits.go(t: List<&2, Nat>, h: Nat) -> Nat:
  match t:
    case Nil{}:
      nbits(h)
    case Con{h2, t2}:
      Nat.add(23n, mbits.go(t2, h2))

# binary digits of a normalized magnitude
def mbits(m: List<&2, Nat>) -> Nat:
  match m:
    case Nil{}:
      0n
    case Con{h, t}:
      mbits.go(t, h)

# Signed
# ------

def bmag(x: SB.Big) -> List<&2, Nat>:
  match x:
    case SB.BPos{m}:
      m
    case SB.BNeg{m}:
      m

def bnorm(x: SB.Big) -> SB.Big:
  match x:
    case SB.BPos{m}:
      SB.BPos{RM.Mag.norm(m)}
    case SB.BNeg{m}:
      SB.BNeg{RM.Mag.norm(m)}

def bshl(x: SB.Big, +k: Nat) -> SB.Big:
  match x:
    case SB.BPos{m}:
      SB.BPos{mshl(m, k)}
    case SB.BNeg{m}:
      SB.BNeg{mshl(m, k)}

def bround(x: SB.Big, +k: Nat) -> SB.Big:
  match x:
    case SB.BPos{m}:
      SB.BPos{mround(m, k)}
    case SB.BNeg{m}:
      SB.BNeg{mround(m, k)}

def babs(x: SB.Big) -> SB.Big:
  match x:
    case SB.BPos{m}:
      SB.BPos{m}
    case SB.BNeg{m}:
      SB.BPos{m}

# Word dyadics m 2^-e
# -------------------

type WD is Data:
  WD{m: SB.Big, e: Nat}

def wd.m(x: WD) -> SB.Big:
  match x:
    case WD{m, e}:
      m

def wd.e(x: WD) -> Nat:
  match x:
    case WD{m, e}:
      e

def wzero() -> WD:
  WD{SB.BPos{Nil{}}, 0n}

def wone() -> WD:
  WD{SB.BPos{Con{1n, Nil{}}}, 0n}

# S.D.add: the larger exponent, the other mantissa shifted up to it
def wadd.go(l: Bool, +a: WD, +b: WD) -> WD:
  match l:
    case True{}:
      WD{bnorm(RB.Big.add(bp(), bshl(wd.m(a), Nat.sub(wd.e(b), wd.e(a))), wd.m(b))), wd.e(b)}
    case False{}:
      WD{bnorm(RB.Big.add(bp(), wd.m(a), bshl(wd.m(b), Nat.sub(wd.e(a), wd.e(b))))), wd.e(a)}

def wadd(+a: WD, +b: WD) -> WD:
  wadd.go(le(wd.e(a), wd.e(b)), a, b)

def wmul(+a: WD, +b: WD) -> WD:
  WD{bnorm(RB.Big.mul(bp(), wd.m(a), wd.m(b))), Nat.add(wd.e(a), wd.e(b))}

def wneg(+a: WD) -> WD:
  WD{RB.Big.neg(wd.m(a)), wd.e(a)}

def wcmp.go(l: Bool, +a: WD, +b: WD) -> Cmp:
  match l:
    case True{}:
      RB.Big.cmp(bp(), bshl(wd.m(a), Nat.sub(wd.e(b), wd.e(a))), wd.m(b))
    case False{}:
      RB.Big.cmp(bp(), wd.m(a), bshl(wd.m(b), Nat.sub(wd.e(a), wd.e(b))))

def wcmp(+a: WD, +b: WD) -> Cmp:
  wcmp.go(le(wd.e(a), wd.e(b)), a, b)

def wabs(+a: WD) -> WD:
  WD{babs(wd.m(a)), wd.e(a)}

# NU.dznorm: zero at exponent 0
def wznorm.go(m: List<&2, Nat>, x: WD) -> WD:
  match m:
    case Nil{}:
      wzero()
    case Con{h, t}:
      x

def wznorm(+x: WD) -> WD:
  wznorm.go(bmag(wd.m(x)), x)

# NU.dsig: about b significant bits
def wsig.sh(l: Bool, m: SB.Big, +e: Nat, +k: Nat) -> WD:
  match l:
    case True{}:
      WD{bround(m, k), Nat.sub(e, k)}
    case False{}:
      WD{bshl(bround(m, k), Nat.sub(k, e)), 0n}

def wsig.go(l: Bool, +x: WD, +k: Nat) -> WD:
  match l:
    case True{}:
      wznorm(x)
    case False{}:
      wsig.sh(le(k, wd.e(x)), wd.m(x), wd.e(x), k)

def wsig.n(+n: Nat, +x: WD, +b: Nat) -> WD:
  wsig.go(le(n, b), x, Nat.sub(n, b))

def wsig(+x: WD, +b: Nat) -> WD:
  wsig.n(mbits(bmag(wd.m(x))), x, b)

def wsadd(+w: Nat, +a: WD, +b: WD) -> WD:
  wsig(wadd(a, b), w)

def wsmul(+w: Nat, +a: WD, +b: WD) -> WD:
  wsig(wmul(a, b), w)

# Conversions with S.D
# --------------------

# p's bits into limbs; cur holds the current limb's low bits, w = 2^(bits
# so far), c the bits left in the limb
def p2m.go(p: S.Pos, c: Nat, cur: Nat, +w: Nat) -> List<&2, Nat>:
  match p:
    case S.XH{}:
      Con{Nat.add(cur, w), Nil{}}
    case S.XO{q}:
      match c:
        case 0n:
          Nil{}
        case 1n+j:
          match j:
            case 0n:
              Con{cur, p2m.go(q, 23n, 0n, 1n)}
            case 1n+i:
              p2m.go(q, 1n+i, cur, Nat.mul(2n, w))
    case S.XI{q}:
      match c:
        case 0n:
          Nil{}
        case 1n+j:
          match j:
            case 0n:
              Con{Nat.add(cur, w), p2m.go(q, 23n, 0n, 1n)}
            case 1n+i:
              p2m.go(q, 1n+i, Nat.add(cur, w), Nat.mul(2n, w))

def p2m(p: S.Pos) -> List<&2, Nat>:
  p2m.go(p, 23n, 0n, 1n)

def z2b(z: S.Z) -> SB.Big:
  match z:
    case S.Z0{}:
      SB.BPos{Nil{}}
    case S.Zpos{p}:
      SB.BPos{p2m(p)}
    case S.Zneg{p}:
      SB.BNeg{p2m(p)}

def lb.none(bt: Nat) -> Maybe<&2, S.Pos>:
  match bt:
    case 0n:
      None{}
    case 1n+j:
      Some{S.XH{}}

def lb.some(bt: Nat, q: S.Pos) -> Maybe<&2, S.Pos>:
  match bt:
    case 0n:
      Some{S.XO{q}}
    case 1n+j:
      Some{S.XI{q}}

def lb.bit(bt: Nat, r: Maybe<&2, S.Pos>) -> Maybe<&2, S.Pos>:
  match r:
    case None{}:
      lb.none(bt)
    case Some{q}:
      lb.some(bt, q)

# h + 2^k hi, for h < 2^k
def lb(k: Nat, +h: Nat, hi: Maybe<&2, S.Pos>) -> Maybe<&2, S.Pos>:
  match k:
    case 0n:
      hi
    case 1n+j:
      lb.bit(Nat.mod(h, 2n), lb(j, Nat.div(h, 2n), hi))

def m2p(m: List<&2, Nat>) -> Maybe<&2, S.Pos>:
  match m:
    case Nil{}:
      None{}
    case Con{h, t}:
      lb(23n, h, m2p(t))

def m2z.s(neg: Bool, p: S.Pos) -> S.Z:
  match neg:
    case True{}:
      S.Zneg{p}
    case False{}:
      S.Zpos{p}

def m2z(neg: Bool, m: Maybe<&2, S.Pos>) -> S.Z:
  match m:
    case None{}:
      S.Z0{}
    case Some{p}:
      m2z.s(neg, p)

def b2z(x: SB.Big) -> S.Z:
  match x:
    case SB.BPos{m}:
      m2z(False{}, m2p(m))
    case SB.BNeg{m}:
      m2z(True{}, m2p(m))

def s2w(x: S.D) -> WD:
  match x:
    case S.D{m, e}:
      WD{z2b(m), e}

def w2s(x: WD) -> S.D:
  match x:
    case WD{m, e}:
      S.D{b2z(m), e}

def s2wv(xs: List<&2, S.D>) -> List<&2, WD>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{s2w(h), s2wv(t)}

def w2sv(xs: List<&2, WD>) -> List<&2, S.D>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{w2s(h), w2sv(t)}

def s2wm(a: List<&2, List<&2, S.D>>) -> List<&2, List<&2, WD>>:
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{s2wv(r), s2wm(t)}

def w2sm(a: List<&2, List<&2, WD>>) -> List<&2, List<&2, S.D>>:
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{w2sv(r), w2sm(t)}

# division at w bits: through S.D (one per pivot, a small share)
def wsdiv(+w: Nat, a: WD, b: WD) -> WD:
  s2w(NU.dsdiv(w, w2s(a), w2s(b)))

# The dyadic elimination, mirrored (lib/numer.bend: dinverse)
# -----------------------------------------------------------

def wget(xs: List<&2, WD>, k: Nat) -> WD:
  match xs k:
    case Nil{} k:
      wzero()
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      wget(t, j)

def wrow(xs: List<&2, List<&2, WD>>, k: Nat) -> List<&2, WD>:
  match xs k:
    case Nil{} k:
      Nil{}
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      wrow(t, j)

def wset(xs: List<&2, List<&2, WD>>, k: Nat, +r: List<&2, WD>) -> List<&2, List<&2, WD>>:
  match xs k:
    case Nil{} k:
      Nil{}
    case Con{h, t} 0n:
      Con{r, t}
    case Con{h, t} 1n+j:
      Con{h, wset(t, j, r)}

def wscale(+w: Nat, +c: WD, xs: List<&2, WD>) -> List<&2, WD>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{wsmul(w, c, x), wscale(w, c, t)}

def waxpy(+w: Nat, xs: List<&2, WD>, +c: WD, ys: List<&2, WD>) -> List<&2, WD>:
  match xs ys:
    case Nil{} ys:
      Nil{}
    case Con{x, t} Nil{}:
      Con{x, t}
    case Con{+x, t} Con{+y, u}:
      Con{wsadd(w, x, wneg(wsmul(w, c, y))), waxpy(w, t, c, u)}

def wzeros(n: Nat) -> List<&2, WD>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Con{wzero(), wzeros(m)}

def wunit(n: Nat, +k: Nat) -> List<&2, WD>:
  match n k:
    case 0n k:
      Nil{}
    case 1n+m 0n:
      Con{wone(), wzeros(m)}
    case 1n+m 1n+j:
      Con{wzero(), wunit(m, j)}

def wapp(xs: List<&2, WD>, ys: List<&2, WD>) -> List<&2, WD>:
  match xs:
    case Nil{}:
      ys
    case Con{h, t}:
      Con{h, wapp(t, ys)}

def waugment(a: List<&2, List<&2, WD>>, +n: Nat, +k: Nat) -> List<&2, List<&2, WD>>:
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{wapp(r, wunit(n, k)), waugment(t, n, 1n+k)}

def wdrop(n: Nat, xs: List<&2, WD>) -> List<&2, WD>:
  match n xs:
    case 0n xs:
      xs
    case 1n+m Nil{}:
      Nil{}
    case 1n+m Con{h, t}:
      wdrop(m, t)

def wmax.go(c: Cmp, a: WD, b: WD) -> WD:
  match c:
    case LT{}:
      b
    case EQ{}:
      a
    case GT{}:
      a

def wmax(+a: WD, +b: WD) -> WD:
  wmax.go(wcmp(a, b), a, b)

def wpivot.bx(l: Bool, +bx: WD, +x: WD) -> WD:
  match l:
    case False{}:
      bx
    case True{}:
      wmax(bx, x)

def wpivot(rows: List<&2, List<&2, WD>>, +c: Nat, +k: Nat, +i: Nat, best: Maybe<&2, Nat>, +bx: WD) -> Maybe<&2, Nat>:
  match rows:
    case Nil{}:
      best
    case Con{+r, t}:
      wpivot(t, c, k, 1n+i, NU.dpivot.best(le(k, i), wcmp(wabs(wget(r, c)), bx), i, best), wpivot.bx(le(k, i), bx, wabs(wget(r, c))))

def wswap(+rows: List<&2, List<&2, WD>>, +a: Nat, +b: Nat) -> List<&2, List<&2, WD>>:
  wset(wset(rows, a, wrow(rows, b)), b, wrow(rows, a))

def wclear.ax(+w: Nat, +r: List<&2, WD>, +p: List<&2, WD>, +c: Nat) -> List<&2, WD>:
  waxpy(w, r, wget(r, c), p)

def wclear.go(b: Bool, +w: Nat, +r: List<&2, WD>, +p: List<&2, WD>, +c: Nat) -> List<&2, WD>:
  match b:
    case True{}:
      p
    case False{}:
      wclear.ax(w, r, p, c)

def wclear(rows: List<&2, List<&2, WD>>, +w: Nat, +p: List<&2, WD>, +c: Nat, +i: Nat) -> List<&2, List<&2, WD>>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{wclear.go(eq(i, c), w, r, p, c), wclear(t, w, p, c, 1n+i)}

def welim(+w: Nat, +rows: List<&2, List<&2, WD>>, +c: Nat) -> List<&2, List<&2, WD>>:
  wclear(rows, w, wscale(w, wsdiv(w, wone(), wget(wrow(rows, c), c)), wrow(rows, c)), c, 0n)

def wgj(k: Nat, +w: Nat, +c: Nat, piv: Maybe<&2, Nat>, +rows: List<&2, List<&2, WD>>) -> Maybe<&2, List<&2, List<&2, WD>>>:
  match k piv:
    case 0n piv:
      Some{rows}
    case 1n+m None{}:
      None{}
    case 1n+m Some{r}:
      +rows2 = welim(w, wswap(rows, c, r), c)
      wgj(m, w, 1n+c, wpivot(rows2, 1n+c, 1n+c, 0n, None{}, wzero()), rows2)

def wrights(+n: Nat, rows: List<&2, List<&2, WD>>) -> List<&2, List<&2, WD>>:
  match rows:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{wdrop(n, r), wrights(n, t)}

def winv.of(+n: Nat, m: Maybe<&2, List<&2, List<&2, WD>>>) -> Maybe<&2, List<&2, List<&2, WD>>>:
  match m:
    case None{}:
      None{}
    case Some{rows}:
      Some{wrights(n, rows)}

def wgj0(+n: Nat, +w: Nat, +rows: List<&2, List<&2, WD>>) -> Maybe<&2, List<&2, List<&2, WD>>>:
  wgj(n, w, 0n, wpivot(rows, 0n, 0n, 0n, None{}, wzero()), rows)

def winverse(+n: Nat, +w: Nat, a: List<&2, List<&2, WD>>) -> Maybe<&2, List<&2, List<&2, WD>>>:
  winv.of(n, wgj0(n, w, waugment(a, n, 0n)))

def mlen(a: List<&2, List<&2, S.D>>) -> Nat:
  match a:
    case Nil{}:
      0n
    case Con{r, t}:
      1n+mlen(t)

# The word instance of the checker's numbers
# ------------------------------------------

def wofq.m(m: Maybe<&2, S.D>) -> Maybe<&2, WD>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{s2w(x)}

def wnum() -> N.Num:
  N.Num{WD, wzero(), wone(), a => b => wadd(a, b), a => b => wmul(a, b), a => wneg(a), a => b => wcmp(a, b), q => wofq.m(KI.dofq(q))}

def wsigv(+b: Nat, xs: List<&2, WD>) -> List<&2, WD>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{wsig(x, b), wsigv(b, t)}

def wsigm(+b: Nat, a: List<&2, List<&2, WD>>) -> List<&2, List<&2, WD>>:
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{wsigv(b, r), wsigm(b, t)}

def yof.m(m: Maybe<&2, List<&2, List<&2, WD>>>) -> List<&2, List<&2, WD>>:
  match m:
    case None{}:
      Nil{}
    case Some{y}:
      wsigm(48n, y)

# Y: the inverse at 96 bits rounded to 48 (computed in words, the fast way)
def yof(+a: List<&2, List<&2, S.D>>) -> List<&2, List<&2, WD>>:
  yof.m(winverse(mlen(a), 96n, s2wm(a)))

# Bit lists with shifts: S.D with exponents aligned by shifting
# -------------------------------------------------------------
# The same representation as S.D; only alignment changes (k XO wraps for
# 2^k, in place of a multiplication by Pos.pow2(k)).

def pshl(p: S.Pos, k: Nat) -> S.Pos:
  match k:
    case 0n:
      p
    case 1n+j:
      S.XO{pshl(p, j)}

def zshl(z: S.Z, +k: Nat) -> S.Z:
  match z:
    case S.Z0{}:
      S.Z0{}
    case S.Zpos{p}:
      S.Zpos{pshl(p, k)}
    case S.Zneg{p}:
      S.Zneg{pshl(p, k)}

def sadd.go(l: Bool, +a: S.D, +b: S.D) -> S.D:
  match l:
    case True{}:
      S.D{S.Z.add(zshl(S.D.man(a), Nat.sub(S.D.exp(b), S.D.exp(a))), S.D.man(b)), S.D.exp(b)}
    case False{}:
      S.D{S.Z.add(S.D.man(a), zshl(S.D.man(b), Nat.sub(S.D.exp(a), S.D.exp(b)))), S.D.exp(a)}

def sadd(+a: S.D, +b: S.D) -> S.D:
  sadd.go(le(S.D.exp(a), S.D.exp(b)), a, b)

def scmp.go(l: Bool, +a: S.D, +b: S.D) -> Cmp:
  match l:
    case True{}:
      S.Z.cmp(zshl(S.D.man(a), Nat.sub(S.D.exp(b), S.D.exp(a))), S.D.man(b))
    case False{}:
      S.Z.cmp(S.D.man(a), zshl(S.D.man(b), Nat.sub(S.D.exp(a), S.D.exp(b))))

def scmp(+a: S.D, +b: S.D) -> Cmp:
  scmp.go(le(S.D.exp(a), S.D.exp(b)), a, b)

def snum() -> N.Num:
  N.Num{S.D, S.D{S.Z0{}, 0n}, S.D{S.Zpos{S.XH{}}, 0n}, a => b => sadd(a, b), a => b => S.D.mul(a, b), a => S.D.neg(a), a => b => scmp(a, b), q => KI.dofq(q)}

# Exact products A A^T
# --------------------

def wdot(xs: List<&2, WD>, ys: List<&2, WD>) -> WD:
  match xs ys:
    case Nil{} ys:
      wzero()
    case Con{x, t} Nil{}:
      wzero()
    case Con{+x, t} Con{+y, u}:
      wadd(wmul(x, y), wdot(t, u))

def srow(+r: List<&2, S.D>, b: List<&2, List<&2, S.D>>) -> List<&2, S.D>:
  match b:
    case Nil{}:
      Nil{}
    case Con{s, u}:
      Con{NU.ddot(r, s), srow(r, u)}

def smm(a: List<&2, List<&2, S.D>>, +b: List<&2, List<&2, S.D>>) -> List<&2, List<&2, S.D>>:
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{srow(r, b), smm(t, b)}

def wrw(+r: List<&2, WD>, b: List<&2, List<&2, WD>>) -> List<&2, WD>:
  match b:
    case Nil{}:
      Nil{}
    case Con{s, u}:
      Con{wdot(r, s), wrw(r, u)}

def wmm(a: List<&2, List<&2, WD>>, +b: List<&2, List<&2, WD>>) -> List<&2, List<&2, WD>>:
  match a:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{wrw(r, b), wmm(t, b)}

# Digests and equality
# --------------------

def zdg(z: S.Z) -> Nat:
  match z:
    case S.Z0{}:
      0n
    case S.Zpos{p}:
      Nat.mul(2n, QRD.size(p))
    case S.Zneg{p}:
      1n+Nat.mul(2n, QRD.size(p))

def ddg(x: S.D) -> Nat:
  match x:
    case S.D{m, e}:
      Nat.add(zdg(m), e)

def vdg(xs: List<&2, S.D>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      Nat.add(ddg(h), vdg(t))

def mdg(a: List<&2, List<&2, S.D>>) -> Nat:
  match a:
    case Nil{}:
      0n
    case Con{r, t}:
      Nat.add(vdg(r), mdg(t))

def odg(m: Maybe<&2, List<&2, List<&2, S.D>>>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{a}:
      mdg(a)

def pos_eq(a: S.Pos, b: S.Pos) -> Bool:
  match a b:
    case S.XH{} S.XH{}:
      True{}
    case S.XO{p} S.XO{q}:
      pos_eq(p, q)
    case S.XI{p} S.XI{q}:
      pos_eq(p, q)
    case a b:
      False{}

def z_eq(a: S.Z, b: S.Z) -> Bool:
  match a b:
    case S.Z0{} S.Z0{}:
      True{}
    case S.Zpos{p} S.Zpos{q}:
      pos_eq(p, q)
    case S.Zneg{p} S.Zneg{q}:
      pos_eq(p, q)
    case a b:
      False{}

def d_eq(x: S.D, y: S.D) -> Bool:
  match x y:
    case S.D{m1, e1} S.D{m2, e2}:
      band(z_eq(m1, m2), eq(e1, e2))

def v_eq(xs: List<&2, S.D>, ys: List<&2, S.D>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Con{x, s} Con{y, t}:
      band(d_eq(x, y), v_eq(s, t))
    case xs ys:
      False{}

def m_eq(a: List<&2, List<&2, S.D>>, b: List<&2, List<&2, S.D>>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Con{r, s} Con{q, t}:
      band(v_eq(r, q), m_eq(s, t))
    case a b:
      False{}

def o_eq(a: Maybe<&2, List<&2, List<&2, S.D>>>, b: Maybe<&2, List<&2, List<&2, S.D>>>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case Some{x} Some{y}:
      m_eq(x, y)
    case a b:
      False{}

def winv.s(m: Maybe<&2, List<&2, List<&2, WD>>>) -> Maybe<&2, List<&2, List<&2, S.D>>>:
  match m:
    case None{}:
      None{}
    case Some{a}:
      Some{w2sm(a)}

def winvs(+n: Nat, +w: Nat, +a: List<&2, List<&2, S.D>>) -> Maybe<&2, List<&2, List<&2, S.D>>>:
  winv.s(winverse(n, w, s2wm(a)))

# Input
# -----

def bit(b: Bool, p: S.Pos) -> S.Pos:
  match b:
    case True{}:
      S.XI{p}
    case False{}:
      S.XO{p}

def pos.go(s: String, acc: S.Pos) -> S.Pos:
  match s:
    case SNil{}:
      acc
    case SCon{h, t}:
      pos.go(t, bit(Char.is_eq(h, '1'), acc))

def pos(s: String) -> S.Pos:
  match s:
    case SNil{}:
      S.XH{}
    case SCon{h, t}:
      pos.go(t, S.XH{})

def z.of(neg: Bool, zero: Bool, s: String, t: String) -> S.Z:
  match neg zero:
    case True{} zero:
      S.Zneg{pos(t)}
    case False{} True{}:
      S.Z0{}
    case False{} False{}:
      S.Zpos{pos(s)}

def z(s: String) -> S.Z:
  match s:
    case SNil{}:
      S.Z0{}
    case SCon{+h, +t}:
      z.of(Char.is_eq(h, '-'), Char.is_eq(h, '0'), SCon{h, t}, t)

def d.of(ps: List<&2, String>) -> S.D:
  match ps:
    case Con{m, Con{e, rest}}:
      S.D{z(m), B.tok.nat(e)}
    case _:
      S.D{S.Z0{}, 0n}

def ds(ts: List<&2, String>) -> List<&2, S.D>:
  match ts:
    case Nil{}:
      []
    case Con{t, rest}:
      Con{d.of(String.split(t, ':')), ds(rest)}

def row.of(ts: List<&2, String>) -> List<&2, S.D>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      ds(t)

def isrow(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{h, t}:
      Char.is_eq(h, 'r')

def rows.add(b: Bool, +l: String, rest: List<&2, List<&2, S.D>>) -> List<&2, List<&2, S.D>>:
  match b:
    case True{}:
      Con{row.of(B.toks(l)), rest}
    case False{}:
      rest

def rows(ls: List<&2, String>) -> List<&2, List<&2, S.D>>:
  match ls:
    case Nil{}:
      Nil{}
    case Con{+l, t}:
      rows.add(isrow(l), l, rows(t))

# The modes
# ---------
# 0 parse; 1 S.D inverse at 96 bits (p = 64); 2 the word inverse
# (converted in and out); 3 both, compared; 4 S.D exact A A^T; 5 the word
# product; 6 both, compared; 7 conversions only; 8 Y (the word inverse
# rounded to 48 bits); 9 Y J by the checker's generic product at S.D; 10
# the same at the word instance; 11 both, compared; 12 Y J at S.D with
# shifts for alignment; 13 that against S.D, compared

def run.go(k: Nat, +a: List<&2, List<&2, S.D>>) -> String:
  match k:
    case 0n:
      "parse " ++ Nat.show(mdg(a))
    case 1n:
      "sd inverse " ++ Nat.show(odg(NU.dinverse(mlen(a), 96n, a)))
    case 2n:
      "word inverse " ++ Nat.show(odg(winvs(mlen(a), 96n, a)))
    case 3n:
      "inverse equal " ++ Bool.show(o_eq(NU.dinverse(mlen(a), 96n, a), winvs(mlen(a), 96n, a)))
    case 4n:
      "sd product " ++ Nat.show(mdg(smm(a, a)))
    case 5n:
      "word product " ++ Nat.show(mdg(w2sm(wmm(s2wm(a), s2wm(a)))))
    case 6n:
      "product equal " ++ Bool.show(m_eq(smm(a, a), w2sm(wmm(s2wm(a), s2wm(a)))))
    case 7n:
      "convert " ++ Bool.show(m_eq(a, w2sm(s2wm(a))))
    case 8n:
      "Y only " ++ Nat.show(mdg(w2sm(yof(a))))
    case 9n:
      "sd generic Y J " ++ Nat.show(mdg(KA.kmatmul(~KI.dnum(), w2sm(yof(a)), a)))
    case 10n:
      "word generic Y J " ++ Nat.show(mdg(w2sm(KA.kmatmul(~wnum(), yof(a), s2wm(a)))))
    case 12n:
      "shift generic Y J " ++ Nat.show(mdg(KA.kmatmul(~snum(), w2sm(yof(a)), a)))
    case 13n:
      "shift generic Y J equal " ++ Bool.show(m_eq(KA.kmatmul(~KI.dnum(), w2sm(yof(a)), a), KA.kmatmul(~snum(), w2sm(yof(a)), a)))
    case 11n:
      "generic Y J equal " ++ Bool.show(m_eq(KA.kmatmul(~KI.dnum(), w2sm(yof(a)), a), w2sm(KA.kmatmul(~wnum(), yof(a), s2wm(a)))))
    case _:
      "modes 0 to 13"

def main() -> IO(Unit):
  do IO<Unit>:
    j : String <- B.slurp("J.txt")
    m : String <- B.slurp("mode.in")
    IO.print(run.go(B.tok.nat(m), rows(String.split(j, '\n'))))
