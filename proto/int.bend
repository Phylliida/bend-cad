# proto/int.bend: prototype bigints for the sk-P1 spike. Untrusted and
# unverified; the verified version is sk-01/sk-02.
#
# A magnitude (Mag) is a list of limbs in base 2^16, least significant first,
# normalized: no zero limb at the high end, so zero is Nil.
#
# Bend cannot destructure a computed pair, so each loop carries its pending
# (carry, limb) pair as a parameter: a call emits the pending limb, then
# continues with the carry. A wrapper starts the loop with (0, 0) and drops
# the spurious first limb.

import Base

# Magnitudes
# ----------

# [c] when c > 0, else []; c must be below 2^16
def Mag.of_limb(c: Nat) -> List<&2, Nat>:
  match c:
    case 0n:
      Nil{}
    case 1n+p:
      Con{1n+p, Nil{}}

# drops the lowest limb
def Mag.drop1(x: List<&2, Nat>) -> List<&2, Nat>:
  match x:
    case Nil{}:
      Nil{}
    case Con{_, t}:
      t

# x·2^16
def Mag.shl16(x: List<&2, Nat>) -> List<&2, Nat>:
  match x:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Con{0n, Con{h, t}}

# keeps the tail t after a limb h, dropping h when it is the high zero
def Mag.norm.con(h: Nat, t: List<&2, Nat>) -> List<&2, Nat>:
  match t:
    case Nil{}:
      Mag.of_limb(h)
    case Con{x, y}:
      Con{h, Con{x, y}}

# strips high zero limbs
def Mag.norm(a: List<&2, Nat>) -> List<&2, Nat>:
  match a:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Mag.norm.con(h, Mag.norm(t))

# emits r, then b + q
def Mag.addc(b: List<&2, Nat>, qr: Nat & Nat) -> List<&2, Nat>:
  match b:
    case Nil{}:
      (q, r) = qr
      Con{r, Mag.of_limb(q)}
    case Con{h, t}:
      (q, r) = qr
      Con{r, Mag.addc(t, Nat.divmod(Nat.add(h, q), 65536n))}

# emits r, then a + b + q
def Mag.add.go(a: List<&2, Nat>, b: List<&2, Nat>, qr: Nat & Nat) -> List<&2, Nat>:
  match a b:
    case Nil{} Nil{}:
      (q, r) = qr
      Con{r, Mag.of_limb(q)}
    case Nil{} Con{bh, bt}:
      (q, r) = qr
      Con{r, Mag.addc(bt, Nat.divmod(Nat.add(bh, q), 65536n))}
    case Con{ah, at} Nil{}:
      (q, r) = qr
      Con{r, Mag.addc(at, Nat.divmod(Nat.add(ah, q), 65536n))}
    case Con{ah, at} Con{bh, bt}:
      (q, r) = qr
      Con{r, Mag.add.go(at, bt, Nat.divmod(Nat.add(Nat.add(ah, bh), q), 65536n))}

# a + b
def Mag.add(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  Mag.norm(Mag.drop1(Mag.add.go(a, b, (0n, 0n))))

# emits r, then a − b − (1 − q), for a ≥ b + (1 − q); not normalized
def Mag.sub.go(a: List<&2, Nat>, b: List<&2, Nat>, qr: Nat & Nat) -> List<&2, Nat>:
  match a b:
    case Nil{} _:
      (q, r) = qr
      Con{r, Nil{}}
    case Con{ah, at} Nil{}:
      (q, r) = qr
      Con{r, Mag.sub.go(at, Nil{}, Nat.divmod(Nat.sub(Nat.add(ah, 65536n), Nat.sub(1n, q)), 65536n))}
    case Con{ah, at} Con{bh, bt}:
      (q, r) = qr
      Con{r, Mag.sub.go(at, bt, Nat.divmod(Nat.sub(Nat.add(ah, 65536n), Nat.add(bh, Nat.sub(1n, q))), 65536n))}

# a − b, for a ≥ b
def Mag.sub(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  Mag.norm(Mag.drop1(Mag.sub.go(a, b, (1n, 0n))))

def Mag.cmp.fin(hi: Cmp, ah: Nat, bh: Nat) -> Cmp:
  match hi:
    case EQ{}:
      Nat.cmp(ah, bh)
    case LT{}:
      LT{}
    case GT{}:
      GT{}

# compares normalized magnitudes
def Mag.cmp(a: List<&2, Nat>, b: List<&2, Nat>) -> Cmp:
  match a b:
    case Nil{} Nil{}:
      EQ{}
    case Nil{} Con{_, _}:
      LT{}
    case Con{_, _} Nil{}:
      GT{}
    case Con{ah, at} Con{bh, bt}:
      Mag.cmp.fin(Mag.cmp(at, bt), ah, bh)

# emits r, then a·k + q, for a limb-sized k
def Mag.mul1.go(a: List<&2, Nat>, +k: Nat, qr: Nat & Nat) -> List<&2, Nat>:
  match a:
    case Nil{}:
      (q, r) = qr
      Con{r, Mag.of_limb(q)}
    case Con{h, t}:
      (q, r) = qr
      Con{r, Mag.mul1.go(t, k, Nat.divmod(Nat.add(Nat.mul(h, k), q), 65536n))}

# a·k for a limb-sized k; not normalized when k = 0
def Mag.mul1(a: List<&2, Nat>, k: Nat) -> List<&2, Nat>:
  Mag.drop1(Mag.mul1.go(a, k, (0n, 0n)))

# a·b, schoolbook; not normalized
def Mag.mul.go(a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  match a:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Mag.add(Mag.mul1(b, h), Mag.shl16(Mag.mul.go(t, b)))

def Mag.mul(a: List<&2, Nat>, +b: List<&2, Nat>) -> List<&2, Nat>:
  Mag.norm(Mag.mul.go(a, b))

# 2^b for b < 16
def Mag.pow2small(b: Nat) -> Nat:
  Nat.pow(2n, b)

# floor(a / 2^n)
def Mag.shr(a: List<&2, Nat>, +n: Nat) -> List<&2, Nat>:
  Mag.norm(Mag.drop1(Mag.mul1(List.drop(&2, Nat, a, Nat.div(n, 16n)), Mag.pow2small(Nat.sub(16n, Nat.mod(n, 16n))))))

# a·2^n
def Mag.shl(a: List<&2, Nat>, +n: Nat) -> List<&2, Nat>:
  Mag.norm(List.append(&2, Nat, List.replicate(Nat, Nat.div(n, 16n), 0n), Mag.mul1(a, Mag.pow2small(Nat.mod(n, 16n)))))

def Mag.pow2(+n: Nat) -> List<&2, Nat>:
  Mag.shl([1n], n)

# n for n < 2^48, by fuel (three limbs)
def Mag.from_nat.go(fuel: Nat, +n: Nat) -> List<&2, Nat>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      Mag.norm(Con{Nat.mod(n, 65536n), Mag.from_nat.go(f, Nat.div(n, 65536n))})

def Mag.from_nat(n: Nat) -> List<&2, Nat>:
  Mag.from_nat.go(3n, n)

def Mag.is_zero(a: List<&2, Nat>) -> Bool:
  match a:
    case Nil{}:
      True{}
    case Con{_, _}:
      False{}

def Mag.b2n(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# number of bits of x, counting the powers p·2^i (i < fuel) at most x
def Mag.limb_bits.go(fuel: Nat, +x: Nat, +p: Nat) -> Nat:
  match fuel:
    case 0n:
      0n
    case 1n+f:
      Nat.add(Mag.b2n(Nat.is_le(p, x)), Mag.limb_bits.go(f, x, Nat.mul(p, 2n)))

def Mag.limb_bits(x: Nat) -> Nat:
  Mag.limb_bits.go(17n, x, 1n)

# bits from the reversed limbs (top limb first) and the limb count
def Mag.bits.top(rev: List<&2, Nat>, n: Nat) -> Nat:
  match rev:
    case Nil{}:
      0n
    case Con{h, _}:
      Nat.add(Nat.mul(16n, Nat.sub(n, 1n)), Mag.limb_bits(h))

# number of bits of a normalized magnitude
def Mag.bits(+a: List<&2, Nat>) -> Nat:
  Mag.bits.top(List.reverse(&2, Nat, a), List.length(&2, Nat, a))

# big-endian division by a small d: emits quotient limbs, then the remainder
def Mag.div1.go(be: List<&2, Nat>, +d: Nat, +r: Nat) -> List<&2, Nat>:
  match be:
    case Nil{}:
      Con{r, Nil{}}
    case Con{h, t}:
      +x = Nat.add(Nat.mul(r, 65536n), h)
      Con{Nat.div(x, d), Mag.div1.go(t, d, Nat.mod(x, d))}

# [r, q_lo, …, q_hi]: the remainder and quotient of a by a small d > 0
def Mag.div1(+a: List<&2, Nat>, +d: Nat) -> List<&2, Nat>:
  List.reverse(&2, Nat, Mag.div1.go(List.reverse(&2, Nat, a), d, 0n))

def Mag.div1n.fin(rq: List<&2, Nat>) -> List<&2, Nat>:
  match rq:
    case Nil{}:
      Nil{}
    case Con{r, q}:
      Con{r, Mag.norm(q)}

# like Mag.div1 with a normalized quotient
def Mag.div1n(+a: List<&2, Nat>, +d: Nat) -> List<&2, Nat>:
  Mag.div1n.fin(Mag.div1(a, d))

# base-10^4 chunks, least significant first, from a div1n result
def Mag.chunks.go(fuel: Nat, rq: List<&2, Nat>) -> List<&2, Nat>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+f:
      match rq:
        case Nil{}:
          Nil{}
        case Con{r, q}:
          match q:
            case Nil{}:
              Con{r, Nil{}}
            case Con{x, y}:
              Con{r, Mag.chunks.go(f, Mag.div1n(Con{x, y}, 10000n))}

def Mag.pad4(c: Nat) -> String:
  String.drop(Nat.show(Nat.add(10000n, c)), 1n)

def Mag.fmt.rest(cs: List<&2, Nat>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{c, t}:
      Mag.pad4(c) ++ Mag.fmt.rest(t)

def Mag.fmt(cs: List<&2, Nat>) -> String:
  match cs:
    case Nil{}:
      "0"
    case Con{c, t}:
      Nat.show(c) ++ Mag.fmt.rest(t)

# decimal
def Mag.show(+a: List<&2, Nat>) -> String:
  Mag.fmt(List.reverse(&2, Nat, Mag.chunks.go(Nat.add(Nat.mul(2n, List.length(&2, Nat, a)), 2n), Mag.div1n(a, 10000n))))

# a as an F32
def Mag.to_f32(a: List<&2, Nat>) -> F32:
  match a:
    case Nil{}:
      0.0
    case Con{h, t}:
      F32.add(F32.from_nat(h), F32.mul(65536.0, Mag.to_f32(t)))

# Integers
# --------

# sign and magnitude; Neg never holds zero
type Int is Data:
  Pos{mag: List<&2, Nat>}
  Neg{mag: List<&2, Nat>}

def Int.zero() -> Int:
  Pos{Nil{}}

# −m
def Int.mk_neg(m: List<&2, Nat>) -> Int:
  match m:
    case Nil{}:
      Pos{Nil{}}
    case Con{h, t}:
      Neg{Con{h, t}}

def Int.neg(a: Int) -> Int:
  match a:
    case Pos{m}:
      Int.mk_neg(m)
    case Neg{m}:
      Pos{m}

def Int.diff.fin(c: Cmp, +x: List<&2, Nat>, +y: List<&2, Nat>) -> Int:
  match c:
    case GT{}:
      Pos{Mag.sub(x, y)}
    case LT{}:
      Neg{Mag.sub(y, x)}
    case EQ{}:
      Pos{Nil{}}

# x − y for magnitudes
def Int.diff(+x: List<&2, Nat>, +y: List<&2, Nat>) -> Int:
  Int.diff.fin(Mag.cmp(x, y), x, y)

def Int.add(a: Int, b: Int) -> Int:
  match a b:
    case Pos{x} Pos{y}:
      Pos{Mag.add(x, y)}
    case Neg{x} Neg{y}:
      Neg{Mag.add(x, y)}
    case Pos{x} Neg{y}:
      Int.diff(x, y)
    case Neg{x} Pos{y}:
      Int.diff(y, x)

def Int.sub(a: Int, b: Int) -> Int:
  Int.add(a, Int.neg(b))

def Int.mul(a: Int, b: Int) -> Int:
  match a b:
    case Pos{x} Pos{y}:
      Pos{Mag.mul(x, y)}
    case Neg{x} Neg{y}:
      Pos{Mag.mul(x, y)}
    case Pos{x} Neg{y}:
      Int.mk_neg(Mag.mul(x, y))
    case Neg{x} Pos{y}:
      Int.mk_neg(Mag.mul(x, y))

def Int.cmp(a: Int, b: Int) -> Cmp:
  match a b:
    case Pos{x} Pos{y}:
      Mag.cmp(x, y)
    case Neg{x} Neg{y}:
      Mag.cmp(y, x)
    case Pos{_} Neg{_}:
      GT{}
    case Neg{_} Pos{_}:
      LT{}

def Int.is_neg(a: Int) -> Bool:
  match a:
    case Pos{_}:
      False{}
    case Neg{_}:
      True{}

def Int.mag(a: Int) -> List<&2, Nat>:
  match a:
    case Pos{m}:
      m
    case Neg{m}:
      m

def Int.abs(a: Int) -> Int:
  Pos{Int.mag(a)}

# floor(a / 2^n)
def Int.shr_floor(a: Int, +n: Nat) -> Int:
  match a:
    case Pos{m}:
      Pos{Mag.shr(m, n)}
    case Neg{m}:
      Int.mk_neg(Mag.shr(Mag.add(m, Mag.sub(Mag.pow2(n), [1n])), n))

# ceil(a / 2^n)
def Int.shr_ceil(a: Int, +n: Nat) -> Int:
  Int.neg(Int.shr_floor(Int.neg(a), n))

# a·2^n
def Int.shl(a: Int, +n: Nat) -> Int:
  match a:
    case Pos{m}:
      Pos{Mag.shl(m, n)}
    case Neg{m}:
      Neg{Mag.shl(m, n)}

def Int.from_nat(n: Nat) -> Int:
  Pos{Mag.from_nat(n)}

def Int.bits(a: Int) -> Nat:
  Mag.bits(Int.mag(a))

def Int.show(a: Int) -> String:
  match a:
    case Pos{m}:
      Mag.show(m)
    case Neg{m}:
      "-" ++ Mag.show(m)

def Int.to_f32(a: Int) -> F32:
  match a:
    case Pos{m}:
      Mag.to_f32(m)
    case Neg{m}:
      F32.neg(Mag.to_f32(m))

def Int.from_f32.if(neg: Bool, +x: F32) -> Int:
  match neg:
    case True{}:
      Int.mk_neg(Mag.from_nat(F32.to_nat(F32.round(F32.neg(x)))))
    case False{}:
      Pos{Mag.from_nat(F32.to_nat(F32.round(x)))}

# x rounded to the nearest integer, for |x| < 2^31
def Int.from_f32(+x: F32) -> Int:
  Int.from_f32.if(F32.is_lt(x, 0.0), x)
