# bend-cad spec numbers: binary positives and integers (Coq's BinPos and
# BinInt shapes), with their meaning in Base's unary Nat.
#
# Binary, because Bend's checker computes Nat in unary: a closed fact about a
# large constant must be a small term. Trusted: these definitions and the
# meaning functions (Pos.nat, Z.of_diff, Z.pnat, Z.nnat). LAWS.bend states
# that the operations agree with their unary meaning.

import Base

# Positives
# ---------

# XH is 1, XO{p} is 2p, XI{p} is 2p + 1
type Pos is Data:
  XH{}
  XO{p: Pos}
  XI{p: Pos}

def Pos.succ(p: Pos) -> Pos:
  match p:
    case XH{}:
      XO{XH{}}
    case XO{q}:
      XI{q}
    case XI{q}:
      XO{Pos.succ(q)}

# a + b + c, with c a carry bit
def Pos.addc(a: Pos, b: Pos, c: Bool) -> Pos:
  match a b c:
    case XH{} XH{} False{}:
      XO{XH{}}
    case XH{} XH{} True{}:
      XI{XH{}}
    case XH{} XO{q} False{}:
      XI{q}
    case XH{} XO{q} True{}:
      XO{Pos.succ(q)}
    case XH{} XI{q} False{}:
      XO{Pos.succ(q)}
    case XH{} XI{q} True{}:
      XI{Pos.succ(q)}
    case XO{p} XH{} False{}:
      XI{p}
    case XO{p} XH{} True{}:
      XO{Pos.succ(p)}
    case XI{p} XH{} False{}:
      XO{Pos.succ(p)}
    case XI{p} XH{} True{}:
      XI{Pos.succ(p)}
    case XO{p} XO{q} False{}:
      XO{Pos.addc(p, q, False{})}
    case XO{p} XO{q} True{}:
      XI{Pos.addc(p, q, False{})}
    case XO{p} XI{q} False{}:
      XI{Pos.addc(p, q, False{})}
    case XO{p} XI{q} True{}:
      XO{Pos.addc(p, q, True{})}
    case XI{p} XO{q} False{}:
      XI{Pos.addc(p, q, False{})}
    case XI{p} XO{q} True{}:
      XO{Pos.addc(p, q, True{})}
    case XI{p} XI{q} False{}:
      XO{Pos.addc(p, q, True{})}
    case XI{p} XI{q} True{}:
      XI{Pos.addc(p, q, True{})}

def Pos.add(a: Pos, b: Pos) -> Pos:
  Pos.addc(a, b, False{})

def Pos.mul(a: Pos, +b: Pos) -> Pos:
  match a:
    case XH{}:
      b
    case XO{p}:
      XO{Pos.mul(p, b)}
    case XI{p}:
      Pos.add(XO{Pos.mul(p, b)}, b)

# 2p - 1
def Pos.pred_double(p: Pos) -> Pos:
  match p:
    case XH{}:
      XH{}
    case XO{q}:
      XI{Pos.pred_double(q)}
    case XI{q}:
      XI{XO{q}}

# the meaning of a positive
def Pos.nat(p: Pos) -> Nat:
  match p:
    case XH{}:
      1n
    case XO{q}:
      Nat.double(Pos.nat(q))
    case XI{q}:
      1n+Nat.double(Pos.nat(q))

# the positive n + 1
def Pos.of_succ(n: Nat) -> Pos:
  match n:
    case 0n:
      XH{}
    case 1n+k:
      Pos.succ(Pos.of_succ(k))

# Integers
# --------

type Z is Data:
  Z0{}
  Zpos{p: Pos}
  Zneg{p: Pos}

def Z.neg(x: Z) -> Z:
  match x:
    case Z0{}:
      Z0{}
    case Zpos{p}:
      Zneg{p}
    case Zneg{p}:
      Zpos{p}

# 2x
def Z.double(x: Z) -> Z:
  match x:
    case Z0{}:
      Z0{}
    case Zpos{p}:
      Zpos{XO{p}}
    case Zneg{p}:
      Zneg{XO{p}}

# 2x + 1
def Z.succ_double(x: Z) -> Z:
  match x:
    case Z0{}:
      Zpos{XH{}}
    case Zpos{p}:
      Zpos{XI{p}}
    case Zneg{p}:
      Zneg{Pos.pred_double(p)}

# 2x - 1
def Z.pred_double(x: Z) -> Z:
  match x:
    case Z0{}:
      Zneg{XH{}}
    case Zpos{p}:
      Zpos{Pos.pred_double(p)}
    case Zneg{p}:
      Zneg{XI{p}}

# a - b, for positives a and b
def Z.pos_sub(a: Pos, b: Pos) -> Z:
  match a b:
    case XI{p} XI{q}:
      Z.double(Z.pos_sub(p, q))
    case XI{p} XO{q}:
      Z.succ_double(Z.pos_sub(p, q))
    case XI{p} XH{}:
      Zpos{XO{p}}
    case XO{p} XI{q}:
      Z.pred_double(Z.pos_sub(p, q))
    case XO{p} XO{q}:
      Z.double(Z.pos_sub(p, q))
    case XO{p} XH{}:
      Zpos{Pos.pred_double(p)}
    case XH{} XI{q}:
      Zneg{XO{q}}
    case XH{} XO{q}:
      Zneg{Pos.pred_double(q)}
    case XH{} XH{}:
      Z0{}

def Z.add(x: Z, y: Z) -> Z:
  match x:
    case Z0{}:
      y
    case Zpos{p}:
      match y:
        case Z0{}:
          Zpos{p}
        case Zpos{q}:
          Zpos{Pos.add(p, q)}
        case Zneg{q}:
          Z.pos_sub(p, q)
    case Zneg{p}:
      match y:
        case Z0{}:
          Zneg{p}
        case Zpos{q}:
          Z.pos_sub(q, p)
        case Zneg{q}:
          Zneg{Pos.add(p, q)}

def Z.sub(x: Z, y: Z) -> Z:
  Z.add(x, Z.neg(y))

def Z.mul(x: Z, y: Z) -> Z:
  match x:
    case Z0{}:
      Z0{}
    case Zpos{p}:
      match y:
        case Z0{}:
          Z0{}
        case Zpos{q}:
          Zpos{Pos.mul(p, q)}
        case Zneg{q}:
          Zneg{Pos.mul(p, q)}
    case Zneg{p}:
      match y:
        case Z0{}:
          Z0{}
        case Zpos{q}:
          Zneg{Pos.mul(p, q)}
        case Zneg{q}:
          Zpos{Pos.mul(p, q)}

# The meaning of an integer: the pair (pnat, nnat) of unary naturals whose
# difference it is, one of them zero; and back, the integer a - b.

def Z.pnat(x: Z) -> Nat:
  match x:
    case Z0{}:
      0n
    case Zpos{p}:
      Pos.nat(p)
    case Zneg{p}:
      0n

def Z.nnat(x: Z) -> Nat:
  match x:
    case Z0{}:
      0n
    case Zpos{p}:
      0n
    case Zneg{p}:
      Pos.nat(p)

def Z.of_diff(a: Nat, b: Nat) -> Z:
  match a b:
    case 0n 0n:
      Z0{}
    case 1n+k 0n:
      Zpos{Pos.of_succ(k)}
    case 0n 1n+k:
      Zneg{Pos.of_succ(k)}
    case 1n+i 1n+j:
      Z.of_diff(i, j)
