# bend-cad: a binary gcd with its quotients (PLAN-sk13b B4.8): gcdw gives
# g, qa and qb with g qa = a and g qb = b (lib/gcdwpf.bend: gw_ok). Both
# even: twice the gcd of the halves; one even: halve it; both odd: the
# larger becomes the difference, which the next step halves. So twice the
# bits are fuel enough; out of fuel, g = 1, which divides everything.
#
# Untrusted in the sense of the rest of lib/: its properties are proven,
# nothing about it is assumed.

import Base
import ../spec/num.bend as S

# g, with a = g qa and b = g qb
type GW is Data:
  GW{g: S.Pos, qa: S.Pos, qb: S.Pos}

def GW.g(r: GW) -> S.Pos:
  match r:
    case GW{g, qa, qb}:
      g

def GW.qa(r: GW) -> S.Pos:
  match r:
    case GW{g, qa, qb}:
      qa

def GW.qb(r: GW) -> S.Pos:
  match r:
    case GW{g, qa, qb}:
      qb

# both halved: twice the gcd
def gw.o(+r: GW) -> GW:
  GW{S.XO{GW.g(r)}, GW.qa(r), GW.qb(r)}

# a halved: twice a's quotient
def gw.a(+r: GW) -> GW:
  GW{GW.g(r), S.XO{GW.qa(r)}, GW.qb(r)}

# b halved
def gw.b(+r: GW) -> GW:
  GW{GW.g(r), GW.qa(r), S.XO{GW.qb(r)}}

# a replaced by a - b: a's quotient is the two added
def gw.sa(+r: GW) -> GW:
  GW{GW.g(r), S.Pos.add(GW.qa(r), GW.qb(r)), GW.qb(r)}

# b replaced by b - a
def gw.sb(+r: GW) -> GW:
  GW{GW.g(r), GW.qa(r), S.Pos.add(GW.qa(r), GW.qb(r))}

# a - b
def zd(+a: S.Pos, +b: S.Pos) -> S.Z:
  S.Z.sub(S.Zpos{a}, S.Zpos{b})

# the step for a and b
type GK is Data:
  EE{x: S.Pos, y: S.Pos}
  EO{x: S.Pos}
  OE{y: S.Pos}
  OZ{}
  OP{c: S.Pos}
  ON{c: S.Pos}

def gkind.oo(d: S.Z) -> GK:
  match d:
    case S.Z0{}:
      OZ{}
    case S.Zpos{c}:
      OP{c}
    case S.Zneg{c}:
      ON{c}

def gkind(a: S.Pos, b: S.Pos) -> GK:
  match a b:
    case S.XH{} S.XH{}:
      gkind.oo(zd(S.XH{}, S.XH{}))
    case S.XH{} S.XO{y}:
      OE{y}
    case S.XH{} S.XI{+y}:
      gkind.oo(zd(S.XH{}, S.XI{y}))
    case S.XO{x} S.XH{}:
      EO{x}
    case S.XO{x} S.XO{y}:
      EE{x, y}
    case S.XO{x} S.XI{y}:
      EO{x}
    case S.XI{+x} S.XH{}:
      gkind.oo(zd(S.XI{x}, S.XH{}))
    case S.XI{x} S.XO{y}:
      OE{y}
    case S.XI{+x} S.XI{+y}:
      gkind.oo(zd(S.XI{x}, S.XI{y}))

# the gcd of a and b with its quotients, k = gkind(a, b)
def gcdw(fuel: Nat, +a: S.Pos, +b: S.Pos, k: GK) -> GW:
  match fuel:
    case 0n:
      GW{S.XH{}, a, b}
    case 1n+f:
      match k:
        case EE{+x, +y}:
          gw.o(gcdw(f, x, y, gkind(x, y)))
        case EO{+x}:
          gw.a(gcdw(f, x, b, gkind(x, b)))
        case OE{+y}:
          gw.b(gcdw(f, a, y, gkind(a, y)))
        case OZ{}:
          GW{a, S.XH{}, S.XH{}}
        case OP{+c}:
          gw.sa(gcdw(f, c, b, gkind(c, b)))
        case ON{+c}:
          gw.sb(gcdw(f, a, c, gkind(a, c)))

def gsize(p: S.Pos) -> Nat:
  match p:
    case S.XH{}:
      1n
    case S.XO{q}:
      1n+gsize(q)
    case S.XI{q}:
      1n+gsize(q)

# the gcd of a and b, with fuel enough
def gcd(+a: S.Pos, +b: S.Pos) -> GW:
  gcdw(1n+Nat.double(Nat.add(gsize(a), gsize(b))), a, b, gkind(a, b))
