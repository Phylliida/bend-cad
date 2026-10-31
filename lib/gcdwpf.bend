# bend-cad: lib/gcdw.bend's gcd gives the quotients it says: g qa = a and
# g qb = b (gw_ok, gcd_ok), by its steps (gkind_ok says what each step
# saw). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ./zring.bend as R
import ./zord.bend as ZO
import ./gcdw.bend as GD

# g q = a
def Div(+g: S.Pos, +q: S.Pos, +a: S.Pos) -> Data:
  {S.Z.mul(S.Zpos{g}, S.Zpos{q}) == S.Zpos{a} : S.Z}

def GOk(+a: S.Pos, +b: S.Pos, +r: GD.GW) -> Data:
  SK.Both(Div(GD.GW.g(r), GD.GW.qa(r), a), Div(GD.GW.g(r), GD.GW.qb(r), b))

# The steps
# ---------

# what gkind saw of a and b
def KindOk(+a: S.Pos, +b: S.Pos, k: GD.GK) -> Data:
  match k:
    case GD.EE{+x, +y}:
      SK.Both({S.XO{x} == a : S.Pos}, {S.XO{y} == b : S.Pos})
    case GD.EO{+x}:
      {S.XO{x} == a : S.Pos}
    case GD.OE{+y}:
      {S.XO{y} == b : S.Pos}
    case GD.OZ{}:
      {GD.zd(a, b) == S.Z0{} : S.Z}
    case GD.OP{+c}:
      {GD.zd(a, b) == S.Zpos{c} : S.Z}
    case GD.ON{+c}:
      {GD.zd(a, b) == S.Zneg{c} : S.Z}

def gkind.oo_ok(+a: S.Pos, +b: S.Pos, d: S.Z, e: {GD.zd(a, b) == d : S.Z}) -> KindOk(a, b, GD.gkind.oo(d)):
  match d:
    case S.Z0{}:
      e
    case S.Zpos{+c}:
      e
    case S.Zneg{+c}:
      e

def gkind_ok(a: S.Pos, b: S.Pos) -> KindOk(a, b, GD.gkind(a, b)):
  match a b:
    case S.XH{} S.XH{}:
      gkind.oo_ok(S.XH{}, S.XH{}, GD.zd(S.XH{}, S.XH{}), {==})
    case S.XH{} S.XO{+y}:
      {==}
    case S.XH{} S.XI{+y}:
      gkind.oo_ok(S.XH{}, S.XI{y}, GD.zd(S.XH{}, S.XI{y}), {==})
    case S.XO{+x} S.XH{}:
      {==}
    case S.XO{+x} S.XO{+y}:
      ({==}, {==})
    case S.XO{+x} S.XI{+y}:
      {==}
    case S.XI{+x} S.XH{}:
      gkind.oo_ok(S.XI{x}, S.XH{}, GD.zd(S.XI{x}, S.XH{}), {==})
    case S.XI{+x} S.XO{+y}:
      {==}
    case S.XI{+x} S.XI{+y}:
      gkind.oo_ok(S.XI{x}, S.XI{y}, GD.zd(S.XI{x}, S.XI{y}), {==})

# Quotients
# ---------

def one_l(+a: S.Pos) -> Div(S.XH{}, a, a):
  {==}

def one_r(+a: S.Pos) -> Div(a, S.XH{}, a):
  R.ring_eq([S.Zpos{a}], E.ZMul{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{0n}, {==})

# 2g q = 2x
def dbl_g(+g: S.Pos, +q: S.Pos, +x: S.Pos, h: Div(g, q, x)) -> Div(S.XO{g}, q, S.XO{x}):
  %h : {S.Z.mul(S.Zpos{S.XO{g}}, S.Zpos{q}) == S.Z.mul(S.Zpos{S.XO{S.XH{}}}, _) : S.Z}
  R.ring_eq([S.Zpos{g}, S.Zpos{q}], E.ZMul{E.ZMul{E.ZCst{S.Zpos{S.XO{S.XH{}}}}, E.ZVar{0n}}, E.ZVar{1n}}, E.ZMul{E.ZCst{S.Zpos{S.XO{S.XH{}}}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, {==})

# g 2q = 2x
def dbl_q(+g: S.Pos, +q: S.Pos, +x: S.Pos, h: Div(g, q, x)) -> Div(g, S.XO{q}, S.XO{x}):
  %h : {S.Z.mul(S.Zpos{g}, S.Zpos{S.XO{q}}) == S.Z.mul(S.Zpos{S.XO{S.XH{}}}, _) : S.Z}
  R.ring_eq([S.Zpos{g}, S.Zpos{q}], E.ZMul{E.ZVar{0n}, E.ZMul{E.ZCst{S.Zpos{S.XO{S.XH{}}}}, E.ZVar{1n}}}, E.ZMul{E.ZCst{S.Zpos{S.XO{S.XH{}}}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, {==})

# g (q1 + q2) = a, from g q1 = c, g q2 = b and a - b = c
def add_div(+g: S.Pos, +q1: S.Pos, +q2: S.Pos, +c: S.Pos, +b: S.Pos, +a: S.Pos, h1: Div(g, q1, c), h2: Div(g, q2, b), hd: {GD.zd(a, b) == S.Zpos{c} : S.Z})
  -> Div(g, S.Pos.add(q1, q2), a):
  %R.ring_eq([S.Zpos{g}, S.Zpos{q1}, S.Zpos{q2}], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}, {==})
    : {_ == S.Zpos{a} : S.Z}
  %Equal.sym(S.Z, S.Z.mul(S.Zpos{g}, S.Zpos{q1}), S.Zpos{c}, h1) : {S.Z.add(_, S.Z.mul(S.Zpos{g}, S.Zpos{q2})) == S.Zpos{a} : S.Z}
  %Equal.sym(S.Z, S.Z.mul(S.Zpos{g}, S.Zpos{q2}), S.Zpos{b}, h2) : {S.Z.add(S.Zpos{c}, _) == S.Zpos{a} : S.Z}
  %hd : {S.Z.add(_, S.Zpos{b}) == S.Zpos{a} : S.Z}
  R.ring_eq([S.Zpos{a}, S.Zpos{b}], E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}, E.ZVar{1n}}, E.ZVar{0n}, {==})

# g (q1 + q2) = b, from g q1 = a, g q2 = c and a - b = -c
def add_div2(+g: S.Pos, +q1: S.Pos, +q2: S.Pos, +a: S.Pos, +c: S.Pos, +b: S.Pos, h1: Div(g, q1, a), h2: Div(g, q2, c), hd: {GD.zd(a, b) == S.Zneg{c} : S.Z})
  -> Div(g, S.Pos.add(q1, q2), b):
  %R.ring_eq([S.Zpos{g}, S.Zpos{q1}, S.Zpos{q2}], E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{2n}}}, E.ZMul{E.ZVar{0n}, E.ZAdd{E.ZVar{1n}, E.ZVar{2n}}}, {==})
    : {_ == S.Zpos{b} : S.Z}
  %Equal.sym(S.Z, S.Z.mul(S.Zpos{g}, S.Zpos{q1}), S.Zpos{a}, h1) : {S.Z.add(_, S.Z.mul(S.Zpos{g}, S.Zpos{q2})) == S.Zpos{b} : S.Z}
  %Equal.sym(S.Z, S.Z.mul(S.Zpos{g}, S.Zpos{q2}), S.Zpos{c}, h2) : {S.Z.add(S.Zpos{a}, _) == S.Zpos{b} : S.Z}
  %hd : {S.Z.add(S.Zpos{a}, S.Z.neg(_)) == S.Zpos{b} : S.Z}
  R.ring_eq([S.Zpos{a}, S.Zpos{b}], E.ZAdd{E.ZVar{0n}, E.ZNeg{E.ZSub{E.ZVar{0n}, E.ZVar{1n}}}}, E.ZVar{1n}, {==})

# a = b: a 1 = b
def gw_ok.oz(+a: S.Pos, +b: S.Pos, hk: {GD.zd(a, b) == S.Z0{} : S.Z}) -> Div(a, S.XH{}, b):
  %Equal.sym(S.Z, S.Zpos{b}, S.Zpos{a}, ZO.sub_eq(S.Zpos{b}, S.Zpos{a}, hk)) : {S.Z.mul(S.Zpos{a}, S.Zpos{S.XH{}}) == _ : S.Z}
  one_r(a)

def gw_ok.ee(+x: S.Pos, +y: S.Pos, +a: S.Pos, +b: S.Pos, +r: GD.GW, hk: SK.Both({S.XO{x} == a : S.Pos}, {S.XO{y} == b : S.Pos}), ih: GOk(x, y, r)) -> GOk(a, b, GD.gw.o(r)):
  (ea, eb) = hk
  (ia, ib) = ih
  %ea : GOk(_, b, GD.gw.o(r))
  %eb : GOk(S.XO{x}, _, GD.gw.o(r))
  (dbl_g(GD.GW.g(r), GD.GW.qa(r), x, ia), dbl_g(GD.GW.g(r), GD.GW.qb(r), y, ib))

def gw_ok.eo(+x: S.Pos, +a: S.Pos, +b: S.Pos, +r: GD.GW, hk: {S.XO{x} == a : S.Pos}, ih: GOk(x, b, r)) -> GOk(a, b, GD.gw.a(r)):
  (ia, ib) = ih
  %hk : GOk(_, b, GD.gw.a(r))
  (dbl_q(GD.GW.g(r), GD.GW.qa(r), x, ia), ib)

def gw_ok.oe(+y: S.Pos, +a: S.Pos, +b: S.Pos, +r: GD.GW, hk: {S.XO{y} == b : S.Pos}, ih: GOk(a, y, r)) -> GOk(a, b, GD.gw.b(r)):
  (ia, ib) = ih
  %hk : GOk(a, _, GD.gw.b(r))
  (ia, dbl_q(GD.GW.g(r), GD.GW.qb(r), y, ib))

def gw_ok.op(+c: S.Pos, +a: S.Pos, +b: S.Pos, +r: GD.GW, hk: {GD.zd(a, b) == S.Zpos{c} : S.Z}, ih: GOk(c, b, r)) -> GOk(a, b, GD.gw.sa(r)):
  (+ia, +ib) = ih
  (add_div(GD.GW.g(r), GD.GW.qa(r), GD.GW.qb(r), c, b, a, ia, ib, hk), ib)

def gw_ok.on(+c: S.Pos, +a: S.Pos, +b: S.Pos, +r: GD.GW, hk: {GD.zd(a, b) == S.Zneg{c} : S.Z}, ih: GOk(a, c, r)) -> GOk(a, b, GD.gw.sb(r)):
  (+ia, +ib) = ih
  (ia, add_div2(GD.GW.g(r), GD.GW.qa(r), GD.GW.qb(r), a, c, b, ia, ib, hk))

# the gcd's quotients are its quotients, whatever the fuel
def gw_ok(fuel: Nat, +a: S.Pos, +b: S.Pos, k: GD.GK, hk: KindOk(a, b, k)) -> GOk(a, b, GD.gcdw(fuel, a, b, k)):
  match fuel:
    case 0n:
      (one_l(a), one_l(b))
    case 1n++f:
      match k:
        case GD.EE{+x, +y}:
          gw_ok.ee(x, y, a, b, GD.gcdw(f, x, y, GD.gkind(x, y)), hk, gw_ok(f, x, y, GD.gkind(x, y), gkind_ok(x, y)))
        case GD.EO{+x}:
          gw_ok.eo(x, a, b, GD.gcdw(f, x, b, GD.gkind(x, b)), hk, gw_ok(f, x, b, GD.gkind(x, b), gkind_ok(x, b)))
        case GD.OE{+y}:
          gw_ok.oe(y, a, b, GD.gcdw(f, a, y, GD.gkind(a, y)), hk, gw_ok(f, a, y, GD.gkind(a, y), gkind_ok(a, y)))
        case GD.OZ{}:
          (one_r(a), gw_ok.oz(a, b, hk))
        case GD.OP{+c}:
          gw_ok.op(c, a, b, GD.gcdw(f, c, b, GD.gkind(c, b)), hk, gw_ok(f, c, b, GD.gkind(c, b), gkind_ok(c, b)))
        case GD.ON{+c}:
          gw_ok.on(c, a, b, GD.gcdw(f, a, c, GD.gkind(a, c)), hk, gw_ok(f, a, c, GD.gkind(a, c), gkind_ok(a, c)))

def gcd_ok(+a: S.Pos, +b: S.Pos) -> GOk(a, b, GD.gcd(a, b)):
  gw_ok(1n+Nat.double(Nat.add(GD.gsize(a), GD.gsize(b))), a, b, GD.gkind(a, b), gkind_ok(a, b))
