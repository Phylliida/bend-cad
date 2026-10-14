# The spec rationals form a field under Q.eq: Q.eq is an equivalence, the
# operations respect it, and the field laws hold up to it. Identities are
# one qring_eq or ring_eq call; transitivity needs cancellation of a
# positive factor, proven through the unary meaning.

import Base
import ./nat.bend as N
import ./pos.bend as P
import ./z.bend as LZ
import ./zring.bend as R
import ./qring.bend as QR
import ../spec/num.bend as S
import ../spec/ring.bend as E

# Cancellation
# ------------

# a * (1 + k) = b * (1 + k) gives a = b
def mul_cancel_nat(a: Nat, b: Nat, +k: Nat, e: {Nat.mul(a, 1n+k) == Nat.mul(b, 1n+k) : Nat}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+j:
      %e : N.NatD(_, Unit, {0n == 1n+j : Nat})
      Unit{}
    case 1n+i 0n:
      %e : N.NatD(_, {1n+i == 0n : Nat}, Unit)
      Unit{}
    case 1n+i 1n+j:
      %mul_cancel_nat(i, j, k, N.add_cancel(1n+k, Nat.mul(i, 1n+k), Nat.mul(j, 1n+k), e)) : {1n+i == 1n+_ : Nat}
      {==}

def pnat_mulp(x: S.Z, +p: S.Pos) -> {S.Z.pnat(S.Z.mul(x, S.Zpos{p})) == Nat.mul(S.Z.pnat(x), S.Pos.nat(p)) : Nat}:
  match x:
    case S.Z0{}:
      {==}
    case S.Zpos{q}:
      Equal.sym(Nat, Nat.mul(S.Pos.nat(q), S.Pos.nat(p)), S.Pos.nat(S.Pos.mul(q, p)), P.mul_nat(q, p))
    case S.Zneg{q}:
      {==}

def nnat_mulp(x: S.Z, +p: S.Pos) -> {S.Z.nnat(S.Z.mul(x, S.Zpos{p})) == Nat.mul(S.Z.nnat(x), S.Pos.nat(p)) : Nat}:
  match x:
    case S.Z0{}:
      {==}
    case S.Zpos{q}:
      {==}
    case S.Zneg{q}:
      Equal.sym(Nat, Nat.mul(S.Pos.nat(q), S.Pos.nat(p)), S.Pos.nat(S.Pos.mul(q, p)), P.mul_nat(q, p))

def pnat_scaled(+x: S.Z, +y: S.Z, +p: S.Pos, e: {S.Z.mul(x, S.Zpos{p}) == S.Z.mul(y, S.Zpos{p}) : S.Z}) -> {Nat.mul(S.Z.pnat(x), 1n+P.pm1(p)) == Nat.mul(S.Z.pnat(y), 1n+P.pm1(p)) : Nat}:
  %P.nat_form(p) : {Nat.mul(S.Z.pnat(x), _) == Nat.mul(S.Z.pnat(y), _) : Nat}
  %pnat_mulp(x, p) : {_ == Nat.mul(S.Z.pnat(y), S.Pos.nat(p)) : Nat}
  %pnat_mulp(y, p) : {S.Z.pnat(S.Z.mul(x, S.Zpos{p})) == _ : Nat}
  %e : {S.Z.pnat(S.Z.mul(x, S.Zpos{p})) == S.Z.pnat(_) : Nat}
  {==}

def nnat_scaled(+x: S.Z, +y: S.Z, +p: S.Pos, e: {S.Z.mul(x, S.Zpos{p}) == S.Z.mul(y, S.Zpos{p}) : S.Z}) -> {Nat.mul(S.Z.nnat(x), 1n+P.pm1(p)) == Nat.mul(S.Z.nnat(y), 1n+P.pm1(p)) : Nat}:
  %P.nat_form(p) : {Nat.mul(S.Z.nnat(x), _) == Nat.mul(S.Z.nnat(y), _) : Nat}
  %nnat_mulp(x, p) : {_ == Nat.mul(S.Z.nnat(y), S.Pos.nat(p)) : Nat}
  %nnat_mulp(y, p) : {S.Z.nnat(S.Z.mul(x, S.Zpos{p})) == _ : Nat}
  %e : {S.Z.nnat(S.Z.mul(x, S.Zpos{p})) == S.Z.nnat(_) : Nat}
  {==}

# x * p = y * p, for a positive p, gives x = y
def mul_cancel(+x: S.Z, +y: S.Z, +p: S.Pos, +e: {S.Z.mul(x, S.Zpos{p}) == S.Z.mul(y, S.Zpos{p}) : S.Z}) -> {x == y : S.Z}:
  %LZ.diff_parts(x) : {_ == y : S.Z}
  %LZ.diff_parts(y) : {S.Z.of_diff(S.Z.pnat(x), S.Z.nnat(x)) == _ : S.Z}
  %mul_cancel_nat(S.Z.pnat(x), S.Z.pnat(y), P.pm1(p), pnat_scaled(x, y, p, e)) : {S.Z.of_diff(S.Z.pnat(x), S.Z.nnat(x)) == S.Z.of_diff(_, S.Z.nnat(y)) : S.Z}
  %mul_cancel_nat(S.Z.nnat(x), S.Z.nnat(y), P.pm1(p), nnat_scaled(x, y, p, e)) : {S.Z.of_diff(S.Z.pnat(x), S.Z.nnat(x)) == S.Z.of_diff(S.Z.pnat(x), _) : S.Z}
  {==}

# Q.eq is an equivalence
# ----------------------

def q_refl(+x: S.Q) -> S.Q.eq(x, x):
  {==}

def q_sym(+x: S.Q, +y: S.Q, h: S.Q.eq(x, y)) -> S.Q.eq(y, x):
  Equal.sym(S.Z, S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}), S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), h)

# the parts of three rationals, as six integers
def env3(+x: S.Q, +y: S.Q, +z: S.Q) -> List<&2, S.Z>:
  [S.Q.num(x), S.Zpos{S.Q.den(x)}, S.Q.num(y), S.Zpos{S.Q.den(y)}, S.Q.num(z), S.Zpos{S.Q.den(z)}]

def q_trans.chain(+x: S.Q, +y: S.Q, +z: S.Q, h1: S.Q.eq(x, y), h2: S.Q.eq(y, z)) -> {S.Z.mul(S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(z)}), S.Zpos{S.Q.den(y)}) == S.Z.mul(S.Z.mul(S.Q.num(z), S.Zpos{S.Q.den(x)}), S.Zpos{S.Q.den(y)}) : S.Z}:
  %R.ring_eq(env3(x, y, z), E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZVar{5n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{5n}}, E.ZVar{3n}}, {==}) : {_ == E.eval(env3(x, y, z), E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{1n}}, E.ZVar{3n}}) : S.Z}
  %R.ring_eq(env3(x, y, z), E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{3n}}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{1n}}, E.ZVar{3n}}, {==}) : {E.eval(env3(x, y, z), E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZVar{5n}}) == _ : S.Z}
  %h2 : {E.eval(env3(x, y, z), E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZVar{5n}}) == S.Z.mul(_, S.Zpos{S.Q.den(x)}) : S.Z}
  %R.ring_eq(env3(x, y, z), E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{1n}}, E.ZVar{5n}}, E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{5n}}, E.ZVar{1n}}, {==}) : {E.eval(env3(x, y, z), E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZVar{5n}}) == _ : S.Z}
  %h1 : {E.eval(env3(x, y, z), E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZVar{5n}}) == S.Z.mul(_, S.Zpos{S.Q.den(z)}) : S.Z}
  {==}

def q_trans(+x: S.Q, +y: S.Q, +z: S.Q, h1: S.Q.eq(x, y), h2: S.Q.eq(y, z)) -> S.Q.eq(x, z):
  mul_cancel(S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(z)}), S.Z.mul(S.Q.num(z), S.Zpos{S.Q.den(x)}), S.Q.den(y), q_trans.chain(x, y, z, h1, h2))

# The operations respect Q.eq
# ---------------------------
# Each side is rearranged so that the hypothesis X * DX2 = X2 * DX applies.

def q_add_cong_l(+x: S.Q, +x2: S.Q, +y: S.Q, h: S.Q.eq(x, x2)) -> S.Q.eq(S.Q.add(x, y), S.Q.add(x2, y)):
  %R.ring_eq(env3(x, x2, y), E.ZAdd{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{5n}, E.ZVar{5n}}}, E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{1n}}, E.ZMul{E.ZVar{3n}, E.ZVar{5n}}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{5n}}, E.ZMul{E.ZVar{4n}, E.ZVar{1n}}}, E.ZMul{E.ZVar{3n}, E.ZVar{5n}}}, {==}) : {_ == E.eval(env3(x, x2, y), E.ZMul{E.ZAdd{E.ZMul{E.ZVar{2n}, E.ZVar{5n}}, E.ZMul{E.ZVar{4n}, E.ZVar{3n}}}, E.ZMul{E.ZVar{1n}, E.ZVar{5n}}}) : S.Z}
  %R.ring_eq(env3(x, x2, y), E.ZAdd{E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{1n}}, E.ZMul{E.ZVar{5n}, E.ZVar{5n}}}, E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{1n}}, E.ZMul{E.ZVar{3n}, E.ZVar{5n}}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{2n}, E.ZVar{5n}}, E.ZMul{E.ZVar{4n}, E.ZVar{3n}}}, E.ZMul{E.ZVar{1n}, E.ZVar{5n}}}, {==}) : {E.eval(env3(x, x2, y), E.ZAdd{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{5n}, E.ZVar{5n}}}, E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{1n}}, E.ZMul{E.ZVar{3n}, E.ZVar{5n}}}}) == _ : S.Z}
  %h : {E.eval(env3(x, x2, y), E.ZAdd{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{5n}, E.ZVar{5n}}}, E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{1n}}, E.ZMul{E.ZVar{3n}, E.ZVar{5n}}}}) == S.Z.add(S.Z.mul(_, S.Z.mul(S.Zpos{S.Q.den(y)}, S.Zpos{S.Q.den(y)})), E.eval(env3(x, x2, y), E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{1n}}, E.ZMul{E.ZVar{3n}, E.ZVar{5n}}})) : S.Z}
  {==}

def q_mul_cong_l(+x: S.Q, +x2: S.Q, +y: S.Q, h: S.Q.eq(x, x2)) -> S.Q.eq(S.Q.mul(x, y), S.Q.mul(x2, y)):
  %R.ring_eq(env3(x, x2, y), E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{4n}, E.ZVar{5n}}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{4n}}, E.ZMul{E.ZVar{3n}, E.ZVar{5n}}}, {==}) : {_ == E.eval(env3(x, x2, y), E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{4n}}, E.ZMul{E.ZVar{1n}, E.ZVar{5n}}}) : S.Z}
  %R.ring_eq(env3(x, x2, y), E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{1n}}, E.ZMul{E.ZVar{4n}, E.ZVar{5n}}}, E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{4n}}, E.ZMul{E.ZVar{1n}, E.ZVar{5n}}}, {==}) : {E.eval(env3(x, x2, y), E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{4n}, E.ZVar{5n}}}) == _ : S.Z}
  %h : {E.eval(env3(x, x2, y), E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{4n}, E.ZVar{5n}}}) == S.Z.mul(_, S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(y)})) : S.Z}
  {==}

def q_neg_cong(+x: S.Q, +x2: S.Q, h: S.Q.eq(x, x2)) -> S.Q.eq(S.Q.neg(x), S.Q.neg(x2)):
  %R.ring_eq(env3(x, x2, x2), E.ZNeg{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}, E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZVar{3n}}, {==}) : {_ == E.eval(env3(x, x2, x2), E.ZMul{E.ZNeg{E.ZVar{2n}}, E.ZVar{1n}}) : S.Z}
  %R.ring_eq(env3(x, x2, x2), E.ZNeg{E.ZMul{E.ZVar{2n}, E.ZVar{1n}}}, E.ZMul{E.ZNeg{E.ZVar{2n}}, E.ZVar{1n}}, {==}) : {E.eval(env3(x, x2, x2), E.ZNeg{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}) == _ : S.Z}
  %h : {E.eval(env3(x, x2, x2), E.ZNeg{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}) == S.Z.neg(_) : S.Z}
  {==}

# Right-hand congruences, through commutativity
# ----------------------------------------------

def q_add_comm(+x: S.Q, +y: S.Q) -> S.Q.eq(S.Q.add(x, y), S.Q.add(y, x)):
  QR.qring_eq([x, y], E.QAdd{E.QVar{0n}, E.QVar{1n}}, E.QAdd{E.QVar{1n}, E.QVar{0n}}, {==})

def q_mul_comm(+x: S.Q, +y: S.Q) -> S.Q.eq(S.Q.mul(x, y), S.Q.mul(y, x)):
  QR.qring_eq([x, y], E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QMul{E.QVar{1n}, E.QVar{0n}}, {==})

def q_add_cong_r(+x: S.Q, +y: S.Q, +y2: S.Q, h: S.Q.eq(y, y2)) -> S.Q.eq(S.Q.add(x, y), S.Q.add(x, y2)):
  q_trans(S.Q.add(x, y), S.Q.add(y2, x), S.Q.add(x, y2),
    q_trans(S.Q.add(x, y), S.Q.add(y, x), S.Q.add(y2, x), q_add_comm(x, y), q_add_cong_l(y, y2, x, h)),
    q_add_comm(y2, x))

def q_mul_cong_r(+x: S.Q, +y: S.Q, +y2: S.Q, h: S.Q.eq(y, y2)) -> S.Q.eq(S.Q.mul(x, y), S.Q.mul(x, y2)):
  q_trans(S.Q.mul(x, y), S.Q.mul(y2, x), S.Q.mul(x, y2),
    q_trans(S.Q.mul(x, y), S.Q.mul(y, x), S.Q.mul(y2, x), q_mul_comm(x, y), q_mul_cong_l(y, y2, x, h)),
    q_mul_comm(y2, x))

# Inverses
# --------

def q_mul_inv(x: S.Q, h: S.Q.eq(x, S.Q{S.Z0{}, S.XH{}}) -> Empty) -> S.Q.eq(S.Q.mul(x, S.Q.inv(x)), S.Q{S.Zpos{S.XH{}}, S.XH{}}):
  match x:
    case S.Q{n, d}:
      match n:
        case S.Z0{}:
          Empty.absurd(S.Q.eq(S.Q.mul(S.Q{S.Z0{}, d}, S.Q.inv(S.Q{S.Z0{}, d})), S.Q{S.Zpos{S.XH{}}, S.XH{}}), h({==}))
        case S.Zpos{+p}:
          R.ring_eq([S.Zpos{p}, S.Zpos{d}], E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZVar{1n}, E.ZVar{0n}}}, {==})
        case S.Zneg{+p}:
          R.ring_eq([S.Zpos{p}, S.Zpos{d}], E.ZMul{E.ZMul{E.ZNeg{E.ZVar{0n}}, E.ZNeg{E.ZVar{1n}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZMul{E.ZCst{S.Zpos{S.XH{}}}, E.ZMul{E.ZVar{1n}, E.ZVar{0n}}}, {==})
