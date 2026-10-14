# The order of the spec rationals: Q.lt is a strict total order up to Q.eq,
# respected by Q.eq, by adding a rational and by positive products. Through
# signs (lib/zord.bend): x < y exactly when the cross difference
# ny dx - nx dy is positive, so each law is one normalizer identity and a
# sign computation.

import Base
import ./zring.bend as R
import ./zord.bend as ZO
import ../spec/num.bend as S
import ../spec/ring.bend as E


# the cross difference of x and y, (y - x) dx dy
def dif(+x: S.Q, +y: S.Q) -> S.Z:
  S.Z.sub(S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}))

# x < y exactly when the cross difference is positive
def lt_dif(+x: S.Q, +y: S.Q, h: S.Q.lt(x, y)) -> ZO.pos(dif(x, y)):
  ZO.lt_pos(S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}), S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), h)

def dif_lt(+x: S.Q, +y: S.Q, h: ZO.pos(dif(x, y))) -> S.Q.lt(x, y):
  ZO.pos_lt(S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}), S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), h)

# Strict order
# ------------

def q_lt_irrefl(+x: S.Q, h: S.Q.lt(x, x)) -> Empty:
  ZO.pos_zero(dif(x, x), R.ring_eq([S.Q.num(x), S.Zpos{S.Q.den(x)}], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{1n}}}, E.ZCst{S.Z0{}}, {==}), lt_dif(x, x, h))

# dy (z - x) = dz (y - x) + dx (z - y), as cross differences
def q_lt_trans(+x: S.Q, +y: S.Q, +z: S.Q, h1: S.Q.lt(x, y), h2: S.Q.lt(y, z)) -> S.Q.lt(x, z):
  dif_lt(x, z, ZO.pos_cancel(S.Q.den(y), dif(x, z),
    ZO.pos_eq(S.Z.mul(S.Zpos{S.Q.den(y)}, S.Z.sub(S.Z.mul(S.Q.num(z), S.Zpos{S.Q.den(x)}), S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(z)}))), S.Z.add(S.Z.mul(S.Zpos{S.Q.den(z)}, S.Z.sub(S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}))), S.Z.mul(S.Zpos{S.Q.den(x)}, S.Z.sub(S.Z.mul(S.Q.num(z), S.Zpos{S.Q.den(y)}), S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(z)})))),
      R.ring_eq([S.Q.num(x), S.Zpos{S.Q.den(x)}, S.Q.num(y), S.Zpos{S.Q.den(y)}, S.Q.num(z), S.Zpos{S.Q.den(z)}], E.ZMul{E.ZVar{3n}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{5n}}}}, E.ZAdd{E.ZMul{E.ZVar{5n}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}}, E.ZMul{E.ZVar{1n}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{3n}}, E.ZMul{E.ZVar{2n}, E.ZVar{5n}}}}}, {==}),
      ZO.pos_add(S.Z.mul(S.Zpos{S.Q.den(z)}, S.Z.sub(S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}))), S.Z.mul(S.Zpos{S.Q.den(x)}, S.Z.sub(S.Z.mul(S.Q.num(z), S.Zpos{S.Q.den(y)}), S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(z)}))),
        ZO.pos_mul(S.Zpos{S.Q.den(z)}, dif(x, y), Unit{}, lt_dif(x, y, h1)),
        ZO.pos_mul(S.Zpos{S.Q.den(x)}, dif(y, z), Unit{}, lt_dif(y, z, h2))))))

# a comparison's verdicts EQ and GT
def q_cmp_eq(+x: S.Q, +y: S.Q, e: {S.Q.cmp(x, y) == EQ{} : Cmp}) -> S.Q.eq(x, y):
  ZO.sub_eq(S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}), S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), ZO.eq_zero(S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}), S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), e))

def q_cmp_gt(+x: S.Q, +y: S.Q, e: {S.Q.cmp(x, y) == GT{} : Cmp}) -> S.Q.lt(y, x):
  dif_lt(y, x, ZO.pos_eq(dif(y, x), S.Z.neg(S.Z.sub(S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}))), R.ring_eq([S.Q.num(x), S.Zpos{S.Q.den(x)}, S.Q.num(y), S.Zpos{S.Q.den(y)}], E.ZSub{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZMul{E.ZVar{2n}, E.ZVar{1n}}}, E.ZNeg{E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}}, {==}), ZO.gt_pos(S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}), S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), e)))

# by the comparison's verdict c
def q_lt_total.go(+x: S.Q, +y: S.Q, c: Cmp, e: {S.Q.cmp(x, y) == c : Cmp}) -> Or(S.Q.lt(x, y), Or(S.Q.eq(x, y), S.Q.lt(y, x))):
  match c:
    case LT{}:
      Inl{e}
    case EQ{}:
      Inr{Inl{q_cmp_eq(x, y, e)}}
    case GT{}:
      Inr{Inr{q_cmp_gt(x, y, e)}}

def q_lt_total(+x: S.Q, +y: S.Q) -> Or(S.Q.lt(x, y), Or(S.Q.eq(x, y), S.Q.lt(y, x))):
  q_lt_total.go(x, y, S.Q.cmp(x, y), {==})

# Q.eq respects the order
# -----------------------

# dx (y - x2) = dx2 (y - x), using nx dx2 = nx2 dx
def q_lt_cong_l.eq(+x: S.Q, +x2: S.Q, +y: S.Q, h: S.Q.eq(x, x2)) -> {S.Z.mul(S.Zpos{S.Q.den(x)}, S.Z.sub(S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x2)}), S.Z.mul(S.Q.num(x2), S.Zpos{S.Q.den(y)}))) == S.Z.mul(S.Zpos{S.Q.den(x2)}, S.Z.sub(S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}))) : S.Z}:
  %R.ring_eq([S.Q.num(x), S.Zpos{S.Q.den(x)}, S.Q.num(x2), S.Zpos{S.Q.den(x2)}, S.Q.num(y), S.Zpos{S.Q.den(y)}], E.ZSub{E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{1n}}, E.ZVar{3n}}, E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{1n}}, E.ZVar{5n}}}, E.ZMul{E.ZVar{1n}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{3n}}, E.ZMul{E.ZVar{2n}, E.ZVar{5n}}}}, {==}) : {_ == S.Z.mul(S.Zpos{S.Q.den(x2)}, S.Z.sub(S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}))) : S.Z}
  %R.ring_eq([S.Q.num(x), S.Zpos{S.Q.den(x)}, S.Q.num(x2), S.Zpos{S.Q.den(x2)}, S.Q.num(y), S.Zpos{S.Q.den(y)}], E.ZSub{E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{1n}}, E.ZVar{3n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{3n}}, E.ZVar{5n}}}, E.ZMul{E.ZVar{3n}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{5n}}}}, {==}) : {S.Z.sub(S.Z.mul(S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), S.Zpos{S.Q.den(x2)}), S.Z.mul(S.Z.mul(S.Q.num(x2), S.Zpos{S.Q.den(x)}), S.Zpos{S.Q.den(y)})) == _ : S.Z}
  %h : {S.Z.sub(S.Z.mul(S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), S.Zpos{S.Q.den(x2)}), S.Z.mul(_, S.Zpos{S.Q.den(y)})) == S.Z.sub(S.Z.mul(S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), S.Zpos{S.Q.den(x2)}), S.Z.mul(S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(x2)}), S.Zpos{S.Q.den(y)})) : S.Z}
  {==}

def q_lt_cong_l(+x: S.Q, +x2: S.Q, +y: S.Q, h: S.Q.eq(x, x2), l: S.Q.lt(x, y)) -> S.Q.lt(x2, y):
  dif_lt(x2, y, ZO.pos_cancel(S.Q.den(x), dif(x2, y),
    ZO.pos_eq(S.Z.mul(S.Zpos{S.Q.den(x)}, S.Z.sub(S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x2)}), S.Z.mul(S.Q.num(x2), S.Zpos{S.Q.den(y)}))), S.Z.mul(S.Zpos{S.Q.den(x2)}, S.Z.sub(S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}))), q_lt_cong_l.eq(x, x2, y, h),
      ZO.pos_mul(S.Zpos{S.Q.den(x2)}, dif(x, y), Unit{}, lt_dif(x, y, l)))))

# dy (y2 - x) = dy2 (y - x), using ny dy2 = ny2 dy
def q_lt_cong_r.eq(+x: S.Q, +y: S.Q, +y2: S.Q, h: S.Q.eq(y, y2)) -> {S.Z.mul(S.Zpos{S.Q.den(y)}, S.Z.sub(S.Z.mul(S.Q.num(y2), S.Zpos{S.Q.den(x)}), S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y2)}))) == S.Z.mul(S.Zpos{S.Q.den(y2)}, S.Z.sub(S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}))) : S.Z}:
  %R.ring_eq([S.Q.num(x), S.Zpos{S.Q.den(x)}, S.Q.num(y), S.Zpos{S.Q.den(y)}, S.Q.num(y2), S.Zpos{S.Q.den(y2)}], E.ZSub{E.ZMul{E.ZMul{E.ZVar{4n}, E.ZVar{3n}}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{5n}}, E.ZVar{3n}}}, E.ZMul{E.ZVar{3n}, E.ZSub{E.ZMul{E.ZVar{4n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{5n}}}}, {==}) : {_ == S.Z.mul(S.Zpos{S.Q.den(y2)}, S.Z.sub(S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}))) : S.Z}
  %R.ring_eq([S.Q.num(x), S.Zpos{S.Q.den(x)}, S.Q.num(y), S.Zpos{S.Q.den(y)}, S.Q.num(y2), S.Zpos{S.Q.den(y2)}], E.ZSub{E.ZMul{E.ZMul{E.ZVar{2n}, E.ZVar{5n}}, E.ZVar{1n}}, E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{5n}}, E.ZVar{3n}}}, E.ZMul{E.ZVar{5n}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}}, {==}) : {S.Z.sub(S.Z.mul(S.Z.mul(S.Q.num(y2), S.Zpos{S.Q.den(y)}), S.Zpos{S.Q.den(x)}), S.Z.mul(S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y2)}), S.Zpos{S.Q.den(y)})) == _ : S.Z}
  %h : {S.Z.sub(S.Z.mul(_, S.Zpos{S.Q.den(x)}), S.Z.mul(S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y2)}), S.Zpos{S.Q.den(y)})) == S.Z.sub(S.Z.mul(S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(y2)}), S.Zpos{S.Q.den(x)}), S.Z.mul(S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y2)}), S.Zpos{S.Q.den(y)})) : S.Z}
  {==}

def q_lt_cong_r(+x: S.Q, +y: S.Q, +y2: S.Q, h: S.Q.eq(y, y2), l: S.Q.lt(x, y)) -> S.Q.lt(x, y2):
  dif_lt(x, y2, ZO.pos_cancel(S.Q.den(y), dif(x, y2),
    ZO.pos_eq(S.Z.mul(S.Zpos{S.Q.den(y)}, S.Z.sub(S.Z.mul(S.Q.num(y2), S.Zpos{S.Q.den(x)}), S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y2)}))), S.Z.mul(S.Zpos{S.Q.den(y2)}, S.Z.sub(S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}))), q_lt_cong_r.eq(x, y, y2, h),
      ZO.pos_mul(S.Zpos{S.Q.den(y2)}, dif(x, y), Unit{}, lt_dif(x, y, l)))))

def q_lt_cong(+x: S.Q, +x2: S.Q, +y: S.Q, +y2: S.Q, h1: S.Q.eq(x, x2), h2: S.Q.eq(y, y2), l: S.Q.lt(x, y)) -> S.Q.lt(x2, y2):
  q_lt_cong_r(x2, y, y2, h2, q_lt_cong_l(x, x2, y, h1, l))

# The order and the operations
# ----------------------------

# (y + z) - (x + z), as a cross difference, is dz dz (y - x)
def q_lt_add(+x: S.Q, +y: S.Q, +z: S.Q, h: S.Q.lt(x, y)) -> S.Q.lt(S.Q.add(x, z), S.Q.add(y, z)):
  dif_lt(S.Q.add(x, z), S.Q.add(y, z),
    ZO.pos_eq(dif(S.Q.add(x, z), S.Q.add(y, z)), S.Z.mul(S.Zpos{S.Q.den(z)}, S.Z.mul(S.Zpos{S.Q.den(z)}, S.Z.sub(S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)})))),
      R.ring_eq([S.Q.num(x), S.Zpos{S.Q.den(x)}, S.Q.num(y), S.Zpos{S.Q.den(y)}, S.Q.num(z), S.Zpos{S.Q.den(z)}], E.ZSub{E.ZMul{E.ZAdd{E.ZMul{E.ZVar{2n}, E.ZVar{5n}}, E.ZMul{E.ZVar{4n}, E.ZVar{3n}}}, E.ZMul{E.ZVar{1n}, E.ZVar{5n}}}, E.ZMul{E.ZAdd{E.ZMul{E.ZVar{0n}, E.ZVar{5n}}, E.ZMul{E.ZVar{4n}, E.ZVar{1n}}}, E.ZMul{E.ZVar{3n}, E.ZVar{5n}}}}, E.ZMul{E.ZVar{5n}, E.ZMul{E.ZVar{5n}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZVar{1n}}, E.ZMul{E.ZVar{0n}, E.ZVar{3n}}}}}, {==}),
      ZO.pos_mul(S.Zpos{S.Q.den(z)}, S.Z.mul(S.Zpos{S.Q.den(z)}, S.Z.sub(S.Z.mul(S.Q.num(y), S.Zpos{S.Q.den(x)}), S.Z.mul(S.Q.num(x), S.Zpos{S.Q.den(y)}))), Unit{},
        ZO.pos_mul(S.Zpos{S.Q.den(z)}, dif(x, y), Unit{}, lt_dif(x, y, h)))))

# 0 < x y: its cross difference with 0 is the product of theirs
def q_lt_mul(+x: S.Q, +y: S.Q, hx: S.Q.lt(S.Q{S.Z0{}, S.XH{}}, x), hy: S.Q.lt(S.Q{S.Z0{}, S.XH{}}, y)) -> S.Q.lt(S.Q{S.Z0{}, S.XH{}}, S.Q.mul(x, y)):
  dif_lt(S.Q{S.Z0{}, S.XH{}}, S.Q.mul(x, y),
    ZO.pos_eq(dif(S.Q{S.Z0{}, S.XH{}}, S.Q.mul(x, y)), S.Z.mul(S.Z.sub(S.Z.mul(S.Q.num(x), S.Zpos{S.XH{}}), S.Z.mul(S.Z0{}, S.Zpos{S.Q.den(x)})), S.Z.sub(S.Z.mul(S.Q.num(y), S.Zpos{S.XH{}}), S.Z.mul(S.Z0{}, S.Zpos{S.Q.den(y)}))),
      R.ring_eq([S.Q.num(x), S.Zpos{S.Q.den(x)}, S.Q.num(y), S.Zpos{S.Q.den(y)}], E.ZSub{E.ZMul{E.ZMul{E.ZVar{0n}, E.ZVar{2n}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZMul{E.ZCst{S.Z0{}}, E.ZMul{E.ZVar{1n}, E.ZVar{3n}}}}, E.ZMul{E.ZSub{E.ZMul{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{1n}}}, E.ZSub{E.ZMul{E.ZVar{2n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZMul{E.ZCst{S.Z0{}}, E.ZVar{3n}}}}, {==}),
      ZO.pos_mul(S.Z.sub(S.Z.mul(S.Q.num(x), S.Zpos{S.XH{}}), S.Z.mul(S.Z0{}, S.Zpos{S.Q.den(x)})), S.Z.sub(S.Z.mul(S.Q.num(y), S.Zpos{S.XH{}}), S.Z.mul(S.Z0{}, S.Zpos{S.Q.den(y)})), lt_dif(S.Q{S.Z0{}, S.XH{}}, x, hx), lt_dif(S.Q{S.Z0{}, S.XH{}}, y, hy))))
