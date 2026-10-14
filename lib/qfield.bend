# The canonical rationals: 0, or a sign and a Stern-Brocot word
# (lib/sb.bend). Every rational is exactly one of these, so Bend's own
# equality is equality of rationals, and they form an ordered field
# (qfield, at the end): the ordered-field axioms of spec/field.bend are
# satisfiable, and meanings can be evaluated in a concrete field. The
# operations go through the spec rationals: to_q, operate, of_q.

import Base
import ./natord.bend as NO
import ./q.bend as LQ
import ./qring.bend as QR
import ./qord.bend as LQO
import ./sb.bend as W
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/field.bend as O

type QC is Data:
  QZ{}
  QP{w: W.SB}
  QN{w: W.SB}

def absurd(-A: Type, x: Empty) -> A:
  match x:

def pp_qp(p: W.PP) -> S.Q:
  match p:
    case W.PP{a, b}:
      S.Q{S.Zpos{a}, b}

def pp_qn(p: W.PP) -> S.Q:
  match p:
    case W.PP{a, b}:
      S.Q{S.Zneg{a}, b}

def to_q(c: QC) -> S.Q:
  match c:
    case QZ{}:
      S.Q{S.Z0{}, S.XH{}}
    case QP{w}:
      pp_qp(W.decode(w))
    case QN{w}:
      pp_qn(W.decode(w))

def of_q.go(n: S.Z, +d: S.Pos) -> QC:
  match n:
    case S.Z0{}:
      QZ{}
    case S.Zpos{p}:
      QP{W.encode(p, d)}
    case S.Zneg{p}:
      QN{W.encode(p, d)}

def of_q(+x: S.Q) -> QC:
  of_q.go(S.Q.num(x), S.Q.den(x))

# to_q (of_q x) = x
# -----------------

def pp_qp_eq(p: W.PP, +n: S.Pos, +d: S.Pos, h: W.pp_eq(p, n, d)) -> S.Q.eq(pp_qp(p), S.Q{S.Zpos{n}, d}):
  match p:
    case W.PP{a, b}:
      h

def pp_qn_eq(p: W.PP, +n: S.Pos, +d: S.Pos, h: W.pp_eq(p, n, d)) -> S.Q.eq(pp_qn(p), S.Q{S.Zneg{n}, d}):
  match p:
    case W.PP{+a, +b}:
      Equal.cong(S.Z, S.Z, z => S.Z.neg(z), S.Z.mul(S.Zpos{a}, S.Zpos{d}), S.Z.mul(S.Zpos{n}, S.Zpos{b}), h)

def dec_enc(+p: S.Pos, +d: S.Pos) -> W.pp_eq(W.decode(W.encode(p, d)), p, d):
  W.dec_enc(Nat.add(S.Pos.nat(p), S.Pos.nat(d)), S.Pos.cmp(p, d), p, d, {==}, NO.le_refl(Nat.add(S.Pos.nat(p), S.Pos.nat(d))))

def to_of.go(n: S.Z, +d: S.Pos) -> S.Q.eq(to_q(of_q.go(n, d)), S.Q{n, d}):
  match n:
    case S.Z0{}:
      {==}
    case S.Zpos{+p}:
      pp_qp_eq(W.decode(W.encode(p, d)), p, d, dec_enc(p, d))
    case S.Zneg{+p}:
      pp_qn_eq(W.decode(W.encode(p, d)), p, d, dec_enc(p, d))

def to_of(x: S.Q) -> S.Q.eq(to_q(of_q(x)), x):
  match x:
    case S.Q{n, +d}:
      to_of.go(n, d)

# of_q respects Q.eq
# ------------------

# a type picked by an integer's sign: a rewrite through it refutes Z0 = Zpos ..
def ZD(z: S.Z, a: Type, b: Type, c: Type) -> Type:
  match z:
    case S.Z0{}:
      a
    case S.Zpos{p}:
      b
    case S.Zneg{p}:
      c

def of_eq.go(n: S.Z, +d: S.Pos, n2: S.Z, +d2: S.Pos, h: {S.Z.mul(n, S.Zpos{d2}) == S.Z.mul(n2, S.Zpos{d}) : S.Z}) -> {of_q.go(n, d) == of_q.go(n2, d2) : QC}:
  match n n2:
    case S.Z0{} S.Z0{}:
      {==}
    case S.Z0{} S.Zpos{p2}:
      %h : ZD(_, Unit, {QZ{} == QP{W.encode(p2, d2)} : QC}, Unit)
      Unit{}
    case S.Z0{} S.Zneg{p2}:
      %h : ZD(_, Unit, Unit, {QZ{} == QN{W.encode(p2, d2)} : QC})
      Unit{}
    case S.Zpos{p} S.Z0{}:
      %h : ZD(_, {QP{W.encode(p, d)} == QZ{} : QC}, Unit, Unit)
      Unit{}
    case S.Zneg{p} S.Z0{}:
      %h : ZD(_, {QN{W.encode(p, d)} == QZ{} : QC}, Unit, Unit)
      Unit{}
    case S.Zpos{p} S.Zneg{p2}:
      %h : ZD(_, Unit, Unit, {QP{W.encode(p, d)} == QN{W.encode(p2, d2)} : QC})
      Unit{}
    case S.Zneg{p} S.Zpos{p2}:
      %h : ZD(_, Unit, {QN{W.encode(p, d)} == QP{W.encode(p2, d2)} : QC}, Unit)
      Unit{}
    case S.Zpos{+p} S.Zpos{+p2}:
      Equal.cong(W.SB, QC, w => QP{w}, W.encode(p, d), W.encode(p2, d2), W.enc_resp(p, d, p2, d2, h))
    case S.Zneg{+p} S.Zneg{+p2}:
      Equal.cong(W.SB, QC, w => QN{w}, W.encode(p, d), W.encode(p2, d2),
        W.enc_resp(p, d, p2, d2, Equal.cong(S.Z, S.Z, z => S.Z.neg(z), S.Zneg{S.Pos.mul(p, d2)}, S.Zneg{S.Pos.mul(p2, d)}, h)))

def of_eq(x: S.Q, y: S.Q, h: S.Q.eq(x, y)) -> {of_q(x) == of_q(y) : QC}:
  match x y:
    case S.Q{n, +d} S.Q{n2, +d2}:
      of_eq.go(n, d, n2, d2, h)

# of_q (to_q c) = c
# -----------------

def of_qp(p: W.PP) -> {of_q(pp_qp(p)) == QP{W.encode_pp(p)} : QC}:
  match p:
    case W.PP{a, b}:
      {==}

def of_qn(p: W.PP) -> {of_q(pp_qn(p)) == QN{W.encode_pp(p)} : QC}:
  match p:
    case W.PP{a, b}:
      {==}

def of_to(c: QC) -> {of_q(to_q(c)) == c : QC}:
  match c:
    case QZ{}:
      {==}
    case QP{+w}:
      Equal.trans(QC, of_q(pp_qp(W.decode(w))), QP{W.encode_pp(W.decode(w))}, QP{w}, of_qp(W.decode(w)),
        Equal.cong(W.SB, QC, v => QP{v}, W.encode_pp(W.decode(w)), w, W.enc_dec(w)))
    case QN{+w}:
      Equal.trans(QC, of_q(pp_qn(W.decode(w))), QN{W.encode_pp(W.decode(w))}, QN{w}, of_qn(W.decode(w)),
        Equal.cong(W.SB, QC, v => QN{v}, W.encode_pp(W.decode(w)), w, W.enc_dec(w)))

# The field
# ---------

def zero() -> QC:
  QZ{}

def one() -> QC:
  QP{W.SB1{}}

def add(+a: QC, +b: QC) -> QC:
  of_q(S.Q.add(to_q(a), to_q(b)))

def mul(+a: QC, +b: QC) -> QC:
  of_q(S.Q.mul(to_q(a), to_q(b)))

def neg(+a: QC) -> QC:
  of_q(S.Q.neg(to_q(a)))

def inv(+a: QC) -> QC:
  of_q(S.Q.inv(to_q(a)))

def lt(+a: QC, +b: QC) -> Data:
  {S.Q.cmp(to_q(a), to_q(b)) == LT{} : Cmp}

# x = to_q (of_q x)
def back(+x: S.Q) -> S.Q.eq(x, to_q(of_q(x))):
  LQ.q_sym(to_q(of_q(x)), x, to_of(x))

# rational identities
def q_add_assoc(+x: S.Q, +y: S.Q, +z: S.Q) -> S.Q.eq(S.Q.add(S.Q.add(x, y), z), S.Q.add(x, S.Q.add(y, z))):
  QR.qring_eq([x, y, z], E.QAdd{E.QAdd{E.QVar{0n}, E.QVar{1n}}, E.QVar{2n}}, E.QAdd{E.QVar{0n}, E.QAdd{E.QVar{1n}, E.QVar{2n}}}, {==})

def q_mul_assoc(+x: S.Q, +y: S.Q, +z: S.Q) -> S.Q.eq(S.Q.mul(S.Q.mul(x, y), z), S.Q.mul(x, S.Q.mul(y, z))):
  QR.qring_eq([x, y, z], E.QMul{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QVar{2n}}, E.QMul{E.QVar{0n}, E.QMul{E.QVar{1n}, E.QVar{2n}}}, {==})

def q_mul_add(+x: S.Q, +y: S.Q, +z: S.Q) -> S.Q.eq(S.Q.mul(x, S.Q.add(y, z)), S.Q.add(S.Q.mul(x, y), S.Q.mul(x, z))):
  QR.qring_eq([x, y, z], E.QMul{E.QVar{0n}, E.QAdd{E.QVar{1n}, E.QVar{2n}}}, E.QAdd{E.QMul{E.QVar{0n}, E.QVar{1n}}, E.QMul{E.QVar{0n}, E.QVar{2n}}}, {==})

def q_add_zero(+x: S.Q) -> S.Q.eq(S.Q.add(x, S.Q{S.Z0{}, S.XH{}}), x):
  QR.qring_eq([x], E.QAdd{E.QVar{0n}, E.QCst{S.Q{S.Z0{}, S.XH{}}}}, E.QVar{0n}, {==})

def q_add_neg(+x: S.Q) -> S.Q.eq(S.Q.add(x, S.Q.neg(x)), S.Q{S.Z0{}, S.XH{}}):
  QR.qring_eq([x], E.QAdd{E.QVar{0n}, E.QNeg{E.QVar{0n}}}, E.QCst{S.Q{S.Z0{}, S.XH{}}}, {==})

def q_mul_one(+x: S.Q) -> S.Q.eq(S.Q.mul(x, S.Q{S.Zpos{S.XH{}}, S.XH{}}), x):
  QR.qring_eq([x], E.QMul{E.QVar{0n}, E.QCst{S.Q{S.Zpos{S.XH{}}, S.XH{}}}}, E.QVar{0n}, {==})

# The axioms
# ----------

def add_assoc(+a: QC, +b: QC, +c: QC) -> {add(add(a, b), c) == add(a, add(b, c)) : QC}:
  of_eq(S.Q.add(to_q(add(a, b)), to_q(c)), S.Q.add(to_q(a), to_q(add(b, c))),
    LQ.q_trans(S.Q.add(to_q(add(a, b)), to_q(c)), S.Q.add(S.Q.add(to_q(a), to_q(b)), to_q(c)), S.Q.add(to_q(a), to_q(add(b, c))),
      LQ.q_add_cong_l(to_q(add(a, b)), S.Q.add(to_q(a), to_q(b)), to_q(c), to_of(S.Q.add(to_q(a), to_q(b)))),
      LQ.q_trans(S.Q.add(S.Q.add(to_q(a), to_q(b)), to_q(c)), S.Q.add(to_q(a), S.Q.add(to_q(b), to_q(c))), S.Q.add(to_q(a), to_q(add(b, c))),
        q_add_assoc(to_q(a), to_q(b), to_q(c)),
        LQ.q_add_cong_r(to_q(a), S.Q.add(to_q(b), to_q(c)), to_q(add(b, c)), back(S.Q.add(to_q(b), to_q(c)))))))

def add_comm(+a: QC, +b: QC) -> {add(a, b) == add(b, a) : QC}:
  of_eq(S.Q.add(to_q(a), to_q(b)), S.Q.add(to_q(b), to_q(a)), LQ.q_add_comm(to_q(a), to_q(b)))

def add_zero(+a: QC) -> {add(a, zero()) == a : QC}:
  Equal.trans(QC, add(a, zero()), of_q(to_q(a)), a, of_eq(S.Q.add(to_q(a), S.Q{S.Z0{}, S.XH{}}), to_q(a), q_add_zero(to_q(a))), of_to(a))

def add_neg(+a: QC) -> {add(a, neg(a)) == zero() : QC}:
  of_eq(S.Q.add(to_q(a), to_q(neg(a))), S.Q{S.Z0{}, S.XH{}},
    LQ.q_trans(S.Q.add(to_q(a), to_q(neg(a))), S.Q.add(to_q(a), S.Q.neg(to_q(a))), S.Q{S.Z0{}, S.XH{}},
      LQ.q_add_cong_r(to_q(a), to_q(neg(a)), S.Q.neg(to_q(a)), to_of(S.Q.neg(to_q(a)))),
      q_add_neg(to_q(a))))

def mul_assoc(+a: QC, +b: QC, +c: QC) -> {mul(mul(a, b), c) == mul(a, mul(b, c)) : QC}:
  of_eq(S.Q.mul(to_q(mul(a, b)), to_q(c)), S.Q.mul(to_q(a), to_q(mul(b, c))),
    LQ.q_trans(S.Q.mul(to_q(mul(a, b)), to_q(c)), S.Q.mul(S.Q.mul(to_q(a), to_q(b)), to_q(c)), S.Q.mul(to_q(a), to_q(mul(b, c))),
      LQ.q_mul_cong_l(to_q(mul(a, b)), S.Q.mul(to_q(a), to_q(b)), to_q(c), to_of(S.Q.mul(to_q(a), to_q(b)))),
      LQ.q_trans(S.Q.mul(S.Q.mul(to_q(a), to_q(b)), to_q(c)), S.Q.mul(to_q(a), S.Q.mul(to_q(b), to_q(c))), S.Q.mul(to_q(a), to_q(mul(b, c))),
        q_mul_assoc(to_q(a), to_q(b), to_q(c)),
        LQ.q_mul_cong_r(to_q(a), S.Q.mul(to_q(b), to_q(c)), to_q(mul(b, c)), back(S.Q.mul(to_q(b), to_q(c)))))))

def mul_comm(+a: QC, +b: QC) -> {mul(a, b) == mul(b, a) : QC}:
  of_eq(S.Q.mul(to_q(a), to_q(b)), S.Q.mul(to_q(b), to_q(a)), LQ.q_mul_comm(to_q(a), to_q(b)))

def mul_one(+a: QC) -> {mul(a, one()) == a : QC}:
  Equal.trans(QC, mul(a, one()), of_q(to_q(a)), a, of_eq(S.Q.mul(to_q(a), S.Q{S.Zpos{S.XH{}}, S.XH{}}), to_q(a), q_mul_one(to_q(a))), of_to(a))

def mul_add(+a: QC, +b: QC, +c: QC) -> {mul(a, add(b, c)) == add(mul(a, b), mul(a, c)) : QC}:
  of_eq(S.Q.mul(to_q(a), to_q(add(b, c))), S.Q.add(to_q(mul(a, b)), to_q(mul(a, c))),
    LQ.q_trans(S.Q.mul(to_q(a), to_q(add(b, c))), S.Q.mul(to_q(a), S.Q.add(to_q(b), to_q(c))), S.Q.add(to_q(mul(a, b)), to_q(mul(a, c))),
      LQ.q_mul_cong_r(to_q(a), to_q(add(b, c)), S.Q.add(to_q(b), to_q(c)), to_of(S.Q.add(to_q(b), to_q(c)))),
      LQ.q_trans(S.Q.mul(to_q(a), S.Q.add(to_q(b), to_q(c))), S.Q.add(S.Q.mul(to_q(a), to_q(b)), S.Q.mul(to_q(a), to_q(c))), S.Q.add(to_q(mul(a, b)), to_q(mul(a, c))),
        q_mul_add(to_q(a), to_q(b), to_q(c)),
        LQ.q_trans(S.Q.add(S.Q.mul(to_q(a), to_q(b)), S.Q.mul(to_q(a), to_q(c))), S.Q.add(to_q(mul(a, b)), S.Q.mul(to_q(a), to_q(c))), S.Q.add(to_q(mul(a, b)), to_q(mul(a, c))),
          LQ.q_add_cong_l(S.Q.mul(to_q(a), to_q(b)), to_q(mul(a, b)), S.Q.mul(to_q(a), to_q(c)), back(S.Q.mul(to_q(a), to_q(b)))),
          LQ.q_add_cong_r(to_q(mul(a, b)), S.Q.mul(to_q(a), to_q(c)), to_q(mul(a, c)), back(S.Q.mul(to_q(a), to_q(c))))))))

# a nonzero element is a nonzero rational
def nz(+a: QC, ne: {a == zero() : QC} -> Empty) -> S.Q.eq(to_q(a), S.Q{S.Z0{}, S.XH{}}) -> Empty:
  e => ne(Equal.trans(QC, a, of_q(to_q(a)), zero(), Equal.sym(QC, of_q(to_q(a)), a, of_to(a)), of_eq(to_q(a), S.Q{S.Z0{}, S.XH{}}, e)))

def mul_inv(+a: QC, ne: {a == zero() : QC} -> Empty) -> {mul(a, inv(a)) == one() : QC}:
  of_eq(S.Q.mul(to_q(a), to_q(inv(a))), S.Q{S.Zpos{S.XH{}}, S.XH{}},
    LQ.q_trans(S.Q.mul(to_q(a), to_q(inv(a))), S.Q.mul(to_q(a), S.Q.inv(to_q(a))), S.Q{S.Zpos{S.XH{}}, S.XH{}},
      LQ.q_mul_cong_r(to_q(a), to_q(inv(a)), S.Q.inv(to_q(a)), to_of(S.Q.inv(to_q(a)))),
      LQ.q_mul_inv(to_q(a), nz(a, ne))))

def lt_irrefl(+a: QC, h: lt(a, a)) -> Empty:
  LQO.q_lt_irrefl(to_q(a), h)

def lt_trans(+a: QC, +b: QC, +c: QC, h1: lt(a, b), h2: lt(b, c)) -> lt(a, c):
  LQO.q_lt_trans(to_q(a), to_q(b), to_q(c), h1, h2)

def lt_total.go(+a: QC, +b: QC, t: Or(S.Q.lt(to_q(a), to_q(b)), Or(S.Q.eq(to_q(a), to_q(b)), S.Q.lt(to_q(b), to_q(a))))) -> Or(lt(a, b), Or({a == b : QC}, lt(b, a))):
  match t:
    case Inl{l}:
      Inl{l}
    case Inr{Inl{e}}:
      Inr{Inl{Equal.trans(QC, a, of_q(to_q(a)), b, Equal.sym(QC, of_q(to_q(a)), a, of_to(a)), Equal.trans(QC, of_q(to_q(a)), of_q(to_q(b)), b, of_eq(to_q(a), to_q(b), e), of_to(b)))}}
    case Inr{Inr{g}}:
      Inr{Inr{g}}

def lt_total(+a: QC, +b: QC) -> Or(lt(a, b), Or({a == b : QC}, lt(b, a))):
  lt_total.go(a, b, LQO.q_lt_total(to_q(a), to_q(b)))

def lt_add(+a: QC, +b: QC, +c: QC, h: lt(a, b)) -> lt(add(a, c), add(b, c)):
  LQO.q_lt_cong(S.Q.add(to_q(a), to_q(c)), to_q(add(a, c)), S.Q.add(to_q(b), to_q(c)), to_q(add(b, c)), back(S.Q.add(to_q(a), to_q(c))), back(S.Q.add(to_q(b), to_q(c))), LQO.q_lt_add(to_q(a), to_q(b), to_q(c), h))

def lt_mul(+a: QC, +b: QC, ha: lt(zero(), a), hb: lt(zero(), b)) -> lt(zero(), mul(a, b)):
  LQO.q_lt_cong(S.Q{S.Z0{}, S.XH{}}, S.Q{S.Z0{}, S.XH{}}, S.Q.mul(to_q(a), to_q(b)), to_q(mul(a, b)), LQ.q_refl(S.Q{S.Z0{}, S.XH{}}), back(S.Q.mul(to_q(a), to_q(b))), LQO.q_lt_mul(to_q(a), to_q(b), ha, hb))

def zero_lt_one() -> lt(zero(), one()):
  {==}

# The canonical rationals are an ordered field
def qfield() -> O.OField:
  O.OField{QC, zero(), one(), a => b => add(a, b), a => b => mul(a, b), a => neg(a), a => inv(a), a => b => lt(a, b),
    a => b => c => add_assoc(a, b, c), a => b => add_comm(a, b), a => add_zero(a), a => add_neg(a),
    a => b => c => mul_assoc(a, b, c), a => b => mul_comm(a, b), a => mul_one(a), a => b => c => mul_add(a, b, c),
    a => h => mul_inv(a, h), a => h => lt_irrefl(a, h), a => b => c => h1 => h2 => lt_trans(a, b, c, h1, h2),
    a => b => lt_total(a, b), a => b => c => h => lt_add(a, b, c, h), a => b => ha => hb => lt_mul(a, b, ha, hb), zero_lt_one()}
