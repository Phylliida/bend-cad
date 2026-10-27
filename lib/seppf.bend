# bend-cad: separating a tagged identity (PLAN-sk13b B3). A complex form
# x = (x_re, x_im) is encoded as the polynomial x_re + t x_im, t a variable
# that neither part mentions, so that one elimination decides membership
# modulo K for both parts at once. This is the way back: if
# A + t B and C + t D are the same polynomial and none of A, B, C, D
# mentions t, then A, C are the same and B, D are the same. At each
# rational point, set t to 0 (A = C) and to 1 (A + B = C + D); the
# rational steps are identities the integer normalizer checks
# (lib/qring.bend). Proofs only.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/solve.bend as SV
import ./q.bend as LQ
import ./qring.bend as QR
import ./qnorm.bend as QN
import ./identpf.bend as ID

def q0() -> S.Q:
  S.Q{S.Z0{}, S.XH{}}

def q1() -> S.Q:
  S.Q{S.Zpos{S.XH{}}, S.XH{}}

# every variable of e is below t
def vbelow(e: E.QExpr, +t: Nat) -> Bool:
  match e:
    case E.QVar{i}:
      SV.lt(i, t)
    case E.QCst{q}:
      True{}
    case E.QAdd{a, b}:
      SV.band(vbelow(a, t), vbelow(b, t))
    case E.QSub{a, b}:
      SV.band(vbelow(a, t), vbelow(b, t))
    case E.QMul{a, b}:
      SV.band(vbelow(a, t), vbelow(b, t))
    case E.QNeg{a}:
      vbelow(a, t)

# a + t b
def tag(+a: E.QExpr, +b: E.QExpr, +t: Nat) -> E.QExpr:
  E.QAdd{a, E.QMul{E.QVar{t}, b}}

# The point with t set
# --------------------

# x's first n entries (0 past its end)
def pad(n: Nat, x: List<&2, S.Q>) -> List<&2, S.Q>:
  match n x:
    case 0n x:
      Nil{}
    case 1n+m Nil{}:
      Con{q0(), pad(m, Nil{})}
    case 1n+m Con{h, tl}:
      Con{h, pad(m, tl)}

def qcat(xs: List<&2, S.Q>, ys: List<&2, S.Q>) -> List<&2, S.Q>:
  match xs:
    case Nil{}:
      ys
    case Con{h, tl}:
      Con{h, qcat(tl, ys)}

# x with entry t set to v
def upd(+x: List<&2, S.Q>, +t: Nat, +v: S.Q) -> List<&2, S.Q>:
  qcat(pad(t, x), [v])

def look_pad.p(b: Bool, x: List<&2, S.Q>, +ys: List<&2, S.Q>, i: Nat) -> Data:
  match b:
    case False{}:
      Unit
    case True{}:
      {E.qlookup(qcat(pad(0n, x), ys), i) == E.qlookup(x, i) : S.Q}

def look_pad.f(x: List<&2, S.Q>, +ys: List<&2, S.Q>, i: Nat, h: {SV.lt(i, 0n) == True{} : Bool}) -> {E.qlookup(qcat(pad(0n, x), ys), i) == E.qlookup(x, i) : S.Q}:
  match i:
    case 0n:
      %h : look_pad.p(_, x, ys, 0n)
      Unit{}
    case 1n+j:
      %h : look_pad.p(_, x, ys, 1n+j)
      Unit{}

# below n, the padded point reads as x
def look_pad(n: Nat, x: List<&2, S.Q>, +ys: List<&2, S.Q>, i: Nat, h: {SV.lt(i, n) == True{} : Bool}) -> {E.qlookup(qcat(pad(n, x), ys), i) == E.qlookup(x, i) : S.Q}:
  match n x i:
    case 0n x i:
      look_pad.f(x, ys, i, h)
    case 1n+m Nil{} 0n:
      {==}
    case 1n+m Nil{} 1n+j:
      look_pad(m, Nil{}, ys, j, h)
    case 1n+m Con{hd, tl} 0n:
      {==}
    case 1n+m Con{hd, tl} 1n+j:
      look_pad(m, tl, ys, j, h)

# at n, it reads v
def look_at(n: Nat, x: List<&2, S.Q>, +v: S.Q) -> {E.qlookup(qcat(pad(n, x), [v]), n) == v : S.Q}:
  match n x:
    case 0n x:
      {==}
    case 1n+m Nil{}:
      look_at(m, Nil{}, v)
    case 1n+m Con{hd, tl}:
      look_at(m, tl, v)

def band_l(a: Bool, +b: Bool, h: {SV.band(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def band_r.p(c: Bool, +b: Bool) -> Data:
  match c:
    case False{}:
      Unit
    case True{}:
      {b == True{} : Bool}

def band_r.f(+b: Bool, h: {False{} == True{} : Bool}) -> {b == True{} : Bool}:
  %h : band_r.p(_, b)
  Unit{}

def band_r(a: Bool, +b: Bool, h: {SV.band(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      band_r.f(b, h)

# a polynomial below t reads the same at x with t set
def eval_upd(+x: List<&2, S.Q>, +t: Nat, +v: S.Q, e: E.QExpr, +h: {vbelow(e, t) == True{} : Bool}) -> {E.qeval(upd(x, t, v), e) == E.qeval(x, e) : S.Q}:
  match e:
    case E.QVar{+i}:
      look_pad(t, x, [v], i, h)
    case E.QCst{q}:
      {==}
    case E.QAdd{+a, +b}:
      %Equal.sym(S.Q, E.qeval(upd(x, t, v), a), E.qeval(x, a), eval_upd(x, t, v, a, band_l(vbelow(a, t), vbelow(b, t), h))) : {S.Q.add(_, E.qeval(upd(x, t, v), b)) == S.Q.add(E.qeval(x, a), E.qeval(x, b)) : S.Q}
      %Equal.sym(S.Q, E.qeval(upd(x, t, v), b), E.qeval(x, b), eval_upd(x, t, v, b, band_r(vbelow(a, t), vbelow(b, t), h))) : {S.Q.add(E.qeval(x, a), _) == S.Q.add(E.qeval(x, a), E.qeval(x, b)) : S.Q}
      {==}
    case E.QSub{+a, +b}:
      %Equal.sym(S.Q, E.qeval(upd(x, t, v), a), E.qeval(x, a), eval_upd(x, t, v, a, band_l(vbelow(a, t), vbelow(b, t), h))) : {S.Q.sub(_, E.qeval(upd(x, t, v), b)) == S.Q.sub(E.qeval(x, a), E.qeval(x, b)) : S.Q}
      %Equal.sym(S.Q, E.qeval(upd(x, t, v), b), E.qeval(x, b), eval_upd(x, t, v, b, band_r(vbelow(a, t), vbelow(b, t), h))) : {S.Q.sub(E.qeval(x, a), _) == S.Q.sub(E.qeval(x, a), E.qeval(x, b)) : S.Q}
      {==}
    case E.QMul{+a, +b}:
      %Equal.sym(S.Q, E.qeval(upd(x, t, v), a), E.qeval(x, a), eval_upd(x, t, v, a, band_l(vbelow(a, t), vbelow(b, t), h))) : {S.Q.mul(_, E.qeval(upd(x, t, v), b)) == S.Q.mul(E.qeval(x, a), E.qeval(x, b)) : S.Q}
      %Equal.sym(S.Q, E.qeval(upd(x, t, v), b), E.qeval(x, b), eval_upd(x, t, v, b, band_r(vbelow(a, t), vbelow(b, t), h))) : {S.Q.mul(E.qeval(x, a), _) == S.Q.mul(E.qeval(x, a), E.qeval(x, b)) : S.Q}
      {==}
    case E.QNeg{+a}:
      %Equal.sym(S.Q, E.qeval(upd(x, t, v), a), E.qeval(x, a), eval_upd(x, t, v, a, h)) : {S.Q.neg(_) == S.Q.neg(E.qeval(x, a)) : S.Q}
      {==}

# The separation
# --------------

# the identity at x with t set to v, read at x
def at_v(+x: List<&2, S.Q>, +t: Nat, +v: S.Q, +a: E.QExpr, +b: E.QExpr, +c: E.QExpr, +d: E.QExpr,
  +ha: {vbelow(a, t) == True{} : Bool}, +hb: {vbelow(b, t) == True{} : Bool}, +hc: {vbelow(c, t) == True{} : Bool}, +hd: {vbelow(d, t) == True{} : Bool},
  h: S.Q.eq(E.qeval(upd(x, t, v), tag(a, b, t)), E.qeval(upd(x, t, v), tag(c, d, t))))
  -> S.Q.eq(S.Q.add(E.qeval(x, a), S.Q.mul(v, E.qeval(x, b))), S.Q.add(E.qeval(x, c), S.Q.mul(v, E.qeval(x, d)))):
  %eval_upd(x, t, v, a, ha) : S.Q.eq(S.Q.add(_, S.Q.mul(v, E.qeval(x, b))), S.Q.add(E.qeval(x, c), S.Q.mul(v, E.qeval(x, d))))
  %eval_upd(x, t, v, b, hb) : S.Q.eq(S.Q.add(E.qeval(upd(x, t, v), a), S.Q.mul(v, _)), S.Q.add(E.qeval(x, c), S.Q.mul(v, E.qeval(x, d))))
  %eval_upd(x, t, v, c, hc) : S.Q.eq(S.Q.add(E.qeval(upd(x, t, v), a), S.Q.mul(v, E.qeval(upd(x, t, v), b))), S.Q.add(_, S.Q.mul(v, E.qeval(x, d))))
  %eval_upd(x, t, v, d, hd) : S.Q.eq(S.Q.add(E.qeval(upd(x, t, v), a), S.Q.mul(v, E.qeval(upd(x, t, v), b))), S.Q.add(E.qeval(upd(x, t, v), c), S.Q.mul(v, _)))
  %look_at(t, x, v) : S.Q.eq(S.Q.add(E.qeval(upd(x, t, v), a), S.Q.mul(_, E.qeval(upd(x, t, v), b))), S.Q.add(E.qeval(upd(x, t, v), c), S.Q.mul(_, E.qeval(upd(x, t, v), d))))
  h

# a + 0 b = a, and (c + 1 d) - c = d, as rational identities
def zm(+a: S.Q, +b: S.Q) -> S.Q.eq(S.Q.add(a, S.Q.mul(q0(), b)), a):
  QR.qring_eq([a, b], E.QAdd{E.QVar{0n}, E.QMul{E.QCst{q0()}, E.QVar{1n}}}, E.QVar{0n}, {==})

def om(+c: S.Q, +d: S.Q) -> S.Q.eq(d, S.Q.sub(S.Q.add(c, S.Q.mul(q1(), d)), c)):
  QR.qring_eq([c, d], E.QVar{1n}, E.QSub{E.QAdd{E.QVar{0n}, E.QMul{E.QCst{q1()}, E.QVar{1n}}}, E.QVar{0n}}, {==})

def sep_re.at(+x: List<&2, S.Q>, +a: E.QExpr, +b: E.QExpr, +c: E.QExpr, +d: E.QExpr, +t: Nat,
  +ha: {vbelow(a, t) == True{} : Bool}, +hb: {vbelow(b, t) == True{} : Bool}, +hc: {vbelow(c, t) == True{} : Bool}, +hd: {vbelow(d, t) == True{} : Bool},
  +hz: {QN.qzero(E.QSub{tag(a, b, t), tag(c, d, t)}) == True{} : Bool}) -> S.Q.eq(E.qeval(x, a), E.qeval(x, c)):
  LQ.q_trans(E.qeval(x, a), S.Q.add(E.qeval(x, c), S.Q.mul(q0(), E.qeval(x, d))), E.qeval(x, c),
    LQ.q_trans(E.qeval(x, a), S.Q.add(E.qeval(x, a), S.Q.mul(q0(), E.qeval(x, b))), S.Q.add(E.qeval(x, c), S.Q.mul(q0(), E.qeval(x, d))),
      LQ.q_sym(S.Q.add(E.qeval(x, a), S.Q.mul(q0(), E.qeval(x, b))), E.qeval(x, a), zm(E.qeval(x, a), E.qeval(x, b))),
      at_v(x, t, q0(), a, b, c, d, ha, hb, hc, hd, ID.ident_ok(tag(a, b, t), tag(c, d, t), hz)(upd(x, t, q0())))),
    zm(E.qeval(x, c), E.qeval(x, d)))

def sep_im.at(+x: List<&2, S.Q>, +a: E.QExpr, +b: E.QExpr, +c: E.QExpr, +d: E.QExpr, +t: Nat,
  +ha: {vbelow(a, t) == True{} : Bool}, +hb: {vbelow(b, t) == True{} : Bool}, +hc: {vbelow(c, t) == True{} : Bool}, +hd: {vbelow(d, t) == True{} : Bool},
  +hz: {QN.qzero(E.QSub{tag(a, b, t), tag(c, d, t)}) == True{} : Bool}) -> S.Q.eq(E.qeval(x, b), E.qeval(x, d)):
  LQ.q_trans(E.qeval(x, b), S.Q.sub(S.Q.add(E.qeval(x, c), S.Q.mul(q1(), E.qeval(x, d))), E.qeval(x, c)), E.qeval(x, d),
    LQ.q_trans(E.qeval(x, b), S.Q.sub(S.Q.add(E.qeval(x, c), S.Q.mul(q1(), E.qeval(x, d))), E.qeval(x, a)), S.Q.sub(S.Q.add(E.qeval(x, c), S.Q.mul(q1(), E.qeval(x, d))), E.qeval(x, c)),
      LQ.q_trans(E.qeval(x, b), S.Q.sub(S.Q.add(E.qeval(x, a), S.Q.mul(q1(), E.qeval(x, b))), E.qeval(x, a)), S.Q.sub(S.Q.add(E.qeval(x, c), S.Q.mul(q1(), E.qeval(x, d))), E.qeval(x, a)),
        om(E.qeval(x, a), E.qeval(x, b)),
        LQ.q_add_cong_l(S.Q.add(E.qeval(x, a), S.Q.mul(q1(), E.qeval(x, b))), S.Q.add(E.qeval(x, c), S.Q.mul(q1(), E.qeval(x, d))), S.Q.neg(E.qeval(x, a)),
          at_v(x, t, q1(), a, b, c, d, ha, hb, hc, hd, ID.ident_ok(tag(a, b, t), tag(c, d, t), hz)(upd(x, t, q1()))))),
      LQ.q_add_cong_r(S.Q.add(E.qeval(x, c), S.Q.mul(q1(), E.qeval(x, d))), S.Q.neg(E.qeval(x, a)), S.Q.neg(E.qeval(x, c)),
        LQ.q_neg_cong(E.qeval(x, a), E.qeval(x, c), sep_re.at(x, a, b, c, d, t, ha, hb, hc, hd, hz)))),
    LQ.q_sym(E.qeval(x, d), S.Q.sub(S.Q.add(E.qeval(x, c), S.Q.mul(q1(), E.qeval(x, d))), E.qeval(x, c)), om(E.qeval(x, c), E.qeval(x, d))))

def sep.z(+a: E.QExpr, +b: E.QExpr, +c: E.QExpr, +d: E.QExpr, +t: Nat,
  +ha: {vbelow(a, t) == True{} : Bool}, +hb: {vbelow(b, t) == True{} : Bool}, +hc: {vbelow(c, t) == True{} : Bool}, +hd: {vbelow(d, t) == True{} : Bool},
  +hz: {QN.qzero(E.QSub{tag(a, b, t), tag(c, d, t)}) == True{} : Bool}) -> SV.Ident(a, c) & SV.Ident(b, d):
  (x => sep_re.at(x, a, b, c, d, t, ha, hb, hc, hd, hz), x => sep_im.at(x, a, b, c, d, t, ha, hb, hc, hd, hz))

# a + t b = c + t d, with none mentioning t, gives a = c and b = d
def sep(+a: E.QExpr, +b: E.QExpr, +c: E.QExpr, +d: E.QExpr, +t: Nat,
  +ha: {vbelow(a, t) == True{} : Bool}, +hb: {vbelow(b, t) == True{} : Bool}, +hc: {vbelow(c, t) == True{} : Bool}, +hd: {vbelow(d, t) == True{} : Bool},
  h: SV.Ident(tag(a, b, t), tag(c, d, t))) -> SV.Ident(a, c) & SV.Ident(b, d):
  sep.z(a, b, c, d, t, ha, hb, hc, hd, ID.qzero_ident(tag(a, b, t), tag(c, d, t), h))
