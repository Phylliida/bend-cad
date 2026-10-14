# Rational identities (without division) by the integer normalizer. The spec
# rationals are unreduced, so a rational expression's numerator and
# denominator are integer expressions in the numerators and denominators of
# its variables; Q.eq is cross-multiplication, an integer identity that
# lib/zring.bend decides.

import Base
import ./zring.bend as R
import ../spec/num.bend as S
import ../spec/ring.bend as E

# Each variable x becomes two integer variables: num x at 2i, and den x - 1
# at 2i + 1 (so that a variable past the end, 0/1, reads as 0 and 0 + 1).
def zenv(env: List<&2, S.Q>) -> List<&2, S.Z>:
  match env:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{S.Q.num(x), Con{S.Z.sub(S.Zpos{S.Q.den(x)}, S.Zpos{S.XH{}}), zenv(t)}}

# the denominator of e, as an integer expression
def trd(e: E.QExpr) -> E.ZExpr:
  match e:
    case E.QVar{i}:
      E.ZAdd{E.ZVar{1n+Nat.double(i)}, E.ZCst{S.Zpos{S.XH{}}}}
    case E.QCst{c}:
      E.ZCst{S.Zpos{S.Q.den(c)}}
    case E.QAdd{a, b}:
      E.ZMul{trd(a), trd(b)}
    case E.QSub{a, b}:
      E.ZMul{trd(a), trd(b)}
    case E.QMul{a, b}:
      E.ZMul{trd(a), trd(b)}
    case E.QNeg{a}:
      trd(a)

# the numerator of e, as an integer expression
def trn(e: E.QExpr) -> E.ZExpr:
  match e:
    case E.QVar{i}:
      E.ZVar{Nat.double(i)}
    case E.QCst{c}:
      E.ZCst{S.Q.num(c)}
    case E.QAdd{+a, +b}:
      E.ZAdd{E.ZMul{trn(a), trd(b)}, E.ZMul{trn(b), trd(a)}}
    case E.QSub{+a, +b}:
      E.ZAdd{E.ZMul{trn(a), trd(b)}, E.ZMul{E.ZNeg{trn(b)}, trd(a)}}
    case E.QMul{a, b}:
      E.ZMul{trn(a), trn(b)}
    case E.QNeg{a}:
      E.ZNeg{trn(a)}

# Soundness
# ---------

def var_num(env: List<&2, S.Q>, i: Nat) -> {E.lookup(zenv(env), Nat.double(i)) == S.Q.num(E.qlookup(env, i)) : S.Z}:
  match env i:
    case Nil{} j:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+j:
      var_num(t, j)

def var_den(env: List<&2, S.Q>, i: Nat) -> {S.Z.add(E.lookup(zenv(env), 1n+Nat.double(i)), S.Zpos{S.XH{}}) == S.Zpos{S.Q.den(E.qlookup(env, i))} : S.Z}:
  match env i:
    case Nil{} j:
      {==}
    case Con{+h, t} 0n:
      R.ring_eq([S.Zpos{S.Q.den(h)}], E.ZAdd{E.ZSub{E.ZVar{0n}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZCst{S.Zpos{S.XH{}}}}, E.ZVar{0n}, {==})
    case Con{h, t} 1n+j:
      var_den(t, j)

def den_ok(+env: List<&2, S.Q>, e: E.QExpr) -> {E.eval(zenv(env), trd(e)) == S.Zpos{S.Q.den(E.qeval(env, e))} : S.Z}:
  match e:
    case E.QVar{i}:
      var_den(env, i)
    case E.QCst{c}:
      {==}
    case E.QAdd{+a, +b}:
      %den_ok(env, a) : {S.Z.mul(E.eval(zenv(env), trd(a)), E.eval(zenv(env), trd(b))) == S.Z.mul(_, S.Zpos{S.Q.den(E.qeval(env, b))}) : S.Z}
      %den_ok(env, b) : {S.Z.mul(E.eval(zenv(env), trd(a)), E.eval(zenv(env), trd(b))) == S.Z.mul(E.eval(zenv(env), trd(a)), _) : S.Z}
      {==}
    case E.QSub{+a, +b}:
      %den_ok(env, a) : {S.Z.mul(E.eval(zenv(env), trd(a)), E.eval(zenv(env), trd(b))) == S.Z.mul(_, S.Zpos{S.Q.den(E.qeval(env, b))}) : S.Z}
      %den_ok(env, b) : {S.Z.mul(E.eval(zenv(env), trd(a)), E.eval(zenv(env), trd(b))) == S.Z.mul(E.eval(zenv(env), trd(a)), _) : S.Z}
      {==}
    case E.QMul{+a, +b}:
      %den_ok(env, a) : {S.Z.mul(E.eval(zenv(env), trd(a)), E.eval(zenv(env), trd(b))) == S.Z.mul(_, S.Zpos{S.Q.den(E.qeval(env, b))}) : S.Z}
      %den_ok(env, b) : {S.Z.mul(E.eval(zenv(env), trd(a)), E.eval(zenv(env), trd(b))) == S.Z.mul(E.eval(zenv(env), trd(a)), _) : S.Z}
      {==}
    case E.QNeg{a}:
      den_ok(env, a)

def num_ok(+env: List<&2, S.Q>, e: E.QExpr) -> {E.eval(zenv(env), trn(e)) == S.Q.num(E.qeval(env, e)) : S.Z}:
  match e:
    case E.QVar{i}:
      var_num(env, i)
    case E.QCst{c}:
      {==}
    case E.QAdd{+a, +b}:
      %num_ok(env, a) : {S.Z.add(S.Z.mul(E.eval(zenv(env), trn(a)), E.eval(zenv(env), trd(b))), S.Z.mul(E.eval(zenv(env), trn(b)), E.eval(zenv(env), trd(a)))) == S.Z.add(S.Z.mul(_, S.Zpos{S.Q.den(E.qeval(env, b))}), S.Z.mul(S.Q.num(E.qeval(env, b)), S.Zpos{S.Q.den(E.qeval(env, a))})) : S.Z}
      %num_ok(env, b) : {S.Z.add(S.Z.mul(E.eval(zenv(env), trn(a)), E.eval(zenv(env), trd(b))), S.Z.mul(E.eval(zenv(env), trn(b)), E.eval(zenv(env), trd(a)))) == S.Z.add(S.Z.mul(E.eval(zenv(env), trn(a)), S.Zpos{S.Q.den(E.qeval(env, b))}), S.Z.mul(_, S.Zpos{S.Q.den(E.qeval(env, a))})) : S.Z}
      %den_ok(env, a) : {S.Z.add(S.Z.mul(E.eval(zenv(env), trn(a)), E.eval(zenv(env), trd(b))), S.Z.mul(E.eval(zenv(env), trn(b)), E.eval(zenv(env), trd(a)))) == S.Z.add(S.Z.mul(E.eval(zenv(env), trn(a)), S.Zpos{S.Q.den(E.qeval(env, b))}), S.Z.mul(E.eval(zenv(env), trn(b)), _)) : S.Z}
      %den_ok(env, b) : {S.Z.add(S.Z.mul(E.eval(zenv(env), trn(a)), E.eval(zenv(env), trd(b))), S.Z.mul(E.eval(zenv(env), trn(b)), E.eval(zenv(env), trd(a)))) == S.Z.add(S.Z.mul(E.eval(zenv(env), trn(a)), _), S.Z.mul(E.eval(zenv(env), trn(b)), E.eval(zenv(env), trd(a)))) : S.Z}
      {==}
    case E.QSub{+a, +b}:
      %num_ok(env, a) : {S.Z.add(S.Z.mul(E.eval(zenv(env), trn(a)), E.eval(zenv(env), trd(b))), S.Z.mul(S.Z.neg(E.eval(zenv(env), trn(b))), E.eval(zenv(env), trd(a)))) == S.Z.add(S.Z.mul(_, S.Zpos{S.Q.den(E.qeval(env, b))}), S.Z.mul(S.Z.neg(S.Q.num(E.qeval(env, b))), S.Zpos{S.Q.den(E.qeval(env, a))})) : S.Z}
      %num_ok(env, b) : {S.Z.add(S.Z.mul(E.eval(zenv(env), trn(a)), E.eval(zenv(env), trd(b))), S.Z.mul(S.Z.neg(E.eval(zenv(env), trn(b))), E.eval(zenv(env), trd(a)))) == S.Z.add(S.Z.mul(E.eval(zenv(env), trn(a)), S.Zpos{S.Q.den(E.qeval(env, b))}), S.Z.mul(S.Z.neg(_), S.Zpos{S.Q.den(E.qeval(env, a))})) : S.Z}
      %den_ok(env, a) : {S.Z.add(S.Z.mul(E.eval(zenv(env), trn(a)), E.eval(zenv(env), trd(b))), S.Z.mul(S.Z.neg(E.eval(zenv(env), trn(b))), E.eval(zenv(env), trd(a)))) == S.Z.add(S.Z.mul(E.eval(zenv(env), trn(a)), S.Zpos{S.Q.den(E.qeval(env, b))}), S.Z.mul(S.Z.neg(E.eval(zenv(env), trn(b))), _)) : S.Z}
      %den_ok(env, b) : {S.Z.add(S.Z.mul(E.eval(zenv(env), trn(a)), E.eval(zenv(env), trd(b))), S.Z.mul(S.Z.neg(E.eval(zenv(env), trn(b))), E.eval(zenv(env), trd(a)))) == S.Z.add(S.Z.mul(E.eval(zenv(env), trn(a)), _), S.Z.mul(S.Z.neg(E.eval(zenv(env), trn(b))), E.eval(zenv(env), trd(a)))) : S.Z}
      {==}
    case E.QMul{+a, +b}:
      %num_ok(env, a) : {S.Z.mul(E.eval(zenv(env), trn(a)), E.eval(zenv(env), trn(b))) == S.Z.mul(_, S.Q.num(E.qeval(env, b))) : S.Z}
      %num_ok(env, b) : {S.Z.mul(E.eval(zenv(env), trn(a)), E.eval(zenv(env), trn(b))) == S.Z.mul(E.eval(zenv(env), trn(a)), _) : S.Z}
      {==}
    case E.QNeg{+a}:
      %num_ok(env, a) : {S.Z.neg(E.eval(zenv(env), trn(a))) == S.Z.neg(_) : S.Z}
      {==}

# Two rational expressions are the same rational under every environment
# when their cross-multiplied integer forms normalize alike (checked by
# computation, {==}).
def qring_eq(+env: List<&2, S.Q>, +e1: E.QExpr, +e2: E.QExpr,
  h: {R.norm(E.ZMul{trn(e1), trd(e2)}) == R.norm(E.ZMul{trn(e2), trd(e1)}) : List<&2, R.ZTerm>})
  -> S.Q.eq(E.qeval(env, e1), E.qeval(env, e2)):
  %num_ok(env, e1) : {S.Z.mul(_, S.Zpos{S.Q.den(E.qeval(env, e2))}) == S.Z.mul(S.Q.num(E.qeval(env, e2)), S.Zpos{S.Q.den(E.qeval(env, e1))}) : S.Z}
  %den_ok(env, e2) : {S.Z.mul(E.eval(zenv(env), trn(e1)), _) == S.Z.mul(S.Q.num(E.qeval(env, e2)), S.Zpos{S.Q.den(E.qeval(env, e1))}) : S.Z}
  %num_ok(env, e2) : {S.Z.mul(E.eval(zenv(env), trn(e1)), E.eval(zenv(env), trd(e2))) == S.Z.mul(_, S.Zpos{S.Q.den(E.qeval(env, e1))}) : S.Z}
  %den_ok(env, e1) : {S.Z.mul(E.eval(zenv(env), trn(e1)), E.eval(zenv(env), trd(e2))) == S.Z.mul(E.eval(zenv(env), trn(e2)), _) : S.Z}
  R.ring_eq(zenv(env), E.ZMul{trn(e1), trd(e2)}, E.ZMul{trn(e2), trd(e1)}, h)
