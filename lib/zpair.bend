# A bootstrap tactic for integer identities: translate a Z expression into
# the Nat expressions of its positive and negative parts (an integer x is
# of_diff(pnat x, nnat x)) and compare those with the Nat normalizer. Sound
# because of_diff is a ring homomorphism (lib/z.bend). Its coefficients are
# unary, so it is meant for the ring laws themselves; the binary-coefficient
# normalizer is lib/zring.bend, proven sound with the laws proven here.

import Base
import ./nat.bend as N
import ./natring.bend as NR
import ./z.bend as LZ
import ../spec/num.bend as S

type ZPExpr is Data:
  ZPVar{i: Nat}
  ZPCst{c: S.Z}
  ZPAdd{a: ZPExpr, b: ZPExpr}
  ZPMul{a: ZPExpr, b: ZPExpr}
  ZPNeg{a: ZPExpr}

def zlookup(env: List<&2, S.Z>, i: Nat) -> S.Z:
  match env i:
    case Nil{} j:
      S.Z0{}
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      zlookup(t, j)

def zeval(+env: List<&2, S.Z>, e: ZPExpr) -> S.Z:
  match e:
    case ZPVar{i}:
      zlookup(env, i)
    case ZPCst{c}:
      c
    case ZPAdd{a, b}:
      S.Z.add(zeval(env, a), zeval(env, b))
    case ZPMul{a, b}:
      S.Z.mul(zeval(env, a), zeval(env, b))
    case ZPNeg{a}:
      S.Z.neg(zeval(env, a))

# the parts of each variable, interleaved: variable i has its positive part
# at 2i and its negative part at 2i + 1
def penv(env: List<&2, S.Z>) -> List<&2, Nat>:
  match env:
    case Nil{}:
      Nil{}
    case Con{+h, t}:
      Con{S.Z.pnat(h), Con{S.Z.nnat(h), penv(t)}}

# the positive part (s = True{}) or the negative part of e
def tr(e: ZPExpr, +s: Bool) -> NR.NExpr:
  match e:
    case ZPVar{i}:
      match s:
        case True{}:
          NR.NVar{Nat.double(i)}
        case False{}:
          NR.NVar{1n+Nat.double(i)}
    case ZPCst{+c}:
      match s:
        case True{}:
          NR.NCst{S.Z.pnat(c)}
        case False{}:
          NR.NCst{S.Z.nnat(c)}
    case ZPAdd{a, b}:
      NR.NAdd{tr(a, s), tr(b, s)}
    case ZPMul{+a, +b}:
      match s:
        case True{}:
          NR.NAdd{NR.NMul{tr(a, True{}), tr(b, True{})}, NR.NMul{tr(a, False{}), tr(b, False{})}}
        case False{}:
          NR.NAdd{NR.NMul{tr(a, True{}), tr(b, False{})}, NR.NMul{tr(a, False{}), tr(b, True{})}}
    case ZPNeg{a}:
      tr(a, Bool.not(s))

# Soundness
# ---------

def penv_p(env: List<&2, S.Z>, i: Nat) -> {S.Z.pnat(zlookup(env, i)) == NR.lookup(penv(env), Nat.double(i)) : Nat}:
  match env i:
    case Nil{} j:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+j:
      penv_p(t, j)

def penv_n(env: List<&2, S.Z>, i: Nat) -> {S.Z.nnat(zlookup(env, i)) == NR.lookup(penv(env), 1n+Nat.double(i)) : Nat}:
  match env i:
    case Nil{} j:
      {==}
    case Con{h, t} 0n:
      {==}
    case Con{h, t} 1n+j:
      penv_n(t, j)

def zsound(+env: List<&2, S.Z>, e: ZPExpr) -> {S.Z.of_diff(NR.eval(penv(env), tr(e, True{})), NR.eval(penv(env), tr(e, False{}))) == zeval(env, e) : S.Z}:
  match e:
    case ZPVar{+i}:
      %penv_p(env, i) : {S.Z.of_diff(_, NR.lookup(penv(env), 1n+Nat.double(i))) == zlookup(env, i) : S.Z}
      %penv_n(env, i) : {S.Z.of_diff(S.Z.pnat(zlookup(env, i)), _) == zlookup(env, i) : S.Z}
      LZ.diff_parts(zlookup(env, i))
    case ZPCst{c}:
      LZ.diff_parts(c)
    case ZPAdd{+a, +b}:
      %zsound(env, a) : {S.Z.of_diff(Nat.add(NR.eval(penv(env), tr(a, True{})), NR.eval(penv(env), tr(b, True{}))), Nat.add(NR.eval(penv(env), tr(a, False{})), NR.eval(penv(env), tr(b, False{})))) == S.Z.add(_, zeval(env, b)) : S.Z}
      %zsound(env, b) : {S.Z.of_diff(Nat.add(NR.eval(penv(env), tr(a, True{})), NR.eval(penv(env), tr(b, True{}))), Nat.add(NR.eval(penv(env), tr(a, False{})), NR.eval(penv(env), tr(b, False{})))) == S.Z.add(S.Z.of_diff(NR.eval(penv(env), tr(a, True{})), NR.eval(penv(env), tr(a, False{}))), _) : S.Z}
      LZ.add_hom(NR.eval(penv(env), tr(a, True{})), NR.eval(penv(env), tr(a, False{})), NR.eval(penv(env), tr(b, True{})), NR.eval(penv(env), tr(b, False{})))
    case ZPMul{+a, +b}:
      %zsound(env, a) : {S.Z.of_diff(Nat.add(Nat.mul(NR.eval(penv(env), tr(a, True{})), NR.eval(penv(env), tr(b, True{}))), Nat.mul(NR.eval(penv(env), tr(a, False{})), NR.eval(penv(env), tr(b, False{})))), Nat.add(Nat.mul(NR.eval(penv(env), tr(a, True{})), NR.eval(penv(env), tr(b, False{}))), Nat.mul(NR.eval(penv(env), tr(a, False{})), NR.eval(penv(env), tr(b, True{}))))) == S.Z.mul(_, zeval(env, b)) : S.Z}
      %zsound(env, b) : {S.Z.of_diff(Nat.add(Nat.mul(NR.eval(penv(env), tr(a, True{})), NR.eval(penv(env), tr(b, True{}))), Nat.mul(NR.eval(penv(env), tr(a, False{})), NR.eval(penv(env), tr(b, False{})))), Nat.add(Nat.mul(NR.eval(penv(env), tr(a, True{})), NR.eval(penv(env), tr(b, False{}))), Nat.mul(NR.eval(penv(env), tr(a, False{})), NR.eval(penv(env), tr(b, True{}))))) == S.Z.mul(S.Z.of_diff(NR.eval(penv(env), tr(a, True{})), NR.eval(penv(env), tr(a, False{}))), _) : S.Z}
      LZ.mul_hom(NR.eval(penv(env), tr(a, True{})), NR.eval(penv(env), tr(a, False{})), NR.eval(penv(env), tr(b, True{})), NR.eval(penv(env), tr(b, False{})))
    case ZPNeg{+a}:
      %zsound(env, a) : {S.Z.of_diff(NR.eval(penv(env), tr(a, False{})), NR.eval(penv(env), tr(a, True{}))) == S.Z.neg(_) : S.Z}
      LZ.neg_diff(NR.eval(penv(env), tr(a, True{})), NR.eval(penv(env), tr(a, False{})))

# Two Z expressions whose positive and negative parts normalize alike are
# equal. Both hypotheses are checked by computation, {==}.
def zp_eq(+env: List<&2, S.Z>, +e1: ZPExpr, +e2: ZPExpr,
  h1: {NR.norm(tr(e1, True{})) == NR.norm(tr(e2, True{})) : List<&2, NR.NTerm>},
  h2: {NR.norm(tr(e1, False{})) == NR.norm(tr(e2, False{})) : List<&2, NR.NTerm>})
  -> {zeval(env, e1) == zeval(env, e2) : S.Z}:
  %zsound(env, e1) : {_ == zeval(env, e2) : S.Z}
  %zsound(env, e2) : {S.Z.of_diff(NR.eval(penv(env), tr(e1, True{})), NR.eval(penv(env), tr(e1, False{}))) == _ : S.Z}
  %NR.ring_eq(penv(env), tr(e1, True{}), tr(e2, True{}), h1) : {S.Z.of_diff(NR.eval(penv(env), tr(e1, True{})), NR.eval(penv(env), tr(e1, False{}))) == S.Z.of_diff(_, NR.eval(penv(env), tr(e2, False{}))) : S.Z}
  %NR.ring_eq(penv(env), tr(e1, False{}), tr(e2, False{}), h2) : {S.Z.of_diff(NR.eval(penv(env), tr(e1, True{})), NR.eval(penv(env), tr(e1, False{}))) == S.Z.of_diff(NR.eval(penv(env), tr(e1, True{})), _) : S.Z}
  {==}
