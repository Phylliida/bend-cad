# bend-cad spec: integer ring expressions and their meaning. Trusted: the
# reflective normalizer's law (LAWS.bend, ring_eq) says what these mean; the
# normalizer itself (lib/zring.bend) is not trusted, only its proof.

import Base
import ./num.bend as S

type ZExpr is Data:
  ZVar{i: Nat}
  ZCst{c: S.Z}
  ZAdd{a: ZExpr, b: ZExpr}
  ZSub{a: ZExpr, b: ZExpr}
  ZMul{a: ZExpr, b: ZExpr}
  ZNeg{a: ZExpr}

# the i-th entry of env, zero past its end
def lookup(env: List<&2, S.Z>, i: Nat) -> S.Z:
  match env i:
    case Nil{} j:
      S.Z0{}
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      lookup(t, j)

def eval(+env: List<&2, S.Z>, e: ZExpr) -> S.Z:
  match e:
    case ZVar{i}:
      lookup(env, i)
    case ZCst{c}:
      c
    case ZAdd{a, b}:
      S.Z.add(eval(env, a), eval(env, b))
    case ZSub{a, b}:
      S.Z.sub(eval(env, a), eval(env, b))
    case ZMul{a, b}:
      S.Z.mul(eval(env, a), eval(env, b))
    case ZNeg{a}:
      S.Z.neg(eval(env, a))
