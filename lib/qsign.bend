# bend-cad: a rational's sign, as spec/solve.bend's checks read it, in
# every ordered field: m >= 0 (refok's nonneg) gives ofq(m) >= 0, m > 0
# (strict_pos) gives ofq(m) > 0, a zero numerator gives 0. Proofs only.
# (lib/satpf.bend has its own copies, proven through its lexicographic
# signs.)

import Base
import ../spec/num.bend as S
import ../spec/field.bend as O
import ../spec/solve.bend as SV
import ./karith.bend as KA
import ./flaws.bend as FL
import ./qord.bend as QO
import ./qemb.bend as QE

def absurd(-A: Type, x: Empty) -> A:
  match x:

def sv_lt(o: Cmp, h: {SV.islt(o) == True{} : Bool}) -> {o == LT{} : Cmp}:
  match o:
    case LT{}:
      {==}
    case EQ{}:
      absurd({EQ{} == LT{} : Cmp}, KA.ft(h))
    case GT{}:
      absurd({GT{} == LT{} : Cmp}, KA.ft(h))

# m > 0: ofq(m) > 0
def q_pos(~F: O.OField, +m: S.Q, h: {SV.islt(S.Q.cmp(SV.qzero(), m)) == True{} : Bool}) -> O.lt(F, O.zero(F), O.ofq(~F, m)):
  (%QE.ofq_zero(~F) : O.lt(F, _, O.ofq(~F, m))
    QE.ofq_lt(~F, SV.qzero(), m, sv_lt(S.Q.cmp(SV.qzero(), m), h)))

def q_nn.go(~F: O.OField, o: Cmp, +m: S.Q, ho: {S.Q.cmp(m, SV.qzero()) == o : Cmp}, h: {SV.bnot(SV.islt(o)) == True{} : Bool}) -> O.le(~F, O.zero(F), O.ofq(~F, m)):
  match o:
    case LT{}:
      absurd(O.le(~F, O.zero(F), O.ofq(~F, m)), KA.ft(h))
    case EQ{}:
      Inr{Equal.sym(O.C(F), O.ofq(~F, m), O.zero(F), Equal.trans(O.C(F), O.ofq(~F, m), O.ofq(~F, SV.qzero()), O.zero(F), QE.ofq_eq(~F, m, SV.qzero(), QO.q_cmp_eq(m, SV.qzero(), ho)), QE.ofq_zero(~F)))}
    case GT{}:
      Inl{(%QE.ofq_zero(~F) : O.lt(F, _, O.ofq(~F, m))
        QE.ofq_lt(~F, SV.qzero(), m, QO.q_cmp_gt(m, SV.qzero(), ho)))}

# m >= 0: ofq(m) >= 0
def q_nn(~F: O.OField, +m: S.Q, h: {SV.bnot(SV.islt(S.Q.cmp(m, SV.qzero()))) == True{} : Bool}) -> O.le(~F, O.zero(F), O.ofq(~F, m)):
  q_nn.go(~F, S.Q.cmp(m, SV.qzero()), m, {==}, h)

def ofq_num0(~F: O.OField, k: S.Q, h: {S.Q.num(k) == S.Z0{} : S.Z}) -> {O.ofq(~F, k) == O.zero(F) : O.C(F)}:
  match k:
    case S.Q{n, +d}:
      %Equal.sym(S.Z, n, S.Z0{}, h) : {O.mul(F, O.ofz(~F, _), O.inv(F, O.ofp(~F, d))) == O.zero(F) : O.C(F)}
      FL.zero_mul(~F, O.inv(F, O.ofp(~F, d)))

def iszz_eq(z: S.Z, h: {SV.iszz(z) == True{} : Bool}) -> {z == S.Z0{} : S.Z}:
  match z:
    case S.Z0{}:
      {==}
    case S.Zpos{p}:
      absurd({S.Zpos{p} == S.Z0{} : S.Z}, KA.ft(h))
    case S.Zneg{p}:
      absurd({S.Zneg{p} == S.Z0{} : S.Z}, KA.ft(h))
