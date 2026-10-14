# The checker's computing numbers: the dyadic and rational instances build
# (Bend checks each map's laws), and which rationals the dyadics hold
# computes: 3/4 is held as 3/2^2, 1/10 is not.

import Base
import ../spec/num.bend as S
import ../spec/field.bend as O
import ../spec/knum.bend as N
import ../lib/kinst.bend as KI

def dyadic_map(~F: O.OField) -> N.Emb<KI.dnum(), F>:
  KI.demb(~F)

def rational_map(~F: O.OField) -> N.Emb<KI.qnum(), F>:
  KI.qemb(~F)

def three_quarters_ok() -> {KI.dofq(S.Q{S.Zpos{S.XI{S.XH{}}}, S.XO{S.XO{S.XH{}}}}) == Some{S.D{S.Zpos{S.XI{S.XH{}}}, 2n}} : Maybe<&2, S.D>}:
  {==}

def tenth_ok() -> {KI.dofq(S.Q{S.Zpos{S.XH{}}, S.XO{S.XI{S.XO{S.XH{}}}}}) == None{} : Maybe<&2, S.D>}:
  {==}
