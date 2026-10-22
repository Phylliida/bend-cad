# bend-cad: the checker's computing numbers (spec/knum.bend) at word
# dyadics, so that the generic checker (plan, cert, kball) runs on words.
# Its map from KI.dnum() is WD.ofd, which commutes with every operation
# (lib/wnumpf.bend). The base 2^(1 + lp) is a parameter (bp = 2^(1+lp) - 1).
# wops: the proposer's other operations (lib/pops.bend) at words: rounding
# by the word twins of lib/wsigpf.bend, the rare ones through S.D.

import Base
import ../spec/num.bend as S
import ../spec/mat.bend as M
import ../spec/knum.bend as N
import ./kinst.bend as KI
import ../rt/wdyad.bend as RD
import ./numer.bend as NU
import ./pops.bend as PO

def wofq.m(+lp: Nat, m: Maybe<&2, S.D>) -> Maybe<&2, RD.WD>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{RD.WD.ofd(lp, x)}

def wnum(+bp: Nat, +lp: Nat) -> N.Num:
  N.Num{RD.WD, RD.WD.ofd(lp, M.d0()), RD.WD.ofd(lp, M.d1()), a => b => RD.WD.add(bp, lp, a, b), a => b => RD.WD.mul(bp, a, b), a => RD.WD.neg(a), a => b => RD.WD.cmp(bp, lp, a, b), q => wofq.m(lp, KI.dofq(q))}

def wops(+bp: Nat, +lp: Nat) -> PO.POps<wnum(bp, lp)>:
  PO.POps{x => RD.WD.ofd(lp, x), x => RD.WD.tod(lp, x), x => b => RD.WD.sig(bp, lp, x, b), x => p => RD.WD.round(bp, lp, x, p), w => a => b => RD.WD.ofd(lp, NU.dsdiv(w, RD.WD.tod(lp, a), RD.WD.tod(lp, b))), x => b => RD.WD.ofd(lp, NU.dsigup(RD.WD.tod(lp, x), b))}
