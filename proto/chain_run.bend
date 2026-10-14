import Base
import ../spec/num.bend as S
import ../spec/cert.bend as C
import ../lib/kinst.bend as KI
import ../lib/plan.bend as PL
import ../tests/chain_data.bend as D

def blocks(p: PL.Plan<KI.dnum()>) -> List<&2, PL.PBlock<KI.dnum()>>:
  match p:
    case PL.Plan{np, bs}:
      bs

def nth(bs: List<&2, PL.PBlock<KI.dnum()>>, i: Nat) -> PL.PBlock<KI.dnum()>:
  match bs i:
    case Nil{} i:
      PL.PBlock{0n, [], C.Cert{[], [], S.D{S.Z0{}, 0n}, [], [], []}}
    case Con{h, t} 0n:
      h
    case Con{h, t} 1n+j:
      nth(t, j)

def b0() -> PL.PBlock<KI.dnum()>:
  nth(blocks(D.ch_plan()), 0n)

def b1() -> PL.PBlock<KI.dnum()>:
  nth(blocks(D.ch_plan()), 1n)

def cert(b: PL.PBlock<KI.dnum()>) -> C.Cert<KI.dnum()>:
  match b:
    case PL.PBlock{n, pars, c}:
      c

def chk(p: PL.Plan<KI.dnum()>) -> Bool:
  PL.check(~KI.dnum(), D.ch_eqs(), D.ch_gc(), D.ch_gr(), p)

def main() -> List<Bool>:
  [chk(D.ch_plan()),
   chk(PL.Plan{4n, [b0()]}),
   chk(PL.Plan{4n, [b1(), b0()]}),
   chk(PL.Plan{3n, [b0(), b1()]}),
   chk(PL.Plan{4n, [b0(), PL.PBlock{2n, [0n, 1n], cert(b1())}]}),
   chk(PL.Plan{4n, [b0(), PL.PBlock{2n, [0n, 1n, 2n, 3n], cert(b1())}]}),
   chk(PL.Plan{4n, [b0(), PL.PBlock{2n, [0n, 1n, 4n, 6n], cert(b1())}]})]
