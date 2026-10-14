# The verified proposer's stages 2-3 end to end on the depth-N chain of
# tools/gen_plan_chain.py (proto/plan_chain.txt): only the sketch and a
# drawing (the solution rounded to whole nm) are read from the file; the
# structure (lib/struct.bend), Newton, Y and the radii (lib/numer.bend)
# are computed here, and the plan goes through lib/plan.bend's checker.
# Native: bin/bend proto/solve_chain_run.bend -o <out>; <out> --threads 1

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../lib/kinst.bend as KI
import ../lib/plan.bend as PL
import ../lib/struct.bend as ST
import ../lib/numer.bend as NU
import ./block.bend as B
import ../lib/qreduce.bend as QRD
import ./plan_chain_run.bend as PR

# the drawing: each center rounded to a whole nm
def draw(xs: List<&2, S.D>) -> List<&2, S.D>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{+x, t}:
      Con{NU.qround(S.D.toq(x), 0n), draw(t)}

def log2r(xs: List<&2, S.D>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{+x, Nil{}}:
      "last radius exponent " ++ Nat.show(S.D.exp(x)) ++ ", mantissa bits " ++ Nat.show(QRD.size(NU.zpos(S.D.man(x))))
    case Con{x, t}:
      log2r(t)

def report(+es: List<&2, E.QExpr>, +p: Nat, m: NU.PR) -> String:
  match m:
    case NU.PRetry{}:
      "P " ++ Nat.show(p) ++ ": no plan (retry)"
    case NU.PStop{}:
      "P " ++ Nat.show(p) ++ ": no plan (stop)"
    case NU.POk{NU.NP{plan, +gc, +gr}}:
      "P " ++ Nat.show(p) ++ ": plan checks " ++ Bool.show(PL.check(~KI.dnum(), es, gc, gr, plan)) ++ "; " ++ log2r(gr)

def go.es(+es: List<&2, E.QExpr>, +nv: Nat, +gc: List<&2, S.D>, +p: Nat) -> String:
  report(es, p, NU.plan(es, nv, ST.structure(es, nv), draw(gc), p))

def go(+n: Nat, +gc: List<&2, S.D>, rs: List<&2, String>, +p: Nat) -> String:
  go.es(SK.Sketch.eqs(PR.sketch(n, rs)), Nat.mul(2n, 2n+n), gc, p)

def run(+p: Nat, ls: List<&2, String>) -> String:
  match ls:
    case Con{meta, Con{gc, Con{gr, Con{rs, bl}}}}:
      go(B.tok.nat(PR.first(B.toks(meta))), PR.ds(B.toks(gc)), B.toks(rs), p)
    case _:
      "bad file"

def runs(+ls: List<&2, String>) -> String:
  run(64n, ls) ++ "\n" ++ run(96n, ls) ++ "\n" ++ run(128n, ls)

def main() -> IO(Unit):
  do IO<Unit>:
    s : String <- B.slurp("proto/plan_chain.txt")
    IO.print(runs(PR.nonempty(String.lines(s))))
