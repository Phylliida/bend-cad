# runs the block certificate on the proto/block.* files written by gen_block.py
import Base
import ./int.bend as I
import ./block.bend as B

def run(meta: List<&2, Nat>, edges: List<&2, B.Edge>, x0: List<&2, I.Int>, yt: List<&2, List<&2, I.Int>>, cols: List<&2, List<&2, B.JEnt>>) -> String:
  match meta:
    case Con{+m, Con{+P, _}}:
      B.Out.show(B.certify(edges, x0, yt, cols, m, P, 10n), P)
    case _:
      "bad meta"

def main() -> IO(Unit):
  do IO<Unit>:
    meta : String <- B.slurp("proto/block.meta")
    es : String <- B.slurp("proto/block.edges")
    x0 : String <- B.slurp("proto/block.x0")
    yt : String <- B.slurp("proto/block.yt")
    jc : String <- B.slurp("proto/block.jcols")
    IO.print(run(B.nats(B.toks(meta)), B.edges.of(String.lines(es)), B.ints(B.toks(x0)), B.rows(String.lines(yt)), B.jcols.of(String.lines(jc))))
