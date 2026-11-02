# bend-cad: the solver over the pass with the direction layer (PLAN-sk13b
# B5.2), beside lib/solve.bend until the switch. The same search, answer
# and verdict, over lib/dpass.bend's classes, pins, structure and system
# solved; the verdict also checks, over the box, that every segment in the
# nd of a drop of a Kept or Amber constraint has positive squared length
# (ndok), so that at every point of the box each dropped equation holds
# where the solved ones do (lib/dsolvepf.bend: solve_exists2).
#
# Untrusted in the sense of the rest of lib/: its properties are proven,
# nothing about it is assumed.

import Base
import ../spec/num.bend as S
import ../spec/ring.bend as E
import ../spec/sketch.bend as SK
import ../spec/solve.bend as SV
import ../spec/dir.bend as DR
import ./karith.bend as KA
import ./kinst.bend as KI
import ./plan.bend as PL
import ./struct.bend as ST
import ./numer.bend as NU
import ./dpass.bend as DPS
import ./solve.bend as SO

# The verdict
# -----------

# the live drops' nd segments are long over the box
def ndok(+sk: SK.Sketch, +x: SO.Out) -> Bool:
  PL.check_sides(~KI.dnum(), DR.ndsides(SV.ents(sk), SV.live_nd(SO.Out.cls(x))), SO.Out.gc(x), SO.Out.gr(x))

# sk-13a's verdict, with the nd sides first (a box too wide for them is
# retried anyway)
def final2(+sk: SK.Sketch, +g0: List<&2, S.D>, +x: SO.Out) -> Bool:
  KA.band(ndok(sk, x), SO.final(sk, g0, x))

# The precision loop (lib/solve.bend's, with final2)
# --------------------------------------------------

def accept2(m: NU.PR, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>) -> Bool:
  match m:
    case NU.POk{+x}:
      final2(sk, g0, SO.found(cls, pins, NU.POk{x}))
    case NU.PRetry{}:
      False{}
    case NU.PStop{}:
      False{}

def ploop2(ps: List<&2, Nat>, ok: Bool, cur: NU.PR, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel) -> SO.Run:
  match ps ok:
    case Nil{} ok:
      SO.Run{ok, cur}
    case Con{p, t} True{}:
      SO.Run{True{}, cur}
    case Con{+p, t} False{}:
      +nx = NU.plan(es, nv, skel, g0, p)
      ploop2(t, accept2(nx, sk, g0, cls, pins), nx, sk, g0, cls, pins, es, nv, skel)

def ploop2.start(ps: List<&2, Nat>, +sk: SK.Sketch, +g0: List<&2, S.D>, +cls: List<&2, SV.Class>, +pins: List<&2, Nat>, +es: List<&2, E.QExpr>, +nv: Nat, +skel: ST.Skel) -> SO.Run:
  match ps:
    case Nil{}:
      SO.Run{False{}, NU.PRetry{}}
    case Con{+p, t}:
      +nx = NU.plan(es, nv, skel, g0, p)
      ploop2(t, accept2(nx, sk, g0, cls, pins), nx, sk, g0, cls, pins, es, nv, skel)

# The structure, from the new pass
# --------------------------------

def cls_of2(+sk: SK.Sketch) -> List<&2, SV.Class>:
  DPS.classes2(sk)

def kept2(+sk: SK.Sketch) -> List<&2, E.QExpr>:
  SV.solved(sk, SV.reds(cls_of2(sk)), SV.dropped(cls_of2(sk)))

def skel_of2(+sk: SK.Sketch) -> ST.Skel:
  DPS.skel2(sk)

def pins_of2(+sk: SK.Sketch) -> List<&2, Nat>:
  DPS.pins2(sk)

# The solver
# ----------

def solve_lw2(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat, +w: Nat) -> SO.Out:
  SO.answer(cls_of2(sk), pins_of2(sk), ploop2.start(SO.precisions(l, w), sk, g0, cls_of2(sk), pins_of2(sk), kept2(sk), SO.nvars(sk), skel_of2(sk)))

def solve_l2(+sk: SK.Sketch, +g0: List<&2, S.D>, +l: Nat) -> SO.Out:
  solve_lw2(sk, g0, l, 7n)

def solve2(+sk: SK.Sketch, +g0: List<&2, S.D>) -> SO.Out:
  solve_l2(sk, g0, 0n)
