# Diagnostic (untrusted): lib/simplex.bend on small hand-made systems.
# Native: bin/bend proto/simplex_test.bend -o proto/simplex_test.

import Base
import ../spec/num.bend as S
import ../lib/simplex.bend as SX

def zs(z: S.Z) -> String:
  match z:
    case S.Z0{}:
      "0"
    case S.Zpos{p}:
      Nat.show(S.Pos.nat(p))
    case S.Zneg{p}:
      "-" ++ Nat.show(S.Pos.nat(p))

def vs(u: List<&2, S.Z>) -> String:
  match u:
    case Nil{}:
      ""
    case Con{x, t}:
      zs(x) ++ " " ++ vs(t)

def rs(u: List<&2, SX.Rw>) -> String:
  match u:
    case Nil{}:
      ""
    case Con{SX.Rw{d, x}, t}:
      Nat.show(S.Pos.nat(d)) ++ "[" ++ vs(x) ++ "] " ++ rs(t)

def show(r: SX.Run) -> String:
  match r:
    case SX.Go{t}:
      "GO (out of steps)"
    case SX.Sat{+t}:
      "SAT " ++ rs(SX.Tab.rows(t))
    case SX.Unsat{+t, i}:
      "UNSAT row " ++ Nat.show(i) ++ " " ++ rs(SX.Tab.rows(t))

def p1() -> S.Z:
  S.Zpos{S.XH{}}

def m1() -> S.Z:
  S.Zneg{S.XH{}}

def p2() -> S.Z:
  S.Zpos{S.XO{S.XH{}}}

def m2() -> S.Z:
  S.Zneg{S.XO{S.XH{}}}

def z0() -> S.Z:
  S.Z0{}

# r > 0
def t1() -> SX.LP:
  SX.LP{[SX.Ineq{[p1()], z0(), True{}}], 1n}

# r > 0, -r >= 0
def t2() -> SX.LP:
  SX.LP{[SX.Ineq{[p1()], z0(), True{}}, SX.Ineq{[m1()], z0(), False{}}], 1n}

# x - 1 >= 0, y - 1 >= 0, 1 - x - y >= 0
def t3() -> SX.LP:
  SX.LP{[SX.Ineq{[p1(), z0()], m1(), False{}}, SX.Ineq{[z0(), p1()], m1(), False{}}, SX.Ineq{[m1(), m1()], p1(), False{}}], 2n}

# x - y > 0, y - x > 0
def t4() -> SX.LP:
  SX.LP{[SX.Ineq{[p1(), m1()], z0(), True{}}, SX.Ineq{[m1(), p1()], z0(), True{}}], 2n}

# x >= 0, y >= 0, x + y - 2 >= 0
def t5() -> SX.LP:
  SX.LP{[SX.Ineq{[p1(), z0()], z0(), False{}}, SX.Ineq{[z0(), p1()], z0(), False{}}, SX.Ineq{[p1(), p1()], m2(), False{}}], 2n}

# -1 >= 0
def t6() -> SX.LP:
  SX.LP{[SX.Ineq{[], m1(), False{}}], 0n}

# x - y >= 0, y - x >= 0, x + y - 2 > 0, 2 - x > 0 (sat: x = y in (1, 2))
def t7() -> SX.LP:
  SX.LP{[SX.Ineq{[p1(), m1()], z0(), False{}}, SX.Ineq{[m1(), p1()], z0(), False{}}, SX.Ineq{[p1(), p1()], m2(), True{}}, SX.Ineq{[m1(), z0()], p2(), True{}}], 2n}

# as t7 with 1 - x >= 0 (unsat)
def t8() -> SX.LP:
  SX.LP{[SX.Ineq{[p1(), m1()], z0(), False{}}, SX.Ineq{[m1(), p1()], z0(), False{}}, SX.Ineq{[p1(), p1()], m2(), True{}}, SX.Ineq{[m1(), z0()], p1(), False{}}], 2n}

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print("t1 " ++ show(SX.solve(t1())))
    IO.print("t2 " ++ show(SX.solve(t2())))
    IO.print("t3 " ++ show(SX.solve(t3())))
    IO.print("t4 " ++ show(SX.solve(t4())))
    IO.print("t5 " ++ show(SX.solve(t5())))
    IO.print("t6 " ++ show(SX.solve(t6())))
    IO.print("t7 " ++ show(SX.solve(t7())))
    IO.print("t8 " ++ show(SX.solve(t8())))
