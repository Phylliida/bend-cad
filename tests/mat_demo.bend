# Dyadic vectors and matrices compute exactly: closed facts check by {==},
# as a certificate checker's would. A = [[1, -2], [3, 1/2]], v = [1, -1].

import Base
import ../spec/num.bend as S
import ../spec/mat.bend as M

def dy(m: S.Z, e: Nat) -> S.D:
  S.D{m, e}

def one() -> S.Z:
  S.Zpos{S.XH{}}

def two() -> S.Z:
  S.Zpos{S.XO{S.XH{}}}

def three() -> S.Z:
  S.Zpos{S.XI{S.XH{}}}

def seven() -> S.Z:
  S.Zpos{S.XI{S.XI{S.XH{}}}}

def a() -> M.DMat():
  [[dy(one(), 0n), dy(S.Z.neg(two()), 0n)], [dy(three(), 0n), dy(one(), 1n)]]

def v() -> M.DVec():
  [dy(one(), 0n), dy(S.Z.neg(one()), 0n)]

# ||A|| = max(1 + 2, 3 + 1/2) = 7/2
def norm_ok() -> S.Q.eq(S.D.toq(M.dnorm(a())), S.Q{seven(), S.XO{S.XH{}}}):
  {==}

# A v = [3, 5/2], of norm 3
def matvec_ok() -> S.Q.eq(S.D.toq(M.dvnorm(M.dmatvec(a(), v()))), S.Q{three(), S.XH{}}):
  {==}

# A A = [[-5, -3], [9/2, -23/4]], so I - A A = [[6, 3], [-9/2, 27/4]], with
# row sums 9 and 45/4
def prod_ok() -> S.Q.eq(S.D.toq(M.dnorm(M.dmadd(M.dident(2n), M.dmneg(M.dmatmul(a(), a()))))), S.Q{S.Zpos{S.XI{S.XO{S.XI{S.XI{S.XO{S.XH{}}}}}}}, S.XO{S.XO{S.XH{}}}}):
  {==}

def main() -> Nat:
  0n
