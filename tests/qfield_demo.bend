# The canonical rationals compute, and equal rationals are one element:
# 2/4 and 1/2 are the same Stern-Brocot word, and 1/2 + 1/3 is 5/6.

import Base
import ../spec/num.bend as S
import ../lib/qfield.bend as QF

def half() -> QF.QC:
  QF.of_q(S.Q{S.Zpos{S.XH{}}, S.XO{S.XH{}}})

def third() -> QF.QC:
  QF.of_q(S.Q{S.Zpos{S.XH{}}, S.XI{S.XH{}}})

# 2/4 = 1/2, as Bend's own equality
def same() -> {QF.of_q(S.Q{S.Zpos{S.XO{S.XH{}}}, S.XO{S.XO{S.XH{}}}}) == half() : QF.QC}:
  {==}

# 1/2 + 1/3 = 5/6
def sum() -> {QF.add(half(), third()) == QF.of_q(S.Q{S.Zpos{S.XI{S.XO{S.XH{}}}}, S.XO{S.XI{S.XH{}}}}) : QF.QC}:
  {==}

# 1/2 - 1/2 = 0
def cancel() -> {QF.add(half(), QF.neg(half())) == QF.QZ{} : QF.QC}:
  {==}

# 1/3 < 1/2
def order() -> QF.lt(third(), half()):
  {==}

def main() -> Nat:
  0n
