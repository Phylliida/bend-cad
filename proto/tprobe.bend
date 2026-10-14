# sk-05b probe (untrusted, not gated): function-valued template parameters
# (~f: @i: Nat -> P(i)) are reusable, may capture local variables, and are
# checked at the instance (a planted wrong family was refused). Only
# leading binders take ~, and a template cannot be matched on.

import Base
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../lib/ford.bend as FO

# a reusable family of facts passed as a template
def twice(~F: O.OField, ~P: Nat -> Data, ~f: @i: Nat -> P(i)) -> M.Both(P(0n), P(1n)):
  (f(0n), f(1n))

def build(~F: O.OField, ~P: Nat -> Data, ~f: @i: Nat -> P(i), n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n++k:
      Con{k, build(~F, ~P, ~f, k)}

def nnz(~F: O.OField, i: Nat) -> Data:
  O.le(~F, O.zero(F), O.zero(F))

def nnzf(~F: O.OField, i: Nat) -> nnz(~F, i):
  FO.le_refl(~F, O.zero(F))

def use(~F: O.OField) -> M.Both(nnz(~F, 0n), nnz(~F, 1n)):
  twice(~F, ~(i => nnz(~F, i)), ~(i => nnzf(~F, i)))

def nnx(~F: O.OField, +x: O.C(F), i: Nat) -> Data:
  O.le(~F, x, x)

def nnxf(~F: O.OField, +x: O.C(F), i: Nat) -> nnx(~F, x, i):
  FO.le_refl(~F, x)

def usex(~F: O.OField, +x: O.C(F)) -> M.Both(nnx(~F, x, 0n), nnx(~F, x, 1n)):
  twice(~F, ~(i => nnx(~F, x, i)), ~(i => nnxf(~F, x, i)))

def seqf(~F: O.OField, ~s: Nat -> O.C(F), ~h: @i: Nat -> O.le(~F, s(i), s(i))) -> M.Both(O.le(~F, s(0n), s(0n)), O.le(~F, s(3n), s(3n))):
  (h(0n), h(3n))

def useseq(~F: O.OField, +x: O.C(F), +y: O.C(F)) -> M.Both(O.le(~F, O.add(F, x, y), O.add(F, x, y)), O.le(~F, O.add(F, x, y), O.add(F, x, y))):
  seqf(~F, ~(t => O.add(F, x, y)), ~(t => FO.le_refl(~F, O.add(F, x, y))))
