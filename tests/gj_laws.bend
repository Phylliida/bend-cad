# bend-cad: the linear algebra under solve_complete (DESIGN §10.4, C1),
# restated here so the gate checks lib/gjpf.bend until the completeness
# proof imports it. In every ordered field:
# - an injective square matrix (n rows of n entries) has a two-sided
#   inverse with n rows;
# - so does a square matrix with a two-sided inverse of any shape (the
#   kind spec/deriv.bend's Regular gives);
# - if [[A, 0], [C, D]] is invertible, so are A and D.

import Base
import ../spec/field.bend as O
import ../spec/mat.bend as M
import ../spec/deriv.bend as DV
import ../lib/gjpf.bend as GJ

def injective_invertible(~F: O.OField, +a: M.Mat(~F), +n: Nat, +hA: {GJ.nrows(~F, a) == n : Nat}, hw: GJ.All(~(j => GJ.roww(~F, a, n, j)), n), inj: @w: M.Vec(~F) -> {M.len(~F, w) == n : Nat} -> {M.matvec(~F, a, w) == GJ.zeros(~F, n) : M.Vec(~F)} -> {w == GJ.zeros(~F, n) : M.Vec(~F)}) -> GJ.InvN(~F, a, n):
  GJ.inv_of_inj(~F, a, n, hA, hw, inj)

def inverse_squares(~F: O.OField, +a: M.Mat(~F), +z: M.Mat(~F), +n: Nat, +hA: {GJ.nrows(~F, a) == n : Nat}, hw: GJ.All(~(j => GJ.roww(~F, a, n, j)), n), hinv: DV.Inverse(~F, a, z, n)) -> GJ.InvN(~F, a, n):
  GJ.invn_of_inverse(~F, a, z, n, hA, hw, hinv)

def block_triangular(~F: O.OField, +a: M.Mat(~F), +c: M.Mat(~F), +d: M.Mat(~F), +n1: Nat, +n2: Nat, +sa: {GJ.nrows(~F, a) == n1 : Nat}, +ra: GJ.rl(~F, a, n1), +sc: {GJ.nrows(~F, c) == n2 : Nat}, +rc: GJ.rl(~F, c, n1), +sd: {GJ.nrows(~F, d) == n2 : Nat}, +rd: GJ.rl(~F, d, n2), +hm: GJ.InvN(~F, GJ.bm(~F, a, c, d, n1, n2), Nat.add(n1, n2))) -> M.Both(GJ.InvN(~F, a, n1), GJ.InvN(~F, d, n2)):
  GJ.block_inv(~F, a, c, d, n1, n2, sa, ra, sc, rc, sd, rd, hm)
