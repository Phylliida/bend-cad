# The commutative ring laws of the binary integers, each by one call to the
# pair tactic (lib/zpair.bend). Stated {target == source}, so a rewrite
# %law(..) : P turns the source form into the target form.

import Base
import ./zpair.bend as ZP
import ../spec/num.bend as S

# x + y = y + x
def add_comm(+x: S.Z, +y: S.Z) -> {S.Z.add(x, y) == S.Z.add(y, x) : S.Z}:
  ZP.zp_eq([x, y], ZP.ZPAdd{ZP.ZPVar{0n}, ZP.ZPVar{1n}}, ZP.ZPAdd{ZP.ZPVar{1n}, ZP.ZPVar{0n}}, {==}, {==})

# x + (y + z) = (x + y) + z
def add_assoc(+x: S.Z, +y: S.Z, +z: S.Z) -> {S.Z.add(x, S.Z.add(y, z)) == S.Z.add(S.Z.add(x, y), z) : S.Z}:
  ZP.zp_eq([x, y, z], ZP.ZPAdd{ZP.ZPVar{0n}, ZP.ZPAdd{ZP.ZPVar{1n}, ZP.ZPVar{2n}}}, ZP.ZPAdd{ZP.ZPAdd{ZP.ZPVar{0n}, ZP.ZPVar{1n}}, ZP.ZPVar{2n}}, {==}, {==})

# x + (y + z) = y + (x + z)
def add_swap(+x: S.Z, +y: S.Z, +z: S.Z) -> {S.Z.add(x, S.Z.add(y, z)) == S.Z.add(y, S.Z.add(x, z)) : S.Z}:
  ZP.zp_eq([x, y, z], ZP.ZPAdd{ZP.ZPVar{0n}, ZP.ZPAdd{ZP.ZPVar{1n}, ZP.ZPVar{2n}}}, ZP.ZPAdd{ZP.ZPVar{1n}, ZP.ZPAdd{ZP.ZPVar{0n}, ZP.ZPVar{2n}}}, {==}, {==})

# x = x + 0
def add_zero(+x: S.Z) -> {x == S.Z.add(x, S.Z0{}) : S.Z}:
  ZP.zp_eq([x], ZP.ZPVar{0n}, ZP.ZPAdd{ZP.ZPVar{0n}, ZP.ZPCst{S.Z0{}}}, {==}, {==})

# x * y = y * x
def mul_comm(+x: S.Z, +y: S.Z) -> {S.Z.mul(x, y) == S.Z.mul(y, x) : S.Z}:
  ZP.zp_eq([x, y], ZP.ZPMul{ZP.ZPVar{0n}, ZP.ZPVar{1n}}, ZP.ZPMul{ZP.ZPVar{1n}, ZP.ZPVar{0n}}, {==}, {==})

# x * (y * z) = (x * y) * z
def mul_assoc(+x: S.Z, +y: S.Z, +z: S.Z) -> {S.Z.mul(x, S.Z.mul(y, z)) == S.Z.mul(S.Z.mul(x, y), z) : S.Z}:
  ZP.zp_eq([x, y, z], ZP.ZPMul{ZP.ZPVar{0n}, ZP.ZPMul{ZP.ZPVar{1n}, ZP.ZPVar{2n}}}, ZP.ZPMul{ZP.ZPMul{ZP.ZPVar{0n}, ZP.ZPVar{1n}}, ZP.ZPVar{2n}}, {==}, {==})

# x * (y * z) = y * (x * z)
def mul_swap(+x: S.Z, +y: S.Z, +z: S.Z) -> {S.Z.mul(x, S.Z.mul(y, z)) == S.Z.mul(y, S.Z.mul(x, z)) : S.Z}:
  ZP.zp_eq([x, y, z], ZP.ZPMul{ZP.ZPVar{0n}, ZP.ZPMul{ZP.ZPVar{1n}, ZP.ZPVar{2n}}}, ZP.ZPMul{ZP.ZPVar{1n}, ZP.ZPMul{ZP.ZPVar{0n}, ZP.ZPVar{2n}}}, {==}, {==})

# (x * z) * (y * w) = (x * y) * (z * w)
def mul_shuffle(+x: S.Z, +y: S.Z, +z: S.Z, +w: S.Z) -> {S.Z.mul(S.Z.mul(x, z), S.Z.mul(y, w)) == S.Z.mul(S.Z.mul(x, y), S.Z.mul(z, w)) : S.Z}:
  ZP.zp_eq([x, y, z, w], ZP.ZPMul{ZP.ZPMul{ZP.ZPVar{0n}, ZP.ZPVar{2n}}, ZP.ZPMul{ZP.ZPVar{1n}, ZP.ZPVar{3n}}}, ZP.ZPMul{ZP.ZPMul{ZP.ZPVar{0n}, ZP.ZPVar{1n}}, ZP.ZPMul{ZP.ZPVar{2n}, ZP.ZPVar{3n}}}, {==}, {==})

# x = 1 * x
def one_mul(+x: S.Z) -> {x == S.Z.mul(S.Zpos{S.XH{}}, x) : S.Z}:
  ZP.zp_eq([x], ZP.ZPVar{0n}, ZP.ZPMul{ZP.ZPCst{S.Zpos{S.XH{}}}, ZP.ZPVar{0n}}, {==}, {==})

# x = x * 1
def mul_one(+x: S.Z) -> {x == S.Z.mul(x, S.Zpos{S.XH{}}) : S.Z}:
  ZP.zp_eq([x], ZP.ZPVar{0n}, ZP.ZPMul{ZP.ZPVar{0n}, ZP.ZPCst{S.Zpos{S.XH{}}}}, {==}, {==})

# 0 = x * 0
def mul_zero(+x: S.Z) -> {S.Z0{} == S.Z.mul(x, S.Z0{}) : S.Z}:
  ZP.zp_eq([x], ZP.ZPCst{S.Z0{}}, ZP.ZPMul{ZP.ZPVar{0n}, ZP.ZPCst{S.Z0{}}}, {==}, {==})

# x * z + y * z = (x + y) * z
def mul_add_r(+x: S.Z, +y: S.Z, +z: S.Z) -> {S.Z.add(S.Z.mul(x, z), S.Z.mul(y, z)) == S.Z.mul(S.Z.add(x, y), z) : S.Z}:
  ZP.zp_eq([x, y, z], ZP.ZPAdd{ZP.ZPMul{ZP.ZPVar{0n}, ZP.ZPVar{2n}}, ZP.ZPMul{ZP.ZPVar{1n}, ZP.ZPVar{2n}}}, ZP.ZPMul{ZP.ZPAdd{ZP.ZPVar{0n}, ZP.ZPVar{1n}}, ZP.ZPVar{2n}}, {==}, {==})

# x * y + x * z = x * (y + z)
def mul_add_l(+x: S.Z, +y: S.Z, +z: S.Z) -> {S.Z.add(S.Z.mul(x, y), S.Z.mul(x, z)) == S.Z.mul(x, S.Z.add(y, z)) : S.Z}:
  ZP.zp_eq([x, y, z], ZP.ZPAdd{ZP.ZPMul{ZP.ZPVar{0n}, ZP.ZPVar{1n}}, ZP.ZPMul{ZP.ZPVar{0n}, ZP.ZPVar{2n}}}, ZP.ZPMul{ZP.ZPVar{0n}, ZP.ZPAdd{ZP.ZPVar{1n}, ZP.ZPVar{2n}}}, {==}, {==})

# -x + -y = -(x + y)
def neg_add(+x: S.Z, +y: S.Z) -> {S.Z.add(S.Z.neg(x), S.Z.neg(y)) == S.Z.neg(S.Z.add(x, y)) : S.Z}:
  ZP.zp_eq([x, y], ZP.ZPAdd{ZP.ZPNeg{ZP.ZPVar{0n}}, ZP.ZPNeg{ZP.ZPVar{1n}}}, ZP.ZPNeg{ZP.ZPAdd{ZP.ZPVar{0n}, ZP.ZPVar{1n}}}, {==}, {==})

# -x * y = -(x * y)
def neg_mul(+x: S.Z, +y: S.Z) -> {S.Z.mul(S.Z.neg(x), y) == S.Z.neg(S.Z.mul(x, y)) : S.Z}:
  ZP.zp_eq([x, y], ZP.ZPMul{ZP.ZPNeg{ZP.ZPVar{0n}}, ZP.ZPVar{1n}}, ZP.ZPNeg{ZP.ZPMul{ZP.ZPVar{0n}, ZP.ZPVar{1n}}}, {==}, {==})
