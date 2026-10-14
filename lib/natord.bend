# Order on Base's Nat, and Euclid's division (Nat.div / Nat.mod) by a base
# 1 + bp. The base stays a variable: a large literal such as 65536n would be
# unfolded to unary by the checker.
#
# SB.Le(a, b) is a <= b, witnessed by the gap k with a + k = b.

import Base
import ./nat.bend as N
import ./natring.bend as NR
import ../spec/big.bend as SB

def le_refl(+a: Nat) -> SB.Le(a, a):
  (0n, Equal.sym(Nat, a, Nat.add(a, 0n), N.add_zero(a)))

# Division
# --------
# Base's Nat.divmod(s, 1 + bp) runs Nat.divmod.go(s, bp, 0, 0): r counts up
# and m counts down, with r + m = bp throughout.

def dm_h0(+r: Nat, -bp: Nat, h: {Nat.add(r, 0n) == bp : Nat}) -> {r == bp : Nat}:
  %h : {r == _ : Nat}
  N.add_zero(r)

def dm_h1(+r: Nat, +mp: Nat, -bp: Nat, h: {Nat.add(r, 1n+mp) == bp : Nat}) -> {1n+Nat.add(r, mp) == bp : Nat}:
  %h : {1n+Nat.add(r, mp) == _ : Nat}
  N.add_succ(r, mp)

def dm_go(n: Nat, m: Nat, +d: Nat, +r: Nat, +bp: Nat, +h: {Nat.add(r, m) == bp : Nat})
  -> {Nat.add(Nat.add(r, Nat.mul(d, 1n+bp)), n) == Nat.add(Nat.mod.fin(Nat.divmod.go(n, m, d, r)), Nat.mul(Nat.div.fin(Nat.divmod.go(n, m, d, r)), 1n+bp)) : Nat}:
  match n:
    case 0n:
      %N.add_zero(Nat.add(r, Nat.mul(d, 1n+bp))) : {_ == Nat.add(r, Nat.mul(d, 1n+bp)) : Nat}
      {==}
    case 1n+np:
      match m:
        case 0n:
          %dm_go(np, r, 1n+d, 0n, bp, dm_h0(r, bp, h)) : {Nat.add(Nat.add(r, Nat.mul(d, 1n+bp)), 1n+np) == _ : Nat}
          %dm_h0(r, bp, h) : {Nat.add(Nat.add(r, Nat.mul(d, 1n+bp)), 1n+np) == 1n+Nat.add(Nat.add(_, Nat.mul(d, 1n+bp)), np) : Nat}
          %N.add_succ(Nat.add(r, Nat.mul(d, 1n+bp)), np) : {_ == 1n+Nat.add(Nat.add(r, Nat.mul(d, 1n+bp)), np) : Nat}
          {==}
        case 1n++mp:
          %dm_go(np, mp, d, 1n+r, bp, dm_h1(r, mp, bp, h)) : {Nat.add(Nat.add(r, Nat.mul(d, 1n+bp)), 1n+np) == _ : Nat}
          %N.add_succ(Nat.add(r, Nat.mul(d, 1n+bp)), np) : {_ == 1n+Nat.add(Nat.add(r, Nat.mul(d, 1n+bp)), np) : Nat}
          {==}

def dm_go_le(n: Nat, m: Nat, -d: Nat, +r: Nat, +bp: Nat, h: {Nat.add(r, m) == bp : Nat}) -> SB.Le(Nat.mod.fin(Nat.divmod.go(n, m, d, r)), bp):
  match n:
    case 0n:
      (m, h)
    case 1n+np:
      match m:
        case 0n:
          dm_go_le(np, r, 1n+d, 0n, bp, dm_h0(r, bp, h))
        case 1n++mp:
          dm_go_le(np, mp, d, 1n+r, bp, dm_h1(r, mp, bp, h))

# s = (s mod B) + (s div B) * B, for B = 1 + bp
def divmod_eq(+s: Nat, +bp: Nat) -> {s == Nat.add(Nat.mod(s, 1n+bp), Nat.mul(Nat.div(s, 1n+bp), 1n+bp)) : Nat}:
  dm_go(s, bp, 0n, 0n, bp, {==})

# s mod B <= bp
def mod_le(+s: Nat, +bp: Nat) -> SB.Le(Nat.mod(s, 1n+bp), bp):
  dm_go_le(s, bp, 0n, 0n, bp, {==})
