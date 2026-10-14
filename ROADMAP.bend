# bend-cad: laws planned but not proven yet (open claims). Not imported by
# PROOF.bend, so the gate stays meaningful. Checking this file reports its
# open laws as TODOs; that is expected.

import Base
import ./LAWS.bend as Laws
import ./spec/field.bend as O
import ./spec/mat.bend as M
import ./spec/knum.bend as N
import ./spec/cert.bend as C
import ./lib/cert.bend as CK

# Block certificates (sk-05, DESIGN §8.3; draft for Danielle's review)
# ------------------------------------------------------------------
# A certificate is checked in the computing numbers K and its claim holds in
# every ordered field F that K maps into (H: a ring map with sound
# comparisons). For every x whose parameters lie in their balls, write
# N(y) = y - Y f(y; x) for the certificate's Newton map and B for the ball
# ||y - ỹ|| <= r. Then 0 <= q < 1, N maps B into itself, N contracts B by
# q, and a fixed point of N is a zero of f. In ℝ these give exactly one
# zero of the block in B for each such x (Banach; DESIGN §8.4).

# LAW: the contraction factor is in [0, 1)
law cert_factor:
  for ~K: N.Num
  for ~F: O.OField
  for ~H: N.Emb<K, F>
  for +b: C.Block
  for +c: C.Cert<K>
  for  ok: {CK.check(~K, b, c) == True{} : Bool}
  M.Both(O.le(~F, O.zero(F), C.factor(~K, ~F, ~H, c)), O.lt(F, C.factor(~K, ~F, ~H, c), O.one(F)))

# LAW: the Newton map sends the ball into itself
law cert_self:
  for ~K: N.Num
  for ~F: O.OField
  for ~H: N.Emb<K, F>
  for +b: C.Block
  for +c: C.Cert<K>
  for  ok: {CK.check(~K, b, c) == True{} : Bool}
  for +x: M.Vec(~F)
  for  hx: C.pinned(~K, ~F, ~H, b, c, x)
  for +y: M.Vec(~F)
  for  hy: C.ball(~K, ~F, ~H, c, y)
  C.ball(~K, ~F, ~H, c, C.newton(~K, ~F, ~H, b, c, x, y))

# LAW: the Newton map contracts the ball by q
law cert_contract:
  for ~K: N.Num
  for ~F: O.OField
  for ~H: N.Emb<K, F>
  for +b: C.Block
  for +c: C.Cert<K>
  for  ok: {CK.check(~K, b, c) == True{} : Bool}
  for +x: M.Vec(~F)
  for  hx: C.pinned(~K, ~F, ~H, b, c, x)
  for +y1: M.Vec(~F)
  for  h1: C.ball(~K, ~F, ~H, c, y1)
  for +y2: M.Vec(~F)
  for  h2: C.ball(~K, ~F, ~H, c, y2)
  for +s: O.C(F)
  for  hs: M.vbnd(~F, C.vsub(~F, y1, y2), s)
  M.vbnd(~F, C.vsub(~F, C.newton(~K, ~F, ~H, b, c, x, y1), C.newton(~K, ~F, ~H, b, c, x, y2)), O.mul(F, C.factor(~K, ~F, ~H, c), s))

# LAW: a fixed point of the Newton map is a zero of the block
law cert_fix:
  for ~K: N.Num
  for ~F: O.OField
  for ~H: N.Emb<K, F>
  for +b: C.Block
  for +c: C.Cert<K>
  for  ok: {CK.check(~K, b, c) == True{} : Bool}
  for +x: M.Vec(~F)
  for +y: M.Vec(~F)
  for  hf: M.vbnd(~F, C.vsub(~F, C.newton(~K, ~F, ~H, b, c, x, y), y), O.zero(F))
  M.vbnd(~F, C.bfun(~F, b, x, y), O.zero(F))
