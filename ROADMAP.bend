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

# Block certificates (sk-05, DESIGN §8.3; reviewed by an independent audit
# and Danielle; blocks number their own variables)
# ------------------------------------------------------------------
# A certificate is checked in the computing numbers K and its claim holds in
# every ordered field F that K maps into (H: a ring map with sound
# comparisons). For every z in the parameters' box, write N(y) =
# y - Y f(y; z) for the certificate's Newton map and B for the box
# |y_i - ỹ_i| <= r_i, for y with as many entries as ỹ (r_i = 0 past the
# last radius). Then 0 <= q < 1, B contains its center, N maps B into itself
# and contracts it by q (in the r-weighted infinity norm), a fixed point of
# N is a zero of f, and B holds at most one zero. In a complete ordered
# field these give exactly one zero of the block in B (Banach, proven in
# Bend; Q18).
#
# The checker is lib/cert.bend (computational part written; it accepts a
# real circle-circle certificate over the dyadics and rejects six bad ones,
# proto/cc_run.bend). The laws move to LAWS.bend with their proofs and a
# gated positive test (check == True on a real block).

# LAW: the contraction factor is in [0, 1)
law cert_factor:
  for ~K: N.Num
  for ~F: O.OField
  for ~H: N.Emb<K, F>
  for +b: C.Block
  for +c: C.Cert<K>
  for  ok: {CK.check(~K, b, c) == True{} : Bool}
  M.Both(O.le(~F, O.zero(F), C.factor(~K, ~F, ~H, c)), O.lt(F, C.factor(~K, ~F, ~H, c), O.one(F)))

# LAW: the box contains its center (so it is not empty)
law cert_center:
  for ~K: N.Num
  for ~F: O.OField
  for ~H: N.Emb<K, F>
  for +b: C.Block
  for +c: C.Cert<K>
  for  ok: {CK.check(~K, b, c) == True{} : Bool}
  C.ball(~K, ~F, ~H, c, C.center(~K, ~F, ~H, c))

# LAW: the Newton map sends the box into itself
law cert_self:
  for ~K: N.Num
  for ~F: O.OField
  for ~H: N.Emb<K, F>
  for +b: C.Block
  for +c: C.Cert<K>
  for  ok: {CK.check(~K, b, c) == True{} : Bool}
  for +z: M.Vec(~F)
  for  hz: C.pinned(~K, ~F, ~H, c, z)
  for +y: M.Vec(~F)
  for  hy: C.ball(~K, ~F, ~H, c, y)
  C.ball(~K, ~F, ~H, c, C.newton(~K, ~F, ~H, b, c, z, y))

# LAW: the Newton map contracts the box by q: points within s radii of
# each other go to points within q s radii (s >= 0: with s < 0 and two
# empty lists the hypothesis holds vacuously and the conclusion is false)
law cert_contract:
  for ~K: N.Num
  for ~F: O.OField
  for ~H: N.Emb<K, F>
  for +b: C.Block
  for +c: C.Cert<K>
  for  ok: {CK.check(~K, b, c) == True{} : Bool}
  for +z: M.Vec(~F)
  for  hz: C.pinned(~K, ~F, ~H, c, z)
  for +y1: M.Vec(~F)
  for  h1: C.ball(~K, ~F, ~H, c, y1)
  for +y2: M.Vec(~F)
  for  h2: C.ball(~K, ~F, ~H, c, y2)
  for +s: O.C(F)
  for  hs0: O.le(~F, O.zero(F), s)
  for  hs: C.near(~K, ~F, ~H, c, s, y1, y2)
  C.near(~K, ~F, ~H, c, O.mul(F, C.factor(~K, ~F, ~H, c), s), C.newton(~K, ~F, ~H, b, c, z, y1), C.newton(~K, ~F, ~H, b, c, z, y2))

# LAW: a fixed point of the Newton map is a zero of the block
law cert_fix:
  for ~K: N.Num
  for ~F: O.OField
  for ~H: N.Emb<K, F>
  for +b: C.Block
  for +c: C.Cert<K>
  for  ok: {CK.check(~K, b, c) == True{} : Bool}
  for +z: M.Vec(~F)
  for +y: M.Vec(~F)
  for  hy: C.ball(~K, ~F, ~H, c, y)
  for  hf: M.vbnd(~F, C.vsub(~F, C.newton(~K, ~F, ~H, b, c, z, y), y), O.zero(F))
  M.vbnd(~F, C.bfun(~F, b, y, z), O.zero(F))

# LAW: the box holds at most one zero of the block
law cert_unique:
  for ~K: N.Num
  for ~F: O.OField
  for ~H: N.Emb<K, F>
  for +b: C.Block
  for +c: C.Cert<K>
  for  ok: {CK.check(~K, b, c) == True{} : Bool}
  for +z: M.Vec(~F)
  for  hz: C.pinned(~K, ~F, ~H, c, z)
  for +y1: M.Vec(~F)
  for  h1: C.ball(~K, ~F, ~H, c, y1)
  for  z1: M.vbnd(~F, C.bfun(~F, b, y1, z), O.zero(F))
  for +y2: M.Vec(~F)
  for  h2: C.ball(~K, ~F, ~H, c, y2)
  for  z2: M.vbnd(~F, C.bfun(~F, b, y2, z), O.zero(F))
  M.vbnd(~F, C.vsub(~F, y1, y2), O.zero(F))
