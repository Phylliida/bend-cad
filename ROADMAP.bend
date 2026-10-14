# bend-cad: laws planned but not proven yet (open claims). Not imported by
# PROOF.bend, so the gate stays meaningful. Checking this file reports its
# open laws as TODOs; that is expected.

import Base
import ./LAWS.bend as Laws
import ./spec/field.bend as O
import ./spec/mat.bend as M
import ./spec/knum.bend as N
import ./spec/cert.bend as C
import ./spec/real.bend as CR
import ./lib/cert.bend as CK

# Existence (sk-05b, DESIGN §8.4, Q18)
# ------------------------------------
# In a complete ordered field (spec/real.bend), the Newton map of a checked
# certificate has a fixed point in its box (Banach): iterate from the
# center, take the limit coordinate by coordinate. With cert_fix that
# point is a zero of the block, and with cert_unique it is the only one.

# LAW: in a complete ordered field the box holds a zero of the block, for
# every choice of the parameters in their box
law cert_exists:
  for ~K: N.Num
  for ~F: O.OField
  for ~R: CR.Complete<F>
  for ~H: N.Emb<K, F>
  for +b: C.Block
  for +c: C.Cert<K>
  for  ok: {CK.check(~K, b, c) == True{} : Bool}
  for +z: M.Vec(~F)
  for  hz: C.pinned(~K, ~F, ~H, c, z)
  Sigma<&2, &2, M.Vec(~F), y => M.Both(C.ball(~K, ~F, ~H, c, y), M.vbnd(~F, C.bfun(~F, b, y, z), O.zero(F)))>
