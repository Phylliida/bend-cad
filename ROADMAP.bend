# bend-cad: laws planned but not proven yet (open claims). Not imported by
# PROOF.bend, so the gate stays meaningful. Checking this file reports its
# open laws as TODOs; that is expected.

import Base
import ./LAWS.bend as Laws
import ./spec/num.bend as S
import ./spec/sketch.bend as K

# Meaning lemmas (sk-03 statements, proven in sk-07; DESIGN §5.5)
# ---------------------------------------------------------------
# For every assignment env of rationals to the variables: a constraint's
# exact equations vanish and its side conditions are positive exactly when
# it means what it says (K.Constraint.means, one case per kind, in the
# vocabulary of spec/geom.bend). Merge kinds need their index sharing (wf).

# LAW: the exact form implies the meaning
law means_sound:
  for +env: List<&2, S.Q>
  for +k: K.Constraint
  for  w: K.Constraint.wf(k)
  for  h: K.Constraint.holds(env, k)
  K.Constraint.means(env, k)

# LAW: the meaning implies the exact form (the form asks for nothing more)
law means_complete:
  for +env: List<&2, S.Q>
  for +k: K.Constraint
  for  h: K.Constraint.means(env, k)
  K.Constraint.holds(env, k)

# LAW: an entity's side conditions hold exactly when it is proper
law ent_sound:
  for +env: List<&2, S.Q>
  for +e: K.Ent
  for  h: K.Ent.holds(env, e)
  K.Ent.means(env, e)

# LAW: a proper entity satisfies its side conditions
law ent_complete:
  for +env: List<&2, S.Q>
  for +e: K.Ent
  for  h: K.Ent.means(env, e)
  K.Ent.holds(env, e)

# LAW: a solution of a well-formed sketch's exact system (F = 0, every side
# condition positive) is a sketch where every drawn curve is proper and every
# driving constraint means what it says
law sketch_sound:
  for +env: List<&2, S.Q>
  for +sk: K.Sketch
  for  w: K.Sketch.wf(sk)
  for  h: K.Sketch.holds(env, sk)
  K.Sketch.means(env, sk)

# LAW: and conversely
law sketch_complete:
  for +env: List<&2, S.Q>
  for +sk: K.Sketch
  for  h: K.Sketch.means(env, sk)
  K.Sketch.holds(env, sk)
