# bend-cad: laws planned but not proven yet (open claims). Not imported by
# PROOF.bend, so the gate stays meaningful. Checking this file reports its
# open laws as TODOs; that is expected.

import Base
import ./LAWS.bend as Laws
import ./spec/field.bend as O
import ./spec/sketch.bend as K

# Meaning lemmas (sk-03 statements, proven in sk-07; DESIGN §5.5)
# ---------------------------------------------------------------
# In every ordered field F (so in the reals, where a sketch's exact solution
# lives), for every assignment env of values to the variables: a
# constraint's exact equations vanish and its side conditions are positive
# exactly when it means what it says (K.Constraint.means, one case per kind,
# in the vocabulary of spec/geom.bend). Merge kinds need their variable
# sharing (wf). F is a template parameter: the proofs see its operations
# only through the ordered-field axioms (spec/field.bend).

# LAW: the exact form implies the meaning
law means_sound:
  for ~F: O.OField
  for +env: List<&2, O.C(F)>
  for +es: List<&2, K.Ent>
  for +k: K.Constraint
  for  w: K.Constraint.wf(es, k)
  for  h: K.Constraint.holds(~F, env, es, k)
  K.Constraint.means(~F, env, es, k)

# LAW: the meaning implies the exact form (the form asks for nothing more)
law means_complete:
  for ~F: O.OField
  for +env: List<&2, O.C(F)>
  for +es: List<&2, K.Ent>
  for +k: K.Constraint
  for  h: K.Constraint.means(~F, env, es, k)
  K.Constraint.holds(~F, env, es, k)

# LAW: an entity's side conditions hold exactly when it is proper
law ent_sound:
  for ~F: O.OField
  for +env: List<&2, O.C(F)>
  for +e: K.Ent
  for  h: K.Ent.holds(~F, env, e)
  K.Ent.means(~F, env, e)

# LAW: a proper entity satisfies its side conditions
law ent_complete:
  for ~F: O.OField
  for +env: List<&2, O.C(F)>
  for +e: K.Ent
  for  h: K.Ent.means(~F, env, e)
  K.Ent.holds(~F, env, e)

# LAW: a solution of a well-formed sketch's exact system (F = 0, every side
# condition positive) is a sketch where every circle and arc is proper and
# every driving constraint means what it says
law sketch_sound:
  for ~F: O.OField
  for +env: List<&2, O.C(F)>
  for +sk: K.Sketch
  for  w: K.Sketch.wf(sk)
  for  h: K.Sketch.holds(~F, env, sk)
  K.Sketch.means(~F, env, sk)

# LAW: and conversely
law sketch_complete:
  for ~F: O.OField
  for +env: List<&2, O.C(F)>
  for +sk: K.Sketch
  for  h: K.Sketch.means(~F, env, sk)
  K.Sketch.holds(~F, env, sk)
