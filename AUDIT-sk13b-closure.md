# Audit: sk-13b's closure design (PLAN-sk13b B3, "Closure, as designed 2026-10-27")

An independent read-only audit (2026-10-27) of the design against
spec/dir.bend's rules. **Verdict:** it found no rule or case pair that the
design gets wrong. The represented sets are the least closure, the
explosion claim holds, and termination holds. It found six points to fix
or state, all now folded into the plan.

## The six points

1. **"Two independent ties make a node hold every form without being
   void" is false in the closure.** A tie ∥(c, u) turns at F to
   ∥(F, conj(u)·z_c), so frame-back puts cross(u, z_c) in K. Two
   independent ties put z_c in K². Full is therefore z_c ∈ K² only, and
   every tie must feed F's generator list.
2. **DThrough from a collapsed c through an open non-root member b**
   closes only through a five-step chain: link check, then the root's
   generators, then the turn check, then the root link, then P_c.
   Simpler: give c the generators w·conj(ℓ_b)·g for g among the root's
   generators (through at b of ∥(b, conj(ℓ_b) g)).
3. **Rebuilt sets are not monotone.** A merge into F, or a root becoming
   a member, can shrink a represented set until a later round restores
   it. So the link check must compute a fresh basis of G_cb: the pair
   test's witness w₁, then a test of i·w₁. That basis is then compared
   with the span of the stored links.
4. **The complex-line check needs an independent basis.** Insert i·b_j
   for the hull's kept non-K rows, with K²'s generators first. A
   redundant generator gives a zero residual whose x is in K², and no
   skeleton item.
5. **Nodes outside the sketch.** NSeg{s} for a non-segment s has
   direction 0, so it is collapsed and void. The checks range over F and
   the sketch's segments, and a lemma covers the rest.
6. **Tied membership includes K:** cross(u, y) ∈ span(cross(u, g_j)) with
   K²'s generators among the g_j. Then cross(u, K²) = K for u ≠ 0.

## Checked and found sound

- F's set is exactly {y : Im y ∈ K}. A member's set is {y : Im(ℓ y) ∈ K}.
- Two linked open nodes are rotations of each other (through and turn
  both ways).
- Labels are unique up to Q: in free components, a second label gives a
  complex line through z_b; in F's component, by its form.
- Every DTurn and DThrough pair of node kinds is covered.
- Self pairs and zero labels are harmless.
- Both generator lists are complete, and K is exact.
- Explosion holds both ways. The refutations that don't explode don't
  change derivability.
- Termination: at most two links per pair (G_cb is a Q-subspace of Q(i)),
  K's rows are bounded by pivots in the facts' monomials and the
  variables, and the hulls are a function of the skeleton.
