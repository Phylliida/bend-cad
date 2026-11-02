# B8b from the goal, minimized (2026-11-02)

Danielle asked for this after C0 (spec/_draft13c.bend, 977fa18) smelled of
fixes on top of fixes: write down what is needed, question every design
constraint, and propose, critique and minimize until it is simple. The
iterations are below, then the result. Nothing here is built.

## Iterations

**0. Start: B8b as planned, with what C0's review added.**
Objects: NdIrred, RefIrred, OverIrred; ValidA; placeholder facts; A
threaded through the closure and its proofs; a deletion loop per segment.
On top of those come the three patches from the review: Angle and
LineDistance exceptions, irreducible sources, and page filters with hover
wording.

**1. The goal, and the constraints.**
- N1. The classification is decided by the sketch, and complete for the
  calculus (honest_unique). *Necessary* (trusted everything is verified
  and complete).
- N2. The certified drawing satisfies every constraint that is not red.
  *Necessary*: it is the product.
- N3. The solver never refuses a drawing at which some derivation of each
  live drop holds. *Necessary*: you asked for every case.
- N4. Everything the page says is proven. *Necessary.*
- N5. The sets the page shows are minimal. *Examine.*

**2. What B8b buys.** It buys N3 and N5. But irreducible nd serves N3 only
if the minimal sufficient set is unique. Then it is contained in every
sufficient set, so if any derivation holds at a drawing, the recorded one
does too. Is it unique?
- I tried to build two sufficient sets with neither inside the other, and
  every attempt failed. The constraint that closes the second path is
  itself dropped, through the first path, so its fact carries the first
  path's nd.
- That suggests uniqueness, but it is not proven.
- This corrects my last message, which said two different irreducible
  sets can exist. I had no example.

So B8b's N3 rests on a conjecture.

**3. Serve N3 directly.** Certification asks whether some derivation holds
at this drawing. It does not ask whether the recorded one is minimal.
P1: after the box is known, look, for each live drop, for a derivation
that passes only through segments the box certifies nonzero. That needs
a restricted closure.

**4. The restricted closure is already there.** "May not be passed
through" is what *collapsed* means in the calculus, and the context
decides collapse.
- P2: run the same closure with the context extended by the uncertified
  segments' two direction parts.
- A derivation valid in the bigger context is valid in the original one
  (Open is antitone in the context).
- Every segment it passes through is open there, so not uncertified.

This removes ValidA, the threading of A, and the second-calculus risk.

**5. Facts from earlier drops.** A derivation found in P2 may read an
earlier drop's fact whose recorded nd the box does not certify. That
doesn't matter. At the drawing, the earlier equation already holds: drops
are checked in order. So the facts can be read as holding outright, which
is DP.sound with the facts' nd dropped (facts.go's withnd False, as rfacts
does). No placeholders are needed.

**6. Where the answer would change.** If the derivation found replaced
the recorded one, the answer's witnesses would depend on the drawing.
solve_exists says `Out.cls(solve_l(..)) == cls_of(sk)`, and that would
break.
P3: the answer stays as it is, and the *verdict* checks, for each live
drop, that it is derivable at the drawing. The classification comes from
the sketch, and the certification from the drawing.

**7. Cost.** A closure per live direction drop at each precision is too
much to pay every time. So today's check stays as the fast path:
- if the recorded nd is certified, accept, as now;
- otherwise run the closure of P2.

The common case costs nothing new. This is an optimization under the same
statement.

**8. The laws.**
- solve_total keeps its statement.
- solve_complete and solve_refused change their hypothesis. Today it is
  "the live drops' recorded nd is nonzero at x*". It becomes "each live
  drop has some derivation, over facts read outright, whose segments are
  nonzero at x*". That is N3 as a theorem, and the weakest condition the
  calculus allows.
- Completeness at x* follows. A derivation valid at x* is valid in the
  extended context: a segment collapsed there is a combination of
  uncertified ones modulo equations that vanish at x*. At a high enough
  precision those are zero at x*, so it is zero too, and was not passed
  through.

**9. N5, examined: two kinds of set.**
- *Removal sets* answer "what do I take out?": the support and the Over
  set. "Remove any one of them" is true only of an irreducible set.
  - The support is irreducible already.
  - The Over set too (OverIrred, decided 2026-11-02).
- *Assumption sets* describe a reason: nd, and the sources. For these, it
  is enough that they are exact for the reason shown and worded as such:
  "its reason needs L4 and L5 to have nonzero length", not "unless".

With that, the three patches go away:
- an Angle's or a LineDistance's segment in nd is a true assumption of
  the reason;
- the order of support against nd stops mattering;
- the sources are described as sufficient.

**10. angle_args.** Under 9's wording a conflict needs no Angle exception.
Removing it would simplify DirRefutes, dconflict's ndclean and the
conflict law's proof. It is optional: what is there is proven.

**11. Drop.nd is stored as well as computed (nd == DR.nd(dv)).** Is that
redundant? Dropping it would make the spec compute the facts' nd
recursively over the constraints. Keep it: here the existing design is
right.

**12. Wider: the spec carries the degree-0 layer twice.**
- A degree-0 drop is a derivation with no nd. PLAN-sk13b already says so:
  "K(e) ... includes sk-13a's degree-0 drops".
- A degree-0 refutation is an RMotz with no nd.
- Yet Honest has WLin, Derivable, NotDerivable, Ref0 and NoRef0 beside
  the direction notions. One calculus would do.

This is outside B8b, and is noted only, not proposed.

**13. Each remaining piece, questioned again.** The fast path is an
optimization, not a concept. The extended context is a list append. The
verdict's new branch is one Or. Nothing else is left.

## Result

Three things, and one already decided:
1. **The verdict accepts a live drop that is derivable at the drawing.**
   The existing closure, run with the uncertified segments' directions
   added to its context, holds the drop's equation; today's check stays as
   the fast path. The proof needs three things:
   - Open, and so validity, is antitone in the context (a small
     induction);
   - DP.sound with the facts read outright;
   - the closure's two directions, for any context: its positive answer
     gives a derivation (as the pass already uses it), and dclose_closed
     (which already takes ctx) gives completeness for solve_complete.
2. **solve_complete and solve_refused** take the weakest hypothesis
   (iteration 8).
3. **The page's wording:** nd and sources describe the reason; supports
   and Over sets are "remove any one".
4. **OverIrred**, as decided: the only clause Honest gains.

What goes: NdIrred, RefIrred, ValidA, placeholder facts, the threading of
A, the deletion loop, and the three patches.

What is given up is a minimal nd in messages. If that is still wanted, it
is the expensive part. Proving that no derivation avoids a segment needs
the facts filtered and the syntactic nd respected, which the
extended-context trick does not give: in a triangle, collapsing two sides
collapses the third. That would be its own decision, with its own one
statement found first.
