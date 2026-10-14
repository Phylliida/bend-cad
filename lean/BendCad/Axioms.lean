/-
bend-cad's field axioms, checked against mathlib's ℝ (DESIGN §8.4, Q18).

The existence law `cert_exists` is proven in Bend for every complete ordered
field, but no complete ordered field can be built in Bend (ℝ has no
decidable order). If the axioms were inconsistent, the law would hold
vacuously. This file transcribes them field by field and proves that ℝ
satisfies every one, so they have a model.

* `OField` is `spec/field.bend`'s `OField` record. Bend's `{a == b : C}` is
  `a = b`, `Empty` is `False`, `Or` is `∨`, and `lt` lands in `Prop` where
  Bend has a `Data` proof object.
* `sub`, `le`, `bnd` are `spec/field.bend`'s `sub` and `le` and
  `spec/mat.bend`'s `bnd`. `le` is a disjunction with the strict case
  first, as in Bend.
* `nat`, `eps`, `cauchy`, `Complete` are `spec/real.bend`. Bend's
  `Nat.add(m(k), a)` is `m k + a`.

`rat_not_complete` checks that the axioms have content: ℚ with its usual
operations has no `Complete` structure.
-/
import Mathlib

namespace BendCad

/-- `spec/field.bend`: an ordered field as one record (15 axioms). -/
structure OField (C : Type) where
  zero : C
  one : C
  add : C → C → C
  mul : C → C → C
  neg : C → C
  inv : C → C
  lt : C → C → Prop
  add_assoc : ∀ a b c, add (add a b) c = add a (add b c)
  add_comm : ∀ a b, add a b = add b a
  add_zero : ∀ a, add a zero = a
  add_neg : ∀ a, add a (neg a) = zero
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  mul_comm : ∀ a b, mul a b = mul b a
  mul_one : ∀ a, mul a one = a
  mul_add : ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)
  mul_inv : ∀ a, (a = zero → False) → mul a (inv a) = one
  lt_irrefl : ∀ a, lt a a → False
  lt_trans : ∀ a b c, lt a b → lt b c → lt a c
  lt_total : ∀ a b, lt a b ∨ (a = b ∨ lt b a)
  lt_add : ∀ a b c, lt a b → lt (add a c) (add b c)
  lt_mul : ∀ a b, lt zero a → lt zero b → lt zero (mul a b)
  zero_lt_one : lt zero one

variable {C : Type}

/-- `spec/field.bend`: `sub(a, b) = add(a, neg(b))`. -/
def OField.sub (F : OField C) (a b : C) : C := F.add a (F.neg b)

/-- `spec/field.bend`: `le(a, b) = Either<lt(a, b), {a == b}>`. -/
def OField.le (F : OField C) (a b : C) : Prop := F.lt a b ∨ a = b

/-- `spec/mat.bend`: `bnd(a, s)`, |a| ≤ s: `s - a` and `s + a` are not negative. -/
def OField.bnd (F : OField C) (a s : C) : Prop :=
  F.le F.zero (F.sub s a) ∧ F.le F.zero (F.add s a)

/-- `spec/real.bend`: n as 0 + 1 + ... + 1. -/
def OField.nat (F : OField C) : ℕ → C
  | 0 => F.zero
  | k + 1 => F.add (F.nat k) F.one

/-- `spec/real.bend`: 1/(k+1). -/
def OField.eps (F : OField C) (k : ℕ) : C := F.inv (F.nat (k + 1))

/-- `spec/real.bend`: s is Cauchy with modulus m. -/
def OField.cauchy (F : OField C) (s : ℕ → C) (m : ℕ → ℕ) : Prop :=
  ∀ k a b, F.bnd (F.sub (s (m k + a)) (s (m k + b))) (F.eps k)

/-- `spec/real.bend`: Archimedean, and every Cauchy sequence with a modulus
converges, both in Skolem form. -/
structure Complete (F : OField C) where
  arch : C → ℕ
  arch_ok : ∀ x, F.lt x (F.nat (arch x))
  lim : (ℕ → C) → (ℕ → ℕ) → C
  lim_ok : ∀ s m, F.cauchy s m → ∀ k a, F.bnd (F.sub (s (m k + a)) (lim s m)) (F.eps k)

/-! ## ℝ is a model -/

/-- ℝ as an `OField`. -/
noncomputable def realOF : OField ℝ where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  inv := (·⁻¹)
  lt := (· < ·)
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  add_neg := add_neg_cancel
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  mul_one := mul_one
  mul_add := mul_add
  mul_inv := fun _ h => mul_inv_cancel₀ h
  lt_irrefl := fun a h => lt_irrefl a h
  lt_trans := fun _ _ _ => lt_trans
  lt_total := fun a b => by
    rcases lt_trichotomy a b with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  lt_add := fun _ _ c h => add_lt_add_right h c
  lt_mul := fun _ _ ha hb => mul_pos ha hb
  zero_lt_one := zero_lt_one

theorem real_sub (a b : ℝ) : realOF.sub a b = a - b := (sub_eq_add_neg a b).symm

theorem real_le (a b : ℝ) : realOF.le a b ↔ a ≤ b := le_iff_lt_or_eq.symm

theorem real_bnd (a s : ℝ) : realOF.bnd a s ↔ |a| ≤ s := by
  unfold OField.bnd
  rw [real_le, real_le, abs_le]
  change 0 ≤ s + -a ∧ 0 ≤ s + a ↔ -s ≤ a ∧ a ≤ s
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

theorem real_nat (k : ℕ) : realOF.nat k = (k : ℝ) := by
  induction k with
  | zero => change (0 : ℝ) = _; simp
  | succ k ih =>
    change realOF.nat k + 1 = _
    rw [ih]; push_cast; ring

theorem real_eps (k : ℕ) : realOF.eps k = 1 / ((k : ℝ) + 1) := by
  change (realOF.nat (k + 1))⁻¹ = _
  rw [real_nat]; push_cast; ring

/-- A sequence Cauchy with a modulus (in the transcribed sense) is Cauchy. -/
theorem real_cauchySeq (s : ℕ → ℝ) (m : ℕ → ℕ) (h : realOF.cauchy s m) : CauchySeq s := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  refine ⟨m k, fun n hn => ?_⟩
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hb := h k a 0
  rw [real_bnd, real_sub, real_eps] at hb
  rw [Real.dist_eq]
  simpa using lt_of_le_of_lt hb hk

/-- ℝ is complete in the transcribed sense. -/
noncomputable def realComplete : Complete realOF where
  arch x := ⌊x⌋₊ + 1
  arch_ok x := by
    change x < realOF.nat (⌊x⌋₊ + 1)
    rw [real_nat]; push_cast
    exact Nat.lt_floor_add_one x
  lim s _ := limUnder Filter.atTop s
  lim_ok s m h k a := by
    have hc := real_cauchySeq s m h
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
    have hT : Filter.Tendsto s Filter.atTop (nhds (limUnder Filter.atTop s)) :=
      tendsto_nhds_limUnder ⟨L, hL⟩
    have hT' : Filter.Tendsto (fun b => s (m k + b)) Filter.atTop
        (nhds (limUnder Filter.atTop s)) := by
      have := hT.comp (Filter.tendsto_add_atTop_nat (m k))
      refine this.congr (fun b => ?_)
      simp [Function.comp, Nat.add_comm]
    have hlim : Filter.Tendsto (fun b => |s (m k + a) - s (m k + b)|) Filter.atTop
        (nhds |s (m k + a) - limUnder Filter.atTop s|) :=
      ((tendsto_const_nhds).sub hT').abs
    have hbound : ∀ b, |s (m k + a) - s (m k + b)| ≤ 1 / ((k : ℝ) + 1) := by
      intro b
      have hb := h k a b
      rwa [real_bnd, real_sub, real_eps] at hb
    rw [real_bnd, real_sub, real_eps]
    exact le_of_tendsto' hlim hbound

/-- The axioms have a model: ℝ. -/
theorem axioms_consistent : Nonempty (Complete realOF) := ⟨realComplete⟩

/-! ## ℚ is not a model

The completeness axioms rule out ℚ: the rational approximations
⌊√2 (n+1)⌋ / (n+1) of √2 are Cauchy with modulus k ↦ 2k + 1, and a rational
limit would equal √2. -/

/-- ℚ as an `OField`. -/
def ratOF : OField ℚ where
  zero := 0
  one := 1
  add := (· + ·)
  mul := (· * ·)
  neg := (- ·)
  inv := (·⁻¹)
  lt := (· < ·)
  add_assoc := add_assoc
  add_comm := add_comm
  add_zero := add_zero
  add_neg := add_neg_cancel
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  mul_one := mul_one
  mul_add := mul_add
  mul_inv := fun _ h => mul_inv_cancel₀ h
  lt_irrefl := fun a h => lt_irrefl a h
  lt_trans := fun _ _ _ => lt_trans
  lt_total := fun a b => by
    rcases lt_trichotomy a b with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  lt_add := fun _ _ c h => add_lt_add_right h c
  lt_mul := fun _ _ ha hb => mul_pos ha hb
  zero_lt_one := zero_lt_one

theorem rat_sub (a b : ℚ) : ratOF.sub a b = a - b := (sub_eq_add_neg a b).symm

theorem rat_le (a b : ℚ) : ratOF.le a b ↔ a ≤ b := le_iff_lt_or_eq.symm

theorem rat_bnd (a s : ℚ) : ratOF.bnd a s ↔ |a| ≤ s := by
  unfold OField.bnd
  rw [rat_le, rat_le, abs_le]
  change 0 ≤ s + -a ∧ 0 ≤ s + a ↔ -s ≤ a ∧ a ≤ s
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

theorem rat_nat (k : ℕ) : ratOF.nat k = (k : ℚ) := by
  induction k with
  | zero => change (0 : ℚ) = _; simp
  | succ k ih =>
    change ratOF.nat k + 1 = _
    rw [ih]; push_cast; ring

theorem rat_eps (k : ℕ) : ratOF.eps k = 1 / ((k : ℚ) + 1) := by
  change (ratOF.nat (k + 1))⁻¹ = _
  rw [rat_nat]; push_cast; ring

/-- ⌊√2 (n+1)⌋ / (n+1). -/
noncomputable def sq2 (n : ℕ) : ℚ := (⌊Real.sqrt 2 * ((n : ℝ) + 1)⌋ : ℚ) / ((n : ℚ) + 1)

theorem sq2_close (n : ℕ) : |((sq2 n : ℚ) : ℝ) - Real.sqrt 2| ≤ 1 / ((n : ℝ) + 1) := by
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h1 := Int.floor_le (Real.sqrt 2 * ((n : ℝ) + 1))
  have h2 := Int.lt_floor_add_one (Real.sqrt 2 * ((n : ℝ) + 1))
  have key : ((sq2 n : ℚ) : ℝ) - Real.sqrt 2
      = ((⌊Real.sqrt 2 * ((n : ℝ) + 1)⌋ : ℝ) - Real.sqrt 2 * ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
    unfold sq2; push_cast; field_simp
  rw [key, abs_div, abs_of_pos hn]
  gcongr
  rw [abs_le]; constructor <;> linarith

theorem one_div_le_of (x y : ℝ) (hx : 0 < x) (h : x ≤ y) : 1 / y ≤ 1 / x :=
  one_div_le_one_div_of_le hx h

theorem sq2_cauchy : ratOF.cauchy sq2 (fun k => 2 * k + 1) := by
  intro k a b
  rw [rat_bnd, rat_sub, rat_eps]
  have hk : (0 : ℝ) < 2 * ((k : ℝ) + 1) := by positivity
  have ha := sq2_close (2 * k + 1 + a)
  have hb := sq2_close (2 * k + 1 + b)
  have hia : 1 / (((2 * k + 1 + a : ℕ) : ℝ) + 1) ≤ 1 / (2 * ((k : ℝ) + 1)) :=
    one_div_le_of _ _ hk (by push_cast; linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)])
  have hib : 1 / (((2 * k + 1 + b : ℕ) : ℝ) + 1) ≤ 1 / (2 * ((k : ℝ) + 1)) :=
    one_div_le_of _ _ hk (by push_cast; linarith [(Nat.cast_nonneg b : (0 : ℝ) ≤ b)])
  have hr : |((sq2 (2 * k + 1 + a) : ℚ) : ℝ) - ((sq2 (2 * k + 1 + b) : ℚ) : ℝ)| ≤ 1 / ((k : ℝ) + 1) := by
    calc |((sq2 (2 * k + 1 + a) : ℚ) : ℝ) - ((sq2 (2 * k + 1 + b) : ℚ) : ℝ)|
        ≤ |((sq2 (2 * k + 1 + a) : ℚ) : ℝ) - Real.sqrt 2| + |Real.sqrt 2 - ((sq2 (2 * k + 1 + b) : ℚ) : ℝ)| :=
          abs_sub_le _ _ _
      _ ≤ 1 / (2 * ((k : ℝ) + 1)) + 1 / (2 * ((k : ℝ) + 1)) := by
          rw [abs_sub_comm (Real.sqrt 2)]; linarith
      _ = 1 / ((k : ℝ) + 1) := by field_simp; ring
  have : ((|sq2 (2 * k + 1 + a) - sq2 (2 * k + 1 + b)| : ℚ) : ℝ) ≤ ((1 / ((k : ℚ) + 1) : ℚ) : ℝ) := by
    push_cast; exact hr
  exact_mod_cast this

/-- ℚ with its usual operations is not complete in the transcribed sense. -/
theorem rat_not_complete (R : Complete ratOF) : False := by
  have hL : ∀ k : ℕ, |((R.lim sq2 (fun k => 2 * k + 1) : ℚ) : ℝ) - Real.sqrt 2| ≤ 2 / ((k : ℝ) + 1) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have h := R.lim_ok sq2 (fun k => 2 * k + 1) sq2_cauchy k 0
    rw [rat_bnd, rat_sub, rat_eps] at h
    have h' : |((sq2 (2 * k + 1 + 0) : ℚ) : ℝ) - ((R.lim sq2 (fun k => 2 * k + 1) : ℚ) : ℝ)| ≤ 1 / ((k : ℝ) + 1) := by
      have : ((|sq2 (2 * k + 1 + 0) - R.lim sq2 (fun k => 2 * k + 1)| : ℚ) : ℝ) ≤ ((1 / ((k : ℚ) + 1) : ℚ) : ℝ) := by
        exact_mod_cast h
      push_cast at this; exact this
    have hc := sq2_close (2 * k + 1 + 0)
    have hi : 1 / (((2 * k + 1 + 0 : ℕ) : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) :=
      one_div_le_of _ _ hk (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
    calc |((R.lim sq2 (fun k => 2 * k + 1) : ℚ) : ℝ) - Real.sqrt 2|
        ≤ |((R.lim sq2 (fun k => 2 * k + 1) : ℚ) : ℝ) - ((sq2 (2 * k + 1 + 0) : ℚ) : ℝ)| + |((sq2 (2 * k + 1 + 0) : ℚ) : ℝ) - Real.sqrt 2| :=
          abs_sub_le _ _ _
      _ ≤ 1 / ((k : ℝ) + 1) + 1 / ((k : ℝ) + 1) := by rw [abs_sub_comm]; linarith
      _ = 2 / ((k : ℝ) + 1) := by ring
  have hz : ((R.lim sq2 (fun k => 2 * k + 1) : ℚ) : ℝ) = Real.sqrt 2 := by
    by_contra hne
    have hpos : 0 < |((R.lim sq2 (fun k => 2 * k + 1) : ℚ) : ℝ) - Real.sqrt 2| :=
      abs_pos.mpr (sub_ne_zero.mpr hne)
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hpos)
    have h2 := hL k
    have : 2 / ((k : ℝ) + 1) = 2 * (1 / ((k : ℝ) + 1)) := by ring
    linarith
  exact irrational_sqrt_two ⟨R.lim sq2 (fun k => 2 * k + 1), hz⟩

end BendCad
