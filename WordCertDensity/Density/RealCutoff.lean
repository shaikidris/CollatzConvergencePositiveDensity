/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Density.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith

/-!
# Real and natural counting cutoffs

The real-cutoff profile uses the same positive-prefix count at the natural
floor, divided by the actual real cutoff. The denominator correction is at
most $1/X$ for $X>0$, so both profiles have the same lower limit.
-/

@[expose] public section

namespace WordCertDensity

open Filter
open scoped Topology

noncomputable section

/-- The positive-prefix count divided by the real cutoff, including empty prefixes. -/
def realPartialDensity (S : Set ℕ) (X : ℝ) : ℝ :=
  (prefixCount S ⌊X⌋₊ : ℝ) / X

/-- Below one the positive prefix is empty, also for nonpositive cutoffs. -/
theorem realPartialDensity_eq_zero_of_lt_one (S : Set ℕ) {X : ℝ} (hX : X < 1) :
    realPartialDensity S X = 0 := by
  simp [realPartialDensity, Nat.floor_eq_zero.mpr hX]

/-- Natural cutoffs recover the original density profile exactly, including zero. -/
@[simp] theorem realPartialDensity_natCast (S : Set ℕ) (N : ℕ) :
    realPartialDensity S N = partialDensity S N := by
  simp [realPartialDensity, partialDensity]

/-- The real profile is nonnegative at every cutoff. -/
theorem realPartialDensity_nonneg (S : Set ℕ) (X : ℝ) :
    0 ≤ realPartialDensity S X := by
  by_cases hX : X < 1
  · rw [realPartialDensity_eq_zero_of_lt_one S hX]
  · exact div_nonneg (Nat.cast_nonneg _) (by linarith)

/-- Enlarging the denominator from the floor can only decrease the profile. -/
theorem realPartialDensity_le_floor (S : Set ℕ) {X : ℝ} (hX : 0 ≤ X) :
    realPartialDensity S X ≤ partialDensity S ⌊X⌋₊ := by
  by_cases hn : ⌊X⌋₊ = 0
  · simp [realPartialDensity, partialDensity, hn]
  · exact div_le_div_of_nonneg_left (Nat.cast_nonneg _)
      (by exact_mod_cast Nat.pos_of_ne_zero hn) (Nat.floor_le hX)

/-- The real profile is at most one, also at nonpositive cutoffs. -/
theorem realPartialDensity_le_one (S : Set ℕ) (X : ℝ) :
    realPartialDensity S X ≤ 1 := by
  by_cases hX : X < 1
  · rw [realPartialDensity_eq_zero_of_lt_one S hX]
    norm_num
  · exact (realPartialDensity_le_floor S (by linarith)).trans
      (partialDensity_le_one S _)

/-- The full denominator loss is at most the reciprocal cutoff. -/
theorem partialDensity_floor_le_real_add (S : Set ℕ) {X : ℝ} (hX : 0 < X) :
    partialDensity S ⌊X⌋₊ ≤ realPartialDensity S X + 1 / X := by
  by_cases hn : ⌊X⌋₊ = 0
  · simp only [hn, partialDensity, prefixCount_zero, Nat.cast_zero, div_zero]
    exact add_nonneg (realPartialDensity_nonneg S X) (le_of_lt (one_div_pos.mpr hX))
  · have hnpos : (0 : ℝ) < ⌊X⌋₊ := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hmul : partialDensity S ⌊X⌋₊ * (⌊X⌋₊ : ℝ) = prefixCount S ⌊X⌋₊ :=
      div_mul_cancel₀ _ (ne_of_gt hnpos)
    have hgap : 0 ≤ X - (⌊X⌋₊ : ℝ) := sub_nonneg.mpr (Nat.floor_le hX.le)
    have hsmall : partialDensity S ⌊X⌋₊ * (X - (⌊X⌋₊ : ℝ)) ≤ 1 := by
      calc
        _ ≤ 1 * (X - (⌊X⌋₊ : ℝ)) :=
          mul_le_mul_of_nonneg_right (partialDensity_le_one S _) hgap
        _ ≤ 1 := by linarith [Nat.lt_floor_add_one X]
    calc
      _ ≤ ((prefixCount S ⌊X⌋₊ : ℝ) + 1) / X := (le_div_iff₀ hX).mpr (by nlinarith)
      _ = realPartialDensity S X + 1 / X := add_div _ _ _

/-- Eventual lower bounds may be stated using either natural or real cutoffs. -/
theorem le_lowerNaturalDensity_iff_real (S : Set ℕ) (d : ℝ) :
    d ≤ lowerNaturalDensity S ↔
      ∀ e < d, ∀ᶠ X : ℝ in atTop, e ≤ realPartialDensity S X := by
  rw [le_lowerNaturalDensity_iff]
  constructor
  · intro h e he
    obtain ⟨e', hee', he'd⟩ := exists_between he
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h e' he'd)
    have hfloor : ∀ᶠ X : ℝ in atTop, N ≤ ⌊X⌋₊ := by
      filter_upwards [eventually_ge_atTop (N : ℝ), eventually_ge_atTop (0 : ℝ)] with X hXN hX
      exact (Nat.le_floor_iff hX).mpr hXN
    have hinv : ∀ᶠ X : ℝ in atTop, X⁻¹ < e' - e :=
      tendsto_inv_atTop_zero.eventually (gt_mem_nhds (sub_pos.mpr hee'))
    filter_upwards [hfloor, hinv, eventually_gt_atTop (0 : ℝ)] with X hX hsmall hpos
    have hbound := partialDensity_floor_le_real_add S hpos
    have hlarge := hN ⌊X⌋₊ hX
    rw [one_div] at hbound
    linarith
  · intro h e he
    have hn := tendsto_natCast_atTop_atTop.eventually (h e he)
    simpa using hn

/-- The manuscript's real-cutoff liminf equals its lower natural density. -/
theorem lowerNaturalDensity_eq_real_liminf (S : Set ℕ) :
    lowerNaturalDensity S =
      liminf (fun X : ℝ => (prefixCount S ⌊X⌋₊ : ℝ) / X) atTop := by
  have hlower : atTop.IsBoundedUnder (· ≥ ·) (realPartialDensity S) :=
    ⟨0, by
      change ∀ᶠ X : ℝ in atTop, 0 ≤ realPartialDensity S X
      exact Eventually.of_forall (realPartialDensity_nonneg S)⟩
  have hupper : atTop.IsBoundedUnder (· ≤ ·) (realPartialDensity S) :=
    ⟨1, by
      change ∀ᶠ X : ℝ in atTop, realPartialDensity S X ≤ 1
      exact Eventually.of_forall (realPartialDensity_le_one S)⟩
  have hiff (d : ℝ) : d ≤ liminf (realPartialDensity S) atTop ↔
      ∀ e < d, ∀ᶠ X : ℝ in atTop, e ≤ realPartialDensity S X :=
    le_liminf_iff' hupper.isCoboundedUnder_ge hlower
  apply le_antisymm
  · exact (hiff _).mpr ((le_lowerNaturalDensity_iff_real S _).mp le_rfl)
  · exact (le_lowerNaturalDensity_iff_real S _).mpr ((hiff _).mp le_rfl)

end

end WordCertDensity
