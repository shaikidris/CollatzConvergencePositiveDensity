/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.MacroSchedule
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # The complete inverse-fourth-power tail at a varying initial count

A discrete reciprocal-cube telescoping estimate gives the retained factor
three without an integral comparison. Actual macrocounts dominate successive
integers beginning at their true initial count, including the first macro.
-/

namespace WordCertDensity.Construction

/-- One reciprocal fourth power is paid by a telescoping reciprocal-cube difference. -/
theorem graft_reciprocalFourth_step {x : ℝ} (hx : 1 ≤ x) :
    1 / x ^ 4 ≤ 3 / x ^ 3 - 3 / (x + 1) ^ 3 := by
  have hxpos : 0 < x := by linarith
  have hc : 1 ≤ x ^ 3 := one_le_pow₀ hx
  have he : 3 / x ^ 3 - 3 / (x + 1) ^ 3 - 1 / x ^ 4 =
      (8 * x ^ 3 + 6 * x ^ 2 - 1) / (x ^ 4 * (x + 1) ^ 3) := by
    field_simp
    ring
  have hn : 0 ≤ (8 * x ^ 3 + 6 * x ^ 2 - 1) / (x ^ 4 * (x + 1) ^ 3) :=
    div_nonneg (by nlinarith [sq_nonneg x]) (by positivity)
  rw [← he] at hn
  linarith

/-- Every finite initial segment retains its reciprocal-cube remainder. -/
theorem graft_reciprocalFourth_partial {B : ℕ} (hB : 1 ≤ B) (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / ((B + n : ℕ) : ℝ) ^ 4) ≤
      3 / (B : ℝ) ^ 3 - 3 / ((B + N : ℕ) : ℝ) ^ 3 := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hs := graft_reciprocalFourth_step
        (x := ((B + N : ℕ) : ℝ)) (by exact_mod_cast (show 1 ≤ B + N by omega))
      simp only [Nat.cast_add, Nat.cast_one, add_assoc] at ih hs ⊢
      linarith

/-- The whole integer tail is summable, with a bound uniform in its starting count. -/
theorem graft_reciprocalFourth_series {B : ℕ} (hB : 1 ≤ B) :
    Summable (fun n : ℕ => 1 / ((B + n : ℕ) : ℝ) ^ 4) ∧
      (∑' n : ℕ, 1 / ((B + n : ℕ) : ℝ) ^ 4) ≤ 3 / (B : ℝ) ^ 3 := by
  have hnonneg (n : ℕ) : (0 : ℝ) ≤ 1 / ((B + n : ℕ) : ℝ) ^ 4 := by positivity
  have hpartial (N : ℕ) : (∑ n ∈ Finset.range N, 1 / ((B + n : ℕ) : ℝ) ^ 4) ≤
      3 / (B : ℝ) ^ 3 :=
    (graft_reciprocalFourth_partial hB N).trans (sub_le_self _ (by positivity))
  exact ⟨summable_of_sum_range_le hnonneg hpartial,
    Real.tsum_le_of_sum_range_le hnonneg hpartial⟩

/-- Every actual macro schedule has the same complete finite tail bound. -/
theorem graft_macroFourth_partial {L : ℝ} (hL : 0 < L) {B : ℕ} (hB : 1 ≤ B) (N : ℕ) :
    (∑ j ∈ Finset.range N, 1 / (macroCount L B j : ℝ) ^ 4) ≤ 3 / (B : ℝ) ^ 3 := by
  calc
    _ ≤ ∑ j ∈ Finset.range N, 1 / ((B + j : ℕ) : ℝ) ^ 4 := by
      apply Finset.sum_le_sum
      intro j _
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (macroCount_lower hL B j)) 4
    _ ≤ _ := (graft_reciprocalFourth_partial hB N).trans (sub_le_self _ (by positivity))

/-- The complete actual macro tail includes stage zero and is bounded uniformly in B. -/
theorem graft_macroFourth_series {L : ℝ} (hL : 0 < L) {B : ℕ} (hB : 1 ≤ B) :
    Summable (fun j : ℕ => 1 / (macroCount L B j : ℝ) ^ 4) ∧
      (∑' j : ℕ, 1 / (macroCount L B j : ℝ) ^ 4) ≤ 3 / (B : ℝ) ^ 3 := by
  have hnonneg (j : ℕ) : (0 : ℝ) ≤ 1 / (macroCount L B j : ℝ) ^ 4 := by positivity
  exact ⟨summable_of_sum_range_le hnonneg (graft_macroFourth_partial hL hB),
    Real.tsum_le_of_sum_range_le hnonneg (graft_macroFourth_partial hL hB)⟩

end WordCertDensity.Construction
