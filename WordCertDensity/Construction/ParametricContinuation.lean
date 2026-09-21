/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.ParametricIncrement
import WordCertDensity.Construction.GraftContinuationTail

/-! # Root-uniform continuation variation with a fixed positive parameter

The full incoming family factor and the first macro increment remain in the
summable tail. One late splice works for every guarded root and later stage.
The baseline true-mean corridor families are retained in this module.
-/

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- The parameterized continuation coefficient is nonnegative at every macro scale. -/
theorem parametricGraftVariationConstant_nonneg (θ : ℝ) {L : ℝ} (hL : 0 ≤ L) (b : ℕ) :
    0 ≤ parametricGraftVariationConstant θ L b := by
  have := Analytic.mixingCoefficient_pos.le
  unfold parametricGraftVariationConstant
  positivity

/-- One old cutoff also pays all smaller-parameter conductor boundaries. -/
theorem eventually_parametricGraftMacroBoundary {θ L : ℝ} (hθcap : θ ≤ 1 / 1000)
    (hL : 0 ≤ L) (δ : ℝ) {b : ℕ} (hb : 100 ≤ b) :
    ∀ᶠ t in atTop, ∀ j,
      parametricBoundary θ L δ (macroCount L (graftInitialCount b t) j) ≤ 1 := by
  filter_upwards [eventually_graftMacroBoundary hL δ hb] with t ht j
  exact (parametricBoundary_le_fixed hθcap L δ _).trans (ht j)

private theorem initialCount_pos {b : ℕ} (hb : 32 ^ 5 ≤ b) (t : ℕ) :
    1 ≤ graftInitialCount b t := by
  have hE := graftPrecision_ge_256 (by omega : 256 ^ 2 ≤ b) t
  unfold graftInitialCount
  omega

/-- Every finite sum of actual continuation increments is bounded by the full uniform tail. -/
theorem physicalParametricGraftMark_variation_partial {θ L δ : ℝ} {b t root : ℕ}
    (hθ : 0 < θ) (hb : 32 ^ 5 ≤ b) (hL : 0 < L) (hδ : 0 < δ) (hsmall : 2 * δ ≤ 1)
    (hpay : 10 ≤ stoppedCorridorRate δ * L)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hboundary : ∀ j, parametricBoundary θ L δ (macroCount L (graftInitialCount b t) j) ≤ 1)
    (N : ℕ) :
    (∑ j ∈ Finset.range N,
      |physicalParametricGraftMark θ L δ b t (j + 1) root - physicalParametricGraftMark θ L δ b
        t j root|) ≤
      parametricContinuationTail θ L b t := by
  have hB0 := initialCount_pos hb t
  have hK := parametricGraftVariationConstant_nonneg θ hL.le b
  have hP := (seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t)
  calc
    _ ≤ ∑ j ∈ Finset.range N, parametricGraftVariationConstant θ L b * seedCapacity b t /
        (macroCount L (graftInitialCount b t) j : ℝ) ^ 4 := by
      apply Finset.sum_le_sum
      intro j _
      exact physicalParametricGraftMark_increment_polynomial hθ hb hL.le hδ hsmall hpay hroot hpaid
        (hB0.trans (macroCount_ge_start L (graftInitialCount b t) j)) (hboundary j)
    _ = (parametricGraftVariationConstant θ L b * seedCapacity b t) *
        ∑ j ∈ Finset.range N, 1 / (macroCount L (graftInitialCount b t) j : ℝ) ^ 4 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ (parametricGraftVariationConstant θ L b * seedCapacity b t) *
        (3 / (graftInitialCount b t : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left (graft_macroFourth_partial hL hB0 N) (mul_nonneg hK hP)
    _ = _ := by unfold parametricContinuationTail graftTailWeight; ring

/-- The complete series of physical increments is summable and obeys the same varying-start
    bound. -/
theorem physicalParametricGraftMark_variation_series {θ L δ : ℝ} {b t root : ℕ}
    (hθ : 0 < θ) (hb : 32 ^ 5 ≤ b) (hL : 0 < L) (hδ : 0 < δ) (hsmall : 2 * δ ≤ 1)
    (hpay : 10 ≤ stoppedCorridorRate δ * L)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hboundary : ∀ j, parametricBoundary θ L δ (macroCount L (graftInitialCount b t) j) ≤ 1) :
    Summable (fun j => |physicalParametricGraftMark θ L δ b t (j + 1) root -
      physicalParametricGraftMark θ L δ b t j root|) ∧
      (∑' j, |physicalParametricGraftMark θ L δ b t (j + 1) root - physicalParametricGraftMark θ
        L δ b t j root|) ≤
        parametricContinuationTail θ L b t := by
  have hp := physicalParametricGraftMark_variation_partial hθ hb hL hδ hsmall hpay hroot hpaid
    hboundary
  exact ⟨summable_of_sum_range_le (fun _ => abs_nonneg _) hp,
    Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _) hp⟩

/-- Every later physical mark stays within the complete continuation budget of stage zero. -/
theorem physicalParametricGraftMark_continuation_bound {θ L δ : ℝ} {b t root : ℕ}
    (hθ : 0 < θ) (hb : 32 ^ 5 ≤ b) (hL : 0 < L) (hδ : 0 < δ) (hsmall : 2 * δ ≤ 1)
    (hpay : 10 ≤ stoppedCorridorRate δ * L)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hboundary : ∀ j, parametricBoundary θ L δ (macroCount L (graftInitialCount b t) j) ≤ 1)
    (N : ℕ) :
    |physicalParametricGraftMark θ L δ b t N root - physicalParametricGraftMark θ L δ b t 0 root| ≤
      parametricContinuationTail θ L b t := by
  have h := dist_le_range_sum_dist (fun j => physicalParametricGraftMark θ L δ b t j root) N
  have hp := physicalParametricGraftMark_variation_partial hθ hb hL hδ hsmall hpay hroot hpaid
    hboundary N
  have h' : |physicalParametricGraftMark θ L δ b t N root - physicalParametricGraftMark θ L δ b
    t 0 root| ≤
      ∑ j ∈ Finset.range N,
        |physicalParametricGraftMark θ L δ b t (j + 1) root - physicalParametricGraftMark θ L δ
          b t j root| := by
    simpa only [Real.dist_eq, abs_sub_comm] using h
  exact h'.trans hp

/-- One late splice threshold works for every guarded root and every later continuation stage. -/
theorem eventually_physicalParametricGraftMark_continuation {θ L δ : ℝ} {b : ℕ}
    (hθ : 0 < θ) (hθcap : θ ≤ 1 / 1000) (hb : 32 ^ 5 ≤ b) (hL : 0 < L) (hδ : 0 < δ) (hsmall : 2
      * δ ≤ 1)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) :
    ∀ᶠ t in atTop, ∀ root, 16 ^ b ≤ root →
      (Summable (fun j =>
        |physicalParametricGraftMark θ L δ b t (j + 1) root - physicalParametricGraftMark θ L δ
          b t j root|) ∧
        (∑' j, |physicalParametricGraftMark θ L δ b t (j + 1) root - physicalParametricGraftMark
          θ L δ b t j root|) ≤
          parametricContinuationTail θ L b t) ∧
      ∀ j, |physicalParametricGraftMark θ L δ b t j root - physicalParametricGraftMark θ L δ b t
        0 root| ≤
        parametricContinuationTail θ L b t := by
  filter_upwards [graftOffsetAbsorption_eventually (by omega : 100 ≤ b),
    eventually_parametricGraftMacroBoundary hθcap hL.le δ (by omega : 100 ≤ b)] with t hoff
      hboundary root hroot
  exact ⟨physicalParametricGraftMark_variation_series hθ hb hL hδ hsmall hpay hroot hoff hboundary,
    physicalParametricGraftMark_continuation_bound hθ hb hL hδ hsmall hpay hroot hoff hboundary⟩

end WordCertDensity.Construction
