/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftSeries
import WordCertDensity.Construction.GraftIncrement
import WordCertDensity.Construction.GraftDecay

/-! # Complete continuation variation, uniformly as the splice moves

The first macro is included. The full incoming factor P_t is retained in
the reciprocal-cube tail, which tends to zero with the actual rounded B_0.
One sufficiently late splice pays the boundary at every later macro count
and works for all physical roots above the fixed seed height.
-/

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- The continuation coefficient is nonnegative for every allowed macro scale. -/
theorem graftVariationConstant_nonneg {L : ℝ} (hL : 0 ≤ L) (b : ℕ) :
    0 ≤ graftVariationConstant L b := by
  have := Analytic.mixingCoefficient_pos.le
  unfold graftVariationConstant
  positivity

/-- The manuscript's complete continuation budget, including the first macro. -/
noncomputable def graftContinuationTail (L : ℝ) (b t : ℕ) : ℝ :=
  3 * graftVariationConstant L b * graftTailWeight b t

/-- The whole incoming-weighted continuation tail tends to zero as the splice moves. -/
theorem graftContinuationTail_tendsto (L : ℝ) {b : ℕ} (hb : 256 ^ 2 ≤ b) :
    Tendsto (graftContinuationTail L b) atTop (𝓝 0) := by
  change Tendsto (fun t => 3 * graftVariationConstant L b * graftTailWeight b t) atTop (𝓝 0)
  simpa only [mul_zero] using
    (graftTailWeight_tendsto hb).const_mul (3 * graftVariationConstant L b)

/-- A late initial count pays the actual conductor boundary at every subsequent macro stage. -/
theorem eventually_graftMacroBoundary {L : ℝ} (hL : 0 ≤ L) (δ : ℝ) {b : ℕ} (hb : 100 ≤ b) :
    ∀ᶠ t in atTop, ∀ j, macroBoundary L δ (macroCount L (graftInitialCount b t) j) ≤ 1 := by
  obtain ⟨B, hB⟩ := eventually_atTop.mp (eventually_macroBoundary_le_one hL δ)
  have ht := (tendsto_atTop.mp (graftInitialCount_tendsto hb)) B
  filter_upwards [ht] with t ht j
  exact hB _ (ht.trans (macroCount_ge_start L (graftInitialCount b t) j))

private theorem initialCount_pos {b : ℕ} (hb : 32 ^ 5 ≤ b) (t : ℕ) :
    1 ≤ graftInitialCount b t := by
  have hE := graftPrecision_ge_256 (by omega : 256 ^ 2 ≤ b) t
  unfold graftInitialCount
  omega

/-- Every finite sum of actual continuation increments is bounded by the full uniform tail. -/
theorem physicalGraftMark_variation_partial {L δ : ℝ} {b t root : ℕ}
    (hb : 32 ^ 5 ≤ b) (hL : 0 < L) (hδ : 0 < δ) (hsmall : 2 * δ ≤ 1)
    (hpay : 10 ≤ stoppedCorridorRate δ * L)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hboundary : ∀ j, macroBoundary L δ (macroCount L (graftInitialCount b t) j) ≤ 1)
    (N : ℕ) :
    (∑ j ∈ Finset.range N,
      |physicalGraftMark L δ b t (j + 1) root - physicalGraftMark L δ b t j root|) ≤
      graftContinuationTail L b t := by
  have hB0 := initialCount_pos hb t
  have hK := graftVariationConstant_nonneg hL.le b
  have hP := (seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t)
  calc
    _ ≤ ∑ j ∈ Finset.range N, graftVariationConstant L b * seedCapacity b t /
        (macroCount L (graftInitialCount b t) j : ℝ) ^ 4 := by
      apply Finset.sum_le_sum
      intro j _
      exact physicalGraftMark_increment_polynomial hb hL.le hδ hsmall hpay hroot hpaid
        (hB0.trans (macroCount_ge_start L (graftInitialCount b t) j)) (hboundary j)
    _ = (graftVariationConstant L b * seedCapacity b t) *
        ∑ j ∈ Finset.range N, 1 / (macroCount L (graftInitialCount b t) j : ℝ) ^ 4 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ (graftVariationConstant L b * seedCapacity b t) *
        (3 / (graftInitialCount b t : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left (graft_macroFourth_partial hL hB0 N) (mul_nonneg hK hP)
    _ = _ := by unfold graftContinuationTail graftTailWeight; ring

/-- The complete series of physical increments is summable and obeys the same varying-start bound. -/
theorem physicalGraftMark_variation_series {L δ : ℝ} {b t root : ℕ}
    (hb : 32 ^ 5 ≤ b) (hL : 0 < L) (hδ : 0 < δ) (hsmall : 2 * δ ≤ 1)
    (hpay : 10 ≤ stoppedCorridorRate δ * L)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hboundary : ∀ j, macroBoundary L δ (macroCount L (graftInitialCount b t) j) ≤ 1) :
    Summable (fun j => |physicalGraftMark L δ b t (j + 1) root - physicalGraftMark L δ b t j root|) ∧
      (∑' j, |physicalGraftMark L δ b t (j + 1) root - physicalGraftMark L δ b t j root|) ≤
        graftContinuationTail L b t := by
  have hp := physicalGraftMark_variation_partial hb hL hδ hsmall hpay hroot hpaid hboundary
  exact ⟨summable_of_sum_range_le (fun _ => abs_nonneg _) hp,
    Real.tsum_le_of_sum_range_le (fun _ => abs_nonneg _) hp⟩

/-- Every later physical mark stays within the complete continuation budget of stage zero. -/
theorem physicalGraftMark_continuation_bound {L δ : ℝ} {b t root : ℕ}
    (hb : 32 ^ 5 ≤ b) (hL : 0 < L) (hδ : 0 < δ) (hsmall : 2 * δ ≤ 1)
    (hpay : 10 ≤ stoppedCorridorRate δ * L)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hboundary : ∀ j, macroBoundary L δ (macroCount L (graftInitialCount b t) j) ≤ 1)
    (N : ℕ) :
    |physicalGraftMark L δ b t N root - physicalGraftMark L δ b t 0 root| ≤
      graftContinuationTail L b t := by
  have h := dist_le_range_sum_dist (fun j => physicalGraftMark L δ b t j root) N
  have hp := physicalGraftMark_variation_partial hb hL hδ hsmall hpay hroot hpaid hboundary N
  have h' : |physicalGraftMark L δ b t N root - physicalGraftMark L δ b t 0 root| ≤
      ∑ j ∈ Finset.range N,
        |physicalGraftMark L δ b t (j + 1) root - physicalGraftMark L δ b t j root| := by
    simpa only [Real.dist_eq, abs_sub_comm] using h
  exact h'.trans hp

/-- One late splice threshold works for every guarded root and every later continuation stage. -/
theorem eventually_physicalGraftMark_continuation {L δ : ℝ} {b : ℕ}
    (hb : 32 ^ 5 ≤ b) (hL : 0 < L) (hδ : 0 < δ) (hsmall : 2 * δ ≤ 1)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) :
    ∀ᶠ t in atTop, ∀ root, 16 ^ b ≤ root →
      (Summable (fun j =>
        |physicalGraftMark L δ b t (j + 1) root - physicalGraftMark L δ b t j root|) ∧
        (∑' j, |physicalGraftMark L δ b t (j + 1) root - physicalGraftMark L δ b t j root|) ≤
          graftContinuationTail L b t) ∧
      ∀ j, |physicalGraftMark L δ b t j root - physicalGraftMark L δ b t 0 root| ≤
        graftContinuationTail L b t := by
  filter_upwards [graftOffsetAbsorption_eventually (by omega : 100 ≤ b),
    eventually_graftMacroBoundary hL.le δ (by omega : 100 ≤ b)] with t hoff hboundary root hroot
  exact ⟨physicalGraftMark_variation_series hb hL hδ hsmall hpay hroot hoff hboundary,
    physicalGraftMark_continuation_bound hb hL hδ hsmall hpay hroot hoff hboundary⟩

end WordCertDensity.Construction
