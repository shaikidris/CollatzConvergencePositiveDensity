/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.ParametricLevels
import WordCertDensity.Construction.GraftDebit

/-! # Initial transition errors at a positive appended marker level

The original enlarged conductor and incoming seed histogram are retained.
Each marker discrepancy keeps its own level, and the rejected original mass
is paid without renormalization. The selectors are the baseline corridors.
-/

namespace WordCertDensity.Construction

open scoped Classical

/-- Smaller positive marker parameters fit the existing enlarged transition conductor. -/
theorem parametricTransitionWords_level {θ : ℝ} (hθcap : θ ≤ 1 / 1000)
    {b : ℕ} (hb : 256 ^ 2 ≤ b) (δ : ℝ) (t : ℕ)
    (w : ValuationWord) (hw : w ∈ graftTransitionWords δ b t) :
    parametricLevel θ (graftInitialCount b t) ≤ 2 * seedSize b t - w.length :=
  (parametricLevel_le_fixed hθcap _).trans (graftTransitionWords_level hb δ t w hw)

/-- Finite stopping at Q=2b_t pays both marker discrepancies and the rejected original mass. -/
theorem parametricTransition_reference_error {θ δ : ℝ} (hθ : 0 < θ) (hθcap : θ ≤ 1 / 1000) (hδ :
    0 < δ) {b : ℕ}
    (hb : 256 ^ 2 ≤ b) (t : ℕ) :
    Reference.mean (2 * seedSize b t) (fun y =>
      |Transfer.coarseSelected (graftTransitionWords δ b t) (2 * seedSize b t)
          (parametricLevel θ (graftInitialCount b t)) (parametricTransitionWords_level hθcap hb
            δ t) y -
        Reference.marker (seedTailDepth b t)
          (Reference.project (graftTransition_level_guards hb t).2.1 y)|) ≤
      (2 / 3 : ℝ) * (Analytic.mixingError (parametricLevel θ (graftInitialCount b t)) +
        Analytic.mixingError (seedTailDepth b t) + graftTransitionFailure δ b t) := by
  have hcount : 1 ≤ graftInitialCount b t := by
    have hE := graftPrecision_ge_256 hb t
    unfold graftInitialCount
    omega
  have hold : 1 ≤ seedTailDepth b t := by
    have hs := seedSize_ge b t
    unfold seedTailDepth
    omega
  have hlen : ∀ w ∈ graftTransitionWords δ b t, w.length ≤ 2 * seedSize b t := by
    intro w hw
    have hd := graftTransitionWords_depth hw
    omega
  have he := Transfer.stopped_transfer_le (graftTransitionWords δ b t) hlen
    (parametricTransitionWords_level hθcap hb δ t) (parametricLevel_pos hθ hcount)
    hold (graftTransition_level_guards hb t).2.1 (graftTransitionWords_prefixFree δ b t)
  have hd := graftTransitionMass_deficit hδ hb t
  change 1 - Reference.stoppingMass (graftTransitionWords δ b t) ≤ _ at hd
  exact he.trans (by linarith)

/-- The exact transition error budget with the incoming family's growth retained. -/
noncomputable def parametricTransitionDebit (θ δ : ℝ) (b t : ℕ) : ℝ :=
  (2 / 3 : ℝ) * seedCapacity b t *
    ((Analytic.mixingCoefficient : ℝ) * (parametricLevel θ (graftInitialCount b t) : ℝ) ^ (-6 : ℝ) +
      (Analytic.mixingCoefficient : ℝ) * (seedTailDepth b t : ℝ) ^ (-6 : ℝ) +
      graftTransitionFailure δ b t)

/-- Both marker errors have the same fixed analytic coefficient and retain separate levels. -/
theorem parametricTransition_reference_order6 {θ δ : ℝ} (hθ : 0 < θ) (hθcap : θ ≤ 1 / 1000) (hδ
    : 0 < δ) {b : ℕ}
    (hb : 256 ^ 2 ≤ b) (t : ℕ) :
    Reference.mean (2 * seedSize b t) (fun y =>
      |Transfer.coarseSelected (graftTransitionWords δ b t) (2 * seedSize b t)
          (parametricLevel θ (graftInitialCount b t)) (parametricTransitionWords_level hθcap hb
            δ t) y -
        Reference.marker (seedTailDepth b t)
          (Reference.project (graftTransition_level_guards hb t).2.1 y)|) ≤
      (2 / 3 : ℝ) *
        ((Analytic.mixingCoefficient : ℝ) * (parametricLevel θ (graftInitialCount b t) : ℝ) ^
          (-6 : ℝ) +
          (Analytic.mixingCoefficient : ℝ) * (seedTailDepth b t : ℝ) ^ (-6 : ℝ) +
          graftTransitionFailure δ b t) := by
  have hcount : 1 ≤ graftInitialCount b t := by
    have hE := graftPrecision_ge_256 hb t
    unfold graftInitialCount
    omega
  have hold : 1 ≤ seedTailDepth b t := by
    have hs := seedSize_ge b t
    unfold seedTailDepth
    omega
  have hk := Analytic.mixingError_le_order6 (parametricLevel_pos hθ hcount)
  have ha := Analytic.mixingError_le_order6 hold
  exact (parametricTransition_reference_error hθ hθcap hδ hb t).trans (by linarith)

/-- Pair the retained transition discrepancy against any restriction of the actual seed family. -/
theorem physicalSeedHistories_parametric_debit (H : Finset (List ValuationWord))
    {θ δ : ℝ} (hθ : 0 < θ) (hθcap : θ ≤ 1 / 1000) (hδ : 0 < δ) {b t root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hH : H ⊆ physicalSeedHistories b t root) :
    (∑ a, Transfer.historyHistogram H List.flatten (seedHistorySource root)
        (2 * seedSize b t) a *
      |Transfer.coarseSelected (graftTransitionWords δ b t) (2 * seedSize b t)
          (parametricLevel θ (graftInitialCount b t))
          (parametricTransitionWords_level hθcap (by omega : 256 ^ 2 ≤ b) δ t) a -
        Reference.marker (seedTailDepth b t)
          (Reference.project (graftTransition_level_guards (by omega : 256 ^ 2 ≤ b) t).2.1 a)|) ≤
      parametricTransitionDebit θ δ b t := by
  have hsmall : 256 ^ 2 ≤ b := by omega
  have hcap := Transfer.capacity_abs_sum_le (2 * seedSize b t)
    (Transfer.historyHistogram H List.flatten (seedHistorySource root) (2 * seedSize b t))
    (fun a => Transfer.coarseSelected (graftTransitionWords δ b t) (2 * seedSize b t)
        (parametricLevel θ (graftInitialCount b t)) (parametricTransitionWords_level hθcap
          hsmall δ t) a -
      Reference.marker (seedTailDepth b t)
        (Reference.project (graftTransition_level_guards hsmall t).2.1 a))
    (physicalSeedHistories_capacity H hb hH _ (le_refl _))
  have hP : 0 ≤ seedCapacity b t :=
    (seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t)
  have hmean := mul_le_mul_of_nonneg_left (parametricTransition_reference_order6 hθ hθcap hδ
    hsmall t) hP
  apply hcap.trans
  simpa only [parametricTransitionDebit, mul_assoc, mul_left_comm] using hmean

end WordCertDensity.Construction
