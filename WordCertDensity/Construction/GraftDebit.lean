/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftTransition
import WordCertDensity.Construction.SeedCapacity
import WordCertDensity.Transfer.CapacityPairing

/-! # The full incoming-weighted transition debit

The actual seed histogram is paired at its allowed enlarged conductor.
Both order-six mixing errors, the unconditioned rejection cost and the
complete incoming capacity remain. Physical realization of compatible
transition extensions is a subsequent hybrid-history obligation.
-/

namespace WordCertDensity.Construction

open scoped Classical

/-- The exact transition error budget with the incoming family's growth retained. -/
noncomputable def graftTransitionDebit (δ : ℝ) (b t : ℕ) : ℝ :=
  (2 / 3 : ℝ) * seedCapacity b t *
    ((Analytic.mixingCoefficient : ℝ) * (macroLevel (graftInitialCount b t) : ℝ) ^ (-6 : ℝ) +
      (Analytic.mixingCoefficient : ℝ) * (seedTailDepth b t : ℝ) ^ (-6 : ℝ) +
      graftTransitionFailure δ b t)

/-- Both marker errors have the same fixed analytic coefficient and retain separate levels. -/
theorem graftTransition_reference_order6 {δ : ℝ} (hδ : 0 < δ) {b : ℕ}
    (hb : 256 ^ 2 ≤ b) (t : ℕ) :
    Reference.mean (2 * seedSize b t) (fun y =>
      |Transfer.coarseSelected (graftTransitionWords δ b t) (2 * seedSize b t)
          (macroLevel (graftInitialCount b t)) (graftTransitionWords_level hb δ t) y -
        Reference.marker (seedTailDepth b t)
          (Reference.project (graftTransition_level_guards hb t).2.1 y)|) ≤
      (2 / 3 : ℝ) *
        ((Analytic.mixingCoefficient : ℝ) * (macroLevel (graftInitialCount b t) : ℝ) ^ (-6 : ℝ) +
          (Analytic.mixingCoefficient : ℝ) * (seedTailDepth b t : ℝ) ^ (-6 : ℝ) +
          graftTransitionFailure δ b t) := by
  have hold : 1 ≤ seedTailDepth b t := by
    have hs := seedSize_ge b t
    unfold seedTailDepth
    omega
  have hk := Analytic.mixingError_le_order6 (graftTransition_level_guards hb t).1
  have ha := Analytic.mixingError_le_order6 hold
  exact (graftTransition_reference_error hδ hb t).trans (by linarith)

/-- Pair the retained transition discrepancy against any restriction of the actual seed family. -/
theorem physicalSeedHistories_graft_debit (H : Finset (List ValuationWord))
    {δ : ℝ} (hδ : 0 < δ) {b t root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hH : H ⊆ physicalSeedHistories b t root) :
    (∑ a, Transfer.historyHistogram H List.flatten (seedHistorySource root)
        (2 * seedSize b t) a *
      |Transfer.coarseSelected (graftTransitionWords δ b t) (2 * seedSize b t)
          (macroLevel (graftInitialCount b t))
          (graftTransitionWords_level (by omega : 256 ^ 2 ≤ b) δ t) a -
        Reference.marker (seedTailDepth b t)
          (Reference.project (graftTransition_level_guards (by omega : 256 ^ 2 ≤ b) t).2.1 a)|) ≤
      graftTransitionDebit δ b t := by
  have hsmall : 256 ^ 2 ≤ b := by omega
  have hcap := Transfer.capacity_abs_sum_le (2 * seedSize b t)
    (Transfer.historyHistogram H List.flatten (seedHistorySource root) (2 * seedSize b t))
    (fun a => Transfer.coarseSelected (graftTransitionWords δ b t) (2 * seedSize b t)
        (macroLevel (graftInitialCount b t)) (graftTransitionWords_level hsmall δ t) a -
      Reference.marker (seedTailDepth b t)
        (Reference.project (graftTransition_level_guards hsmall t).2.1 a))
    (physicalSeedHistories_capacity H hb hH _ (le_refl _))
  have hP : 0 ≤ seedCapacity b t :=
    (seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t)
  have hmean := mul_le_mul_of_nonneg_left (graftTransition_reference_order6 hδ hsmall t) hP
  apply hcap.trans
  simpa only [graftTransitionDebit, mul_assoc, mul_left_comm] using hmean

end WordCertDensity.Construction
