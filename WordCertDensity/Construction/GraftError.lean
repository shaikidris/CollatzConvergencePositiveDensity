/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftTransitionPolynomial
import WordCertDensity.Construction.GraftContinuationTail
import WordCertDensity.Construction.GraftIdentity

/-! # The full uniform physical graft error

The actual transition loss and the complete continuation variation are
paid together. The error tends to zero with the splice, and one late splice
threshold works simultaneously for every guarded root and every stage.
-/

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- The literal transition debit plus the complete incoming-weighted continuation tail. -/
noncomputable def graftTotalError (L δ : ℝ) (b t : ℕ) : ℝ :=
  graftTransitionDebit δ b t + graftContinuationTail L b t

/-- The full graft error is nonnegative for every allowed macro scale. -/
theorem graftTotalError_nonneg {L : ℝ} (hL : 0 ≤ L) (δ : ℝ) (b t : ℕ) :
    0 ≤ graftTotalError L δ b t := by
  have ht := graftTransitionDebit_nonneg δ b t
  have hK := graftVariationConstant_nonneg hL b
  have hP := graftTailWeight_nonneg b t
  unfold graftTotalError graftContinuationTail
  positivity

/-- Both complete error budgets tend to zero with the same actual splice parameter. -/
theorem graftTotalError_tendsto (L : ℝ) {δ : ℝ} (hδ : 0 < δ) {b : ℕ}
    (hb : 256 ^ 2 ≤ b) : Tendsto (graftTotalError L δ b) atTop (𝓝 0) := by
  change Tendsto (fun t => graftTransitionDebit δ b t + graftContinuationTail L b t) atTop (𝓝 0)
  simpa only [add_zero] using
    (graftTransitionDebit_tendsto hδ hb).add (graftContinuationTail_tendsto L hb)

/-- The physical graft stays within its full vanishing error of the original seed mark. -/
theorem eventually_physicalGraftMark_error {L δ : ℝ} {b : ℕ}
    (hb : 32 ^ 5 ≤ b) (hL : 0 < L) (hδ : 0 < δ) (hsmall : 2 * δ ≤ 1)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) :
    ∀ᶠ t in atTop, ∀ root, 16 ^ b ≤ root → ∀ j,
      |physicalGraftMark L δ b t j root - physicalSeedMark b t root| ≤ graftTotalError L δ b t := by
  filter_upwards [eventually_physicalGraftMark_continuation hb hL hδ hsmall hpay,
    graftOffsetAbsorption_eventually (by omega : 100 ≤ b)] with t htail hoff root hroot j
  have hcont := (htail root hroot).2 j
  have htrans := physicalGraftMark_transition_debit L hδ hb hroot hoff
  calc
    _ ≤ |physicalGraftMark L δ b t j root - physicalGraftMark L δ b t 0 root| +
        |physicalGraftMark L δ b t 0 root - physicalSeedMark b t root| := abs_sub_le _ _ _
    _ ≤ graftContinuationTail L b t + graftTransitionDebit δ b t := add_le_add hcont htrans
    _ = _ := by rw [graftTotalError, add_comm]

end WordCertDensity.Construction
