/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.ParametricTransitionDecay
import WordCertDensity.Construction.ParametricContinuation
import WordCertDensity.Construction.ParametricIdentity
import WordCertDensity.Construction.GraftError

/-! # Full uniform physical graft error at positive theta

Both complete error budgets are paid before the splice. The error vanishes
with the splice uniformly over guarded roots and continuation stages.
The baseline physical selectors are retained; revised selectors remain S04.
-/

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- The literal transition debit plus the complete incoming-weighted continuation tail. -/
noncomputable def parametricTotalError (θ L δ : ℝ) (b t : ℕ) : ℝ :=
  parametricTransitionDebit θ δ b t + parametricContinuationTail θ L b t

/-- The complete error exactly specializes to the already built fixed-scale error. -/
theorem parametricTotalError_fixed (L δ : ℝ) (b t : ℕ) :
    parametricTotalError (1 / 1000) L δ b t = graftTotalError L δ b t := by
  simp only [parametricTotalError, graftTotalError, parametricTransitionDebit_fixed,
    parametricContinuationTail_fixed]

/-- The full graft error is nonnegative for every allowed macro scale. -/
theorem parametricTotalError_nonneg (θ : ℝ) {L : ℝ} (hL : 0 ≤ L) (δ : ℝ) (b t : ℕ) :
    0 ≤ parametricTotalError θ L δ b t := by
  have ht := parametricTransitionDebit_nonneg θ δ b t
  have hK := parametricGraftVariationConstant_nonneg θ hL b
  have hP := graftTailWeight_nonneg b t
  unfold parametricTotalError parametricContinuationTail
  positivity

/-- Both complete error budgets tend to zero with the same actual splice parameter. -/
theorem parametricTotalError_tendsto (L : ℝ) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) {b : ℕ}
    (hb : 256 ^ 2 ≤ b) : Tendsto (parametricTotalError θ L δ b) atTop (𝓝 0) := by
  change Tendsto (fun t => parametricTransitionDebit θ δ b t + parametricContinuationTail θ L b
    t) atTop (𝓝 0)
  simpa only [add_zero] using
    (parametricTransitionDebit_tendsto hθ hδ hb).add (parametricContinuationTail_tendsto θ L hb)

/-- The physical graft stays within its full vanishing error of the original seed mark. -/
theorem eventually_physicalParametricGraftMark_error {θ L δ : ℝ} {b : ℕ}
    (hθ : 0 < θ) (hθcap : θ ≤ 1 / 1000) (hb : 32 ^ 5 ≤ b) (hL : 0 < L) (hδ : 0 < δ) (hsmall : 2
      * δ ≤ 1)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) :
    ∀ᶠ t in atTop, ∀ root, 16 ^ b ≤ root → ∀ j,
      |physicalParametricGraftMark θ L δ b t j root - physicalSeedMark b t root| ≤
        parametricTotalError θ L δ b t := by
  filter_upwards [eventually_physicalParametricGraftMark_continuation hθ hθcap hb hL hδ hsmall hpay,
    graftOffsetAbsorption_eventually (by omega : 100 ≤ b)] with t htail hoff root hroot j
  have hcont := (htail root hroot).2 j
  have htrans := physicalParametricGraftMark_transition_debit L hθ hδ hθcap hb hroot hoff
  calc
    _ ≤ |physicalParametricGraftMark θ L δ b t j root - physicalParametricGraftMark θ L δ b t 0
      root| +
        |physicalParametricGraftMark θ L δ b t 0 root - physicalSeedMark b t root| := abs_sub_le
          _ _ _
    _ ≤ parametricContinuationTail θ L b t + parametricTransitionDebit θ δ b t := add_le_add
      hcont htrans
    _ = _ := by rw [parametricTotalError, add_comm]

end WordCertDensity.Construction
