/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalDecayBound

/-! # Uniform vanishing terminal payment at fixed positive theta

The coefficient is fixed before the stage, root and cutoff. Its literal error
is nonnegative and tends to zero along the actual macro schedule. Eventual
finite guards discharge the physical payment theorem simultaneously for all
roots and all cutoffs satisfying the parent shell conditions.
-/

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- The complete original error tends to zero with the original-block count. -/
theorem terminalPaymentError_tendsto (b t : ℕ) {θ : ℝ}
    (hθ : 0 < θ) (hcap : θ ≤ 1/1000) :
    Tendsto (terminalPaymentError b t θ) atTop (𝓝 0) := by
  have hmajor : Tendsto (fun B : ℕ => terminalPaymentCoefficient b t θ/(B : ℝ)^3)
      atTop (𝓝 0) := by
    simpa [div_eq_mul_inv, inv_pow] using
      ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 3).const_mul
        (terminalPaymentCoefficient b t θ)
  apply squeeze_zero' (Eventually.of_forall (terminalPaymentError_nonneg b t θ)) ?_ hmajor
  filter_upwards [eventually_terminalStage_guards hθ hcap, eventually_ge_atTop 1] with B h hB
  exact terminalPaymentError_polynomial b t hθ hcap hB h.1

/-- Original physical terminal marks obey one vanishing budget uniformly in root and cutoff. -/
theorem selectedTerminalPayment (L θ : ℝ) (b t : ℕ)
    (hb : 32^5 ≤ b) (hL : 0 < L) (hθ : 0 < θ) (hcap : θ ≤ 1/1000)
    (hpaid : graftOffsetAbsorption b t ≤ 1) :
    let error := fun j => terminalPaymentError b t θ
      (macroCount L (graftInitialCount b t) j)
    (∀ j, 0 ≤ error j) ∧ Tendsto error atTop (𝓝 0) ∧
      ∀ᶠ j in atTop, ∀ root : ℕ, 16^b ≤ root →
        let B := macroCount L (graftInitialCount b t) j
        let d := ⌊θ*B⌋₊
        let k := parametricLevel θ B
        ∀ X : ℝ,
        (∀ r ∈ physicalGraftRecords L (θ/20) b t j root,
          let y := graftRecordSource root r
          16^d ≤ y ∧ terminalShellLow d y < X ∧
            X ≤ (2 : ℝ)^(2*terminalRadius d)*terminalShellLow d y) →
        |selectedTerminalMark L (θ/20) X b t j root d (terminalPrecision d) k -
          physicalParametricGraftMark θ L (θ/20) b t j root| ≤ error j := by
  dsimp only
  have hcount := macroCount_tendsto hL (graftInitialCount b t)
  refine ⟨fun j => terminalPaymentError_nonneg b t θ _,
    (terminalPaymentError_tendsto b t hθ hcap).comp hcount, ?_⟩
  filter_upwards [hcount.eventually (eventually_terminalStage_guards hθ hcap)]
    with j hj root _hroot X hshell
  exact selectedTerminalMark_payment_budget hb hθ hcap hpaid hj.1 hj.2.1 hj.2.2 hshell

end WordCertDensity.Construction
