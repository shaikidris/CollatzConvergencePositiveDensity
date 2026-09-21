/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalIdentity

/-! # Literal finite terminal budget at positive theta

This is the manuscript's scalar budget, with its original precision cap and
the fixed incoming coefficient. The pointwise physical theorem uses explicit
finite-stage guards; their eventual validity and the decay limit remain consumers.
-/

namespace WordCertDensity.Construction

/-- Literal terminal payment error from the predeclared parameterized interface. -/
noncomputable def terminalPaymentError (b t : ℕ) (θ : ℝ) (B : ℕ) : ℝ :=
  let d := ⌊θ*B⌋₊
  let k := parametricLevel θ B
  (2/3 : ℝ) * seedCapacity b t * ((B : ℝ)+1)^2 *
    ((2 : ℝ)^(b+1)+2) * (2*terminalRadius d+1) *
    (2*Analytic.mixingCoefficient/(k : ℝ)^6 + 2*Real.exp (-(d : ℝ)/64000) +
      (2 : ℝ)^(-((terminalPrecision d : ℤ)+1)))

/-- The full scalar budget is nonnegative at every parameter and every finite stage. -/
theorem terminalPaymentError_nonneg (b t : ℕ) (θ : ℝ) (B : ℕ) :
    0 ≤ terminalPaymentError b t θ B := by
  have hP := (seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t)
  have hC := Analytic.mixingCoefficient_pos.le
  unfold terminalPaymentError
  positivity

/-- The exact original geometric cap loss has the same integer-exponent notation. -/
theorem terminalPrecision_tail_eq (d : ℕ) :
    (1/2 : ℝ)^(terminalPrecision d+1) = (2 : ℝ)^(-((terminalPrecision d : ℤ)+1)) := by
  rw [zpow_neg, zpow_add₀ (by norm_num), zpow_natCast, zpow_one, pow_succ, div_pow]
  simp only [one_pow, one_div, mul_inv_rev]
  ring

/-- At every guarded finite stage the physical marked difference obeys the literal budget. -/
theorem selectedTerminalMark_payment_budget {θ L X : ℝ} {b t j root : ℕ}
    (hb : 32^5 ≤ b) (hθ : 0 < θ) (hθcap : θ ≤ 1/1000)
    (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hd : 200 ≤ ⌊θ * macroCount L (graftInitialCount b t) j⌋₊)
    (hk : 1 ≤ parametricLevel θ (macroCount L (graftInitialCount b t) j))
    (hboundary : terminalBoundary ⌊θ * macroCount L (graftInitialCount b t) j⌋₊
      (parametricLevel θ (macroCount L (graftInitialCount b t) j))
      (macroCount L (graftInitialCount b t) j) ≤ 1)
    (hshell : ∀ r ∈ physicalGraftRecords L (θ/20) b t j root,
      let d := ⌊θ * macroCount L (graftInitialCount b t) j⌋₊
      let y := graftRecordSource root r
      16^d ≤ y ∧ terminalShellLow d y < X ∧
        X ≤ (2 : ℝ)^(2*terminalRadius d)*terminalShellLow d y) :
    let B := macroCount L (graftInitialCount b t) j
    let d := ⌊θ*B⌋₊
    let k := parametricLevel θ B
    |selectedTerminalMark L (θ/20) X b t j root d (terminalPrecision d) k -
      physicalParametricGraftMark θ L (θ/20) b t j root| ≤ terminalPaymentError b t θ B := by
  have h := selectedTerminalMark_payment hb (by positivity : 0 ≤ θ/20)
    (by linarith : 2*(θ/20) ≤ 1) hpaid hd hk
    (terminalPrecision ⌊θ * macroCount L (graftInitialCount b t) j⌋₊) hshell
  have hp := terminalPartitionDebit_paid b t (macroCount L (graftInitialCount b t) j)
    ⌊θ * macroCount L (graftInitialCount b t) j⌋₊
    (terminalPrecision ⌊θ * macroCount L (graftInitialCount b t) j⌋₊) hk hboundary
  simpa only [terminalPaymentError, terminalPrecision_tail_eq] using h.trans hp

end WordCertDensity.Construction
