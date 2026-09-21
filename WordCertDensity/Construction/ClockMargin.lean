/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.StoppedMeans
import WordCertDensity.Targets

/-! # Strict positive-parameter ordinary clock margin -/

namespace WordCertDensity.Construction

/-- The terminal clock coefficient with both original error allowances. -/
noncomputable def terminalClockRate (Y R θ : ℝ) : ℝ :=
  (R+θ/20+(481/100)*θ)/(Real.log 2*(Y-θ/20))

/-- Elementary logarithmic guards locate the reference coefficient. -/
theorem criticalClock_bounds : 0 < criticalClock ∧ criticalClock < 11 := by
  have hl : 0 < Real.log (4/3 : ℝ) := by linarith [Head.log_four_thirds_lower]
  constructor
  · exact div_pos (by norm_num) hl
  · apply (div_lt_iff₀ hl).mpr
    linarith [Head.log_four_thirds_lower]

/-- The actual stopped expectations satisfy the exact reference ratio identity. -/
theorem stoppedMean_clock_identity :
    stoppedExpectation (fun w => w.ordinaryCost) =
      criticalClock*Real.log 2*stoppedExpectation displacement := by
  have hd : 0 < Real.log 2*stoppedExpectation displacement :=
    mul_pos (by linarith [Head.log_two_lower])
      (by linarith [stoppedExpectation_displacement_lower])
  have h := (div_eq_iff hd.ne').mp stoppedExpectation_clock_ratio
  simpa only [criticalClock, mul_assoc] using h

/-- Denominator positivity retains the full theta domain. -/
theorem terminalClock_denominator_pos {Y θ : ℝ} (hY : 3 ≤ Y) (hθ : θ ≤ 1/1000) :
    0 < Real.log 2*(Y-θ/20) :=
  mul_pos (by linarith [Head.log_two_lower]) (by linarith)

/-- Subtracting the reference clock gives the exact parameterized margin. -/
theorem terminalClock_margin_identity {Y R θ : ℝ} (hY : 3 ≤ Y)
    (hR : R=criticalClock*Real.log 2*Y) (hθ : θ ≤ 1/1000) :
    terminalClockRate Y R θ-criticalClock =
      θ*((1+criticalClock*Real.log 2)/20+481/100)/(Real.log 2*(Y-θ/20)) := by
  have hd := (terminalClock_denominator_pos hY hθ).ne'
  apply (eq_div_iff hd).mpr
  rw [sub_mul, terminalClockRate, div_mul_cancel₀ _ hd, hR]
  ring

/-- Every positive theta gives a strict loss smaller than three theta. -/
theorem terminalClock_margin {Y R θ : ℝ} (hY : 3 ≤ Y)
    (hR : R=criticalClock*Real.log 2*Y) (hθ : 0 < θ) (hcap : θ ≤ 1/1000) :
    0 < terminalClockRate Y R θ-criticalClock ∧
      terminalClockRate Y R θ-criticalClock < 3*θ := by
  have hd := terminalClock_denominator_pos hY hcap
  have hl : (2/3 : ℝ) < Real.log 2 := by linarith [Head.log_two_lower]
  have hu : Real.log 2 < (7/10 : ℝ) := by linarith [Head.log_two_upper]
  have hc := criticalClock_bounds
  have hn0 : 0 < (1+criticalClock*Real.log 2)/20+481/100 := by
    nlinarith [mul_pos hc.1 (by linarith : 0 < Real.log 2)]
  have hn1 : (1+criticalClock*Real.log 2)/20+481/100 < 1049/200 := by
    nlinarith [mul_lt_mul_of_pos_right hc.2 (by linarith : 0 < Real.log 2)]
  have hy : 3-1/20000 ≤ Y-θ/20 := by linarith
  have hd1 : 6-1/10000 < 3*(Real.log 2*(Y-θ/20)) := by
    nlinarith [mul_lt_mul_of_pos_right hl (by linarith : 0 < Y-θ/20)]
  rw [terminalClock_margin_identity hY hR hcap]
  refine ⟨div_pos (mul_pos hθ hn0) hd, ?_⟩
  apply (div_lt_iff₀ hd).mpr
  have hm := mul_lt_mul_of_pos_left (show
    (1+criticalClock*Real.log 2)/20+481/100 < 3*(Real.log 2*(Y-θ/20)) by linarith) hθ
  nlinarith

/-- The manuscript's parameter margin with the actual stopped means discharged. -/
theorem stoppedMean_terminalClock_margin {θ : ℝ} (hθ : 0 < θ) (hcap : θ ≤ 1/1000) :
    0 < terminalClockRate (stoppedExpectation displacement)
      (stoppedExpectation (fun w => w.ordinaryCost)) θ-criticalClock ∧
    terminalClockRate (stoppedExpectation displacement)
      (stoppedExpectation (fun w => w.ordinaryCost)) θ-criticalClock < 3*θ :=
  terminalClock_margin stoppedExpectation_displacement_lower stoppedMean_clock_identity hθ hcap

end WordCertDensity.Construction
