/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalLogScale

/-! # Literal common cutoff endpoints and their positive linear room -/

namespace WordCertDensity.Construction

/-- Lower common endpoint in binary logarithmic coordinates. -/
noncomputable def commonLowExponent (θ Y plus : ℝ) (B : ℕ) : ℝ :=
  (Y+θ/20)*B+plus+binaryLog (terminalShellLow ⌊θ*B⌋₊ 1)

/-- Upper common endpoint with the full selected-shift radius. -/
noncomputable def commonHighExponent (θ Y minus : ℝ) (B : ℕ) : ℝ :=
  (Y-θ/20)*B+minus+binaryLog (terminalShellLow ⌊θ*B⌋₊ 1)+2*terminalRadius ⌊θ*B⌋₊

/-- Linear coefficient of the lower endpoint. -/
noncomputable def commonLowRate (θ Y : ℝ) : ℝ :=
  Y+θ/20+θ*((2-Head.logRatio)-terminalRadiusRate)

/-- Linear coefficient of the upper endpoint. -/
noncomputable def commonHighRate (θ Y : ℝ) : ℝ :=
  Y-θ/20+θ*((2-Head.logRatio)+terminalRadiusRate)

/-- Both terminal endpoint coefficients are positive and bounded independently of depth. -/
theorem terminalEndpointRates_bounds :
    0 ≤ (2-Head.logRatio)-terminalRadiusRate ∧
    (2-Head.logRatio)-terminalRadiusRate ≤ 1 ∧
    0 ≤ (2-Head.logRatio)+terminalRadiusRate ∧
    (2-Head.logRatio)+terminalRadiusRate ≤ 2 := by
  unfold terminalRadiusRate
  constructor
  · linarith [terminal_logRatio_upper]
  constructor
  · linarith [Head.one_lt_logRatio]
  constructor <;> linarith [terminal_logRatio_upper, Head.one_lt_logRatio]

/-- Positive theta supplies the exact printed linear gap between endpoint rates. -/
theorem commonRates_gap {θ Y : ℝ} (hθ : 0 < θ) (hY : 3 ≤ Y) :
    0 < commonLowRate θ Y ∧
      (179/500 : ℝ)*θ ≤ commonHighRate θ Y-commonLowRate θ Y := by
  have hp := mul_nonneg hθ.le terminalEndpointRates_bounds.1
  have hg := mul_le_mul_of_nonneg_left terminalRadiusRate_bounds.1 hθ.le
  unfold commonLowRate commonHighRate
  constructor <;> nlinarith

/-- The common lower endpoint has a uniform six-unit rounding error. -/
theorem commonLow_linear {θ Y plus : ℝ} (hθ : 0 ≤ θ) {B : ℕ} (hB : 200 ≤ ⌊θ*B⌋₊) :
    |commonLowExponent θ Y plus B-(commonLowRate θ Y*B+plus)| ≤ 6 := by
  have hd1 : (⌊θ*B⌋₊ : ℝ) ≤ θ*B := Nat.floor_le (by positivity)
  have hd2 := Nat.lt_floor_add_one (θ*(B : ℝ))
  have hlo := mul_le_mul_of_nonneg_left
    (show θ*(B : ℝ)-1 ≤ (⌊θ*B⌋₊ : ℝ) by linarith) terminalEndpointRates_bounds.1
  have hhi := mul_le_mul_of_nonneg_left hd1 terminalEndpointRates_bounds.1
  have hs := abs_le.mp (terminalShellLow_linear hB)
  unfold commonLowExponent commonLowRate
  rw [abs_le]
  constructor <;> nlinarith [terminalEndpointRates_bounds.2.1]

/-- The common upper endpoint has a uniform seven-unit rounding error. -/
theorem commonHigh_linear {θ Y minus : ℝ} (hθ : 0 ≤ θ) {B : ℕ} (hB : 200 ≤ ⌊θ*B⌋₊) :
    |commonHighExponent θ Y minus B-(commonHighRate θ Y*B+minus)| ≤ 7 := by
  have hd1 : (⌊θ*B⌋₊ : ℝ) ≤ θ*B := Nat.floor_le (by positivity)
  have hd2 := Nat.lt_floor_add_one (θ*(B : ℝ))
  have hlo := mul_le_mul_of_nonneg_left
    (show θ*(B : ℝ)-1 ≤ (⌊θ*B⌋₊ : ℝ) by linarith) terminalEndpointRates_bounds.2.2.1
  have hhi := mul_le_mul_of_nonneg_left hd1 terminalEndpointRates_bounds.2.2.1
  have hr := abs_le.mp (terminalRadius_linear hB)
  have hc := terminalCorrection_log_bounds (show 0 < ⌊θ*B⌋₊ by omega)
  unfold commonHighExponent commonHighRate
  rw [terminalShellLow_binaryLog (show 0 < ⌊θ*B⌋₊ by omega), abs_le]
  constructor <;> nlinarith [terminalEndpointRates_bounds.2.2.2]

/-- The exact radius bound gives the printed positive-theta corridor width. -/
theorem commonInterval_room {θ Y minus plus : ℝ} {B : ℕ} (hB : 200 ≤ ⌊θ*B⌋₊) :
    (179/500 : ℝ)*θ*B-5+minus-plus ≤
      commonHighExponent θ Y minus B-commonLowExponent θ Y plus B := by
  have hr := (terminalRadius_bounds hB).1
  have hd := Nat.lt_floor_add_one (θ*(B : ℝ))
  unfold commonHighExponent commonLowExponent
  nlinarith

end WordCertDensity.Construction
