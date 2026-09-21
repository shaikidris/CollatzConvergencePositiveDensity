/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalParameters

/-! # Exact radius guards and terminal endpoint shifts

The strict integer power comparison supplies the printed 229/1000 margin.
On the manuscript domain every radius subtraction is exact, and the two
endpoint shifts retain the prescribed precision and parent-dependent shift.
-/

namespace WordCertDensity.Construction

/-- The exact finite power comparison gives the manuscript's sharper logarithm guard. -/
theorem terminal_logRatio_upper : Head.logRatio < 317 / 200 := by
  apply (div_lt_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  have hp : (3 : ℝ) ^ 200 < 2 ^ 317 := by
    have hn : (3 : ℕ) ^ 200 < 2 ^ 200 * 2 ^ 117 := by decide
    have hc : ((3 ^ 200 : ℕ) : ℝ) < ((2 ^ 200 * 2 ^ 117 : ℕ) : ℝ) := Nat.cast_lt.mpr hn
    rw [show (317 : ℕ) = 200 + 117 from rfl, pow_add]
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using hc
  have h := Real.log_lt_log (by positivity : (0 : ℝ) < 3 ^ 200) hp
  rw [Real.log_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

private theorem raw_radius_lower (b : ℕ) :
    (229 / 1000 : ℝ) * b - 2 ≤
      2 * (terminalWidth b : ℝ) - terminalJ (terminalWidth b) -
        2 * (terminalPrecision b : ℝ) := by
  have hw : (3 : ℝ) * b ≤ 5 * (terminalWidth b : ℝ) + 4 := by
    exact_mod_cast (terminalWidth_bounds b).2
  have he : (100 : ℝ) * terminalPrecision b ≤ b := by
    exact_mod_cast terminalPrecision_upper b
  have hj := (terminalJ_bounds (terminalWidth b)).2
  have hlog := mul_le_mul_of_nonneg_right terminal_logRatio_upper.le
    (Nat.cast_nonneg (terminalWidth b) : (0 : ℝ) ≤ terminalWidth b)
  nlinarith

/-- The two natural subtractions defining the radius do not truncate on the terminal domain. -/
theorem terminalRadius_subtraction_guard {b : ℕ} (hb : 200 ≤ b) :
    terminalJ (terminalWidth b) + 2 * terminalPrecision b ≤ 2 * terminalWidth b := by
  have hr := raw_radius_lower b
  have hbR : (200 : ℝ) ≤ b := by exact_mod_cast hb
  have h : (terminalJ (terminalWidth b) : ℝ) + 2 * terminalPrecision b ≤
      2 * (terminalWidth b : ℝ) := by linarith
  exact_mod_cast h

/-- Cleared-integer identity for the literal radius. -/
theorem terminalRadius_balance {b : ℕ} (hb : 200 ≤ b) :
    terminalRadius b + terminalJ (terminalWidth b) + 2 * terminalPrecision b =
      2 * terminalWidth b := by
  have h := terminalRadius_subtraction_guard hb
  unfold terminalRadius
  omega

/-- Real interpretation of the integer radius, without truncated subtraction. -/
theorem terminalRadius_cast {b : ℕ} (hb : 200 ≤ b) :
    (terminalRadius b : ℝ) = 2 * (terminalWidth b : ℝ) -
      terminalJ (terminalWidth b) - 2 * (terminalPrecision b : ℝ) := by
  unfold terminalRadius
  rw [Nat.sub_sub, Nat.cast_sub (terminalRadius_subtraction_guard hb)]
  push_cast
  ring

/-- Both printed radius estimates hold with the exact floor and ceiling conventions. -/
theorem terminalRadius_bounds {b : ℕ} (hb : 200 ≤ b) :
    (229 / 1000 : ℝ) * b - 2 ≤ terminalRadius b ∧
      (terminalRadius b : ℝ) ≤ (3 / 5 : ℝ) * (2 - Head.logRatio) * b := by
  constructor
  · rw [terminalRadius_cast hb]
    exact raw_radius_lower b
  · have hw : (5 : ℝ) * terminalWidth b ≤ 3 * (b : ℝ) := by
      exact_mod_cast (terminalWidth_bounds b).1
    have hwidth : (terminalWidth b : ℝ) ≤ (3 / 5 : ℝ) * b := by linarith
    have hc : 0 ≤ 2 - Head.logRatio := by linarith [Head.logRatio_lt_eight_fifths]
    have hmul := mul_le_mul_of_nonneg_left hwidth hc
    have hj := (terminalJ_bounds (terminalWidth b)).1
    have he : (0 : ℝ) ≤ terminalPrecision b := Nat.cast_nonneg _
    rw [terminalRadius_cast hb]
    nlinarith

/-- The terminal radius is strictly positive throughout the manuscript domain. -/
theorem terminalRadius_pos {b : ℕ} (hb : 200 ≤ b) : 0 < terminalRadius b := by
  have hr := (terminalRadius_bounds hb).1
  have hbR : (200 : ℝ) ≤ b := by exact_mod_cast hb
  have h : (0 : ℝ) < terminalRadius b := by linarith
  exact_mod_cast h

/-- The exact lower and upper endpoint shifts used in the two tail events. -/
theorem terminalBarrier_endpoints {b : ℕ} (hb : 200 ≤ b) (u : ℕ) :
    terminalBarrier b u (terminalLow b) - 2 * (terminalLow b : ℤ) =
      2 * (terminalPrecision b : ℤ) + u ∧
    terminalBarrier b u (terminalHigh b) - 2 * (terminalHigh b : ℤ) =
      (u : ℤ) - 2 * terminalRadius b - 2 * terminalPrecision b := by
  have hw := terminalWidth_le b
  have hl1 : terminalLow b - b = 0 := by unfold terminalLow; omega
  have hl2 : b - terminalLow b = terminalWidth b := by unfold terminalLow; omega
  have hh1 : terminalHigh b - b = terminalWidth b := by unfold terminalHigh; omega
  have hh2 : b - terminalHigh b = 0 := by unfold terminalHigh; omega
  have hl : (terminalLow b : ℤ) = (b : ℤ) - terminalWidth b := Nat.cast_sub hw
  have hh : (terminalHigh b : ℤ) = (b : ℤ) + terminalWidth b := by simp [terminalHigh]
  have hr : (terminalRadius b : ℤ) + terminalJ (terminalWidth b) +
      2 * terminalPrecision b = 2 * terminalWidth b := by exact_mod_cast terminalRadius_balance hb
  constructor
  · rw [terminalBarrier, hl1, hl2, terminalJ_zero, hl]
    omega
  · rw [terminalBarrier, hh1, hh2, terminalJ_zero, hh]
    omega

end WordCertDensity.Construction
