/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalShell
import WordCertDensity.Construction.TerminalRadius
import WordCertDensity.Construction.GraftLogBounds

/-! # Bounded rounding losses in the literal terminal logarithmic scale -/

namespace WordCertDensity.Construction

/-- Linear coefficient of the radius before its bounded integer rounding errors. -/
noncomputable def terminalRadiusRate : ℝ := (3/5)*(2-Head.logRatio)-1/50

/-- The exact reference logarithm gives a positive, bounded radius coefficient. -/
theorem terminalRadiusRate_bounds : 229/1000 ≤ terminalRadiusRate ∧ terminalRadiusRate ≤ 1 := by
  unfold terminalRadiusRate
  constructor <;> linarith [terminal_logRatio_upper, Head.one_lt_logRatio]

/-- The radius remains within three units of its linear coefficient. -/
theorem terminalRadius_linear {b : ℕ} (hb : 200 ≤ b) :
    |(terminalRadius b : ℝ)-terminalRadiusRate*b| ≤ 3 := by
  have hw1 : (5 : ℝ)*terminalWidth b ≤ 3*b := by exact_mod_cast (terminalWidth_bounds b).1
  have hw2 : (3 : ℝ)*b ≤ 5*terminalWidth b+4 := by exact_mod_cast (terminalWidth_bounds b).2
  have hp1 : (100 : ℝ)*terminalPrecision b ≤ b := by exact_mod_cast terminalPrecision_upper b
  have hp2 : (b : ℝ) < 100*terminalPrecision b+100 := by
    exact_mod_cast (show b < 100*terminalPrecision b+100 by unfold terminalPrecision; omega)
  have hc : 0 ≤ 2-Head.logRatio := by linarith [Head.logRatio_lt_eight_fifths]
  have hlow := mul_le_mul_of_nonneg_left
    (show (3/5 : ℝ)*b-1 ≤ terminalWidth b by linarith) hc
  have hhigh := mul_le_mul_of_nonneg_left
    (show (terminalWidth b : ℝ) ≤ (3/5)*b by linarith) hc
  obtain ⟨hj1,hj2⟩ := terminalJ_bounds (terminalWidth b)
  rw [terminalRadius_cast hb]
  unfold terminalRadiusRate
  rw [abs_le]
  constructor <;> nlinarith [Head.one_lt_logRatio]

/-- The relative correction stays in a fixed positive interval once the depth is positive. -/
theorem terminalEta_le_eighth {b : ℕ} (hb : 0 < b) : terminalEta b ≤ 1/8 := by
  have hp : (1/8 : ℝ)^(b-1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  unfold terminalEta
  conv_lhs => rw [show b=b-1+1 by omega, pow_succ]
  nlinarith

/-- The logarithmic offset correction lies between minus one and zero. -/
theorem terminalCorrection_log_bounds {b : ℕ} (hb : 0 < b) :
    -1 ≤ binaryLog (1-terminalEta b) ∧ binaryLog (1-terminalEta b) ≤ 0 := by
  have he := terminalEta_le_eighth hb
  have he0 := (terminalEta_bounds hb).1
  have hlo := binaryLog_mono (by norm_num : (0 : ℝ)<1/2)
    (show (1/2 : ℝ) ≤ 1-terminalEta b by linarith)
  have hhi := binaryLog_mono (by linarith : 0 < 1-terminalEta b)
    (show 1-terminalEta b ≤ 1 by linarith)
  have hhalf : binaryLog (1/2) = -1 := by
    simp [binaryLog, ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ)<2))]
  have hone : binaryLog 1 = 0 := by simp [binaryLog]
  exact ⟨by simpa only [hhalf] using hlo, by simpa only [hone] using hhi⟩

/-- Exact logarithm of the lower shell, retaining the radius and offset correction. -/
theorem terminalShellLow_binaryLog {b : ℕ} (hb : 0 < b) :
    binaryLog (terminalShellLow b 1) =
      (2-Head.logRatio)*b-terminalRadius b+binaryLog (1-terminalEta b)-1 := by
  have hpos : 0 < 1-terminalEta b := sub_pos.mpr (terminalEta_bounds hb).2
  have hlog : Real.log (terminalShellLow b 1) =
      Real.log (1-terminalEta b)+((2-Head.logRatio)*b-terminalRadius b)*Real.log 2-Real.log 2 := by
    rw [terminalShellLow, mul_one,
      Real.log_div (mul_pos hpos (terminalScale_pos b 0)).ne' (by norm_num),
      Real.log_mul hpos.ne' (terminalScale_pos b 0).ne', terminalScale_log]
    simp
  unfold binaryLog
  rw [hlog]
  field_simp
  ring

/-- The full shell logarithm differs from its linear part by at most five. -/
theorem terminalShellLow_linear {b : ℕ} (hb : 200 ≤ b) :
    |binaryLog (terminalShellLow b 1)-((2-Head.logRatio)-terminalRadiusRate)*b| ≤ 5 := by
  have hr := abs_le.mp (terminalRadius_linear hb)
  have he := terminalCorrection_log_bounds (show 0 < b by omega)
  rw [terminalShellLow_binaryLog (show 0 < b by omega), abs_le]
  constructor <;> linarith

end WordCertDensity.Construction
