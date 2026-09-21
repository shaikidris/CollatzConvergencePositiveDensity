/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.ClockMargin
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! # Exact arithmetic for the illustrative ordinary clock 10.431 -/

namespace WordCertDensity.Construction

/-- Three atanh terms give the printed lower bound, strictly paid by the fourth. -/
theorem clock_log_four_thirds_lower : (72526/252105 : ℝ) < Real.log (4/3 : ℝ) := by
  have h := Real.sum_range_le_log_div (by norm_num : (0 : ℝ)≤1/7)
    (by norm_num : (1/7 : ℝ)<1) 4
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- The exact rational checkpoint displayed in the manuscript. -/
theorem clockCheckpoint_bound :
    9/((3-1/20000)*Real.log (4/3 : ℝ))+
      (1/20000+481/100000)/((3-1/20000)*Real.log 2) <
        (1747479290400/167532267749 : ℝ) ∧
    (1747479290400/167532267749 : ℝ) < 10431/1000 := by
  have h1 : 9/((3-1/20000)*Real.log (4/3 : ℝ)) <
      9/((3-1/20000)*(72526/252105 : ℝ)) := by
    apply div_lt_div_of_pos_left (by norm_num) (by norm_num)
    nlinarith [clock_log_four_thirds_lower]
  have h2 : (1/20000+481/100000)/((3-1/20000)*Real.log 2) <
      (1/20000+481/100000)/((3-1/20000)*(693/1000 : ℝ)) := by
    apply div_lt_div_of_pos_left (by norm_num) (by norm_num)
    nlinarith [Head.log_two_lower]
  constructor
  · norm_num at h1 h2
    linarith
  · norm_num

/-- At theta=1/1000, the mean-three formula equals the printed checkpoint expression. -/
theorem terminalClock_at_three :
    terminalClockRate 3 (criticalClock*Real.log 2*3) (1/1000) =
      9/((3-1/20000)*Real.log (4/3 : ℝ))+
        (1/20000+481/100000)/((3-1/20000)*Real.log 2) := by
  have h2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne'
  have h4 : Real.log (4/3 : ℝ) ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ)<4/3)).ne'
  unfold terminalClockRate criticalClock
  field_simp
  ring

/-- Increasing the stopped mean above three can only improve the fixed checkpoint. -/
theorem terminalClock_fixed_bound {Y R : ℝ} (hY : 3 ≤ Y)
    (hR : R=criticalClock*Real.log 2*Y) :
    terminalClockRate Y R (1/1000) < 10431/1000 := by
  have hd := terminalClock_denominator_pos (Y := 3) (θ := 1/1000) (by norm_num) (by norm_num)
  have hden : Real.log 2*(3-(1/1000)/20) ≤ Real.log 2*(Y-(1/1000)/20) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith [Head.log_two_lower])
  have hn : 0 ≤ (1/1000 : ℝ)*((1+criticalClock*Real.log 2)/20+481/100) := by
    have hp := mul_pos criticalClock_bounds.1 (Real.log_pos (by norm_num : (1 : ℝ)<2))
    nlinarith
  have hm := div_le_div_of_nonneg_left hn hd hden
  have hi := terminalClock_margin_identity hY hR (by norm_num : (1/1000 : ℝ)≤1/1000)
  have hj := terminalClock_margin_identity (Y := 3) (R := criticalClock*Real.log 2*3)
    (θ := 1/1000) (by norm_num) rfl (by norm_num)
  have hthree := terminalClock_at_three
  have hb := clockCheckpoint_bound.1.trans clockCheckpoint_bound.2
  linarith

end WordCertDensity.Construction
