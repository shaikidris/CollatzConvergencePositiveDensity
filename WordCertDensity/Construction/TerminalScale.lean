/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalPhysical

/-! # Terminal slope bounds from literal ceiling errors

The two ceiling errors lie in [0,1), and the final overshoot is at most one.
The inverse physical slope therefore lies between one half and four times
the terminal scale, with no approximation of the logarithmic constant.
-/

namespace WordCertDensity.Construction

/-- The positive multiplicative scale before the relative offset correction. -/
noncomputable def terminalScale (b u : ℕ) : ℝ :=
  (4 : ℝ) ^ b * 2 ^ u / (2 ^ terminalRadius b * 3 ^ b)

/-- Every terminal multiplicative scale is strictly positive. -/
theorem terminalScale_pos (b u : ℕ) : 0 < terminalScale b u := by
  unfold terminalScale
  positivity

/-- The selected shift acts by its exact binary factor. -/
theorem terminalScale_shift (b u : ℕ) :
    terminalScale b u = 2 ^ u * terminalScale b 0 := by
  simp only [terminalScale, pow_zero, mul_one]
  ring

/-- The logarithm of the scale retains the literal integer shift and radius. -/
theorem terminalScale_log (b u : ℕ) :
    Real.log (terminalScale b u) =
      ((2 - Head.logRatio) * b + u - terminalRadius b) * Real.log 2 := by
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [terminalScale, Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  simp only [Real.log_pow, h4]
  unfold Head.logRatio
  field_simp
  ring

/-- The two ceiling errors give the exact displacement corridor for reduced terminal words. -/
theorem terminalWord_displacement {b u : ℕ} {w : ValuationWord}
    (hw : TerminalWord b u 1 w) :
    (2 - Head.logRatio) * b + u - terminalRadius b - 1 ≤ displacement w ∧
      displacement w ≤ (2 - Head.logRatio) * b + u - terminalRadius b + 2 := by
  have hlo : (2 : ℝ) * b + terminalJ (w.length - b) - terminalJ (b - w.length) + u -
      terminalRadius b ≤ w.total := by
    have h := sub_nonneg.mp hw.2.2.2.1
    unfold terminalBarrier at h
    exact_mod_cast h
  have hhi : (w.total : ℝ) - ((2 : ℝ) * b + terminalJ (w.length - b) -
      terminalJ (b - w.length) + u - terminalRadius b) ≤ 1 := by
    have h := hw.2.2.2.2
    unfold terminalBarrier at h
    exact_mod_cast h
  have hr := terminalJ_bounds (w.length - b)
  have hl := terminalJ_bounds (b - w.length)
  have hbal : (w.length : ℝ) + (b - w.length : ℕ) = (b : ℝ) + (w.length - b : ℕ) := by
    exact_mod_cast (show w.length + (b - w.length) = b + (w.length - b) by omega)
  have hm := congrArg (fun t : ℝ => Head.logRatio * t) hbal
  unfold displacement
  constructor <;> nlinarith [hr.1, hr.2, hl.1, hl.2]

/-- The actual inverse slope is between the two printed scale factors. -/
theorem terminalWord_inverseSlope {b u : ℕ} {w : ValuationWord}
    (hw : TerminalWord b u 1 w) :
    terminalScale b u / 2 ≤ 1 / Transfer.weight w ∧
      1 / Transfer.weight w ≤ 4 * terminalScale b u := by
  have hp := terminalScale_pos b u
  have hwp := one_div_pos.mpr (Transfer.weight_pos w)
  have hlog : Real.log (1 / Transfer.weight w) = displacement w * Real.log 2 := by
    rw [one_div, Real.log_inv, log_weight_eq]
    ring
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have hd := terminalWord_displacement hw
  constructor
  · apply (Real.log_le_log_iff (by positivity) hwp).mp
    rw [Real.log_div (ne_of_gt hp) (by norm_num), terminalScale_log, hlog]
    have h := mul_le_mul_of_nonneg_right hd.1 h2
    nlinarith
  · apply (Real.log_le_log_iff hwp (by positivity)).mp
    rw [Real.log_mul (by norm_num) (ne_of_gt hp), terminalScale_log, hlog, h4]
    have h := mul_le_mul_of_nonneg_right hd.2 h2
    nlinarith

end WordCertDensity.Construction
