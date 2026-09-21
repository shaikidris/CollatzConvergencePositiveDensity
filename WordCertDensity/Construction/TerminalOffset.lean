/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalBarrier
import WordCertDensity.Construction.OffsetEnvelope

/-! # Uniform physical offset margin for terminal words

The literal depth bound and the exact inequality (3/2)^8 < 2^5 control
every cap. A parent at height 16^b leaves relative offset below 8^(-b).
-/

namespace WordCertDensity.Construction

/-- Relative terminal offset ceiling, in a natural-power form. -/
noncomputable def terminalEta (b : ℕ) : ℝ := (1 / 8 : ℝ) ^ b

/-- Every retained terminal word has the cleared depth bound 5d <= 8b. -/
theorem terminalWord_depth_bound {b u K : ℕ} {w : ValuationWord}
    (hw : TerminalWord b u K w) : 5 * w.length ≤ 8 * b := by
  have hd := hw.2.1
  have hwidth := (terminalWidth_bounds b).1
  unfold terminalHigh at hd
  omega

/-- The geometric depth envelope is strictly below 2^b on the terminal depth range. -/
theorem terminalDepth_power_bound {b d : ℕ} (hb : 0 < b) (hd : 5 * d ≤ 8 * b) :
    (3 / 2 : ℝ) ^ d < 2 ^ b := by
  have hm : ((3 / 2 : ℝ) ^ d) ^ 5 ≤ ((3 / 2 : ℝ) ^ 8) ^ b := by
    rw [← pow_mul, ← pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have hs : ((3 / 2 : ℝ) ^ 8) ^ b < ((2 : ℝ) ^ 5) ^ b :=
    pow_lt_pow_left₀ (by norm_num) (by positivity) (by omega)
  have he : ((2 : ℝ) ^ 5) ^ b = ((2 : ℝ) ^ b) ^ 5 := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [he] at hs
  by_contra h
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 ^ b) (le_of_not_gt h) 5
  exact (not_lt_of_ge hp) (hm.trans_lt hs)

/-- Both offset bounds in N.offset hold for every retained cap. -/
theorem terminalWord_offset {b u K : ℕ} (hb : 0 < b) {w : ValuationWord}
    (hw : TerminalWord b u K w) :
    0 ≤ (w.offset : ℝ) ∧ (w.offset : ℝ) ≤ (3 / 2 : ℝ) ^ w.length - 1 ∧
      (w.offset : ℝ) < 2 ^ b := by
  have ho := Rat.cast_le (K := ℝ) |>.mpr (word_offset_le_depth w)
  norm_num only [Rat.cast_sub, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] at ho
  have hp := terminalDepth_power_bound hb (terminalWord_depth_bound hw)
  exact ⟨Rat.cast_nonneg.mpr (ValuationWord.offset_nonneg w), ho, by linarith⟩

/-- The relative offset ceiling is positive and strictly below one at every positive size. -/
theorem terminalEta_bounds {b : ℕ} (hb : 0 < b) : 0 < terminalEta b ∧ terminalEta b < 1 := by
  constructor
  · unfold terminalEta
    positivity
  · have h := pow_lt_pow_left₀ (by norm_num : (1 / 8 : ℝ) < 1)
      (by norm_num : (0 : ℝ) ≤ 1 / 8) (by omega : b ≠ 0)
    simpa only [one_pow, terminalEta] using h

/-- The parent-height recipe absorbs the binary offset envelope exactly. -/
theorem terminalEta_height (b : ℕ) : terminalEta b * (16 : ℝ) ^ b = 2 ^ b := by
  rw [terminalEta, ← mul_pow]
  norm_num

/-- Every allowed parent has the strict relative offset margin used by the sharp shell. -/
theorem terminalWord_relative_offset {b u K : ℕ} (hb : 0 < b) {w : ValuationWord}
    (hw : TerminalWord b u K w) {y : ℝ} (hy : (16 : ℝ) ^ b ≤ y) :
    (w.offset : ℝ) / y < terminalEta b := by
  have hyp : 0 < y := (by positivity : (0 : ℝ) < 16 ^ b).trans_le hy
  apply (div_lt_iff₀ hyp).mpr
  have h := mul_le_mul_of_nonneg_left hy (terminalEta_bounds hb).1.le
  rw [terminalEta_height] at h
  exact (terminalWord_offset hb hw).2.2.trans_le h

end WordCertDensity.Construction
