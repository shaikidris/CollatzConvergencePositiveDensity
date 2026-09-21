/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.ExactVariationTail

/-! # Integer denominators for the startup residual -/

namespace WordCertDensity.Construction

/-- The integer numerator U_n of the manuscript's exact tail. -/
def cubicTailNumerator (n a d : ℕ) : ℕ :=
  d * ((n + 1) ^ 3 * (d - a) ^ 3 + 3 * (n + 1) ^ 2 * a * (d - a) ^ 2 +
    3 * (n + 1) * a * (d + a) * (d - a) + a * (d ^ 2 + 4 * a * d + a ^ 2))

/-- Clearing the rational tail gives exactly the integer numerator and denominator. -/
theorem cubicTailFormula_integer (n a d : ℕ) (had : a < d) :
    cubicTailFormula n ((a : ℝ) / d) =
      (a : ℝ) ^ n * cubicTailNumerator n a d /
        ((d : ℝ) ^ n * ((d - a : ℕ) : ℝ) ^ 4) := by
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_le a |>.trans_lt had))
  have hda : (d : ℝ) - a ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast had.ne')
  unfold cubicTailFormula cubicTailNumerator
  push_cast [Nat.cast_sub had.le]
  rw [div_pow]
  field_simp

/-- A positive residual with integer numerator is at least one denominator unit. -/
theorem residual_integer_lower (A B : ℕ) (hB : 0 < B)
    (hpos : 0 < (24 / 25 : ℝ) - (A : ℝ) / B) :
    1 / (25 * (B : ℝ)) ≤ (24 / 25 : ℝ) - (A : ℝ) / B := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hlt : (A : ℝ) / B < 24 / 25 := by linarith
  have hcross := (div_lt_iff₀ hBr).mp hlt
  have hint : 25 * A < 24 * B := by exact_mod_cast (show (25 : ℝ) * A < 24 * B by linarith)
  have hone : (25 : ℝ) * A + 1 ≤ 24 * B := by exact_mod_cast (Nat.succ_le_of_lt hint)
  apply (div_le_iff₀ (mul_pos (by norm_num) hBr)).mpr
  field_simp
  nlinarith

/-- The integer powers in the startup multiplier introduce no new denominator. -/
theorem cubicTail_residual_lower (t n a d : ℕ) (had : a < d)
    (hpos : 0 < (24 / 25 : ℝ) - (2 : ℝ) ^ t * cubicTailFormula n ((a : ℝ) / d)) :
    1 / (25 * (d : ℝ) ^ n * ((d - a : ℕ) : ℝ) ^ 4) ≤
      (24 / 25 : ℝ) - (2 : ℝ) ^ t * cubicTailFormula n ((a : ℝ) / d) := by
  have hd : 0 < d := (Nat.zero_le a).trans_lt had
  have he : 0 < d - a := Nat.sub_pos_of_lt had
  have hB : 0 < d ^ n * (d - a) ^ 4 := Nat.mul_pos (Nat.pow_pos hd) (Nat.pow_pos he)
  have hid : (2 : ℝ) ^ t * cubicTailFormula n ((a : ℝ) / d) =
      ((2 ^ t * a ^ n * cubicTailNumerator n a d : ℕ) : ℝ) /
        ((d ^ n * (d - a) ^ 4 : ℕ) : ℝ) := by
    rw [cubicTailFormula_integer n a d had]
    push_cast
    ring
  rw [hid] at hpos ⊢
  have h := residual_integer_lower (2 ^ t * a ^ n * cubicTailNumerator n a d)
    (d ^ n * (d - a) ^ 4) hB hpos
  simpa only [Nat.cast_mul, Nat.cast_pow, mul_assoc] using h

end WordCertDensity.Construction
