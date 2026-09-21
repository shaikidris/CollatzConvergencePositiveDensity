/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.HeadGate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Entropy cost of the strict first crossing

The head total pays the ambient group size. The collision square root must
halve this exponent before the finite head families are summed.
-/

@[expose] public section

namespace WordCertDensity.Head

/-- Strict crossing pays the group size with the exact width-dependent entropy exponent. -/
theorem entropy_lt {v : ℝ} {n l : ℕ} (hn : 0 < n)
    (hl : gateLevel v n < (l : ℝ)) :
    (3 : ℝ) ^ n / (2 : ℝ) ^ l < (n : ℝ) ^ (Real.log 2 * v ^ 2) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hc := mul_lt_mul_of_pos_right hl h2
  have hcancel : (Real.log 3 / Real.log 2) * Real.log 2 = Real.log 3 :=
    div_mul_cancel₀ _ h2.ne'
  simp only [gateLevel, logRatio, sub_mul, mul_assoc, hcancel] at hc
  rw [← Real.rpow_natCast, ← Real.rpow_natCast,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos hn', ← Real.exp_sub, Real.exp_lt_exp]
  nlinarith only [hc]

/-- The exact square of the single-slice rate, with half the entropy loss. -/
theorem slice_rate_sq {x : ℝ} (hx : 0 < x) (D v : ℝ) :
    (D * x ^ (-6409 + Real.log 2 * v ^ 2 / 2)) ^ 2 =
      (D / x ^ 6409) ^ 2 * x ^ (Real.log 2 * v ^ 2) := by
  rw [mul_pow, ← Real.rpow_natCast (x ^ (-6409 + Real.log 2 * v ^ 2 / 2)) 2,
    ← Real.rpow_mul hx.le, div_pow, ← pow_mul,
    ← Real.rpow_natCast x (6409 * 2)]
  rw [div_mul_eq_mul_div,
    mul_div_assoc (D ^ 2) (x ^ (Real.log 2 * v ^ 2)) (x ^ ((6409 * 2 : ℕ) : ℝ)),
    ← Real.rpow_sub hx]
  congr 2
  norm_num
  ring

end WordCertDensity.Head
