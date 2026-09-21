/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.PostExitPotential
import Mathlib.Tactic

/-! # Exact splitting of the potential's literal pair product -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- The full pair product splits at an exact observed pair time, retaining
the actual accumulated integer height and the literal remaining suffix. -/
theorem whiteWindowProduct_add (white : ℕ → ℤ → Prop) (z : ℝ≥0∞)
    (h k j : ℕ) (l : ℤ) (w : ValuationWord) :
    whiteWindowProduct white z (h + k) j l w =
      whiteWindowProduct white z h j l w *
        whiteWindowProduct white z k (j + h)
          (l + ValuationWord.total (w.take (2 * h))) (w.drop (2 * h)) := by
  induction h generalizing j l w with
  | zero => simp [whiteWindowProduct, ValuationWord.total]
  | succ h ih =>
      rw [Nat.succ_add, whiteWindowProduct, ih, whiteWindowProduct]
      have hh : ValuationWord.total (w.take (2 * (h + 1))) =
          ValuationWord.total (w.take 2) + ValuationWord.total ((w.drop 2).take (2 * h)) := by
        rw [show 2 * (h + 1) = 2 + 2 * h by omega, List.take_add,
          ValuationWord.total_append]
      have hd : (w.drop 2).drop (2 * h) = w.drop (2 * (h + 1)) := by
        rw [List.drop_drop]
        congr 1
        omega
      rw [hd, hh, Nat.cast_add, show j + 1 + h = j + (h + 1) by omega]
      simp only [add_assoc, mul_assoc]

/-- Discarding the past factors only increases a product of discounts. -/
theorem whiteWindowProduct_le_suffix (white : ℕ → ℤ → Prop) {z : ℝ≥0∞}
    (hz : z ≤ 1) (h k j : ℕ) (l : ℤ) (w : ValuationWord) :
    whiteWindowProduct white z (h + k) j l w ≤
      whiteWindowProduct white z k (j + h)
        (l + ValuationWord.total (w.take (2 * h))) (w.drop (2 * h)) := by
  rw [whiteWindowProduct_add]
  simpa only [one_mul] using mul_le_mul_left (whiteWindowProduct_le_one white hz h j l w) _

/-- Discarding factors after the split only increases the product. -/
theorem whiteWindowProduct_le_prefix (white : ℕ → ℤ → Prop) {z : ℝ≥0∞}
    (hz : z ≤ 1) (h k j : ℕ) (l : ℤ) (w : ValuationWord) :
    whiteWindowProduct white z (h + k) j l w ≤ whiteWindowProduct white z h j l w := by
  rw [whiteWindowProduct_add]
  simpa only [mul_one] using mul_le_mul_right
    (whiteWindowProduct_le_one white hz k (j + h)
      (l + ValuationWord.total (w.take (2 * h))) (w.drop (2 * h))) _

end WordCertDensity.LocalPrimitive
