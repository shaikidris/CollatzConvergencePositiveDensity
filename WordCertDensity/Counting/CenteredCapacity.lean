/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.SecondCapacity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Centered finite capacity with the full-group mean -/

namespace WordCertDensity.Counting

/-- Centering the actual weights retains the occupied/unoccupied capacity factor. -/
theorem centered_weight_capacity (Q : ℕ) (w : Fin Q → ℝ) (T : ℝ)
    (hQ : 0 < Q) (hw : ∀ r, 0 ≤ w r) (hcap : ∀ r, w r ≤ T/Q) :
    (Q : ℝ) * ∑ r, (w r - (∑ i, w i)/Q)^2 ≤ (∑ r, w r)*(T-∑ r, w r) := by
  let U := ∑ r, w r
  have hq : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have he : (∑ r, (w r - U/Q)^2) = (∑ r, w r^2) - U^2/Q := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    change (∑ r, w r^2) - 2*U*(U/Q) + (Q : ℝ)*(U/Q)^2 = (∑ r, w r^2)-U^2/Q
    field_simp
    <;> ring
  have hc : (∑ r, w r^2) ≤ (T/Q)*U := by
    calc
      _ ≤ ∑ r, (T/Q)*w r := Finset.sum_le_sum (fun r _ => by
        have h := mul_le_mul_of_nonneg_right (hcap r) (hw r)
        nlinarith)
      _ = _ := (Finset.mul_sum ..).symm
  change (Q : ℝ) * ∑ r, (w r-U/Q)^2 ≤ U*(T-U)
  rw [he]
  have hcu := (le_div_iff₀ hq).mp (show (∑ r, w r^2) ≤ T*U/Q by simpa [div_mul_eq_mul_div] using hc)
  have hd : (Q : ℝ) * (U^2/Q) = U^2 := mul_div_cancel₀ _ hq.ne'
  nlinarith

end WordCertDensity.Counting
