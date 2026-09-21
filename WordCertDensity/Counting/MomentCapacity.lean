/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import Mathlib.Analysis.MeanInequalities

/-! # Finite real-moment and maximum bounds for the same occupied weights -/

namespace WordCertDensity.Counting

/-- The original finite residue cap controls every nonnegative real moment. -/
theorem finite_moment_capacity (Q : ℕ) (h w : Fin Q → ℝ) (T s B : ℝ)
    (hT : 0 ≤ T) (hs : 1 ≤ s) (hh : ∀ r, 0 ≤ h r) (hw : ∀ r, 0 ≤ w r)
    (hcap : ∀ r, w r ≤ T/Q) (hB : (∑ r, h r ^ s)/Q ≤ B) :
    (∑ r, w r*h r) ≤ (∑ r, w r) ^ (1-1/s) * (T*B) ^ (1/s) := by
  have he : (∑ r, w r * h r ^ s) ≤ T * B := by
    calc
      _ ≤ ∑ r : Fin Q, (T/Q) * h r ^ s :=
        Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_right (hcap r)
          (Real.rpow_nonneg (hh r) s))
      _ = T * ((∑ r : Fin Q, h r ^ s)/Q) := by rw [← Finset.mul_sum]; ring
      _ ≤ T * B := mul_le_mul_of_nonneg_left hB hT
  have hmoment := Real.inner_le_weight_mul_Lp_of_nonneg Finset.univ hs w h hw hh
  have hn : 0 ≤ ∑ r, w r * h r ^ s :=
    Finset.sum_nonneg (fun r _ => mul_nonneg (hw r) (Real.rpow_nonneg (hh r) s))
  have hp : 0 ≤ s⁻¹ := inv_nonneg.mpr (by linarith)
  have hpow := Real.rpow_le_rpow hn he hp
  have hfactor : 0 ≤ (∑ r, w r) ^ (1-s⁻¹) :=
    Real.rpow_nonneg (Finset.sum_nonneg (fun r _ => hw r)) _
  simpa only [one_div] using hmoment.trans (mul_le_mul_of_nonneg_left hpow hfactor)

/-- A maximum bound uses exactly the same weights and occupied mass. -/
theorem finite_maximum_capacity (Q : ℕ) (h w : Fin Q → ℝ) (S : ℝ)
    (hw : ∀ r, 0 ≤ w r) (hmax : ∀ r, h r ≤ S) :
    (∑ r, w r*h r) ≤ S * ∑ r, w r := by
  calc
    _ ≤ ∑ r, w r*S := Finset.sum_le_sum
      (fun r _ => mul_le_mul_of_nonneg_left (hmax r) (hw r))
    _ = _ := by rw [← Finset.sum_mul, mul_comm]

end WordCertDensity.Counting
