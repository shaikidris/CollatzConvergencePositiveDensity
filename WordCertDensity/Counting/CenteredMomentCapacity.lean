/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.CenteredCapacity

/-! # Finite centered capacity from the exact full mean and variance -/

namespace WordCertDensity.Counting

/-- The centered estimate retains both occupied mass and complementary capacity. -/
theorem finite_centered_capacity (Q : ℕ) (h w : Fin Q → ℝ) (T μ V : ℝ)
    (hQ : 0 < Q) (hw : ∀ r, 0 ≤ w r) (hcap : ∀ r, w r ≤ T/Q)
    (hmean : (∑ r, h r)/Q = μ) (hvar : (∑ r, (h r-μ)^2)/Q ≤ V) :
    (∑ r, w r*h r) ≤ μ*(∑ r, w r) + Real.sqrt (V*(∑ r, w r)*(T-∑ r, w r)) := by
  let U := ∑ r, w r
  have hq : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hm : (∑ r, h r) = μ*Q := (div_eq_iff hq.ne').mp hmean
  have hv : (∑ r, (h r-μ)^2) ≤ V*Q := (div_le_iff₀ hq).mp hvar
  have hV : 0 ≤ V := (div_nonneg (Finset.sum_nonneg (fun r _ => sq_nonneg _)) hq.le).trans hvar
  have hz : (∑ r, (h r-μ)) = 0 := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, hm]
    ring
  have hi : (∑ r, (w r-U/Q)*(h r-μ)) = (∑ r, w r*h r)-μ*U := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hz, mul_zero, sub_zero]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun r : Fin Q => w r-U/Q) (fun r => h r-μ)
  rw [hi] at hc
  have hb := centered_weight_capacity Q w T hQ hw hcap
  have hn : 0 ≤ ∑ r, (w r-U/Q)^2 := Finset.sum_nonneg (fun r _ => sq_nonneg _)
  have he := mul_le_mul_of_nonneg_left hv hn
  have hf := mul_le_mul_of_nonneg_right hb hV
  have hsq : ((∑ r, w r*h r)-μ*U)^2 ≤ V*U*(T-U) := by
    dsimp only [U] at *
    nlinarith
  have hnon : 0 ≤ V*U*(T-U) := (sq_nonneg _).trans hsq
  have hsqrt := Real.sq_sqrt hnon
  have hp := Real.sqrt_nonneg (V*U*(T-U))
  change (∑ r, w r*h r) ≤ μ*U + Real.sqrt (V*U*(T-U))
  nlinarith

end WordCertDensity.Counting
