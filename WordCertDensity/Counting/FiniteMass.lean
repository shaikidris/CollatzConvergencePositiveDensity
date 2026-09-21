/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.CenteredMomentCapacity
import WordCertDensity.Counting.MomentCapacity
import WordCertDensity.Counting.CenteredInverse

/-! # Inverting all three bounds for the same finite occupied weights -/

namespace WordCertDensity.Counting

/-- The residue caps retain an upper bound on total occupied mass. -/
theorem finite_total_capacity (Q : ℕ) (w : Fin Q → ℝ) (T : ℝ)
    (hQ : 0 < Q) (hcap : ∀ r, w r ≤ T/Q) : (∑ r, w r) ≤ T := by
  have hq : (Q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  calc
    _ ≤ ∑ _ : Fin Q, T/Q := Finset.sum_le_sum (fun r _ => hcap r)
    _ = T := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp

/-- Cubing the fractional Holder estimate gives the finite mass inverse. -/
theorem fractional_mass_lower {U T B p : ℝ}
    (hU : 0 ≤ U) (hT : 0 < T) (hB : 0 < B) (hp : 0 ≤ p)
    (hmarked : p ≤ U^(1/3 : ℝ)*(T*B)^(2/3 : ℝ)) :
    p^3/(T^2*B^2) ≤ U := by
  have hc := pow_le_pow_left₀ hp hmarked 3
  rw [mul_pow, ← Real.rpow_mul_natCast hU,
    ← Real.rpow_mul_natCast (mul_pos hT hB).le] at hc
  norm_num at hc
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < T^2*B^2)).2
  nlinarith

/-- All three inverse branches lower-bound the same finite physical mass. -/
theorem finite_threeBranch_mass (Q : ℕ) (h w : Fin Q → ℝ) (μ V T S B p : ℝ)
    (hQ : 0 < Q) (hμ : 0 < μ) (hV : 0 < V) (hT : 0 < T)
    (hS : 0 < S) (hB : 0 < B) (hp : 0 ≤ p) (hpaid : p ≤ μ*T)
    (hh : ∀ r, 0 ≤ h r) (hw : ∀ r, 0 ≤ w r) (hcap : ∀ r, w r ≤ T/Q)
    (hmean : (∑ r, h r)/Q = μ) (hvar : (∑ r, (h r-μ)^2)/Q ≤ V)
    (hmax : ∀ r, h r ≤ S) (hmoment : (∑ r, h r^(3/2 : ℝ))/Q ≤ B)
    (hmarked : p ≤ ∑ r, w r*h r) :
    max (max (capacitySmallRoot (μ^2+V) (2*μ*p+V*T) (p^2)) (p/S))
      (p^3/(T^2*B^2)) ≤ ∑ r, w r := by
  have hU : 0 ≤ ∑ r, w r := Finset.sum_nonneg (fun r _ => hw r)
  have hUT := finite_total_capacity Q w T hQ hcap
  have hc := finite_centered_capacity Q h w T μ V hQ hw hcap hmean hvar
  have hcenter := centered_capacity_mass_lower hμ hV hT hp hpaid hU hUT (hmarked.trans hc)
  have hmaximum : p/S ≤ ∑ r, w r := by
    apply (div_le_iff₀ hS).2
    simpa only [mul_comm] using hmarked.trans (finite_maximum_capacity Q h w S hw hmax)
  have hf := finite_moment_capacity Q h w T (3/2) B hT.le (by norm_num)
    hh hw hcap hmoment
  norm_num at hf
  exact max_le (max_le hcenter hmaximum)
    (fractional_mass_lower hU hT hB hp (hmarked.trans hf))

end WordCertDensity.Counting
