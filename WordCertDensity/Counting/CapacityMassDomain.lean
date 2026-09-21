/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.CenteredInverse

/-! # Domains of the three finite capacity inverses -/

namespace WordCertDensity.Counting

/-- A maximum ceiling above the mean gives the required mass domain. -/
theorem maximum_capacity_inverse_domain {μ S p : ℝ}
    (hμ : 0 < μ) (hS : μ ≤ S) (hp : 0 ≤ p) :
    0 ≤ p/S ∧ p/S ≤ p/μ :=
  ⟨div_nonneg hp (hμ.le.trans hS), div_le_div_of_nonneg_left hp hμ hS⟩

/-- The squared Jensen ceiling controls the order-three-halves inverse domain. -/
theorem fractional_capacity_inverse_domain {μ T B p : ℝ}
    (hμ : 0 < μ) (hT : 0 < T) (hB : 0 < B)
    (hmean : μ^3 ≤ B^2) (hp : 0 ≤ p) (hpaid : p ≤ μ*T) :
    0 ≤ p^3/(T^2*B^2) ∧ p^3/(T^2*B^2) ≤ p/μ := by
  refine ⟨by positivity, ?_⟩
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < T^2*B^2) hμ).2
  have hs : p^2 ≤ (μ*T)^2 := pow_le_pow_left₀ hp hpaid 2
  have hleft := mul_le_mul_of_nonneg_right hs (mul_nonneg hp hμ.le)
  have hright := mul_le_mul_of_nonneg_left hmean (mul_nonneg hp (sq_nonneg T))
  nlinarith

/-- Taking the maximum of all three branches preserves the same marked-mass domain. -/
theorem combined_capacity_inverse_domain {μ V T S B p W : ℝ}
    (hμ : 0 < μ) (hV : 0 < V) (hT : 0 < T) (hS : μ ≤ S) (hB : 0 < B)
    (hmean : μ^3 ≤ B^2) (hp : 0 ≤ p) (hpW : p ≤ W) (hpaid : W ≤ μ*T) :
    let u := max (max (capacitySmallRoot (μ^2+V) (2*μ*p+V*T) (p^2)) (p/S))
      (p^3/(T^2*B^2))
    0 ≤ u ∧ u ≤ W/μ := by
  have hc := centered_capacity_inverse_domain hμ hV hT hp (hpW.trans hpaid)
  have hm := maximum_capacity_inverse_domain hμ hS hp
  have hf := fractional_capacity_inverse_domain hμ hT hB hmean hp (hpW.trans hpaid)
  have hbound := div_le_div_of_nonneg_right hpW hμ.le
  exact ⟨hc.1.trans ((le_max_left _ _).trans (le_max_left _ _)),
    max_le (max_le (hc.2.trans hbound) (hm.2.trans hbound)) (hf.2.trans hbound)⟩

end WordCertDensity.Counting
