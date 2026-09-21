/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.CapacityInverse

/-! # The smaller inverse of the centered finite-capacity bound -/

namespace WordCertDensity.Counting

/-- The exact centered-capacity discriminant is nonnegative throughout the marked domain. -/
theorem centered_capacity_discriminant {μ V T p : ℝ}
    (hV : 0 ≤ V) (hp : 0 ≤ p) (hpaid : p ≤ μ*T) :
    0 ≤ (2*μ*p+V*T)^2-4*(μ^2+V)*p^2 := by
  have h := mul_nonneg (mul_nonneg hV hp) (sub_nonneg.mpr hpaid)
  nlinarith [sq_nonneg (V*T)]

/-- The stable inverse lies between zero and marked mass divided by the full mean. -/
theorem centered_capacity_inverse_domain {μ V T p : ℝ}
    (hμ : 0 < μ) (hV : 0 < V) (hT : 0 < T) (hp : 0 ≤ p) (hpaid : p ≤ μ*T) :
    0 ≤ capacitySmallRoot (μ^2+V) (2*μ*p+V*T) (p^2) ∧
      capacitySmallRoot (μ^2+V) (2*μ*p+V*T) (p^2) ≤ p/μ := by
  have hA : 0 < μ^2+V := by positivity
  have hB : 0 < 2*μ*p+V*T := by positivity
  refine ⟨capacitySmallRoot_nonneg hB (sq_nonneg p),
    capacitySmallRoot_le hA hB (centered_capacity_discriminant hV.le hp hpaid) ?_⟩
  have he : (μ^2+V)*(p/μ)^2-(2*μ*p+V*T)*(p/μ)+p^2 = V*(p/μ)*(p/μ-T) := by
    field_simp
    <;> ring
  rw [he]
  exact mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hV.le (div_nonneg hp hμ.le))
    (sub_nonpos.mpr ((div_le_iff₀ hμ).2 (by nlinarith)))

/-- The physical centered-capacity inequality forces the smaller-root mass lower bound. -/
theorem centered_capacity_mass_lower {μ V T p U : ℝ}
    (hμ : 0 < μ) (hV : 0 < V) (hT : 0 < T) (hp : 0 ≤ p) (hpaid : p ≤ μ*T)
    (hU : 0 ≤ U) (hUT : U ≤ T) (hmarked : p ≤ μ*U+Real.sqrt (V*U*(T-U))) :
    capacitySmallRoot (μ^2+V) (2*μ*p+V*T) (p^2) ≤ U := by
  by_cases hlow : p ≤ μ*U
  · exact (centered_capacity_inverse_domain hμ hV hT hp hpaid).2.trans
      ((div_le_iff₀ hμ).2 (by nlinarith))
  · apply capacitySmallRoot_le (by positivity : 0 < μ^2+V)
      (by positivity : 0 < 2*μ*p+V*T)
      (centered_capacity_discriminant hV.le hp hpaid)
    have hn : 0 ≤ V*U*(T-U) := mul_nonneg (mul_nonneg hV.le hU) (sub_nonneg.mpr hUT)
    have hs := Real.sq_sqrt hn
    have hh := Real.sqrt_nonneg (V*U*(T-U))
    nlinarith

end WordCertDensity.Counting
