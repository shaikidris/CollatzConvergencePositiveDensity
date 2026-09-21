/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.ProfileThreshold

/-! # The terminal pivot of greedy finite allocation -/

namespace WordCertDensity.Counting

/-- One largest positive entry suffices when its capacity covers the requested mark. -/
theorem thresholdAllocation_single (Q : ℕ) (h : Fin Q → ℝ) (T p : ℝ) (i : Fin Q)
    (hT : 0 ≤ T) (hi : 0 < h i) (hmax : ∀ r, h r ≤ h i)
    (hp : 0 ≤ p) (hpaid : p ≤ (T/Q)*h i) :
    ∃ w : Fin Q → ℝ, feasibleAllocation Q h T p w ∧
      thresholdAllocation Q h w T (h i) ∧ (∑ r, w r*h r) = p ∧
      (∀ r, r ≠ i → w r = 0) := by
  classical
  let w : Fin Q → ℝ := fun r => if r = i then p/h i else 0
  have hcap : ∀ r, 0 ≤ w r ∧ w r ≤ T/Q := by
    intro r
    by_cases hr : r = i
    · simp only [w, if_pos hr]
      exact ⟨div_nonneg hp hi.le, (div_le_iff₀ hi).2 hpaid⟩
    · simp only [w, if_neg hr]
      exact ⟨le_rfl, div_nonneg hT (Nat.cast_nonneg Q)⟩
  have hmark : (∑ r, w r*h r) = p := by
    simp only [w, ite_mul, zero_mul]
    simp [hi.ne']
  refine ⟨w, ⟨hcap, hmark.ge⟩, ⟨?_, ?_⟩, hmark, ?_⟩
  · intro r hr
    exact False.elim ((not_lt_of_ge (hmax r)) hr)
  · intro r hr
    have hri : r ≠ i := by intro he; subst r; exact (lt_irrefl _ hr)
    simp only [w, if_neg hri]
  · intro r hr
    simp only [w, if_neg hr]

/-- The terminal greedy case has the exact value p divided by its largest entry. -/
theorem allocationValue_single (Q : ℕ) (h : Fin Q → ℝ) (T p : ℝ) (i : Fin Q)
    (hT : 0 ≤ T) (hi : 0 < h i) (hmax : ∀ r, h r ≤ h i)
    (hp : 0 ≤ p) (hpaid : p ≤ (T/Q)*h i) :
    allocationValue Q h T p = p/h i := by
  obtain ⟨w, hw, ht, hm, _⟩ := thresholdAllocation_single Q h T p i hT hi hmax hp hpaid
  have he := (thresholdAllocation_optimal Q h w T p (h i) hi hw ht hm).2
  have hz : (∑ r, max (h r-h i) 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r _
    exact max_eq_right (sub_nonpos.mpr (hmax r))
  simpa only [hz, mul_zero, sub_zero, max_eq_left hp] using he

end WordCertDensity.Counting
