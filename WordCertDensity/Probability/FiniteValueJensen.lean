/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! # Countable mixtures with a finite set of values -/

@[expose] public section

namespace WordCertDensity.FiniteValue

open scoped Classical

variable {ι β : Type*}

/-- Group the original coefficient series by its finite input value. -/
noncomputable def coefficientFiber (c : ι → ℝ) (τ : ι → β) (b : β) : ℝ :=
  ∑' i, if τ i = b then c i else 0

/-- Restricting a summable coefficient series to one input fiber preserves summability. -/
theorem fiber_summable {c : ι → ℝ} (hc : Summable c) (τ : ι → β) (b : β) :
    Summable (fun i => if τ i = b then c i else 0) := by
  exact (hc.indicator {i | τ i = b}).congr (fun i => by
    simp only [Set.indicator_apply, Set.mem_ofPred_eq])

/-- Nonnegative coefficients remain nonnegative after finite-value grouping. -/
theorem coefficientFiber_nonneg {c : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (τ : ι → β) (b : β) :
    0 ≤ coefficientFiber c τ b := by
  apply tsum_nonneg
  intro i
  split_ifs
  · exact hc i
  · exact le_rfl

variable [Fintype β]

/-- Finite-value grouping preserves any real-valued weighted expectation. -/
theorem sum_coefficientFiber {c : ι → ℝ} (hc : Summable c) (τ : ι → β) (f : β → ℝ) :
    (∑ b, coefficientFiber c τ b * f b) = ∑' i, c i * f (τ i) := by
  simp only [coefficientFiber, ← tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun b _ => (fiber_summable hc τ b).mul_right (f b))]
  apply tsum_congr
  intro i
  simp [ite_mul]

/-- The grouped coefficients retain their full total. -/
theorem sum_coefficientFiber_one {c : ι → ℝ} (hc : Summable c) (τ : ι → β) :
    (∑ b, coefficientFiber c τ b) = ∑' i, c i := by
  simpa only [mul_one] using sum_coefficientFiber hc τ (fun _ => 1)

/-- A finite-valued observable times nonnegative summable coefficients is summable. -/
theorem summable_weighted {c : ι → ℝ} (hc : Summable c) (hc0 : ∀ i, 0 ≤ c i)
    (τ : ι → β) (f : β → ℝ) : Summable (fun i => c i * f (τ i)) := by
  apply (hc.mul_right (∑ b, |f b|)).of_norm_bounded
  intro i
  have h := Finset.single_le_sum (fun b _ => abs_nonneg (f b)) (Finset.mem_univ (τ i))
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc0 i)] using
    mul_le_mul_of_nonneg_left h (hc0 i)

/-- Jensen for countable weights and finite input values needs no boundary continuity premise. -/
theorem jensen {c : ι → ℝ} (hc : Summable c) (hc0 : ∀ i, 0 ≤ c i)
    (hc1 : ∑' i, c i = 1) (τ : ι → β) (x : β → ℝ) (hx : ∀ b, 0 ≤ x b)
    (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ (Set.Ici 0) Φ) :
    Φ (∑' i, c i * x (τ i)) ≤ ∑' i, c i * Φ (x (τ i)) := by
  have hsum : ∑ b, coefficientFiber c τ b = 1 :=
    (sum_coefficientFiber_one hc τ).trans hc1
  have h := hΦ.map_sum_le (t := Finset.univ)
    (fun b _ => coefficientFiber_nonneg hc0 τ b) hsum (fun b _ => hx b)
  simp only [smul_eq_mul] at h
  rw [sum_coefficientFiber hc τ x, sum_coefficientFiber hc τ (fun b => Φ (x b))] at h
  exact h

end WordCertDensity.FiniteValue
