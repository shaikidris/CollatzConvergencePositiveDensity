/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Counting.BandCensus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Finite threshold allocation with fractional occupations -/

@[expose] public section

namespace WordCertDensity.Counting

open scoped BigOperators

/-- Filling a cheaper initial set gives a lower bound for every fractional occupation. -/
theorem occupation_threshold (S T : Finset ℕ) (w D : ℕ → ℝ) (d τ : ℝ)
    (hTS : T ⊆ S) (hx : ∀ x ∈ S, 0 < (x : ℝ))
    (hw : ∀ x ∈ S, 0 ≤ w x ∧ w x ≤ 1)
    (hcheap : ∀ x ∈ T, D x = d ∧ (x : ℝ) * d ≤ τ)
    (hdear : ∀ x ∈ S, x ∉ T → τ ≤ (x : ℝ) * D x) :
    d * T.card + τ * ((∑ x ∈ S, w x / x) - ∑ x ∈ T, (x : ℝ)⁻¹) ≤
      ∑ x ∈ S, w x * D x := by
  have hlow : ∀ x ∈ T, d - τ / x ≤ w x * D x - τ * (w x / x) := by
    intro x hxt
    have hxpos := hx x (hTS hxt)
    obtain ⟨hD, hc⟩ := hcheap x hxt
    have hc' : d - τ / x ≤ 0 := by
      have := (le_div_iff₀ hxpos).mpr (by simpa [mul_comm] using hc)
      linarith
    have h := mul_le_mul_of_nonpos_right (hw x (hTS hxt)).2 hc'
    rw [hD]
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith [h]
  have hnonneg : ∀ x ∈ S, x ∉ T → 0 ≤ w x * D x - τ * (w x / x) := by
    intro x hxs hxt
    have hc : τ / x ≤ D x :=
      (div_le_iff₀ (hx x hxs)).mpr (by simpa [mul_comm] using hdear x hxs hxt)
    have h := mul_le_mul_of_nonneg_left hc (hw x hxs).1
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith [h]
  have hsum := (Finset.sum_le_sum hlow).trans
    (Finset.sum_le_sum_of_subset_of_nonneg hTS hnonneg)
  have he : (∑ x ∈ T, (d - τ / x)) = d * T.card - τ * ∑ x ∈ T, (x : ℝ)⁻¹ := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv,
      ← Finset.mul_sum]
    ring
  have he' : (∑ x ∈ S, (w x * D x - τ * (w x / x))) =
      (∑ x ∈ S, w x * D x) - τ * ∑ x ∈ S, w x / x := by
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
  rw [he, he'] at hsum
  linarith

end WordCertDensity.Counting
