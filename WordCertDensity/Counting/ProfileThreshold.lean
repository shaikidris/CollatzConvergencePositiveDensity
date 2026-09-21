/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.ProfileValue

/-! # Exact optimality of threshold allocations, including ties -/

namespace WordCertDensity.Counting

/-- Threshold allocations fill higher entries and empty lower entries; ties remain free. -/
def thresholdAllocation (Q : ℕ) (h w : Fin Q → ℝ) (T t : ℝ) : Prop :=
  (∀ r, t < h r → w r = T/Q) ∧ (∀ r, h r < t → w r = 0)

/-- A threshold allocation saturates the pointwise hinge identity, including equal entries. -/
theorem thresholdAllocation_identity (Q : ℕ) (h w : Fin Q → ℝ) (T t : ℝ)
    (hthreshold : thresholdAllocation Q h w T t) (r : Fin Q) :
    w r*h r = t*w r+(T/Q)*max (h r-t) 0 := by
  rcases lt_trichotomy (h r) t with hlt | heq | hgt
  · rw [hthreshold.2 r hlt, max_eq_right (by linarith : h r-t ≤ 0)]
    ring
  · rw [heq]
    simp only [sub_self, max_self, mul_zero, add_zero]
    ring
  · rw [hthreshold.1 r hgt, max_eq_left (by linarith : 0 ≤ h r-t)]
    ring

/-- Exact marked mass makes a threshold allocation attain its hinge bound. -/
theorem thresholdAllocation_mass (Q : ℕ) (h w : Fin Q → ℝ) (T p t : ℝ)
    (ht : 0 < t) (hw : ∀ r, 0 ≤ w r)
    (hthreshold : thresholdAllocation Q h w T t) (hmark : (∑ r, w r*h r) = p) :
    (∑ r, w r) = max (p-(T/Q)*∑ r, max (h r-t) 0) 0 / t := by
  have he := Finset.sum_congr rfl (fun r (_ : r ∈ Finset.univ) =>
    thresholdAllocation_identity Q h w T t hthreshold r)
  rw [hmark, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at he
  have hu : 0 ≤ ∑ r, w r := Finset.sum_nonneg (fun r _ => hw r)
  have hp : 0 ≤ p-(T/Q)*∑ r, max (h r-t) 0 := by nlinarith
  rw [max_eq_left hp]
  apply (eq_div_iff ht.ne').2
  nlinarith

/-- Any feasible threshold allocation with exact marked mass proves equality in hinge duality. -/
theorem thresholdAllocation_optimal (Q : ℕ) (h w : Fin Q → ℝ) (T p t : ℝ)
    (ht : 0 < t) (hw : feasibleAllocation Q h T p w)
    (hthreshold : thresholdAllocation Q h w T t) (hmark : (∑ r, w r*h r) = p) :
    allocationValue Q h T p = ∑ r, w r ∧
      allocationValue Q h T p = max (p-(T/Q)*∑ r, max (h r-t) 0) 0 / t := by
  have he := thresholdAllocation_mass Q h w T p t ht (fun r => (hw.1 r).1) hthreshold hmark
  have hl := allocationValue_hinge Q h T p t ht ⟨w, hw⟩
  have hb : BddBelow {u | ∃ v, feasibleAllocation Q h T p v ∧ u = ∑ r, v r} := by
    refine ⟨0, ?_⟩
    rintro u ⟨v, hv, rfl⟩
    exact Finset.sum_nonneg (fun r _ => (hv.1 r).1)
  have hu : allocationValue Q h T p ≤ ∑ r, w r := csInf_le hb ⟨w, hw, rfl⟩
  have heq : allocationValue Q h T p = ∑ r, w r := le_antisymm hu (he ▸ hl)
  exact ⟨heq, heq.trans he⟩

end WordCertDensity.Counting
