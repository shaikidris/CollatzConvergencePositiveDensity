/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.ProfileCompact

/-! # The attained allocation value and the hinge lower bound -/

namespace WordCertDensity.Counting

/-- Infimum of occupied mass over exactly the feasible allocations. -/
noncomputable def allocationValue (Q : ℕ) (h : Fin Q → ℝ) (T p : ℝ) : ℝ :=
  sInf {u | ∃ w, feasibleAllocation Q h T p w ∧ u = ∑ r, w r}

/-- The infimum equals an attained feasible minimum. -/
theorem allocationValue_attained (Q : ℕ) (h : Fin Q → ℝ) (T p : ℝ)
    (hne : ∃ w, feasibleAllocation Q h T p w) :
    ∃ w, feasibleAllocation Q h T p w ∧ (∑ r, w r) = allocationValue Q h T p := by
  obtain ⟨w, hw, hmin⟩ := feasibleAllocation_exists_min Q h T p hne
  have hb : BddBelow {u | ∃ v, feasibleAllocation Q h T p v ∧ u = ∑ r, v r} := by
    refine ⟨0, ?_⟩
    rintro u ⟨v, hv, rfl⟩
    exact Finset.sum_nonneg (fun r _ => (hv.1 r).1)
  refine ⟨w, hw, le_antisymm ?_ ?_⟩
  · unfold allocationValue
    have hne' : Set.Nonempty {u : ℝ | ∃ v : Fin Q → ℝ,
        feasibleAllocation Q h T p v ∧ u = ∑ r, v r} := ⟨∑ r, w r, w, hw, rfl⟩
    apply le_csInf hne'
    rintro u ⟨v, hv, rfl⟩
    exact hmin v hv
  · exact csInf_le hb ⟨w, hw, rfl⟩

/-- The exact allocation value lies between zero and the uniform fractional allocation. -/
theorem allocationValue_domain (Q : ℕ) (h : Fin Q → ℝ) (μ T p : ℝ)
    (hQ : 0 < Q) (hμ : 0 < μ) (hp : 0 ≤ p) (hpaid : p ≤ T*μ)
    (hmean : (∑ r, h r)/Q = μ) :
    0 ≤ allocationValue Q h T p ∧ allocationValue Q h T p ≤ p/μ := by
  have hunif := feasibleAllocation_uniform Q h μ T p hQ hμ hp hpaid hmean
  obtain ⟨w, hw, heq⟩ := allocationValue_attained Q h T p ⟨_, hunif.1⟩
  have hb : BddBelow {u | ∃ v, feasibleAllocation Q h T p v ∧ u = ∑ r, v r} := by
    refine ⟨0, ?_⟩
    rintro u ⟨v, hv, rfl⟩
    exact Finset.sum_nonneg (fun r _ => (hv.1 r).1)
  refine ⟨heq ▸ Finset.sum_nonneg (fun r _ => (hw.1 r).1), ?_⟩
  exact csInf_le hb ⟨_, hunif.1, hunif.2.symm⟩

/-- Every hinge threshold gives a lower bound for every feasible occupied mass. -/
theorem feasibleAllocation_hinge (Q : ℕ) (h w : Fin Q → ℝ) (T p t : ℝ)
    (ht : 0 < t) (hw : feasibleAllocation Q h T p w) :
    max (p-(T/Q)*∑ r, max (h r-t) 0) 0 / t ≤ ∑ r, w r := by
  have hpoint (r : Fin Q) : w r*h r ≤ t*w r+(T/Q)*max (h r-t) 0 := by
    have hlow := le_max_left (h r-t) 0
    have hnon := le_max_right (h r-t) 0
    have h1 := mul_le_mul_of_nonneg_left hlow (hw.1 r).1
    have h2 := mul_le_mul_of_nonneg_right (hw.1 r).2 hnon
    nlinarith
  have hsum := Finset.sum_le_sum (fun r (_ : r ∈ Finset.univ) => hpoint r)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  apply (div_le_iff₀ ht).2
  apply max_le
  · nlinarith [hw.2]
  · exact mul_nonneg (Finset.sum_nonneg (fun r _ => (hw.1 r).1)) ht.le

/-- The hinge lower bound holds for the attained profile value. -/
theorem allocationValue_hinge (Q : ℕ) (h : Fin Q → ℝ) (T p t : ℝ)
    (ht : 0 < t) (hne : ∃ w, feasibleAllocation Q h T p w) :
    max (p-(T/Q)*∑ r, max (h r-t) 0) 0 / t ≤ allocationValue Q h T p := by
  obtain ⟨w, hw, he⟩ := allocationValue_attained Q h T p hne
  rw [← he]
  exact feasibleAllocation_hinge Q h w T p t ht hw

end WordCertDensity.Counting
