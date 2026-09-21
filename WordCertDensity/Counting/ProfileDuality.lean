/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.ProfileGreedy

/-! # Attained finite profile duality -/

namespace WordCertDensity.Counting

/-- Positive feasible demand has an optimal threshold allocation with at most one partial entry. -/
theorem allocationValue_greedy (Q : ℕ) (h : Fin Q → ℝ) (μ T p : ℝ)
    (hQ : 0 < Q) (hT : 0 < T) (hp : 0 < p) (hpaid : p ≤ T*μ)
    (hmean : (∑ r, h r)/Q = μ) :
    ∃ w t, 0 < t ∧ feasibleAllocation Q h T p w ∧
      thresholdAllocation Q h w T t ∧ (∑ r, w r*h r) = p ∧
      allocationValue Q h T p = ∑ r, w r ∧
      allocationValue Q h T p = max (p-(T/Q)*∑ r, max (h r-t) 0) 0/t ∧
      (∀ i j, 0 < w i → w i < T/Q → 0 < w j → w j < T/Q → i = j) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hbudget : p ≤ (T/Q)*∑ r, h r := by
    calc
      p ≤ T*μ := hpaid
      _ = (T/Q)*∑ r, h r := by rw [← hmean]; ring
  obtain ⟨g⟩ := greedyAllocation_exists Finset.univ h (T/Q)
    (div_pos hT hQr) p hp hbudget
  have hw : feasibleAllocation Q h T p g.weight := ⟨g.bounds, g.marked.ge⟩
  have ht : thresholdAllocation Q h g.weight T g.threshold :=
    ⟨fun r => g.above r (Finset.mem_univ r), fun r => g.below r (Finset.mem_univ r)⟩
  have he := thresholdAllocation_optimal Q h g.weight T p g.threshold
    g.positive hw ht g.marked
  exact ⟨g.weight, g.threshold, g.positive, hw, ht, g.marked, he.1, he.2, g.onePartial⟩

/-- The finite profile equals the supremum of hinge bounds, including zero and full demand. -/
theorem allocationValue_duality (Q : ℕ) (h : Fin Q → ℝ) (μ T p : ℝ)
    (hQ : 0 < Q) (hμ : 0 < μ) (hT : 0 < T) (hp : 0 ≤ p)
    (hpaid : p ≤ T*μ) (hmean : (∑ r, h r)/Q = μ) :
    allocationValue Q h T p =
      sSup {a | ∃ t > 0, a = max (p-(T/Q)*∑ r, max (h r-t) 0) 0/t} := by
  let H : Set ℝ := {a | ∃ t > 0, a = max (p-(T/Q)*∑ r, max (h r-t) 0) 0/t}
  have hfeas : ∃ w, feasibleAllocation Q h T p w :=
    ⟨_, (feasibleAllocation_uniform Q h μ T p hQ hμ hp hpaid hmean).1⟩
  have hnonempty : H.Nonempty := ⟨_, 1, zero_lt_one, rfl⟩
  have hbound : ∀ a ∈ H, a ≤ allocationValue Q h T p := by
    rintro a ⟨t, ht, rfl⟩
    exact allocationValue_hinge Q h T p t ht hfeas
  have hbounded : BddAbove H := ⟨_, hbound⟩
  change allocationValue Q h T p = sSup H
  apply le_antisymm ?_ (csSup_le hnonempty hbound)
  rcases hp.eq_or_lt with he | hpos
  · have hv := allocationValue_domain Q h μ T p hQ hμ hp hpaid hmean
    have hz : allocationValue Q h T p = 0 := by
      have hpdiv : p/μ = 0 := by rw [← he, zero_div]
      rw [hpdiv] at hv
      exact le_antisymm hv.2 hv.1
    rw [hz]
    have hl : (0 : ℝ) ≤ max (p-(T/Q)*∑ r, max (h r-1) 0) 0/1 :=
      div_nonneg (le_max_right _ _) zero_le_one
    exact hl.trans (le_csSup hbounded ⟨1, zero_lt_one, rfl⟩)
  · obtain ⟨w, t, ht, _, _, _, _, heq, _⟩ :=
      allocationValue_greedy Q h μ T p hQ hT hpos hpaid hmean
    exact le_csSup hbounded ⟨t, ht, heq⟩

end WordCertDensity.Counting
