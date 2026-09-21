/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.ProfilePivot

/-! # Reinserting a full pivot in the greedy allocation recursion -/

namespace WordCertDensity.Counting

/-- Removing a saturated pivot preserves the residual marked-capacity budget. -/
theorem allocation_pivot_budget (Q : ℕ) (h : Fin Q → ℝ) (C p : ℝ) (i : Fin Q)
    (hpaid : p ≤ C*∑ r, h r) (hfull : C*h i < p) :
    0 < p-C*h i ∧ p-C*h i ≤ C*∑ r ∈ Finset.univ.erase i, h r := by
  classical
  have he := Finset.sum_erase_add Finset.univ h (Finset.mem_univ i)
  have hscaled := congrArg (fun x : ℝ => C*x) he
  constructor <;> nlinarith [hscaled]

/-- Reinserting a full pivot preserves threshold structure and at most one partial weight. -/
theorem thresholdAllocation_extend (Q : ℕ) (h v : Fin Q → ℝ) (T p t : ℝ) (i : Fin Q)
    (hT : 0 ≤ T) (hti : t ≤ h i)
    (hv : ∀ r, r ≠ i → 0 ≤ v r ∧ v r ≤ T/Q)
    (habove : ∀ r, r ≠ i → t < h r → v r = T/Q)
    (hbelow : ∀ r, r ≠ i → h r < t → v r = 0)
    (hmark : (∑ r ∈ Finset.univ.erase i, v r*h r) = p-(T/Q)*h i)
    (hpartial : ∀ r s, r ≠ i → s ≠ i →
      0 < v r → v r < T/Q → 0 < v s → v s < T/Q → r = s) :
    ∃ w : Fin Q → ℝ, feasibleAllocation Q h T p w ∧
      thresholdAllocation Q h w T t ∧ (∑ r, w r*h r) = p ∧ w i = T/Q ∧
      (∀ r, r ≠ i → w r = v r) ∧
      (∀ r s, 0 < w r → w r < T/Q → 0 < w s → w s < T/Q → r = s) := by
  classical
  let w : Fin Q → ℝ := fun r => if r = i then T/Q else v r
  have hwi : w i = T/Q := by simp [w]
  have hother (r : Fin Q) (hr : r ≠ i) : w r = v r := by simp only [w, if_neg hr]
  have hcap (r : Fin Q) : 0 ≤ w r ∧ w r ≤ T/Q := by
    by_cases hr : r = i
    · subst r
      rw [hwi]
      exact ⟨div_nonneg hT (Nat.cast_nonneg Q), le_rfl⟩
    · rw [hother r hr]
      exact hv r hr
  have hm : (∑ r, w r*h r) = p := by
    have he := Finset.sum_erase_add Finset.univ (fun r => w r*h r) (Finset.mem_univ i)
    have herase : (∑ r ∈ Finset.univ.erase i, w r*h r) =
        ∑ r ∈ Finset.univ.erase i, v r*h r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [hother r (Finset.mem_erase.mp hr).1]
    rw [herase, hmark, hwi] at he
    linarith
  refine ⟨w, ⟨hcap, hm.ge⟩, ⟨?_, ?_⟩, hm, hwi, hother, ?_⟩
  · intro r hr
    by_cases hri : r = i
    · simpa only [hri] using hwi
    · rw [hother r hri]
      exact habove r hri hr
  · intro r hr
    have hri : r ≠ i := by intro he; subst r; exact (not_lt_of_ge hti) hr
    rw [hother r hri]
    exact hbelow r hri hr
  · intro r s hr0 hrC hs0 hsC
    have hri : r ≠ i := by intro he; subst r; rw [hwi] at hrC; exact (lt_irrefl _) hrC
    have hsi : s ≠ i := by intro he; subst s; rw [hwi] at hsC; exact (lt_irrefl _) hsC
    rw [hother r hri] at hr0 hrC
    rw [hother s hsi] at hs0 hsC
    exact hpartial r s hri hsi hr0 hrC hs0 hsC

end WordCertDensity.Counting
