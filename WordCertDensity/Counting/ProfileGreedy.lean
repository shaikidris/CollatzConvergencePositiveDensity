/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.ProfileExtension

/-! # Greedy allocation on a finite set of nonnegative entries -/

namespace WordCertDensity.Counting

/-- Data and invariants preserved while the finite greedy recursion removes full pivots. -/
structure GreedyAllocation {ι : Type*} (I : Finset ι) (h : ι → ℝ) (C p : ℝ) where
  /-- The assigned occupied weight at each entry. -/
  weight : ι → ℝ
  /-- The positive profile value separating full and empty entries. -/
  threshold : ℝ
  positive : 0 < threshold
  witness : ∃ i ∈ I, h i = threshold
  bounds : ∀ i, 0 ≤ weight i ∧ weight i ≤ C
  support : ∀ i, i ∉ I → weight i = 0
  marked : (∑ i ∈ I, weight i*h i) = p
  above : ∀ i ∈ I, threshold < h i → weight i = C
  below : ∀ i ∈ I, h i < threshold → weight i = 0
  onePartial : ∀ i j, 0 < weight i → weight i < C →
    0 < weight j → weight j < C → i = j

/-- Every positive feasible marked demand has a finite greedy allocation with at most one partial entry. -/
theorem greedyAllocation_exists {ι : Type*} [DecidableEq ι] (I : Finset ι)
    (h : ι → ℝ) (C : ℝ) (hC : 0 < C)
    (p : ℝ) (hp : 0 < p) (hpaid : p ≤ C*∑ i ∈ I, h i) :
    Nonempty (GreedyAllocation I h C p) := by
  classical
  induction I using Finset.strongInductionOn generalizing p with
  | _ I ih =>
    have hsum : 0 < ∑ i ∈ I, h i := by nlinarith
    have hne : I.Nonempty := by
      by_contra hn
      have hempty := Finset.not_nonempty_iff_eq_empty.mp hn
      simp [hempty] at hsum
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image I h hne
    have hip : 0 < h i := by
      by_contra hn
      have hsumle : (∑ j ∈ I, h j) ≤ 0 :=
        Finset.sum_nonpos (fun j hj => (hmax j hj).trans (le_of_not_gt hn))
      linarith
    by_cases hstop : p ≤ C*h i
    · let w : ι → ℝ := fun j => if j = i then p/h i else 0
      have hwi : w i = p/h i := by simp [w]
      have hwo (j : ι) (hj : j ≠ i) : w j = 0 := by simp [w, hj]
      refine ⟨{
        weight := w
        threshold := h i
        positive := hip
        witness := ⟨i, hi, rfl⟩
        bounds := ?_
        support := ?_
        marked := ?_
        above := ?_
        below := ?_
        onePartial := ?_ }⟩
      · intro j
        by_cases hj : j = i
        · subst j
          rw [hwi]
          exact ⟨div_nonneg hp.le hip.le, (div_le_iff₀ hip).2 hstop⟩
        · rw [hwo j hj]
          exact ⟨le_rfl, hC.le⟩
      · intro j hj
        exact hwo j (by intro he; subst j; exact hj hi)
      · simp [w, hi, hip.ne']
      · intro j hj hgt
        exact False.elim ((not_lt_of_ge (hmax j hj)) hgt)
      · intro j _ hlt
        exact hwo j (by intro he; subst j; exact (lt_irrefl _) hlt)
      · intro j k hj _ hk _
        have hji : j = i := by by_contra hn; rw [hwo j hn] at hj; exact (lt_irrefl _) hj
        have hki : k = i := by by_contra hn; rw [hwo k hn] at hk; exact (lt_irrefl _) hk
        exact hji.trans hki.symm
    · have hremain : 0 < p-C*h i := by linarith [lt_of_not_ge hstop]
      have hbudget : p-C*h i ≤ C*∑ j ∈ I.erase i, h j := by
        have he := congrArg (fun x : ℝ => C*x) (Finset.sum_erase_add I h hi)
        nlinarith
      obtain ⟨g⟩ := ih (I.erase i) (Finset.erase_ssubset hi) (p-C*h i) hremain hbudget
      obtain ⟨j, hj, hjt⟩ := g.witness
      have hti : g.threshold ≤ h i := by rw [← hjt]; exact hmax j (Finset.mem_erase.mp hj).2
      let w : ι → ℝ := fun r => if r = i then C else g.weight r
      have hwi : w i = C := by simp [w]
      have hwo (r : ι) (hr : r ≠ i) : w r = g.weight r := by simp [w, hr]
      refine ⟨{
        weight := w
        threshold := g.threshold
        positive := g.positive
        witness := ⟨j, (Finset.mem_erase.mp hj).2, hjt⟩
        bounds := ?_
        support := ?_
        marked := ?_
        above := ?_
        below := ?_
        onePartial := ?_ }⟩
      · intro r
        by_cases hr : r = i
        · subst r; rw [hwi]; exact ⟨hC.le, le_rfl⟩
        · rw [hwo r hr]; exact g.bounds r
      · intro r hr
        have hri : r ≠ i := by intro he; subst r; exact hr hi
        rw [hwo r hri]
        exact g.support r (by intro he; exact hr (Finset.mem_erase.mp he).2)
      · have he := Finset.sum_erase_add I (fun r => w r*h r) hi
        have hs : (∑ r ∈ I.erase i, w r*h r) = p-C*h i := by
          rw [← g.marked]
          apply Finset.sum_congr rfl
          intro r hr
          rw [hwo r (Finset.mem_erase.mp hr).1]
        rw [hs, hwi] at he
        linarith
      · intro r hr ht
        by_cases hri : r = i
        · subst r; exact hwi
        · rw [hwo r hri]; exact g.above r (Finset.mem_erase.mpr ⟨hri, hr⟩) ht
      · intro r hr ht
        have hri : r ≠ i := by intro he; subst r; exact (not_lt_of_ge hti) ht
        rw [hwo r hri]
        exact g.below r (Finset.mem_erase.mpr ⟨hri, hr⟩) ht
      · intro r s hr0 hrC hs0 hsC
        have hri : r ≠ i := by intro he; subst r; rw [hwi] at hrC; exact (lt_irrefl _) hrC
        have hsi : s ≠ i := by intro he; subst s; rw [hwi] at hsC; exact (lt_irrefl _) hsC
        rw [hwo r hri] at hr0 hrC
        rw [hwo s hsi] at hs0 hsC
        exact g.onePartial r s hr0 hrC hs0 hsC

end WordCertDensity.Counting
