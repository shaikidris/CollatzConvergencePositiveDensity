/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Counting.TowerPacking
public import WordCertDensity.Counting.StripDebit
public import WordCertDensity.Counting.BandAllocation
import Mathlib.Tactic.Linarith

/-! # Finite shell packing with a single actual integer count -/

@[expose] public section

namespace WordCertDensity.Counting

open scoped BigOperators

/-- Ordered geometric shells have no common source, including their half-open boundaries. -/
theorem geometric_shells_disjoint (I : Finset ℕ) (S : ℕ → Finset ℕ) {Y R : ℝ}
    (hY : 0 < Y) (hR : 1 < R)
    (hS : ∀ j ∈ I, ∀ x ∈ S j, Y / R ^ j ≤ (x : ℝ) ∧ (x : ℝ) < R * (Y / R ^ j)) :
    (I : Set ℕ).PairwiseDisjoint S := by
  have hupper : ∀ i j : ℕ, i < j → R * (Y / R ^ j) ≤ Y / R ^ i := by
    intro i j hij
    calc
      R * (Y / R ^ j) ≤ R * (Y / R ^ (i + 1)) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_left hY.le (by positivity)
            (pow_le_pow_right₀ hR.le (by omega))) (by positivity)
      _ = Y / R ^ i := shell_upper_eq (by linarith) i
  intro i hi j hj hne
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨hli, hui⟩ := hS i hi x hxi
  obtain ⟨hlj, huj⟩ := hS j hj x hxj
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact (not_lt_of_ge hli) (huj.trans_le (hupper i j hij))
  · exact (not_lt_of_ge hlj) (hui.trans_le (hupper j i hji))

/-- Arbitrarily many disjoint source families share one integer-prefix capacity. -/
theorem family_occupation_cost_le_prefixCount (G : Set ℕ) (I : Finset ℕ)
    (S : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ) {Y : ℝ}
    (hclosed : ∀ x ∈ G, ∀ n : ℕ, 2 ^ n * x ∈ G)
    (hd : (I : Set ℕ).PairwiseDisjoint S)
    (hS : ∀ j ∈ I, ∀ x ∈ S j, Odd x ∧ x ∈ G ∧ 0 < x ∧ (x : ℝ) ≤ Y)
    (hw : ∀ j ∈ I, ∀ x ∈ S j, w j x ≤ 1) :
    (∑ j ∈ I, ∑ x ∈ S j, w j x * towerCount Y x) ≤ (prefixCount G ⌊Y⌋₊ : ℝ) := by
  classical
  have hsum := sum_towerCount_le_prefixCount G (I.biUnion S) hclosed (by
    intro x hx
    obtain ⟨j, hj, hx⟩ := Finset.mem_biUnion.mp hx
    exact hS j hj x hx)
  rw [Finset.sum_biUnion hd] at hsum
  calc
    _ ≤ ∑ j ∈ I, ∑ x ∈ S j, (towerCount Y x : ℝ) :=
      Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun x hx => by
        simpa using mul_le_mul_of_nonneg_right (hw j hj x hx) (Nat.cast_nonneg _)))
    _ ≤ _ := by exact_mod_cast hsum

/-- Actual reciprocal-bounded source weights satisfy the finite allocation estimate. -/
theorem weighted_source_band_cost (S : Finset ℕ) (a : ℕ → ℝ) {X s : ℝ} {j : ℕ}
    (hX : 1 ≤ X) (hj : 1 ≤ j) (hs : 1 < s) (hsu : s ≤ 3 / 2)
    (hS : ∀ x ∈ S, x ∈ oddOpenBand X 16 ∧ 0 ≤ a x ∧ a x ≤ (x : ℝ)⁻¹)
    (hm : Real.log s / 2 ≤ ∑ x ∈ S, a x) :
    2 * (j : ℝ) * (s - 1) * X - 4 * j * (s + 1) ≤
      ∑ x ∈ S, ((x : ℝ) * a x) * towerCount ((16 : ℝ) ^ j * X) x := by
  classical
  let w : ℕ → ℝ := fun x => if x ∈ S then (x : ℝ) * a x else 0
  have hsub : S ⊆ oddOpenBand X 16 := fun x hx => (hS x hx).1
  have hpos : ∀ x ∈ S, 0 < (x : ℝ) := by
    intro x hx
    have := ((mem_oddOpenBand X 16 x).mp (hsub hx)).2.1
    linarith
  have hw : ∀ x ∈ oddOpenBand X 16, 0 ≤ w x ∧ w x ≤ 1 := by
    intro x _
    by_cases hx : x ∈ S
    · simp only [w, if_pos hx]
      refine ⟨mul_nonneg (hpos x hx).le (hS x hx).2.1, ?_⟩
      have h := mul_le_mul_of_nonneg_left (hS x hx).2.2 (hpos x hx).le
      simpa only [mul_inv_cancel₀ (ne_of_gt (hpos x hx))] using h
    · simp [w, hx]
  have hmass : (∑ x ∈ oddOpenBand X 16, w x / x) = ∑ x ∈ S, a x := by
    rw [← Finset.sum_subset hsub (fun x _ hx => by simp [w, hx])]
    apply Finset.sum_congr rfl
    intro x hx
    simp only [w, if_pos hx]
    field_simp [ne_of_gt (hpos x hx)]
  have hc := band_occupation_cost hX hj hs hsu w hw (by simpa only [hmass] using hm)
  rw [← Finset.sum_subset hsub (fun x _ hx => by simp [w, hx])] at hc
  have he : (∑ x ∈ S, w x * towerCount ((16 : ℝ) ^ j * X) x) =
      ∑ x ∈ S, ((x : ℝ) * a x) * towerCount ((16 : ℝ) ^ j * X) x := by
    apply Finset.sum_congr rfl
    intro x hx
    simp only [w, if_pos hx]
  rwa [he] at hc

/-- Finite allocations in disjoint exact bands give a lower bound for the same actual set. -/
theorem packed_source_band_cost (G : Set ℕ) (I : Finset ℕ) (S : ℕ → Finset ℕ)
    (a : ℕ → ℕ → ℝ) (s : ℕ → ℝ) {Y : ℝ}
    (hclosed : ∀ x ∈ G, ∀ n : ℕ, 2 ^ n * x ∈ G)
    (hd : (I : Set ℕ).PairwiseDisjoint S)
    (hidx : ∀ j ∈ I, 1 ≤ j ∧ (16 : ℝ) ^ j ≤ Y)
    (hs : ∀ j ∈ I, 1 < s j ∧ s j ≤ 3 / 2)
    (hS : ∀ j ∈ I, ∀ x ∈ S j, x ∈ oddOpenBand (Y / (16 : ℝ) ^ j) 16 ∧
      x ∈ G ∧ 0 ≤ a j x ∧ a j x ≤ (x : ℝ)⁻¹)
    (hm : ∀ j ∈ I, Real.log (s j) / 2 ≤ ∑ x ∈ S j, a j x) :
    (∑ j ∈ I, (2 * (j : ℝ) * (s j - 1) * (Y / (16 : ℝ) ^ j) - 4 * j * (s j + 1))) ≤
      (prefixCount G ⌊Y⌋₊ : ℝ) := by
  have hxpos : ∀ j ∈ I, ∀ x ∈ S j, 0 < (x : ℝ) := by
    intro j hj x hx
    have hlow := ((mem_oddOpenBand _ _ x).mp (hS j hj x hx).1).2.1
    have hbase : 1 ≤ Y / (16 : ℝ) ^ j := (one_le_div (by positivity)).mpr (hidx j hj).2
    linarith
  have hcost := family_occupation_cost_le_prefixCount G I S (fun j x => (x : ℝ) * a j x)
    hclosed hd (by
      intro j hj x hx
      obtain ⟨ho, _, hu⟩ := (mem_oddOpenBand _ _ x).mp (hS j hj x hx).1
      have hY : 0 < Y := (by positivity : (0 : ℝ) < 16 ^ j).trans_le (hidx j hj).2
      have hpow : (16 : ℝ) ≤ 16 ^ j := by
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 16) (hidx j hj).1
      have hupper : 16 * (Y / (16 : ℝ) ^ j) ≤ Y := by
        calc
          _ ≤ (16 : ℝ) ^ j * (Y / (16 : ℝ) ^ j) :=
            mul_le_mul_of_nonneg_right hpow (by positivity)
          _ = Y := mul_div_cancel₀ Y (by positivity)
      exact ⟨ho, (hS j hj x hx).2.1, by exact_mod_cast hxpos j hj x hx,
        hu.le.trans hupper⟩) (by
      intro j hj x hx
      have h := mul_le_mul_of_nonneg_left (hS j hj x hx).2.2.2 (hxpos j hj x hx).le
      simpa only [mul_inv_cancel₀ (ne_of_gt (hxpos j hj x hx))] using h)
  apply le_trans (Finset.sum_le_sum ?_) hcost
  intro j hj
  have h := weighted_source_band_cost (S j) (a j)
    ((one_le_div (by positivity)).mpr (hidx j hj).2) (hidx j hj).1
    (hs j hj).1 (hs j hj).2
    (fun x hx => ⟨(hS j hj x hx).1, (hS j hj x hx).2.2⟩) (hm j hj)
  rwa [mul_div_cancel₀ Y (by positivity : (16 : ℝ) ^ j ≠ 0)] at h

end WordCertDensity.Counting
