/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Counting.DyadicCost
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

/-! # Actual integer counts from disjoint odd dyadic towers -/

@[expose] public section

namespace WordCertDensity.Counting

open scoped BigOperators

noncomputable section

/-- The actual finite positive prefix of a dyadic tower. -/
def dyadicPrefix (x N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter (fun z => ∃ n : ℕ, 2 ^ n * x = z)

/-- The finite tower prefix retains both the positive cutoff and its exponent witness. -/
theorem mem_dyadicPrefix (x N z : ℕ) :
    z ∈ dyadicPrefix x N ↔ 1 ≤ z ∧ z ≤ N ∧ ∃ n : ℕ, 2 ^ n * x = z := by
  classical
  simp [dyadicPrefix, and_assoc]

/-- A positive integer has at most one expression as an odd base times a power of two. -/
theorem odd_dyadic_unique {x y n m : ℕ} (hx : Odd x) (hy : Odd y)
    (heq : 2 ^ n * x = 2 ^ m * y) : x = y ∧ n = m := by
  induction n generalizing m with
  | zero =>
    cases m with
    | zero => simpa using heq
    | succ m =>
      have h : Even x := by
        refine ⟨2 ^ m * y, ?_⟩
        simp only [pow_zero, one_mul, pow_succ] at heq
        nlinarith
      exact False.elim ((Nat.not_even_iff_odd.mpr hx) h)
  | succ n ih =>
    cases m with
    | zero =>
      have h : Even y := by
        refine ⟨2 ^ n * x, ?_⟩
        simp only [pow_zero, one_mul, pow_succ] at heq
        nlinarith
      exact False.elim ((Nat.not_even_iff_odd.mpr hy) h)
    | succ m =>
      have h : 2 ^ n * x = 2 ^ m * y := by
        simp only [pow_succ] at heq
        nlinarith
      obtain ⟨hxy, hnm⟩ := ih h
      exact ⟨hxy, congrArg Nat.succ hnm⟩

/-- Different odd bases have disjoint finite towers, independently of the cutoff. -/
theorem dyadicPrefix_disjoint {x y N : ℕ} (hx : Odd x) (hy : Odd y) (hne : x ≠ y) :
    Disjoint (dyadicPrefix x N) (dyadicPrefix y N) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨_, _, n, hn⟩ := (mem_dyadicPrefix x N z).mp hz
  obtain ⟨_, _, m, hm⟩ := (mem_dyadicPrefix y N z).mp hz'
  exact hne (odd_dyadic_unique hx hy (hn.trans hm.symm)).1

/-- The previously proved exact logarithmic formula counts this literal finite tower. -/
theorem card_dyadicPrefix {Y : ℝ} {x : ℕ} (hx : 0 < x) (hY : (x : ℝ) ≤ Y) :
    (dyadicPrefix x ⌊Y⌋₊).card = towerCount Y x := by
  rw [towerCount_eq_prefixCount hx hY]
  rfl

/-- Summed tower counts of distinct odd sources do not exceed the actual integer prefix. -/
theorem sum_towerCount_le_prefixCount (G : Set ℕ) (S : Finset ℕ) {Y : ℝ}
    (hclosed : ∀ x ∈ G, ∀ n : ℕ, 2 ^ n * x ∈ G)
    (hS : ∀ x ∈ S, Odd x ∧ x ∈ G ∧ 0 < x ∧ (x : ℝ) ≤ Y) :
    (∑ x ∈ S, towerCount Y x) ≤ prefixCount G ⌊Y⌋₊ := by
  classical
  have hd : (S : Set ℕ).PairwiseDisjoint (fun x => dyadicPrefix x ⌊Y⌋₊) := by
    intro x hx y hy hne
    exact dyadicPrefix_disjoint (hS x hx).1 (hS y hy).1 hne
  have hsub : S.biUnion (fun x => dyadicPrefix x ⌊Y⌋₊) ⊆
      (Finset.Icc 1 ⌊Y⌋₊).filter (fun z => z ∈ G) := by
    intro z hz
    obtain ⟨x, hx, hz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hpos, htop, n, rfl⟩ := (mem_dyadicPrefix x ⌊Y⌋₊ z).mp hz
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpos, htop⟩, hclosed x (hS x hx).2.1 n⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_biUnion hd] at hc
  have he : (∑ x ∈ S, (dyadicPrefix x ⌊Y⌋₊).card) = ∑ x ∈ S, towerCount Y x :=
    Finset.sum_congr rfl (fun x hx => card_dyadicPrefix (hS x hx).2.2.1 (hS x hx).2.2.2)
  rw [he] at hc
  exact hc

/-- Fractional occupations charge no more than one copy of each actual dyadic tower. -/
theorem occupation_towerCost_le_prefixCount (G : Set ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    {Y : ℝ} (hclosed : ∀ x ∈ G, ∀ n : ℕ, 2 ^ n * x ∈ G)
    (hS : ∀ x ∈ S, Odd x ∧ x ∈ G ∧ 0 < x ∧ (x : ℝ) ≤ Y)
    (hw : ∀ x ∈ S, w x ≤ 1) :
    (∑ x ∈ S, w x * towerCount Y x) ≤ (prefixCount G ⌊Y⌋₊ : ℝ) := by
  calc
    _ ≤ ∑ x ∈ S, (towerCount Y x : ℝ) := Finset.sum_le_sum (fun x hx => by
      simpa using mul_le_mul_of_nonneg_right (hw x hx) (Nat.cast_nonneg (towerCount Y x)))
    _ ≤ _ := by exact_mod_cast sum_towerCount_le_prefixCount G S hclosed hS

end

end WordCertDensity.Counting
