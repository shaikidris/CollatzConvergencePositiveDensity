/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.CyclicTransfer

/-! # Sound majorants and backward propagation for the cyclic certificate -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Bounded nonnegative cyclic inputs give the original summable binary series. -/
theorem cyclicSum_summable {g : ℕ → ℝ} {M : ℝ}
    (hg : ∀ j, 0 ≤ g j ∧ g j ≤ M) (i : ℕ) :
    Summable (fun j : ℕ => (2 : ℝ) ^ (-((j + 1 : ℕ) : ℤ)) * g (i + j + 1)) := by
  have h := (weightedSeries_summable (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) (fun j => hg (i + j + 1))).div_const 2
  exact h.congr (fun j => by rw [cyclicCoefficient_eq]; ring)

/-- Pointwise domination survives the exact positive infinite cyclic convolution. -/
theorem cyclicSum_mono_of_bounds {g h : ℕ → ℝ} {M : ℝ}
    (hg : ∀ j, 0 ≤ g j) (hh : ∀ j, 0 ≤ h j ∧ h j ≤ M)
    (hle : ∀ j, g j ≤ h j) (i : ℕ) : cyclicSum g i ≤ cyclicSum h i := by
  have hc (j : ℕ) : 0 ≤ (2 : ℝ) ^ (-((j + 1 : ℕ) : ℤ)) := by
    rw [cyclicCoefficient_eq]
    positivity
  have hs := cyclicSum_summable hh i
  have ht := Summable.of_nonneg_of_le
    (fun j => mul_nonneg (hc j) (hg (i + j + 1)))
    (fun j => mul_le_mul_of_nonneg_left (hle (i + j + 1)) (hc j)) hs
  exact ht.tsum_le_tsum
    (fun j => mul_le_mul_of_nonneg_left (hle (i + j + 1)) (hc j)) hs

/-- Upper arrays retain their order after compatibility and quotient selection. -/
theorem cycleEntry_mono (n : ℕ) (f g : ZMod (3 ^ n) → ℝ)
    (h : ∀ x, f x ≤ g x) (i : ℕ) : cycleEntry n f i ≤ cycleEntry n g i := by
  unfold cycleEntry compatibleInput
  split_ifs
  · exact h _
  · exact le_rfl

/-- The cyclic computation from any bounded upper input dominates the actual next density. -/
theorem cyclic_density_upper (n : ℕ) (f : ZMod (3 ^ n) → ℝ) (M : ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hupper : ∀ x, Reference.density n x ≤ f x)
    (i : ℕ) : Reference.density (n + 1) ((2 : ZMod (3 ^ (n + 1))) ^ i) ≤
      3 * cyclicSum (cycleEntry n f) i := by
  rw [cyclic_density_transfer]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 3)
  apply cyclicSum_mono_of_bounds _ (cycleEntry_bounds n f M hf)
    (cycleEntry_mono n (Reference.density n) f hupper)
  intro j
  unfold cycleEntry compatibleInput
  split_ifs
  · exact Reference.density_nonneg n _
  · exact le_rfl

/-- The finite initialization bound is an upper bound on the actual residue-one density. -/
theorem cyclic_density_seed_bound (n : ℕ) (f : ZMod (3 ^ n) → ℝ) (M : ℝ)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ M) (hupper : ∀ x, Reference.density n x ≤ f x)
    (T : ℕ) : Reference.density (n + 1) 1 ≤
      3 * ((∑ a ∈ Finset.range T, (2 : ℝ) ^ (-((a + 1 : ℕ) : ℤ)) *
        cycleEntry n f (a + 1)) + M / (2 : ℝ) ^ T) := by
  have hu := cyclic_density_upper n f M hf hupper 0
  have ht := cyclicSum_tail_le (cycleEntry_bounds n f M hf) T
  have hm := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 3)
  simpa only [pow_zero] using hu.trans hm

/-- Every certified backward update preserves the upper bound down to index zero. -/
theorem cyclicUpperInduction (h g : ℕ → ℝ) (z : ℕ → ℕ) (n : ℕ)
    (hrec : ∀ i < n, h i = (g (i + 1) + h (i + 1)) / 2) (hn : h n ≤ z n)
    (hstep : ∀ i < n, g (i + 1) + (z (i + 1) : ℝ) ≤ 2 * z i) :
    ∀ i ≤ n, h i ≤ z i := by
  have descend : ∀ k i : ℕ, i + k = n → h i ≤ z i := by
    intro k
    induction k with
    | zero =>
      intro i hi
      have he : i = n := by omega
      simpa only [he] using hn
    | succ k ih =>
      intro i hi
      have hin : i < n := by omega
      have hnext := ih (i + 1) (by omega)
      have hr := hrec i hin
      have hs := hstep i hin
      linarith
  intro i hi
  exact descend (n - i) i (by omega)

/-- The cyclic driver keeps its seed at zero and updates only the positive interior indices. -/
theorem cyclicUpper_periodic (g : ℕ → ℝ) (M : ℝ) (p : ℕ) (hp : 0 < p)
    (hg : ∀ j, 0 ≤ g j ∧ g j ≤ M) (hperiod : ∀ j, g (j + p) = g j)
    (z : ℕ → ℕ) (hseed : cyclicSum g 0 ≤ z 0) (hwrap : z p = z 0)
    (hstep : ∀ i, 0 < i → i < p → g (i + 1) + (z (i + 1) : ℝ) ≤ 2 * z i) :
    ∀ i < p, cyclicSum g i ≤ z i := by
  have hn : cyclicSum g p ≤ z p := by
    have h := cyclicSum_periodic hperiod 0
    simp only [Nat.zero_add] at h
    rw [h, hwrap]
    exact hseed
  have hb := cyclicUpperInduction (fun i => cyclicSum g (i + 1))
    (fun i => g (i + 1)) (fun i => z (i + 1)) (p - 1)
    (fun i _ => cyclicSum_recurrence hg (i + 1))
    (by simpa only [show p - 1 + 1 = p by omega] using hn)
    (fun i hi => hstep (i + 1) (by omega) (by omega))
  intro i hi
  by_cases hi0 : i = 0
  · simpa only [hi0] using hseed
  · have h := hb (i - 1) (by omega)
    simpa only [show i - 1 + 1 = i by omega] using h

end WordCertDensity.Certificates
