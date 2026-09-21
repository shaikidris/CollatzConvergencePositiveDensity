/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Transfer.LetterParity

/-! # The factor-two one-letter operator bound and reference marker cap -/

@[expose] public section

namespace WordCertDensity.Transfer

/-- Bounded one-letter payloads retain at most twice their bound under finite transfer. -/
theorem letterOperator_sum_le (n r : ℕ) (A : Finset ℕ+) {B : ℝ} (hB : 0 ≤ B)
    (g : ℕ+ → ZMod (3 ^ n) → ℝ) (hg : ∀ a z, g a z ≤ B) :
    (∑ a ∈ A, wordOperator [a] (n + 1) (g a) (r : ZMod (3 ^ (n + 1)))) ≤ 2 * B := by
  classical
  by_cases hr : 3 ∣ r
  · have he (a : ℕ+) : wordOperator [a] (n + 1) (g a)
        (r : ZMod (3 ^ (n + 1))) = 0 :=
      wordOperator_off_image _ _ _ _ (singleton_off_image_of_three_dvd hr a n)
    simp_rw [he]
    simp only [Finset.sum_const_zero]
    positivity
  · let S := A.filter (fun a => (r : ZMod (3 ^ (n + 1))) ∈ Set.range (wordMap [a] (n + 1)))
    have hs := compatibleLetter_sum_le hr S (fun a ha => (Finset.mem_filter.mp ha).2)
    calc
      _ ≤ ∑ a ∈ A, if (r : ZMod (3 ^ (n + 1))) ∈ Set.range (wordMap [a] (n + 1))
          then (3 / (2 : ℝ) ^ (a : ℕ)) * B else 0 := by
        apply Finset.sum_le_sum
        intro a _
        split_ifs with ha
        · obtain ⟨z, hz⟩ := ha
          rw [← hz, wordOperator_image [a] (show [a].length ≤ n + 1 by simp)]
          have h := mul_le_mul_of_nonneg_left (hg a z) (weight_pos [a]).le
          simpa only [weight_eq, List.length_singleton, ValuationWord.total,
            List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, pow_one] using h
        · rw [wordOperator_off_image _ _ _ _ ha]
      _ = (∑ a ∈ S, 3 / (2 : ℝ) ^ (a : ℕ)) * B := by
        simp only [Finset.sum_mul, S, Finset.sum_filter, ite_mul, zero_mul]
      _ ≤ 2 * B := mul_le_mul_of_nonneg_right hs hB

/-- A countable nonnegative bounded one-letter transfer has the same factor-two cap. -/
theorem letterOperator_tsum_le (n : ℕ) (y : ZMod (3 ^ (n + 1))) {B : ℝ} (hB : 0 ≤ B)
    (g : ℕ+ → ZMod (3 ^ n) → ℝ) (hg0 : ∀ a z, 0 ≤ g a z) (hg : ∀ a z, g a z ≤ B) :
    (∑' a : ℕ+, wordOperator [a] (n + 1) (g a) y) ≤ 2 * B := by
  apply Real.tsum_le_of_sum_le (fun a => wordOperator_nonneg _ _ _ (hg0 a) y)
  intro A
  simpa only [ZMod.natCast_zmod_val] using letterOperator_sum_le n y.val A hB g hg

end WordCertDensity.Transfer

namespace WordCertDensity.Reference

/-- The reference marker has the elementary exponential cap at every level. -/
theorem marker_le_two_pow (n : ℕ) (y : ZMod (3 ^ n)) : marker n y ≤ (2 / 3 : ℝ) * 2 ^ n := by
  induction n with
  | zero => rw [marker_zero]; norm_num
  | succ n ih =>
    rw [marker_succ]
    have h := Transfer.letterOperator_tsum_le n y
      (by positivity : (0 : ℝ) ≤ (2 / 3) * 2 ^ n)
      (fun _ => marker n) (fun _ => marker_nonneg n) (fun _ => ih)
    calc
      _ ≤ 2 * ((2 / 3 : ℝ) * 2 ^ n) := h
      _ = _ := by rw [pow_succ]; ring

end WordCertDensity.Reference
