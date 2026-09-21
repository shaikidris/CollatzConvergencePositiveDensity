/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.ExactLowLevels
import WordCertDensity.Certificates.FractionalSoundness

/-! # Upper-array summaries and the exact initial maximum and energy rows -/

namespace WordCertDensity.Certificates

open scoped Classical

/-- A natural pointwise numerator check certifies a rational maximum ceiling. -/
theorem integer_maximum_certificate (d S p q : ℕ) (hS : 0 < S) (hq : 0 < q)
    (z : ZMod (3 ^ d) → ℕ)
    (hz : ∀ x, (S : ℝ) * Reference.density d x ≤ z x)
    (hcap : ∀ x, q * z x ≤ p * S) : Reference.maximum d ≤ (p : ℝ) / q := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  apply (le_div_iff₀ (by exact_mod_cast hq : (0 : ℝ) < q)).mpr
  have hu := hz x
  have hc : (q : ℝ) * z x ≤ (p : ℝ) * S := by exact_mod_cast hcap x
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  nlinarith [mul_le_mul_of_nonneg_left hu hqr.le]

/-- A complete integer sum of squares certifies a rational full-group energy ceiling. -/
theorem integer_energy_certificate (d S p q : ℕ) (hS : 0 < S) (hq : 0 < q)
    (z : ZMod (3 ^ d) → ℕ)
    (hz : ∀ x, (S : ℝ) * Reference.density d x ≤ z x)
    (hsum : q * (∑ x, z x ^ 2) ≤ p * 3 ^ d * S ^ 2) :
    Reference.moment 2 d ≤ (p : ℝ) / q := by
  have hp (x : ZMod (3 ^ d)) :
      (S : ℝ) ^ 2 * Reference.density d x ^ 2 ≤ (z x : ℝ) ^ 2 := by
    have h := sq_le_sq₀ (mul_nonneg (Nat.cast_nonneg S) (Reference.density_nonneg d x))
      (Nat.cast_nonneg (z x)) |>.mpr (hz x)
    nlinarith [h]
  have hu := Finset.sum_le_sum (s := Finset.univ) (fun x _ => hp x)
  rw [← Finset.mul_sum] at hu
  have hc : (q : ℝ) * (∑ x, (z x : ℝ) ^ 2) ≤ (p : ℝ) * (3 : ℝ) ^ d * (S : ℝ) ^ 2 := by
    exact_mod_cast hsum
  have hsr : (0 : ℝ) < S := by exact_mod_cast hS
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have h3 : 0 < (3 : ℝ) ^ d := by positivity
  unfold Reference.moment Reference.mean
  simp only [Real.rpow_two]
  apply (div_le_div_iff₀ h3 hqr).mpr
  have h := mul_le_mul_of_nonneg_left hu hqr.le
  nlinarith [sq_pos_of_pos hsr]

/-- The first nontrivial maximum row is exact for the actual reference law. -/
theorem maximum_one : Reference.maximum 1 = 2 := by
  obtain ⟨h0, h1, h2⟩ := Reference.density_one_values
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨x, rfl⟩
    fin_cases x
    · change Reference.density 1 0 ≤ 2
      rw [h0]; norm_num
    · change Reference.density 1 1 ≤ 2
      rw [h1]; norm_num
    · change Reference.density 1 2 ≤ 2
      exact h2.le
  · simpa only [h2] using Reference.density_le_maximum 1 2

/-- The complete depth-two vector has the printed exact maximum. -/
theorem maximum_two : Reference.maximum 2 = 22 / 7 := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨x, rfl⟩
    rw [Reference.density_two_vector]
    have hv (i : Fin 9) :
        (([0, 8/7, 16/7, 0, 11/7, 4/7, 0, 2/7, 22/7] : List ℝ)[i.val]?.getD 0) ≤ 22 / 7 := by
      fin_cases i <;> norm_num
    exact hv x
  · have h := Reference.density_le_maximum 2 8
    rw [Reference.density_two_vector] at h
    norm_num at h ⊢
    exact h

/-- Full-group summation gives the exact depth-one second moment. -/
theorem energy_one : Reference.moment 2 1 = 5 / 3 := by
  obtain ⟨h0, h1, h2⟩ := Reference.density_one_values
  unfold Reference.moment Reference.mean
  simp only [Real.rpow_two, pow_one]
  change (∑ x : Fin 3, Reference.density 1 x ^ 2) / 3 = 5 / 3
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (Reference.density 1 0 ^ 2 + (Reference.density 1 1 ^ 2 +
    (Reference.density 1 2 ^ 2 + 0))) / 3 = 5 / 3
  rw [h0, h1, h2]
  norm_num

/-- Full-group summation of the complete exact seed gives the depth-two second moment. -/
theorem energy_two : Reference.moment 2 2 = 15 / 7 := by
  unfold Reference.moment Reference.mean
  simp only [Real.rpow_two, Reference.density_two_vector]
  change (∑ x : Fin 9,
    (([0, 8/7, 16/7, 0, 11/7, 4/7, 0, 2/7, 22/7] : List ℝ)[x.val]?.getD 0) ^ 2) /
      (3 : ℝ) ^ 2 = 15 / 7
  norm_num [Fin.sum_univ_succ]

end WordCertDensity.Certificates
