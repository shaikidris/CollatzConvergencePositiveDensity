/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Reference.FanCoset

/-! # Exact fan maximum and second-moment normalization -/

namespace WordCertDensity.Reference

open scoped Classical

/-- The maximum over the complete finite fan profile. -/
noncomputable def fanMaximum (m : ℕ) : ℝ := sSup (Set.range (fan m))

/-- The finite maximum bounds every actual fan value. -/
theorem fan_le_maximum (m : ℕ) (x : ZMod (3 ^ m)) : fan m x ≤ fanMaximum m :=
  le_csSup (Set.finite_range (fan m)).bddAbove (Set.mem_range_self x)

/-- The fan maximum is nonnegative at every level. -/
theorem fanMaximum_nonneg (m : ℕ) : 0 ≤ fanMaximum m :=
  (fan_nonneg m 0).trans (fan_le_maximum m 0)

/-- Both unit cosets and the zero coset are bounded by the residue-two fan ceiling. -/
theorem density_le_fanMaximum (m : ℕ) (y : ZMod (3 ^ (m + 1))) :
    density (m + 1) y ≤ (9 / 4 : ℝ) * fanMaximum m := by
  have hc : ∀ c : ZMod (3 ^ 1), c = 0 ∨ c = 1 ∨ c = 2 := by decide
  rcases hc (project (show 1 ≤ m + 1 by omega) y) with h0 | h1 | h2
  · rw [density_zero_coset m y h0]
    exact mul_nonneg (by norm_num) (fanMaximum_nonneg m)
  · have hy : y ∈ Finset.univ.image (evenEmbedding m) := by
      rw [image_evenEmbedding]
      exact (mem_fiber _ _ _).mpr h1
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    rw [density_evenEmbedding]
    have h := fan_le_maximum m x
    have hz := fanMaximum_nonneg m
    linarith
  · have hy : y ∈ Finset.univ.image (fanEmbedding m) := by
      rw [image_fanEmbedding]
      exact (mem_fiber _ _ _).mpr h2
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    rw [density_fanEmbedding]
    exact mul_le_mul_of_nonneg_left (fan_le_maximum m x) (by norm_num)

/-- The exact maximum factor uses the entire next-level density profile. -/
theorem fan_maximum_identity (m : ℕ) : fanMaximum m = (4 / 9 : ℝ) * maximum (m + 1) := by
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨x, rfl⟩
    rw [fan_density_identity]
    exact mul_le_mul_of_nonneg_left (density_le_maximum (m + 1) _) (by norm_num)
  · have h : maximum (m + 1) ≤ (9 / 4 : ℝ) * fanMaximum m := by
      apply csSup_le (Set.range_nonempty _)
      rintro _ ⟨y, rfl⟩
      exact density_le_fanMaximum m y
    linarith

/-- The second moment has the printed exact factor sixty-four over one hundred thirty-five. -/
theorem fan_second_moment (m : ℕ) :
    mean m (fun x => fan m x ^ (2 : ℝ)) = (64 / 135 : ℝ) * moment 2 (m + 1) := by
  have h := fan_moments 2 (by norm_num) m
  norm_num at h
  simpa only [Real.rpow_two] using h

end WordCertDensity.Reference
