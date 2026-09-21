/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Reference.FanEven
import WordCertDensity.Reference.Moments

/-! # Full-group coset sums and exact real-order fan moments -/

namespace WordCertDensity.Reference

open scoped Classical

/-- The residue-zero coset has zero actual density. -/
theorem density_zero_coset (m : ℕ) (y : ZMod (3 ^ (m + 1)))
    (hy : project (show 1 ≤ m + 1 by omega) y = 0) : density (m + 1) y = 0 := by
  apply density_eq_zero_of_not_isUnit (by omega)
  intro hu
  have h := hu.map (project (show 1 ≤ m + 1 by omega))
  rw [hy] at h
  let : Nontrivial (ZMod (3 ^ 1)) := ZMod.nontrivial_iff.mpr (by decide)
  exact not_isUnit_zero h

/-- A test vanishing at zero has exactly the two unit-coset contributions. -/
theorem density_coset_sum (m : ℕ) (Φ : ℝ → ℝ) (hΦ : Φ 0 = 0) :
    (∑ y, Φ (density (m + 1) y)) =
      (∑ x, Φ (density (m + 1) (evenEmbedding m x))) +
      ∑ x, Φ (density (m + 1) (fanEmbedding m x)) := by
  let f : ZMod (3 ^ (m + 1)) → ℝ := fun y => Φ (density (m + 1) y)
  have hs := Finset.sum_fiberwise (Finset.univ : Finset (ZMod (3 ^ (m + 1))))
    (project (show 1 ≤ m + 1 by omega)) f
  change (∑ c : ZMod (3 ^ 1), ∑ y ∈ fiber (show 1 ≤ m + 1 by omega) c, f y) = ∑ y, f y at hs
  have hz : (∑ y ∈ fiber (show 1 ≤ m + 1 by omega) 0, f y) = 0 := by
    apply Finset.sum_eq_zero
    intro y hy
    dsimp [f]
    rw [density_zero_coset m y ((mem_fiber _ _ _).mp hy), hΦ]
  have he : (∑ y ∈ fiber (show 1 ≤ m + 1 by omega) 1, f y) =
      ∑ x, f (evenEmbedding m x) := by
    rw [← image_evenEmbedding, Finset.sum_image
      (fun a _ b _ h => evenEmbedding_injective m h)]
  have ho : (∑ y ∈ fiber (show 1 ≤ m + 1 by omega) 2, f y) =
      ∑ x, f (fanEmbedding m x) := by
    rw [← image_fanEmbedding, Finset.sum_image
      (fun a _ b _ h => fanEmbedding_injective m h)]
  have hU : (Finset.univ : Finset (ZMod (3 ^ 1))) = {0, 1, 2} := by decide
  rw [hU] at hs
  simp only [Finset.sum_insert
    (by decide : (0 : ZMod (3 ^ 1)) ∉ {(1 : ZMod (3 ^ 1)), (2 : ZMod (3 ^ 1))}),
    Finset.sum_insert (by decide : (1 : ZMod (3 ^ 1)) ∉ {(2 : ZMod (3 ^ 1))}),
    Finset.sum_singleton] at hs
  rw [hz, he, ho, zero_add] at hs
  exact hs.symm

/-- The exact full-group fan moment identity holds for every positive real order. -/
theorem fan_moment_identity (s : ℝ) (hs : 0 < s) (m : ℕ) :
    mean m (fun x => fan m x ^ s) =
      (3 * (8 / 9 : ℝ) ^ s / (1 + (2 : ℝ) ^ s)) * moment s (m + 1) := by
  have h := density_coset_sum m (fun x => x ^ s) (Real.zero_rpow hs.ne')
  simp_rw [density_evenEmbedding, density_fanEmbedding] at h
  simp only [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 9 / 8) (fan_nonneg _ _),
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 9 / 4) (fan_nonneg _ _),
    ← Finset.mul_sum] at h
  have hprod : (8 / 9 : ℝ) ^ s * (9 / 8 : ℝ) ^ s = 1 := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8 / 9) (by norm_num : (0 : ℝ) ≤ 9 / 8)]
    norm_num
  have hratio : (9 / 4 : ℝ) ^ s = (2 : ℝ) ^ s * (9 / 8 : ℝ) ^ s := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 9 / 8)]
    norm_num
  have hden : 1 + (2 : ℝ) ^ s ≠ 0 := ne_of_gt (by positivity)
  have hthree : (3 : ℝ) ^ m ≠ 0 := by positivity
  simp only [moment, mean]
  rw [h, hratio, pow_succ]
  field_simp
  linear_combination -(∑ x, fan m x ^ s) * hprod

/-- The retained manuscript domain includes order one. -/
theorem fan_moments (s : ℝ) (hs : 1 ≤ s) (m : ℕ) :
    mean m (fun x => fan m x ^ s) =
      (3 * (8 / 9 : ℝ) ^ s / (1 + (2 : ℝ) ^ s)) * moment s (m + 1) :=
  fan_moment_identity s (by linarith) m

end WordCertDensity.Reference
