/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import WordCertDensity.Reference.ConditionalJensen

/-! # All real-order moments and maximum inheritance for the reference law -/

@[expose] public section

namespace WordCertDensity.Reference

open scoped Classical

/-- Full-group moment, with the original density normalization at every level. -/
noncomputable def moment (s : ℝ) (n : ℕ) : ℝ := mean n (fun x => density n x ^ s)

/-- Maximum of the actual finite reference density, including the one-point level zero. -/
noncomputable def maximum (n : ℕ) : ℝ := sSup (Set.range (density n))

/-- Every real-order moment is nonnegative. -/
theorem moment_nonneg (s : ℝ) (n : ℕ) : 0 ≤ moment s n :=
  mean_nonneg n _ (fun x => Real.rpow_nonneg (density_nonneg n x) s)

/-- Order one retains mean one exactly. -/
theorem moment_one (n : ℕ) : moment 1 n = 1 := by
  simp only [moment, Real.rpow_one, mean_density]

/-- The level-zero moment is one at every real order. -/
theorem moment_zero (s : ℝ) : moment s 0 = 1 := by
  simp only [moment, density_zero, Real.one_rpow, mean_const]

/-- Jensen gives submultiplicativity for every real order at least one, including empty blocks. -/
theorem moment_inheritance (s : ℝ) (hs : 1 ≤ s) (u v : ℕ) :
    moment s (u + v) ≤ moment s u * moment s v := by
  have h := convex_inheritance (fun x => x ^ s) (convexOn_rpow hs) u v
  simp only [Real.mul_rpow (density_nonneg _ _) (density_nonneg _ _), mean_mul] at h
  calc
    moment s (u + v) ≤ mean u (fun x => density u x ^ s * moment s v) := h
    _ = moment s u * moment s v := by
      simp only [mul_comm _ (moment s v), mean_mul]
      rfl

/-- Each actual reference density value is bounded by its finite maximum. -/
theorem density_le_maximum (n : ℕ) (x : ZMod (3 ^ n)) : density n x ≤ maximum n :=
  le_csSup (Set.finite_range (density n)).bddAbove (Set.mem_range_self x)

/-- The reference maximum is nonnegative. -/
theorem maximum_nonneg (n : ℕ) : 0 ≤ maximum n :=
  (density_nonneg n 0).trans (density_le_maximum n 0)

/-- The empty-block maximum is exactly one. -/
theorem maximum_zero : maximum 0 = 1 := by
  apply le_antisymm
  · exact csSup_le (Set.range_nonempty _) (by rintro _ ⟨x, rfl⟩; exact (density_zero x).le)
  · simpa only [density_zero] using density_le_maximum 0 0

/-- On each complete fiber the short-block maximum is scaled by its actual coarse density. -/
theorem density_fiber_le_maximum (u v : ℕ) (y : ZMod (3 ^ v)) (z : ZMod (3 ^ u)) :
    density (u + v) (fiberLift u v y z) ≤ maximum u * density v y := by
  have hs := FiniteValue.summable_weighted (mixtureCoefficient_summable v y)
    (mixtureCoefficient_nonneg v y)
    (fun w => mixtureShift u v y w + mixtureMultiplier u w * z) (density u)
  calc
    density (u + v) (fiberLift u v y z) =
        ∑' w, mixtureCoefficient v y w *
          density u (mixtureShift u v y w + mixtureMultiplier u w * z) :=
      affine_mixture u v y z
    _ ≤ ∑' w, mixtureCoefficient v y w * maximum u :=
      hs.tsum_le_tsum (fun w => mul_le_mul_of_nonneg_left
        (density_le_maximum u _) (mixtureCoefficient_nonneg v y w))
        ((mixtureCoefficient_summable v y).mul_right _)
    _ = maximum u * density v y := by
      rw [tsum_mul_right, mixtureCoefficient_sum, mul_comm]

/-- The actual finite maximum is submultiplicative for all block lengths. -/
theorem maximum_inheritance (u v : ℕ) : maximum (u + v) ≤ maximum u * maximum v := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨x, rfl⟩
  have hx : x ∈ Finset.univ.image (fiberLift u v (project (Nat.le_add_left v u) x)) := by
    rw [image_fiberLift]
    exact (mem_fiber _ _ _).mpr rfl
  obtain ⟨z, _, hz⟩ := Finset.mem_image.mp hx
  have h := (density_fiber_le_maximum u v (project (Nat.le_add_left v u) x) z).trans
    (mul_le_mul_of_nonneg_left (density_le_maximum v _) (maximum_nonneg u))
  simpa only [hz] using h

end WordCertDensity.Reference
