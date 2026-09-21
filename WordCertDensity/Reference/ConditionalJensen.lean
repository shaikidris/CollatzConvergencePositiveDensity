/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Probability.FiniteValueJensen
public import WordCertDensity.Reference.FiberAverages

/-! # Convex averaging of the exact conditional reference mixture -/

@[expose] public section

namespace WordCertDensity.Reference

open scoped Classical

/-- Conditional Jensen on a complete projection fiber, including a zero-density fiber. -/
theorem conditional_jensen (u v : ℕ) (y : ZMod (3 ^ v))
    (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ (Set.Ici 0) Φ) :
    mean u (fun z => Φ (density (u + v) (fiberLift u v y z))) ≤
      mean u (fun x => Φ (density v y * density u x)) := by
  by_cases hy : density v y = 0
  · simp only [affine_mixture_zero_fiber u v y hy, hy, zero_mul]
    exact le_rfl
  have hy0 : 0 < density v y := lt_of_le_of_ne (density_nonneg v y) (Ne.symm hy)
  let c : ValuationWord → ℝ := fun w => mixtureCoefficient v y w / density v y
  let τ : ValuationWord → ZMod (3 ^ u) → ZMod (3 ^ u) :=
    fun w z => mixtureShift u v y w + mixtureMultiplier u w * z
  have hc : Summable c := (mixtureCoefficient_summable v y).div_const _
  have hc0 : ∀ w, 0 ≤ c w := fun w =>
    div_nonneg (mixtureCoefficient_nonneg v y w) hy0.le
  have hc1 : ∑' w, c w = 1 := by
    simp only [c, tsum_div_const, mixtureCoefficient_sum, div_self hy]
  have heq (z : ZMod (3 ^ u)) :
      (∑' w, c w * (density v y * density u (τ w z))) =
        density (u + v) (fiberLift u v y z) := by
    rw [affine_mixture]
    apply tsum_congr
    intro w
    dsimp [c, τ]
    field_simp
  have hj (z : ZMod (3 ^ u)) := FiniteValue.jensen hc hc0 hc1 (fun w => τ w z)
    (fun x => density v y * density u x)
    (fun x => mul_nonneg hy0.le (density_nonneg u x)) Φ hΦ
  have hs (z : ZMod (3 ^ u)) :
      Summable (fun w => c w * Φ (density v y * density u (τ w z))) :=
    FiniteValue.summable_weighted hc hc0 (fun w => τ w z)
      (fun x => Φ (density v y * density u x))
  calc
    mean u (fun z => Φ (density (u + v) (fiberLift u v y z))) ≤
        mean u (fun z => ∑' w, c w * Φ (density v y * density u (τ w z))) :=
      mean_mono u _ _ (fun z => by simpa only [heq z] using hj z)
    _ = ∑' w, mean u (fun z => c w * Φ (density v y * density u (τ w z))) :=
      mean_tsum_index u _ hs
    _ = ∑' w, c w * mean u (fun x => Φ (density v y * density u x)) := by
      apply tsum_congr
      intro w
      rw [mean_mul]
      congr 1
      exact mean_mixtureAffine u v y w (fun x => Φ (density v y * density u x))
    _ = mean u (fun x => Φ (density v y * density u x)) := by
      rw [tsum_mul_right, hc1, one_mul]

/-- All finite convex tests inherit across reference blocks; monotonicity is unnecessary. -/
theorem convex_inheritance (Φ : ℝ → ℝ) (hΦ : ConvexOn ℝ (Set.Ici 0) Φ) (u v : ℕ) :
    mean (u + v) (fun z => Φ (density (u + v) z)) ≤
      mean u (fun x => mean v (fun y => Φ (density u x * density v y))) := by
  rw [mean_fibers]
  conv_rhs => rw [mean_comm]
  exact mean_mono v _ _ (fun y => by
    simpa only [mul_comm] using conditional_jensen u v y Φ hΦ)

end WordCertDensity.Reference
