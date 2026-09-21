/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.ParametricLevels
import WordCertDensity.Construction.GraftBoundaryCutoff

/-! # Parameter-dependent mixing and the unchanged conductor boundary

Both marker costs retain the sixth inverse power of the fixed positive
parameter. The same printed cutoff pays the actual finite-modulus boundary.
-/

namespace WordCertDensity.Construction

/-- The literal finite-modulus boundary at the parameterized conductor. -/
noncomputable def parametricBoundary (θ L δ : ℝ) (B : ℕ) : ℝ :=
  (3 : ℝ) ^ parametricConductor θ L δ B * (1 / 8 : ℝ) ^ B

/-- Both marker errors and the original, unnormalized rejection deficit. -/
noncomputable def parametricError (θ L δ : ℝ) (B : ℕ) : ℝ :=
  Analytic.mixingError (parametricLevel θ (B + macroLength L B)) +
    Analytic.mixingError (parametricLevel θ B) + 1 - macroblockMass L δ B

theorem parametricBoundary_pos (θ L δ : ℝ) (B : ℕ) : 0 < parametricBoundary θ L δ B := by
  unfold parametricBoundary
  positivity

/-- Smaller positive markers retain the full boundary and only decrease it. -/
theorem parametricBoundary_le_fixed {θ : ℝ} (hθ : θ ≤ 1 / 1000) (L δ : ℝ) (B : ℕ) :
    parametricBoundary θ L δ B ≤ macroBoundary L δ B :=
  mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) (parametricConductor_le_fixed hθ L δ B)) (by positivity)

/-- No new boundary cutoff is needed as the fixed positive parameter decreases. -/
theorem parametricBoundary_le_one_of_cutoff {θ L : ℝ} (hθ : θ ≤ 1 / 1000)
    (hL : 0 ≤ L) (δ : ℝ) {B : ℕ} (hB : graftBoundaryCutoff L ≤ (B : ℝ)) :
    parametricBoundary θ L δ B ≤ 1 :=
  (parametricBoundary_le_fixed hθ L δ B).trans (macroBoundary_le_one_of_graftCutoff hL δ hB)

/-- Exact recovery of the two fixed-scale error definitions. -/
theorem parametricError_fixed (L δ : ℝ) (B : ℕ) :
    parametricError (1 / 1000) L δ B = macroError L δ B := by
  simp only [parametricError, macroError, parametricLevel_fixed]

/-- The true positive count retains exactly the sixth inverse power of theta. -/
theorem parametricLevel_mixing_le {θ : ℝ} (hθ : 0 < θ) {B k : ℕ} (hB : 1 ≤ B)
    (hk : parametricLevel θ B ≤ k) :
    Analytic.mixingError k ≤ (Analytic.mixingCoefficient : ℝ) * (θ⁻¹) ^ 6 / (B : ℝ) ^ 6 := by
  have hb : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have he : θ * B ≤ k := (parametricLevel_bounds hθ.le B).1.trans (Nat.cast_le.mpr hk)
  have hm := Analytic.mixingError_le_order6 ((parametricLevel_pos hθ hB).trans hk)
  have hp := Real.rpow_le_rpow_of_nonpos (mul_pos hθ hb) he (by norm_num : (-6 : ℝ) ≤ 0)
  apply hm.trans
  have hmul := mul_le_mul_of_nonneg_left hp Analytic.mixingCoefficient_pos.le
  convert hmul using 1
  rw [Real.mul_rpow hθ.le hb.le]
  norm_num [Real.rpow_neg, Real.rpow_natCast, div_eq_mul_inv, inv_pow, mul_assoc]

theorem parametricError_nonneg {θ : ℝ} (hθ : 0 < θ) (L δ : ℝ) {B : ℕ} (hB : 1 ≤ B) :
    0 ≤ parametricError θ L δ B := by
  have hg := parametricConductor_guards hθ L δ hB
  have hnew := (Analytic.mixingError_pos (hg.1.trans hg.2.1)).le
  have hold := (Analytic.mixingError_pos hg.1).le
  have hm := (macroblockMass_bounds L δ B).2
  unfold parametricError
  linarith

/-- Both marker costs and the full rejected mass have the required common order-six bound. -/
theorem parametricError_le {θ L δ : ℝ} (hθ : 0 < θ) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) {B : ℕ} (hB : 1 ≤ B) :
    parametricError θ L δ B ≤
      (2 * (Analytic.mixingCoefficient : ℝ) * (θ⁻¹) ^ 6 + L + 5) / (B : ℝ) ^ 6 := by
  have hb : (1 : ℝ) ≤ B := Nat.one_le_cast.mpr hB
  have hold := parametricLevel_mixing_le hθ hB (le_refl (parametricLevel θ B))
  have hnew := parametricLevel_mixing_le hθ hB
    (parametricLevel_mono hθ.le (Nat.le_add_right B (macroLength L B)))
  have hdef := (macroblockMass_deficit_bounds hL hδ hpay B).2
  have hpow : ((B : ℝ) + 2) ^ (-9 : ℝ) ≤ (B : ℝ) ^ (-6 : ℝ) := by
    apply (Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ (B : ℝ) + 2)
      (by norm_num : (-9 : ℝ) ≤ -6)).trans
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
  have hdef' := hdef.trans (mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ L + 5))
  have hdef'' : 1 - macroblockMass L δ B ≤ (L + 5) / (B : ℝ) ^ 6 := by
    simpa only [Real.rpow_neg (by linarith : (0 : ℝ) ≤ B),
      show (6 : ℝ) = (6 : ℕ) by norm_num, Real.rpow_natCast, div_eq_mul_inv] using hdef'
  unfold parametricError
  calc
    _ ≤ (Analytic.mixingCoefficient : ℝ) * (θ⁻¹) ^ 6 / (B : ℝ) ^ 6 +
        (Analytic.mixingCoefficient : ℝ) * (θ⁻¹) ^ 6 / (B : ℝ) ^ 6 +
        (L + 5) / (B : ℝ) ^ 6 := by linarith
    _ = _ := by ring

end WordCertDensity.Construction
