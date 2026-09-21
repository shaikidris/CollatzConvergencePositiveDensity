/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.MacroLevels
import WordCertDensity.Analytic.FullMixing
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Positivity

/-!
# Actual macroblock boundary and error decay

The conductor is the next literal level plus the actual maximal word depth.
Both mixing levels and the original rejected mass remain in the error.
-/

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- Residual single-point capacity at the actual next conductor. -/
noncomputable def macroBoundary (L δ : ℝ) (B : ℕ) : ℝ :=
  (3 : ℝ) ^ macroConductor L δ B * (1 / 8 : ℝ) ^ B

/-- All three costs in the literal stopped-transfer application. -/
noncomputable def macroError (L δ : ℝ) (B : ℕ) : ℝ :=
  Analytic.mixingError (macroLevel (B + macroLength L B)) +
    Analytic.mixingError (macroLevel B) + 1 - macroblockMass L δ B

/-- The boundary term is positive, including at the initial count. -/
theorem macroBoundary_pos (L δ : ℝ) (B : ℕ) : 0 < macroBoundary L δ B := by
  unfold macroBoundary
  positivity

/-- The exact conductor gives a geometric majorant after a finite initial segment. -/
theorem eventually_macroBoundary_le {L : ℝ} (hL : 0 ≤ L) (δ : ℝ) :
    ∀ᶠ B in atTop, macroBoundary L δ B ≤ (3 / 8 : ℝ) ^ B := by
  filter_upwards [eventually_macroConductor_le_count hL δ] with B hB
  calc
    _ ≤ (3 : ℝ) ^ B * (1 / 8 : ℝ) ^ B :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hB) (by positivity)
    _ = _ := by rw [← mul_pow]; norm_num

/-- Every fixed polynomial weight preserves summability of the actual boundary. -/
theorem summable_pow_macroBoundary {L : ℝ} (hL : 0 ≤ L) (δ : ℝ) (d : ℕ) :
    Summable (fun B : ℕ => ((B : ℝ) + 2) ^ d * macroBoundary L δ B) := by
  have hs := (summable_pow_mul_geometric_of_norm_lt_one d
    (by norm_num : ‖(3 / 8 : ℝ)‖ < 1)).mul_left ((3 : ℝ) ^ d)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_macroBoundary_le hL δ, eventually_ge_atTop (1 : ℕ)]
    with B hq hB
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
    (macroBoundary_pos L δ B).le)]
  have hb : (1 : ℝ) ≤ B := Nat.one_le_cast.mpr hB
  have hp : ((B : ℝ) + 2) ^ d ≤ (3 * (B : ℝ)) ^ d :=
    pow_le_pow_left₀ (by positivity) (by linarith) d
  calc
    _ ≤ (3 * (B : ℝ)) ^ d * (3 / 8 : ℝ) ^ B :=
      mul_le_mul hp hq (macroBoundary_pos L δ B).le (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- In particular the exact single-point boundary tends to zero. -/
theorem macroBoundary_tendsto {L : ℝ} (hL : 0 ≤ L) (δ : ℝ) :
    Tendsto (macroBoundary L δ) atTop (𝓝 0) := by
  have hs : Summable (macroBoundary L δ) := by
    simpa only [pow_zero, one_mul] using summable_pow_macroBoundary hL δ 0
  exact hs.tendsto_atTop_zero

/-- Eventually the boundary is at most one, with no change to its exact definition. -/
theorem eventually_macroBoundary_le_one {L : ℝ} (hL : 0 ≤ L) (δ : ℝ) :
    ∀ᶠ B in atTop, macroBoundary L δ B ≤ 1 := by
  filter_upwards [eventually_macroBoundary_le hL δ] with B hB
  exact hB.trans (pow_le_one₀ (by norm_num) (by norm_num))

/-- Any level at least the literal old level has the same shifted order-six bound. -/
theorem macroLevel_mixing_le {B k : ℕ} (hB : 1 ≤ B) (hk : macroLevel B ≤ k) :
    Analytic.mixingError k ≤
      (Analytic.mixingCoefficient : ℝ) * 3000 ^ 6 * ((B : ℝ) + 2) ^ (-6 : ℝ) := by
  have hb : (1 : ℝ) ≤ B := Nat.one_le_cast.mpr hB
  have hl := (macroLevel_bounds B).1
  have hcast : (macroLevel B : ℝ) ≤ k := Nat.cast_le.mpr hk
  have he : ((B : ℝ) + 2) / 3000 ≤ k := by linarith
  have hm := Analytic.mixingError_le_order6 ((macroLevel_pos hB).trans hk)
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity :
    (0 : ℝ) < ((B : ℝ) + 2) / 3000) he (by norm_num : (-6 : ℝ) ≤ 0)
  apply hm.trans
  have hmul := mul_le_mul_of_nonneg_left hp Analytic.mixingCoefficient_pos.le
  convert hmul using 1
  rw [Real.div_rpow (by positivity) (by norm_num)]
  norm_num [Real.rpow_neg, Real.rpow_natCast, div_eq_mul_inv]
  ring

/-- The literal three-term error is nonnegative at every positive count. -/
theorem macroError_nonneg (L δ : ℝ) {B : ℕ} (hB : 1 ≤ B) :
    0 ≤ macroError L δ B := by
  have hg := macroConductor_guards L δ hB
  have hnew := (Analytic.mixingError_pos (hg.1.trans hg.2.1)).le
  have hold := (Analytic.mixingError_pos hg.1).le
  have hm := (macroblockMass_bounds L δ B).2
  unfold macroError
  linarith

/-- Both level costs and the original rejection deficit have a common order-six majorant. -/
theorem macroError_le {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) {B : ℕ} (hB : 1 ≤ B) :
    macroError L δ B ≤
      (2 * (Analytic.mixingCoefficient : ℝ) * 3000 ^ 6 + L + 5) *
        ((B : ℝ) + 2) ^ (-6 : ℝ) := by
  have hold := macroLevel_mixing_le hB (le_refl (macroLevel B))
  have hnew := macroLevel_mixing_le hB
    (macroLevel_mono (Nat.le_add_right B (macroLength L B)))
  have hdef := (macroblockMass_deficit_bounds hL hδ hpay B).2
  have hp := Real.rpow_le_rpow_of_exponent_le
    (by have := Nat.cast_nonneg (α := ℝ) B; linarith : (1 : ℝ) ≤ (B : ℝ) + 2)
    (by norm_num : (-9 : ℝ) ≤ -6)
  have hdef' := hdef.trans (mul_le_mul_of_nonneg_left hp (by linarith : 0 ≤ L + 5))
  unfold macroError
  nlinarith

/-- A cubic count weight still leaves a summable error, even over all integer counts. -/
theorem summable_cube_macroError {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) :
    Summable (fun B : ℕ => ((B : ℝ) + 2) ^ 3 * macroError L δ B) := by
  have hs0 := (summable_nat_add_iff 2).mpr
    (Real.summable_nat_rpow.mpr (by norm_num : (-3 : ℝ) < -1))
  have hs : Summable (fun B : ℕ => ((B : ℝ) + 2) ^ (-3 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hs0
  apply (hs.mul_left
    (2 * (Analytic.mixingCoefficient : ℝ) * 3000 ^ 6 + L + 5)).of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with B hB
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity)
    (macroError_nonneg L δ hB))]
  have he : ((B : ℝ) + 2) ^ 3 * ((B : ℝ) + 2) ^ (-6 : ℝ) =
      ((B : ℝ) + 2) ^ (-3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by positivity)]
    norm_num
  calc
    _ ≤ ((B : ℝ) + 2) ^ 3 *
        ((2 * (Analytic.mixingCoefficient : ℝ) * 3000 ^ 6 + L + 5) *
          ((B : ℝ) + 2) ^ (-6 : ℝ)) :=
      mul_le_mul_of_nonneg_left (macroError_le hL hδ hpay hB) (by positivity)
    _ = _ := by rw [← mul_assoc, mul_comm (_ ^ 3), mul_assoc, he]

end WordCertDensity.Construction
