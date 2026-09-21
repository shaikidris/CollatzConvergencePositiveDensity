/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.SeedCoefficient
import WordCertDensity.Construction.SeedRate

/-! # One geometric majorant for actual seed increments -/

namespace WordCertDensity.Construction

/-- A marker depth at least one eighth of the block pays at most the factor 8^92. -/
theorem seedMarker_inverse92 {B m : ℝ} (hB : 0 < B) (hm : B / 8 ≤ m) :
    m ^ (-92 : ℝ) ≤ (8 : ℝ) ^ 92 * B ^ (-92 : ℝ) := by
  have hmpos : 0 < m := (div_pos hB (by norm_num)).trans_le hm
  have hp := pow_le_pow_left₀ hB.le (show B ≤ 8 * m by linarith) 92
  rw [mul_pow] at hp
  rw [seed_rpow_neg92, seed_rpow_neg92]
  have h := (div_le_div_iff₀ (pow_pos hmpos 92) (pow_pos hB 92)).mpr
    (show (1 : ℝ) * B ^ 92 ≤ 8 ^ 92 * m ^ 92 by simpa only [one_mul] using hp)
  simpa only [one_div, div_eq_mul_inv, one_mul] using h

/-- Both marker costs and the seed depth are bounded using the same actual block depth. -/
theorem seedIncrement_inverse92_sum {B : ℕ} (hB : 8 ≤ B) :
    (seedNextMarker B : ℝ) ^ (-92 : ℝ) + (B / 4 : ℕ) ^ (-92 : ℝ) +
      (B : ℝ) ^ (-92 : ℝ) ≤ (2 * (8 : ℝ) ^ 92 + 1) * (B : ℝ) ^ (-92 : ℝ) := by
  have hbpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hl := seedMarker_inverse92 hbpos (seedIncrement_old_lower hB)
  have hk0 : (B / 4 : ℕ) ≤ (seedNextMarker B : ℝ) := by
    exact_mod_cast (seedIncrement_marker_guards hB).2.1
  have hk := seedMarker_inverse92 hbpos ((seedIncrement_old_lower hB).trans hk0)
  calc
    _ ≤ (8 : ℝ) ^ 92 * (B : ℝ) ^ (-92 : ℝ) +
        8 ^ 92 * (B : ℝ) ^ (-92 : ℝ) + (B : ℝ) ^ (-92 : ℝ) :=
      add_le_add (add_le_add hk hl) (le_refl _)
    _ = _ := by ring

/-- A root-independent coefficient retaining the initial inverse-depth gain. -/
noncomputable def seedGeometricCoefficient (b : ℕ) : ℝ :=
  (2 / 3 : ℝ) * seedCapacityConstant b * Analytic.mixingCoefficient *
    (2 * (8 : ℝ) ^ 92 + 1) * (b : ℝ) ^ (-92 : ℝ)

/-- Every actual physical increment has one geometric rate, with the original capacity included. -/
theorem physicalSeedMark_increment_geometric {b root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) (n : ℕ) :
    |physicalSeedMark b (n + 1) root - physicalSeedMark b n root| ≤
      seedGeometricCoefficient b * ((n : ℝ) + 1) ^ 3 * seedVariationRate ^ n := by
  have hB := hb.trans (seedSize_ge b n)
  have hc : 0 ≤ seedCapacity b n := (seedTagBudget_nonneg b n).trans (seedTagBudget_le_capacity b n)
  have hA : 0 ≤ (2 / 3 : ℝ) * seedCapacity b n * Analytic.mixingCoefficient :=
    mul_nonneg (mul_nonneg (by norm_num) hc) Analytic.mixingCoefficient_pos.le
  apply (physicalSeedMark_increment_absorbed hb hr n).trans
  calc
    _ ≤ (2 / 3 : ℝ) * seedCapacity b n * Analytic.mixingCoefficient *
        ((2 * (8 : ℝ) ^ 92 + 1) * (seedSize b n : ℝ) ^ (-92 : ℝ)) :=
      mul_le_mul_of_nonneg_left (seedIncrement_inverse92_sum (by omega)) hA
    _ ≤ (2 / 3 : ℝ) * seedCapacity b n * Analytic.mixingCoefficient *
        ((2 * (8 : ℝ) ^ 92 + 1) *
          ((b : ℝ) ^ (-92 : ℝ) * ((seedScheduleRate ^ 92)⁻¹) ^ n)) := by
      apply mul_le_mul_of_nonneg_left _ hA
      exact mul_le_mul_of_nonneg_left (seedSize_inverse92 (by omega) n) (by positivity)
    _ = _ := by
      unfold seedGeometricCoefficient seedCapacity seedVariationRate
      rw [mul_pow]
      ring

/-- The retained uniform variation coefficient F_b. -/
noncomputable def seedVariationCoefficient (b : ℕ) : ℝ :=
  (2 : ℝ) ^ 467 * b * 16 ^ b * (Analytic.mixingCoefficient + 1)

/-- The initial capacity, including its boundary term, fits the printed 220 b 16^b allowance. -/
theorem seedCapacityConstant_variation_le {b : ℕ} (hb : 1 ≤ b) :
    (2 / 3 : ℝ) * seedCapacityConstant b ≤ 220 * b * (16 : ℝ) ^ b := by
  have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have htwo : (2 : ℝ) ^ (b + 1) ≤ 16 ^ b := by
    calc
      _ ≤ (2 : ℝ) ^ (4 * b) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = _ := by rw [pow_mul]; norm_num
  have ht : (20 : ℝ) * (4 * b + 1) ≤ 100 * b := by linarith
  have hs : (2 : ℝ) ^ (b + 1) + 16 ^ b ≤ 2 * 16 ^ b := by linarith
  have hm := mul_le_mul ht hs (by positivity : (0 : ℝ) ≤ 2 ^ (b + 1) + 16 ^ b)
    (by positivity : (0 : ℝ) ≤ 100 * b)
  calc
    _ ≤ (2 / 3 : ℝ) * (100 * b * (2 * 16 ^ b)) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = (400 / 3 : ℝ) * (b * 16 ^ b) := by ring
    _ ≤ 220 * (b * (16 : ℝ) ^ b) :=
      mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    _ = _ := by ring

/-- The numerical depth-loss allowance lies below the retained binary coefficient. -/
theorem seedVariation_scalar_guard : 220 * (2 * (8 : ℝ) ^ 92 + 1) ≤ 2 ^ 467 := by
  calc
    _ ≤ (2 : ℝ) ^ 200 * 2 ^ 86 := by norm_num
    _ = (2 : ℝ) ^ 286 := by rw [← pow_add]
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by decide : (286 : ℕ) ≤ 467)

/-- The sharper geometric coefficient is bounded by the manuscript's uniform coefficient. -/
theorem seedGeometricCoefficient_le_variation {b : ℕ} (hb : 1 ≤ b) :
    seedGeometricCoefficient b ≤ seedVariationCoefficient b := by
  have hC := Analytic.mixingCoefficient_pos.le
  have hbp : (b : ℝ) ^ (-92 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hb) (by norm_num)
  have hcap := seedCapacityConstant_variation_le hb
  have hfirst := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcap hC) (show (0 : ℝ) ≤ 2 * 8 ^ 92 + 1 by positivity)
  have hwhole := mul_le_mul hfirst hbp (by positivity : (0 : ℝ) ≤ (b : ℝ) ^ (-92 : ℝ))
    (show 0 ≤ (220 * (b : ℝ) * 16 ^ b * Analytic.mixingCoefficient) * (2 * (8 : ℝ) ^ 92 + 1) by positivity)
  calc
    seedGeometricCoefficient b ≤
        (220 * (b : ℝ) * 16 ^ b * Analytic.mixingCoefficient) * (2 * (8 : ℝ) ^ 92 + 1) * 1 := hwhole
    _ = (220 * (2 * (8 : ℝ) ^ 92 + 1)) * (b * 16 ^ b) * Analytic.mixingCoefficient := by ring
    _ ≤ (2 : ℝ) ^ 467 * (b * 16 ^ b) * Analytic.mixingCoefficient :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right seedVariation_scalar_guard (by positivity)) hC
    _ ≤ (2 : ℝ) ^ 467 * (b * 16 ^ b) * (Analytic.mixingCoefficient + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = seedVariationCoefficient b := by simp only [seedVariationCoefficient, mul_assoc]

/-- The stated root-uniform variation theorem holds at every generation. -/
theorem physicalSeedMark_variation {b root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) (n : ℕ) :
    |physicalSeedMark b (n + 1) root - physicalSeedMark b n root| ≤
      seedVariationCoefficient b * ((n : ℝ) + 1) ^ 3 * seedVariationRate ^ n := by
  apply (physicalSeedMark_increment_geometric hb hr n).trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (seedGeometricCoefficient_le_variation (by omega)) (by positivity))
    (pow_nonneg seedVariationRate_contracts.1.le n)

end WordCertDensity.Construction
