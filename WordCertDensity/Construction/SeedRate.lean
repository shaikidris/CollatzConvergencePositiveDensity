/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.SeedTags

/-! # The retained geometric rate for uniform seed variation -/

@[expose] public section

namespace WordCertDensity.Construction

/-- The sharper schedule base pays the floor loss at every permitted stage. -/
noncomputable def seedScheduleRate : ℝ := 100999 / 100000

/-- The variation rate includes the growth of the incoming tag budget. -/
noncomputable def seedVariationRate : ℝ := seedTagGrowth * (seedScheduleRate ^ 92)⁻¹

/-- The literal floored next depth dominates the retained real schedule base. -/
theorem seedSize_step_sharp {B : ℕ} (hB : 100000 ≤ B) :
    seedScheduleRate * B ≤ (B + B / 100 : ℕ) := by
  have hf : B ≤ 100 * (B / 100) + 99 := by omega
  have hf' : (B : ℝ) ≤ 100 * (B / 100 : ℕ) + 99 := by exact_mod_cast hf
  have hb' : (100000 : ℝ) ≤ B := by exact_mod_cast hB
  unfold seedScheduleRate
  push_cast
  linarith

/-- The sharp lower schedule bound holds at every stage, including stage zero. -/
theorem seedSize_geometric_sharp {b : ℕ} (hb : 100000 ≤ b) (n : ℕ) :
    (b : ℝ) * seedScheduleRate ^ n ≤ seedSize b n := by
  induction n with
  | zero => simp [seedSize]
  | succ n ih =>
    have h := seedSize_step_sharp (hb.trans (seedSize_ge b n))
    calc
      _ = seedScheduleRate * ((b : ℝ) * seedScheduleRate ^ n) := by rw [pow_succ]; ring
      _ ≤ seedScheduleRate * seedSize b n :=
        mul_le_mul_of_nonneg_left ih (by norm_num [seedScheduleRate])
      _ ≤ _ := h

/-- Negative order 92 is an inverse natural power; no approximation is involved. -/
theorem seed_rpow_neg92 (x : ℝ) : x ^ (-92 : ℝ) = (x ^ (92 : ℕ))⁻¹ := by
  rw [show (-92 : ℝ) = -(92 : ℕ) by norm_num, Real.rpow_neg_natCast, zpow_neg, zpow_natCast]

/-- The sharp schedule turns inverse powers into geometric decay with the initial depth retained. -/
theorem seedSize_inverse92 {b : ℕ} (hb : 100000 ≤ b) (n : ℕ) :
    (seedSize b n : ℝ) ^ (-92 : ℝ) ≤
      (b : ℝ) ^ (-92 : ℝ) * ((seedScheduleRate ^ 92)⁻¹) ^ n := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have ha : 0 < seedScheduleRate := by norm_num [seedScheduleRate]
  have hp := pow_le_pow_left₀ (show (0 : ℝ) ≤ b * seedScheduleRate ^ n by positivity)
    (seedSize_geometric_sharp hb n) 92
  have hprod : (0 : ℝ) < ((b : ℝ) * seedScheduleRate ^ n) ^ 92 := by positivity
  have hseed : (0 : ℝ) < (seedSize b n : ℝ) ^ 92 := by
      have h := hb.trans (seedSize_ge b n)
      have hx : (0 : ℝ) < seedSize b n := by exact_mod_cast (show 0 < seedSize b n by omega)
      positivity
  have hi := inv_le_inv₀ hseed hprod
  rw [seed_rpow_neg92, seed_rpow_neg92]
  calc
    _ ≤ (((b : ℝ) * seedScheduleRate ^ n) ^ 92)⁻¹ := hi.mpr hp
    _ = _ := by
      simp only [mul_pow, mul_inv_rev, inv_pow, ← pow_mul]
      rw [Nat.mul_comm n 92]
      ring

/-- The exact rational variation rate lies in the manuscript's retained narrow interval. -/
theorem seedVariationRate_bounds :
    (2 / 5 : ℝ) < seedVariationRate ∧ seedVariationRate < 41 / 100 := by
  norm_num [seedVariationRate, seedTagGrowth, seedScheduleRate]

/-- The tag-adjusted inverse power has a strictly contracting geometric base. -/
theorem seedVariationRate_contracts : 0 < seedVariationRate ∧ seedVariationRate < 1 / 2 := by
  have h := seedVariationRate_bounds
  constructor <;> linarith

end WordCertDensity.Construction
