/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.SeedFailure
public import WordCertDensity.Construction.SeedRate

/-! # Persistent seed survival

The first layer records the exact deficit constants and proves that every
stage's original seed failure is bounded by the manuscript's geometric
exponential deficit.
-/

@[expose] public section

namespace WordCertDensity.Construction

/-- The fixed initial depth used by the canonical survival construction. -/
def survivalSeedSize : ℕ := 32 ^ 5

/-- The retained infinite-survival fraction. -/
noncomputable def survivalFraction : ℝ := 24 / 25

/-- The geometric rate in the summable survival-deficit envelope. -/
noncomputable def survivalDeficitRate : ℝ := 504 / 503

/-- The exponential coefficient in the survival-deficit envelope. -/
noncomputable def survivalDeficitExponent : ℝ := 511 / 64

/-- The stagewise majorant for the rejected reference mass. -/
noncomputable def survivalDeficit (j : ℕ) : ℝ :=
  2 * Real.exp (-survivalDeficitExponent * survivalDeficitRate ^ j)

/-- The survival-deficit rate is strictly larger than one. -/
theorem one_lt_survivalDeficitRate : 1 < survivalDeficitRate := by
  norm_num [survivalDeficitRate]

/-- The survival-deficit rate is positive. -/
theorem survivalDeficitRate_pos : 0 < survivalDeficitRate :=
  zero_lt_one.trans one_lt_survivalDeficitRate

/-- Five powers of the deficit rate fit inside the floor-aware seed growth rate. -/
theorem survivalDeficitRate_fifth_lt :
    survivalDeficitRate ^ 5 < seedScheduleRate := by
  norm_num [survivalDeficitRate, seedScheduleRate]

/-- The fixed-time exponent coefficient strictly exceeds the retained deficit exponent. -/
theorem survivalDeficitExponent_lt :
    survivalDeficitExponent < 32 / (4 + 3 / 512 : ℝ) := by
  norm_num [survivalDeficitExponent]

/-- The fifth root of every scheduled depth dominates the chosen geometric rate. -/
theorem survivalRate_le_seedSize_fifthRoot (j : ℕ) :
    32 * survivalDeficitRate ^ j ≤
      (seedSize survivalSeedSize j : ℝ) ^ (1 / 5 : ℝ) := by
  have hrate : survivalDeficitRate ^ 5 ≤ seedScheduleRate :=
    survivalDeficitRate_fifth_lt.le
  have hp : (survivalDeficitRate ^ 5) ^ j ≤ seedScheduleRate ^ j :=
    pow_le_pow_left₀ (pow_nonneg survivalDeficitRate_pos.le 5) hrate j
  have hs := seedSize_geometric_sharp (b := survivalSeedSize) (by norm_num [survivalSeedSize]) j
  have hpow : (32 * survivalDeficitRate ^ j : ℝ) ^ 5 ≤
      (seedSize survivalSeedSize j : ℝ) := by
    calc
      (32 * survivalDeficitRate ^ j : ℝ) ^ 5 =
          32 ^ 5 * (survivalDeficitRate ^ 5) ^ j := by
            rw [mul_pow, ← pow_mul, ← pow_mul, Nat.mul_comm]
      _ ≤ 32 ^ 5 * seedScheduleRate ^ j :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (survivalSeedSize : ℕ) * seedScheduleRate ^ j := by
        norm_num [survivalSeedSize]
      _ ≤ (seedSize survivalSeedSize j : ℝ) := by
        simpa using hs
  have hratej : 0 ≤ survivalDeficitRate ^ j := pow_nonneg survivalDeficitRate_pos.le j
  have hr := Real.rpow_le_rpow (pow_nonneg (mul_nonneg (by norm_num) hratej) 5) hpow
    (by norm_num : (0 : ℝ) ≤ 1 / 5)
  rw [← Real.rpow_natCast_mul (mul_nonneg (by norm_num) hratej)] at hr
  norm_num at hr
  simpa using hr

/-- The original failure at every seed stage is bounded by the retained deficit. -/
theorem seedWords_failure_le_survivalDeficit (j : ℕ) :
    1 - Reference.stoppingMass (seedWords (seedSize survivalSeedSize j)) ≤
      survivalDeficit j := by
  have hfailure := seedWords_failure_power_le
    (b := seedSize survivalSeedSize j)
    ((show 32 ^ 5 ≤ survivalSeedSize by simp [survivalSeedSize]).trans
      (seedSize_ge survivalSeedSize j))
  have hroot := survivalRate_le_seedSize_fifthRoot j
  have hexponent : survivalDeficitExponent * survivalDeficitRate ^ j ≤
      (seedSize survivalSeedSize j : ℝ) ^ (1 / 5 : ℝ) / (4 + 3 / 512) := by
    calc
      survivalDeficitExponent * survivalDeficitRate ^ j ≤
          (32 / (4 + 3 / 512 : ℝ)) * survivalDeficitRate ^ j :=
        mul_le_mul_of_nonneg_right survivalDeficitExponent_lt.le
          (pow_nonneg survivalDeficitRate_pos.le j)
      _ = (32 * survivalDeficitRate ^ j) / (4 + 3 / 512 : ℝ) := by ring
      _ ≤ (seedSize survivalSeedSize j : ℝ) ^ (1 / 5 : ℝ) /
          (4 + 3 / 512 : ℝ) := by
        exact div_le_div_of_nonneg_right hroot (by norm_num)
  unfold survivalDeficit
  apply hfailure.trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [neg_mul]
  exact Real.exp_le_exp.mpr (neg_le_neg hexponent)

end WordCertDensity.Construction
