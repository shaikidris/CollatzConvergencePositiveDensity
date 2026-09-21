/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Counting.DyadicBasin
public import WordCertDensity.Counting.OddBand
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Literal tower counts and their cost in a band of radius sixteen -/

@[expose] public section

namespace WordCertDensity.Counting

noncomputable section

/-- The manuscript's tower count, used only above the positive base. -/
def towerCount (Y : ℝ) (x : ℕ) : ℕ := 1 + ⌊Real.logb 2 (Y / x)⌋₊

/-- The floor formula counts the actual dyadic multiples, including the upper endpoint. -/
theorem towerCount_eq_prefixCount {Y : ℝ} {x : ℕ} (hx : 0 < x) (hY : (x : ℝ) ≤ Y) :
    towerCount Y x = prefixCount (Set.range (fun n : ℕ => 2 ^ n * x)) ⌊Y⌋₊ := by
  rw [prefixCount_dyadicRange_real hx hY]
  simp only [towerCount, Nat.add_comm]

/-- A specified dyadic multiple below the cutoff supplies all earlier copies. -/
theorem towerCount_lower {Y : ℝ} {x n : ℕ} (hx : 0 < (x : ℝ))
    (h : (2 : ℝ) ^ n * x ≤ Y) : n + 1 ≤ towerCount Y x := by
  have hp : 0 < Y / x := div_pos ((mul_pos (by positivity) hx).trans_le h) hx
  have hl : (n : ℝ) ≤ Real.logb 2 (Y / x) := by
    rw [Real.le_logb_iff_rpow_le (by norm_num) hp, Real.rpow_natCast, le_div_iff₀ hx]
    exact h
  have hf : n ≤ ⌊Real.logb 2 (Y / x)⌋₊ :=
    (Nat.le_floor_iff ((Nat.cast_nonneg n).trans hl)).mpr hl
  simpa only [towerCount, Nat.add_comm] using Nat.add_le_add_right hf 1

/-- A missing dyadic multiple gives the matching upper bound. -/
theorem towerCount_upper {Y : ℝ} {x n : ℕ} (hx : 0 < (x : ℝ))
    (hY : 0 < Y) (hn : 0 < n) (h : Y < (2 : ℝ) ^ n * x) :
    towerCount Y x ≤ n := by
  have hl : Real.logb 2 (Y / x) < (n : ℝ) := by
    rw [Real.logb_lt_iff_lt_rpow (by norm_num) (div_pos hY hx),
      Real.rpow_natCast, div_lt_iff₀ hx]
    exact h
  have hf := (Nat.floor_lt' (Nat.ne_of_gt hn)).mpr hl
  dsimp [towerCount]
  omega

/-- A relative dyadic subband gives an exact integer lower bound without discarding boundaries. -/
theorem towerCount_subband_lower {X : ℝ} {x j h : ℕ}
    (hx : 0 < (x : ℝ)) (hh : h ≤ 4 * j) (hu : (x : ℝ) ≤ 2 ^ h * X) :
    4 * j - h + 1 ≤ towerCount ((16 : ℝ) ^ j * X) x := by
  apply towerCount_lower hx
  calc
    (2 : ℝ) ^ (4 * j - h) * x ≤ 2 ^ (4 * j - h) * (2 ^ h * X) :=
      mul_le_mul_of_nonneg_left hu (by positivity)
    _ = (16 : ℝ) ^ j * X := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hh, pow_mul]
      norm_num

/-- In the first open subband each point has exactly four times the band index copies. -/
theorem towerCount_first_subband {X : ℝ} {x j : ℕ} (hX : 0 < X) (hj : 1 ≤ j)
    (hl : X < (x : ℝ)) (hu : (x : ℝ) < 2 * X) :
    towerCount ((16 : ℝ) ^ j * X) x = 4 * j := by
  have hlo := towerCount_subband_lower (hX.trans hl)
    (show 1 ≤ 4 * j by omega) (by simpa using hu.le)
  have hhi : towerCount ((16 : ℝ) ^ j * X) x ≤ 4 * j := by
    apply towerCount_upper (hX.trans hl) (by positivity) (by omega)
    rw [pow_mul]
    norm_num
    exact hl
  omega

/-- Past the first subband, cost per harmonic mass is at least six times its index and base. -/
theorem towerCost_later_subbands {X : ℝ} {x j : ℕ} (hX : 0 < X) (hj : 1 ≤ j)
    (hl : 2 * X ≤ (x : ℝ)) (hu : (x : ℝ) < 16 * X) :
    6 * (j : ℝ) * X ≤ (x : ℝ) * towerCount ((16 : ℝ) ^ j * X) x := by
  have hx : 0 < (x : ℝ) := by linarith
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  by_cases h4 : (x : ℝ) ≤ 4 * X
  · have h := towerCount_subband_lower hx (show 2 ≤ 4 * j by omega)
      (by norm_num; exact h4)
    have he : 4 * j - 2 + 1 + 1 = 4 * j := by omega
    have hr : 4 * (j : ℝ) - 1 ≤ towerCount ((16 : ℝ) ^ j * X) x := by
      have := (show ((4 * j - 2 + 1 : ℕ) : ℝ) ≤ towerCount ((16 : ℝ) ^ j * X) x by exact_mod_cast h)
      have he' : ((4 * j - 2 + 1 : ℕ) : ℝ) + 1 = 4 * (j : ℝ) := by exact_mod_cast he
      linarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ (j : ℝ) - 1) hX.le,
      mul_le_mul_of_nonneg_left hr hx.le]
  · by_cases h8 : (x : ℝ) ≤ 8 * X
    · have h := towerCount_subband_lower hx (show 3 ≤ 4 * j by omega)
        (by norm_num; exact h8)
      have hnat : 2 * j ≤ towerCount ((16 : ℝ) ^ j * X) x := by omega
      have hr : 2 * (j : ℝ) ≤ towerCount ((16 : ℝ) ^ j * X) x := by exact_mod_cast hnat
      nlinarith [mul_le_mul_of_nonneg_left hr hx.le]
    · have h := towerCount_subband_lower hx (show 4 ≤ 4 * j by omega)
        (by norm_num; exact hu.le)
      have hnat : j ≤ towerCount ((16 : ℝ) ^ j * X) x := by omega
      have hr : (j : ℝ) ≤ towerCount ((16 : ℝ) ^ j * X) x := by exact_mod_cast hnat
      nlinarith [mul_le_mul_of_nonneg_left hr hx.le]

end

end WordCertDensity.Counting
