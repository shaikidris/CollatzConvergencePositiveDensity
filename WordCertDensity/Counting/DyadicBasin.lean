/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Roots.DyadicBasin
public import WordCertDensity.Density.Basic
public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.Ring

/-!
# Exact dyadic basin counts and zero density

The actual positive-prefix count is logarithmic, with an exact formula at
natural and real cutoffs. The full partial-density profile tends to zero;
therefore every logarithmic-clock subset has lower natural density zero.
-/

@[expose] public section

namespace WordCertDensity

open Filter
open scoped Topology

/-- A cutoff for dyadic exponents gives the exact positive-prefix count. -/
theorem prefixCount_dyadicRange_of_cutoff {y N k : ℕ} (hy : 0 < y)
    (hk : ∀ n, n < k ↔ 2 ^ n * y ≤ N) :
    prefixCount (Set.range (fun n : ℕ => 2 ^ n * y)) N = k := by
  classical
  have hinj : Function.Injective (fun n : ℕ => 2 ^ n * y) :=
    (show StrictMono (fun n : ℕ => 2 ^ n * y) from fun _ _ h =>
      Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by decide) h) hy).injective
  have hset : (Finset.Icc 1 N).filter (fun x => x ∈ Set.range (fun n : ℕ => 2 ^ n * y)) =
      (Finset.range k).image (fun n => 2 ^ n * y) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_range,
      Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨⟨_, hN⟩, n, rfl⟩
      exact ⟨n, (hk n).mpr hN, rfl⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨Nat.succ_le_of_lt (Nat.mul_pos (pow_pos (by decide) n) hy), (hk n).mp hn⟩,
        n, rfl⟩
  rw [prefixCount, hset, Finset.card_image_of_injective _ hinj, Finset.card_range]

/-- The exact dyadic count includes the empty-prefix case below the target. -/
theorem prefixCount_dyadicRange {y : ℕ} (hy : 0 < y) (N : ℕ) :
    prefixCount (Set.range (fun n : ℕ => 2 ^ n * y)) N =
      if N < y then 0 else Nat.log 2 (N / y) + 1 := by
  split_ifs with hN
  · apply prefixCount_dyadicRange_of_cutoff hy
    intro n
    have hp : 1 ≤ 2 ^ n := Nat.succ_le_of_lt (pow_pos (by decide) n)
    constructor
    · omega
    · intro h
      nlinarith
  · apply prefixCount_dyadicRange_of_cutoff hy
    intro n
    rw [Nat.lt_succ_iff, Nat.le_log_iff_pow_le (by decide)
      (Nat.ne_of_gt (Nat.div_pos (Nat.le_of_not_gt hN) hy)), Nat.le_div_iff_mul_le hy]

/-- A finite prefix at the natural floor is exactly the positive real-cutoff prefix. -/
theorem mem_prefix_floor_iff (S : Set ℕ) {X : ℝ} (hX : 0 ≤ X) (x : ℕ) :
    (x ∈ Finset.Icc 1 ⌊X⌋₊ ∧ x ∈ S) ↔
      0 < x ∧ (x : ℝ) ≤ X ∧ x ∈ S := by
  classical
  simp [Finset.mem_Icc, Nat.le_floor_iff hX, Nat.succ_le_iff, and_assoc]

/-- The exact dyadic count at a real cutoff is one plus its binary-logarithm floor. -/
theorem prefixCount_dyadicRange_real {y : ℕ} (hy : 0 < y) {X : ℝ} (hX : (y : ℝ) ≤ X) :
    prefixCount (Set.range (fun n : ℕ => 2 ^ n * y)) ⌊X⌋₊ =
      ⌊Real.logb 2 (X / y)⌋₊ + 1 := by
  have hyr : (0 : ℝ) < y := by exact_mod_cast hy
  have hXpos : 0 < X := hyr.trans_le hX
  have hratio : 0 < X / y := div_pos hXpos hyr
  have hlog : 0 ≤ Real.logb 2 (X / y) :=
    Real.logb_nonneg (by norm_num) ((one_le_div hyr).mpr hX)
  apply prefixCount_dyadicRange_of_cutoff hy
  intro n
  rw [Nat.lt_succ_iff, Nat.le_floor_iff hlog,
    Real.le_logb_iff_rpow_le (by norm_num) hratio, Real.rpow_natCast,
    le_div_iff₀ hyr, Nat.le_floor_iff hXpos.le]
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

/-- The exact natural-cutoff formula for the full basin of a positive multiple of three. -/
theorem prefixCount_ordinaryBasin_of_three_dvd {y : ℕ} (hy : 3 ∣ y) (hpos : 0 < y) (N : ℕ) :
    prefixCount (ordinaryBasin y) N = if N < y then 0 else Nat.log 2 (N / y) + 1 := by
  rw [ordinaryBasin_eq_dyadic_range hy hpos]
  exact prefixCount_dyadicRange hpos N

/-- The manuscript's exact count at every real cutoff at least the target. -/
theorem prefixCount_ordinaryBasin_real_of_three_dvd {y : ℕ}
    (hy : 3 ∣ y) (hpos : 0 < y) {X : ℝ} (hX : (y : ℝ) ≤ X) :
    prefixCount (ordinaryBasin y) ⌊X⌋₊ = ⌊Real.logb 2 (X / y)⌋₊ + 1 := by
  rw [ordinaryBasin_eq_dyadic_range hy hpos]
  exact prefixCount_dyadicRange_real hpos hX

/-- Every dyadic ray has a logarithmic upper count, uniformly over its positive base. -/
theorem prefixCount_dyadicRange_le {y : ℕ} (hy : 0 < y) (N : ℕ) :
    prefixCount (Set.range (fun n : ℕ => 2 ^ n * y)) N ≤ Nat.log 2 N + 1 := by
  rw [prefixCount_dyadicRange hy N]
  split_ifs
  · omega
  · exact Nat.add_le_add_right (Nat.log_mono_right (Nat.div_le_self N y)) 1

/-- The actual natural-density profile of every positive dyadic ray converges to zero. -/
theorem partialDensity_dyadicRange_tendsto_zero {y : ℕ} (hy : 0 < y) :
    Tendsto (partialDensity (Set.range (fun n : ℕ => 2 ^ n * y))) atTop (𝓝 0) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  have hupper : Tendsto (fun N : ℕ => (Real.log N / N) / Real.log 2 + (N : ℝ)⁻¹)
      atTop (𝓝 0) := by
    simpa using ((hlog.comp hcast).div_const (Real.log 2)).add
      (tendsto_inv_atTop_zero.comp hcast)
  apply squeeze_zero (partialDensity_nonneg _) _ hupper
  intro N
  have hcount : (prefixCount (Set.range (fun n : ℕ => 2 ^ n * y)) N : ℝ) ≤
      Real.logb 2 N + 1 := by
    calc
      _ ≤ (Nat.log 2 N : ℝ) + 1 := by exact_mod_cast prefixCount_dyadicRange_le hy N
      _ ≤ _ := by simpa [add_comm] using add_le_add_right (Real.natLog_le_logb N 2) 1
  calc
    partialDensity (Set.range (fun n : ℕ => 2 ^ n * y)) N ≤ (Real.logb 2 N + 1) / N :=
      div_le_div_of_nonneg_right hcount (Nat.cast_nonneg N)
    _ = (Real.log N / N) / Real.log 2 + (N : ℝ)⁻¹ := by
      simp only [Real.logb, div_eq_mul_inv]
      ring

/-- The full basin of a positive multiple of three has natural density zero. -/
theorem partialDensity_ordinaryBasin_tendsto_zero {y : ℕ} (hy : 3 ∣ y) (hpos : 0 < y) :
    Tendsto (partialDensity (ordinaryBasin y)) atTop (𝓝 0) := by
  rw [ordinaryBasin_eq_dyadic_range hy hpos]
  exact partialDensity_dyadicRange_tendsto_zero hpos

/-- In particular the manuscript's lower natural density of that full basin is zero. -/
theorem lowerNaturalDensity_ordinaryBasin_eq_zero {y : ℕ} (hy : 3 ∣ y) (hpos : 0 < y) :
    lowerNaturalDensity (ordinaryBasin y) = 0 :=
  (partialDensity_ordinaryBasin_tendsto_zero hy hpos).liminf_eq

/-- Every real logarithmic clock has zero lower density at a positive target divisible by three. -/
theorem lowerNaturalDensity_goodTarget_eq_zero_of_three_dvd {y : ℕ}
    (hy : 3 ∣ y) (hpos : 0 < y) (c : ℝ) : lowerNaturalDensity (goodTarget y c) = 0 := by
  apply le_antisymm _ (lowerNaturalDensity_nonneg _)
  calc
    _ ≤ lowerNaturalDensity (ordinaryBasin y) :=
      lowerNaturalDensity_mono (goodTarget_subset_ordinaryBasin y c)
    _ = 0 := lowerNaturalDensity_ordinaryBasin_eq_zero hy hpos

end WordCertDensity
