/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Counting.DyadicCost
public import WordCertDensity.Counting.Occupation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Harmonic occupation forces a dyadic counting cost -/

@[expose] public section

namespace WordCertDensity.Counting

open Filter
open scoped BigOperators Topology

/-- The low odd band is contained in the ambient band of radius sixteen. -/
theorem oddOpenBand_subset {X s t : ℝ} (hX : 0 ≤ X) (hst : s ≤ t) :
    oddOpenBand X s ⊆ oddOpenBand X t := by
  intro x hx
  obtain ⟨ho, hl, hu⟩ := (mem_oddOpenBand X s x).mp hx
  exact (mem_oddOpenBand X t x).mpr
    ⟨ho, hl, hu.trans_le (mul_le_mul_of_nonneg_right hst hX)⟩

/-- The first subband is cheaper than every point outside its selected initial segment. -/
theorem band_occupation_threshold {X s : ℝ} {j : ℕ} (hX : 0 < X) (hj : 1 ≤ j)
    (hs : 1 < s) (hsu : s ≤ 3 / 2) (w : ℕ → ℝ)
    (hw : ∀ x ∈ oddOpenBand X 16, 0 ≤ w x ∧ w x ≤ 1) :
    4 * (j : ℝ) * (oddOpenBand X s).card + 4 * j * s * X *
      ((∑ x ∈ oddOpenBand X 16, w x / x) - ∑ x ∈ oddOpenBand X s, (x : ℝ)⁻¹) ≤
        ∑ x ∈ oddOpenBand X 16, w x * towerCount ((16 : ℝ) ^ j * X) x := by
  apply occupation_threshold _ _ w (fun x => towerCount ((16 : ℝ) ^ j * X) x)
    (4 * j) (4 * j * s * X) (oddOpenBand_subset hX.le (by linarith))
    (fun x hx => hX.trans ((mem_oddOpenBand X 16 x).mp hx).2.1) hw
  · intro x hx
    obtain ⟨_, hl, hu⟩ := (mem_oddOpenBand X s x).mp hx
    have h2 : (x : ℝ) < 2 * X := hu.trans_le
      (mul_le_mul_of_nonneg_right (by linarith) hX.le)
    have hc := towerCount_first_subband hX hj hl h2
    refine ⟨by exact_mod_cast hc, ?_⟩
    have := mul_le_mul_of_nonneg_left hu.le (by positivity : (0 : ℝ) ≤ 4 * j)
    nlinarith
  · intro x hx hxt
    obtain ⟨ho, hl, hu⟩ := (mem_oddOpenBand X 16 x).mp hx
    have hsx : s * X ≤ (x : ℝ) := by
      by_contra h
      exact hxt ((mem_oddOpenBand X s x).mpr ⟨ho, hl, lt_of_not_ge h⟩)
    by_cases h2 : (x : ℝ) < 2 * X
    · rw [towerCount_first_subband hX hj hl h2]
      push_cast
      have := mul_le_mul_of_nonneg_left hsx (by positivity : (0 : ℝ) ≤ 4 * j)
      nlinarith
    · have hc := towerCost_later_subbands hX hj (le_of_not_gt h2) hu
      have hsbound := mul_le_mul_of_nonneg_right hsu
        (by positivity : (0 : ℝ) ≤ 4 * j * X)
      nlinarith

/-- A finite error suffices whenever the harmonic mass reaches a fixed inner threshold. -/
theorem band_occupation_cost {X s : ℝ} {j : ℕ} (hX : 1 ≤ X) (hj : 1 ≤ j)
    (hs : 1 < s) (hsu : s ≤ 3 / 2) (w : ℕ → ℝ)
    (hw : ∀ x ∈ oddOpenBand X 16, 0 ≤ w x ∧ w x ≤ 1)
    (hm : Real.log s / 2 ≤ ∑ x ∈ oddOpenBand X 16, w x / x) :
    2 * (j : ℝ) * (s - 1) * X - 4 * j * (s + 1) ≤
      ∑ x ∈ oddOpenBand X 16, w x * towerCount ((16 : ℝ) ^ j * X) x := by
  have hp : 0 < X := by linarith
  have ht := band_occupation_threshold hp hj hs hsu w hw
  have hcard := (abs_le.mp (card_oddOpenBand_error hX hs)).1
  have hc : (s - 1) * X / 2 - 1 ≤ ((oddOpenBand X s).card : ℝ) := by linarith
  have hc' := mul_le_mul_of_nonneg_left hc (by positivity : (0 : ℝ) ≤ 4 * j)
  have hmass : -(1 / X) ≤
      (∑ x ∈ oddOpenBand X 16, w x / x) - ∑ x ∈ oddOpenBand X s, (x : ℝ)⁻¹ := by
    linarith [oddOpenBand_harmonic_upper hX hs]
  have hm' := mul_le_mul_of_nonneg_left hmass
    (by positivity : (0 : ℝ) ≤ 4 * j * s * X)
  have he : 4 * (j : ℝ) * s * X * -(1 / X) = -(4 * j * s) := by
    field_simp
  rw [he] at hm'
  nlinarith

/-- Every admitted limiting harmonic mass forces the manuscript's asymptotic band cost. -/
theorem harmonicBandCost (j : ℕ) (a : ℝ) (hj : 1 ≤ j) (ha : 0 ≤ a)
    (hau : a ≤ Real.log (3 / 2) / 2) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ Y : ℝ in atTop, ∀ w : ℕ → ℝ,
      (∀ x ∈ oddOpenBand (Y / (16 : ℝ) ^ j) 16, 0 ≤ w x ∧ w x ≤ 1) →
      a - η ≤ (∑ x ∈ oddOpenBand (Y / (16 : ℝ) ^ j) 16, w x / x) →
      (2 * j * (Real.exp (2 * a) - 1) / (16 : ℝ) ^ j - ε) * Y ≤
        ∑ x ∈ oddOpenBand (Y / (16 : ℝ) ^ j) 16, w x * towerCount Y x := by
  by_cases ha0 : a = 0
  · refine ⟨1, by norm_num, ?_⟩
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with Y hY w hw _
    have hc : 0 ≤ ∑ x ∈ oddOpenBand (Y / (16 : ℝ) ^ j) 16,
        w x * towerCount Y x :=
      Finset.sum_nonneg (fun x hx => mul_nonneg (hw x hx).1 (Nat.cast_nonneg _))
    simp only [ha0, mul_zero, Real.exp_zero, sub_self, zero_div, zero_sub]
    exact (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hε.le) hY).trans hc
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hjp : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
  have hq : (0 : ℝ) < (16 : ℝ) ^ j := by positivity
  have hE : 1 < Real.exp (2 * a) := by
    simpa using Real.exp_lt_exp.mpr (by linarith : 0 < 2 * a)
  have hgap : 0 < ε * (16 : ℝ) ^ j / (4 * j) := by positivity
  obtain ⟨s, hsL, hsE⟩ := exists_between (show
      max 1 (Real.exp (2 * a) - ε * (16 : ℝ) ^ j / (4 * j)) < Real.exp (2 * a) by
    exact max_lt hE (by linarith))
  have hs : 1 < s := (le_max_left _ _).trans_lt hsL
  have hspos : 0 < s := by linarith
  have hsu : s ≤ 3 / 2 := by
    have h := Real.exp_le_exp.mpr (by linarith : 2 * a ≤ Real.log (3 / 2))
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 3 / 2)] at h
    exact hsE.le.trans h
  have hlog : Real.log s / 2 < a := by
    have h := Real.log_lt_log hspos hsE
    rw [Real.log_exp] at h
    linarith
  have hcoef : 2 * (j : ℝ) * (Real.exp (2 * a) - s) / (16 : ℝ) ^ j ≤ ε / 2 := by
    have hnear : Real.exp (2 * a) - s < ε * (16 : ℝ) ^ j / (4 * j) := by
      have := (le_max_right _ _).trans_lt hsL
      linarith
    have hnear' := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * j)).mp hnear
    apply (div_le_iff₀ hq).mpr
    nlinarith
  refine ⟨(a - Real.log s / 2) / 2, by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop ((16 : ℝ) ^ j),
    eventually_ge_atTop (8 * (j : ℝ) * (s + 1) / ε)] with Y hY hlarge w hw hm
  have hYp : 0 < Y := hq.trans_le hY
  have hX : 1 ≤ Y / (16 : ℝ) ^ j := (one_le_div hq).mpr hY
  have hmass : Real.log s / 2 ≤ ∑ x ∈ oddOpenBand (Y / (16 : ℝ) ^ j) 16, w x / x := by
    linarith
  have hc := band_occupation_cost hX hj hs hsu w hw hmass
  rw [mul_div_cancel₀ Y (ne_of_gt hq)] at hc
  have herr : 4 * (j : ℝ) * (s + 1) ≤ ε * Y / 2 := by
    have h := (div_le_iff₀ hε).mp hlarge
    nlinarith
  have hnegative : (2 * (j : ℝ) * (Real.exp (2 * a) - s) / (16 : ℝ) ^ j - ε / 2) * Y ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) hYp.le
  calc
    _ = 2 * (j : ℝ) * (s - 1) * (Y / (16 : ℝ) ^ j) - ε * Y / 2 +
        (2 * j * (Real.exp (2 * a) - s) / (16 : ℝ) ^ j - ε / 2) * Y := by ring
    _ ≤ 2 * (j : ℝ) * (s - 1) * (Y / (16 : ℝ) ^ j) - 4 * j * (s + 1) := by linarith
    _ ≤ _ := hc

end WordCertDensity.Counting
