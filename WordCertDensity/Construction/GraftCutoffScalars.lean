/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.MacroLevels
import Mathlib.Analysis.Real.Sqrt

/-! # Scalar bounds for the explicit graft conductor cutoff

At positive large counts the ceiling costs one logarithm. If a macro uses
at most B blocks, every precision index stays below twice the current
scale; the depth coefficient is then linear in L+1.
-/

namespace WordCertDensity.Construction

/-- At counts at least two the shifted logarithm pays one full ceiling unit. -/
theorem graft_log_count_ge_one {B : ℕ} (hB : 2 ≤ B) : 1 ≤ Real.log ((B : ℝ) + 2) := by
  have hb : (2 : ℝ) ≤ B := by exact_mod_cast hB
  have h := Real.log_le_log (by norm_num : (0 : ℝ) < 4) (by linarith : (4 : ℝ) ≤ B + 2)
  have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [he] at h
  linarith [Head.log_two_lower]

/-- The shifted square root costs at most the factor three halves. -/
theorem graft_sqrt_shift_le {B : ℕ} (hB : 2 ≤ B) :
    Real.sqrt ((B : ℝ) + 2) ≤ (3 / 2 : ℝ) * Real.sqrt (B : ℝ) := by
  have hb : (2 : ℝ) ≤ B := by exact_mod_cast hB
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg B)]
  nlinarith

/-- A square-root logarithm bound suffices to keep the next macro shorter than B. -/
theorem graft_log_count_le_sqrt {B : ℕ} (hB : 2 ≤ B) :
    Real.log ((B : ℝ) + 2) ≤ 3 * Real.sqrt (B : ℝ) := by
  have h := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ (B : ℝ) + 2)
    (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at h
  have hs := graft_sqrt_shift_le hB
  linarith

/-- Squaring the quarter-power logarithm bound gives the manuscript's coefficient twenty-four. -/
theorem graft_log_count_sq_le_sqrt {B : ℕ} (hB : 2 ≤ B) :
    Real.log ((B : ℝ) + 2) ^ 2 ≤ 24 * Real.sqrt (B : ℝ) := by
  have hlog := graft_log_count_ge_one hB
  have h := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ (B : ℝ) + 2)
    (by norm_num : (0 : ℝ) < 1 / 4)
  have hp : Real.log ((B : ℝ) + 2) ≤ 4 * ((B : ℝ) + 2) ^ (1 / 4 : ℝ) := by linarith
  have hs := pow_le_pow_left₀ (by linarith : 0 ≤ Real.log ((B : ℝ) + 2)) hp 2
  have he : (4 * ((B : ℝ) + 2) ^ (1 / 4 : ℝ)) ^ 2 =
      16 * Real.sqrt ((B : ℝ) + 2) := by
    rw [mul_pow, ← Real.rpow_mul_natCast (by positivity)]
    norm_num only [show (4 : ℝ) ^ 2 = 16 by norm_num,
      show (1 / 4 : ℝ) * (2 : ℕ) = 1 / 2 by norm_num]
    rw [Real.sqrt_eq_rpow]
  rw [he] at hs
  have hshift := graft_sqrt_shift_le hB
  linarith

/-- For B at least two, L+1 suffices for the logarithmic macro length bound. -/
theorem graft_macroLength_le_log {L : ℝ} (hL : 0 ≤ L) {B : ℕ} (hB : 2 ≤ B) :
    (macroLength L B : ℝ) ≤ (L + 1) * Real.log ((B : ℝ) + 2) := by
  have h := (macroLength_bounds hL B).2
  have hlog := graft_log_count_ge_one hB
  nlinarith

/-- A macro of length at most B has the exact linear-in-L depth coefficient. -/
theorem graft_macroDepth_le {L : ℝ} (hL : 0 ≤ L) {B : ℕ} (hB : 2 ≤ B)
    (hlen : macroLength L B ≤ B) :
    (scheduledDepthBudget B (macroLength L B) : ℝ) ≤
      4000 * (L + 1) * Real.log ((B : ℝ) + 2) ^ 2 := by
  have hlenR : (macroLength L B : ℝ) ≤ B := Nat.cast_le.mpr hlen
  have hlog : Real.log ((B + macroLength L B : ℕ) + (2 : ℝ)) ≤
      2 * Real.log ((B : ℝ) + 2) := by
    have harg : ((B + macroLength L B : ℕ) : ℝ) + 2 ≤ 2 * ((B : ℝ) + 2) := by
      push_cast
      linarith
    have h := Real.log_le_log (by positivity) harg
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)] at h
    have htwo := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
      (by have := Nat.cast_nonneg (α := ℝ) B; linarith : (2 : ℝ) ≤ B + 2)
    linarith
  have hp := mul_le_mul (graft_macroLength_le_log hL hB) hlog
    (by linarith [log_count_add_two_lower (B + macroLength L B)] :
      0 ≤ Real.log ((B + macroLength L B : ℕ) + (2 : ℝ)))
    (by have := graft_log_count_ge_one hB; positivity : 0 ≤ (L + 1) * Real.log ((B : ℝ) + 2))
  have hd := scheduledDepthBudget_le_log B (macroLength L B)
  nlinarith

/-- The manuscript conductor uses the whole scheduled precision budget. -/
noncomputable def graftBudgetConductor (L : ℝ) (B : ℕ) : ℕ :=
  macroLevel (B + macroLength L B) + scheduledDepthBudget B (macroLength L B)

/-- Ceiling and precision terms give the stated 4002 logarithm-squared conductor coefficient. -/
theorem graftBudgetConductor_le_log {L : ℝ} (hL : 0 ≤ L) {B : ℕ} (hB : 2 ≤ B)
    (hlen : macroLength L B ≤ B) :
    (graftBudgetConductor L B : ℝ) ≤
      (B : ℝ) / 1000 + 4002 * (L + 1) * Real.log ((B : ℝ) + 2) ^ 2 := by
  have hk := (macroLevel_bounds (B + macroLength L B)).2
  have hd := graft_macroDepth_le hL hB hlen
  have hl := graft_macroLength_le_log hL hB
  have hlog := graft_log_count_ge_one hB
  have hsq : Real.log ((B : ℝ) + 2) ≤ Real.log ((B : ℝ) + 2) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ L + 1)
  have hone : 1 ≤ (L + 1) * Real.log ((B : ℝ) + 2) ^ 2 :=
    one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ hlog)
  unfold graftBudgetConductor
  push_cast at hk ⊢
  nlinarith

/-- The actual finite-family conductor never exceeds the scheduled-budget conductor. -/
theorem macroConductor_le_graftBudget (L δ : ℝ) (B : ℕ) :
    macroConductor L δ B ≤ graftBudgetConductor L B :=
  Nat.add_le_add_left (macroblockDepth_le L δ B) _

end WordCertDensity.Construction
