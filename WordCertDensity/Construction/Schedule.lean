/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.PrecisionTail
public import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Linarith

/-!
# Global precision at the original block index

The same schedule is indexed by the actual original-block count, including
when a continuation begins late. Its original stopped-family deficits are
summable; they are never renormalized by surviving mass.
-/

@[expose] public section

namespace WordCertDensity.Construction

/-- The manuscript precision E_i; the formula also has a harmless value at i=0. -/
noncomputable def continuationPrecision (i : ℕ) : ℕ :=
  ⌈1000 * Real.log ((i : ℝ) + 2) / Real.log 2⌉₊

/-- The actual unconditioned mass lost by the scheduled finite stopped family. -/
noncomputable def continuationLoss (i : ℕ) : ℝ :=
  1 - Reference.stoppingMass (stoppedWords (continuationPrecision i))

private theorem log_two_pos : 0 < Real.log 2 := by linarith [Head.log_two_lower]

private theorem schedule_log_nonneg (i : ℕ) : 0 ≤ Real.log ((i : ℝ) + 2) := by
  apply Real.log_nonneg
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  linarith

/-- Lower and strict upper rounding bounds for the literal real logarithm. -/
theorem continuationPrecision_bounds (i : ℕ) :
    1000 * Real.log ((i : ℝ) + 2) / Real.log 2 ≤ continuationPrecision i ∧
      (continuationPrecision i : ℝ) <
        1000 * Real.log ((i : ℝ) + 2) / Real.log 2 + 1 := by
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one
    (div_nonneg (mul_nonneg (by norm_num) (schedule_log_nonneg i)) log_two_pos.le)⟩

/-- Even the unused zero index meets the fixed timeout range. -/
theorem continuationPrecision_ge_thousand (i : ℕ) : 1000 ≤ continuationPrecision i := by
  have hl : Real.log 2 ≤ Real.log ((i : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith)
  have hb : (1000 : ℝ) ≤ 1000 * Real.log ((i : ℝ) + 2) / Real.log 2 := by
    apply (le_div_iff₀ log_two_pos).mpr
    linarith
  have h := hb.trans (continuationPrecision_bounds i).1
  exact_mod_cast h

/-- The actual precision never decreases as the original count advances. -/
theorem continuationPrecision_mono : Monotone continuationPrecision := by
  intro i j hij
  apply Nat.ceil_mono
  apply div_le_div_of_nonneg_right _ log_two_pos.le
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.log_le_log (by positivity)
  exact_mod_cast Nat.add_le_add_right hij 2

/-- The scheduled original deficit has the literal inverse tenth-power majorant. -/
theorem continuationLoss_bound (i : ℕ) :
    0 ≤ continuationLoss i ∧ continuationLoss i ≤ ((i : ℝ) + 2) ^ (-10 : ℝ) := by
  constructor
  · exact sub_nonneg.mpr (stoppedWords_mass_bounds _).2
  · have hE : 256 ≤ continuationPrecision i :=
      (by norm_num : 256 ≤ 1000).trans (continuationPrecision_ge_thousand i)
    have h := stoppedWords_timeout (continuationPrecision i) hE
    refine h.1.trans (h.2.trans ?_)
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos (by positivity : 0 < (i : ℝ) + 2)]
    apply Real.exp_le_exp.mpr
    have hb := (div_le_iff₀ log_two_pos).mp (continuationPrecision_bounds i).1
    nlinarith

/-- The fixed inverse-power envelope is summable over all original indices. -/
theorem summable_continuationLoss_majorant :
    Summable (fun i : ℕ => ((i : ℝ) + 2) ^ (-10 : ℝ)) := by
  have h := (summable_nat_add_iff 2).mpr
    (Real.summable_nat_rpow.mpr (by norm_num : (-10 : ℝ) < -1))
  simpa only [Nat.cast_add, Nat.cast_ofNat] using h

/-- Actual rejection losses over the full global precision schedule are summable. -/
theorem summable_continuationLoss : Summable continuationLoss :=
  summable_continuationLoss_majorant.of_nonneg_of_le
    (fun i => (continuationLoss_bound i).1) (fun i => (continuationLoss_bound i).2)

/-- The depth-minus-one exponential envelope grows at most as a fixed polynomial. -/
theorem continuationPrecision_offset_polynomial (i : ℕ) :
    (3 / 2 : ℝ) ^ (continuationPrecision i - 1) ≤ ((i : ℝ) + 2) ^ (1000 : ℕ) := by
  have hp : 1 ≤ continuationPrecision i :=
    (by norm_num : 1 ≤ 1000).trans (continuationPrecision_ge_thousand i)
  have hb := (continuationPrecision_bounds i).2
  have hprev : ((continuationPrecision i - 1 : ℕ) : ℝ) <
      1000 * Real.log ((i : ℝ) + 2) / Real.log 2 := by
    rw [Nat.cast_sub hp, Nat.cast_one]
    linarith
  have hexp := (lt_div_iff₀ log_two_pos).mp hprev
  calc
    (3 / 2 : ℝ) ^ (continuationPrecision i - 1) ≤
        (2 : ℝ) ^ (continuationPrecision i - 1) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = Real.exp (Real.log 2 * ((continuationPrecision i - 1 : ℕ) : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ Real.exp (Real.log ((i : ℝ) + 2) * 1000) := by
      apply Real.exp_le_exp.mpr
      linarith
    _ = ((i : ℝ) + 2) ^ (1000 : ℕ) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by positivity : 0 < (i : ℝ) + 2)]
      norm_num

end WordCertDensity.Construction
