/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.ScheduledBlocks
public import WordCertDensity.Construction.StoppedConcentration
public import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Macro lengths at the actual current count

The coefficient is fixed before the starting count. The recursion advances
by the actual number of original blocks consumed, with no restart of a small
macro index. A positive stopped-corridor rate supplies an explicit admissible
coefficient at every positive corridor width.
-/

@[expose] public section

namespace WordCertDensity.Construction

open Filter Asymptotics

/-- Every natural original count gives a positive logarithm bounded away from zero. -/
theorem log_count_add_two_lower (B : ℕ) : (1 / 2 : ℝ) < Real.log ((B : ℝ) + 2) := by
  have h : Real.log 2 ≤ Real.log ((B : ℝ) + 2) :=
    Real.log_le_log (by norm_num) (by have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B; linarith)
  linarith [Head.log_two_lower]

/-- Number of original stopped blocks in the next macroblock at current count B. -/
noncomputable def macroLength (L : ℝ) (B : ℕ) : ℕ := ⌈L * Real.log ((B : ℝ) + 2)⌉₊

/-- Actual cumulative original-block count after j macroblocks. -/
noncomputable def macroCount (L : ℝ) (B₀ : ℕ) : ℕ → ℕ
  | 0 => B₀
  | j + 1 => macroCount L B₀ j + macroLength L (macroCount L B₀ j)

/-- A concrete coefficient pays more than the required ten units of corridor exponent. -/
noncomputable def macroCoefficient (δ : ℝ) : ℝ := 11 / stoppedCorridorRate δ

/-- The chosen coefficient is positive and pays exactly eleven, hence strictly more than ten. -/
theorem macroCoefficient_spec {δ : ℝ} (hδ : 0 < δ) :
    0 < macroCoefficient δ ∧ stoppedCorridorRate δ * macroCoefficient δ = 11 := by
  have hc := stoppedCorridorRate_pos hδ
  refine ⟨div_pos (by norm_num) hc, ?_⟩
  simpa only [macroCoefficient, mul_comm] using div_mul_cancel₀ (11 : ℝ) hc.ne'

/-- Exact lower and strict upper rounding guards for the macro length. -/
theorem macroLength_bounds {L : ℝ} (hL : 0 ≤ L) (B : ℕ) :
    L * Real.log ((B : ℝ) + 2) ≤ macroLength L B ∧
      (macroLength L B : ℝ) < L * Real.log ((B : ℝ) + 2) + 1 := by
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one
    (mul_nonneg hL (by linarith [log_count_add_two_lower B]))⟩

/-- A positive coefficient always consumes at least one original block. -/
theorem macroLength_pos {L : ℝ} (hL : 0 < L) (B : ℕ) : 0 < macroLength L B := by
  have h : 1 ≤ macroLength L B := Nat.one_le_ceil_iff.mpr
    (mul_pos hL (by linarith [log_count_add_two_lower B]))
  omega

/-- Advancing the current count never decreases the next macro length. -/
theorem macroLength_mono {L : ℝ} (hL : 0 ≤ L) : Monotone (macroLength L) := by
  intro B C hBC
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ hL
  apply Real.log_le_log (by positivity)
  exact_mod_cast Nat.add_le_add_right hBC 2

/-- One explicit logarithmic bound absorbs the rounding error at all counts. -/
theorem macroLength_le_log {L : ℝ} (hL : 0 ≤ L) (B : ℕ) :
    (macroLength L B : ℝ) ≤ (L + 2) * Real.log ((B : ℝ) + 2) := by
  have h := (macroLength_bounds hL B).2
  nlinarith [log_count_add_two_lower B]

/-- A coarse linear bound is convenient for converting precision losses to polynomial tails. -/
theorem macroLength_le_count {L : ℝ} (hL : 0 ≤ L) (B : ℕ) :
    (macroLength L B : ℝ) ≤ (L + 1) * ((B : ℝ) + 2) := by
  have h := (macroLength_bounds hL B).2
  have hm := mul_le_mul_of_nonneg_left
    (Real.log_le_self (by positivity : 0 ≤ (B : ℝ) + 2)) hL
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  nlinarith

/-- The macro length has logarithmic growth with a coefficient independent of B_0. -/
theorem macroLength_isBigO {L : ℝ} (hL : 0 ≤ L) :
    (fun B : ℕ => (macroLength L B : ℝ)) =O[atTop]
      (fun B : ℕ => Real.log ((B : ℝ) + 2)) := by
  apply IsBigO.of_bound (L + 2)
  apply Filter.Eventually.of_forall
  intro B
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs,
    abs_of_pos (by linarith [log_count_add_two_lower B])]
  exact macroLength_le_log hL B

/-- Each macro index advances the actual count strictly. -/
theorem macroCount_strictMono {L : ℝ} (hL : 0 < L) (B₀ : ℕ) :
    StrictMono (macroCount L B₀) := by
  apply strictMono_nat_of_lt_succ
  intro j
  change macroCount L B₀ j < macroCount L B₀ j + macroLength L (macroCount L B₀ j)
  have h := macroLength_pos hL (macroCount L B₀ j)
  omega

/-- At least one original block is consumed at each macro step, including from count zero. -/
theorem macroCount_lower {L : ℝ} (hL : 0 < L) (B₀ j : ℕ) :
    B₀ + j ≤ macroCount L B₀ j := by
  induction j with
  | zero => simp [macroCount]
  | succ j ih =>
      change B₀ + (j + 1) ≤ macroCount L B₀ j + macroLength L (macroCount L B₀ j)
      have h := macroLength_pos hL (macroCount L B₀ j)
      omega

/-- The total consumed count is exactly the sum of the actual successive macro lengths. -/
theorem macroCount_eq_sum (L : ℝ) (B₀ j : ℕ) :
    macroCount L B₀ j = B₀ + ∑ k ∈ Finset.range j, macroLength L (macroCount L B₀ k) := by
  induction j with
  | zero => simp [macroCount]
  | succ j ih =>
      change macroCount L B₀ j + macroLength L (macroCount L B₀ j) = _
      rw [Finset.sum_range_succ]
      omega

/-- The actual count eventually reaches every threshold from each fixed starting count. -/
theorem macroCount_tendsto {L : ℝ} (hL : 0 < L) (B₀ : ℕ) :
    Tendsto (macroCount L B₀) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro n
  exact Filter.eventually_atTop.2 ⟨n, fun j hj => by
    have h := macroCount_lower hL B₀ j
    omega⟩

/-- Paying ten units of exponent gives the inverse tenth-power corridor factor. -/
theorem macroLength_exp_le (L c : ℝ) (hc : 0 ≤ c) (hpay : 10 ≤ c * L) (B : ℕ) :
    Real.exp (-c * macroLength L B) ≤ ((B : ℝ) + 2) ^ (-10 : ℝ) := by
  have hceil := Nat.le_ceil (L * Real.log ((B : ℝ) + 2))
  change L * Real.log ((B : ℝ) + 2) ≤ (macroLength L B : ℝ) at hceil
  have hm := mul_le_mul_of_nonneg_left hceil hc
  have hp := mul_le_mul_of_nonneg_right hpay
    (show 0 ≤ Real.log ((B : ℝ) + 2) by linarith [log_count_add_two_lower B])
  rw [Real.rpow_def_of_pos (by positivity : 0 < (B : ℝ) + 2)]
  apply Real.exp_le_exp.mpr
  nlinarith

end WordCertDensity.Construction
