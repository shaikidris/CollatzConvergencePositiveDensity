/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.MacroSchedule
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform scalar bounds for the actual-count macro schedule

The literal precision budget is bounded by an explicit multiple of log^2(B+2).
The precision-plus-corridor envelope is bounded by (L+5)(B+2)^(-9), uniformly
in the starting count. Identification of this envelope with an upper bound
on the actual finite macroblock deficit is a separate probability theorem.
-/

@[expose] public section

namespace WordCertDensity.Construction

open Filter Asymptotics

/-- The strict precision-minus-one budget is at most a fixed logarithmic bound. -/
theorem continuationPrecision_sub_one_le_log (i : ℕ) :
    ((continuationPrecision i - 1 : ℕ) : ℝ) ≤ 2000 * Real.log ((i : ℝ) + 2) := by
  have hp : 1 ≤ continuationPrecision i :=
    (by norm_num : 1 ≤ 1000).trans (continuationPrecision_ge_thousand i)
  have hb := (continuationPrecision_bounds i).2
  have hl : 0 ≤ Real.log ((i : ℝ) + 2) := by linarith [log_count_add_two_lower i]
  have hi : (Real.log 2)⁻¹ ≤ 2 := by
    apply (inv_le_iff_one_le_mul₀ (by linarith [Head.log_two_lower])).mpr
    linarith [Head.log_two_lower]
  have hm := mul_le_mul_of_nonneg_left hi
    (show 0 ≤ 1000 * Real.log ((i : ℝ) + 2) by positivity)
  rw [Nat.cast_sub hp, Nat.cast_one]
  rw [div_eq_mul_inv] at hb
  linarith

/-- Keep the full finite precision sum before replacing its terms by the last logarithm. -/
theorem scheduledDepthBudget_le_log (B n : ℕ) :
    (scheduledDepthBudget B n : ℝ) ≤
      (n : ℝ) * 2000 * Real.log ((B + n : ℕ) + (2 : ℝ)) := by
  rw [scheduledDepthBudget, Nat.cast_sum]
  calc
    (∑ j ∈ Finset.range n, ((continuationPrecision (B + j + 1) - 1 : ℕ) : ℝ)) ≤
        ∑ j ∈ Finset.range n, 2000 * Real.log ((B + n : ℕ) + (2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro j hj
      refine (continuationPrecision_sub_one_le_log (B + j + 1)).trans ?_
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.log_le_log (by positivity)
      have hn : B + j + 1 ≤ B + n := by have h := Finset.mem_range.mp hj; omega
      exact_mod_cast Nat.add_le_add_right hn 2
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

private theorem next_count_log_le {L : ℝ} (hL : 0 ≤ L) (B : ℕ) :
    Real.log ((B + macroLength L B : ℕ) + (2 : ℝ)) ≤
      (2 * L + 5) * Real.log ((B : ℝ) + 2) := by
  have hlen := macroLength_le_count hL B
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have harg : ((B + macroLength L B : ℕ) : ℝ) + 2 ≤
      (L + 2) * ((B : ℝ) + 2) := by
    push_cast
    nlinarith
  have hl := Real.log_le_log (by positivity) harg
  rw [Real.log_mul (by positivity : L + 2 ≠ 0) (by positivity : (B : ℝ) + 2 ≠ 0)] at hl
  have hc := Real.log_le_self (by positivity : 0 ≤ L + 2)
  have hm := mul_le_mul_of_nonneg_left (log_count_add_two_lower B).le
    (show 0 ≤ 2 * (L + 2) by positivity)
  nlinarith

/-- An all-count log-squared depth bound, with no dependence on an initial macro count. -/
theorem macroDepth_le_log_sq {L : ℝ} (hL : 0 ≤ L) (B : ℕ) :
    (scheduledDepthBudget B (macroLength L B) : ℝ) ≤
      (2000 * (L + 2) * (2 * L + 5)) * (Real.log ((B : ℝ) + 2)) ^ 2 := by
  have hdepth := scheduledDepthBudget_le_log B (macroLength L B)
  have hlen := macroLength_le_log hL B
  have hlog := next_count_log_le hL B
  have hp := mul_le_mul hlen hlog
    (show 0 ≤ Real.log ((B + macroLength L B : ℕ) + (2 : ℝ)) by
      linarith [log_count_add_two_lower (B + macroLength L B)])
    (show 0 ≤ (L + 2) * Real.log ((B : ℝ) + 2) by
      exact mul_nonneg (by positivity) (by linarith [log_count_add_two_lower B]))
  calc
    (scheduledDepthBudget B (macroLength L B) : ℝ) ≤
        (macroLength L B : ℝ) * 2000 *
          Real.log ((B + macroLength L B : ℕ) + (2 : ℝ)) := hdepth
    _ ≤ 2000 * (((L + 2) * Real.log ((B : ℝ) + 2)) *
        ((2 * L + 5) * Real.log ((B : ℝ) + 2))) := by nlinarith
    _ = _ := by ring

/-- The literal macroblock depth budget is O(log^2(B+2)). -/
theorem macroDepth_isBigO {L : ℝ} (hL : 0 ≤ L) :
    (fun B : ℕ => (scheduledDepthBudget B (macroLength L B) : ℝ)) =O[atTop]
      (fun B : ℕ => Real.log ((B : ℝ) + 2) ^ 2) := by
  apply IsBigO.of_bound (2000 * (L + 2) * (2 * L + 5))
  apply Filter.Eventually.of_forall
  intro B
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _), Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg _)]
  exact macroDepth_le_log_sq hL B

/-- Scalar precision-plus-corridor envelope, before the actual mass identification. -/
noncomputable def macroDeficitEnvelope (L c : ℝ) (B : ℕ) : ℝ :=
  (macroLength L B : ℝ) * ((B : ℝ) + 3) ^ (-10 : ℝ) +
    4 * Real.exp (-c * macroLength L B)

/-- The exact union-bound envelope is nonnegative and has a uniform ninth-power majorant. -/
theorem macroDeficitEnvelope_bounds {L c : ℝ} (hL : 0 ≤ L) (hc : 0 ≤ c)
    (hpay : 10 ≤ c * L) (B : ℕ) :
    0 ≤ macroDeficitEnvelope L c B ∧
      macroDeficitEnvelope L c B ≤ (L + 5) * ((B : ℝ) + 2) ^ (-9 : ℝ) := by
  refine ⟨by unfold macroDeficitEnvelope; positivity, ?_⟩
  have hbase : ((B : ℝ) + 3) ^ (-10 : ℝ) ≤ ((B : ℝ) + 2) ^ (-10 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  have hprod := mul_le_mul (macroLength_le_count hL B) hbase
    (show 0 ≤ ((B : ℝ) + 3) ^ (-10 : ℝ) by positivity)
    (show 0 ≤ (L + 1) * ((B : ℝ) + 2) by positivity)
  have heq : ((B : ℝ) + 2) * ((B : ℝ) + 2) ^ (-10 : ℝ) =
      ((B : ℝ) + 2) ^ (-9 : ℝ) := by
    calc
      _ = ((B : ℝ) + 2) ^ (1 : ℝ) * ((B : ℝ) + 2) ^ (-10 : ℝ) := by
        rw [Real.rpow_one]
      _ = ((B : ℝ) + 2) ^ ((1 : ℝ) + -10) :=
        (Real.rpow_add (by positivity) 1 (-10)).symm
      _ = _ := by norm_num
  have hm : (macroLength L B : ℝ) * ((B : ℝ) + 3) ^ (-10 : ℝ) ≤
      (L + 1) * ((B : ℝ) + 2) ^ (-9 : ℝ) := by
    refine hprod.trans_eq ?_
    rw [mul_assoc, heq]
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hstep : ((B : ℝ) + 2) ^ (-10 : ℝ) ≤ ((B : ℝ) + 2) ^ (-9 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have ht := mul_le_mul_of_nonneg_left ((macroLength_exp_le L c hc hpay B).trans hstep)
    (show (0 : ℝ) ≤ 4 by norm_num)
  unfold macroDeficitEnvelope
  nlinarith

/-- The scalar envelope has the manuscript's O((B+2)^(-9)) bound. -/
theorem macroDeficitEnvelope_isBigO {L c : ℝ} (hL : 0 ≤ L) (hc : 0 ≤ c)
    (hpay : 10 ≤ c * L) :
    macroDeficitEnvelope L c =O[atTop] (fun B : ℕ => ((B : ℝ) + 2) ^ (-9 : ℝ)) := by
  apply IsBigO.of_bound (L + 5)
  apply Filter.Eventually.of_forall
  intro B
  rw [Real.norm_eq_abs, abs_of_nonneg (macroDeficitEnvelope_bounds hL hc hpay B).1,
    Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact (macroDeficitEnvelope_bounds hL hc hpay B).2

/-- The scalar envelope is summable even over every integer original count. -/
theorem summable_macroDeficitEnvelope {L c : ℝ} (hL : 0 ≤ L) (hc : 0 ≤ c)
    (hpay : 10 ≤ c * L) : Summable (macroDeficitEnvelope L c) := by
  have h := (summable_nat_add_iff 2).mpr
    (Real.summable_nat_rpow.mpr (by norm_num : (-9 : ℝ) < -1))
  have hs : Summable (fun B : ℕ => ((B : ℝ) + 2) ^ (-9 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using h
  exact (hs.mul_left (L + 5)).of_nonneg_of_le
    (fun B => (macroDeficitEnvelope_bounds hL hc hpay B).1)
    (fun B => (macroDeficitEnvelope_bounds hL hc hpay B).2)

end WordCertDensity.Construction
