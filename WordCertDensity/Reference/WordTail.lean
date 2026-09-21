/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.WordMoment
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The exact two-sided Chernoff threshold for valuation words

A single parameter strictly below the geometric pole bounds both tails.
The length is positive and the deviation parameter is strictly positive.
-/

@[expose] public section

namespace WordCertDensity
namespace Reference

private theorem exists_chernoff_parameter {r z : ℝ} (hr : 0 < r) (hz : 0 < z) :
    ∃ t : ℝ, 0 < t ∧ t < Real.log 2 ∧
      -t * (2 * Real.sqrt (r * z) + z / Real.log 2) +
        r * (t ^ 2 / (1 - (Real.log 2)⁻¹ * t)) = -z := by
  let a := Real.sqrt r
  let b := Real.sqrt z
  let c := GeometricLog.poleCoefficient
  let d := a + c * b
  have ha : 0 < a := Real.sqrt_pos.mpr hr
  have hb : 0 < b := Real.sqrt_pos.mpr hz
  have hc : 0 < c := GeometricLog.poleCoefficient_pos
  have hd : 0 < d := add_pos ha (mul_pos hc hb)
  have hasq : a ^ 2 = r := Real.sq_sqrt hr.le
  have hbsq : b ^ 2 = z := Real.sq_sqrt hz.le
  have hroot : Real.sqrt (r * z) = a * b := Real.sqrt_mul hr.le z
  have hclog : c * Real.log 2 = 1 := GeometricLog.poleCoefficient_mul_log
  have hcb : Real.log 2 * (c * b) = b := by
    calc
      _ = (c * Real.log 2) * b := by ring
      _ = b := by rw [hclog, one_mul]
  have hdom : b / d < Real.log 2 := by
    apply (div_lt_iff₀ hd).mpr
    dsimp only [d]
    rw [mul_add, hcb]
    linarith [mul_pos GeometricLog.log_two_pos ha]
  have hslack : 1 - c * (b / d) = a / d := by
    dsimp only [d]
    field_simp
    ring
  have hcut : z / Real.log 2 = c * z := by
    dsimp only [c, GeometricLog.poleCoefficient]
    rw [div_eq_mul_inv, mul_comm]
  refine ⟨b / d, div_pos hb hd, hdom, ?_⟩
  change -(b / d) * (2 * Real.sqrt (r * z) + z / Real.log 2) +
    r * ((b / d) ^ 2 / (1 - c * (b / d))) = -z
  rw [hroot, hcut, hslack, ← hasq, ← hbsq]
  dsimp only [d]
  field_simp
  ring

/-- The positive centered word tail has the manuscript's exact optimized threshold. -/
theorem word_upperTail_chernoff {n : ℕ} (hn : 0 < n) {z : ℝ} (hz : 0 < z) :
    Gated.probability (wordPMF n)
      (fun w => 2 * Real.sqrt ((n : ℝ) * z) + z / Real.log 2 ≤ ValuationWord.centeredTotal w) ≤
      Real.exp (-z) := by
  obtain ⟨t, ht, hdom, he⟩ := exists_chernoff_parameter (r := (n : ℝ)) (by exact_mod_cast hn) hz
  calc
    _ ≤ Real.exp (-t * (2 * Real.sqrt ((n : ℝ) * z) + z / Real.log 2) +
        (n : ℝ) * (t ^ 2 / (1 - (Real.log 2)⁻¹ * t))) := word_upperTail_le n ht.le hdom
    _ = _ := congrArg Real.exp he

/-- The negative centered word tail satisfies the same optimized threshold. -/
theorem word_lowerTail_chernoff {n : ℕ} (hn : 0 < n) {z : ℝ} (hz : 0 < z) :
    Gated.probability (wordPMF n)
      (fun w => ValuationWord.centeredTotal w ≤ -(2 * Real.sqrt ((n : ℝ) * z) + z / Real.log 2)) ≤
      Real.exp (-z) := by
  obtain ⟨t, ht, hdom, he⟩ := exists_chernoff_parameter (r := (n : ℝ)) (by exact_mod_cast hn) hz
  have hd : 0 < 1 - (Real.log 2)⁻¹ * t := GeometricLog.slack_pos hdom
  have hd1 : 1 - (Real.log 2)⁻¹ * t ≤ 1 :=
    sub_le_self _ (mul_nonneg GeometricLog.poleCoefficient_pos.le ht.le)
  have hs : t ^ 2 ≤ t ^ 2 / (1 - (Real.log 2)⁻¹ * t) := by
    apply (le_div_iff₀ hd).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hd1 (sq_nonneg t)
  have hcost := add_le_add_left (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg n))
    (-t * (2 * Real.sqrt ((n : ℝ) * z) + z / Real.log 2))
  have hfinal : -t * (2 * Real.sqrt ((n : ℝ) * z) + z / Real.log 2) +
      (n : ℝ) * t ^ 2 ≤ -z := by linarith only [hcost, he]
  exact (word_lowerTail_le n ht.le).trans (Real.exp_le_exp.mpr hfinal)

/-- Both original iid tails, with non-strict threshold and no conditioning on a good event. -/
theorem word_absTail_le {n : ℕ} (hn : 0 < n) {z : ℝ} (hz : 0 < z) :
    Gated.probability (wordPMF n)
      (fun w => 2 * Real.sqrt ((n : ℝ) * z) + z / Real.log 2 ≤ |ValuationWord.centeredTotal w|) ≤
      2 * Real.exp (-z) := by
  let cutoff := 2 * Real.sqrt ((n : ℝ) * z) + z / Real.log 2
  have h := Gated.probability_mono_on_support (wordPMF n)
    (fun w => cutoff ≤ |ValuationWord.centeredTotal w|)
    (fun w => cutoff ≤ ValuationWord.centeredTotal w ∨ ValuationWord.centeredTotal w ≤ -cutoff)
    (fun w _ hw => by
      by_cases hsign : 0 ≤ ValuationWord.centeredTotal w
      · exact Or.inl (by simpa only [abs_of_nonneg hsign] using hw)
      · rw [abs_of_neg (lt_of_not_ge hsign)] at hw
        exact Or.inr (by linarith))
  have hu := Gated.probability_or_le (wordPMF n)
    (fun w => cutoff ≤ ValuationWord.centeredTotal w)
    (fun w => ValuationWord.centeredTotal w ≤ -cutoff)
  have ht := add_le_add (word_upperTail_chernoff hn hz) (word_lowerTail_chernoff hn hz)
  exact (h.trans hu).trans (by simpa only [cutoff, two_mul] using ht)

end Reference
end WordCertDensity
