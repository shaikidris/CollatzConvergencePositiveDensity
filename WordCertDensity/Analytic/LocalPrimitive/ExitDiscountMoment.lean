/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.EntryWhiteExit
public import WordCertDensity.Probability.FiniteUnion
import Mathlib.Tactic

/-! # Exact one-exit exponential expectation -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- Split the literal one-exit discount expectation over its white event. -/
theorem exitDiscountMoment_eq {α : Type*} (p : PMF α) (W : α → Prop) :
    (∑' x, p x * (if W x then ENNReal.ofReal (Real.exp (-1)) else 1)).toReal =
      Real.exp (-1) * Gated.probability p W + (1 - Gated.probability p W) := by
  have he : (∑' x, p x * (if W x then ENNReal.ofReal (Real.exp (-1)) else 1)) =
      ENNReal.ofReal (Real.exp (-1)) * (∑' x, if W x then p x else 0) +
        (∑' x, @ite ℝ≥0∞ (¬ W x) (Classical.propDecidable _) (p x) 0) := by
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
    apply tsum_congr
    intro x
    by_cases hx : W x <;> simp [hx, mul_comm]
  rw [he, ENNReal.toReal_add, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  rotate_left
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Gated.event_ne_top p W)
  · exact Gated.event_ne_top p (fun x => ¬ W x)
  change Real.exp (-1) * Gated.probability p W +
    Gated.probability p (fun x => ¬ W x) = _
  rw [Gated.probability_compl]

/-- A white-exit probability of fifteen sixteenths contracts the literal
one-exit discount expectation by at least one quarter. -/
theorem exitDiscountMoment_le {α : Type*} (p : PMF α) (W : α → Prop)
    (hW : (15 / 16 : ℝ) ≤ Gated.probability p W) :
    (∑' x, p x * (if W x then ENNReal.ofReal (Real.exp (-1)) else 1)).toReal ≤
      (3 / 4 : ℝ) := by
  rw [exitDiscountMoment_eq]
  have h := whiteExit_discount_le hW
  linarith

/-- The same contraction in the native codomain of countable stopped sums. -/
theorem exitDiscountMoment_ennreal_le {α : Type*} (p : PMF α) (W : α → Prop)
    (hW : (15 / 16 : ℝ) ≤ Gated.probability p W) :
    (∑' x, p x * (if W x then ENNReal.ofReal (Real.exp (-1)) else 1)) ≤
      (3 / 4 : ℝ≥0∞) := by
  have hz : ENNReal.ofReal (Real.exp (-1)) ≤ 1 := by
    apply ENNReal.ofReal_le_one.mpr
    exact Real.exp_le_one_iff.mpr (by norm_num)
  have hsum : (∑' x, p x * (if W x then ENNReal.ofReal (Real.exp (-1)) else 1)) ≤ 1 := by
    calc
      _ ≤ ∑' x, p x := ENNReal.tsum_le_tsum (fun x => by
        by_cases hx : W x
        · simpa only [if_pos hx, mul_one] using mul_le_mul_right hz (p x)
        · simp [hx])
      _ = 1 := PMF.tsum_coe p
  apply (ENNReal.toReal_le_toReal (ne_of_lt (lt_of_le_of_lt hsum (by simp)))
    (by finiteness)).mp
  simpa only [ENNReal.toReal_div, ENNReal.toReal_ofNat] using exitDiscountMoment_le p W hW

end WordCertDensity.LocalPrimitive
