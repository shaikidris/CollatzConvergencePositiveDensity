/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.PostExitProduct
public import WordCertDensity.Analytic.LocalPrimitive.IntegerPotential

/-! # The window product is the original integer-height potential

This bridge identifies the source-law expectation exactly. The ensuing
estimate leaves only the geometric white-visit shortage probability open.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- The literal product expectation equals the original integer-height pair
potential, with no change of law or additional stopping assumption. -/
theorem whiteWindowProduct_eq_integerPairPotential {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (white : ℕ → ℤ → Prop) (h j : ℕ) (l : ℤ) :
    (∑' w : ValuationWord, Reference.wordPMF (2 * h) w *
      whiteWindowProduct white (ENNReal.ofReal (1 - 2 * ε ^ 2)) h j l w).toReal =
      integerPairPotential ε white h j l := by
  have hz : ENNReal.ofReal (1 - 2 * ε ^ 2) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg ε]
  have hfinite (h j : ℕ) (l : ℤ) :
      (∑' w : ValuationWord, Reference.wordPMF (2 * h) w *
        whiteWindowProduct white (ENNReal.ofReal (1 - 2 * ε ^ 2)) h j l w) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top
      (whiteWindowProduct_mass_le_one white hz h j l)
  induction h generalizing j l with
  | zero => simp [whiteWindowProduct, integerPairPotential, PMF.tsum_coe]
  | succ h ih =>
      rw [whiteWindowProduct_moment_succ, integerPairPotential_succ]
      have hrow (u : ValuationWord) :
          Reference.wordPMF 2 u *
            (if white j l ∧ u.total = 3 then ENNReal.ofReal (1 - 2 * ε ^ 2) else 1) *
              (∑' v : ValuationWord, Reference.wordPMF (2 * h) v *
                whiteWindowProduct white (ENNReal.ofReal (1 - 2 * ε ^ 2)) h
                  (j + 1) (l + u.total) v) ≠ ⊤ := by
        have hf := hfinite h (j + 1) (l + u.total)
        apply ENNReal.mul_ne_top _ hf
        apply ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
        split_ifs
        · exact ENNReal.ofReal_ne_top
        · exact ENNReal.one_ne_top
      rw [ENNReal.tsum_toReal_eq hrow]
      apply tsum_congr
      intro u
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ih]
      by_cases hw : white j l ∧ u.total = 3 <;>
        simp [hw, pairDiscount, ENNReal.toReal_ofReal (by linarith : 0 ≤ 1 - 2 * ε ^ 2)]

/-- Original integer-height potential bounded by the original white-visit
shortage and an explicit exponential term from predictable cancellation. -/
theorem integerPairPotential_le_whiteShortage {ε : ℝ} (hε : 2 * ε ^ 2 ≤ 1)
    (white : ℕ → ℤ → Prop) (N : ℕ)
    (hext : ∀ j, N ≤ j → ∀ l, white j l) (h k j : ℕ) (l : ℤ) :
    integerPairPotential ε white h j l ≤
      Gated.probability (Reference.wordPMF (2 * h))
        (fun w => whiteVisitCount white h j l w < k) +
        Real.exp (-(ε ^ 2 * (k : ℝ) / 2)) := by
  have hb := whiteWindowProduct_expectation_le_exp white
    (a := 2 * ε ^ 2) (by positivity) hε N hext h k j l
  rw [whiteWindowProduct_eq_integerPairPotential hε] at hb
  convert hb using 1
  congr 2
  ring

end WordCertDensity.LocalPrimitive
