/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.ProductSplit
public import WordCertDensity.Analytic.LocalPrimitive.LayerBridge
public import WordCertDensity.Analytic.LocalPrimitive.WordEntries
import Mathlib.Tactic

/-! # The actual remaining potential and the white-extended product -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- A window product only depends on the white predicate at its sampled columns. -/
theorem whiteWindowProduct_congr_columns (W V : ℕ → ℤ → Prop) (z : ℝ≥0∞)
    (h j : ℕ) (l : ℤ) (w : ValuationWord)
    (hWV : ∀ t, t < h → ∀ b, W (j + t) b ↔ V (j + t) b) :
    whiteWindowProduct W z h j l w = whiteWindowProduct V z h j l w := by
  induction h generalizing j l w with
  | zero => rfl
  | succ h ih =>
      rw [whiteWindowProduct, whiteWindowProduct]
      have hwv : W j l ↔ V j l := by simpa using hWV 0 (by omega) l
      rw [hwv]
      congr 1
      apply ih
      intro t ht b
      have he := hWV (t + 1) (by omega) b
      simpa only [Nat.add_assoc, Nat.add_comm 1 t] using he

/-- Before the terminal column, extending all subsequent columns as white
does not change the original phase product. -/
theorem phaseProduct_eq_extended (n : ℕ) (ξ : ZMod (3 ^ n)) (z : ℝ≥0∞)
    (h j : ℕ) (l : ℤ) (w : ValuationWord) (hj : j + h ≤ n / 2) :
    whiteWindowProduct (phaseWhiteAtInt n ξ) z h j l w =
      whiteWindowProduct (extendedPhaseWhite n ξ) z h j l w := by
  apply whiteWindowProduct_congr_columns
  intro t ht b
  have hbefore : ¬ n / 2 ≤ j + t := by omega
  simp only [phaseWhiteAtInt, extendedPhaseWhite, hbefore, false_or]

/-- The actual remaining-distance potential is exactly the expectation of
the extended product on its own original reference horizon. -/
theorem phaseRemainingPotential_eq_product (n m : ℕ) (ξ : ZMod (3 ^ n))
    (l : ℤ) (hm : m ≤ n / 2) :
    phaseRemainingPotential n ξ (n / 2) m l =
      (∑' w : ValuationWord, Reference.wordPMF (2 * m) w *
        whiteWindowProduct (extendedPhaseWhite n ξ)
          (ENNReal.ofReal (1 - 2 * localEpsilon ^ 2)) m (n / 2 - m) l w).toReal := by
  unfold phaseRemainingPotential phasePairPotential
  rw [← whiteWindowProduct_eq_integerPairPotential localEpsilon_guard]
  congr 1
  apply tsum_congr
  intro w
  rw [phaseProduct_eq_extended n ξ _ m (n / 2 - m) l w (by omega)]

end WordCertDensity.LocalPrimitive
