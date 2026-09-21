/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.EntryMomentInduction
public import WordCertDensity.Analytic.LocalPrimitive.ExitWhiteCount
import Mathlib.Tactic

/-! # Repeated-entry probability on the original word law -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- The E.entries exponential probability estimate, with entry index r
denoting the manuscript's entry number r+1. -/
theorem entry_white_shortage_mass_le {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (r H P Q K : ℕ) (hHP : H ≤ P) (hQ : H + (8 * n + 8) ≤ Q) :
    (∑' w : ValuationWord,
      if (∃ t, t ≤ H ∧ wordBlackEntryTime hn ξ hξ j l w r = some t) ∧
        sampledWhiteStateCount n ξ j l w P < K then Reference.wordPMF (2 * Q) w else 0) ≤
      ENNReal.ofReal (Real.exp (K : ℝ)) * (3 / 4 : ℝ≥0∞) ^ r := by
  have hb : (∑' w : ValuationWord,
      if (∃ t, t ≤ H ∧ wordBlackEntryTime hn ξ hξ j l w r = some t) ∧
        sampledWhiteStateCount n ξ j l w P < K then Reference.wordPMF (2 * Q) w else 0) ≤
      ENNReal.ofReal (Real.exp (K : ℝ)) * entryStoppedMoment hn ξ hξ j l r H Q := by
    unfold entryStoppedMoment
    rw [← ENNReal.tsum_mul_left]
    apply ENNReal.tsum_le_tsum
    intro w
    split_ifs with he
    · obtain ⟨⟨t, htH, ht⟩, hc⟩ := he
      rw [entryStoppedWeight_of_entry hn ξ hξ j l r H t w htH ht]
      have hcount := pastWhiteExitCount_le_states hn ξ hξ j l w r t P (by omega)
      have hreal : (pastWhiteExitCount hn ξ hξ j l w t r : ℝ) ≤ (K : ℝ) := by
        exact_mod_cast (show pastWhiteExitCount hn ξ hξ j l w t r ≤ K by omega)
      have hexp : 1 ≤ Real.exp (K : ℝ) *
          Real.exp (-(pastWhiteExitCount hn ξ hξ j l w t r : ℝ)) := by
        rw [← Real.exp_add]
        apply Real.one_le_exp_iff.mpr
        linarith
      have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (K : ℝ)) *
          pastExitDiscount hn ξ hξ j l w t r := by
        simpa only [ENNReal.ofReal_one, ENNReal.ofReal_mul (Real.exp_pos _).le,
          pastExitDiscount] using ENNReal.ofReal_le_ofReal hexp
      simpa only [one_mul, mul_assoc] using mul_le_mul_left hone (Reference.wordPMF (2 * Q) w)
    · exact zero_le
  exact hb.trans (mul_le_mul_right (entryStoppedMoment_le_pow hn ξ hξ j l r H Q hQ) _)

end WordCertDensity.LocalPrimitive
