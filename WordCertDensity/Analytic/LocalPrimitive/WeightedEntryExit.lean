/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.WeightedStoppedTail
public import WordCertDensity.Analytic.LocalPrimitive.EntryStoppedWhite
public import WordCertDensity.Analytic.LocalPrimitive.ExitDiscountMoment

/-! # White-exit mass with prefix-measurable past weights -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- The actual white-exit lower bound remains valid with every nonnegative
weight determined by the entry prefix, including discounts from past exits. -/
theorem entryPrefixWhiteTail_weighted_mass {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (j : ℕ) (l : ℤ) (r H Q : ℕ) (hQ : H + (8 * n + 8) ≤ Q)
    (a : wordEntryPrefixFamily hn ξ hξ j l r H → ℝ≥0∞) :
    (∑' u : wordEntryPrefixFamily hn ξ hξ j l r H,
      a u * Reference.wordPMF (u : ValuationWord).length u) * (15 / 16 : ℝ≥0∞) ≤
    ∑' w : ValuationWord, ∑' u : wordEntryPrefixFamily hn ξ hξ j l r H,
      if (u : ValuationWord) <+: w ∧
        entryPrefixWhiteTail hn ξ hξ j l u (w.drop (u : ValuationWord).length)
      then a u * Reference.wordPMF (2 * Q) w else 0 := by
  rw [weightedStoppedTail_factor _ (2 * Q) a
    (entryPrefixWhiteTail hn ξ hξ j l) (by
      intro u hu
      have := wordEntryPrefixFamily_length hn ξ hξ j l r H u hu
      omega)]
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro u
  apply mul_le_mul_right
  apply (ENNReal.toReal_le_toReal (by finiteness)
    (Gated.event_ne_top _ (entryPrefixWhiteTail hn ξ hξ j l u))).mp
  have hp := (entryPrefixWhiteTail_probability hn ξ hξ j l r H Q hQ u u.property).le
  simpa only [Gated.probability, ENNReal.toReal_div, ENNReal.toReal_ofNat] using hp

/-- After factorization at actual entry prefixes, one white-exit discount
contracts every nonnegative past-weighted mass by three quarters. -/
theorem entryPrefix_discount_contraction {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (j : ℕ) (l : ℤ) (r H Q : ℕ) (hQ : H + (8 * n + 8) ≤ Q)
    (a : wordEntryPrefixFamily hn ξ hξ j l r H → ℝ≥0∞) :
    (∑' u : wordEntryPrefixFamily hn ξ hξ j l r H,
      a u * Reference.wordPMF (u : ValuationWord).length u *
        ∑' v : ValuationWord, Reference.wordPMF (2 * Q - (u : ValuationWord).length) v *
          (if entryPrefixWhiteTail hn ξ hξ j l u v
            then ENNReal.ofReal (Real.exp (-1)) else 1)) ≤
    (∑' u : wordEntryPrefixFamily hn ξ hξ j l r H,
      a u * Reference.wordPMF (u : ValuationWord).length u) * (3 / 4 : ℝ≥0∞) := by
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro u
  apply mul_le_mul_right
  exact exitDiscountMoment_ennreal_le _ _
    (entryPrefixWhiteTail_probability hn ξ hξ j l r H Q hQ u u.property).le

/-- The one-exit contraction holds on the original full-word distribution,
with every actual entry prefix retaining its past weight. -/
theorem entryPrefix_source_discount_contraction {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (j : ℕ) (l : ℤ) (r H Q : ℕ) (hQ : H + (8 * n + 8) ≤ Q)
    (a : wordEntryPrefixFamily hn ξ hξ j l r H → ℝ≥0∞) :
    (∑' w : ValuationWord, ∑' u : wordEntryPrefixFamily hn ξ hξ j l r H,
      if (u : ValuationWord) <+: w then a u * (Reference.wordPMF (2 * Q) w *
        (if entryPrefixWhiteTail hn ξ hξ j l u (w.drop (u : ValuationWord).length)
          then ENNReal.ofReal (Real.exp (-1)) else 1)) else 0) ≤
    (∑' u : wordEntryPrefixFamily hn ξ hξ j l r H,
      a u * Reference.wordPMF (u : ValuationWord).length u) * (3 / 4 : ℝ≥0∞) := by
  rw [weightedStoppedDiscount_factor _ (2 * Q) a
    (entryPrefixWhiteTail hn ξ hξ j l) _ (by
      intro u hu
      have := wordEntryPrefixFamily_length hn ξ hξ j l r H u hu
      omega)]
  exact entryPrefix_discount_contraction hn ξ hξ j l r H Q hQ a

end WordCertDensity.LocalPrimitive
