/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.WordEntryStopping
public import WordCertDensity.Analytic.LocalPrimitive.EntryWhiteExit

/-! # White-exit inputs on the actual countable entry family -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- Fresh white exit from the endpoint of an exact entry prefix. -/
def entryPrefixWhiteTail {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (u v : ValuationWord) : Prop :=
  stoppedWhiteExitEvent n (entryWordTriangle hn ξ hξ j l u (u.length / 2)).1
    (j + u.length / 2)
    ((entryWordTriangle hn ξ hξ j l u (u.length / 2)).2 -
      entryWordHeight l u (u.length / 2)).toNat
    (entryWordTriangle hn ξ hξ j l u (u.length / 2)).2
    (entryWordHeight l u (u.length / 2)) ξ v

/-- Each actual entry prefix has white-exit probability above fifteen
sixteenths under exactly the remaining original-word law. -/
theorem entryPrefixWhiteTail_probability {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (j : ℕ) (l : ℤ) (r H Q : ℕ) (hQ : H + (8 * n + 8) ≤ Q)
    (u : ValuationWord) (hu : u ∈ wordEntryPrefixFamily hn ξ hξ j l r H) :
    (15 / 16 : ℝ) < Gated.probability (Reference.wordPMF (2 * Q - u.length))
      (entryPrefixWhiteTail hn ξ hξ j l u) := by
  obtain ⟨t, htH, hlen, ht⟩ := hu
  have htlen : u.length / 2 = t := by omega
  have hb := wordBlackEntry_whiteExitProbability hn ξ hξ j l u r t ht
  have hh := wordBlackEntry_passageHorizon_le hn ξ hξ j l u r t ht
  unfold entryPrefixWhiteTail
  rw [htlen]
  rw [← stoppedWhiteExitProbability_horizon n _ _ _ (2 * Q - u.length)
    _ _ ξ (by omega)]
  exact hb

/-- The white-exit mass after a numbered entry is at least fifteen
sixteenths of its stopping mass, all under the same original source law. -/
theorem entryPrefixWhiteTail_stopped_mass {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (j : ℕ) (l : ℤ) (r H Q : ℕ) (hQ : H + (8 * n + 8) ≤ Q) :
    Reference.countableStoppingMass (wordEntryPrefixFamily hn ξ hξ j l r H) *
      (15 / 16 : ℝ≥0∞) ≤
    ∑' w : ValuationWord,
      if ∃ u : wordEntryPrefixFamily hn ξ hξ j l r H,
        (u : ValuationWord) <+: w ∧
          entryPrefixWhiteTail hn ξ hξ j l u (w.drop (u : ValuationWord).length)
      then Reference.wordPMF (2 * Q) w else 0 := by
  rw [wordEntryPrefixFamily_tail_factor hn ξ hξ j l r H Q (by omega)]
  unfold Reference.countableStoppingMass
  rw [← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro u
  rw [← wordPMF_length_eventMass]
  apply mul_le_mul_right
  apply (ENNReal.toReal_le_toReal (by finiteness)
    (Gated.event_ne_top _ (entryPrefixWhiteTail hn ξ hξ j l u))).mp
  have hp := (entryPrefixWhiteTail_probability hn ξ hξ j l r H Q hQ u u.property).le
  simpa only [Gated.probability, ENNReal.toReal_div, ENNReal.toReal_ofNat] using hp

end WordCertDensity.LocalPrimitive
