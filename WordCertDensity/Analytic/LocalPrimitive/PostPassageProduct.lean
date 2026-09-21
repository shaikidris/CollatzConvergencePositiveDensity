/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.PassageMomentBound
public import WordCertDensity.Analytic.LocalPrimitive.PostPassageHorizon
public import WordCertDensity.Analytic.LocalPrimitive.PostExitProduct
public import WordCertDensity.Analytic.LocalPrimitive.WhiteCountIdentity
import Mathlib.Tactic

/-! # The literal discounted product after the original first passage -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- The literal product expectation selected by exact passage prefixes.
Prefix-freeness ensures at most one summand is selected on each source word. -/
noncomputable def postPassageProductMoment (n : ℕ) (ξ : ZMod (3 ^ n))
    (s j : ℕ) (l : ℤ) (B L : ℕ) (z : ℝ≥0∞) : ℝ≥0∞ :=
  ∑' w : ValuationWord, ∑' u : passagePrefixFamily s,
    if (u : ValuationWord) <+: w then Reference.wordPMF (2 * L) w *
      whiteWindowProduct (extendedPhaseWhite n ξ) z (localPrimitiveP B)
        (j + (u : ValuationWord).length / 2) (l + (u : ValuationWord).total)
        (w.drop (u : ValuationWord).length) else 0

/-- The recursive white-count event selected at the exact crossing. -/
def passageWhiteShortageEvent (n : ℕ) (ξ : ZMod (3 ^ n))
    (s j : ℕ) (l : ℤ) (B : ℕ) (w : ValuationWord) : Prop :=
  ∃ u : passagePrefixFamily s, (u : ValuationWord) <+: w ∧
    whiteVisitCount (extendedPhaseWhite n ξ) (localPrimitiveP B)
      (j + (u : ValuationWord).length / 2) (l + (u : ValuationWord).total)
      (w.drop (u : ValuationWord).length) < localPrimitiveK B

/-- The prefix-selected recursive count is exactly the time-indexed
post-passage shortage event on a complete observed window. -/
theorem passageWhiteShortageEvent_iff (n : ℕ) (ξ : ZMod (3 ^ n))
    (s j : ℕ) (l : ℤ) (B : ℕ) (w : ValuationWord)
    (hw : 2 * (s / 2 + 1 + localPrimitiveP B) ≤ w.length) :
    passageWhiteShortageEvent n ξ s j l B w ↔ postPassageShortageEvent n ξ s j l B w := by
  constructor
  · rintro ⟨u, hup, hshort⟩
    obtain ⟨i, hlen, hi⟩ := u.property
    have hidx := i.isLt
    have he : (u : ValuationWord) = w.take (2 * ((i : ℕ) + 1)) := by
      simpa only [hlen] using List.prefix_iff_eq_take.mp hup
    have hd : (u : ValuationWord).length / 2 = (i : ℕ) + 1 := by omega
    refine ⟨i, (horizonTailEvent_prefix_iff hup (by omega)).mp hi, ?_⟩
    rw [sampledWhiteStateCount_eq_whiteVisitCount n ξ _ _ _ _
      (by rw [List.length_drop]; omega)]
    rw [hd, hlen] at hshort
    rw [he] at hshort
    exact hshort
  · rintro ⟨i, hi, hshort⟩
    have hidx := i.isLt
    have hp := passagePrefixFamily_take s w i hi (by omega)
    have hlen : (w.take (2 * ((i : ℕ) + 1))).length = 2 * ((i : ℕ) + 1) :=
      List.length_take_of_le (by omega)
    refine ⟨⟨_, hp⟩, List.take_prefix _ _, ?_⟩
    dsimp
    rw [hlen]
    have hd : 2 * ((i : ℕ) + 1) / 2 = (i : ℕ) + 1 := by omega
    rw [hd]
    rw [sampledWhiteStateCount_eq_whiteVisitCount n ξ _ _ _ _
      (by rw [List.length_drop]; omega)] at hshort
    exact hshort

/-- Averaging the fresh predictable-mark estimate yields the original
post-passage shortage mass plus the exact quarter-mark moment. -/
theorem postPassageProductMoment_le (n : ℕ) (ξ : ZMod (3 ^ n))
    (s j : ℕ) (l : ℤ) (B L : ℕ) {z : ℝ≥0∞} (hz : z ≤ 1)
    (hL : s / 2 + 1 + localPrimitiveP B + localPrimitiveK B + n / 2 ≤ L) :
    postPassageProductMoment n ξ s j l B L z ≤
      (∑' w : ValuationWord, if passageWhiteShortageEvent n ξ s j l B w
        then Reference.wordPMF (2 * L) w else 0) +
        ((1 / 4 : ℝ≥0∞) * z + 3 / 4) ^ localPrimitiveK B := by
  apply countableStoppedMoment_le_event_add (passagePrefixFamily s) (2 * L)
    (fun u v => whiteWindowProduct (extendedPhaseWhite n ξ) z (localPrimitiveP B)
      (j + u.length / 2) (l + u.total) v)
    (fun u v => whiteVisitCount (extendedPhaseWhite n ξ) (localPrimitiveP B)
      (j + u.length / 2) (l + u.total) v < localPrimitiveK B) _
    (fun u hu => by have := passagePrefixFamily_length s u hu; omega)
    (passagePrefixFamily_prefix_free s)
  intro u
  obtain ⟨i, hlen, _⟩ := u.property
  have hidx := i.isLt
  have hrem : 2 * L - (u : ValuationWord).length = 2 * (L - ((i : ℕ) + 1)) := by omega
  rw [hrem]
  exact whiteWindowProduct_moment_le (extendedPhaseWhite n ξ) hz (n / 2)
    (extendedPhaseWhite_after_terminal n ξ) (localPrimitiveP B) (L - ((i : ℕ) + 1))
    (localPrimitiveK B) (j + (u : ValuationWord).length / 2) (l + (u : ValuationWord).total)
    (by omega) (by omega)

end WordCertDensity.LocalPrimitive
