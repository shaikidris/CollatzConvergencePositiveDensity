/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.ExitWhiteCount
public import WordCertDensity.Analytic.LocalPrimitive.EntryCrossing
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! # White shortage bounds every observed gap before an entry -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical

/-- Every interval of white states contributes its full length to the count. -/
theorem white_interval_length_le (n : ℕ) (ξ : ZMod (3 ^ n)) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (a b P : ℕ) (hbP : b ≤ P)
    (hwhite : ∀ t, a ≤ t → t < b →
      extendedPhaseWhite n ξ (j + t) (entryWordHeight l w t)) :
    b - a ≤ sampledWhiteStateCount n ξ j l w P := by
  have hsub : Finset.Ico a b ⊆ (Finset.range P).filter (fun t =>
      extendedPhaseWhite n ξ (j + t) (entryWordHeight l w t)) := by
    intro t ht
    have hh := Finset.mem_Ico.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hwhite t hh.1 hh.2⟩
  simpa only [Nat.card_Ico, sampledWhiteStateCount] using Finset.card_le_card hsub

/-- If fewer than K white states occur, an observed interval of K states
must contain a black state. -/
theorem black_state_in_shortage_window (n : ℕ) (ξ : ZMod (3 ^ n))
    (j : ℕ) (l : ℤ) (w : ValuationWord) (a K P : ℕ)
    (hsample : 2 * P ≤ w.length) (ha : a + K ≤ P)
    (hshort : sampledWhiteStateCount n ξ j l w P < K) :
    ∃ t, a ≤ t ∧ t < a + K ∧ entryWordBlack n ξ j l w t := by
  by_contra hnone
  have hwhite : ∀ t, a ≤ t → t < a + K →
      extendedPhaseWhite n ξ (j + t) (entryWordHeight l w t) := by
    intro t hat hta
    have hb : ¬ entryWordBlack n ξ j l w t := fun hb => hnone ⟨t, hat, hta, hb⟩
    have he := entryWordBlack_iff_not_white n ξ j l w t (by omega)
    exact Classical.not_not.mp (fun hw => hb (he.mpr hw))
  have hc := white_interval_length_le n ξ j l w a (a + K) P ha hwhite
  omega

/-- The next first-black search succeeds within the same K-state window. -/
theorem first_black_soon_of_shortage (n : ℕ) (ξ : ZMod (3 ^ n))
    (j : ℕ) (l : ℤ) (w : ValuationWord) (a K P : ℕ)
    (hsample : 2 * P ≤ w.length) (ha : a + K ≤ P)
    (hshort : sampledWhiteStateCount n ξ j l w P < K) :
    ∃ t, t < a + K ∧ firstEventFrom (entryWordBlack n ξ j l w) a = some t := by
  obtain ⟨q, haq, hq, hb⟩ := black_state_in_shortage_window n ξ j l w a K P hsample ha hshort
  obtain ⟨t, htq, ht⟩ := firstEventFrom_exists_le (entryWordBlack n ξ j l w) a q haq hb
  exact ⟨t, by omega, ht⟩

end WordCertDensity.LocalPrimitive
