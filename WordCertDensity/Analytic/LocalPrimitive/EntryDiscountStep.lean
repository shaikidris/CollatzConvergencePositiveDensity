/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.EntryDiscountHistory
public import WordCertDensity.Analytic.LocalPrimitive.EntryTailCrossing
public import WordCertDensity.Analytic.LocalPrimitive.EntryStoppedWhite
import Mathlib.Tactic

/-! # Pointwise comparison of successive entry discounts -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- The fresh white-exit event attached to a specified full-word entry state. -/
def entryStateWhiteTail {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (s : ℕ) : Prop :=
  stoppedWhiteExitEvent n (entryWordTriangle hn ξ hξ j l w s).1
    (j + s) ((entryWordTriangle hn ξ hξ j l w s).2 - entryWordHeight l w s).toNat
    (entryWordTriangle hn ξ hξ j l w s).2 (entryWordHeight l w s) ξ (w.drop (2 * s))

/-- The prefix-tail event in the stopped law is the identical event attached
to the full word's entry state. -/
theorem entryPrefixWhiteTail_iff_state {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (u w : ValuationWord) (s : ℕ) (hu : u.length = 2 * s) (hp : u <+: w) :
    entryPrefixWhiteTail hn ξ hξ j l u (w.drop u.length) ↔
      entryStateWhiteTail hn ξ hξ j l w s := by
  have hs : u.length / 2 = s := by omega
  have hw : 2 * s ≤ w.length := by have := hp.length_le; omega
  have he : u.take (2 * s) = w.take (2 * s) := by
    rw [← hu, List.take_length]
    exact List.prefix_iff_eq_take.mp hp
  have htri := entryWordTriangle_prefix_congr hn ξ hξ j l (by omega) hw he
  have hheight := entryWordHeight_prefix_congr l (by omega) hw he
  unfold entryPrefixWhiteTail entryStateWhiteTail
  rw [hs, htri, hheight, hu]

/-- If another entry exists, the concrete white-tail event supplies its
intervening white-exit indicator, strictly before that next entry. -/
theorem entryStateWhiteTail_before_next {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (r s t : ℕ)
    (hs : wordBlackEntryTime hn ξ hξ j l w r = some s)
    (ht : wordBlackEntryTime hn ξ hξ j l w (r + 1) = some t)
    (hlen : 2 * (s + (8 * n + 8)) ≤ w.length)
    (he : entryStateWhiteTail hn ξ hξ j l w s) :
    whiteExitBefore hn ξ hξ j l w t r := by
  have hh := wordBlackEntry_passageHorizon_le hn ξ hξ j l w r s hs
  obtain ⟨q, hq, hw, _⟩ := wordBlackExitTime_white_of_tail_event
    hn ξ hξ j l w r s hs (by omega) he
  have hqt := (blackEntryTime_white_gap (entryWordBlack n ξ j l w)
    (entryWordHeight l w) (fun k => (entryWordTriangle hn ξ hξ j l w k).2)
    r q t hq ht).1
  apply (whiteExitBefore_at_entry hn ξ hξ j l w (r + 1) t (t + 1) r ht
    (by omega) (by omega)).mp
  exact ⟨q, by omega, hq, Or.inr hw⟩

/-- The next-entry discount is dominated by the current discount times
the concrete fresh-exit factor on the same original word. -/
theorem pastExitDiscount_next_le {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (r s t : ℕ)
    (hs : wordBlackEntryTime hn ξ hξ j l w r = some s)
    (ht : wordBlackEntryTime hn ξ hξ j l w (r + 1) = some t)
    (hlen : 2 * (s + (8 * n + 8)) ≤ w.length) :
    pastExitDiscount hn ξ hξ j l w t (r + 1) ≤
      pastExitDiscount hn ξ hξ j l w s r *
        (if entryStateWhiteTail hn ξ hξ j l w s
          then ENNReal.ofReal (Real.exp (-1)) else 1) := by
  rw [pastExitDiscount_next_entry hn ξ hξ j l w r s t hs ht]
  apply mul_le_mul_right
  by_cases he : entryStateWhiteTail hn ξ hξ j l w s
  · have hw := entryStateWhiteTail_before_next hn ξ hξ j l w r s t hs ht hlen he
    simp [he, hw]
  · simp only [if_neg he]
    split_ifs
    · apply ENNReal.ofReal_le_one.mpr
      exact Real.exp_le_one_iff.mpr (by norm_num)
    · exact le_rfl

end WordCertDensity.LocalPrimitive
