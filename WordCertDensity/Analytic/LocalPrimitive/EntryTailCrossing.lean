/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.EntryWhiteExit
import WordCertDensity.Analytic.Typical

/-! # Identification of suffix first passage with the actual recorded exit -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- Heights after an observed cut are computed from its literal suffix. -/
theorem entryWordHeight_tail (l : ℤ) (w : ValuationWord) (s d : ℕ)
    (hd : 2 * (s + d) ≤ w.length) :
    entryWordHeight l w (s + d) = entryWordHeight l w s +
      (ValuationWord.total ((w.drop (2 * s)).take (2 * d)) : ℤ) := by
  rw [entryWordHeight_of_sampled l w (s + d) hd,
    entryWordHeight_of_sampled l w s (by omega), Nat.mul_add,
    List.take_add, ValuationWord.total_append, Nat.cast_add]
  omega

/-- A fresh suffix's strict first passage across the actual selected top
is exactly the exit time in the original full word. -/
theorem wordBlackExitTime_of_tail_passage {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (j : ℕ) (l : ℤ) (w : ValuationWord) (r s i : ℕ)
    (hs : wordBlackEntryTime hn ξ hξ j l w r = some s)
    (hlen : 2 * (s + (i + 1)) ≤ w.length)
    (hpass : horizonTailEvent
      ((entryWordTriangle hn ξ hξ j l w s).2 - entryWordHeight l w s).toNat
      0 i (w.drop (2 * s))) :
    wordBlackExitTime hn ξ hξ j l w r = some (s + (i + 1)) := by
  have htop := wordBlackEntryTime_top_ge hn ξ hξ j l w r s hs
  have hgap : (((entryWordTriangle hn ξ hξ j l w s).2 -
      entryWordHeight l w s).toNat : ℤ) =
      (entryWordTriangle hn ξ hξ j l w s).2 - entryWordHeight l w s :=
    Int.toNat_of_nonneg (sub_nonneg.mpr htop)
  apply blackExitTime_of_first_crossing _ _ _ r s _ hs (by omega)
  · rw [entryWordHeight_tail l w s (i + 1) hlen]
    have := hpass.2
    omega
  · intro q hsq hqt
    have hq : q = s + (q - s) := by omega
    rw [hq, entryWordHeight_tail l w s (q - s) (by omega)]
    have hm := ValuationWord.total_take_mono (w.drop (2 * s))
      (show 2 * (q - s) ≤ 2 * i by omega)
    have := hpass.1
    omega

/-- The fresh white-exit event produces a sampled white exit of the actual
entry process, with the same before-terminal convention. -/
theorem wordBlackExitTime_white_of_tail_event {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (j : ℕ) (l : ℤ) (w : ValuationWord) (r s : ℕ)
    (hs : wordBlackEntryTime hn ξ hξ j l w r = some s)
    (hlen : 2 * (s +
      ((entryWordTriangle hn ξ hξ j l w s).2 - entryWordHeight l w s).toNat / 2 + 1)
        ≤ w.length)
    (hevent : stoppedWhiteExitEvent n (entryWordTriangle hn ξ hξ j l w s).1
      (j + s) ((entryWordTriangle hn ξ hξ j l w s).2 - entryWordHeight l w s).toNat
      (entryWordTriangle hn ξ hξ j l w s).2 (entryWordHeight l w s) ξ
      (w.drop (2 * s))) :
    ∃ t, wordBlackExitTime hn ξ hξ j l w r = some t ∧
      ¬ phaseBlackAtInt n ξ (j + t) (entryWordHeight l w t) ∧ j + t < n / 2 := by
  obtain ⟨i, hpass, hwhite, hterminal⟩ := hevent
  have hi := i.isLt
  have hsample : 2 * (s + ((i : ℕ) + 1)) ≤ w.length := by omega
  refine ⟨s + ((i : ℕ) + 1),
    wordBlackExitTime_of_tail_passage hn ξ hξ j l w r s i hs hsample hpass, ?_,
    by simpa only [Nat.add_assoc] using hterminal⟩
  have htop := wordBlackEntryTime_top_ge hn ξ hξ j l w r s hs
  have hgap := Int.toNat_of_nonneg (sub_nonneg.mpr htop)
  have hc := hpass.2
  have hheight := entryWordHeight_tail l w s ((i : ℕ) + 1) hsample
  have heq : entryWordHeight l w (s + ((i : ℕ) + 1)) =
      (entryWordTriangle hn ξ hξ j l w s).2 +
      ((ValuationWord.total ((w.drop (2 * s)).take (2 * ((i : ℕ) + 1))) -
        ((entryWordTriangle hn ξ hξ j l w s).2 - entryWordHeight l w s).toNat : ℕ) : ℤ) := by
    omega
  rw [heq]
  simpa only [Nat.add_assoc] using hwhite

end WordCertDensity.LocalPrimitive
