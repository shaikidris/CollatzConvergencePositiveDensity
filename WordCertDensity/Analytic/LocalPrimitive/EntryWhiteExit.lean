/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.WordEntries
public import WordCertDensity.Analytic.LocalPrimitive.WhiteExit
import Mathlib.Tactic

/-! # White-exit probability at the actual selected entry triangle

The fresh law here starts at the literal sampled entry state, with the
triangle top chosen by the entry process. Stopped-tail factorization is
needed separately to lift this estimate into the common source word.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- The white-exit event only reads its finite first-passage horizon. -/
theorem stoppedWhiteExitEvent_take (n a j s : ℕ) (top l : ℤ)
    (ξ : ZMod (3 ^ n)) (w : ValuationWord) :
    stoppedWhiteExitEvent n a j s top l ξ (w.take (2 * (s / 2 + 1))) ↔
      stoppedWhiteExitEvent n a j s top l ξ w := by
  unfold stoppedWhiteExitEvent
  apply exists_congr
  intro i
  have hi := i.isLt
  simp only [horizonTailEvent, List.take_take,
    min_eq_left (show 2 * (i : ℕ) ≤ 2 * (s / 2 + 1) by omega),
    min_eq_left (show 2 * ((i : ℕ) + 1) ≤ 2 * (s / 2 + 1) by omega)]

/-- Extending the fresh sampling horizon preserves the white-exit probability. -/
theorem stoppedWhiteExitProbability_horizon (n a j s Q : ℕ) (top l : ℤ)
    (ξ : ZMod (3 ^ n)) (hQ : 2 * (s / 2 + 1) ≤ Q) :
    stoppedWhiteExitProbability n a j s top l ξ =
      Gated.probability (Reference.wordPMF Q)
        (stoppedWhiteExitEvent n a j s top l ξ) := by
  have hm := Gated.probability_map (Reference.wordPMF Q)
    (fun w => w.take (2 * (s / 2 + 1))) (stoppedWhiteExitEvent n a j s top l ξ)
  rw [Reference.wordPMF_map_take_of_le hQ] at hm
  simpa only [stoppedWhiteExitProbability, stoppedWhiteExitEvent_take] using hm

/-- A first-crossing witness identifies the exit recorded by the recursive
entry process. This is the converse needed when transporting a fresh tail. -/
theorem blackExitTime_of_first_crossing (black : ℕ → Prop) (height top : ℕ → ℤ)
    (r s t : ℕ) (hs : blackEntryTime black height top r = some s)
    (hst : s < t) (hcross : top s < height t)
    (hbefore : ∀ q, s < q → q < t → height q ≤ top s) :
    blackExitTime black height top r = some t := by
  simp only [blackExitTime, hs, Option.bind_some]
  apply (firstEventFrom_eq_some_iff _ _ _).mpr
  refine ⟨by omega, hcross, ?_⟩
  intro q hsq hqt
  have := hbefore q (by omega) hqt
  omega

/-- The white-exit lower bound pays the exponential factor used in E.entries. -/
theorem whiteExit_discount_le {p : ℝ} (hp : (15 / 16 : ℝ) ≤ p) :
    1 - p + p * Real.exp (-1) ≤ (3 / 4 : ℝ) := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hi : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos 1)]
    linarith
  have hp₀ : 0 ≤ p := by linarith
  have hm := mul_le_mul_of_nonneg_left hi hp₀
  linarith

/-- Every recorded entry has the uniform white-exit bound under the fresh
original pair law, including zero distance to its selected triangle top. -/
theorem wordBlackEntry_whiteExitProbability {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (j : ℕ) (l : ℤ) (w : ValuationWord) (r t : ℕ)
    (ht : wordBlackEntryTime hn ξ hξ j l w r = some t) :
    (15 / 16 : ℝ) < stoppedWhiteExitProbability n
      (entryWordTriangle hn ξ hξ j l w t).1 (j + t)
      ((entryWordTriangle hn ξ hξ j l w t).2 - entryWordHeight l w t).toNat
      (entryWordTriangle hn ξ hξ j l w t).2 (entryWordHeight l w t) ξ := by
  have hb := wordBlackEntryTime_spec hn ξ hξ j l w r t ht
  obtain ⟨hsel, hstart⟩ := entryWordTriangle_spec hn ξ hξ j l w t hb
  have hj₀ : 2 * (entryWordTriangle hn ξ hξ j l w t).1 < n := by
    have := hstart.1
    have := hb.2.1
    omega
  by_cases hs : ((entryWordTriangle hn ξ hξ j l w t).2 -
      entryWordHeight l w t).toNat = 0
  · rw [hs]
    exact stoppedWhiteExitProbability_zero_gt_fifteen_sixteenths
      n _ _ _ _ ξ hsel hstart hs hn hj₀ hξ
  · exact stoppedWhiteExitProbability_gt_fifteen_sixteenths
      (Nat.pos_of_ne_zero hs) n _ _ _ _ ξ hsel hstart rfl hn hj₀ hξ

/-- All selected entry triangles admit one deterministic fresh-word horizon.
The deliberately loose bound is used only to couple stopped events on a
single original word, and does not alter the manuscript's decay constants. -/
theorem wordBlackEntry_passageHorizon_le {n : ℕ} (hn : 0 < n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ)
    (j : ℕ) (l : ℤ) (w : ValuationWord) (r t : ℕ)
    (ht : wordBlackEntryTime hn ξ hξ j l w r = some t) :
    ((entryWordTriangle hn ξ hξ j l w t).2 - entryWordHeight l w t).toNat / 2 + 1
      ≤ 8 * n + 8 := by
  have hb := wordBlackEntryTime_spec hn ξ hξ j l w r t ht
  obtain ⟨hsel, hstart⟩ := entryWordTriangle_spec hn ξ hξ j l w t hb
  have hj₀ : 2 * (entryWordTriangle hn ξ hξ j l w t).1 < n := by
    have := hstart.1
    have := hb.2.1
    omega
  have hbound := firstPassageExit_before_terminal n _ (j + t)
    (5 * (((entryWordTriangle hn ξ hξ j l w t).2 -
      entryWordHeight l w t).toNat / 16) + 9)
    _ _ _ ξ hsel hstart rfl le_rfl hn hj₀ hξ
  omega

end WordCertDensity.LocalPrimitive
