/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.PassageLaw
public import WordCertDensity.Analytic.LocalPrimitive.EntryWhiteExit
import Mathlib.Tactic

/-! # The original white-exit probability on the exact passage law -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical

/-- A stopped prefix exits at a phase-white state strictly before the terminal. -/
def passageWhiteExit (n : ℕ) (ξ : ZMod (3 ^ n)) (j : ℕ) (l : ℤ)
    (u : ValuationWord) : Prop :=
  phaseWhiteAtInt n ξ (j + u.length / 2) (l + u.total) ∧ j + u.length / 2 < n / 2

/-- The overshoot coordinate is the actual accumulated integer height. -/
theorem passage_exit_height (top l : ℤ) (htop : l ≤ top) (i : ℕ) (w : ValuationWord)
    (hi : horizonTailEvent (top - l).toNat 0 i w) :
    top + ((ValuationWord.total (w.take (2 * (i + 1))) - (top - l).toNat : ℕ) : ℤ) =
      l + ValuationWord.total (w.take (2 * (i + 1))) := by
  have htotal : (top - l).toNat ≤ ValuationWord.total (w.take (2 * (i + 1))) := by
    have := hi.2
    omega
  rw [Nat.cast_sub htotal, Int.toNat_of_nonneg (by omega)]
  ring

/-- The white predicate on exact passage prefixes is the established original
white-exit event, with no changed distribution or shifted height. -/
theorem passageWhiteExit_event_iff (n a j : ℕ) (ξ : ZMod (3 ^ n))
    (top l : ℤ) (htop : l ≤ top) (w : ValuationWord)
    (hlen : 2 * ((top - l).toNat / 2 + 1) ≤ w.length) :
    (∃ u : passagePrefixFamily (top - l).toNat,
      (u : ValuationWord) <+: w ∧ passageWhiteExit n ξ j l u) ↔
      stoppedWhiteExitEvent n a j (top - l).toNat top l ξ w := by
  constructor
  · rintro ⟨u, hup, hw⟩
    obtain ⟨i, hlength, hi⟩ := u.property
    have hip := (horizonTailEvent_prefix_iff hup (by omega)).mp hi
    have he : (u : ValuationWord) = w.take (2 * ((i : ℕ) + 1)) := by
      simpa only [hlength] using List.prefix_iff_eq_take.mp hup
    have hd : (u : ValuationWord).length / 2 = (i : ℕ) + 1 := by omega
    change ¬ phaseBlackAtInt n ξ (j + (u : ValuationWord).length / 2)
      (l + (u : ValuationWord).total) ∧ j + (u : ValuationWord).length / 2 < n / 2 at hw
    rw [hd, he] at hw
    refine ⟨i, hip, ?_⟩
    rw [passage_exit_height top l htop i w hip]
    exact hw
  · rintro ⟨i, hi, hw, hbefore⟩
    have hidx := i.isLt
    have hp := passagePrefixFamily_take (top - l).toNat w i hi (by omega)
    have hlength : (w.take (2 * ((i : ℕ) + 1))).length = 2 * ((i : ℕ) + 1) :=
      List.length_take_of_le (by omega)
    refine ⟨⟨_, hp⟩, List.take_prefix _ _, ?_⟩
    change ¬ phaseBlackAtInt n ξ (j + (w.take (2 * ((i : ℕ) + 1))).length / 2)
      (l + ValuationWord.total (w.take (2 * ((i : ℕ) + 1)))) ∧
        j + (w.take (2 * ((i : ℕ) + 1))).length / 2 < n / 2
    rw [hlength, show 2 * ((i : ℕ) + 1) / 2 = (i : ℕ) + 1 by omega]
    rw [passage_exit_height top l htop i w hi] at hw
    exact ⟨hw, hbefore⟩

/-- The stopped-law white probability equals the already-proved fresh
original-word white-exit probability. -/
theorem passagePMF_white_probability (n a j : ℕ) (ξ : ZMod (3 ^ n))
    (top l : ℤ) (htop : l ≤ top) :
    Gated.probability (passagePMF (top - l).toNat) (fun u => passageWhiteExit n ξ j l u) =
      stoppedWhiteExitProbability n a j (top - l).toNat top l ξ := by
  rw [passagePMF_probability _ ((top - l).toNat / 2 + 1) le_rfl]
  unfold stoppedWhiteExitProbability
  apply Gated.probability_congr_on_support
  intro w hw
  have hlen : w.length = 2 * ((top - l).toNat / 2 + 1) := by
    by_contra hne
    exact hw (Reference.wordPMF_eq_zero_of_length_ne _ _ hne)
  exact passageWhiteExit_event_iff n a j ξ top l htop w (by omega)

/-- The actual stopped law has white-exit probability above fifteen sixteenths,
including a starting state at the top of its selected triangle. -/
theorem passagePMF_white_gt_fifteen_sixteenths {n a j : ℕ}
    (hn : 0 < n) (ha : 2 * a < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (top l : ℤ)
    (hsel : isSelectedPhaseTriangle n ξ a top)
    (hstart : inPhaseTriangleIntMul n ξ a top j l) :
    (15 / 16 : ℝ) < Gated.probability (passagePMF (top - l).toNat)
      (fun u => passageWhiteExit n ξ j l u) := by
  rw [passagePMF_white_probability n a j ξ top l hstart.2.1]
  by_cases hs : (top - l).toNat = 0
  · rw [hs]
    exact stoppedWhiteExitProbability_zero_gt_fifteen_sixteenths n a j top l ξ
      hsel hstart hs hn ha hξ
  · exact stoppedWhiteExitProbability_gt_fifteen_sixteenths (Nat.pos_of_ne_zero hs)
      n a j top l ξ hsel hstart rfl hn ha hξ

end WordCertDensity.LocalPrimitive
