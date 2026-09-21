/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.EntryDiscountStep
public import WordCertDensity.Analytic.LocalPrimitive.WeightedEntryExit
import Mathlib.Tactic

/-! # Original-law discounted entry weights -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- Prefix representation of the actual discounted entry contribution.
Prefix-freeness ensures at most one summand is nonzero. -/
noncomputable def entryStoppedWeight {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (r H : ℕ) (w : ValuationWord) : ℝ≥0∞ :=
  ∑' u : wordEntryPrefixFamily hn ξ hξ j l r H,
    if (u : ValuationWord) <+: w then
      pastExitDiscount hn ξ hξ j l u ((u : ValuationWord).length / 2) r else 0

/-- A selected entry contributes exactly its actual past-exit discount. -/
theorem entryStoppedWeight_of_entry {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (r H t : ℕ) (w : ValuationWord) (htH : t ≤ H)
    (ht : wordBlackEntryTime hn ξ hξ j l w r = some t) :
    entryStoppedWeight hn ξ hξ j l r H w = pastExitDiscount hn ξ hξ j l w t r := by
  have hsample := (wordBlackEntryTime_spec hn ξ hξ j l w r t ht).1
  have hlen : (w.take (2 * t)).length = 2 * t := List.length_take_of_le hsample
  have he : w.take (2 * t) = (w.take (2 * t)).take (2 * t) := by simp
  have hentry := (wordBlackEntryTime_prefix_congr hn ξ hξ j l hsample
    (by omega) he r).mp ht
  let u : wordEntryPrefixFamily hn ξ hξ j l r H :=
    ⟨w.take (2 * t), t, htH, hlen, hentry⟩
  have hp : (u : ValuationWord) <+: w := List.take_prefix _ _
  unfold entryStoppedWeight
  rw [tsum_eq_single u]
  · rw [if_pos hp]
    have hu : (u : ValuationWord).length / 2 = t := by dsimp [u]; omega
    rw [hu]
    exact (pastExitDiscount_prefix_congr hn ξ hξ j l hsample (by omega) he r).symm
  · intro v hv
    have hnot : ¬ (v : ValuationWord) <+: w := by
      intro hvp
      have hne : (v : ValuationWord) ≠ u := fun heq => hv (Subtype.ext heq)
      have hf := wordEntryPrefixFamily_prefix_free hn ξ hξ j l r H
      rcases List.prefix_or_prefix_of_prefix hvp hp with hh | hh
      · exact hf v.property u.property hne hh
      · exact hf u.property v.property (Ne.symm hne) hh
    simp [hnot]

/-- If the entry does not occur by the cutoff, its contribution is zero. -/
theorem entryStoppedWeight_of_absent {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (r H : ℕ) (w : ValuationWord)
    (hno : ¬ ∃ t, t ≤ H ∧ wordBlackEntryTime hn ξ hξ j l w r = some t) :
    entryStoppedWeight hn ξ hξ j l r H w = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro u
  have hp : ¬ (u : ValuationWord) <+: w := by
    intro hup
    exact hno ((wordEntryPrefixFamily_event_iff hn ξ hξ j l r H w).mp
      ⟨u, u.property, hup⟩)
  simp [hp]

/-- The discounted entry contribution is bounded by one pointwise. -/
theorem entryStoppedWeight_le_one {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (r H : ℕ) (w : ValuationWord) : entryStoppedWeight hn ξ hξ j l r H w ≤ 1 := by
  by_cases he : ∃ t, t ≤ H ∧ wordBlackEntryTime hn ξ hξ j l w r = some t
  · obtain ⟨t, htH, ht⟩ := he
    rw [entryStoppedWeight_of_entry hn ξ hξ j l r H t w htH ht]
    exact pastExitDiscount_le_one hn ξ hξ j l w t r
  · rw [entryStoppedWeight_of_absent hn ξ hξ j l r H w he]
    exact zero_le

/-- Discounted entry expectation on the original common word law. -/
noncomputable def entryStoppedMoment {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ) (r H Q : ℕ) : ℝ≥0∞ :=
  ∑' w : ValuationWord, entryStoppedWeight hn ξ hξ j l r H w * Reference.wordPMF (2 * Q) w

/-- The original expectation equals its past-discount-weighted prefix mass. -/
theorem entryStoppedMoment_eq_prefix_mass {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (r H Q : ℕ) (hHQ : H ≤ Q) :
    entryStoppedMoment hn ξ hξ j l r H Q =
      ∑' u : wordEntryPrefixFamily hn ξ hξ j l r H,
        pastExitDiscount hn ξ hξ j l u ((u : ValuationWord).length / 2) r *
          Reference.wordPMF (u : ValuationWord).length u := by
  unfold entryStoppedMoment entryStoppedWeight
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro u
  have hlen : (u : ValuationWord).length ≤ 2 * Q := by
    have := wordEntryPrefixFamily_length hn ξ hξ j l r H u u.property
    omega
  rw [wordPMF_length_eventMass, ← Reference.prefix_eventMass u hlen,
    ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro w
  by_cases hp : (u : ValuationWord) <+: w <;> simp [hp]

/-- The original discounted entry expectation is finite and at most one. -/
theorem entryStoppedMoment_le_one {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ) (r H Q : ℕ) :
    entryStoppedMoment hn ξ hξ j l r H Q ≤ 1 := by
  calc
    _ ≤ ∑' w : ValuationWord, Reference.wordPMF (2 * Q) w := by
      apply ENNReal.tsum_le_tsum
      intro w
      simpa only [one_mul] using
        mul_le_mul_left (entryStoppedWeight_le_one hn ξ hξ j l r H w)
          (Reference.wordPMF (2 * Q) w)
    _ = 1 := PMF.tsum_coe _

end WordCertDensity.LocalPrimitive
