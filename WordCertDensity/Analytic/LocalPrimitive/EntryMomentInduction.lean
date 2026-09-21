/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.EntryExpectation
import Mathlib.Tactic

/-! # Original-law contraction of successive discounted entries -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- The original next-entry expectation contracts by three quarters.
Paths on which the next entry is absent contribute zero. -/
theorem entryStoppedMoment_step {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (r H Q : ℕ) (hQ : H + (8 * n + 8) ≤ Q) :
    entryStoppedMoment hn ξ hξ j l (r + 1) H Q ≤
      entryStoppedMoment hn ξ hξ j l r H Q * (3 / 4 : ℝ≥0∞) := by
  let a : wordEntryPrefixFamily hn ξ hξ j l r H → ℝ≥0∞ :=
    fun u => pastExitDiscount hn ξ hξ j l u ((u : ValuationWord).length / 2) r
  have hsource := entryPrefix_source_discount_contraction hn ξ hξ j l r H Q hQ a
  rw [entryStoppedMoment_eq_prefix_mass hn ξ hξ j l r H Q (by omega)]
  apply le_trans ?_ hsource
  apply ENNReal.tsum_le_tsum
  intro w
  by_cases hp : Reference.wordPMF (2 * Q) w = 0
  · simp [hp]
  by_cases he : ∃ t, t ≤ H ∧ wordBlackEntryTime hn ξ hξ j l w (r + 1) = some t
  · obtain ⟨t, htH, ht⟩ := he
    obtain ⟨s, q, hs, _, hsq, hqt⟩ := blackEntryTime_previous
      (entryWordBlack n ξ j l w) (entryWordHeight l w)
      (fun k => (entryWordTriangle hn ξ hξ j l w k).2) r t ht
    have hsH : s ≤ H := by omega
    have hsample := (wordBlackEntryTime_spec hn ξ hξ j l w r s hs).1
    have hlen : w.length = 2 * Q := (Reference.wordPMF_mem_support_iff _ w).mp hp
    have hprefixlen : (w.take (2 * s)).length = 2 * s := List.length_take_of_le hsample
    have htake : w.take (2 * s) = (w.take (2 * s)).take (2 * s) := by simp
    have hentry := (wordBlackEntryTime_prefix_congr hn ξ hξ j l hsample
      (by omega) htake r).mp hs
    let u : wordEntryPrefixFamily hn ξ hξ j l r H :=
      ⟨w.take (2 * s), s, hsH, hprefixlen, hentry⟩
    have hup : (u : ValuationWord) <+: w := List.take_prefix _ _
    have huLen : (u : ValuationWord).length = 2 * s := hprefixlen
    have ha : a u = pastExitDiscount hn ξ hξ j l w s r := by
      dsimp [a]
      rw [show (u : ValuationWord).length / 2 = s by omega]
      exact (pastExitDiscount_prefix_congr hn ξ hξ j l hsample (by omega) htake r).symm
    have hb := entryPrefixWhiteTail_iff_state hn ξ hξ j l u w s huLen hup
    have hd := pastExitDiscount_next_le hn ξ hξ j l w r s t hs ht (by omega)
    rw [entryStoppedWeight_of_entry hn ξ hξ j l (r + 1) H t w htH ht]
    apply le_trans ?_ (ENNReal.le_tsum u)
    rw [if_pos hup, ha, hb]
    have hm := mul_le_mul_left hd (Reference.wordPMF (2 * Q) w)
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hm
  · rw [entryStoppedWeight_of_absent hn ξ hξ j l (r + 1) H w he, zero_mul]
    exact zero_le

/-- Iteration of the source-law contraction over actual numbered entries. -/
theorem entryStoppedMoment_le_pow {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (r H Q : ℕ) (hQ : H + (8 * n + 8) ≤ Q) :
    entryStoppedMoment hn ξ hξ j l r H Q ≤ (3 / 4 : ℝ≥0∞) ^ r := by
  induction r with
  | zero => simpa using entryStoppedMoment_le_one hn ξ hξ j l 0 H Q
  | succ r ih =>
      calc
        _ ≤ entryStoppedMoment hn ξ hξ j l r H Q * (3 / 4 : ℝ≥0∞) :=
          entryStoppedMoment_step hn ξ hξ j l r H Q hQ
        _ ≤ (3 / 4 : ℝ≥0∞) ^ r * (3 / 4 : ℝ≥0∞) := mul_le_mul_left ih _
        _ = _ := (pow_succ _ _).symm

end WordCertDensity.LocalPrimitive
