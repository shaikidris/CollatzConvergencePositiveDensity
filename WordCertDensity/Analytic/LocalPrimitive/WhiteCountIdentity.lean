/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.WhiteVisitScan
public import WordCertDensity.Analytic.LocalPrimitive.ExitWhiteCount
import Mathlib.Tactic

/-! # Equality of recursive and time-indexed white-state counts -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical BigOperators

/-- The recursive scan counts precisely the white literal prefix states. -/
theorem whiteVisitCount_eq_sum (white : ℕ → ℤ → Prop) (h j : ℕ) (l : ℤ)
    (w : ValuationWord) :
    whiteVisitCount white h j l w =
      ∑ t ∈ Finset.range h,
        if white (j + t) (l + (ValuationWord.total (w.take (2 * t)) : ℤ)) then 1 else 0 := by
  induction h generalizing j l w with
  | zero => simp [whiteVisitCount]
  | succ h ih =>
      rw [whiteVisitCount, ih, Finset.sum_range_succ']
      have hzero : ValuationWord.total (w.take (2 * 0)) = 0 := by simp [ValuationWord.total]
      simp only [hzero, Nat.cast_zero, add_zero]
      rw [add_comm (if white j l then 1 else 0)]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      have hh : ValuationWord.total (w.take (2 * (t + 1))) =
          ValuationWord.total (w.take 2) + ValuationWord.total ((w.drop 2).take (2 * t)) := by
        rw [show 2 * (t + 1) = 2 + 2 * t by omega, List.take_add, ValuationWord.total_append]
      rw [hh, Nat.cast_add]
      simp only [Nat.add_comm 1 t, add_assoc]

/-- On an observed pair window, the finite time-set count and the recursive
post-exit count are identical. -/
theorem sampledWhiteStateCount_eq_whiteVisitCount (n : ℕ) (ξ : ZMod (3 ^ n))
    (j : ℕ) (l : ℤ) (w : ValuationWord) (P : ℕ) (hP : 2 * P ≤ w.length) :
    sampledWhiteStateCount n ξ j l w P =
      whiteVisitCount (extendedPhaseWhite n ξ) P j l w := by
  rw [whiteVisitCount_eq_sum]
  unfold sampledWhiteStateCount
  have hb := Finset.sum_boole (R := ℕ)
    (fun t => extendedPhaseWhite n ξ (j + t) (entryWordHeight l w t)) (Finset.range P)
  simp only [Nat.cast_id] at hb
  rw [← hb]
  apply Finset.sum_congr rfl
  intro t ht
  rw [entryWordHeight_of_sampled l w t (by have := Finset.mem_range.mp ht; omega)]

end WordCertDensity.LocalPrimitive
