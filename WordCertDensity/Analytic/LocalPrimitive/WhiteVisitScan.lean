/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.PredictableMarks

/-! # White-visit counts and completion of the predictable scan

All counts inspect the current state before consuming the next valuation pair.
These deterministic identities connect the long-horizon predictable sample
to the finite post-exit window once that window has enough white visits.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- Number of white states before h pair steps on the literal sampled walk. -/
noncomputable def whiteVisitCount (white : ℕ → ℤ → Prop) :
    ℕ → ℕ → ℤ → ValuationWord → ℕ
  | 0, _, _, _ => 0
  | h + 1, j, l, w =>
      (if white j l then 1 else 0) +
        whiteVisitCount white h (j + 1)
          (l + ValuationWord.total (w.take 2)) (w.drop 2)

/-- Number of marked white states in the full h-step window. -/
noncomputable def whiteMarkCount (white : ℕ → ℤ → Prop) :
    ℕ → ℕ → ℤ → ValuationWord → ℕ
  | 0, _, _, _ => 0
  | h + 1, j, l, w =>
      (if white j l ∧ ValuationWord.total (w.take 2) = 3 then 1 else 0) +
        whiteMarkCount white h (j + 1)
          (l + ValuationWord.total (w.take 2)) (w.drop 2)

/-- Once its quota is zero the predictable scan counts nothing further. -/
theorem predictableMarkCount_zero_quota (white : ℕ → ℤ → Prop)
    (h j : ℕ) (l : ℤ) (w : ValuationWord) :
    predictableMarkCount white h 0 j l w = 0 := by
  cases h <;> rfl

/-- Every quota-selected mark is a marked white state of the full window. -/
theorem predictableMarkCount_le_whiteMarkCount (white : ℕ → ℤ → Prop)
    (h k j : ℕ) (l : ℤ) (w : ValuationWord) :
    predictableMarkCount white h k j l w ≤ whiteMarkCount white h j l w := by
  induction h generalizing k j l w with
  | zero => simp [predictableMarkCount, whiteMarkCount]
  | succ h ih =>
      cases k with
      | zero => rw [predictableMarkCount_zero_quota]; exact Nat.zero_le _
      | succ k =>
          by_cases hw : white j l
          · simp only [predictableMarkCount, whiteMarkCount, hw, if_true, true_and]
            exact Nat.add_le_add_left (ih k _ _ _) _
          · simp only [predictableMarkCount, whiteMarkCount, hw,
              false_and, if_false, zero_add]
            exact ih (k + 1) _ _ _

/-- Having seen k whites makes the selected count independent of how much
longer the word scan is allowed to run. No probability assumption is needed. -/
theorem predictableMarkCount_stable_of_whiteVisits (white : ℕ → ℤ → Prop)
    (h t k j : ℕ) (l : ℤ) (w : ValuationWord)
    (hk : k ≤ whiteVisitCount white h j l w) :
    predictableMarkCount white (h + t) k j l w =
      predictableMarkCount white h k j l w := by
  induction h generalizing k j l w with
  | zero =>
      have hk0 : k = 0 := by simpa [whiteVisitCount] using hk
      subst k
      rw [predictableMarkCount_zero_quota, predictableMarkCount_zero_quota]
  | succ h ih =>
      cases k with
      | zero => rw [predictableMarkCount_zero_quota, predictableMarkCount_zero_quota]
      | succ k =>
          rw [show h + 1 + t = (h + t) + 1 by omega]
          by_cases hw : white j l
          · have hk' : k ≤ whiteVisitCount white h (j + 1)
                (l + ValuationWord.total (w.take 2)) (w.drop 2) := by
              simp only [whiteVisitCount, if_pos hw] at hk
              omega
            simp only [predictableMarkCount, if_pos hw]
            rw [ih k _ _ _ hk']
          · have hk' : k + 1 ≤ whiteVisitCount white h (j + 1)
                (l + ValuationWord.total (w.take 2)) (w.drop 2) := by
              simpa only [whiteVisitCount, if_neg hw, zero_add] using hk
            simp only [predictableMarkCount, if_neg hw]
            exact ih (k + 1) _ _ _ hk'

/-- The long-horizon selected marks are already present in a shorter window
whenever that window contains the requested number of white states. -/
theorem predictableMarkCount_le_window_marks (white : ℕ → ℤ → Prop)
    (h H k j : ℕ) (l : ℤ) (w : ValuationWord) (hH : h ≤ H)
    (hk : k ≤ whiteVisitCount white h j l w) :
    predictableMarkCount white H k j l w ≤ whiteMarkCount white h j l w := by
  have he := predictableMarkCount_stable_of_whiteVisits white h (H - h) k j l w hk
  rw [Nat.add_sub_of_le hH] at he
  rw [he]
  exact predictableMarkCount_le_whiteMarkCount white h k j l w

end WordCertDensity.LocalPrimitive
