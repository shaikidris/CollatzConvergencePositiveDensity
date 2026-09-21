/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.WordEntryPrefix
public import WordCertDensity.Analytic.LocalPrimitive.EntryOrder
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! # Prefix dependence of the actual white-exit discount history -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- A numbered exit is white and occurs strictly before the observation cut. -/
def whiteExitBefore {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (T r : ℕ) : Prop :=
  ∃ t, t < T ∧ wordBlackExitTime hn ξ hξ j l w r = some t ∧
    extendedPhaseWhite n ξ (j + t) (entryWordHeight l w t)

/-- The count of white exits among the first r exits before the cut. -/
noncomputable def pastWhiteExitCount {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (T r : ℕ) : ℕ :=
  ((Finset.range r).filter (whiteExitBefore hn ξ hξ j l w T)).card

/-- Earlier white-exit events are determined by the observed prefix. -/
theorem whiteExitBefore_prefix_congr {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    {u v : ValuationWord} {T : ℕ} (hu : 2 * T ≤ u.length) (hv : 2 * T ≤ v.length)
    (he : u.take (2 * T) = v.take (2 * T)) (r : ℕ) :
    whiteExitBefore hn ξ hξ j l u T r ↔ whiteExitBefore hn ξ hξ j l v T r := by
  unfold whiteExitBefore
  apply exists_congr
  intro t
  by_cases ht : t < T
  · have hp := word_take_pair_prefix he (show t ≤ T by omega)
    have hx := wordBlackExitTime_prefix_congr hn ξ hξ j l
      (by omega) (by omega) hp r
    have hh := entryWordHeight_prefix_congr l (by omega) (by omega) hp
    rw [hh]
    exact and_congr_right (fun _ => and_congr hx Iff.rfl)
  · simp [ht]

/-- Counting the actual earlier white exits preserves prefix dependence. -/
theorem pastWhiteExitCount_prefix_congr {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    {u v : ValuationWord} {T : ℕ} (hu : 2 * T ≤ u.length) (hv : 2 * T ≤ v.length)
    (he : u.take (2 * T) = v.take (2 * T)) (r : ℕ) :
    pastWhiteExitCount hn ξ hξ j l u T r = pastWhiteExitCount hn ξ hξ j l v T r := by
  unfold pastWhiteExitCount
  congr 1
  apply Finset.filter_congr
  intro i _
  exact whiteExitBefore_prefix_congr hn ξ hξ j l hu hv he i

/-- The exponential discount contributed by the observed past white exits. -/
noncomputable def pastExitDiscount {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (T r : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-(pastWhiteExitCount hn ξ hξ j l w T r : ℝ)))

/-- The actual past discount can be used as a stopping-prefix weight. -/
theorem pastExitDiscount_prefix_congr {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    {u v : ValuationWord} {T : ℕ} (hu : 2 * T ≤ u.length) (hv : 2 * T ≤ v.length)
    (he : u.take (2 * T) = v.take (2 * T)) (r : ℕ) :
    pastExitDiscount hn ξ hξ j l u T r = pastExitDiscount hn ξ hξ j l v T r := by
  unfold pastExitDiscount
  rw [pastWhiteExitCount_prefix_congr hn ξ hξ j l hu hv he r]

/-- Adding one exit index records exactly its white-exit indicator. -/
theorem pastWhiteExitCount_succ {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (T r : ℕ) :
    pastWhiteExitCount hn ξ hξ j l w T (r + 1) =
      pastWhiteExitCount hn ξ hξ j l w T r +
        if whiteExitBefore hn ξ hξ j l w T r then 1 else 0 := by
  classical
  by_cases h : whiteExitBefore hn ξ hξ j l w T r
  · simp [pastWhiteExitCount, Finset.range_add_one, Finset.filter_insert, h]
  · simp [pastWhiteExitCount, Finset.range_add_one, Finset.filter_insert, h]

/-- At an existing entry all earlier white exits are strictly in the past.
An exit equal to the entry is black, by the inclusive re-entry convention. -/
theorem whiteExitBefore_at_entry {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (r s T i : ℕ)
    (hs : wordBlackEntryTime hn ξ hξ j l w r = some s) (hsT : s ≤ T) (hi : i < r) :
    whiteExitBefore hn ξ hξ j l w T i ↔ whiteExitBefore hn ξ hξ j l w s i := by
  obtain ⟨q, hq, hqs⟩ := blackEntryTime_earlier_exit
    (entryWordBlack n ξ j l w) (entryWordHeight l w)
    (fun t => (entryWordTriangle hn ξ hξ j l w t).2) r s hs i hi
  constructor
  · rintro ⟨t, _, ht, hw⟩
    have htq : t = q := Option.some.inj (ht.symm.trans hq)
    have hts : t ≤ s := by omega
    have hne : t ≠ s := by
      intro he
      rw [he] at hw
      have hb := wordBlackEntryTime_spec hn ξ hξ j l w r s hs
      exact ((entryWordBlack_iff_not_white n ξ j l w s hb.1).mp hb) hw
    exact ⟨t, by omega, ht, hw⟩
  · rintro ⟨t, hts, ht, hw⟩
    exact ⟨t, by omega, ht, hw⟩

/-- Observing beyond entry r cannot change the discount from exits before r. -/
theorem pastWhiteExitCount_at_entry {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (r s T : ℕ)
    (hs : wordBlackEntryTime hn ξ hξ j l w r = some s) (hsT : s ≤ T) :
    pastWhiteExitCount hn ξ hξ j l w T r = pastWhiteExitCount hn ξ hξ j l w s r := by
  unfold pastWhiteExitCount
  congr 1
  apply Finset.filter_congr
  intro i hi
  exact whiteExitBefore_at_entry hn ξ hξ j l w r s T i hs hsT (Finset.mem_range.mp hi)

/-- Across consecutive entry cuts the history gains exactly the intervening
white-exit indicator; earlier exit counts are unchanged. -/
theorem pastWhiteExitCount_next_entry {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (r s t : ℕ)
    (hs : wordBlackEntryTime hn ξ hξ j l w r = some s)
    (ht : wordBlackEntryTime hn ξ hξ j l w (r + 1) = some t) :
    pastWhiteExitCount hn ξ hξ j l w t (r + 1) =
      pastWhiteExitCount hn ξ hξ j l w s r +
        if whiteExitBefore hn ξ hξ j l w t r then 1 else 0 := by
  have hst := blackEntryTime_strict_succ (entryWordBlack n ξ j l w)
    (entryWordHeight l w) (fun q => (entryWordTriangle hn ξ hξ j l w q).2)
    r s t hs ht
  rw [pastWhiteExitCount_succ,
    pastWhiteExitCount_at_entry hn ξ hξ j l w r s t hs (by omega)]

/-- The actual discount gains precisely one exponential factor at a white
exit between successive entries. -/
theorem pastExitDiscount_next_entry {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (r s t : ℕ)
    (hs : wordBlackEntryTime hn ξ hξ j l w r = some s)
    (ht : wordBlackEntryTime hn ξ hξ j l w (r + 1) = some t) :
    pastExitDiscount hn ξ hξ j l w t (r + 1) =
      pastExitDiscount hn ξ hξ j l w s r *
        if whiteExitBefore hn ξ hξ j l w t r then ENNReal.ofReal (Real.exp (-1))
        else 1 := by
  unfold pastExitDiscount
  rw [pastWhiteExitCount_next_entry hn ξ hξ j l w r s t hs ht]
  by_cases hw : whiteExitBefore hn ξ hξ j l w t r
  · simp only [if_pos hw, Nat.cast_add, Nat.cast_one, neg_add_rev]
    rw [Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm]
  · simp [hw]

/-- Past-exit discounts are bounded by one on every observed word. -/
theorem pastExitDiscount_le_one {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (T r : ℕ) : pastExitDiscount hn ξ hξ j l w T r ≤ 1 := by
  unfold pastExitDiscount
  apply ENNReal.ofReal_le_one.mpr
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (Nat.cast_nonneg _)

end WordCertDensity.LocalPrimitive
