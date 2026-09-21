/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.EntryGeometry
public import WordCertDensity.Analytic.LocalPrimitive.EntryTimes

/-! # Entry and exit times on sampled reference valuation words

The path uses the total of the first 2t letters. Entries are observed only
at sampled times and before the terminal column. Thus `none` denotes absence
in this observed path, not a claim about unsampled future randomness.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical

/-- Actual integer height at pair time t, using only complete sampled pairs.
After the observed horizon the height is constant. -/
def entryWordHeight (l : ℤ) (w : ValuationWord) (t : ℕ) : ℤ :=
  l + ValuationWord.total ((w.take (2 * (w.length / 2))).take (2 * t))

/-- At a sampled pair time the height is exactly the literal prefix total. -/
theorem entryWordHeight_of_sampled (l : ℤ) (w : ValuationWord) (t : ℕ)
    (ht : 2 * t ≤ w.length) :
    entryWordHeight l w t = l + ValuationWord.total (w.take (2 * t)) := by
  simp only [entryWordHeight, List.take_take]
  rw [min_eq_left (by omega : 2 * t ≤ 2 * (w.length / 2))]

/-- The observed height is constant after the last complete pair. -/
theorem entryWordHeight_after_horizon (l : ℤ) (w : ValuationWord) (t : ℕ)
    (ht : w.length / 2 ≤ t) :
    entryWordHeight l w t = entryWordHeight l w (w.length / 2) := by
  simp only [entryWordHeight, List.take_take, min_self]
  rw [min_eq_right (by omega : 2 * (w.length / 2) ≤ 2 * t)]

/-- Blackness on the observed word, with the manuscript's terminal white
extension. The length guard distinguishes sampled from unsampled states. -/
def entryWordBlack (n : ℕ) (ξ : ZMod (3 ^ n)) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (t : ℕ) : Prop :=
  2 * t ≤ w.length ∧ j + t < n / 2 ∧ phaseBlackAtInt n ξ (j + t) (entryWordHeight l w t)

/-- The E.6 white extension: every column at or after the terminal is white. -/
def extendedPhaseWhite (n : ℕ) (ξ : ZMod (3 ^ n)) (j : ℕ) (l : ℤ) : Prop :=
  n / 2 ≤ j ∨ ¬ phaseBlackAtInt n ξ j l

/-- The white-extension hypothesis required by the predictable-mark producer. -/
theorem extendedPhaseWhite_after_terminal (n : ℕ) (ξ : ZMod (3 ^ n))
    (j : ℕ) (hj : n / 2 ≤ j) (l : ℤ) : extendedPhaseWhite n ξ j l := Or.inl hj

/-- At sampled states, entry blackness is exactly the complement of the
manuscript's white extension. -/
theorem entryWordBlack_iff_not_white (n : ℕ) (ξ : ZMod (3 ^ n))
    (j : ℕ) (l : ℤ) (w : ValuationWord) (t : ℕ) (ht : 2 * t ≤ w.length) :
    entryWordBlack n ξ j l w t ↔
      ¬ extendedPhaseWhite n ξ (j + t) (entryWordHeight l w t) := by
  simp [entryWordBlack, extendedPhaseWhite, ht]

/-- The selected triangle determined by the sampled entry state. Outside a
black observed state, the unused value is the current coordinate itself. -/
noncomputable def entryWordTriangle {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (t : ℕ) : ℕ × ℤ :=
  if hb : entryWordBlack n ξ j l w t then
    (entryTriangle hn (by have := hb.2.1; omega) ξ hξ hb.2.2).val
  else (j + t, entryWordHeight l w t)

/-- The actual sampled-word entry sequence, indexed from zero. -/
noncomputable def wordBlackEntryTime {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (r : ℕ) : Option ℕ :=
  blackEntryTime (entryWordBlack n ξ j l w) (entryWordHeight l w)
    (fun t => (entryWordTriangle hn ξ hξ j l w t).2) r

/-- The strict crossing of the triangle top fixed at the corresponding
sampled entry. An unobserved crossing remains absent on the finite word. -/
noncomputable def wordBlackExitTime {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (r : ℕ) : Option ℕ :=
  blackExitTime (entryWordBlack n ξ j l w) (entryWordHeight l w)
    (fun t => (entryWordTriangle hn ξ hξ j l w t).2) r

/-- Every observed black state receives a selected triangle containing the
literal state, so the accepted white-exit theorem can use this same top. -/
theorem entryWordTriangle_spec {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (t : ℕ) (hb : entryWordBlack n ξ j l w t) :
    isSelectedPhaseTriangle n ξ (entryWordTriangle hn ξ hξ j l w t).1
      (entryWordTriangle hn ξ hξ j l w t).2 ∧
    inPhaseTriangleIntMul n ξ (entryWordTriangle hn ξ hξ j l w t).1
      (entryWordTriangle hn ξ hξ j l w t).2 (j + t) (entryWordHeight l w t) := by
  simp only [entryWordTriangle, dif_pos hb]
  exact (entryTriangle hn (by have := hb.2.1; omega) ξ hξ hb.2.2).property

/-- A recorded entry is sampled, before the terminal column, and black. -/
theorem wordBlackEntryTime_spec {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (r t : ℕ)
    (ht : wordBlackEntryTime hn ξ hξ j l w r = some t) :
    entryWordBlack n ξ j l w t :=
  blackEntryTime_is_black _ _ _ r t ht

/-- The top used at a recorded entry is at or above the sampled height. -/
theorem wordBlackEntryTime_top_ge {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (r t : ℕ)
    (ht : wordBlackEntryTime hn ξ hξ j l w r = some t) :
    entryWordHeight l w t ≤ (entryWordTriangle hn ξ hξ j l w t).2 :=
  (entryWordTriangle_spec hn ξ hξ j l w t
    (wordBlackEntryTime_spec hn ξ hξ j l w r t ht)).2.2.1

/-- The inclusive convention holds on the original sampled word itself. -/
theorem wordBlackEntryTime_of_black_exit {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (r t : ℕ)
    (ht : wordBlackExitTime hn ξ hξ j l w r = some t)
    (hb : entryWordBlack n ξ j l w t) :
    wordBlackEntryTime hn ξ hξ j l w (r + 1) = some t :=
  blackEntryTime_of_black_exit _ _ _ r t ht hb

/-- Every recorded exit occurs at a complete sampled pair time. In
particular the constant continuation of the finite path creates no exits. -/
theorem wordBlackExitTime_sampled {n : ℕ} (hn : 0 < n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) (j : ℕ) (l : ℤ)
    (w : ValuationWord) (r t : ℕ)
    (ht : wordBlackExitTime hn ξ hξ j l w r = some t) : 2 * t ≤ w.length := by
  obtain ⟨s, hs, _⟩ := Option.bind_eq_some_iff.mp ht
  have hb := wordBlackEntryTime_spec hn ξ hξ j l w r s hs
  have htop := wordBlackEntryTime_top_ge hn ξ hξ j l w r s hs
  have hex := blackExitTime_spec (entryWordBlack n ξ j l w) (entryWordHeight l w)
    (fun q => (entryWordTriangle hn ξ hξ j l w q).2) r s t hs ht
  by_contra hnot
  have hst : s ≤ w.length / 2 := by have := hb.1; omega
  have hHt : w.length / 2 < t := by omega
  have hle : entryWordHeight l w (w.length / 2) ≤
      (entryWordTriangle hn ξ hξ j l w s).2 := by
    by_cases he : s = w.length / 2
    · simpa only [he] using htop
    · exact hex.2.2 (w.length / 2) (by omega) hHt
  have htHeight := entryWordHeight_after_horizon l w t (by omega)
  rw [htHeight] at hex
  omega

end WordCertDensity.LocalPrimitive
