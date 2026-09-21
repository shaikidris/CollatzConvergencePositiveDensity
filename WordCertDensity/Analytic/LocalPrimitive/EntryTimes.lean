/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Data.Nat.Find
import Mathlib.Tactic

/-! # Inclusive entries and fixed-top strict exits

An absent event is represented by `none`. An entry samples its top once;
the exit search keeps that top fixed. The next black search begins at the
exit itself, rather than at its successor.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical

/-- First occurrence of an event at or after the inclusive starting time. -/
noncomputable def firstEventFrom (P : ℕ → Prop) (start : ℕ) : Option ℕ :=
  if h : ∃ t, start ≤ t ∧ P t then some (Nat.find h) else none

/-- The selected time is exactly the least admissible occurrence. -/
theorem firstEventFrom_eq_some_iff (P : ℕ → Prop) (start t : ℕ) :
    firstEventFrom P start = some t ↔
      start ≤ t ∧ P t ∧ ∀ s, start ≤ s → s < t → ¬ P s := by
  unfold firstEventFrom
  split_ifs with h
  · rw [Option.some.injEq, Nat.find_eq_iff]
    constructor
    · rintro ⟨⟨hst, ht⟩, hmin⟩
      exact ⟨hst, ht, fun s hs hlt hp => hmin s hlt ⟨hs, hp⟩⟩
    · rintro ⟨hst, ht, hmin⟩
      exact ⟨⟨hst, ht⟩, fun s hlt hs => hmin s hs.1 hlt hs.2⟩
  · constructor
    · intro he
      cases he
    · rintro ⟨hst, ht, _⟩
      exact (h ⟨t, hst, ht⟩).elim

/-- No occurrence means the whole remaining interval avoids the event. -/
theorem firstEventFrom_eq_none_iff (P : ℕ → Prop) (start : ℕ) :
    firstEventFrom P start = none ↔ ∀ t, start ≤ t → ¬ P t := by
  unfold firstEventFrom
  split_ifs with h
  · obtain ⟨t, ht, hp⟩ := h
    simp only [false_iff]
    intro hn
    exact hn t ht hp
  · simp only [true_iff]
    intro t ht hp
    exact h ⟨t, ht, hp⟩

/-- An event already present at the initial time is selected immediately. -/
theorem firstEventFrom_of_event (P : ℕ → Prop) (start : ℕ) (h : P start) :
    firstEventFrom P start = some start :=
  (firstEventFrom_eq_some_iff P start start).mpr
    ⟨le_rfl, h, fun _ hs hlt => (by omega)⟩

/-- Successive black entries, with a fixed entry top and inclusive re-entry.
Index zero denotes the manuscript's first entry. -/
noncomputable def blackEntryTime (black : ℕ → Prop) (height top : ℕ → ℤ) :
    ℕ → Option ℕ
  | 0 => firstEventFrom black 0
  | r + 1 => (blackEntryTime black height top r).bind fun s =>
      (firstEventFrom (fun t => top s < height t) (s + 1)).bind fun t =>
        firstEventFrom black t

/-- First strict top crossing after an entry, keeping that entry's top fixed. -/
noncomputable def blackExitTime (black : ℕ → Prop) (height top : ℕ → ℤ)
    (r : ℕ) : Option ℕ :=
  (blackEntryTime black height top r).bind fun s =>
    firstEventFrom (fun t => top s < height t) (s + 1)

/-- The next entry search starts at the exit, including a black exit itself. -/
theorem blackEntryTime_succ (black : ℕ → Prop) (height top : ℕ → ℤ) (r : ℕ) :
    blackEntryTime black height top (r + 1) =
      (blackExitTime black height top r).bind (firstEventFrom black) := by
  simp [blackEntryTime, blackExitTime, Option.bind_assoc]

/-- A recorded exit is strictly later than its recorded entry and crosses
the fixed top; all intermediate states remain at or below that same top. -/
theorem blackExitTime_spec (black : ℕ → Prop) (height top : ℕ → ℤ)
    (r s t : ℕ) (hs : blackEntryTime black height top r = some s)
    (ht : blackExitTime black height top r = some t) :
    s < t ∧ top s < height t ∧ ∀ q, s < q → q < t → height q ≤ top s := by
  simp only [blackExitTime, hs, Option.bind_some] at ht
  obtain ⟨hst, htop, hmin⟩ := (firstEventFrom_eq_some_iff _ _ _).mp ht
  refine ⟨by omega, htop, ?_⟩
  intro q hsq hqt
  have hnot := hmin q (by omega) hqt
  omega

/-- A black exit is the next entry at exactly the same time. -/
theorem blackEntryTime_of_black_exit (black : ℕ → Prop) (height top : ℕ → ℤ)
    (r t : ℕ) (ht : blackExitTime black height top r = some t) (hb : black t) :
    blackEntryTime black height top (r + 1) = some t := by
  rw [blackEntryTime_succ, ht, Option.bind_some]
  exact firstEventFrom_of_event black t hb

/-- Every time from the exit up to the next entry is white. -/
theorem blackEntryTime_white_gap (black : ℕ → Prop) (height top : ℕ → ℤ)
    (r t s : ℕ) (ht : blackExitTime black height top r = some t)
    (hs : blackEntryTime black height top (r + 1) = some s) :
    t ≤ s ∧ ∀ q, t ≤ q → q < s → ¬ black q := by
  rw [blackEntryTime_succ, ht, Option.bind_some] at hs
  obtain ⟨hle, _, hgap⟩ := (firstEventFrom_eq_some_iff _ _ _).mp hs
  exact ⟨hle, hgap⟩

/-- If entries cease after an exit, all later times are white. -/
theorem blackEntryTime_none_white_tail (black : ℕ → Prop) (height top : ℕ → ℤ)
    (r t : ℕ) (ht : blackExitTime black height top r = some t)
    (hs : blackEntryTime black height top (r + 1) = none) :
    ∀ q, t ≤ q → ¬ black q := by
  rw [blackEntryTime_succ, ht, Option.bind_some] at hs
  exact (firstEventFrom_eq_none_iff black t).mp hs

/-- Every recorded entry is black. -/
theorem blackEntryTime_is_black (black : ℕ → Prop) (height top : ℕ → ℤ)
    (r s : ℕ) (hs : blackEntryTime black height top r = some s) : black s := by
  cases r with
  | zero => exact ((firstEventFrom_eq_some_iff black 0 s).mp hs).2.1
  | succ r =>
      rw [blackEntryTime_succ] at hs
      obtain ⟨t, _, ht⟩ := Option.bind_eq_some_iff.mp hs
      exact ((firstEventFrom_eq_some_iff black t s).mp ht).2.1

/-- The initial gap before the first entry is white. -/
theorem blackEntryTime_initial_gap (black : ℕ → Prop) (height top : ℕ → ℤ)
    (s : ℕ) (hs : blackEntryTime black height top 0 = some s) :
    ∀ q, q < s → ¬ black q := by
  have hh := ((firstEventFrom_eq_some_iff black 0 s).mp hs).2.2
  exact fun q hq => hh q (Nat.zero_le _) hq

/-- Once no entry remains, all later entry indices also fail. -/
theorem blackEntryTime_none_succ (black : ℕ → Prop) (height top : ℕ → ℤ)
    (r : ℕ) (hr : blackEntryTime black height top r = none) :
    blackEntryTime black height top (r + 1) = none := by
  simp [blackEntryTime, hr]

/-- Consecutive existing entries are strictly increasing, even when an
exit is itself black and therefore the next entry. -/
theorem blackEntryTime_strict_succ (black : ℕ → Prop) (height top : ℕ → ℤ)
    (r s s' : ℕ) (hs : blackEntryTime black height top r = some s)
    (hs' : blackEntryTime black height top (r + 1) = some s') : s < s' := by
  have hnext := hs'
  rw [blackEntryTime_succ] at hnext
  obtain ⟨t, ht, _⟩ := Option.bind_eq_some_iff.mp hnext
  have hst := (blackExitTime_spec black height top r s t hs ht).1
  have hts := (blackEntryTime_white_gap black height top r t s' ht hs').1
  omega

/-- Consecutive existing exits are strictly increasing. -/
theorem blackExitTime_strict_succ (black : ℕ → Prop) (height top : ℕ → ℤ)
    (r t t' : ℕ) (ht : blackExitTime black height top r = some t)
    (ht' : blackExitTime black height top (r + 1) = some t') : t < t' := by
  obtain ⟨s, hs, _⟩ := Option.bind_eq_some_iff.mp ht'
  have hts := (blackEntryTime_white_gap black height top r t s ht hs).1
  have hst := (blackExitTime_spec black height top (r + 1) s t' hs ht').1
  omega

end WordCertDensity.LocalPrimitive
