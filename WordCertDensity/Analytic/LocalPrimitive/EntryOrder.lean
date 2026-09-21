/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.EntryTimes

/-! # Earlier exits at an existing entry -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- An existing next entry supplies its preceding entry and exit, including
the possible equality of the exit with the next entry. -/
theorem blackEntryTime_previous (black : ℕ → Prop) (height top : ℕ → ℤ)
    (r s : ℕ) (hs : blackEntryTime black height top (r + 1) = some s) :
    ∃ a t, blackEntryTime black height top r = some a ∧
      blackExitTime black height top r = some t ∧ a < t ∧ t ≤ s := by
  have hx := hs
  rw [blackEntryTime_succ] at hx
  obtain ⟨t, ht, _⟩ := Option.bind_eq_some_iff.mp hx
  obtain ⟨a, ha, _⟩ := Option.bind_eq_some_iff.mp ht
  exact ⟨a, t, ha, ht, (blackExitTime_spec black height top r a t ha ht).1,
    (blackEntryTime_white_gap black height top r t s ht hs).1⟩

/-- Every earlier numbered exit exists by the time of an existing entry. -/
theorem blackEntryTime_earlier_exit (black : ℕ → Prop) (height top : ℕ → ℤ)
    (r s : ℕ) (hs : blackEntryTime black height top r = some s)
    (i : ℕ) (hi : i < r) :
    ∃ t, blackExitTime black height top i = some t ∧ t ≤ s := by
  induction r generalizing s with
  | zero => omega
  | succ r ih =>
      obtain ⟨a, t, ha, ht, hat, hts⟩ := blackEntryTime_previous black height top r s hs
      by_cases hir : i = r
      · subst i
        exact ⟨t, ht, hts⟩
      · obtain ⟨q, hq, hqa⟩ := ih a ha (by omega)
        exact ⟨q, hq, by omega⟩

end WordCertDensity.LocalPrimitive
