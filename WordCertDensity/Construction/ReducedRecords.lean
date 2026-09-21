/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftPrefix
import WordCertDensity.Construction.TerminalRecords
import WordCertDensity.Roots.PoolCharge

/-! # Unique complete terminal records

Record identification holds for every overshoot cap. The actual physical
parent then determines the selected shift without an extra metadata choice.
-/

namespace WordCertDensity.Construction

/-- A complete selected word determines its graft record and terminal suffix. -/
theorem selectedTerminalRecords_word_injective {L δ X : ℝ} {b t j root d K : ℕ}
    (hb : 0 < b) : Set.InjOn terminalRecordWord
      (selectedTerminalRecords L δ X b t j root d K : Set _) := by
  intro r hr s hs he
  obtain ⟨hr, _, _⟩ := (mem_selectedTerminalRecords L δ X b t j root d K r.1 r.2).mp hr
  obtain ⟨hs, _, _⟩ := (mem_selectedTerminalRecords L δ X b t j root d K s.1 s.2).mp hs
  have h := graftRecords_append_injective hb
    ((mem_physicalGraftRecords L δ b t j root r.1).mp hr).1
    ((mem_physicalGraftRecords L δ b t j root s.1).mp hs).1 he
  exact Prod.ext h.1 h.2

/-- The selected record's canonical source is an actual positive odd source. -/
theorem selectedTerminalRecords_physical {L δ X : ℝ} {b t j root d K : ℕ}
    {r : GraftRecord × ValuationWord}
    (hr : r ∈ selectedTerminalRecords L δ X b t j root d K) :
    PhysicalHistory (terminalRecordWord r) root (terminalRecordSource root r) :=
  ((mem_selectedTerminalRecords L δ X b t j root d K r.1 r.2).mp hr).2.2

/-- Equal actual sources in a nonrecurrent pool identify root and complete terminal record. -/
theorem selectedTerminalRecords_pool_unique {L δ X : ℝ} {b t j d K : ℕ}
    {pool : Finset ℕ} (hb : 0 < b)
    (hP : NonrecurrentPool acceleratedStep (pool : Set ℕ))
    {root other : ℕ} (hr : root ∈ pool) (ho : other ∈ pool)
    {r s : GraftRecord × ValuationWord}
    (hrc : r ∈ selectedTerminalRecords L δ X b t j root d K)
    (hsc : s ∈ selectedTerminalRecords L δ X b t j other d K)
    (he : terminalRecordSource root r = terminalRecordSource other s) :
    root = other ∧ r = s := by
  have hp := selectedTerminalRecords_physical hrc
  have hq := selectedTerminalRecords_physical hsc
  rw [← he] at hq
  obtain ⟨hroot, hword⟩ := hp.pool_unique hP hq hr ho
  subst other
  exact ⟨rfl, selectedTerminalRecords_word_injective hb hrc hsc hword⟩

/-- Identifying the parent identifies the deterministic selected shift. -/
theorem terminalRecord_parent_shift_eq {L δ X : ℝ} {b t j root d K : ℕ}
    (hb : 0 < b) {r s : GraftRecord × ValuationWord}
    (hr : r ∈ selectedTerminalRecords L δ X b t j root d K)
    (hs : s ∈ selectedTerminalRecords L δ X b t j root d K)
    (he : terminalRecordWord r = terminalRecordWord s) :
    graftRecordSource root r.1 = graftRecordSource root s.1 ∧
      terminalSelector d (graftRecordSource root r.1) X =
        terminalSelector d (graftRecordSource root s.1) X := by
  have h := selectedTerminalRecords_word_injective hb hr hs he
  subst s
  exact ⟨rfl, rfl⟩

end WordCertDensity.Construction
