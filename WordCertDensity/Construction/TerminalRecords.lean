/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftRecords
import WordCertDensity.Construction.TerminalSelector
import WordCertDensity.Transfer.Composition

/-! # Actual terminal records with a parent-dependent shift

The original graft record and terminal word are retained as a pair. Filtering
uses the full physical history; its equivalent child test permits exact finite
summation without losing the parent index or normalizing selected weights.
-/

namespace WordCertDensity.Construction

open scoped Classical

/-- Complete original history before terminal compression. -/
def terminalRecordWord (r : GraftRecord × ValuationWord) : ValuationWord :=
  graftRecordWord r.1 ++ r.2

/-- Canonical source of the complete terminal record. -/
def terminalRecordSource (root : ℕ) (r : GraftRecord × ValuationWord) : ℕ :=
  ⌊(terminalRecordWord r).inverseEndpoint root⌋₊

/-- A physical terminal record certifies its canonical source exactly. -/
theorem terminalRecordSource_eq {root x : ℕ} {r : GraftRecord × ValuationWord}
    (hp : PhysicalHistory (terminalRecordWord r) root x) : terminalRecordSource root r = x := by
  rw [terminalRecordSource, hp.inverseEndpoint_eq, Nat.floor_natCast]

/-- Child realization is equivalent to the full physical filter at an actual parent. -/
theorem terminalRecord_physical_iff {root : ℕ} {r : GraftRecord} (w : ValuationWord)
    (hp : PhysicalHistory (graftRecordWord r) root (graftRecordSource root r)) :
    PhysicalHistory (terminalRecordWord (r,w)) root (terminalRecordSource root (r,w)) ↔
      ∃ x, PhysicalHistory w (graftRecordSource root r) x := by
  constructor
  · intro h
    obtain ⟨middle, hpre, hchild⟩ := h.append_split
    exact ⟨_, by simpa only [hpre.source_unique hp] using hchild⟩
  · rintro ⟨x, hx⟩
    have hfull : PhysicalHistory (terminalRecordWord (r,w)) root x := hp.append hx
    simpa only [terminalRecordSource_eq hfull] using hfull

/-- Exactly the literal original terminal family, with its shift chosen by the parent. -/
noncomputable def selectedTerminalRecords (L δ X : ℝ) (b t j root d K : ℕ) :
    Finset (GraftRecord × ValuationWord) :=
  ((physicalGraftRecords L δ b t j root).biUnion fun r =>
    (terminalWords d (terminalSelector d (graftRecordSource root r) X) K).image
      (fun w => (r,w))).filter fun r =>
        PhysicalHistory (terminalRecordWord r) root (terminalRecordSource root r)

/-- Every pair retains its actual parent, its selected word and its physical realization. -/
theorem mem_selectedTerminalRecords (L δ X : ℝ) (b t j root d K : ℕ)
    (r : GraftRecord) (w : ValuationWord) :
    (r,w) ∈ selectedTerminalRecords L δ X b t j root d K ↔
      r ∈ physicalGraftRecords L δ b t j root ∧
        w ∈ terminalWords d (terminalSelector d (graftRecordSource root r) X) K ∧
        PhysicalHistory (terminalRecordWord (r,w)) root (terminalRecordSource root (r,w)) := by
  simp [selectedTerminalRecords, Finset.mem_biUnion, Finset.mem_image, and_assoc]

/-- Summation keeps the original parent/child identity and each full physical filter. -/
theorem selectedTerminalRecords_sum (L δ X : ℝ) (b t j root d K : ℕ)
    (F : GraftRecord × ValuationWord → ℝ) :
    (∑ p ∈ selectedTerminalRecords L δ X b t j root d K, F p) =
      ∑ r ∈ physicalGraftRecords L δ b t j root,
        ∑ w ∈ terminalWords d (terminalSelector d (graftRecordSource root r) X) K,
          if ∃ x, PhysicalHistory w (graftRecordSource root r) x then F (r,w) else 0 := by
  rw [selectedTerminalRecords, Finset.sum_filter, Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro w _
      rw [terminalRecord_physical_iff w
        ((mem_physicalGraftRecords L δ b t j root r).mp hr).2]
    · intro w _ v _ he
      exact congrArg Prod.snd he
  · intro r _ s _ hne
    apply Finset.disjoint_left.mpr
    intro p hp hq
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hp
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hq
    exact hne (congrArg Prod.fst (hw.trans hv.symm))

/-- Actual original terminal mass, marked before overshoot compression. -/
noncomputable def selectedTerminalMark (L δ X : ℝ) (b t j root d K k : ℕ) : ℝ :=
  ∑ r ∈ selectedTerminalRecords L δ X b t j root d K,
    Transfer.weight (terminalRecordWord r) *
      Reference.marker k (terminalRecordSource root r : ZMod (3^k))

/-- Original mass factors once over the physical parent and its selected child. -/
theorem selectedTerminalMark_children (L δ X : ℝ) (b t j root d K k : ℕ) :
    selectedTerminalMark L δ X b t j root d K k =
      ∑ r ∈ physicalGraftRecords L δ b t j root, Transfer.weight (graftRecordWord r) *
        ∑ w ∈ terminalWords d (terminalSelector d (graftRecordSource root r) X) K,
          if ∃ x, PhysicalHistory w (graftRecordSource root r) x then
            Transfer.weight w * Reference.marker k (terminalRecordSource root (r,w)) else 0 := by
  rw [selectedTerminalMark, selectedTerminalRecords_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs
  · rw [terminalRecordWord, Transfer.weight_append, mul_assoc]
  · rw [mul_zero]

end WordCertDensity.Construction
