/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.Compression
import WordCertDensity.Construction.ReducedRecords
import WordCertDensity.Reference.FanMap

/-! # Actual selected records under indexed compression

Compression retains the original graft and thus its physical parent and
selected shift. Only the final valuation of the terminal suffix changes.
-/

namespace WordCertDensity.Construction

/-- The quotient index selected by this record's own physical parent. -/
noncomputable def recordCompressionIndex (X : ℝ) (root d : ℕ)
    (r : GraftRecord × ValuationWord) : ℕ :=
  compressionIndex d (terminalSelector d (graftRecordSource root r.1) X) r.2

/-- The complete reduced record keeps its original graft. -/
noncomputable def compressedRecord (X : ℝ) (root d : ℕ)
    (r : GraftRecord × ValuationWord) : GraftRecord × ValuationWord :=
  (r.1, compressWord r.2 (recordCompressionIndex X root d r))

/-- Compression retains the index until the finite-image sum is formed. -/
noncomputable def recordCompression (X : ℝ) (root d : ℕ)
    (r : GraftRecord × ValuationWord) : (GraftRecord × ValuationWord) × ℕ :=
  (compressedRecord X root d r, recordCompressionIndex X root d r)

/-- A selected record supplies its actual physical terminal suffix at the original parent. -/
theorem selectedTerminalRecords_child {L δ X : ℝ} {b t j root d K : ℕ}
    {r : GraftRecord × ValuationWord}
    (hr : r ∈ selectedTerminalRecords L δ X b t j root d K) :
    PhysicalHistory r.2 (graftRecordSource root r.1) (terminalRecordSource root r) := by
  obtain ⟨hgr, _, hp⟩ := (mem_selectedTerminalRecords L δ X b t j root d K r.1 r.2).mp hr
  have hpre := ((mem_physicalGraftRecords L δ b t j root r.1).mp hgr).2
  obtain ⟨y, hy, hc⟩ := hp.append_split
  simpa only [hy.source_unique hpre] using hc

/-- Compression creates an actual reduced record and the exact original source. -/
theorem compressedRecord_mem_source {L δ X : ℝ} {b t j root d K : ℕ}
    {r : GraftRecord × ValuationWord}
    (hr : r ∈ selectedTerminalRecords L δ X b t j root d K) :
    compressedRecord X root d r ∈ selectedTerminalRecords L δ X b t j root d 1 ∧
      terminalRecordSource root r = fanSource (recordCompressionIndex X root d r)
        (terminalRecordSource root (compressedRecord X root d r)) := by
  obtain ⟨hgr, hw, _⟩ := (mem_selectedTerminalRecords L δ X b t j root d K r.1 r.2).mp hr
  have ht := (mem_terminalWords _ _ _ _).mp hw
  have hpre := ((mem_physicalGraftRecords L δ b t j root r.1).mp hgr).2
  obtain ⟨z, hz, hx⟩ := compressWord_physical ht (selectedTerminalRecords_child hr)
  have hfull : PhysicalHistory (terminalRecordWord (compressedRecord X root d r)) root z :=
    hpre.append hz
  have he := terminalRecordSource_eq hfull
  constructor
  · apply (mem_selectedTerminalRecords L δ X b t j root d 1 _ _).mpr
    refine ⟨hgr, (mem_terminalWords _ _ _ _).mpr (compressWord_terminal ht), ?_⟩
    change PhysicalHistory (terminalRecordWord (compressedRecord X root d r)) root
      (terminalRecordSource root (compressedRecord X root d r))
    rw [he]
    exact hfull
  · rw [he]
    simpa only [recordCompressionIndex] using hx

/-- The complete physical record weight retains the exact four-power factor. -/
theorem compressedRecord_weight {L δ X : ℝ} {b t j root d K : ℕ}
    {r : GraftRecord × ValuationWord}
    (hr : r ∈ selectedTerminalRecords L δ X b t j root d K) :
    Transfer.weight (terminalRecordWord r) =
      (4 : ℝ)^(-(recordCompressionIndex X root d r : ℤ))*
        Transfer.weight (terminalRecordWord (compressedRecord X root d r)) := by
  have ht := (mem_terminalWords _ _ _ _).mp
    ((mem_selectedTerminalRecords L δ X b t j root d K r.1 r.2).mp hr).2.1
  have h := compression_physical_weight ht
  change Transfer.weight (graftRecordWord r.1 ++ r.2) =
    (4 : ℝ)^(-(recordCompressionIndex X root d r : ℤ))*
      Transfer.weight (graftRecordWord r.1 ++ compressWord r.2 (recordCompressionIndex X root d r))
  rw [Transfer.weight_append, Transfer.weight_append, h]
  unfold recordCompressionIndex
  ring

/-- The original residue is the fan image of its actual reduced source. -/
theorem compressedRecord_residue {L δ X : ℝ} {b t j root d K : ℕ}
    {r : GraftRecord × ValuationWord}
    (hr : r ∈ selectedTerminalRecords L δ X b t j root d K) (k : ℕ) :
    (terminalRecordSource root r : ZMod (3^k)) =
      Reference.fanMap k (recordCompressionIndex X root d r)
        (terminalRecordSource root (compressedRecord X root d r) : ZMod (3^k)) := by
  rw [(compressedRecord_mem_source hr).2, fanSource_eq]
  exact (Reference.fanMap_natCast _ _ _).symm

/-- Distinct original records remain distinct when the compression index is retained. -/
theorem recordCompression_injective {L δ X : ℝ} {b t j root d K : ℕ} :
    Set.InjOn (recordCompression X root d)
      (selectedTerminalRecords L δ X b t j root d K : Set _) := by
  intro r hr s hs he
  have hparent : r.1 = s.1 := congrArg (fun p => p.1.1) he
  have hpair := congrArg (fun p => (p.1.2, p.2)) he
  rcases r with ⟨pre,w⟩
  rcases s with ⟨other,v⟩
  dsimp only at hparent
  subst other
  have hw := (mem_terminalWords _ _ _ _).mp
    ((mem_selectedTerminalRecords L δ X b t j root d K pre w).mp hr).2.1
  have hv := (mem_terminalWords _ _ _ _).mp
    ((mem_selectedTerminalRecords L δ X b t j root d K pre v).mp hs).2.1
  exact Prod.ext rfl (compression_injective hw hv hpair)

end WordCertDensity.Construction
