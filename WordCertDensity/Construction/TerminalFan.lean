/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.CompressedRecords
import WordCertDensity.Reference.FanFinite

/-! # Original terminal marks bounded by the actual reduced-record fan -/

namespace WordCertDensity.Construction

open scoped Classical

/-- Original marked mass is exactly the sum over its finite indexed compression image. -/
theorem selectedTerminalMark_compression_image (L δ X : ℝ) (b t j root d K k : ℕ) :
    selectedTerminalMark L δ X b t j root d K k =
      ∑ p ∈ (selectedTerminalRecords L δ X b t j root d K).image (recordCompression X root d),
        Transfer.weight (terminalRecordWord p.1)*(4 : ℝ)^(-(p.2 : ℤ))*
          Reference.marker k (Reference.fanMap k p.2 (terminalRecordSource root p.1)) := by
  rw [Finset.sum_image]
  · unfold selectedTerminalMark
    apply Finset.sum_congr rfl
    intro r hr
    change Transfer.weight (terminalRecordWord r)*Reference.marker k (terminalRecordSource root r) =
      Transfer.weight (terminalRecordWord (compressedRecord X root d r))*
        (4 : ℝ)^(-(recordCompressionIndex X root d r : ℤ))*
          Reference.marker k (Reference.fanMap k (recordCompressionIndex X root d r)
            (terminalRecordSource root (compressedRecord X root d r)))
    rw [compressedRecord_weight hr, compressedRecord_residue hr k]
    ring
  · intro r hr s hs he
    exact recordCompression_injective hr hs he

/-- Nonnegative series enlargement is applied only after the finite image is identified. -/
theorem selectedTerminalMark_fan_le (L δ X : ℝ) (b t j root d K k : ℕ) :
    selectedTerminalMark L δ X b t j root d K k ≤
      ∑ r ∈ selectedTerminalRecords L δ X b t j root d 1,
        Transfer.weight (terminalRecordWord r)*Reference.fan k (terminalRecordSource root r) := by
  rw [selectedTerminalMark_compression_image]
  apply Reference.finiteFanImage_le
    (selectedTerminalRecords L δ X b t j root d 1) k (terminalRecordSource root)
    (fun r => Transfer.weight (terminalRecordWord r))
    ((selectedTerminalRecords L δ X b t j root d K).image (recordCompression X root d))
  · intro r _
    exact (Transfer.weight_pos _).le
  · intro p hp
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hp
    exact (compressedRecord_mem_source hr).1

end WordCertDensity.Construction
