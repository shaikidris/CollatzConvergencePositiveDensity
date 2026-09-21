/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftCapacity
import WordCertDensity.Construction.MacroPairing

/-! # Complete macro-transfer debit for actual hybrid records

The incoming growth, total corridor tags, composed offset, finite-modulus
boundary and both marker errors remain in the paired discrepancy. The
physical mark increment identity and the uniform varying-splice tail are
separate subsequent consumers of this bound.
-/

namespace WordCertDensity.Construction

open scoped Classical

/-- The full continuation debit at an actual original block count. -/
noncomputable def graftMacroDebit (L δ : ℝ) (b t B : ℕ) : ℝ :=
  (2 / 3 : ℝ) * (seedCapacity b t * ((B : ℝ) + 1) ^ 2) *
    ((2 : ℝ) ^ (b + 1) + 1 + macroBoundary L δ B) * macroError L δ B

/-- The continuation budget is nonnegative at every positive original count. -/
theorem graftMacroDebit_nonneg (L δ : ℝ) (b t : ℕ) {B : ℕ} (hB : 1 ≤ B) :
    0 ≤ graftMacroDebit L δ b t B := by
  have hP := (seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t)
  have he := macroError_nonneg L δ hB
  have hboundary := (macroBoundary_pos L δ B).le
  unfold graftMacroDebit
  positivity

/-- Pair the next stopped macro transfer against any actual retained hybrid subfamily. -/
theorem physicalGraftRecords_macro_debit (H : Finset GraftRecord) {L δ : ℝ}
    {b t j root : ℕ} (hb : 32 ^ 5 ≤ b) (hδ : 0 ≤ δ) (hsmall : 2 * δ ≤ 1)
    (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hH : H ⊆ physicalGraftRecords L δ b t j root)
    (hB : 1 ≤ macroCount L (graftInitialCount b t) j) :
    (∑ a, Transfer.historyHistogram H graftRecordWord (graftRecordSource root)
        (macroConductor L δ (macroCount L (graftInitialCount b t) j)) a *
      |macroVariationTest L δ (macroCount L (graftInitialCount b t) j) hB a|) ≤
      graftMacroDebit L δ b t (macroCount L (graftInitialCount b t) j) := by
  have member r (hr : r ∈ H) :=
    (mem_physicalGraftRecords L δ b t j root r).mp (hH hr)
  apply macro_stopped_variation H graftRecordWord (graftRecordSource root)
    hB (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (b + 1) + 1)
    (fun r hr => (member r hr).2)
    (fun r hr s hs ht he => physicalGraftRecords_source_injective
      (by omega : 0 < b) (hH hr) (hH hs) ht he)
    (fun r hr => graftRecords_weight hb (member r hr).1)
  · intro r hr
    obtain ⟨hlen, hpre, hw, _, hmacro⟩ := (mem_graftRecords L δ b t j r).mp (member r hr).1
    exact ⟨Rat.cast_nonneg.mpr (ValuationWord.offset_nonneg _),
      (graftTotal_offset hb hpre hlen hw hmacro hpaid).le⟩
  · exact graftRecords_tag_card H (by omega : 200 ≤ b) hδ hsmall
      (fun r hr => (member r hr).1)

end WordCertDensity.Construction
