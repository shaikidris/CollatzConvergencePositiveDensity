/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.ParametricPairing

/-! # Actual graft marks at parameterized appended levels

The retained physical records are unchanged. Their marker level and the
conductor used to pair the next transfer retain the positive parameter.
The transition and successive-mark identities are subsequent consumers.
-/

namespace WordCertDensity.Construction

/-- Actual physical record sum at the new appended level. -/
noncomputable def physicalParametricGraftMark (θ L δ : ℝ) (b t j root : ℕ) : ℝ :=
  ∑ r ∈ physicalGraftRecords L δ b t j root, Transfer.weight (graftRecordWord r) *
    Reference.marker (parametricLevel θ (macroCount L (graftInitialCount b t) j))
      (graftRecordSource root r :
        ZMod (3 ^ parametricLevel θ (macroCount L (graftInitialCount b t) j)))

/-- Exact specialization recovers the previously built actual physical mark. -/
theorem physicalParametricGraftMark_fixed (L δ : ℝ) (b t j root : ℕ) :
    physicalParametricGraftMark (1 / 1000) L δ b t j root = physicalGraftMark L δ b t j root := by
  exact congrArg (fun k : ℕ =>
    ∑ r ∈ physicalGraftRecords L δ b t j root, Transfer.weight (graftRecordWord r) *
      Reference.marker k (graftRecordSource root r : ZMod (3 ^ k)))
    (parametricLevel_fixed (macroCount L (graftInitialCount b t) j))

/-- Nonnegativity comes from actual contributions, for every parameter and stage. -/
theorem physicalParametricGraftMark_nonneg (θ L δ : ℝ) (b t j root : ℕ) :
    0 ≤ physicalParametricGraftMark θ L δ b t j root := by
  unfold physicalParametricGraftMark
  exact Finset.sum_nonneg fun r _ =>
    mul_nonneg (Transfer.weight_pos _).le (Reference.marker_nonneg _ _)

/-- Any retained physical graft subfamily has the full parameter-dependent macro debit. -/
theorem physicalGraftRecords_parametric_debit (H : Finset GraftRecord) {θ L δ : ℝ}
    {b t j root : ℕ} (hθ : 0 < θ) (hb : 32 ^ 5 ≤ b) (hδ : 0 ≤ δ) (hsmall : 2 * δ ≤ 1)
    (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hH : H ⊆ physicalGraftRecords L δ b t j root)
    (hB : 1 ≤ macroCount L (graftInitialCount b t) j) :
    (∑ a, Transfer.historyHistogram H graftRecordWord (graftRecordSource root)
        (parametricConductor θ L δ (macroCount L (graftInitialCount b t) j)) a *
      |parametricVariationTest θ L δ (macroCount L (graftInitialCount b t) j) hθ hB a|) ≤
      parametricGraftDebit θ L δ b t (macroCount L (graftInitialCount b t) j) := by
  have member r (hr : r ∈ H) :=
    (mem_physicalGraftRecords L δ b t j root r).mp (hH hr)
  apply parametric_stopped_variation H graftRecordWord (graftRecordSource root)
    hθ hB (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ (b + 1) + 1)
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
