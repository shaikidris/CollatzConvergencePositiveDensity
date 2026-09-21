/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.ParametricGraft
import WordCertDensity.Construction.ParametricTransition
import WordCertDensity.Construction.GraftIdentity

/-! # Exact physical initial-transition mark at parameterized levels

Coarse transfer is identified with compatible physical children using the
proved strict offset margin. The signed seed-histogram identity then pays
the full original incoming-weighted debit, with both marker levels retained.
This module uses the baseline true-mean corridor families.
-/

namespace WordCertDensity.Construction

open scoped Classical

/-- The initial hybrid mark is the original weighted sum over physical transition children. -/
theorem physicalParametricGraftMark_zero (θ L δ : ℝ) (b t root : ℕ) :
    physicalParametricGraftMark θ L δ b t 0 root =
      ∑ pre ∈ physicalSeedHistories b t root, Transfer.weight pre.flatten *
        ∑ w ∈ graftTransitionWords δ b t,
          if ∃ source, PhysicalHistory w (seedHistorySource root pre) source then
            Transfer.weight w * Reference.marker (parametricLevel θ (graftInitialCount b t))
              (graftRecordSource root (pre, w, []) : ZMod (3 ^ parametricLevel θ
                (graftInitialCount b t)))
          else 0 := by
  rw [physicalParametricGraftMark, physicalGraftRecords_sum_zero]
  apply Finset.sum_congr rfl
  intro pre _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs
  · rw [graftRecordWeight_zero, mul_assoc]
    rfl
  · rw [mul_zero]

/-- At every actual seed parent, coarse transfer equals all its physical transition children. -/
theorem parametricTransitionCoarse_eq_children {θ δ : ℝ} {b t root : ℕ} (hθcap : θ ≤ 1 / 1000)
    (hb : 32 ^ 5 ≤ b)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1)
    {pre : List ValuationWord} (hpre : pre ∈ physicalSeedHistories b t root) :
    Transfer.coarseSelected (graftTransitionWords δ b t) (2 * seedSize b t)
      (parametricLevel θ (graftInitialCount b t))
      (parametricTransitionWords_level hθcap (by omega : 256 ^ 2 ≤ b) δ t)
      (seedHistorySource root pre : ZMod (3 ^ (2 * seedSize b t))) =
    ∑ w ∈ graftTransitionWords δ b t,
      if ∃ source, PhysicalHistory w (seedHistorySource root pre) source then
        Transfer.weight w * Reference.marker (parametricLevel θ (graftInitialCount b t))
          (graftRecordSource root (pre, w, []) : ZMod (3 ^ parametricLevel θ (graftInitialCount
            b t)))
      else 0 := by
  have hp := (mem_physicalSeedHistories b t root pre).mp hpre |>.2
  rw [Transfer.coarseSelected]
  conv_rhs => rw [← Finset.sum_attach (graftTransitionWords δ b t)]
  apply Finset.sum_congr rfl
  intro w _
  have hq : w.val.length ≤ 2 * seedSize b t := by
    have hd := graftTransitionWords_depth w.property
    omega
  split_ifs with hc
  · obtain ⟨source, hc⟩ := hc
    rw [Transfer.wordOperator_of_physical hq hc, Reference.project_natCast,
      graftRecordSource_zero hp hc]
  · have hoff := graftAppended_offset_lt_parent hb hroot hpaid hpre w.property
      (L := 0) (ws := []) (show MacroHistory 0 δ (graftInitialCount b t) [] from trivial)
    simp only [List.flatten_nil, List.append_nil] at hoff
    exact Transfer.wordOperator_eq_zero_of_no_physical w.val hq _ hp.source_odd hoff hc _

/-- The physical transition-stage mark equals coarse transfer against original incoming weights. -/
theorem physicalParametricGraftMark_coarse (L : ℝ) {θ δ : ℝ} {b t root : ℕ} (hθcap : θ ≤ 1 /
    1000) (hb : 32 ^ 5 ≤ b)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1) :
    physicalParametricGraftMark θ L δ b t 0 root =
      ∑ pre ∈ physicalSeedHistories b t root, Transfer.weight pre.flatten *
        Transfer.coarseSelected (graftTransitionWords δ b t) (2 * seedSize b t)
          (parametricLevel θ (graftInitialCount b t))
          (parametricTransitionWords_level hθcap (by omega : 256 ^ 2 ≤ b) δ t)
          (seedHistorySource root pre : ZMod (3 ^ (2 * seedSize b t))) := by
  rw [physicalParametricGraftMark_zero]
  apply Finset.sum_congr rfl
  intro pre hp
  rw [parametricTransitionCoarse_eq_children hθcap hb hroot hpaid hp]

/-- The signed test keeps the transition and incoming markers at their actual levels. -/
noncomputable def parametricTransitionTest (θ δ : ℝ) (b t : ℕ) (hθcap : θ ≤ 1 / 1000) (hb : 256
    ^ 2 ≤ b)
    (y : ZMod (3 ^ (2 * seedSize b t))) : ℝ :=
  Transfer.coarseSelected (graftTransitionWords δ b t) (2 * seedSize b t)
    (parametricLevel θ (graftInitialCount b t)) (parametricTransitionWords_level hθcap hb δ t) y -
      Reference.marker (seedTailDepth b t) (Reference.project (graftTransition_level_guards hb
        t).2.1 y)

/-- The actual physical transition loss has exactly the signed incoming-histogram identity. -/
theorem physicalParametricGraftMark_transition_identity (L : ℝ) {θ δ : ℝ} {b t root : ℕ}
    (hθcap : θ ≤ 1 / 1000) (hb : 32 ^ 5 ≤ b) (hroot : 16 ^ b ≤ root) (hpaid :
      graftOffsetAbsorption b t ≤ 1) :
    physicalParametricGraftMark θ L δ b t 0 root - physicalSeedMark b t root =
      ∑ y, Transfer.historyHistogram (physicalSeedHistories b t root) List.flatten
        (seedHistorySource root) (2 * seedSize b t) y *
          parametricTransitionTest θ δ b t hθcap (by omega : 256 ^ 2 ≤ b) y := by
  rw [Transfer.historyHistogram_pair_eq, physicalParametricGraftMark_coarse L hθcap hb hroot hpaid,
    physicalSeedMark, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro pre _
  rw [parametricTransitionTest, Reference.project_natCast, mul_sub]

/-- The original marked mass loses at most the full transition debit, with no extra branch cost. -/
theorem physicalParametricGraftMark_transition_debit (L : ℝ) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ)
    {b t root : ℕ} (hθcap : θ ≤ 1 / 1000) (hb : 32 ^ 5 ≤ b) (hroot : 16 ^ b ≤ root)
    (hpaid : graftOffsetAbsorption b t ≤ 1) :
    |physicalParametricGraftMark θ L δ b t 0 root - physicalSeedMark b t root| ≤
      parametricTransitionDebit θ δ b t := by
  rw [physicalParametricGraftMark_transition_identity L hθcap hb hroot hpaid]
  calc
    _ ≤ ∑ y, |Transfer.historyHistogram (physicalSeedHistories b t root) List.flatten
        (seedHistorySource root) (2 * seedSize b t) y *
          parametricTransitionTest θ δ b t hθcap (by omega : 256 ^ 2 ≤ b) y| :=
            Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, Transfer.historyHistogram (physicalSeedHistories b t root) List.flatten
        (seedHistorySource root) (2 * seedSize b t) y *
          |parametricTransitionTest θ δ b t hθcap (by omega : 256 ^ 2 ≤ b) y| := by
      apply Finset.sum_congr rfl
      intro y _
      rw [abs_mul, abs_of_nonneg (Transfer.historyHistogram_nonneg _ _ _ _ y)]
    _ ≤ _ := physicalSeedHistories_parametric_debit _ hθ hθcap hδ hb (Finset.Subset.refl _)

/-- The transition supplies the incoming mark minus its complete paid error. -/
theorem physicalParametricGraftMark_zero_lower (L : ℝ) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ)
    {b t root : ℕ} (hθcap : θ ≤ 1 / 1000) (hb : 32 ^ 5 ≤ b) (hroot : 16 ^ b ≤ root)
    (hpaid : graftOffsetAbsorption b t ≤ 1) :
    physicalSeedMark b t root - parametricTransitionDebit θ δ b t ≤ physicalParametricGraftMark
      θ L δ b t 0 root := by
  have h := physicalParametricGraftMark_transition_debit L hθ hδ hθcap hb hroot hpaid
  linarith [neg_abs_le (physicalParametricGraftMark θ L δ b t 0 root - physicalSeedMark b t root)]

end WordCertDensity.Construction
