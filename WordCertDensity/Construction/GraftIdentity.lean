/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftMark
import WordCertDensity.Construction.GraftDebit

/-! # The actual physical transition mark and its signed histogram identity

The uniform total-offset margin descends to every actual incoming parent.
Consequently coarse transfer equals precisely the physical child sum, and the
actual change in marked mass is paid by the full incoming-weighted debit.
-/

namespace WordCertDensity.Construction

open scoped Classical

/-- Uniform total-offset absorption gives a strict appended-offset margin at every actual parent. -/
theorem graftAppended_offset_lt_parent {b t root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1)
    {pre : List ValuationWord} (hpre : pre ∈ physicalSeedHistories b t root)
    {L δ : ℝ} {w : ValuationWord} (hw : w ∈ graftTransitionWords δ b t)
    {ws : List ValuationWord} (hws : MacroHistory L δ (graftInitialCount b t) ws) :
    ValuationWord.offset (w ++ ws.flatten) < (seedHistorySource root pre : ℚ) := by
  obtain ⟨hs, hp⟩ := (mem_physicalSeedHistories b t root pre).mp hpre
  obtain ⟨hlen, hblocks⟩ := (mem_seedBlockLists b 0 t pre).mp hs
  have hr : (16 : ℝ) ^ b ≤ (root : ℝ) := by exact_mod_cast hroot
  have hoff := (graftTotal_offset hb hblocks hlen hw hws hpaid).trans
    ((graftOffset_ceiling_lt (by omega : 1 ≤ b)).trans_le hr)
  have ha := congrArg (fun x : ℚ => (x : ℝ)) hp.affine_eq
  norm_num only [Rat.cast_natCast, Rat.cast_add, Rat.cast_mul] at ha
  rw [ValuationWord.offset_append, Rat.cast_add, Rat.cast_mul] at hoff
  have hmul : (ValuationWord.slope pre.flatten : ℝ) *
      (ValuationWord.offset (w ++ ws.flatten) : ℝ) <
      (ValuationWord.slope pre.flatten : ℝ) * (seedHistorySource root pre : ℝ) := by linarith
  have h := (mul_lt_mul_iff_right₀ (Transfer.weight_pos pre.flatten)).mp hmul
  apply Rat.cast_lt (K := ℝ) |>.mp
  simpa only [Rat.cast_natCast] using h

/-- At every actual seed parent, coarse transfer equals all its physical transition children. -/
theorem graftCoarse_eq_children {δ : ℝ} {b t root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1)
    {pre : List ValuationWord} (hpre : pre ∈ physicalSeedHistories b t root) :
    Transfer.coarseSelected (graftTransitionWords δ b t) (2 * seedSize b t)
      (macroLevel (graftInitialCount b t))
      (graftTransitionWords_level (by omega : 256 ^ 2 ≤ b) δ t)
      (seedHistorySource root pre : ZMod (3 ^ (2 * seedSize b t))) =
    ∑ w ∈ graftTransitionWords δ b t,
      if ∃ source, PhysicalHistory w (seedHistorySource root pre) source then
        Transfer.weight w * Reference.marker (macroLevel (graftInitialCount b t))
          (graftRecordSource root (pre, w, []) : ZMod (3 ^ macroLevel (graftInitialCount b t)))
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
theorem physicalGraftMark_coarse (L : ℝ) {δ : ℝ} {b t root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1) :
    physicalGraftMark L δ b t 0 root =
      ∑ pre ∈ physicalSeedHistories b t root, Transfer.weight pre.flatten *
        Transfer.coarseSelected (graftTransitionWords δ b t) (2 * seedSize b t)
          (macroLevel (graftInitialCount b t))
          (graftTransitionWords_level (by omega : 256 ^ 2 ≤ b) δ t)
          (seedHistorySource root pre : ZMod (3 ^ (2 * seedSize b t))) := by
  rw [physicalGraftMark_zero]
  apply Finset.sum_congr rfl
  intro pre hp
  rw [graftCoarse_eq_children hb hroot hpaid hp]

/-- The signed test keeps the transition and incoming markers at their actual levels. -/
noncomputable def graftTransitionTest (δ : ℝ) (b t : ℕ) (hb : 256 ^ 2 ≤ b)
    (y : ZMod (3 ^ (2 * seedSize b t))) : ℝ :=
  Transfer.coarseSelected (graftTransitionWords δ b t) (2 * seedSize b t)
    (macroLevel (graftInitialCount b t)) (graftTransitionWords_level hb δ t) y -
      Reference.marker (seedTailDepth b t) (Reference.project (graftTransition_level_guards hb t).2.1 y)

/-- The actual physical transition loss has exactly the signed incoming-histogram identity. -/
theorem physicalGraftMark_transition_identity (L : ℝ) {δ : ℝ} {b t root : ℕ}
    (hb : 32 ^ 5 ≤ b) (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1) :
    physicalGraftMark L δ b t 0 root - physicalSeedMark b t root =
      ∑ y, Transfer.historyHistogram (physicalSeedHistories b t root) List.flatten
        (seedHistorySource root) (2 * seedSize b t) y *
          graftTransitionTest δ b t (by omega : 256 ^ 2 ≤ b) y := by
  rw [Transfer.historyHistogram_pair_eq, physicalGraftMark_coarse L hb hroot hpaid,
    physicalSeedMark, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro pre _
  rw [graftTransitionTest, Reference.project_natCast, mul_sub]

/-- The original marked mass loses at most the full transition debit, with no extra branch cost. -/
theorem physicalGraftMark_transition_debit (L : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {b t root : ℕ} (hb : 32 ^ 5 ≤ b) (hroot : 16 ^ b ≤ root)
    (hpaid : graftOffsetAbsorption b t ≤ 1) :
    |physicalGraftMark L δ b t 0 root - physicalSeedMark b t root| ≤
      graftTransitionDebit δ b t := by
  rw [physicalGraftMark_transition_identity L hb hroot hpaid]
  calc
    _ ≤ ∑ y, |Transfer.historyHistogram (physicalSeedHistories b t root) List.flatten
        (seedHistorySource root) (2 * seedSize b t) y *
          graftTransitionTest δ b t (by omega : 256 ^ 2 ≤ b) y| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, Transfer.historyHistogram (physicalSeedHistories b t root) List.flatten
        (seedHistorySource root) (2 * seedSize b t) y *
          |graftTransitionTest δ b t (by omega : 256 ^ 2 ≤ b) y| := by
      apply Finset.sum_congr rfl
      intro y _
      rw [abs_mul, abs_of_nonneg (Transfer.historyHistogram_nonneg _ _ _ _ y)]
    _ ≤ _ := physicalSeedHistories_graft_debit _ hδ hb (Finset.Subset.refl _)

/-- The transition supplies the incoming mark minus its complete paid error. -/
theorem physicalGraftMark_zero_lower (L : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {b t root : ℕ} (hb : 32 ^ 5 ≤ b) (hroot : 16 ^ b ≤ root)
    (hpaid : graftOffsetAbsorption b t ≤ 1) :
    physicalSeedMark b t root - graftTransitionDebit δ b t ≤ physicalGraftMark L δ b t 0 root := by
  have h := physicalGraftMark_transition_debit L hδ hb hroot hpaid
  linarith [neg_abs_le (physicalGraftMark L δ b t 0 root - physicalSeedMark b t root)]

end WordCertDensity.Construction
