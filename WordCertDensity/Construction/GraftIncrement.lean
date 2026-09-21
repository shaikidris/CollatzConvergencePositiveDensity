/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftExtension
import WordCertDensity.Construction.GraftMacroBound

/-! # Exact physical macro increments and their full debit

The uniform total-offset bound descends to each physical hybrid parent.
Thus the coarse operator counts exactly its physical macro children, and
successive actual marks have the signed histogram identity used by transfer.
-/

namespace WordCertDensity.Construction

open scoped Classical

/-- Every selected final macro word has strict offset margin at its actual physical parent. -/
theorem graftMacro_offset_lt_parent {L δ : ℝ} {b t j root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1)
    {r : GraftRecord} (hr : r ∈ physicalGraftRecords L δ b t j root)
    {w : ValuationWord} (hw : w ∈ macroblocks L δ (macroCount L (graftInitialCount b t) j)) :
    ValuationWord.offset w < (graftRecordSource root r : ℚ) := by
  obtain ⟨hf, hp⟩ := (mem_physicalGraftRecords L δ b t j root r).mp hr
  have hnext := (mem_graftRecords_snoc L δ b t j r w).mpr ⟨hf, hw⟩
  obtain ⟨hlen, hpre, htr, _, hmacro⟩ :=
    (mem_graftRecords L δ b t (j + 1) (graftRecordSnoc r w)).mp hnext
  have hrR : (16 : ℝ) ^ b ≤ (root : ℝ) := by exact_mod_cast hroot
  have hoff := (graftTotal_offset hb hpre hlen htr hmacro hpaid).trans
    ((graftOffset_ceiling_lt (by omega : 1 ≤ b)).trans_le hrR)
  change ((graftRecordWord (graftRecordSnoc r w)).offset : ℝ) < (root : ℝ) at hoff
  rw [graftRecordWord_snoc, ValuationWord.offset_append, Rat.cast_add, Rat.cast_mul] at hoff
  have ha := congrArg (fun x : ℚ => (x : ℝ)) hp.affine_eq
  norm_num only [Rat.cast_natCast, Rat.cast_add, Rat.cast_mul] at ha
  have hmul : (ValuationWord.slope (graftRecordWord r) : ℝ) * (w.offset : ℝ) <
      (ValuationWord.slope (graftRecordWord r) : ℝ) * (graftRecordSource root r : ℝ) := by linarith
  have h := (mul_lt_mul_iff_right₀ (Transfer.weight_pos (graftRecordWord r))).mp hmul
  apply Rat.cast_lt (K := ℝ) |>.mp
  simpa only [Rat.cast_natCast] using h

/-- At an actual hybrid parent, the coarse macro operator equals precisely its physical children. -/
theorem graftMacroCoarse_eq_children {L δ : ℝ} {b t j root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1)
    {r : GraftRecord} (hr : r ∈ physicalGraftRecords L δ b t j root) :
    Transfer.coarseSelected (macroblocks L δ (macroCount L (graftInitialCount b t) j))
      (macroConductor L δ (macroCount L (graftInitialCount b t) j))
      (macroLevel (macroCount L (graftInitialCount b t) (j + 1)))
      (fun _ hw => (macroConductor_word_guards hw).2)
      (graftRecordSource root r :
        ZMod (3 ^ macroConductor L δ (macroCount L (graftInitialCount b t) j))) =
    ∑ w ∈ macroblocks L δ (macroCount L (graftInitialCount b t) j),
      if ∃ source, PhysicalHistory w (graftRecordSource root r) source then
        Transfer.weight w *
          Reference.marker (macroLevel (macroCount L (graftInitialCount b t) (j + 1)))
            (graftRecordSource root (graftRecordSnoc r w) :
              ZMod (3 ^ macroLevel (macroCount L (graftInitialCount b t) (j + 1))))
      else 0 := by
  have hp := (mem_physicalGraftRecords L δ b t j root r).mp hr |>.2
  dsimp only [Transfer.coarseSelected]
  conv_rhs => rw [← Finset.sum_attach (macroblocks L δ (macroCount L (graftInitialCount b t) j))]
  apply Finset.sum_congr rfl
  intro w _
  have hq := (macroConductor_word_guards w.property).1
  split_ifs with hc
  · obtain ⟨source, hc⟩ := hc
    rw [Transfer.wordOperator_of_physical hq hc, Reference.project_natCast,
      graftRecordSource_snoc hp hc]
  · exact Transfer.wordOperator_eq_zero_of_no_physical w.val hq _ hp.source_odd
      (graftMacro_offset_lt_parent hb hroot hpaid hr w.property) hc _

/-- The actual next-stage mark is coarse macro transfer against original physical weights. -/
theorem physicalGraftMark_macro_coarse {L δ : ℝ} {b t j root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1) :
    physicalGraftMark L δ b t (j + 1) root =
      ∑ r ∈ physicalGraftRecords L δ b t j root, Transfer.weight (graftRecordWord r) *
        Transfer.coarseSelected (macroblocks L δ (macroCount L (graftInitialCount b t) j))
          (macroConductor L δ (macroCount L (graftInitialCount b t) j))
          (macroLevel (macroCount L (graftInitialCount b t) (j + 1)))
          (fun _ hw => (macroConductor_word_guards hw).2)
          (graftRecordSource root r :
            ZMod (3 ^ macroConductor L δ (macroCount L (graftInitialCount b t) j))) := by
  rw [physicalGraftMark_snoc]
  apply Finset.sum_congr rfl
  intro r hr
  rw [graftMacroCoarse_eq_children hb hroot hpaid hr]

/-- The change of actual physical marks is the exact signed macro histogram pairing. -/
theorem physicalGraftMark_increment_identity {L δ : ℝ} {b t j root : ℕ}
    (hb : 32 ^ 5 ≤ b) (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hB : 1 ≤ macroCount L (graftInitialCount b t) j) :
    physicalGraftMark L δ b t (j + 1) root - physicalGraftMark L δ b t j root =
      ∑ y, Transfer.historyHistogram (physicalGraftRecords L δ b t j root)
        graftRecordWord (graftRecordSource root)
        (macroConductor L δ (macroCount L (graftInitialCount b t) j)) y *
          macroVariationTest L δ (macroCount L (graftInitialCount b t) j) hB y := by
  rw [Transfer.historyHistogram_pair_eq, physicalGraftMark_macro_coarse hb hroot hpaid,
    physicalGraftMark, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [macroVariationTest, Reference.project_natCast, mul_sub]
  rfl

/-- The full macro debit bounds actual physical mark increments without additional branch loss. -/
theorem physicalGraftMark_increment_debit {L δ : ℝ} {b t j root : ℕ}
    (hb : 32 ^ 5 ≤ b) (hδ : 0 ≤ δ) (hsmall : 2 * δ ≤ 1)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hB : 1 ≤ macroCount L (graftInitialCount b t) j) :
    |physicalGraftMark L δ b t (j + 1) root - physicalGraftMark L δ b t j root| ≤
      graftMacroDebit L δ b t (macroCount L (graftInitialCount b t) j) := by
  rw [physicalGraftMark_increment_identity hb hroot hpaid hB]
  calc
    _ ≤ ∑ y, |Transfer.historyHistogram (physicalGraftRecords L δ b t j root)
        graftRecordWord (graftRecordSource root)
        (macroConductor L δ (macroCount L (graftInitialCount b t) j)) y *
          macroVariationTest L δ (macroCount L (graftInitialCount b t) j) hB y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, Transfer.historyHistogram (physicalGraftRecords L δ b t j root)
        graftRecordWord (graftRecordSource root)
        (macroConductor L δ (macroCount L (graftInitialCount b t) j)) y *
          |macroVariationTest L δ (macroCount L (graftInitialCount b t) j) hB y| := by
      apply Finset.sum_congr rfl
      intro y _
      rw [abs_mul, abs_of_nonneg (Transfer.historyHistogram_nonneg _ _ _ _ y)]
    _ ≤ _ := physicalGraftRecords_macro_debit _ hb hδ hsmall hpaid (Finset.Subset.refl _) hB

/-- The original physical increments satisfy K_var P_t B_j^-4 once the boundary is paid. -/
theorem physicalGraftMark_increment_polynomial {L δ : ℝ} {b t j root : ℕ}
    (hb : 32 ^ 5 ≤ b) (hL : 0 ≤ L) (hδ : 0 < δ) (hsmall : 2 * δ ≤ 1)
    (hpay : 10 ≤ stoppedCorridorRate δ * L)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hB : 1 ≤ macroCount L (graftInitialCount b t) j)
    (hboundary : macroBoundary L δ (macroCount L (graftInitialCount b t) j) ≤ 1) :
    |physicalGraftMark L δ b t (j + 1) root - physicalGraftMark L δ b t j root| ≤
      graftVariationConstant L b * seedCapacity b t /
        (macroCount L (graftInitialCount b t) j : ℝ) ^ 4 :=
  (physicalGraftMark_increment_debit hb hδ.le hsmall hroot hpaid hB).trans
    (graftMacroDebit_polynomial hL hδ hpay b t hB hboundary)

end WordCertDensity.Construction
