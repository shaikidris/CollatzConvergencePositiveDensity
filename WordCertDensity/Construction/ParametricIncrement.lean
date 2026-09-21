/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.ParametricGraft
import WordCertDensity.Construction.GraftIncrement

/-! # Exact successive physical marks at parameterized marker levels

The actual parent/child decomposition keeps its original weights, offset
margin and boundary term. Only appended marker levels vary with theta.
The retained families here use the baseline true-mean corridor; the revised
inner-selector migration is a separate construction obligation.
-/

namespace WordCertDensity.Construction

open scoped Classical

/-- The next actual mark is the original weighted sum of its physical macro children. -/
theorem physicalParametricGraftMark_snoc (θ L δ : ℝ) (b t j root : ℕ) :
    physicalParametricGraftMark θ L δ b t (j + 1) root =
      ∑ r ∈ physicalGraftRecords L δ b t j root, Transfer.weight (graftRecordWord r) *
        ∑ w ∈ macroblocks L δ (macroCount L (graftInitialCount b t) j),
          if ∃ source, PhysicalHistory w (graftRecordSource root r) source then
            Transfer.weight w *
              Reference.marker (parametricLevel θ (macroCount L (graftInitialCount b t) (j + 1)))
                (graftRecordSource root (graftRecordSnoc r w) :
                  ZMod (3 ^ parametricLevel θ (macroCount L (graftInitialCount b t) (j + 1))))
          else 0 := by
  rw [physicalParametricGraftMark, physicalGraftRecords_sum_snoc]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs
  · rw [graftRecordWeight_snoc, mul_assoc]
  · rw [mul_zero]

/-- At an actual hybrid parent, the coarse macro operator equals precisely its physical children. -/
theorem parametricGraftMacroCoarse_eq_children {θ L δ : ℝ} {b t j root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1)
    {r : GraftRecord} (hr : r ∈ physicalGraftRecords L δ b t j root) :
    Transfer.coarseSelected (macroblocks L δ (macroCount L (graftInitialCount b t) j))
      (parametricConductor θ L δ (macroCount L (graftInitialCount b t) j))
      (parametricLevel θ (macroCount L (graftInitialCount b t) (j + 1)))
      (fun _ hw => (parametricConductor_word_guards θ hw).2)
      (graftRecordSource root r :
        ZMod (3 ^ parametricConductor θ L δ (macroCount L (graftInitialCount b t) j))) =
    ∑ w ∈ macroblocks L δ (macroCount L (graftInitialCount b t) j),
      if ∃ source, PhysicalHistory w (graftRecordSource root r) source then
        Transfer.weight w *
          Reference.marker (parametricLevel θ (macroCount L (graftInitialCount b t) (j + 1)))
            (graftRecordSource root (graftRecordSnoc r w) :
              ZMod (3 ^ parametricLevel θ (macroCount L (graftInitialCount b t) (j + 1))))
      else 0 := by
  have hp := (mem_physicalGraftRecords L δ b t j root r).mp hr |>.2
  dsimp only [Transfer.coarseSelected]
  conv_rhs => rw [← Finset.sum_attach (macroblocks L δ (macroCount L (graftInitialCount b t) j))]
  apply Finset.sum_congr rfl
  intro w _
  have hq := (parametricConductor_word_guards θ w.property).1
  split_ifs with hc
  · obtain ⟨source, hc⟩ := hc
    rw [Transfer.wordOperator_of_physical hq hc, Reference.project_natCast,
      graftRecordSource_snoc hp hc]
  · exact Transfer.wordOperator_eq_zero_of_no_physical w.val hq _ hp.source_odd
      (graftMacro_offset_lt_parent hb hroot hpaid hr w.property) hc _

/-- The actual next-stage mark is coarse macro transfer against original physical weights. -/
theorem physicalParametricGraftMark_macro_coarse {θ L δ : ℝ} {b t j root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1) :
    physicalParametricGraftMark θ L δ b t (j + 1) root =
      ∑ r ∈ physicalGraftRecords L δ b t j root, Transfer.weight (graftRecordWord r) *
        Transfer.coarseSelected (macroblocks L δ (macroCount L (graftInitialCount b t) j))
          (parametricConductor θ L δ (macroCount L (graftInitialCount b t) j))
          (parametricLevel θ (macroCount L (graftInitialCount b t) (j + 1)))
          (fun _ hw => (parametricConductor_word_guards θ hw).2)
          (graftRecordSource root r :
            ZMod (3 ^ parametricConductor θ L δ (macroCount L (graftInitialCount b t) j))) := by
  rw [physicalParametricGraftMark_snoc]
  apply Finset.sum_congr rfl
  intro r hr
  rw [parametricGraftMacroCoarse_eq_children hb hroot hpaid hr]

/-- The change of actual physical marks is the exact signed macro histogram pairing. -/
theorem physicalParametricGraftMark_increment_identity {θ L δ : ℝ} {b t j root : ℕ}
    (hθ : 0 < θ) (hb : 32 ^ 5 ≤ b) (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hB : 1 ≤ macroCount L (graftInitialCount b t) j) :
    physicalParametricGraftMark θ L δ b t (j + 1) root - physicalParametricGraftMark θ L δ b t j
      root =
      ∑ y, Transfer.historyHistogram (physicalGraftRecords L δ b t j root)
        graftRecordWord (graftRecordSource root)
        (parametricConductor θ L δ (macroCount L (graftInitialCount b t) j)) y *
          parametricVariationTest θ L δ (macroCount L (graftInitialCount b t) j) hθ hB y := by
  rw [Transfer.historyHistogram_pair_eq, physicalParametricGraftMark_macro_coarse hb hroot hpaid,
    physicalParametricGraftMark, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r _
  rw [parametricVariationTest, Reference.project_natCast, mul_sub]
  rfl

/-- The full macro debit bounds actual physical mark increments without additional branch loss. -/
theorem physicalParametricGraftMark_increment_debit {θ L δ : ℝ} {b t j root : ℕ}
    (hθ : 0 < θ) (hb : 32 ^ 5 ≤ b) (hδ : 0 ≤ δ) (hsmall : 2 * δ ≤ 1)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hB : 1 ≤ macroCount L (graftInitialCount b t) j) :
    |physicalParametricGraftMark θ L δ b t (j + 1) root - physicalParametricGraftMark θ L δ b t
      j root| ≤
      parametricGraftDebit θ L δ b t (macroCount L (graftInitialCount b t) j) := by
  rw [physicalParametricGraftMark_increment_identity hθ hb hroot hpaid hB]
  calc
    _ ≤ ∑ y, |Transfer.historyHistogram (physicalGraftRecords L δ b t j root)
        graftRecordWord (graftRecordSource root)
        (parametricConductor θ L δ (macroCount L (graftInitialCount b t) j)) y *
          parametricVariationTest θ L δ (macroCount L (graftInitialCount b t) j) hθ hB y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ y, Transfer.historyHistogram (physicalGraftRecords L δ b t j root)
        graftRecordWord (graftRecordSource root)
        (parametricConductor θ L δ (macroCount L (graftInitialCount b t) j)) y *
          |parametricVariationTest θ L δ (macroCount L (graftInitialCount b t) j) hθ hB y| := by
      apply Finset.sum_congr rfl
      intro y _
      rw [abs_mul, abs_of_nonneg (Transfer.historyHistogram_nonneg _ _ _ _ y)]
    _ ≤ _ := physicalGraftRecords_parametric_debit _ hθ hb hδ hsmall hpaid (Finset.Subset.refl _) hB

/-- The original physical increments satisfy K_var P_t B_j^-4 once the boundary is paid. -/
theorem physicalParametricGraftMark_increment_polynomial {θ L δ : ℝ} {b t j root : ℕ}
    (hθ : 0 < θ) (hb : 32 ^ 5 ≤ b) (hL : 0 ≤ L) (hδ : 0 < δ) (hsmall : 2 * δ ≤ 1)
    (hpay : 10 ≤ stoppedCorridorRate δ * L)
    (hroot : 16 ^ b ≤ root) (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hB : 1 ≤ macroCount L (graftInitialCount b t) j)
    (hboundary : parametricBoundary θ L δ (macroCount L (graftInitialCount b t) j) ≤ 1) :
    |physicalParametricGraftMark θ L δ b t (j + 1) root - physicalParametricGraftMark θ L δ b t
      j root| ≤
      parametricGraftVariationConstant θ L b * seedCapacity b t /
        (macroCount L (graftInitialCount b t) j : ℝ) ^ 4 :=
  (physicalParametricGraftMark_increment_debit hθ hb hδ.le hsmall hroot hpaid hB).trans
    (parametricGraftDebit_polynomial hθ hL hδ hpay b t hB hboundary)

end WordCertDensity.Construction
