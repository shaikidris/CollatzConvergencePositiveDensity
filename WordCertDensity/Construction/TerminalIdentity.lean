/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalRecords
import WordCertDensity.Construction.TerminalPayment
import WordCertDensity.Construction.ParametricGraft

/-! # Exact physical terminal mark and its selected-shift payment

At every guarded physical parent, compatibility and the strict offset margin
identify coarse transfer with actual children. The full original record sum
therefore differs from the graft mark by the already paid selected pairing.
-/

namespace WordCertDensity.Construction

open scoped Classical

/-- Coarse terminal transfer equals the physical children of a specified actual graft parent. -/
theorem terminalCoarse_eq_recordChildren {root d : ℕ} {r : GraftRecord}
    (hp : PhysicalHistory (graftRecordWord r) root (graftRecordSource root r))
    (hd : 0 < d) (hy : 16^d ≤ graftRecordSource root r) (u K k : ℕ) :
    terminalCoarse d u K k (graftRecordSource root r) =
      ∑ w ∈ terminalWords d u K,
        if ∃ x, PhysicalHistory w (graftRecordSource root r) x then
          Transfer.weight w * Reference.marker k (terminalRecordSource root (r,w)) else 0 := by
  rw [terminalCoarse, Transfer.coarseSelected]
  conv_rhs => rw [← Finset.sum_attach (terminalWords d u K)]
  apply Finset.sum_congr rfl
  intro w _
  have hq := (terminalConductor_word_guards k w.property).1
  split_ifs with hc
  · obtain ⟨x, hx⟩ := hc
    have hfull : PhysicalHistory (terminalRecordWord (r,w.val)) root x := hp.append hx
    rw [Transfer.wordOperator_of_physical hq hx, Reference.project_natCast,
      terminalRecordSource_eq hfull]
  · have hmax : (16 : ℝ)^d ≤ (graftRecordSource root r : ℝ) := by exact_mod_cast hy
    have hoff : w.val.offset < (graftRecordSource root r : ℚ) := by
      apply Rat.cast_lt (K := ℝ) |>.mp
      simpa only [Rat.cast_natCast] using
        (terminalWord_offset hd ((mem_terminalWords d u K w.val).mp w.property)).2.2.trans_le
          ((pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) ≤ 16) d).trans hmax)
    exact Transfer.wordOperator_eq_zero_of_no_physical w.val hq _ hp.source_odd hoff hc _

/-- Exact physical terminal mass is coarse transfer against the original parent weights. -/
theorem selectedTerminalMark_coarse {L δ X : ℝ} {b t j root d : ℕ}
    (hd : 0 < d) (K k : ℕ)
    (hheight : ∀ r ∈ physicalGraftRecords L δ b t j root,
      16^d ≤ graftRecordSource root r) :
    selectedTerminalMark L δ X b t j root d K k =
      ∑ r ∈ physicalGraftRecords L δ b t j root, Transfer.weight (graftRecordWord r) *
        terminalCoarse d (terminalSelector d (graftRecordSource root r) X) K k
          (graftRecordSource root r) := by
  rw [selectedTerminalMark_children]
  apply Finset.sum_congr rfl
  intro r hr
  rw [terminalCoarse_eq_recordChildren
    ((mem_physicalGraftRecords L δ b t j root r).mp hr).2 hd (hheight r hr)]

/-- The difference of the two actual physical marks is exactly the selected signed pairing. -/
theorem selectedTerminalMark_identity {θ L δ X : ℝ} {b t j root d : ℕ}
    (hd : 0 < d) (K : ℕ)
    (hheight : ∀ r ∈ physicalGraftRecords L δ b t j root,
      16^d ≤ graftRecordSource root r) :
    selectedTerminalMark L δ X b t j root d K
        (parametricLevel θ (macroCount L (graftInitialCount b t) j)) -
      physicalParametricGraftMark θ L δ b t j root =
        terminalSelectedDiscrepancy L δ X b t j root d K
          (parametricLevel θ (macroCount L (graftInitialCount b t) j)) := by
  rw [selectedTerminalMark_coarse hd K _ hheight, physicalParametricGraftMark,
    ← Finset.sum_sub_distrib, terminalSelectedDiscrepancy]
  apply Finset.sum_congr rfl
  intro r _
  rw [terminalVariationTest, Reference.project_natCast, mul_sub]

/-- The literal physical terminal mark pays every selected shift and the full modulus boundary. -/
theorem selectedTerminalMark_payment {θ L δ X : ℝ} {b t j root d : ℕ}
    (hb : 32^5 ≤ b) (hδ : 0 ≤ δ) (hsmall : 2*δ ≤ 1)
    (hpaid : graftOffsetAbsorption b t ≤ 1) (hd : 200 ≤ d)
    (hk : 1 ≤ parametricLevel θ (macroCount L (graftInitialCount b t) j)) (K : ℕ)
    (hshell : ∀ r ∈ physicalGraftRecords L δ b t j root,
      16^d ≤ graftRecordSource root r ∧
        terminalShellLow d (graftRecordSource root r) < X ∧
          X ≤ (2 : ℝ)^(2*terminalRadius d)*terminalShellLow d (graftRecordSource root r)) :
    |selectedTerminalMark L δ X b t j root d K
        (parametricLevel θ (macroCount L (graftInitialCount b t) j)) -
      physicalParametricGraftMark θ L δ b t j root| ≤
        terminalPartitionDebit b t (macroCount L (graftInitialCount b t) j) d K
          (parametricLevel θ (macroCount L (graftInitialCount b t) j)) := by
  rw [selectedTerminalMark_identity (by omega : 0 < d) K (fun r hr => (hshell r hr).1)]
  exact terminalSelectedDiscrepancy_bound hb hδ hsmall hpaid hd hk K
    (fun r hr => (hshell r hr).2)

end WordCertDensity.Construction
