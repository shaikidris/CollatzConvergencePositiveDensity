/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalFan
import WordCertDensity.Construction.ReducedCharge

/-! # Grouping the actual reduced fan mass by physical source

All root and record sums are retained. Grouping is an exact finite identity;
the original selected terminal marks are the left side of the resulting bound.
-/

namespace WordCertDensity.Construction

open scoped Classical

/-- Exactly the physical sources of the complete reduced-record family. -/
noncomputable def reducedSourceSet (L δ X : ℝ) (b t j d : ℕ) (pool : Finset ℕ) : Finset ℕ :=
  pool.biUnion fun root =>
    (selectedTerminalRecords L δ X b t j root d 1).image (terminalRecordSource root)

/-- An actual reduced record contributes its source to the pooled source set. -/
theorem mem_reducedSourceSet {L δ X : ℝ} {b t j d : ℕ} {pool : Finset ℕ}
    {root : ℕ} (hr : root ∈ pool) {r : GraftRecord × ValuationWord}
    (hrec : r ∈ selectedTerminalRecords L δ X b t j root d 1) :
    terminalRecordSource root r ∈ reducedSourceSet L δ X b t j d pool := by
  exact Finset.mem_biUnion.mpr ⟨root, hr, Finset.mem_image_of_mem _ hrec⟩

/-- Grouping one root's actual normalized records is an exact finite identity. -/
theorem reducedRoot_group (L δ X : ℝ) (b t j d : ℕ) (pool : Finset ℕ)
    (F : ℕ → ℝ) {root : ℕ} (hr : root ∈ pool) :
    (∑ r ∈ selectedTerminalRecords L δ X b t j root d 1,
      Transfer.weight (terminalRecordWord r)*F (terminalRecordSource root r)) / root =
      ∑ x ∈ reducedSourceSet L δ X b t j d pool,
        ((∑ r ∈ (selectedTerminalRecords L δ X b t j root d 1).filter
          (fun r => terminalRecordSource root r = x), Transfer.weight (terminalRecordWord r)) /
            root)*F x := by
  have hmaps : ∀ r ∈ selectedTerminalRecords L δ X b t j root d 1,
      terminalRecordSource root r ∈ reducedSourceSet L δ X b t j d pool :=
    fun r hrec => mem_reducedSourceSet hr hrec
  have h := Finset.sum_fiberwise_of_maps_to hmaps
    (fun r => Transfer.weight (terminalRecordWord r)/(root : ℝ)*F (terminalRecordSource root r))
  calc
    _ = ∑ r ∈ selectedTerminalRecords L δ X b t j root d 1,
        Transfer.weight (terminalRecordWord r)/(root : ℝ)*F (terminalRecordSource root r) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = _ := by
      rw [← h]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      rw [(Finset.mem_filter.mp hr).2]

/-- Summing roots and then sources yields the literal pooled charge, without multiplicity loss. -/
theorem reducedFan_group (L δ X : ℝ) (b t j d : ℕ) (pool : Finset ℕ) (F : ℕ → ℝ) :
    (∑ root ∈ pool, (∑ r ∈ selectedTerminalRecords L δ X b t j root d 1,
      Transfer.weight (terminalRecordWord r)*F (terminalRecordSource root r))/root) =
      ∑ x ∈ reducedSourceSet L δ X b t j d pool, reducedSourceCharge L δ X b t j d x pool*F x := by
  calc
    _ = ∑ root ∈ pool, ∑ x ∈ reducedSourceSet L δ X b t j d pool,
        ((∑ r ∈ (selectedTerminalRecords L δ X b t j root d 1).filter
          (fun r => terminalRecordSource root r = x), Transfer.weight (terminalRecordWord r))/root)*F x :=
      Finset.sum_congr rfl (fun root hr => reducedRoot_group L δ X b t j d pool F hr)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [reducedSourceCharge, Finset.sum_mul]

/-- Actual original terminal marks are bounded by their reduced-source fan charge. -/
theorem selectedTerminalFanCharge (L δ X : ℝ) (b t j d K k : ℕ) (pool : Finset ℕ) :
    (∑ root ∈ pool, selectedTerminalMark L δ X b t j root d K k/root) ≤
      ∑ x ∈ reducedSourceSet L δ X b t j d pool,
        reducedSourceCharge L δ X b t j d x pool*Reference.fan k (x : ZMod (3^k)) := by
  calc
    _ ≤ ∑ root ∈ pool, (∑ r ∈ selectedTerminalRecords L δ X b t j root d 1,
        Transfer.weight (terminalRecordWord r)*Reference.fan k (terminalRecordSource root r))/root :=
      Finset.sum_le_sum fun root _ => div_le_div_of_nonneg_right
        (selectedTerminalMark_fan_le L δ X b t j root d K k) (Nat.cast_nonneg root)
    _ = _ := reducedFan_group L δ X b t j d pool (fun x => Reference.fan k (x : ZMod (3^k)))

end WordCertDensity.Construction
