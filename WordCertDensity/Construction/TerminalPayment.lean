/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftCapacity
import WordCertDensity.Construction.TerminalTransfer
import WordCertDensity.Construction.TerminalSelector
import WordCertDensity.Transfer.SelectedPartition

/-! # Actual shift-group terminal payment

The parent-selected discrepancy is paired with restricted physical graft
histograms. Its full debit retains the number of shifts and the finite-modulus
boundary. Identifying this pairing with the extended physical record mark and
proving the eventual vanishing budget are separate consumer obligations.
-/

namespace WordCertDensity.Construction

/-- The finite-modulus point term at the terminal conductor. -/
noncomputable def terminalBoundary (d k B : ℕ) : ℝ :=
  (3 : ℝ)^terminalConductor d k * (1/8 : ℝ)^B

/-- Complete incoming-weighted debit before paying the modulus boundary. -/
noncomputable def terminalPartitionDebit (b t B d K k : ℕ) : ℝ :=
  (2/3 : ℝ) * seedCapacity b t * ((B : ℝ)+1)^2 *
    ((2 : ℝ)^(b+1)+1+terminalBoundary d k B) *
    (2*(terminalRadius d : ℝ)+1) * terminalTransferError d K k

/-- Original parent weights paired with their own selected terminal test. -/
noncomputable def terminalSelectedDiscrepancy (L δ X : ℝ) (b t j root d K k : ℕ) : ℝ :=
  ∑ r ∈ physicalGraftRecords L δ b t j root,
    Transfer.weight (graftRecordWord r) *
      terminalVariationTest d (terminalSelector d (graftRecordSource root r) X) K k
        (graftRecordSource root r : ZMod (3^terminalConductor d k))

/-- Every arbitrary selection of permitted shifts pays the full shift count. -/
theorem physicalGraft_selected_terminal_pairing (H : Finset GraftRecord)
    {L δ : ℝ} {b t j root d k : ℕ} (hb : 32^5 ≤ b)
    (hδ : 0 ≤ δ) (hsmall : 2*δ ≤ 1) (hpaid : graftOffsetAbsorption b t ≤ 1)
    (hH : H ⊆ physicalGraftRecords L δ b t j root)
    (hd : 200 ≤ d) (hk : 1 ≤ k) (K : ℕ) (select : GraftRecord → ℕ)
    (hselect : ∀ r ∈ H, select r ≤ 2*terminalRadius d) :
    |∑ r ∈ H, Transfer.weight (graftRecordWord r) *
      terminalVariationTest d (select r) K k (graftRecordSource root r)| ≤
        terminalPartitionDebit b t (macroCount L (graftInitialCount b t) j) d K k := by
  have hP := (seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t)
  have h := Transfer.history_selected_pairing H (Finset.range (2*terminalRadius d+1))
    select graftRecordWord (graftRecordSource root) (terminalConductor d k)
    (fun u => terminalVariationTest d u K k)
    (B := (seedCapacity b t * ((macroCount L (graftInitialCount b t) j : ℝ)+1)^2) *
      ((2 : ℝ)^(b+1)+1+(3 : ℝ)^terminalConductor d k *
        (1/8 : ℝ)^macroCount L (graftInitialCount b t) j))
    (E := (2/3 : ℝ)*terminalTransferError d K k) (by positivity)
    (fun r hr => Finset.mem_range.mpr (Nat.lt_succ_iff.mpr (hselect r hr)))
    (physicalGraftRecords_capacity H hb hδ hsmall hpaid hH (terminalConductor d k))
    (fun u hu => terminalVariationTest_mean hd
      (Nat.lt_succ_iff.mp (Finset.mem_range.mp hu)) hk K)
  simp only [Finset.card_range, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h
  convert h using 1
  unfold terminalPartitionDebit terminalBoundary
  ring

/-- The actual cutoff-dependent least shift is paid uniformly over every admissible cutoff. -/
theorem terminalSelectedDiscrepancy_bound {L δ X : ℝ} {b t j root d k : ℕ}
    (hb : 32^5 ≤ b) (hδ : 0 ≤ δ) (hsmall : 2*δ ≤ 1)
    (hpaid : graftOffsetAbsorption b t ≤ 1) (hd : 200 ≤ d) (hk : 1 ≤ k) (K : ℕ)
    (hshell : ∀ r ∈ physicalGraftRecords L δ b t j root,
      terminalShellLow d (graftRecordSource root r) < X ∧
        X ≤ (2 : ℝ)^(2*terminalRadius d)*terminalShellLow d (graftRecordSource root r)) :
    |terminalSelectedDiscrepancy L δ X b t j root d K k| ≤
      terminalPartitionDebit b t (macroCount L (graftInitialCount b t) j) d K k := by
  apply physicalGraft_selected_terminal_pairing _ hb hδ hsmall hpaid
    (Finset.Subset.refl _) hd hk K
    (fun r => terminalSelector d (graftRecordSource root r) X)
  intro r hr
  exact (terminalSelector_spec d (graftRecordSource root r) X
    (hshell r hr).1 (hshell r hr).2).2.1

/-- Paying the boundary leaves precisely the fixed offset window plus one. -/
theorem terminalPartitionDebit_paid (b t B d K : ℕ) {k : ℕ} (hk : 1 ≤ k)
    (hboundary : terminalBoundary d k B ≤ 1) :
    terminalPartitionDebit b t B d K k ≤
      (2/3 : ℝ)*seedCapacity b t*((B : ℝ)+1)^2*((2 : ℝ)^(b+1)+2)*
        (2*(terminalRadius d : ℝ)+1)*
        (2*(Analytic.mixingCoefficient : ℝ)/(k : ℝ)^6 +
          2*Real.exp (-(d : ℝ)/64000)+(1/2 : ℝ)^(K+1)) := by
  have hP := (seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t)
  have hnon := terminalTransferError_nonneg d K hk
  have hbound : (2 : ℝ)^(b+1)+1+terminalBoundary d k B ≤ (2 : ℝ)^(b+1)+2 := by
    linarith
  unfold terminalPartitionDebit
  apply mul_le_mul _ (terminalTransferError_order6 d K hk) hnon (by positivity)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hbound (by positivity)) (by positivity)

end WordCertDensity.Construction
