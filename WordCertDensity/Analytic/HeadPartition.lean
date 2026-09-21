/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The finite first-crossing partition argument is adapted from Lech Mazur,
Copyright 2026 Lech Mazur, under Apache License 2.0. The original LICENSE
and NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
This version uses the local gate, exact iid PMF and full manuscript width range.
-/
module

public import WordCertDensity.Analytic.HeadTail
import Mathlib.Tactic.Ring

/-!
# Finite head partition and the rejected original mass

The first-crossing gates are disjoint. At the common cutoff their union
contains every globally typical iid word. Its complement therefore has mass
at most the original probability of typicality failure.
-/

@[expose] public section

namespace WordCertDensity
namespace HeadSlice

/-- The manuscript's finite index set k<n and l<2n. -/
abbrev Index (n : ℕ) := Fin n × Fin (2 * n)

/-- A finite slice index specifies its prefix gate in the actual full word. -/
def indexGate (v : ℝ) (n : ℕ) (i : Index n) (w : ValuationWord) : Prop :=
  gate v n i.1 i.2 w

/-- The union of the permitted first-crossing slices. -/
def unionGate (v : ℝ) (n : ℕ) (w : ValuationWord) : Prop :=
  ∃ i : Index n, indexGate v n i w

/-- Original residue mass of full words not covered by any permitted head slice. -/
noncomputable def rejectedMass (v : ℝ) (n : ℕ) (y : ZMod (3 ^ n)) : ℝ :=
  Gated.mass (Reference.wordPMF n) (fun w => ¬ unionGate v n w)
    (ValuationWord.residueOffset n) y

/-- Failure of the complete contiguous-interval typicality condition under the iid word law. -/
noncomputable def failureProbability (v : ℝ) (n : ℕ) : ℝ :=
  Gated.probability (Reference.wordPMF n) (fun w => ¬ Head.Typical v n w)

/-- A prefix gate records the actual first crossing in the full word. -/
theorem crossing_of_gate {v : ℝ} {n k l : ℕ} {w : ValuationWord}
    (h : gate v n k l w) : Head.Crossing (Head.gateLevel v n) w k := by
  change Head.Gate v n k l (w.take (k + 1)) at h
  have hlen := h.length_eq
  rw [List.length_take] at hlen
  refine ⟨by omega, ?_, h.lt_total⟩
  simpa only [List.take_take, Nat.min_eq_left (Nat.le_succ k)] using h.prefix_le

/-- Two accepted finite slice indices for the same full word must be equal. -/
theorem index_eq {v : ℝ} {n : ℕ} {i j : Index n} {w : ValuationWord}
    (hi : indexGate v n i w) (hj : indexGate v n j w) : i = j := by
  have hk : (i.1 : ℕ) = (j.1 : ℕ) := (crossing_of_gate hi).eq (crossing_of_gate hj)
  have hli := Head.Gate.total_eq hi
  have hlj := Head.Gate.total_eq hj
  have hl : (i.2 : ℕ) = (j.2 : ℕ) := by
    rw [← hli, ← hlj, hk]
  exact Prod.ext (Fin.ext hk) (Fin.ext hl)

/-- Distinct finite slice indices select disjoint original word events. -/
theorem indexGate_disjoint {v : ℝ} {n : ℕ} {i j : Index n} (hij : i ≠ j)
    (w : ValuationWord) : ¬ (indexGate v n i w ∧ indexGate v n j w) := by
  rintro ⟨hi, hj⟩
  exact hij (index_eq hi hj)

/-- Every globally typical full word is covered by the permitted finite slice family. -/
theorem unionGate_of_typical {v : ℝ} {n : ℕ} {w : ValuationWord}
    (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) (hn : 2 ^ 80 ≤ n)
    (hlen : w.length = n) (ht : Head.Typical v n w) : unionGate v n w := by
  obtain ⟨k, ⟨hk, hg⟩, _⟩ := Head.existsUnique_head hv hv' hn hlen ht
  have hl := (hg.ranges hv hv' hn).2.2.2
  exact ⟨(⟨k, hk⟩, ⟨ValuationWord.total (w.take (k + 1)), hl⟩), hg⟩

/-- There are exactly 2n^2 candidate slices, including the empty level-zero index set. -/
theorem card_index (n : ℕ) : Fintype.card (Index n) = 2 * n ^ 2 := by
  simp only [Index, Fintype.card_prod, Fintype.card_fin]
  ring

/-- The union submass is exactly the sum of original selected full-word slice masses. -/
theorem union_mass_eq_sum (v : ℝ) (n : ℕ) (y : ZMod (3 ^ n)) :
    Gated.mass (Reference.wordPMF n) (unionGate v n) (ValuationWord.residueOffset n) y =
      ∑ i : Index n, mass v n i.1 i.2 y := by
  exact Gated.mass_union (Reference.wordPMF n) (indexGate v n)
    (ValuationWord.residueOffset n) (fun _ _ _ hi hj => index_eq hi hj) y

/-- The actual reference residue mass splits into all original slices and a nonnegative remainder. -/
theorem reference_mass_decomposition (v : ℝ) (n : ℕ) (y : ZMod (3 ^ n)) :
    Reference.mass n y = (∑ i : Index n, mass v n i.1 i.2 y) + rejectedMass v n y := by
  have h := Gated.mass_add_compl (Reference.wordPMF n) (unionGate v n)
    (ValuationWord.residueOffset n) y
  rw [union_mass_eq_sum] at h
  exact h.symm

/-- Rejected original residue mass is nonnegative. -/
theorem rejectedMass_nonneg (v : ℝ) (n : ℕ) (y : ZMod (3 ^ n)) :
    0 ≤ rejectedMass v n y := ENNReal.toReal_nonneg

/-- The full rejected mass is exactly the original probability of missing all head gates. -/
theorem rejectedMass_sum (v : ℝ) (n : ℕ) :
    (∑ y, rejectedMass v n y) =
      Gated.probability (Reference.wordPMF n) (fun w => ¬ unionGate v n w) :=
  Gated.mass_sum (Reference.wordPMF n) (fun w => ¬ unionGate v n w)
    (ValuationWord.residueOffset n)

/-- At the common cutoff only globally atypical iid words can contribute rejected mass. -/
theorem rejectedMass_sum_le_failure {v : ℝ} {n : ℕ}
    (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) (hn : 2 ^ 80 ≤ n) :
    (∑ y, rejectedMass v n y) ≤ failureProbability v n := by
  rw [rejectedMass_sum]
  apply Gated.probability_mono_on_support
  intro w hp hbad ht
  have hlen : w.length = n := (Reference.wordPMF_mem_support_iff n w).mp hp
  exact hbad (unionGate_of_typical hv hv' hn hlen ht)

end HeadSlice
end WordCertDensity
