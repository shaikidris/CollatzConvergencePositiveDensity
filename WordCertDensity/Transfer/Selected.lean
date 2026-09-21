/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Transfer.Prefix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Selected reference density and exact stopping deficit

Finite prefix-free families retain their original probability. Both the
full-tail transfer and its coarse replacement have mean (2/3)p(V).
-/

@[expose] public section

namespace WordCertDensity.Transfer

/-- The selected density A(V,q), using each word's full remaining reference tail. -/
noncomputable def selected (V : Finset ValuationWord) (q : ℕ) (y : ZMod (3 ^ q)) : ℝ :=
  ∑ w ∈ V, wordOperator w q (Reference.marker (q - w.length)) y

/-- The coarse density L(V,q,k); each word has at least k remaining digits. -/
noncomputable def coarseSelected (V : Finset ValuationWord) (q k : ℕ)
    (hk : ∀ w ∈ V, k ≤ q - w.length) (y : ZMod (3 ^ q)) : ℝ :=
  ∑ w : V, wordOperator w q
    (fun z => Reference.marker k (Reference.project (hk w w.property) z)) y

private theorem mean_finset_sum {α : Type*} (q : ℕ) (s : Finset α)
    (f : α → ZMod (3 ^ q) → ℝ) :
    Reference.mean q (fun y => ∑ i ∈ s, f i y) = ∑ i ∈ s, Reference.mean q (f i) := by
  simp only [Reference.mean]
  rw [Finset.sum_comm, Finset.sum_div]

/-- Prefix exclusion identifies the affine sum with the original selected residue submass. -/
theorem selected_eq_gated (V : Finset ValuationWord) {q : ℕ}
    (hlen : ∀ w ∈ V, w.length ≤ q)
    (hfree : (V : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v))
    (y : ZMod (3 ^ q)) :
    selected V q y = ((2 / 3 : ℝ) * (3 : ℝ) ^ q) *
      Gated.mass (Reference.wordPMF q) (Reference.prefixFamilyEvent V)
        (ValuationWord.residueOffset q) y := by
  classical
  have hu (i j : V) (a : ValuationWord) (hi : (i : ValuationWord) <+: a)
      (hj : (j : ValuationWord) <+: a) : i = j :=
    Subtype.ext (Reference.prefixFamily_unique hfree i.property j.property hi hj)
  have he : (fun a => ∃ w : V, (w : ValuationWord) <+: a) =
      Reference.prefixFamilyEvent V := by
    funext a
    apply propext
    simp [Reference.prefixFamilyEvent]
  have hp := Gated.mass_union (Reference.wordPMF q)
    (fun w : V => fun a => (w : ValuationWord) <+: a) (ValuationWord.residueOffset q) hu y
  rw [he] at hp
  have hs : selected V q y =
      ∑ w : V, wordOperator w q (Reference.marker (q - w.val.length)) y :=
    (Finset.sum_attach V (fun w => wordOperator w q (Reference.marker (q - w.length)) y)).symm
  rw [hs, hp, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  exact wordOperator_marker_eq_prefix w (hlen w w.property) y

/-- Every selected affine marker contribution is nonnegative. -/
theorem selected_nonneg (V : Finset ValuationWord) (q : ℕ) (y : ZMod (3 ^ q)) :
    0 ≤ selected V q y := by
  apply Finset.sum_nonneg
  intro w _
  exact wordOperator_nonneg w q _ (Reference.marker_nonneg _) y

/-- A prefix-free selected reference density is pointwise dominated by the original marker. -/
theorem selected_le_marker (V : Finset ValuationWord) {q : ℕ}
    (hlen : ∀ w ∈ V, w.length ≤ q)
    (hfree : (V : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v))
    (y : ZMod (3 ^ q)) : selected V q y ≤ Reference.marker q y := by
  have h := Gated.mass_add_compl (Reference.wordPMF q)
    (Reference.prefixFamilyEvent V) (ValuationWord.residueOffset q) y
  have hn := Gated.mass_nonneg (Reference.wordPMF q)
    (fun w => ¬ Reference.prefixFamilyEvent V w) (ValuationWord.residueOffset q) y
  change _ + _ = Reference.mass q y at h
  have hm : Gated.mass (Reference.wordPMF q) (Reference.prefixFamilyEvent V)
      (ValuationWord.residueOffset q) y ≤ Reference.mass q y := by linarith
  rw [selected_eq_gated V hlen hfree]
  calc
    _ ≤ ((2 / 3 : ℝ) * (3 : ℝ) ^ q) * Reference.mass q y :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    _ = Reference.marker q y := by simp only [Reference.marker, Reference.density]; ring

/-- Full-tail selected transfer has exactly the original family mass times two thirds. -/
theorem mean_selected (V : Finset ValuationWord) {q : ℕ}
    (hlen : ∀ w ∈ V, w.length ≤ q) :
    Reference.mean q (selected V q) = (2 / 3 : ℝ) * Reference.stoppingMass V := by
  unfold selected
  rw [mean_finset_sum, Reference.stoppingMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [mean_wordOperator w (hlen w hw), Reference.mean_marker]
  ring

/-- Coarse replacement has the same mean; no mixing estimate is needed for this identity. -/
theorem mean_coarseSelected (V : Finset ValuationWord) {q k : ℕ}
    (hlen : ∀ w ∈ V, w.length ≤ q) (hk : ∀ w ∈ V, k ≤ q - w.length) :
    Reference.mean q (coarseSelected V q k hk) = (2 / 3 : ℝ) * Reference.stoppingMass V := by
  classical
  have hs : Reference.stoppingMass V = ∑ w : V, 1 / (2 : ℝ) ^ w.val.total :=
    (Finset.sum_attach V (fun w => 1 / (2 : ℝ) ^ w.total)).symm
  unfold coarseSelected
  rw [mean_finset_sum, hs, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [mean_wordOperator w (hlen w w.property), Reference.mean_project, Reference.mean_marker]
  ring

/-- The full marker minus selected density has exactly the original missing mean mass. -/
theorem mean_selected_deficit (V : Finset ValuationWord) {q : ℕ}
    (hlen : ∀ w ∈ V, w.length ≤ q) :
    Reference.mean q (fun y => Reference.marker q y - selected V q y) =
      (2 / 3 : ℝ) * (1 - Reference.stoppingMass V) := by
  rw [Reference.mean_sub, Reference.mean_marker, mean_selected V hlen]
  ring

/-- An empty family selects no density. -/
@[simp] theorem selected_empty (q : ℕ) (y : ZMod (3 ^ q)) : selected ∅ q y = 0 := by
  simp [selected]

/-- Selecting only the empty word retains the entire reference marker. -/
@[simp] theorem selected_singleton_nil (q : ℕ) (y : ZMod (3 ^ q)) :
    selected {[]} q y = Reference.marker q y := by
  simp [selected, wordOperator_nil]

end WordCertDensity.Transfer
