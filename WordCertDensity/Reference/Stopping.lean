/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.Words
public import WordCertDensity.Probability.FiniteUnion

/-!
# Original mass of a finite prefix-free stopping family

The family is a finite set of existing positive valuation words. Its mass is
an unnormalized sum of geometric word weights. Pairwise prefix exclusion
identifies that sum with an event in the actual iid word law, including the
empty family and a family containing the empty word.
-/

@[expose] public section

namespace WordCertDensity.Reference

/-- The literal survival mass p(V), without conditioning on selection. -/
noncomputable def stoppingMass (V : Finset ValuationWord) : ℝ :=
  ∑ w ∈ V, 1 / (2 : ℝ) ^ w.total

/-- A full word is selected when it has a prefix in the finite family. -/
def prefixFamilyEvent (V : Finset ValuationWord) (w : ValuationWord) : Prop :=
  ∃ u ∈ V, u <+: w

/-- The actual iid probability of a prescribed prefix is its geometric weight. -/
theorem prefix_probability (w : ValuationWord) {n : ℕ} (hw : w.length ≤ n) :
    Gated.probability (wordPMF n) (fun a => w <+: a) = 1 / (2 : ℝ) ^ w.total := by
  have h := Gated.probability_map (wordPMF n) (fun a => a.take w.length)
    (fun a => a = w)
  rw [wordPMF_map_take_of_le hw] at h
  have he := Gated.probability_congr_on_support (wordPMF n)
    (fun a => w <+: a) (fun a => a.take w.length = w)
    (fun _ _ => by rw [List.prefix_iff_eq_take]; exact eq_comm)
  rw [he, ← h]
  classical
  unfold Gated.probability
  rw [tsum_eq_single w]
  · simpa using wordPMF_toReal_length_eq_inv_pow w
  · intro a ha
    simp [ha]

/-- Prefix exclusion gives uniqueness of a selected member on every full word. -/
theorem prefixFamily_unique {V : Finset ValuationWord}
    (hfree : (V : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v))
    {u v w : ValuationWord} (hu : u ∈ V) (hv : v ∈ V)
    (huw : u <+: w) (hvw : v <+: w) : u = v := by
  by_contra hne
  rcases List.prefix_or_prefix_of_prefix huw hvw with h | h
  · exact hfree hu hv hne h
  · exact hfree hv hu (fun he => hne he.symm) h

/-- A finite prefix-free family's original selection probability is exactly p(V). -/
theorem prefixFamily_probability (V : Finset ValuationWord) {n : ℕ}
    (hlen : ∀ w ∈ V, w.length ≤ n)
    (hfree : (V : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v)) :
    Gated.probability (wordPMF n) (prefixFamilyEvent V) = stoppingMass V := by
  classical
  have hu (i j : V) (w : ValuationWord) (hi : (i : ValuationWord) <+: w)
      (hj : (j : ValuationWord) <+: w) : i = j :=
    Subtype.ext (prefixFamily_unique hfree i.property j.property hi hj)
  have h := Gated.probability_union (wordPMF n)
    (fun i : V => fun w => (i : ValuationWord) <+: w) hu
  have he : prefixFamilyEvent V = (fun w => ∃ i : V, (i : ValuationWord) <+: w) := by
    funext w
    apply propext
    simp [prefixFamilyEvent]
  rw [he, h]
  simp_rw [prefix_probability _ (hlen _ (Subtype.mem _))]
  exact Finset.sum_attach V (fun w => 1 / (2 : ℝ) ^ w.total)

/-- The uncovered original word probability is precisely the missing survival mass. -/
theorem prefixFamily_compl_probability (V : Finset ValuationWord) {n : ℕ}
    (hlen : ∀ w ∈ V, w.length ≤ n)
    (hfree : (V : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v)) :
    Gated.probability (wordPMF n) (fun w => ¬ prefixFamilyEvent V w) = 1 - stoppingMass V := by
  rw [Gated.probability_compl, prefixFamily_probability V hlen hfree]

/-- Survival mass is nonnegative for every finite family, even with overlaps. -/
theorem stoppingMass_nonneg (V : Finset ValuationWord) : 0 ≤ stoppingMass V := by
  exact Finset.sum_nonneg (fun _ _ => by positivity)

/-- A finite prefix-free family's unconditioned mass is at most one. -/
theorem stoppingMass_le_one (V : Finset ValuationWord)
    (hfree : (V : Set ValuationWord).Pairwise (fun u v => ¬ u <+: v)) : stoppingMass V ≤ 1 := by
  have hlen (w : ValuationWord) (hw : w ∈ V) : w.length ≤ V.sup List.length :=
    Finset.le_sup hw
  rw [← prefixFamily_probability V hlen hfree]
  exact Gated.probability_le_one _ _

/-- Restricting a family can only decrease its original survival mass. -/
theorem stoppingMass_mono {U V : Finset ValuationWord} (h : U ⊆ V) :
    stoppingMass U ≤ stoppingMass V :=
  Finset.sum_le_sum_of_subset_of_nonneg h (fun _ _ _ => by positivity)

/-- No selected words means zero original survival mass. -/
@[simp] theorem stoppingMass_empty : stoppingMass ∅ = 0 := by simp [stoppingMass]

/-- A singleton retains precisely its geometric word probability. -/
@[simp] theorem stoppingMass_singleton (w : ValuationWord) :
    stoppingMass {w} = 1 / (2 : ℝ) ^ w.total := by simp [stoppingMass]

end WordCertDensity.Reference
