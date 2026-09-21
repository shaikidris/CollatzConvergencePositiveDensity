/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.SeedHistories
public import WordCertDensity.Transfer.Selected

/-!
# Exact finite seed marks

The seed conductor leaves exactly the prescribed terminal reference depth.
The mean retains the product of the original block masses, including the
empty history, without conditioning on survival.
-/

@[expose] public section

namespace WordCertDensity.Construction

/-- The reference depth left after all seed blocks have been transferred. -/
def seedTailDepth (b n : ℕ) : ℕ := seedSize b n / 4

/-- The full conductor is cumulative word depth plus terminal reference depth. -/
def seedConductor (b n : ℕ) : ℕ := seedDepth b 0 n + seedTailDepth b n

/-- Every complete seed word leaves exactly the same reference tail. -/
theorem seedConductor_sub_length {b n : ℕ} {w : ValuationWord}
    (hw : w ∈ seedHistoryWords b 0 n) :
    seedConductor b n - w.length = seedTailDepth b n := by
  rw [seedHistoryWords_depth hw, seedConductor, Nat.add_sub_cancel_left]

/-- The seed conductor contains every complete word in its finite family. -/
theorem seedHistoryWords_length_le {b n : ℕ} {w : ValuationWord}
    (hw : w ∈ seedHistoryWords b 0 n) : w.length ≤ seedConductor b n := by
  rw [seedHistoryWords_depth hw, seedConductor]
  omega

private theorem seedMass_eq_sum {b : ℕ} (hb : 0 < b) (t n : ℕ) :
    Reference.stoppingMass (seedHistoryWords b t n) =
      ∑ ws ∈ seedBlockLists b t n, 1 / (2 : ℝ) ^ (ValuationWord.total ws.flatten) := by
  classical
  unfold Reference.stoppingMass seedHistoryWords
  rw [Finset.sum_image]
  intro us hu vs hv he
  exact seedBlocks_flatten_injective hb ((mem_seedBlockLists b t n us).mp hu).2
    ((mem_seedBlockLists b t n vs).mp hv).2 he

/-- Concatenation multiplies the original next-block mass by the remaining mass. -/
theorem seedHistoryWords_mass_succ {b : ℕ} (hb : 0 < b) (t n : ℕ) :
    Reference.stoppingMass (seedHistoryWords b t (n + 1)) =
      Reference.stoppingMass (seedWords (seedSize b t)) *
        Reference.stoppingMass (seedHistoryWords b (t + 1) n) := by
  classical
  rw [seedMass_eq_sum hb, seedBlockLists, Finset.sum_image]
  · rw [Finset.product_eq_sprod, Finset.sum_product]
    simp_rw [List.flatten_cons, ValuationWord.total_append, pow_add,
      ← one_div_mul_one_div]
    rw [← Finset.sum_mul_sum, ← seedMass_eq_sum hb]
    rfl
  · intro a ha c hc he
    exact Prod.ext (List.cons.inj he).1 (List.cons.inj he).2

/-- The complete finite seed family has exactly the product of its original block masses. -/
theorem seedHistoryWords_mass_product {b : ℕ} (hb : 0 < b) (t n : ℕ) :
    Reference.stoppingMass (seedHistoryWords b t n) =
      ∏ j ∈ Finset.range n, Reference.stoppingMass (seedWords (seedSize b (t + j))) := by
  induction n generalizing t with
  | zero =>
    simp [seedHistoryWords, seedBlockLists, Reference.stoppingMass, ValuationWord.total]
  | succ n ih =>
    rw [seedHistoryWords_mass_succ hb, ih]
    simp [Finset.prod_range_succ', Nat.add_comm, Nat.add_left_comm, mul_comm]

/-- The actual finite seed mark, using the full reference tail at its exact conductor. -/
noncomputable def seedMark (b n : ℕ) : ZMod (3 ^ seedConductor b n) → ℝ :=
  Transfer.selected (seedHistoryWords b 0 n) (seedConductor b n)

/-- Each summand uses precisely the terminal reference depth specified by the seed. -/
theorem seedMark_eq_sum (b n : ℕ) (y : ZMod (3 ^ seedConductor b n)) :
    seedMark b n y = ∑ w ∈ seedHistoryWords b 0 n,
      Transfer.wordOperator w (seedConductor b n)
        (Reference.marker (seedConductor b n - w.length)) y := rfl

/-- Seed marks are nonnegative without a survival estimate. -/
theorem seedMark_nonneg (b n : ℕ) (y : ZMod (3 ^ seedConductor b n)) :
    0 ≤ seedMark b n y := Transfer.selected_nonneg _ _ _

/-- The exact full-group mean is two thirds of the unconditioned product mass. -/
theorem mean_seedMark {b : ℕ} (hb : 0 < b) (n : ℕ) :
    Reference.mean (seedConductor b n) (seedMark b n) =
      (2 / 3 : ℝ) * ∏ j ∈ Finset.range n,
        Reference.stoppingMass (seedWords (seedSize b j)) := by
  rw [seedMark, Transfer.mean_selected _ (fun _ hw => seedHistoryWords_length_le hw),
    seedHistoryWords_mass_product hb]
  simp only [Nat.zero_add]

/-- Prefix exclusion bounds the seed mark by the unselected reference marker. -/
theorem seedMark_le_marker (b n : ℕ) (y : ZMod (3 ^ seedConductor b n)) :
    seedMark b n y ≤ Reference.marker (seedConductor b n) y :=
  Transfer.selected_le_marker _ (fun _ hw => seedHistoryWords_length_le hw)
    (seedHistoryWords_prefixFree b 0 n) y

/-- Positive initial tail depth gives a positive conductor even for the empty history. -/
theorem seedConductor_pos {b : ℕ} (hb : 4 ≤ b) (n : ℕ) :
    0 < seedConductor b n := by
  have hs := seedSize_ge b n
  unfold seedConductor seedTailDepth
  omega

/-- At positive seed depth no nonunit residue carries marked mass. -/
theorem seedMark_eq_zero_of_not_isUnit {b : ℕ} (hb : 4 ≤ b) (n : ℕ)
    (y : ZMod (3 ^ seedConductor b n)) (hy : ¬ IsUnit y) : seedMark b n y = 0 := by
  apply le_antisymm _ (seedMark_nonneg b n y)
  exact (seedMark_le_marker b n y).trans_eq
    (Reference.marker_eq_zero_of_not_isUnit (seedConductor_pos hb n) y hy)

/-- Before the first block, the seed mark is exactly its reference tail. -/
theorem seedMark_zero (b : ℕ) (y : ZMod (3 ^ seedConductor b 0)) :
    seedMark b 0 y = Reference.marker (seedConductor b 0) y := by
  simp [seedMark, seedHistoryWords, seedBlockLists]

end WordCertDensity.Construction
