/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.LongCrossing
public import WordCertDensity.Probability.FiniteUnion

/-!
# Original-word contracts for the long-crossing estimate

All offsets are events on the same word. The final propositions below specify
the unconditional delivery; they are not asserted as theorems. Intermediate
assembly lemmas retain their missing producer hypotheses explicitly.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- The actual position after `q + p` original pairs from a fixed start. -/
def longCrossingPosition (j : ℕ) (l : ℤ) (q p : ℕ) (w : ValuationWord) : ℕ × ℤ :=
  (j + q + p, l + ValuationWord.total (w.take (2 * (q + p))))

/-- A selected nonterminal phase triangle of at least the specified log size
contains the given lattice point. -/
def inLargeSelectedTriangle (n : ℕ) (ξ : ZMod (3 ^ n)) (u : ℕ)
    (point : ℕ × ℤ) : Prop :=
  ∃ a b, 2 * a < n ∧ isSelectedPhaseTriangle n ξ a b ∧
    (u : ℝ) ≤ phaseTriangleLogSize n a b ξ ∧
    inPhaseTriangleIntMul n ξ a b point.1 point.2

/-- The unique strict crossing followed by `p` pairs lands in a large triangle.
The bounded index is zero-based, as in `horizonTailEvent`. -/
def longCrossingLargeEvent (n : ℕ) (ξ : ZMod (3 ^ n)) (s j : ℕ)
    (l : ℤ) (H p : ℕ) (w : ValuationWord) : Prop :=
  ∃ i : Fin (s / 2 + 1), horizonTailEvent s 0 i w ∧
    inLargeSelectedTriangle n ξ (longCrossingThreshold H p)
      (longCrossingPosition j l ((i : ℕ) + 1) p w)

/-- Every offset in the union is measured on the same original-word law. -/
def longCrossingLargeUnionEvent (n : ℕ) (ξ : ZMod (3 ^ n)) (s j : ℕ)
    (l : ℤ) (H P : ℕ) (w : ValuationWord) : Prop :=
  ∃ p ∈ Finset.range P, longCrossingLargeEvent n ξ s j l H p w

/-- The literal fixed-offset right side of `(E.large-triangle)`. -/
noncomputable def longCrossingProbabilityBound (A H s p : ℕ) : ℝ :=
  (4 / A + 1 / (16 * (A : ℝ) ^ 2) + 2560 * (A : ℝ) ^ 2 / H) /
      ((p : ℝ) + 1) ^ 2 + 8 * A * ((p : ℝ) + 1) / Real.sqrt s

/-- Original E.5 geometry and numerical recipe assumptions. `P` may be any
positive horizon; E-L6 will instantiate the manuscript's particular recurrence. -/
def longCrossingAdmissible (n : ℕ) (ξ : ZMod (3 ^ n)) (a j : ℕ)
    (top l : ℤ) (B A H P Z : ℕ) : Prop :=
  0 < n ∧ ¬ (3 : ZMod (3 ^ n)) ∣ ξ ∧ 2 * a < n ∧
    isSelectedPhaseTriangle n ξ a top ∧ inPhaseTriangleIntMul n ξ a top j l ∧
    0 < B ∧ 0 < P ∧ A = 64 * (16 * 10 ^ B) ∧
    H = 2 ^ 17 * A ^ 2 * (16 * 10 ^ B) ∧
    Z = 128 * A * (P + 1) ^ 2 * (16 * 10 ^ B) ∧
    (Z : ℝ) ≤ Real.sqrt (top - l).toNat

/-- The required fixed-offset theorem, with all mathematical premises exposed.
This proposition remains an open delivery until an unconditional producer exists. -/
def LongCrossingFixedTarget : Prop :=
  ∀ (n : ℕ) (ξ : ZMod (3 ^ n)) (a j : ℕ) (top l : ℤ) (B A H P Z : ℕ),
    longCrossingAdmissible n ξ a j top l B A H P Z →
    ∀ L, (top - l).toNat / 2 + 1 + P ≤ L → ∀ p < P,
      Gated.probability (Reference.wordPMF (2 * L))
          (longCrossingLargeEvent n ξ (top - l).toNat j l H p) ≤
        longCrossingProbabilityBound A H (top - l).toNat p

/-- The simultaneous E.5 target on one original-word PMF, retaining all offsets
and every sufficiently long deterministic word horizon. -/
def LongCrossingUnionTarget : Prop :=
  ∀ (n : ℕ) (ξ : ZMod (3 ^ n)) (a j : ℕ) (top l : ℤ) (B A H P Z : ℕ),
    longCrossingAdmissible n ξ a j top l B A H P Z →
    ∀ L, (top - l).toNat / 2 + 1 + P ≤ L →
      Gated.probability (Reference.wordPMF (2 * L))
          (longCrossingLargeUnionEvent n ξ (top - l).toNat j l H P) <
        1 / (16 * (10 : ℝ) ^ B)

/-- Removing unused future letters preserves the actual stopped-position event.
This is deterministic and holds even off the word law's support. -/
theorem longCrossingLargeEvent_take_iff (n : ℕ) (ξ : ZMod (3 ^ n))
    (s j : ℕ) (l : ℤ) (H p L : ℕ) (hL : s / 2 + 1 + p ≤ L)
    (w : ValuationWord) :
    longCrossingLargeEvent n ξ s j l H p (w.take (2 * L)) ↔
      longCrossingLargeEvent n ξ s j l H p w := by
  unfold longCrossingLargeEvent
  apply exists_congr
  intro i
  have hi := i.isLt
  have hiL : 2 * (i : ℕ) ≤ 2 * L := by omega
  have hqL : 2 * ((i : ℕ) + 1) ≤ 2 * L := by omega
  have hpL : 2 * ((i : ℕ) + 1 + p) ≤ 2 * L := by omega
  simp only [horizonTailEvent, longCrossingPosition, List.take_take,
    Nat.min_eq_left hiL, Nat.min_eq_left hqL, Nat.min_eq_left hpL]

/-- The fixed-offset probability does not depend on unused future letters. -/
theorem longCrossingLargeEvent_probability_extend (n : ℕ) (ξ : ZMod (3 ^ n))
    (s j : ℕ) (l : ℤ) (H p L L' : ℕ) (hL : s / 2 + 1 + p ≤ L)
    (hLL' : L ≤ L') :
    Gated.probability (Reference.wordPMF (2 * L'))
        (longCrossingLargeEvent n ξ s j l H p) =
      Gated.probability (Reference.wordPMF (2 * L))
        (longCrossingLargeEvent n ξ s j l H p) := by
  have hmap := Gated.probability_map (Reference.wordPMF (2 * L'))
    (fun w => w.take (2 * L)) (longCrossingLargeEvent n ξ s j l H p)
  rw [Reference.wordPMF_map_take_of_le (show 2 * L ≤ 2 * L' by omega)] at hmap
  rw [hmap]
  apply Gated.probability_congr_on_support
  intro w _
  exact (longCrossingLargeEvent_take_iff n ξ s j l H p L hL w).symm

/-- The all-times event also ignores every unused future letter. -/
theorem longCrossingLargeUnionEvent_take_iff (n : ℕ) (ξ : ZMod (3 ^ n))
    (s j : ℕ) (l : ℤ) (H P L : ℕ) (hL : s / 2 + 1 + P ≤ L)
    (w : ValuationWord) :
    longCrossingLargeUnionEvent n ξ s j l H P (w.take (2 * L)) ↔
      longCrossingLargeUnionEvent n ξ s j l H P w := by
  unfold longCrossingLargeUnionEvent
  apply exists_congr
  intro p
  apply and_congr_right
  intro hp
  have hpP := Finset.mem_range.mp hp
  exact longCrossingLargeEvent_take_iff n ξ s j l H p L (by omega) w

/-- Simultaneous probability is invariant under extension of the common horizon. -/
theorem longCrossingLargeUnionEvent_probability_extend (n : ℕ) (ξ : ZMod (3 ^ n))
    (s j : ℕ) (l : ℤ) (H P L L' : ℕ) (hL : s / 2 + 1 + P ≤ L)
    (hLL' : L ≤ L') :
    Gated.probability (Reference.wordPMF (2 * L'))
        (longCrossingLargeUnionEvent n ξ s j l H P) =
      Gated.probability (Reference.wordPMF (2 * L))
        (longCrossingLargeUnionEvent n ξ s j l H P) := by
  have hmap := Gated.probability_map (Reference.wordPMF (2 * L'))
    (fun w => w.take (2 * L)) (longCrossingLargeUnionEvent n ξ s j l H P)
  rw [Reference.wordPMF_map_take_of_le (show 2 * L ≤ 2 * L' by omega)] at hmap
  rw [hmap]
  apply Gated.probability_congr_on_support
  intro w _
  exact (longCrossingLargeUnionEvent_take_iff n ξ s j l H P L hL w).symm

/-- The final all-times assembly consumes fixed-time bounds on exactly one PMF
and a finite scalar sum bound. Both missing producers remain explicit. -/
theorem longCrossingLargeUnion_probability_lt_of_bounds
    (n : ℕ) (ξ : ZMod (3 ^ n)) (s j : ℕ) (l : ℤ) (A H P L : ℕ) (δ : ℝ)
    (hfixed : ∀ p < P, Gated.probability (Reference.wordPMF (2 * L))
      (longCrossingLargeEvent n ξ s j l H p) ≤ longCrossingProbabilityBound A H s p)
    (hsum : (∑ p ∈ Finset.range P, longCrossingProbabilityBound A H s p) < δ) :
    Gated.probability (Reference.wordPMF (2 * L))
      (longCrossingLargeUnionEvent n ξ s j l H P) < δ := by
  have hunion := Gated.probability_biUnion_le (Reference.wordPMF (2 * L))
    (Finset.range P) (fun p => longCrossingLargeEvent n ξ s j l H p)
  apply lt_of_le_of_lt hunion
  apply lt_of_le_of_lt _ hsum
  apply Finset.sum_le_sum
  intro p hp
  exact hfixed p (Finset.mem_range.mp hp)

/-- Complete conditional delivery contract: fixed-time analysis and a purely
numerical sum are the only remaining premises at the final union assembly. -/
theorem longCrossingUnionTarget_of_fixedTarget (hfixed : LongCrossingFixedTarget)
    (hsum : ∀ (s B A H P Z : ℕ), 0 < B → 0 < P →
      A = 64 * (16 * 10 ^ B) → H = 2 ^ 17 * A ^ 2 * (16 * 10 ^ B) →
      Z = 128 * A * (P + 1) ^ 2 * (16 * 10 ^ B) → (Z : ℝ) ≤ Real.sqrt s →
      (∑ p ∈ Finset.range P, longCrossingProbabilityBound A H s p) <
        1 / (16 * (10 : ℝ) ^ B)) :
    LongCrossingUnionTarget := by
  intro n ξ a j top l B A H P Z hadm L hL
  have hf := hfixed n ξ a j top l B A H P Z hadm L hL
  rcases hadm with ⟨_, _, _, _, _, hB, hP, hA, hH, hZ, hlevel⟩
  exact longCrossingLargeUnion_probability_lt_of_bounds n ξ (top - l).toNat j l
    A H P L _ hf (hsum _ B A H P Z hB hP hA hH hZ hlevel)

end WordCertDensity.LocalPrimitive
