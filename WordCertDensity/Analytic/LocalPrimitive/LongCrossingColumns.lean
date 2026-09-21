/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.LongCrossingHorizontal

/-! # Unconditional mass of deterministic bad columns -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical

/-- The post-crossing column belongs to a fixed deterministic set. -/
def longCrossingColumnsEvent (s j p : ℕ) (columns : Finset ℕ) (w : ValuationWord) : Prop :=
  ∃ i : Fin (s / 2 + 1), horizonTailEvent s 0 i w ∧ j + ((i : ℕ) + 1) + p ∈ columns

private theorem single_column_probability_le (L s j p x : ℕ)
    (hL : s / 2 + 1 ≤ L) (hs : 0 < s) :
    Gated.probability (Reference.wordPMF (2 * L))
        (fun w => ∃ i : Fin (s / 2 + 1), horizonTailEvent s 0 i w ∧
          j + ((i : ℕ) + 1) + p = x) ≤ 4 / Real.sqrt (s : ℝ) := by
  let q := x - j - p
  by_cases hq : 0 < q ∧ q ≤ s / 2 + 1
  · have hmono : Gated.probability (Reference.wordPMF (2 * L))
        (fun w => ∃ i : Fin (s / 2 + 1), horizonTailEvent s 0 i w ∧
          j + ((i : ℕ) + 1) + p = x) ≤
        Gated.probability (Reference.wordPMF (2 * L)) (horizonTailEvent s 0 (q - 1)) := by
      apply Gated.probability_mono_on_support
      intro w _ hw
      rcases hw with ⟨i, hi, hx⟩
      have heq : (i : ℕ) = q - 1 := by dsimp [q]; omega
      simpa only [heq] using hi
    apply hmono.trans
    rw [horizonPassageIndexEvent_probability_eq hq.1 (hq.2.trans hL),
      pairPassageIndexProbability_eq_fairPassageIndexProbability hq.1]
    exact fairPassageIndexProbability_le_four_div_sqrt hs hq.1
  · have hempty : ∀ w, ¬ (∃ i : Fin (s / 2 + 1), horizonTailEvent s 0 i w ∧
          j + ((i : ℕ) + 1) + p = x) := by
      rintro w ⟨i, _, hx⟩
      have hi := i.isLt
      apply hq
      dsimp [q]
      omega
    simp only [hempty, if_false, Gated.probability, tsum_zero, ENNReal.toReal_zero]
    positivity

/-- Apply the unconditional passage-index atom estimate to all deterministic
bad columns. No vertical coordinate is fixed or conditioned on. -/
theorem longCrossingColumns_probability_le (L s j p : ℕ) (columns : Finset ℕ)
    (hL : s / 2 + 1 ≤ L) (hs : 0 < s) :
    Gated.probability (Reference.wordPMF (2 * L)) (longCrossingColumnsEvent s j p columns) ≤
      (columns.card : ℝ) * (4 / Real.sqrt (s : ℝ)) := by
  let G : ℕ → ValuationWord → Prop := fun x w =>
    ∃ i : Fin (s / 2 + 1), horizonTailEvent s 0 i w ∧ j + ((i : ℕ) + 1) + p = x
  have heq : Gated.probability (Reference.wordPMF (2 * L))
      (longCrossingColumnsEvent s j p columns) =
      Gated.probability (Reference.wordPMF (2 * L)) (fun w => ∃ x ∈ columns, G x w) := by
    apply Gated.probability_congr_on_support
    intro w _
    constructor
    · rintro ⟨i, hi, hx⟩
      exact ⟨_, hx, i, hi, rfl⟩
    · rintro ⟨x, hx, i, hi, heq⟩
      exact ⟨i, hi, heq.symm ▸ hx⟩
  rw [heq]
  apply (Gated.probability_biUnion_le _ columns G).trans
  calc
    _ ≤ ∑ _x ∈ columns, 4 / Real.sqrt (s : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      exact single_column_probability_le L s j p x hL hs
    _ = _ := by simp

end WordCertDensity.LocalPrimitive
