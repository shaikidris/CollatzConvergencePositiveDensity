/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.LongCrossingTail

/-! # Two-sided original-law horizontal rectangle tail -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical

/-- Transport an event depending only on the strict passage index from one
original word horizon to its proved fair-binomial marginal. -/
theorem horizonPassage_predicate_probability_eq (L s : ℕ)
    (hL : s / 2 + 1 ≤ L) (Q : ℕ → Prop) :
    Gated.probability (Reference.wordPMF (2 * L))
        (fun w => ∃ i : Fin (s / 2 + 1), horizonTailEvent s 0 i w ∧ Q (i + 1)) =
      Gated.probability (Probability.fairBinomial s) (fun k => Q (passageIndex k)) := by
  let G : Fin (s / 2 + 1) → ValuationWord → Prop :=
    fun i w => horizonTailEvent s 0 i w ∧ Q (i + 1)
  let F : Fin (s / 2 + 1) → ℕ → Prop :=
    fun i k => passageIndex k = i + 1 ∧ Q (i + 1)
  have hG : ∀ i k w, G i w → G k w → i = k := by
    intro i k w hi hk
    exact Fin.ext (horizonTailEvent_unique hi.1 hk.1)
  have hF : ∀ i k x, F i x → F k x → i = k := by
    intro i k x hi hk
    apply Fin.ext
    have := hi.1
    have := hk.1
    omega
  have hfair : Gated.probability (Probability.fairBinomial s) (fun k => ∃ i, F i k) =
      Gated.probability (Probability.fairBinomial s) (fun k => Q (passageIndex k)) := by
    apply Gated.probability_congr_on_support
    intro k hk
    constructor
    · rintro ⟨i, heq, hQ⟩
      exact heq.symm ▸ hQ
    · intro hQ
      have hks : k ≤ s := by
        by_contra hnot
        exact hk (fairBinomial_eq_zero_of_lt s k (by omega))
      have hjpos := passageIndex_pos k
      have hjle := passageIndex_le_of_le hks
      let i : Fin (s / 2 + 1) := ⟨passageIndex k - 1, by omega⟩
      have heq : passageIndex k = (i : ℕ) + 1 := by dsimp [i]; omega
      exact ⟨i, heq, heq ▸ hQ⟩
  calc
    _ = ∑ i, Gated.probability (Reference.wordPMF (2 * L)) (G i) :=
      Gated.probability_union _ G hG
    _ = ∑ i, Gated.probability (Probability.fairBinomial s) (F i) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hQ : Q (i + 1)
      · simp only [G, F, hQ, and_true]
        have h := horizonPassageIndexEvent_probability_eq (s := s)
          (j := (i : ℕ) + 1) (N := L) (by omega) (by have := i.isLt; omega)
        simp only [Nat.add_sub_cancel] at h
        rw [h, pairPassageIndexProbability_eq_fairPassageIndexProbability (by omega)]
        rfl
      · simp [G, F, hQ, Gated.probability]
    _ = _ := (Gated.probability_union _ F hF).symm.trans hfair

/-- Two-sided deviation of the actual original-word passage index. -/
def longCrossingHorizontalEvent (s : ℕ) (a : ℝ) (w : ValuationWord) : Prop :=
  ∃ i : Fin (s / 2 + 1), horizonTailEvent s 0 i w ∧
    a * Real.sqrt s + 1 < |(((i : ℕ) + 1 : ℕ) : ℝ) - (s : ℝ) / 4|

private theorem passage_deviation_implies_count_deviation (s k : ℕ) (a : ℝ)
    (h : a * Real.sqrt s + 1 < |(passageIndex k : ℝ) - (s : ℝ) / 4|) :
    2 * a * Real.sqrt s ≤ Probability.fairCenteredCount s k ∨
      Probability.fairCenteredCount s k ≤ -(2 * a * Real.sqrt s) := by
  have hfloor : 2 * (k / 2) ≤ k := by omega
  have hceil : k ≤ 2 * (k / 2) + 1 := by omega
  have hf : (2 : ℝ) * (k / 2 : ℕ) ≤ k := by exact_mod_cast hfloor
  have hc : (k : ℝ) ≤ 2 * (k / 2 : ℕ) + 1 := by exact_mod_cast hceil
  simp only [passageIndex, Nat.cast_add, Nat.cast_one] at h
  unfold Probability.fairCenteredCount
  rcases lt_abs.mp h with h | h
  · left
    linarith
  · right
    linarith

/-- Both Hoeffding tails apply to the same original-word horizontal event. -/
theorem longCrossingHorizontal_probability_le_exp (L s : ℕ) (hL : s / 2 + 1 ≤ L)
    (hs : 0 < s) (a : ℝ) (ha : 0 ≤ a) :
    Gated.probability (Reference.wordPMF (2 * L)) (longCrossingHorizontalEvent s a) ≤
      2 * Real.exp (-8 * a ^ 2) := by
  unfold longCrossingHorizontalEvent
  rw [horizonPassage_predicate_probability_eq L s hL
    (fun q => a * Real.sqrt s + 1 < |(q : ℝ) - (s : ℝ) / 4|)]
  let U : ℕ → Prop := fun k => 2 * a * Real.sqrt s ≤ Probability.fairCenteredCount s k
  let D : ℕ → Prop := fun k => Probability.fairCenteredCount s k ≤ -(2 * a * Real.sqrt s)
  have hcontain : Gated.probability (Probability.fairBinomial s)
      (fun k => a * Real.sqrt s + 1 < |(passageIndex k : ℝ) - (s : ℝ) / 4|) ≤
        Gated.probability (Probability.fairBinomial s) (fun k => U k ∨ D k) := by
    apply Gated.probability_mono_on_support
    intro k _ hk
    exact passage_deviation_implies_count_deviation s k a hk
  have harg : 0 ≤ 2 * a * Real.sqrt (s : ℝ) := by positivity
  have hu := Probability.fairBinomial_centeredUpperTail_le s hs harg
  have hd := Probability.fairBinomial_centeredLowerTail_le s hs harg
  have he : -2 * (2 * a * Real.sqrt (s : ℝ)) ^ 2 / s = -8 * a ^ 2 := by
    have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
    have hsq := Real.sq_sqrt (Nat.cast_nonneg s)
    field_simp
    nlinarith
  rw [he] at hu hd
  exact hcontain.trans ((Gated.probability_or_le _ U D).trans (by dsimp [U, D]; linarith))

/-- The exponential two-sided error implies E.5's inverse-square bound at
the widths used there. This does not assert the all-positive-width E.4 bound. -/
theorem longCrossingHorizontal_probability_le (L s : ℕ) (hL : s / 2 + 1 ≤ L)
    (hs : 0 < s) (a : ℝ) (ha : 1 ≤ a) :
    Gated.probability (Reference.wordPMF (2 * L)) (longCrossingHorizontalEvent s a) ≤
      1 / (16 * a ^ 2) := by
  have ha0 : 0 < a := by linarith
  have hsq : 1 ≤ a ^ 2 := by nlinarith
  have hexp : 32 * a ^ 2 ≤ Real.exp (8 * a ^ 2) := by
    have h := Real.pow_div_factorial_le_exp (8 * a ^ 2) (by positivity) 2
    norm_num at h
    nlinarith [mul_nonneg (sq_nonneg a) (sub_nonneg.mpr hsq)]
  apply (longCrossingHorizontal_probability_le_exp L s hL hs a ha0.le).trans
  rw [show -8 * a ^ 2 = -(8 * a ^ 2) by ring, Real.exp_neg]
  calc
    _ ≤ 2 * (1 / (32 * a ^ 2)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hexp
    _ = _ := by field_simp; ring

end WordCertDensity.LocalPrimitive
