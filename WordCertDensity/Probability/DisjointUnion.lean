/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Probability.FiniteUnion

/-! # Disjoint unions of original PMF events

Nonnegative sums permit the countable cylinder decomposition used for the
geometric overshoot. No conditional probability or changed source law is used.
-/

@[expose] public section

namespace WordCertDensity.Gated

/-- Disjoint original events have the sum of their original probabilities. -/
theorem probability_iUnion {α ι : Type*} (p : PMF α) (G : ι → α → Prop)
    (hunique : ∀ i j a, G i a → G j a → i = j) :
    probability p (fun a => ∃ i, G i a) = ∑' i, probability p (G i) := by
  classical
  have hpoint (a : α) : (if ∃ i, G i a then p a else 0) =
      ∑' i, if G i a then p a else 0 := by
    by_cases h : ∃ i, G i a
    · obtain ⟨i, hi⟩ := h
      rw [if_pos ⟨i, hi⟩, tsum_eq_single i]
      · simp [hi]
      · intro j hj
        have hj' : ¬ G j a := fun hg => hj (hunique j i a hg hi)
        simp [hj']
    · simp only [not_exists] at h
      simp [h]
  unfold probability
  simp_rw [hpoint]
  rw [ENNReal.tsum_comm, ENNReal.tsum_toReal_eq (fun i => event_ne_top p (G i))]

end WordCertDensity.Gated
