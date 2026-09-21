/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.PassageMoment

/-! # Original-law averaging of a suffix moment estimate -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- A bounded prefix-free family has source mass at most one. -/
theorem countableStoppingMass_le_one (S : Set ValuationWord) (N : ℕ)
    (hlen : ∀ u ∈ S, u.length ≤ N)
    (hfree : S.Pairwise (fun u v => ¬ u <+: v)) :
    Reference.countableStoppingMass S ≤ 1 := by
  rw [Reference.countableStoppingMass_eq_event S N hlen hfree]
  calc
    _ ≤ ∑' w : ValuationWord, Reference.wordPMF N w :=
      ENNReal.tsum_le_tsum (fun w => by split_ifs <;> simp)
    _ = 1 := PMF.tsum_coe _

/-- A fresh moment bounded by its shortage event plus a uniform error gives
the original stopped shortage mass plus the same error after averaging. -/
theorem countableStoppedMoment_le_event_add (S : Set ValuationWord) (N : ℕ)
    (F : ValuationWord → ValuationWord → ℝ≥0∞)
    (E : ValuationWord → ValuationWord → Prop) (c : ℝ≥0∞)
    (hlen : ∀ u ∈ S, u.length ≤ N)
    (hfree : S.Pairwise (fun u v => ¬ u <+: v))
    (hF : ∀ u : S,
      (∑' v : ValuationWord, Reference.wordPMF (N - (u : ValuationWord).length) v * F u v) ≤
        (∑' v : ValuationWord, if E u v then
          Reference.wordPMF (N - (u : ValuationWord).length) v else 0) + c) :
    (∑' w : ValuationWord, ∑' u : S, if (u : ValuationWord) <+: w then
      Reference.wordPMF N w * F u (w.drop (u : ValuationWord).length) else 0) ≤
      (∑' w : ValuationWord, if ∃ u : S,
        (u : ValuationWord) <+: w ∧ E u (w.drop (u : ValuationWord).length)
        then Reference.wordPMF N w else 0) + c := by
  rw [countableStoppedMoment_factor S N F hlen,
    countableStoppedTail_factor S N E hlen hfree]
  calc
    _ ≤ ∑' u : S, Reference.wordPMF (u : ValuationWord).length u *
        ((∑' v : ValuationWord, if E u v then
          Reference.wordPMF (N - (u : ValuationWord).length) v else 0) + c) :=
      ENNReal.tsum_le_tsum (fun u => mul_le_mul_right (hF u) _)
    _ = (∑' u : S, Reference.wordPMF (u : ValuationWord).length u *
        (∑' v : ValuationWord, if E u v then
          Reference.wordPMF (N - (u : ValuationWord).length) v else 0)) +
        Reference.countableStoppingMass S * c := by
      simp_rw [mul_add]
      rw [ENNReal.tsum_add]
      congr 1
      simp_rw [wordPMF_length_eventMass]
      exact ENNReal.tsum_mul_right
    _ ≤ _ := add_le_add le_rfl (by
      simpa only [one_mul] using
        mul_le_mul_left (countableStoppingMass_le_one S N hlen hfree) c)

end WordCertDensity.LocalPrimitive
