/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.WhiteVisits
public import WordCertDensity.Reference.CountableStopping

/-! # Original-law tail factorization at bounded stopping prefixes

All masses are computed under the original reference word PMF. The tail
horizon depends on the selected prefix, and its event may depend on that
prefix as well.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- At a prescribed prefix, the remaining original word has the fresh tail
law with the exact remaining horizon. -/
theorem prefix_tail_probability (u : ValuationWord) (N : ℕ)
    (hu : u.length ≤ N) (B : ValuationWord → Prop) :
    Gated.probability (Reference.wordPMF N)
      (fun w => u <+: w ∧ B (w.drop u.length)) =
      (Reference.wordPMF u.length u).toReal *
        Gated.probability (Reference.wordPMF (N - u.length)) B := by
  have he := Gated.probability_congr_on_support (Reference.wordPMF N)
    (fun w => u <+: w ∧ B (w.drop u.length))
    (fun w => w.take u.length = u ∧ B (w.drop u.length))
    (fun w _ => by rw [List.prefix_iff_eq_take]; exact and_congr eq_comm Iff.rfl)
  rw [he]
  have h := wordPMF_fixedCut_tail_probability u.length (N - u.length) u B
  simpa only [Nat.add_sub_of_le hu] using h

/-- The same prescribed-prefix factorization in ENNReal, before any
countable sum or conversion to real probabilities. -/
theorem prefix_tail_eventMass (u : ValuationWord) (N : ℕ)
    (hu : u.length ≤ N) (B : ValuationWord → Prop) :
    (∑' w : ValuationWord, if u <+: w ∧ B (w.drop u.length)
      then Reference.wordPMF N w else 0) =
      Reference.wordPMF u.length u *
        ∑' v : ValuationWord, if B v then Reference.wordPMF (N - u.length) v else 0 := by
  have hleft : (∑' w : ValuationWord, if u <+: w ∧ B (w.drop u.length)
      then Reference.wordPMF N w else 0) ≠ ⊤ := by
    apply ne_of_lt
    calc
      _ ≤ ∑' w, Reference.wordPMF N w := ENNReal.tsum_le_tsum (fun w => by
        split_ifs <;> simp)
      _ < ⊤ := by rw [PMF.tsum_coe]; simp
  apply (ENNReal.toReal_eq_toReal_iff' hleft
    (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (Gated.event_ne_top _ B))).mp
  rw [ENNReal.toReal_mul]
  have he : (∑' w : ValuationWord, if u <+: w ∧ B (w.drop u.length)
      then Reference.wordPMF N w else 0) =
      ∑' w : ValuationWord, @ite ℝ≥0∞ (u <+: w ∧ B (w.drop u.length))
        (Classical.propDecidable _) (Reference.wordPMF N w) 0 := by
    apply tsum_congr
    intro w
    by_cases hw : u <+: w ∧ B (w.drop u.length) <;> simp [hw]
  rw [he]
  exact prefix_tail_probability u N hu B

/-- Countable prefix-free selection factors the original tail law exactly.
This bounded stopping identity allows arbitrary prefix-dependent tail events
and does not condition or renormalize the source mass. -/
theorem countableStoppedTail_factor
    (S : Set ValuationWord) (N : ℕ) (B : ValuationWord → ValuationWord → Prop)
    (hlen : ∀ u ∈ S, u.length ≤ N)
    (hfree : S.Pairwise (fun u v => ¬ u <+: v)) :
    (∑' w : ValuationWord,
      if ∃ u : S, (u : ValuationWord) <+: w ∧ B u (w.drop (u : ValuationWord).length)
      then Reference.wordPMF N w else 0) =
    ∑' u : S, Reference.wordPMF (u : ValuationWord).length u *
      ∑' v : ValuationWord,
        if B u v then Reference.wordPMF (N - (u : ValuationWord).length) v else 0 := by
  rw [Reference.countableStopping_tail_event_decomposition S N B hfree]
  apply tsum_congr
  intro u
  exact prefix_tail_eventMass u N (hlen u u.property) (B u)

/-- The geometric mass of a word is its original atom at its own length. -/
theorem wordPMF_length_eventMass (u : ValuationWord) :
    Reference.wordPMF u.length u = (1 / 2 : ℝ≥0∞) ^ u.total := by
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (by finiteness)).mp
  simpa using Reference.wordPMF_toReal_length u

/-- A tail event of constant mass at every selected prefix factors out of
the countable stopping mass. No finiteness of the prefix family is required. -/
theorem countableStoppedTail_constant
    (S : Set ValuationWord) (N : ℕ) (B : ValuationWord → ValuationWord → Prop)
    (hlen : ∀ u ∈ S, u.length ≤ N)
    (hfree : S.Pairwise (fun u v => ¬ u <+: v)) (c : ℝ≥0∞)
    (hB : ∀ u : S, (∑' v : ValuationWord,
      if B u v then Reference.wordPMF (N - (u : ValuationWord).length) v else 0) = c) :
    (∑' w : ValuationWord,
      if ∃ u : S, (u : ValuationWord) <+: w ∧ B u (w.drop (u : ValuationWord).length)
      then Reference.wordPMF N w else 0) = Reference.countableStoppingMass S * c := by
  rw [countableStoppedTail_factor S N B hlen hfree]
  simp_rw [hB, wordPMF_length_eventMass]
  exact ENNReal.tsum_mul_right

/-- A fresh first pair has total three with mass one quarter, in the native
nonnegative codomain used for countable stopping families. -/
theorem freshPairMark_tail_eventMass (q : ℕ) :
    (∑' v : ValuationWord, @ite ℝ≥0∞ (ValuationWord.total (v.take 2) = 3)
      (Classical.propDecidable _) (Reference.wordPMF (2 + q) v) 0) =
      (1 / 4 : ℝ≥0∞) := by
  apply (ENNReal.toReal_eq_toReal_iff'
    (Gated.event_ne_top (Reference.wordPMF (2 + q)) _ ) (by finiteness)).mp
  change Gated.probability (Reference.wordPMF (2 + q))
    (fun v => ValuationWord.total (v.take 2) = 3) = (1 / 4 : ℝ≥0∞).toReal
  rw [freshPairMark_tail_probability]
  norm_num

/-- The first post-stop pair has exact mark mass one quarter of the selected
mass, including infinite valuation families at a bounded stopping horizon. -/
theorem countableStoppedMark_eventMass (S : Set ValuationWord) (N : ℕ)
    (hlen : ∀ u ∈ S, u.length + 2 ≤ N)
    (hfree : S.Pairwise (fun u v => ¬ u <+: v)) :
    (∑' w : ValuationWord,
      if ∃ u : S, (u : ValuationWord) <+: w ∧
        ValuationWord.total ((w.drop (u : ValuationWord).length).take 2) = 3
      then Reference.wordPMF N w else 0) =
      Reference.countableStoppingMass S * (1 / 4 : ℝ≥0∞) := by
  apply countableStoppedTail_constant S N
    (fun _ v => ValuationWord.total (v.take 2) = 3)
    (fun u hu => by have := hlen u hu; omega) hfree
  intro u
  have hN : N - (u : ValuationWord).length =
      2 + (N - (u : ValuationWord).length - 2) := by
    have := hlen u u.property
    omega
  rw [hN]
  exact freshPairMark_tail_eventMass _

end WordCertDensity.LocalPrimitive
