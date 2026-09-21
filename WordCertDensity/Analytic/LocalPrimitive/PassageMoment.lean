/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.PassageStopping
import Mathlib.Tactic

/-! # Literal moments after original-law stopping prefixes -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical ENNReal

/-- At an exact prefix, an arbitrary nonnegative suffix moment factors under
the original word law. -/
theorem prefix_tail_moment_factor (u : ValuationWord) (N : ℕ) (hu : u.length ≤ N)
    (F : ValuationWord → ℝ≥0∞) :
    (∑' w : ValuationWord, if u <+: w then
      Reference.wordPMF N w * F (w.drop u.length) else 0) =
      Reference.wordPMF u.length u *
        ∑' v : ValuationWord, Reference.wordPMF (N - u.length) v * F v := by
  have hf := prefixSuffixMoment_factor u.length (N - u.length)
    (fun v : ValuationWord => v = u) F
  unfold prefixSuffixMoment at hf
  rw [Nat.add_sub_of_le hu] at hf
  have hatom : (∑' v : ValuationWord,
      Reference.wordPMF u.length v * (if v = u then 1 else 0)) =
        Reference.wordPMF u.length u := by simp
  rw [hatom] at hf
  convert hf using 1
  apply tsum_congr
  intro w
  have he : u <+: w ↔ w.take u.length = u :=
    List.prefix_iff_eq_take.trans eq_comm
  by_cases hp : u <+: w
  · simp [hp, he.mp hp]
  · have hne : w.take u.length ≠ u := fun h => hp (he.mpr h)
    simp [hp, hne]

/-- Summing over exact stopping prefixes preserves each prefix-dependent
tail observable. Prefix-freeness is used by consumers to identify one selected
observable per source word. -/
theorem countableStoppedMoment_factor (S : Set ValuationWord) (N : ℕ)
    (F : ValuationWord → ValuationWord → ℝ≥0∞)
    (hlen : ∀ u ∈ S, u.length ≤ N) :
    (∑' w : ValuationWord, ∑' u : S, if (u : ValuationWord) <+: w then
      Reference.wordPMF N w * F u (w.drop (u : ValuationWord).length) else 0) =
      ∑' u : S, Reference.wordPMF (u : ValuationWord).length u *
        ∑' v : ValuationWord, Reference.wordPMF (N - (u : ValuationWord).length) v * F u v := by
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro u
  exact prefix_tail_moment_factor u N (hlen u u.property) (F u)

end WordCertDensity.LocalPrimitive
