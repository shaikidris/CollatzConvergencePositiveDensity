/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Reference.Stopping
import WordCertDensity.Probability.DisjointUnion

/-! # Exact geometric tails after a specified original prefix

The event is a disjoint union of full prefix cylinders. Its probability and
the overshoot ratio follow directly from their original geometric weights.
-/

namespace WordCertDensity.Reference

/-- Raise a positive letter by a natural excess. -/
def raisedLetter (a : ℕ+) (k : ℕ) : ℕ+ :=
  ⟨(a : ℕ) + k, Nat.add_pos_left a.property k⟩

/-- The raised positive letter has the stated natural value. -/
@[simp] theorem raisedLetter_val (a : ℕ+) (k : ℕ) :
    (raisedLetter a k : ℕ) = (a : ℕ) + k := rfl

/-- The next letter after a specified prefix reaches a positive integer threshold. -/
def PrefixTail (v : ValuationWord) (a : ℕ+) (w : ValuationWord) : Prop :=
  ∃ k : ℕ, (v ++ [raisedLetter a k]) <+: w

/-- The exact original probability of the prefix and its next-letter tail. -/
theorem prefixTail_probability (v : ValuationWord) (a : ℕ+) {n : ℕ}
    (hn : v.length + 1 ≤ n) :
    Gated.probability (wordPMF n) (PrefixTail v a) =
      2 * (1 / 2 : ℝ) ^ (v.total + (a : ℕ)) := by
  have hunique (i j : ℕ) (w : ValuationWord)
      (hi : (v ++ [raisedLetter a i]) <+: w)
      (hj : (v ++ [raisedLetter a j]) <+: w) : i = j := by
    have he : (v ++ [raisedLetter a i]) = (v ++ [raisedLetter a j]) :=
      by
        rcases List.prefix_or_prefix_of_prefix hi hj with h | h
        · exact h.eq_of_length (by simp)
        · exact (h.eq_of_length (by simp)).symm
    have hv := List.append_right_injective v he
    have hk := congrArg PNat.val (List.singleton_injective hv)
    change (a : ℕ) + i = (a : ℕ) + j at hk
    omega
  unfold PrefixTail
  rw [Gated.probability_iUnion _ _ hunique]
  have hc (k : ℕ) := prefix_probability (v ++ [raisedLetter a k])
    (n := n) (by simpa only [List.length_append, List.length_cons, List.length_nil] using hn)
  simp_rw [hc]
  have he (k : ℕ) :
      1 / (2 : ℝ) ^ (ValuationWord.total (v ++ [raisedLetter a k])) =
        (1 / 2 : ℝ) ^ (v.total + (a : ℕ)) * (1 / 2 : ℝ) ^ k := by
    rw [ValuationWord.total_append]
    change 1 / (2 : ℝ) ^ (v.total + (raisedLetter a k : ℕ)) = _
    rw [raisedLetter_val]
    rw [← one_div_pow, ← pow_add]
    congr 1
    omega
  simp_rw [he]
  rw [tsum_mul_left, tsum_geometric_two]
  ring

/-- Raising the next-letter threshold by K+1 pays exactly the geometric overshoot factor. -/
theorem prefixTail_probability_ratio (v : ValuationWord) (a : ℕ+) (K : ℕ) {n : ℕ}
    (hn : v.length + 1 ≤ n) :
    Gated.probability (wordPMF n)
        (PrefixTail v (raisedLetter a (K + 1))) =
      (1 / 2 : ℝ) ^ (K + 1) * Gated.probability (wordPMF n) (PrefixTail v a) := by
  rw [prefixTail_probability v (raisedLetter a (K + 1)) hn,
    prefixTail_probability v a hn]
  rw [raisedLetter_val]
  rw [← Nat.add_assoc, pow_add]
  ring

end WordCertDensity.Reference
