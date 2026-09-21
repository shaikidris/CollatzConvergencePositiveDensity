/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.WordTail
public import WordCertDensity.Analytic.Typical
import Lean.Elab.Tactic.Omega

/-!
# Exact contiguous-interval tails under the original word law

Dropping the initial letters and taking the requested interval preserves
its iid law. This specializes the word bound to the intervals in Typical.
-/

@[expose] public section

namespace WordCertDensity
namespace Reference

/-- Every contiguous interval has the actual reference law at its own length. -/
theorem wordPMF_map_interval {n i j : ℕ} (hij : i ≤ j) (hjn : j ≤ n) :
    (wordPMF n).map (fun w => (w.drop i).take (j - i)) = wordPMF (j - i) := by
  have hi := hij.trans hjn
  have hd : (wordPMF n).map (fun w => w.drop i) = wordPMF (n - i) := by
    simpa only [Nat.add_sub_of_le hi] using wordPMF_map_drop i (n - i)
  change (wordPMF n).map ((fun w : ValuationWord => w.take (j - i)) ∘
    (fun w : ValuationWord => w.drop i)) = wordPMF (j - i)
  rw [← PMF.map_comp, hd, wordPMF_map_take_of_le (Nat.sub_le_sub_right hjn i)]

end Reference

namespace Head

/-- The centered interval total agrees with the centered word whenever the interval fits. -/
theorem interval_centeredTotal {w : ValuationWord} {i j : ℕ} (hj : j ≤ w.length) :
    ValuationWord.centeredTotal ((w.drop i).take (j - i)) =
      (intervalSum w i j : ℝ) - 2 * ((j - i : ℕ) : ℝ) := by
  have hlen : ((w.drop i).take (j - i)).length = j - i := by
    rw [List.length_take, List.length_drop, Nat.min_eq_left (Nat.sub_le_sub_right hj i)]
  simp only [ValuationWord.centeredTotal, hlen, intervalSum]

/-- Every nonempty interval satisfies the same exact two-sided Chernoff bound. -/
theorem interval_absTail_le {n i j : ℕ} (hij : i < j) (hjn : j ≤ n) {z : ℝ} (hz : 0 < z) :
    Gated.probability (Reference.wordPMF n)
      (fun w => 2 * Real.sqrt (((j - i : ℕ) : ℝ) * z) + z / Real.log 2 ≤
        |(intervalSum w i j : ℝ) - 2 * ((j - i : ℕ) : ℝ)|) ≤ 2 * Real.exp (-z) := by
  have h := Reference.word_absTail_le (Nat.sub_pos_of_lt hij) hz
  rw [← Reference.wordPMF_map_interval hij.le hjn, Gated.probability_map] at h
  have he := Gated.probability_congr_on_support (Reference.wordPMF n)
    (fun w => 2 * Real.sqrt (((j - i : ℕ) : ℝ) * z) + z / Real.log 2 ≤
      |ValuationWord.centeredTotal ((w.drop i).take (j - i))|)
    (fun w => 2 * Real.sqrt (((j - i : ℕ) : ℝ) * z) + z / Real.log 2 ≤
      |(intervalSum w i j : ℝ) - 2 * ((j - i : ℕ) : ℝ)|)
    (fun w hw => by
      have hl : w.length = n := (Reference.wordPMF_mem_support_iff n w).mp hw
      rw [interval_centeredTotal (by omega)])
  rw [← he]
  exact h

end Head
end WordCertDensity
