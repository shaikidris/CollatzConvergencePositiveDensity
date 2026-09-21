/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.HeadPartition
public import WordCertDensity.Analytic.IntervalFailure
public import WordCertDensity.Probability.FiniteUnion
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-! # Actual interval coverage and the triangular count -/

@[expose] public section

namespace WordCertDensity
namespace Head

/-- Every atypical word has an actual positive-length interval with a valid starting position. -/
theorem not_typical_iff_intervals {v : ℝ} {n : ℕ} {w : ValuationWord} (hlen : w.length = n) :
    ¬ Typical v n w ↔ ∃ r ∈ Finset.range n, ∃ i ∈ Finset.range (n - r),
      intervalFailure v n i (i + (r + 1)) w := by
  classical
  unfold Typical
  push Not
  constructor
  · rintro ⟨i, j, hij, hj, hb⟩
    refine ⟨j - i - 1, Finset.mem_range.mpr (by omega), i, Finset.mem_range.mpr (by omega), ?_⟩
    have he : i + (j - i - 1 + 1) = j := by omega
    simpa only [he, intervalFailure] using hb
  · rintro ⟨r, hr, i, hi, hb⟩
    simp only [Finset.mem_range] at hr hi
    exact ⟨i, i + (r + 1), by omega, by omega, hb⟩

/-- Summing the number of starts at each positive length gives exactly n(n+1)/2 intervals. -/
theorem sum_interval_starts (n : ℕ) :
    (∑ r ∈ Finset.range n, ((n - r : ℕ) : ℝ)) = (n : ℝ) * ((n : ℝ) + 1) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have hin : (∑ r ∈ Finset.range n, ((n + 1 - r : ℕ) : ℝ)) =
          (∑ r ∈ Finset.range n, ((n - r : ℕ) : ℝ)) + n := by
        calc
          _ = ∑ r ∈ Finset.range n, (((n - r : ℕ) : ℝ) + 1) := by
            apply Finset.sum_congr rfl
            intro r hr
            have he : n + 1 - r = (n - r) + 1 := by
              have := Finset.mem_range.mp hr
              omega
            rw [he, Nat.cast_add, Nat.cast_one]
          _ = _ := by simp [Finset.sum_add_distrib]
      rw [hin, ih]
      norm_num
      ring

end Head

namespace HeadSlice

/-- The global failure probability is bounded by the sum over all actual intervals, grouped by length. -/
theorem failureProbability_le_intervals (v : ℝ) (n : ℕ) :
    failureProbability v n ≤ ∑ r ∈ Finset.range n, ∑ i ∈ Finset.range (n - r),
      Gated.probability (Reference.wordPMF n) (Head.intervalFailure v n i (i + (r + 1))) := by
  have he := Gated.probability_congr_on_support (Reference.wordPMF n)
    (fun w => ¬ Head.Typical v n w)
    (fun w => ∃ r ∈ Finset.range n, ∃ i ∈ Finset.range (n - r),
      Head.intervalFailure v n i (i + (r + 1)) w)
    (fun w hw => Head.not_typical_iff_intervals ((Reference.wordPMF_mem_support_iff n w).mp hw))
  unfold failureProbability
  rw [he]
  calc
    _ ≤ ∑ r ∈ Finset.range n, Gated.probability (Reference.wordPMF n)
        (fun w => ∃ i ∈ Finset.range (n - r), Head.intervalFailure v n i (i + (r + 1)) w) :=
      Gated.probability_biUnion_le _ _ _
    _ ≤ _ := Finset.sum_le_sum (fun r _ => Gated.probability_biUnion_le _ _ _)

end HeadSlice
end WordCertDensity
