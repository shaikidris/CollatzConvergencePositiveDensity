/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Reference.Entropy
import WordCertDensity.Reference.EntropyLimits
import WordCertDensity.Density.Profile

/-! # Restricted analytic extensions of Phase 1

The actual reference entropy has a finite monotone limit with an explicit
summable tail and zero normalized growth. No limit in the Renyi order is
asserted here. Exact residue profiles and their actual-source density
applications use only accepted depth-eleven inputs for moment comparisons.
-/

namespace WordCertDensity.Reference

/-- Positive-index entropy increments obey the actual compact mixing envelope. -/
theorem entropy_increment (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ entropy (n + 1) - entropy n ∧
      entropy (n + 1) - entropy n ≤ min (Real.log 3) (Analytic.mixingError n) := by
  refine ⟨(entropy_increment_l1 n).1, le_min ?_ ?_⟩
  · exact entropy_increment_log_three n
  · exact (entropy_increment_l1 n).2.trans
      (Analytic.mean_le_mixingError hn (Nat.le_succ n))

end WordCertDensity.Reference

namespace WordCertDensity.Release.AnalyticExtensions

open Reference Filter
open scoped Topology

/-- The actual fan allocation attains its exact hinge-dual value on the full feasible range. -/
theorem profile_allocation (m : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hpaid : p ≤ (2 * Real.log 2) * (8 / 9)) :
    (∃ w, Counting.feasibleProfile m p w ∧ (∑ r, w r) = Counting.profile m p) ∧
    Counting.profile m p = sSup {a | ∃ t : ℝ, 0 < t ∧
      a = max (p - (2 * Real.log 2) * Reference.mean m
        (fun r => max (Reference.fan m r - t) 0)) 0 / t} ∧
    0 ≤ Counting.profile m p ∧ Counting.profile m p ≤ p / (8 / 9) :=
  Counting.profile_hinge m p hp hpaid

/-- Every real moment of order greater than one supplies a lower bound on the exact profile. -/
theorem profile_moment_bound (m : ℕ) (p s B : ℝ) (hm : 2 ≤ m)
    (hp : 0 ≤ p) (hpaid : p ≤ (2 * Real.log 2) * (8 / 9))
    (hs : 1 < s) (hB : 0 < B)
    (hmoment : Reference.mean m (fun r => Reference.fan m r ^ s) ≤ B) :
    p ^ (s / (s - 1)) / ((2 * Real.log 2 * B) ^ (1 / (s - 1))) ≤
      Counting.profile m p :=
  Density.profile_moment_bound m p s B hm hp hpaid hs hB hmoment

/-- A single positive canonical residual gives the full profile bound for every larger clock. -/
theorem profile_density :
    ∃ W : ℝ, Density.SmallScore W ∧ ∃ m : ℕ, 2 ≤ m ∧ 0 < Density.residual W m ∧
      ∀ c : ℝ, criticalClock < c →
        Counting.radial (Counting.profile m (Density.residual W m)) ≤
          lowerNaturalDensity (goodTarget 1 c) :=
  Density.canonical_profile_density

/-- Every positive target prime to three has its own actual positive profile residual. -/
theorem target_profile_density {target : ℕ} (htarget : 0 < target)
    (hnotthree : ¬ 3 ∣ target) :
    ∃ W : ℝ, Density.SmallScore W ∧ ∃ m : ℕ, 2 ≤ m ∧ 0 < Density.residual W m ∧
      ∀ c : ℝ, criticalClock < c →
        Counting.radial (Counting.profile m (Density.residual W m)) ≤
          lowerNaturalDensity (goodTarget target c) :=
  Density.admissibleTarget_profile_density htarget hnotthree

/-- The actual positive-index entropy increment obeys the compact mixing envelope. -/
theorem entropy_increment (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ Reference.entropy (n + 1) - Reference.entropy n ∧
      Reference.entropy (n + 1) - Reference.entropy n ≤
        min (Real.log 3) (Analytic.mixingError n) :=
  Reference.entropy_increment n hn

/-- The actual reference entropy converges with the full compact-envelope tail. -/
theorem entropy_limit :
    ∃ z : ℝ, Tendsto Reference.entropy atTop (𝓝 z) ∧
      (∀ n, Reference.entropy n ≤ z) ∧
      z ≤ (2 / 3 : ℝ) * Real.log 2 + ∑' j : ℕ, entropyError (j + 1) ∧
      (∀ n, 1 ≤ n → 0 ≤ z - Reference.entropy n ∧
        z - Reference.entropy n ≤ ∑' j : ℕ, entropyError (n + j)) := by
  simpa only [entropy_one] using bounded_increment_limit entropy_nonneg entropy_monotone
    (fun n hn => entropyError_nonneg hn)
    (fun n hn => (entropy_increment n hn).2) entropyError_summable

/-- The same limit obeys the manuscript's explicit optimized-power series bound. -/
theorem entropy_limit_power :
    ∃ z : ℝ, Tendsto Reference.entropy atTop (𝓝 z) ∧
      (∀ n, Reference.entropy n ≤ z) ∧
      z ≤ (2 / 3 : ℝ) * Real.log 2 + ∑' j : ℕ, min (Real.log 3)
        (Analytic.mixingCoefficient * ((j + 1 : ℕ) : ℝ) ^ (-Analytic.mixingExponent)) := by
  obtain ⟨z, hz, hbound, hseries, _⟩ := entropy_limit
  refine ⟨z, hz, hbound, hseries.trans (add_le_add le_rfl ?_)⟩
  simpa only [Nat.add_comm] using entropyError_tail_le_power 1 (by omega)

/-- Both normalized order-one growth and the positive-index infimum vanish. -/
theorem entropy_zero_rate :
    Tendsto (fun n : ℕ => Reference.entropy n / n) atTop (𝓝 0) ∧
      (⨅ n : ℕ, Reference.entropy (n + 1) / (n + 1 : ℝ)) = 0 := by
  obtain ⟨z, _, hbound, _, _⟩ := entropy_limit
  exact ⟨bounded_nonneg_normalized_tendsto_zero entropy_nonneg hbound,
    bounded_nonneg_normalized_iInf_zero entropy_nonneg hbound⟩

end WordCertDensity.Release.AnalyticExtensions
