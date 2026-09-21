/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.ParametricError

/-! # Nonnegative limits of the parameterized physical graft

The summable physical increments yield nonnegative limiting marks inside
the same root-uniform total error budget at every sufficiently late splice.
-/

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- At one root-independent late-splice threshold, all guarded physical grafts
converge to nonnegative marks within the original complete error budget. -/
theorem eventually_physicalParametricGraftMark_limit {θ L δ : ℝ} {b : ℕ}
    (hθ : 0 < θ) (hθcap : θ ≤ 1 / 1000) (hb : 32 ^ 5 ≤ b) (hL : 0 < L) (hδ : 0 < δ) (hsmall : 2
      * δ ≤ 1)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) :
    ∀ᶠ t in atTop, ∀ root, 16 ^ b ≤ root → ∃ z : ℝ,
      0 ≤ z ∧ Tendsto (fun j => physicalParametricGraftMark θ L δ b t j root) atTop (𝓝 z) ∧
        |z - physicalSeedMark b t root| ≤ parametricTotalError θ L δ b t := by
  filter_upwards [eventually_physicalParametricGraftMark_continuation hθ hθcap hb hL hδ hsmall hpay,
    eventually_physicalParametricGraftMark_error hθ hθcap hb hL hδ hsmall hpay] with t hcont
      herr root hroot
  have hs : Summable (fun j =>
      dist (physicalParametricGraftMark θ L δ b t j root) (physicalParametricGraftMark θ L δ b t
        (j + 1) root)) := by
    simpa only [Real.dist_eq, abs_sub_comm] using (hcont root hroot).1.1
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete (cauchySeq_of_summable_dist hs)
  refine ⟨z, ?_, hz, ?_⟩
  · exact ge_of_tendsto hz (Eventually.of_forall fun j => physicalParametricGraftMark_nonneg θ L
    δ b t j root)
  · exact le_of_tendsto (hz.sub_const (physicalSeedMark b t root)).abs
      (Eventually.of_forall (herr root hroot))

end WordCertDensity.Construction
