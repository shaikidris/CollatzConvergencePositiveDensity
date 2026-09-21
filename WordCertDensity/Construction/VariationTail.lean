/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.SeedTail

/-! # The complete variation tail at a finite startup stage

The analytic tail decreases to zero. The explicit rational formula and the
finite arithmetic search bound are separate subsequent obligations.
-/

namespace WordCertDensity.Construction

open Filter Topology

/-- The complete cubic geometric tail, including its initial term. -/
noncomputable def seedVariationTail (N : ℕ) : ℝ :=
  ∑' m, seedVariationTerm (N + m)

/-- Every shifted tail is an absolutely convergent real series. -/
theorem summable_seedVariationTail (N : ℕ) :
    Summable (fun m => seedVariationTerm (N + m)) :=
  summable_seedVariationTerm.comp_injective (fun _ _ h => Nat.add_left_cancel h)

/-- The tail loses exactly its initial term when the startup advances. -/
theorem seedVariationTail_step (N : ℕ) :
    seedVariationTail N = seedVariationTerm N + seedVariationTail (N + 1) := by
  have h := (summable_seedVariationTail N).tsum_eq_zero_add
  simpa [seedVariationTail, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Each summand is strictly positive at the literal variation rate. -/
theorem seedVariationTerm_pos (N : ℕ) : 0 < seedVariationTerm N := by
  unfold seedVariationTerm
  exact mul_pos (pow_pos (by positivity) 3)
    (pow_pos seedVariationRate_contracts.1 N)

/-- The complete tail is nonnegative. -/
theorem seedVariationTail_nonneg (N : ℕ) : 0 ≤ seedVariationTail N :=
  tsum_nonneg fun m => (seedVariationTerm_pos (N + m)).le

/-- Removing a positive initial term strictly decreases the complete tail. -/
theorem seedVariationTail_strictAnti : StrictAnti seedVariationTail := by
  apply strictAnti_nat_of_succ_lt
  intro N
  have h := seedVariationTail_step N
  have hp := seedVariationTerm_pos N
  linarith

/-- The entire future variation tail tends to zero. -/
theorem seedVariationTail_tendsto_zero :
    Tendsto seedVariationTail atTop (𝓝 0) := by
  change Tendsto (fun N => ∑' m, seedVariationTerm (N + m)) atTop (𝓝 0)
  simpa only [Nat.add_comm] using
    (tendsto_sum_nat_add (f := seedVariationTerm))

/-- Any fixed scalar multiple of the complete tail eventually fits a positive budget. -/
theorem seedVariationTail_eventually_lt (A : ℝ) {budget : ℝ} (hbudget : 0 < budget) :
    ∀ᶠ N : ℕ in atTop, A * seedVariationTail N < budget := by
  have h := seedVariationTail_tendsto_zero.const_mul A
  have hzero : A * (0 : ℝ) < budget := by simpa using hbudget
  exact h.eventually_lt_const hzero

/-- One startup controls all later marks at every root above the height guard. -/
theorem exists_uniform_seedVariation_startup {b : ℕ} (hb : 32 ^ 5 ≤ b)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 16 ≤ N ∧ ∀ root : ℕ, 16 ^ b ≤ root →
      ∀ n : ℕ, N ≤ n →
        |physicalSeedMark b n root - physicalSeedMark b N root| < ε := by
  obtain ⟨N, hN, hsmall⟩ :=
    ((eventually_ge_atTop (16 : ℕ)).and
      (seedVariationTail_eventually_lt (seedVariationCoefficient b) hε)).exists
  refine ⟨N, hN, ?_⟩
  intro root hr n hn
  exact (physicalSeedMark_finite_tail hb hr hn).trans_lt hsmall

end WordCertDensity.Construction
