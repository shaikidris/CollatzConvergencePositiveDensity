/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith

/-! # Eventual interval coverage without endpoint monotonicity -/

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- An upper-endpoint sequence tending to infinity reaches every real cutoff. -/
theorem interval_upper_exists {upper : ℕ → ℝ} (hu : Tendsto upper atTop atTop) (X : ℝ) :
    ∃ j, X ≤ upper j := (hu.eventually (eventually_ge_atTop X)).exists

/-- The first upper endpoint reaching the cutoff; no monotonicity is assumed. -/
noncomputable def intervalStage (upper : ℕ → ℝ) (hu : Tendsto upper atTop atTop) (X : ℝ) : ℕ :=
  Nat.find (interval_upper_exists hu X)

/-- The chosen interval reaches the requested upper edge. -/
theorem intervalStage_spec {upper : ℕ → ℝ} (hu : Tendsto upper atTop atTop) (X : ℝ) :
    X ≤ upper (intervalStage upper hu X) := Nat.find_spec (interval_upper_exists hu X)

/-- The selected index escapes every finite prefix as the cutoff tends to infinity. -/
theorem intervalStage_tendsto {upper : ℕ → ℝ} (hu : Tendsto upper atTop atTop) :
    Tendsto (intervalStage upper hu) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_gt_atTop (∑ i ∈ Finset.range n, |upper i|)] with X hX
  by_contra hn
  have hi : intervalStage upper hu X ∈ Finset.range n := Finset.mem_range.mpr (by omega)
  have hs := Finset.single_le_sum (fun i _ => abs_nonneg (upper i)) hi
  have hx := intervalStage_spec hu X
  have ha := le_abs_self (upper (intervalStage upper hu X))
  linarith

/-- Eventual consecutive overlap covers all large cutoffs with a diverging stage selector. -/
theorem interval_eventual_coverage (lower upper : ℕ → ℝ)
    (hu : Tendsto upper atTop atTop)
    (hoverlap : ∀ᶠ j : ℕ in atTop, lower (j+1) ≤ upper j) :
    ∃ stage : ℝ → ℕ, Tendsto stage atTop atTop ∧
      ∀ᶠ X : ℝ in atTop, lower (stage X) < X ∧ X ≤ upper (stage X) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hoverlap
  refine ⟨intervalStage upper hu, intervalStage_tendsto hu, ?_⟩
  filter_upwards [(intervalStage_tendsto hu).eventually (eventually_ge_atTop (N+1))] with X hstage
  have hprev : ¬ X ≤ upper (intervalStage upper hu X-1) :=
    Nat.find_min (interval_upper_exists hu X)
      (by change intervalStage upper hu X-1 < intervalStage upper hu X; omega)
  have ho := hN (intervalStage upper hu X-1) (by omega)
  have he : intervalStage upper hu X-1+1 = intervalStage upper hu X := by omega
  rw [he] at ho
  exact ⟨ho.trans_lt (lt_of_not_ge hprev), intervalStage_spec hu X⟩

end WordCertDensity.Construction
