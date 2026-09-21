/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # Attained weighted allocation on a finite capped root family

The objective is minimized over every cap-constrained vector with the required
total mass. The physical persistent vector is a later feasible input, not the
definition of this minimum. This module supplies R.score's finite optimization
core and the common-vector interface for RP03.
-/

namespace WordCertDensity.Roots

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- The capped feasible set with total mass at least the prescribed value. -/
def allocationFeasible (B m : ℝ) : Set (ι → ℝ) :=
  Set.Icc (fun _ => 0) (fun _ => B) ∩ {v | m ≤ ∑ i, v i}

/-- The weighted allocation objective; root applications use reciprocal costs. -/
def allocationObjective (cost v : ι → ℝ) : ℝ := ∑ i, cost i * v i

/-- The infimum of all feasible objectives, shown attained below. -/
noncomputable def allocationScore (cost : ι → ℝ) (B m : ℝ) : ℝ :=
  sInf (allocationObjective cost '' allocationFeasible B m)

/-- The finite capped feasible set is compact. -/
theorem allocationFeasible_compact (B m : ℝ) :
    IsCompact (allocationFeasible (ι := ι) B m) := by
  have hc : Continuous (fun v : ι → ℝ => ∑ i, v i) := by fun_prop
  exact isCompact_Icc.inter_right (isClosed_le continuous_const hc)

/-- Full-cap allocation witnesses feasibility whenever the total capacity suffices. -/
theorem allocationFeasible_nonempty {B m : ℝ} (hB : 0 ≤ B)
    (hm : m ≤ (Fintype.card ι : ℝ) * B) :
    (allocationFeasible (ι := ι) B m).Nonempty := by
  refine ⟨fun _ => B, ⟨⟨fun _ => hB, fun _ => le_rfl⟩, ?_⟩⟩
  change m ≤ ∑ _ : ι, B
  simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hm

/-- The finite weighted objective is continuous. -/
theorem allocationObjective_continuous (cost : ι → ℝ) :
    Continuous (allocationObjective cost) := by
  unfold allocationObjective
  fun_prop

/-- The score is attained by an actual feasible vector, for arbitrary real costs. -/
theorem allocationScore_attained (cost : ι → ℝ) {B m : ℝ} (hB : 0 ≤ B)
    (hm : m ≤ (Fintype.card ι : ℝ) * B) :
    ∃ v ∈ allocationFeasible B m, allocationScore cost B m = allocationObjective cost v ∧
      ∀ w ∈ allocationFeasible B m, allocationObjective cost v ≤ allocationObjective cost w := by
  obtain ⟨v, hv, hmin⟩ := (allocationFeasible_compact B m).exists_isMinOn
    (allocationFeasible_nonempty hB hm) (allocationObjective_continuous cost).continuousOn
  have hleast : IsLeast (allocationObjective cost '' allocationFeasible B m)
      (allocationObjective cost v) := by
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    exact hmin hw
  exact ⟨v, hv, hleast.csInf_eq, fun w hw => hmin hw⟩

/-- Every feasible physical vector supplies an upper bound for the allocation minimum. -/
theorem allocationScore_le (cost : ι → ℝ) {B m : ℝ} (hB : 0 ≤ B)
    (hm : m ≤ (Fintype.card ι : ℝ) * B) {v : ι → ℝ}
    (hv : v ∈ allocationFeasible B m) :
    allocationScore cost B m ≤ allocationObjective cost v := by
  obtain ⟨w, _, heq, hmin⟩ := allocationScore_attained cost hB hm
  rw [heq]
  exact hmin v hv

/-- A uniform nonnegative cost lower bound prices the entire required mass. -/
theorem allocationScore_lower (cost : ι → ℝ) {B m c : ℝ} (hB : 0 ≤ B)
    (hm : m ≤ (Fintype.card ι : ℝ) * B) (hc : 0 ≤ c) (hcost : ∀ i, c ≤ cost i) :
    c * m ≤ allocationScore cost B m := by
  obtain ⟨v, hv, heq, _⟩ := allocationScore_attained cost hB hm
  rw [heq]
  calc
    _ ≤ c * ∑ i, v i := mul_le_mul_of_nonneg_left hv.2 hc
    _ = ∑ i, c * v i := Finset.mul_sum _ _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hcost i) (hv.1.1 i)

/-- Positive required mass and a positive cost floor give a strictly positive score. -/
theorem allocationScore_pos (cost : ι → ℝ) {B m c : ℝ} (hB : 0 ≤ B)
    (hm : m ≤ (Fintype.card ι : ℝ) * B) (hc : 0 < c) (hcost : ∀ i, c ≤ cost i)
    (hmpos : 0 < m) : 0 < allocationScore cost B m :=
  (mul_pos hc hmpos).trans_le (allocationScore_lower cost hB hm hc.le hcost)

/-- Increasing the required mass cannot decrease the allocation minimum. -/
theorem allocationScore_mono_mass (cost : ι → ℝ) {B m₁ m₂ : ℝ} (hB : 0 ≤ B)
    (hm : m₂ ≤ (Fintype.card ι : ℝ) * B) (hle : m₁ ≤ m₂) :
    allocationScore cost B m₁ ≤ allocationScore cost B m₂ := by
  obtain ⟨v, hv, heq, _⟩ := allocationScore_attained cost hB hm
  rw [heq]
  exact allocationScore_le cost hB (hle.trans hm) ⟨hv.1, hle.trans hv.2⟩

end WordCertDensity.Roots
