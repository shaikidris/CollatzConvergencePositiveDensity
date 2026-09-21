/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-! # Existence of a minimum for finite capped residue allocation -/

namespace WordCertDensity.Counting

/-- Feasible weights retain the per-residue cap and required marked mass. -/
def feasibleAllocation (Q : ℕ) (h : Fin Q → ℝ) (T p : ℝ) (w : Fin Q → ℝ) : Prop :=
  (∀ r, 0 ≤ w r ∧ w r ≤ T/Q) ∧ p ≤ ∑ r, w r*h r

/-- Finite capped allocation has a compact feasible region. -/
theorem feasibleAllocation_isCompact (Q : ℕ) (h : Fin Q → ℝ) (T p : ℝ) :
    IsCompact {w | feasibleAllocation Q h T p w} := by
  have hc : IsClosed {w : Fin Q → ℝ | p ≤ ∑ r, w r*h r} :=
    isClosed_le continuous_const (by fun_prop)
  have he : {w | feasibleAllocation Q h T p w} =
      Set.Icc (fun _ : Fin Q => (0 : ℝ)) (fun _ => T/Q) ∩
        {w | p ≤ ∑ r, w r*h r} := by
    ext w
    simp only [feasibleAllocation, Set.mem_ofPred_eq, Set.mem_inter_iff,
      Set.mem_Icc, Pi.le_def, forall_and]
  rw [he]
  exact isCompact_Icc.inter_right hc

/-- Every feasible finite allocation problem attains its minimum occupied mass. -/
theorem feasibleAllocation_exists_min (Q : ℕ) (h : Fin Q → ℝ) (T p : ℝ)
    (hne : ∃ w, feasibleAllocation Q h T p w) :
    ∃ w, feasibleAllocation Q h T p w ∧
      ∀ v, feasibleAllocation Q h T p v → (∑ r, w r) ≤ ∑ r, v r := by
  obtain ⟨w, hw, hmin⟩ := (feasibleAllocation_isCompact Q h T p).exists_isMinOn
    hne (show ContinuousOn (fun w : Fin Q → ℝ => ∑ r, w r) _ by fun_prop)
  exact ⟨w, hw, fun v hv => hmin hv⟩

/-- The uniform fractional allocation is feasible throughout the full mean-capacity range. -/
theorem feasibleAllocation_uniform (Q : ℕ) (h : Fin Q → ℝ) (μ T p : ℝ)
    (hQ : 0 < Q) (hμ : 0 < μ) (hp : 0 ≤ p) (hpaid : p ≤ T*μ)
    (hmean : (∑ r, h r)/Q = μ) :
    feasibleAllocation Q h T p (fun _ => (p/μ)/Q) ∧
      (∑ _ : Fin Q, (p/μ)/Q) = p/μ := by
  have hq : (0 : ℝ) < Q := Nat.cast_pos.mpr hQ
  have hs : (∑ r, h r) = μ*Q := (div_eq_iff hq.ne').1 hmean
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro r
    exact ⟨by positivity, div_le_div_of_nonneg_right ((div_le_iff₀ hμ).2 hpaid) hq.le⟩
  · rw [← Finset.mul_sum, hs]
    have he : (p/μ)/Q*(μ*Q) = p := by field_simp
    exact he.ge
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

end WordCertDensity.Counting
