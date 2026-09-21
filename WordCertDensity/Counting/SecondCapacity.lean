/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Finite second-moment capacity and positive source mass -/

namespace WordCertDensity.Counting
open scoped BigOperators

/-- Weighted Cauchy-Schwarz keeps the actual occupied mass. -/
theorem weighted_second_mass {ι : Type*} (S : Finset ι) (w h : ι → ℝ)
    (hw : ∀ i ∈ S, 0 ≤ w i) :
    (∑ i ∈ S, w i * h i) ^ 2 ≤ (∑ i ∈ S, w i) * ∑ i ∈ S, w i * h i ^ 2 := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S hw
    (fun i hi => mul_nonneg (hw i hi) (sq_nonneg (h i)))
  intro i _
  nlinarith [sq_nonneg (w i * h i)]

/-- A full-group moment ceiling and per-residue capacity bound the weighted marked square. -/
theorem finite_second_capacity (Q : ℕ) (w h : Fin Q → ℝ) (T B : ℝ)
    (hT : 0 ≤ T) (hw : ∀ i, 0 ≤ w i) (hcap : ∀ i, w i ≤ T / Q)
    (hB : (∑ i, h i ^ 2) / Q ≤ B) :
    (∑ i, w i * h i) ^ 2 ≤ (∑ i, w i) * (T * B) := by
  have he : (∑ i, w i * h i ^ 2) ≤ T * B := by
    calc
      _ ≤ ∑ i : Fin Q, (T / Q) * h i ^ 2 :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hcap i) (sq_nonneg _))
      _ = T * ((∑ i : Fin Q, h i ^ 2) / Q) := by rw [← Finset.mul_sum]; ring
      _ ≤ T * B := mul_le_mul_of_nonneg_left hB hT
  exact (weighted_second_mass Finset.univ w h (fun i _ => hw i)).trans
    (mul_le_mul_of_nonneg_left he (Finset.sum_nonneg (fun i _ => hw i)))

/-- Any guaranteed positive marked mass gives a concrete lower bound on occupied mass. -/
theorem second_capacity_mass_lower (Q : ℕ) (w h : Fin Q → ℝ) (T B p : ℝ)
    (hT : 0 < T) (hBpos : 0 < B) (hp : 0 ≤ p)
    (hw : ∀ i, 0 ≤ w i) (hh : ∀ i, 0 ≤ h i) (hcap : ∀ i, w i ≤ T / Q)
    (hB : (∑ i, h i ^ 2) / Q ≤ B) (hmarked : p ≤ ∑ i, w i * h i) :
    p ^ 2 / (T * B) ≤ ∑ i, w i := by
  apply (div_le_iff₀ (mul_pos hT hBpos)).2
  have hs : 0 ≤ ∑ i, w i * h i := Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hh i))
  have hc := finite_second_capacity Q w h T B hT.le hw hcap hB
  nlinarith

end WordCertDensity.Counting
