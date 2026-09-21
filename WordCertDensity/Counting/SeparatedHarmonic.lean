/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite harmonic sums with a separation bound

All but the first point are paid for by consecutive logarithmic increments.
The first reciprocal retains the finite boundary term.
-/

@[expose] public section

namespace WordCertDensity.Counting

open scoped BigOperators

/-- A positive gap pays for the reciprocal at its right endpoint. -/
theorem inv_le_log_gap {a b δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hgap : a + δ ≤ b) : b⁻¹ ≤ (Real.log b - Real.log a) / δ := by
  have hb : 0 < b := by linarith
  have hlog := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)] at hlog
  have hratio : (b - a) / b ≤ Real.log b - Real.log a := by
    rw [sub_div, div_self (ne_of_gt hb)]
    linarith
  apply (le_div_iff₀ hδ).mpr
  calc
    b⁻¹ * δ = δ / b := by rw [div_eq_mul_inv, mul_comm]
    _ ≤ (b - a) / b := div_le_div_of_nonneg_right (by linarith) hb.le
    _ ≤ _ := hratio

/-- A separated finite set has a logarithmic harmonic bound with one boundary term. -/
theorem sum_inv_le_log_of_separated (S : Finset ℕ) {X Y δ : ℝ}
    (hX : 0 < X) (hδ : 0 < δ) (hXY : X ≤ Y)
    (hmem : ∀ x ∈ S, X ≤ (x : ℝ) ∧ (x : ℝ) ≤ Y)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x < y → (x : ℝ) + δ ≤ y) :
    (∑ x ∈ S, (x : ℝ)⁻¹) ≤ X⁻¹ + (Real.log Y - Real.log X) / δ := by
  classical
  induction S using Finset.induction_on_max generalizing Y with
  | empty =>
    simp only [Finset.sum_empty]
    have hlog : Real.log X ≤ Real.log Y := Real.log_le_log hX hXY
    exact add_nonneg (inv_nonneg.mpr hX.le) (div_nonneg (sub_nonneg.mpr hlog) hδ.le)
  | insert a S hmax ih =>
    have ha : a ∉ S := fun ha => (hmax a ha).false
    have haX := (hmem a (Finset.mem_insert_self a S)).1
    have haY := (hmem a (Finset.mem_insert_self a S)).2
    have hapos : (0 : ℝ) < a := hX.trans_le haX
    rw [Finset.sum_insert ha]
    rcases S.eq_empty_or_nonempty with rfl | hS
    · simp only [Finset.sum_empty, add_zero]
      have hlog : 0 ≤ (Real.log Y - Real.log X) / δ :=
        div_nonneg (sub_nonneg.mpr (Real.log_le_log hX hXY)) hδ.le
      exact (inv_anti₀ hX haX).trans (le_add_of_nonneg_right hlog)
    · let b := S.max' hS
      have hbS : b ∈ S := Finset.max'_mem S hS
      have hbX : X ≤ (b : ℝ) := (hmem b (Finset.mem_insert_of_mem hbS)).1
      have hbound := ih hbX
        (fun x hx => ⟨(hmem x (Finset.mem_insert_of_mem hx)).1,
          by exact_mod_cast Finset.le_max' S x hx⟩)
        (fun x hx y hy hxy => hsep x (Finset.mem_insert_of_mem hx)
          y (Finset.mem_insert_of_mem hy) hxy)
      have hstep := inv_le_log_gap (hX.trans_le hbX) hδ
        (hsep b (Finset.mem_insert_of_mem hbS) a (Finset.mem_insert_self a S) (hmax b hbS))
      have hlog := div_le_div_of_nonneg_right
        (sub_le_sub_right (Real.log_le_log hapos haY) (Real.log X)) hδ.le
      calc
        _ ≤ (Real.log a - Real.log b) / δ +
            (X⁻¹ + (Real.log b - Real.log X) / δ) := add_le_add hstep hbound
        _ = X⁻¹ + (Real.log a - Real.log X) / δ := by ring
        _ ≤ _ := add_le_add le_rfl hlog

end WordCertDensity.Counting
