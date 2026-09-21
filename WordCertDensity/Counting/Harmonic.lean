/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Counting.SeparatedHarmonic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Harmonic capacity of actual odd sources

Odd representatives in one class modulo an odd modulus have spacing at least
twice the modulus. The finite reciprocal sum retains its first-point term.
Grouping actual weights by residue then bounds every nonnegative residue test.
-/

@[expose] public section

namespace WordCertDensity.Counting

open scoped BigOperators

/-- Distinct odd representatives of one class have the full twice-modulus gap. -/
theorem odd_residue_spacing {Q x y : ℕ} (hQ : Odd Q) (hx : Odd x) (hy : Odd y)
    (hxy : x < y) (hres : (x : ZMod Q) = y) : x + 2 * Q ≤ y := by
  have hmod : Q ∣ y - x := ((ZMod.natCast_eq_natCast_iff x y Q).mp hres).dvd'
  have htwo : 2 ∣ y - x := (hy.tsub_odd hx).two_dvd
  have hdiv : 2 * Q ∣ y - x := hQ.coprime_two_left.mul_dvd_of_dvd_of_dvd htwo hmod
  have := Nat.le_of_dvd (Nat.sub_pos_of_lt hxy) hdiv
  omega

/-- The exact finite bound for a weighted subset of one odd residue class. -/
theorem odd_residue_capacity (Q : ℕ) (X R : ℝ) (S : Finset ℕ) (a : ℕ → ℝ)
    (hQ : 0 < Q) (hQodd : Odd Q) (hX : 0 < X) (hR : 1 < R)
    (hdata : ∀ x ∈ S, Odd x ∧ X ≤ (x : ℝ) ∧ (x : ℝ) < R * X ∧
      0 ≤ a x ∧ a x ≤ (x : ℝ)⁻¹) (r : ZMod Q) :
    (∑ x ∈ S.filter (fun x : ℕ => (x : ZMod Q) = r), a x) ≤
      1 / X + Real.log R / (2 * Q) := by
  classical
  have hδ : (0 : ℝ) < 2 * Q := by positivity
  have hbound := sum_inv_le_log_of_separated
    (S.filter (fun x : ℕ => (x : ZMod Q) = r)) hX hδ (by nlinarith : X ≤ R * X)
    (fun x hx => ⟨(hdata x (Finset.mem_filter.mp hx).1).2.1,
      (hdata x (Finset.mem_filter.mp hx).1).2.2.1.le⟩)
    (by
      intro x hx y hy hxy
      have hxS := Finset.mem_filter.mp hx
      have hyS := Finset.mem_filter.mp hy
      have hgap := odd_residue_spacing hQodd (hdata x hxS.1).1 (hdata y hyS.1).1
        hxy (hxS.2.trans hyS.2.symm)
      exact_mod_cast hgap)
  calc
    _ ≤ ∑ x ∈ S.filter (fun x : ℕ => (x : ZMod Q) = r), (x : ℝ)⁻¹ :=
      Finset.sum_le_sum (fun x hx => (hdata x (Finset.mem_filter.mp hx).1).2.2.2.2)
    _ ≤ X⁻¹ + (Real.log (R * X) - Real.log X) / (2 * Q) := hbound
    _ = _ := by rw [Real.log_mul (by linarith) (ne_of_gt hX)]; simp [one_div]

/-- The manuscript's coefficient form keeps the finite boundary term Q/X. -/
theorem odd_residue_capacity_coefficient (Q : ℕ) (X R : ℝ) (S : Finset ℕ) (a : ℕ → ℝ)
    (hQ : 0 < Q) (hQodd : Odd Q) (hX : 0 < X) (hR : 1 < R)
    (hdata : ∀ x ∈ S, Odd x ∧ X ≤ (x : ℝ) ∧ (x : ℝ) < R * X ∧
      0 ≤ a x ∧ a x ≤ (x : ℝ)⁻¹) (r : ZMod Q) :
    0 ≤ (∑ x ∈ S.filter (fun x : ℕ => (x : ZMod Q) = r), a x) ∧
      (∑ x ∈ S.filter (fun x : ℕ => (x : ZMod Q) = r), a x) ≤
        ((Q : ℝ) / X + Real.log R / 2) / Q := by
  classical
  refine ⟨Finset.sum_nonneg (fun x hx => (hdata x (Finset.mem_filter.mp hx).1).2.2.2.1), ?_⟩
  have heq : ((Q : ℝ) / X + Real.log R / 2) / Q =
      1 / X + Real.log R / (2 * Q) := by
    have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hQ
    field_simp [hQr, ne_of_gt hX]
  rw [heq]
  exact odd_residue_capacity Q X R S a hQ hQodd hX hR hdata r

/-- Exact grouping of a finite physical weighted test by its residue. -/
theorem sum_residue_test {Q : ℕ} [NeZero Q] (S : Finset ℕ) (a : ℕ → ℝ)
    (ψ : ZMod Q → ℝ) :
    (∑ x ∈ S, a x * ψ (x : ZMod Q)) =
      ∑ r : ZMod Q, (∑ x ∈ S.filter (fun x : ℕ => (x : ZMod Q) = r), a x) * ψ r := by
  classical
  have hmaps : ∀ x ∈ S, (x : ZMod Q) ∈ (Finset.univ : Finset (ZMod Q)) :=
    fun _ _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun x => a x * ψ (x : ZMod Q))]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x hx
  rw [(Finset.mem_filter.mp hx).2]

/-- Every nonnegative residue test is controlled by its full-group mean. -/
theorem odd_harmonic_test (Q : ℕ) [NeZero Q] (X R : ℝ) (S : Finset ℕ) (a : ℕ → ℝ)
    (hQ : 0 < Q) (hQodd : Odd Q) (hX : 0 < X) (hR : 1 < R)
    (hdata : ∀ x ∈ S, Odd x ∧ X ≤ (x : ℝ) ∧ (x : ℝ) < R * X ∧
      0 ≤ a x ∧ a x ≤ (x : ℝ)⁻¹) (ψ : ZMod Q → ℝ) (hψ : ∀ r, 0 ≤ ψ r) :
    (∑ x ∈ S, a x * ψ (x : ZMod Q)) ≤
      ((Q : ℝ) / X + Real.log R / 2) * ((∑ r : ZMod Q, ψ r) / Q) := by
  classical
  rw [sum_residue_test]
  calc
    _ ≤ ∑ r : ZMod Q, (((Q : ℝ) / X + Real.log R / 2) / Q) * ψ r :=
      Finset.sum_le_sum (fun r _ => mul_le_mul_of_nonneg_right
        (odd_residue_capacity_coefficient Q X R S a hQ hQodd hX hR hdata r).2 (hψ r))
    _ = _ := by rw [← Finset.mul_sum]; ring

end WordCertDensity.Counting
