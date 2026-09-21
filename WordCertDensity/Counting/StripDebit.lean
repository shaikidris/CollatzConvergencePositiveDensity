/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Counting.Harmonic
public import WordCertDensity.Counting.OddBand
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Finite harmonic debit when a larger shell is trimmed to radius sixteen -/

@[expose] public section

namespace WordCertDensity.Counting

open scoped BigOperators

/-- An initial closed strip pays one boundary reciprocal and half its logarithmic width. -/
theorem strip_harmonic_upper (S : Finset ℕ) (a : ℕ → ℝ) {X Z : ℝ}
    (hX : 0 < X) (hXZ : X ≤ Z)
    (hS : ∀ x ∈ S, Odd x ∧ X ≤ (x : ℝ) ∧ a x ≤ (x : ℝ)⁻¹) :
    (∑ x ∈ S.filter (fun x : ℕ => (x : ℝ) ≤ Z), a x) ≤
      1 / X + (Real.log Z - Real.log X) / 2 := by
  classical
  have hs := sum_inv_le_log_of_separated (S.filter (fun x : ℕ => (x : ℝ) ≤ Z))
    hX (by norm_num : (0 : ℝ) < 2) hXZ
    (fun x hx => ⟨(hS x (Finset.mem_filter.mp hx).1).2.1, (Finset.mem_filter.mp hx).2⟩)
    (by
      intro x hx y hy hxy
      have hg := odd_residue_spacing (by decide : Odd 1)
        (hS x (Finset.mem_filter.mp hx).1).1 (hS y (Finset.mem_filter.mp hy).1).1 hxy
        (Subsingleton.elim (x : ZMod 1) (y : ZMod 1))
      norm_num at hg
      exact_mod_cast hg)
  exact (Finset.sum_le_sum (fun x hx => (hS x (Finset.mem_filter.mp hx).1).2.2)).trans
    (by simpa only [one_div] using hs)

/-- Removing the lower boundary as well as the strip retains the complementary marked mass. -/
theorem retained_mass_after_strip (S : Finset ℕ) (a : ℕ → ℝ) {X Z u : ℝ}
    (hX : 0 < X) (hXZ : X ≤ Z)
    (hS : ∀ x ∈ S, Odd x ∧ X ≤ (x : ℝ) ∧ a x ≤ (x : ℝ)⁻¹)
    (hm : u ≤ ∑ x ∈ S, a x) :
    u - (1 / X + (Real.log Z - Real.log X) / 2) ≤
      ∑ x ∈ S.filter (fun x : ℕ => Z < (x : ℝ)), a x := by
  classical
  have hs := strip_harmonic_upper S a hX hXZ hS
  have he := Finset.sum_filter_add_sum_filter_not S (fun x : ℕ => (x : ℝ) ≤ Z) a
  simp only [not_le] at he
  linarith

/-- The exact logarithmic width of the removed strip at a fixed shell index. -/
theorem radial_strip_width {Y R : ℝ} (hY : 0 < Y) (hR : 0 < R) (j : ℕ) :
    Real.log (Y / (16 : ℝ) ^ j) - Real.log (Y / R ^ j) =
      j * Real.log (R / 16) := by
  rw [Real.log_div (ne_of_gt hY) (by positivity),
    Real.log_div (ne_of_gt hY) (by positivity),
    Real.log_div (ne_of_gt hR) (by norm_num)]
  simp only [Real.log_pow]
  ring

/-- The finite strip error has exactly the printed logarithmic debit and a vanishing boundary. -/
theorem radial_strip_debit (S : Finset ℕ) (a : ℕ → ℝ) {Y R u : ℝ} (j : ℕ)
    (hY : 0 < Y) (hR : 16 ≤ R)
    (hS : ∀ x ∈ S, Odd x ∧ Y / R ^ j ≤ (x : ℝ) ∧ a x ≤ (x : ℝ)⁻¹)
    (hm : u ≤ ∑ x ∈ S, a x) :
    u - (j / 2 * Real.log (R / 16) + R ^ j / Y) ≤
      ∑ x ∈ S.filter (fun x : ℕ => Y / (16 : ℝ) ^ j < (x : ℝ)), a x := by
  have hRp : 0 < R := by linarith
  have hXZ : Y / R ^ j ≤ Y / (16 : ℝ) ^ j :=
    div_le_div_of_nonneg_left hY.le (by positivity)
      (pow_le_pow_left₀ (by norm_num) hR j)
  have h := retained_mass_after_strip S a (div_pos hY (by positivity)) hXZ hS hm
  rw [radial_strip_width hY hRp] at h
  have he : 1 / (Y / R ^ j) + (j : ℝ) * Real.log (R / 16) / 2 =
      j / 2 * Real.log (R / 16) + R ^ j / Y := by
    simp only [div_div_eq_mul_div, one_mul]
    ring
  rwa [he] at h

/-- Multiplication by the radius cancels one shell exponent, at a real cutoff. -/
theorem shell_upper_eq {Y R : ℝ} (hR : R ≠ 0) (j : ℕ) :
    R * (Y / R ^ (j + 1)) = Y / R ^ j := by
  rw [pow_succ]
  field_simp

/-- Trimming a larger shell places every retained odd source in the exact open band. -/
theorem retained_mem_oddOpenBand {Y R : ℝ} {j x : ℕ} (hY : 0 < Y) (hR : 16 ≤ R)
    (hj : 1 ≤ j) (hx : Odd x) (hl : Y / (16 : ℝ) ^ j < (x : ℝ))
    (hu : (x : ℝ) < R * (Y / R ^ j)) :
    x ∈ oddOpenBand (Y / (16 : ℝ) ^ j) 16 := by
  apply (mem_oddOpenBand _ _ x).mpr
  refine ⟨hx, hl, hu.trans_le ?_⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  rw [shell_upper_eq (by linarith : R ≠ 0),
    shell_upper_eq (by norm_num : (16 : ℝ) ≠ 0)]
  exact div_le_div_of_nonneg_left hY.le (by positivity)
    (pow_le_pow_left₀ (by norm_num) hR k)

end WordCertDensity.Counting
