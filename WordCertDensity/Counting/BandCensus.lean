/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Counting.OddBand
public import WordCertDensity.Counting.Harmonic
public import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Explicit odd-band harmonic and cardinality errors -/

@[expose] public section

namespace WordCertDensity.Counting

open scoped BigOperators

/-- Logarithmic growth is bounded by the relative length at its left endpoint. -/
theorem log_sub_le_div_gap {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log b - Real.log a ≤ (b - a) / a := by
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div (ne_of_gt hb) (ne_of_gt ha)] at h
  simpa only [sub_div, div_self (ne_of_gt ha)] using h

/-- Exact odd-band summation uses the consecutive index interval. -/
theorem sum_oddOpenBand {X s : ℝ} (hX : 1 ≤ X) (f : ℕ → ℝ) :
    (∑ x ∈ oddOpenBand X s, f x) =
      ∑ n ∈ Finset.Ico (oddBandLowerIndex X) (oddBandUpperIndex X s), f (2 * n + 1) := by
  classical
  rw [oddOpenBand_eq_image hX, Finset.sum_image]
  intro a _ b _ hab
  dsimp at hab
  omega

/-- Consecutive odd reciprocals pay for the full logarithmic interval to the next odd point. -/
theorem odd_index_log_le_sum {A B : ℕ} (hAB : A ≤ B) :
    Real.log (2 * (B : ℝ) + 1) - Real.log (2 * (A : ℝ) + 1) ≤
      2 * ∑ n ∈ Finset.Ico A B, (2 * (n : ℝ) + 1)⁻¹ := by
  induction B, hAB using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
    rw [Finset.sum_Ico_succ_top hAB]
    have hstep := log_sub_le_div_gap
      (by positivity : (0 : ℝ) < 2 * B + 1)
      (by positivity : (0 : ℝ) < 2 * (B + 1) + 1)
    have hgap : (2 * ((B : ℝ) + 1) + 1 - (2 * B + 1)) / (2 * B + 1) =
        2 * (2 * (B : ℝ) + 1)⁻¹ := by ring
    rw [hgap] at hstep
    push_cast
    linarith

/-- The upper harmonic estimate retains the boundary reciprocal at the real lower cutoff. -/
theorem oddOpenBand_harmonic_upper {X s : ℝ} (hX : 1 ≤ X) (hs : 1 < s) :
    (∑ x ∈ oddOpenBand X s, (x : ℝ)⁻¹) ≤ Real.log s / 2 + 1 / X := by
  have hp : 0 < X := by linarith
  have h := odd_residue_capacity 1 X s (oddOpenBand X s) (fun x => (x : ℝ)⁻¹)
    (by decide) (by decide) hp hs (by
      intro x hx
      obtain ⟨ho, hl, hu⟩ := (mem_oddOpenBand X s x).mp hx
      exact ⟨ho, hl.le, hu, inv_nonneg.mpr (by positivity), le_rfl⟩) 0
  have hf : (oddOpenBand X s).filter (fun x : ℕ => (x : ZMod 1) = 0) =
      oddOpenBand X s := by
    classical
    exact Finset.filter_eq_self.mpr (fun x _ => Subsingleton.elim _ _)
  rw [hf] at h
  simpa [add_comm] using h

/-- The lower harmonic estimate pays at most one reciprocal for the strict lower boundary. -/
theorem oddOpenBand_harmonic_lower {X s : ℝ} (hX : 1 ≤ X) (hs : 1 < s) :
    Real.log s / 2 - 1 / X ≤ ∑ x ∈ oddOpenBand X s, (x : ℝ)⁻¹ := by
  have hp : 0 < X := by linarith
  have hspos : 0 < s := by linarith
  have hl := oddBand_lower_bounds hX
  have hu := oddBand_upper_bounds hX hs
  push_cast at hl hu
  have ht := odd_index_log_le_sum (oddBand_indices_le hX hs)
  have hfirst : Real.log (2 * (oddBandLowerIndex X : ℝ) + 1) - Real.log X ≤ 2 / X := by
    calc
      _ ≤ (2 * (oddBandLowerIndex X : ℝ) + 1 - X) / X :=
        log_sub_le_div_gap hp (by positivity)
      _ ≤ 2 / X := div_le_div_of_nonneg_right (by linarith [hl.2]) hp.le
  have hlast := Real.log_le_log (mul_pos hspos hp) hu.1
  rw [Real.log_mul (ne_of_gt hspos) (ne_of_gt hp)] at hlast
  rw [sum_oddOpenBand hX]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [show 2 / X = 2 * (1 / X) by ring] at hfirst
  linarith

/-- The full odd-band harmonic error is bounded by the reciprocal cutoff. -/
theorem oddOpenBand_harmonic_error {X s : ℝ} (hX : 1 ≤ X) (hs : 1 < s) :
    |(∑ x ∈ oddOpenBand X s, (x : ℝ)⁻¹) - Real.log s / 2| ≤ 1 / X := by
  rw [abs_le]
  constructor
  · linarith [oddOpenBand_harmonic_lower hX hs]
  · linarith [oddOpenBand_harmonic_upper hX hs]

/-- One explicit constant works for both census errors for every fixed radius greater than one. -/
theorem oddBandCensus (s : ℝ) (hs : 1 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, 1 ≤ X →
      |(∑ x ∈ oddOpenBand X s, (x : ℝ)⁻¹) - Real.log s / 2| ≤ C / X ∧
      |((oddOpenBand X s).card : ℝ) - (s - 1) * X / 2| ≤ C := by
  exact ⟨1, by norm_num, fun X hX =>
    ⟨oddOpenBand_harmonic_error hX hs, card_oddOpenBand_error hX hs⟩⟩

end WordCertDensity.Counting
