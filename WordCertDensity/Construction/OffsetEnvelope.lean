/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.Schedule
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Accumulated contraction and a finite offset envelope

Positive letters give C_w <= (3/2)^depth-1. The global precision makes each
block envelope polynomial in its actual index. The contraction (1/8)^(i-1)
is retained before summation. An explicit, deliberately coarse geometric
majorant supplies effective truncation of the manuscript's C_infinity.
-/

@[expose] public section

namespace WordCertDensity.Construction

/-- Positive valuations bound every word offset; no first-crossing premise is needed. -/
theorem word_offset_le_depth (w : ValuationWord) :
    w.offset ≤ (3 / 2 : ℚ) ^ w.length - 1 := by
  induction w with
  | nil => norm_num [ValuationWord.offset]
  | cons k w ih =>
      have hd : (2 : ℚ) ≤ 2 ^ (k : ℕ) := by
        simpa using pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) k.pos
      have hp : (0 : ℚ) < 2 ^ (k : ℕ) := by positivity
      have h1 : (1 : ℚ) / 2 ^ (k : ℕ) ≤ 1 / 2 := by
        apply (div_le_div_iff₀ hp (by norm_num)).mpr
        linarith
      have h3 : (3 : ℚ) / 2 ^ (k : ℕ) ≤ 3 / 2 := by
        apply (div_le_div_iff₀ hp (by norm_num)).mpr
        linarith
      have hm := mul_le_mul_of_nonneg_right h3 (ValuationWord.offset_nonneg w)
      have hi := mul_le_mul_of_nonneg_left ih (by norm_num : (0 : ℚ) ≤ 3 / 2)
      simp only [ValuationWord.offset, List.length_cons, pow_succ]
      linarith

/-- Strict total precision gives the literal depth-minus-one scheduled offset bound. -/
theorem scheduledWord_offset_bounds (i : ℕ) {w : ValuationWord}
    (hw : w ∈ stoppedWords (continuationPrecision i)) :
    0 ≤ (w.offset : ℝ) ∧
      (w.offset : ℝ) ≤ (3 / 2 : ℝ) ^ (continuationPrecision i - 1) - 1 := by
  have hc : (w.offset : ℝ) ≤ (3 / 2 : ℝ) ^ w.length - 1 := by
    have h : (w.offset : ℝ) ≤ (((3 / 2 : ℚ) ^ w.length - 1 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (word_offset_le_depth w)
    norm_num only [Rat.cast_sub, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_one] at h
    exact h
  have hlen : w.length ≤ continuationPrecision i - 1 := by
    have h := stoppedWords_length_lt hw
    omega
  have hp := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3 / 2) hlen
  exact ⟨Rat.cast_nonneg.mpr (ValuationWord.offset_nonneg w), by linarith⟩

/-- Zero-based summand: j=0 is original block i=1. -/
noncomputable def continuationOffsetTerm (j : ℕ) : ℝ :=
  (1 / 8 : ℝ) ^ j * ((3 / 2 : ℝ) ^ (continuationPrecision (j + 1) - 1) - 1)

/-- A fixed explicit geometric-majorant coefficient; numerical optimization is irrelevant. -/
noncomputable def continuationOffsetMajorant : ℝ :=
  (2 : ℝ) ^ (1000 : ℕ) * (Nat.factorial 1000 : ℝ) * Real.exp (3 / 2)

/-- The exact infinite offset envelope in (S.offsetsum). -/
noncomputable def continuationOffsetBound : ℝ := ∑' j, continuationOffsetTerm j

/-- Every original-index summand is nonnegative. -/
theorem continuationOffsetTerm_nonneg (j : ℕ) : 0 ≤ continuationOffsetTerm j := by
  unfold continuationOffsetTerm
  apply mul_nonneg (by positivity)
  exact sub_nonneg.mpr (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 3 / 2))

/-- The explicit coefficient is strictly positive. -/
theorem continuationOffsetMajorant_pos : 0 < continuationOffsetMajorant := by
  unfold continuationOffsetMajorant
  exact mul_pos (mul_pos (by positivity) (Nat.cast_pos.mpr (Nat.factorial_pos 1000)))
    (Real.exp_pos _)

private theorem polynomial_geometric_bound (j k : ℕ) :
    ((j : ℝ) + 3) ^ k ≤
      (2 : ℝ) ^ k * (Nat.factorial k : ℝ) * Real.exp (3 / 2) * 2 ^ j := by
  have hf : (0 : ℝ) < Nat.factorial k := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have h := Real.pow_div_factorial_le_exp (((j : ℝ) + 3) / 2) (by positivity) k
  have hm := mul_le_mul_of_nonneg_right ((div_le_iff₀ hf).mp h)
    (show (0 : ℝ) ≤ 2 ^ k by positivity)
  have hid : (((j : ℝ) + 3) / 2) ^ k * 2 ^ k = ((j : ℝ) + 3) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  rw [hid] at hm
  have he : Real.exp (1 / 2) ≤ 2 := by
    calc
      Real.exp (1 / 2) ≤ Real.exp (Real.log 2) :=
        Real.exp_le_exp.mpr (by linarith [Head.log_two_lower])
      _ = 2 := Real.exp_log (by norm_num)
  have hp := pow_le_pow_left₀ (Real.exp_nonneg (1 / 2)) he j
  have heq : Real.exp (((j : ℝ) + 3) / 2) =
      Real.exp (3 / 2) * Real.exp (1 / 2) ^ j := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  rw [heq] at hm
  have hh := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (2 : ℝ) ^ k * (Nat.factorial k : ℝ) * Real.exp (3 / 2) by positivity)
  nlinarith

/-- The polynomial block envelope and accumulated contraction give a fixed geometric bound. -/
theorem continuationOffsetTerm_le (j : ℕ) :
    continuationOffsetTerm j ≤ continuationOffsetMajorant * (1 / 4 : ℝ) ^ j := by
  have hpoly := continuationPrecision_offset_polynomial (j + 1)
  simp only [Nat.cast_add, Nat.cast_one] at hpoly
  have hp := polynomial_geometric_bound j 1000
  have hb : (3 / 2 : ℝ) ^ (continuationPrecision (j + 1) - 1) - 1 ≤
      continuationOffsetMajorant * 2 ^ j := by
    unfold continuationOffsetMajorant
    have heq : (j : ℝ) + 1 + 2 = (j : ℝ) + 3 := by ring
    rw [heq] at hpoly
    exact (sub_le_self _ (by norm_num : (0 : ℝ) ≤ 1)).trans (hpoly.trans hp)
  calc
    continuationOffsetTerm j ≤ (1 / 8 : ℝ) ^ j * (continuationOffsetMajorant * 2 ^ j) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = continuationOffsetMajorant * ((1 / 8 : ℝ) ^ j * 2 ^ j) := by ring
    _ = continuationOffsetMajorant * (1 / 4 : ℝ) ^ j := by
      rw [← mul_pow]
      norm_num

private theorem summable_offset_majorant :
    Summable (fun j : ℕ => continuationOffsetMajorant * (1 / 4 : ℝ) ^ j) :=
  (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
    (by norm_num : (1 / 4 : ℝ) < 1)).mul_left _

/-- The literal accumulated-contraction series converges. -/
theorem summable_continuationOffsetTerm : Summable continuationOffsetTerm :=
  summable_offset_majorant.of_nonneg_of_le continuationOffsetTerm_nonneg continuationOffsetTerm_le

/-- An explicit geometric tail makes truncation effective at every natural cutoff. -/
theorem continuationOffset_tail_le (n : ℕ) :
    (∑' j : ℕ, continuationOffsetTerm (j + n)) ≤
      (4 / 3 : ℝ) * continuationOffsetMajorant * (1 / 4 : ℝ) ^ n := by
  have hs := (summable_nat_add_iff n).mpr summable_continuationOffsetTerm
  have hm := (summable_nat_add_iff n).mpr summable_offset_majorant
  calc
    (∑' j : ℕ, continuationOffsetTerm (j + n)) ≤
        ∑' j : ℕ, continuationOffsetMajorant * (1 / 4 : ℝ) ^ (j + n) :=
      hs.tsum_le_tsum (fun j => continuationOffsetTerm_le (j + n)) hm
    _ = (4 / 3 : ℝ) * continuationOffsetMajorant * (1 / 4 : ℝ) ^ n := by
      simp_rw [pow_add]
      rw [tsum_mul_left, tsum_mul_right,
        tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4)
          (by norm_num : (1 / 4 : ℝ) < 1)]
      ring

/-- The manuscript's C_infinity is a nonnegative finite real with an explicit upper bound. -/
theorem continuationOffsetBound_bounds :
    0 ≤ continuationOffsetBound ∧
      continuationOffsetBound ≤ (4 / 3 : ℝ) * continuationOffsetMajorant := by
  refine ⟨tsum_nonneg continuationOffsetTerm_nonneg, ?_⟩
  simpa [continuationOffsetBound] using continuationOffset_tail_le 0

/-- Every finite initial offset sum lies below the same complete envelope. -/
theorem continuationOffset_partial_le (n : ℕ) :
    (∑ j ∈ Finset.range n, continuationOffsetTerm j) ≤ continuationOffsetBound := by
  exact summable_continuationOffsetTerm.sum_le_tsum (Finset.range n)
    (fun j _ => continuationOffsetTerm_nonneg j)

end WordCertDensity.Construction
