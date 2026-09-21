/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The exact geometric-series summation is adapted from Lech Mazur,
Copyright 2026 Lech Mazur, under Apache License 2.0. The original LICENSE
and NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
The local distribution and the full-pole log bounds replace the source's
restricted, weaker quadratic estimate.
-/
module

public import WordCertDensity.Reference.Geometric
public import WordCertDensity.Probability.GeometricLogBounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact centered moments of the actual reference valuation

All moment identities are stated strictly before log 2, where summability
is proved. The positive bound has the exact reciprocal-log pole coefficient;
the negative-parameter bound holds on the whole nonnegative half-line.
-/

@[expose] public section

namespace WordCertDensity
namespace Reference

open scoped ENNReal

/-- The actual reference exponential moment of the centered valuation K-2. -/
noncomputable def centeredExpMoment (s : ℝ) : ℝ :=
  ∑' a : ℕ+, (geometricLetter a).toReal * Real.exp (s * ((a : ℕ) - (2 : ℝ)))

private theorem centeredTerm_succ (s : ℝ) (n : ℕ) :
    (geometricLetter n.succPNat).toReal * Real.exp (s * ((n.succPNat : ℕ) - (2 : ℝ))) =
      (Real.exp (-s) / 2) * (Real.exp s / 2) ^ n := by
  rw [geometricLetter_toReal]
  have hn : (n.succPNat : ℕ) = n + 1 := rfl
  rw [hn, show s * (((n + 1 : ℕ) : ℝ) - 2) = -s + (n : ℝ) * s by push_cast; ring,
    Real.exp_add, Real.exp_nat_mul]
  ring

/-- The centered geometric exponential series is summable at every real parameter below its pole. -/
theorem summable_centeredExpMoment {s : ℝ} (hs : s < Real.log 2) :
    Summable (fun a : ℕ+ => (geometricLetter a).toReal * Real.exp (s * ((a : ℕ) - (2 : ℝ)))) := by
  have hratio0 : 0 ≤ Real.exp s / 2 := by positivity
  have hratio1 : Real.exp s / 2 < 1 := by linarith [GeometricLog.denominator_pos hs]
  apply (Equiv.pnatEquivNat.symm.summable_iff).mp
  have h := (summable_geometric_of_norm_lt_one
    (show ‖Real.exp s / 2‖ < 1 by rw [Real.norm_of_nonneg hratio0]; exact hratio1)).mul_left
      (Real.exp (-s) / 2)
  apply h.congr
  intro n
  rw [Function.comp_apply, Equiv.pnatEquivNat_symm_apply, centeredTerm_succ]

/-- The exact moment of K-2 retains the leading exp(-s) factor. -/
theorem centeredExpMoment_eq {s : ℝ} (hs : s < Real.log 2) :
    centeredExpMoment s = Real.exp (-s) / (2 - Real.exp s) := by
  have hratio0 : 0 ≤ Real.exp s / 2 := by positivity
  have hratio1 : Real.exp s / 2 < 1 := by linarith [GeometricLog.denominator_pos hs]
  unfold centeredExpMoment
  calc
    _ = ∑' n : ℕ, (geometricLetter (Equiv.pnatEquivNat.symm n)).toReal *
        Real.exp (s * (((Equiv.pnatEquivNat.symm n : ℕ+) : ℕ) - (2 : ℝ))) :=
      (Equiv.pnatEquivNat.symm.tsum_eq _).symm
    _ = ∑' n : ℕ, (Real.exp (-s) / 2) * (Real.exp s / 2) ^ n := by
      apply tsum_congr
      intro n
      rw [Equiv.pnatEquivNat_symm_apply, centeredTerm_succ]
    _ = (Real.exp (-s) / 2) * (1 - Real.exp s / 2)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hratio0 hratio1]
    _ = Real.exp (-s) / (2 - Real.exp s) := by field_simp

/-- Every admissible moment is strictly positive. -/
theorem centeredExpMoment_pos {s : ℝ} (hs : s < Real.log 2) : 0 < centeredExpMoment s := by
  rw [centeredExpMoment_eq hs]
  exact div_pos (Real.exp_pos _) (GeometricLog.denominator_pos hs)

/-- The actual expectation has the closed log form used in the manuscript. -/
theorem log_centeredExpMoment_eq {s : ℝ} (hs : s < Real.log 2) :
    Real.log (centeredExpMoment s) = GeometricLog.value s := by
  rw [centeredExpMoment_eq hs, Real.log_div (Real.exp_pos _).ne'
    (GeometricLog.denominator_pos hs).ne', Real.log_exp]
  rfl

/-- The exact positive-side log bound holds on the full open pole interval. -/
theorem log_centeredExpMoment_le {s : ℝ} (hs0 : 0 ≤ s) (hs : s < Real.log 2) :
    Real.log (centeredExpMoment s) ≤ s ^ 2 / (1 - (Real.log 2)⁻¹ * s) := by
  rw [log_centeredExpMoment_eq hs]
  exact GeometricLog.value_le_upper hs0 hs

/-- The exact negative-side log bound holds for every nonnegative parameter. -/
theorem log_centeredExpMoment_neg_le {s : ℝ} (hs : 0 ≤ s) :
    Real.log (centeredExpMoment (-s)) ≤ s ^ 2 := by
  rw [log_centeredExpMoment_eq (by linarith [GeometricLog.log_two_pos] : -s < Real.log 2)]
  exact GeometricLog.value_neg_le_sq hs

/-- The positive exponential moment bound is ready for the independent-word Markov argument. -/
theorem centeredExpMoment_le_exp {s : ℝ} (hs0 : 0 ≤ s) (hs : s < Real.log 2) :
    centeredExpMoment s ≤ Real.exp (s ^ 2 / (1 - (Real.log 2)⁻¹ * s)) :=
  (Real.log_le_iff_le_exp (centeredExpMoment_pos hs)).mp (log_centeredExpMoment_le hs0 hs)

/-- The negative exponential moment bound retains its smaller quadratic exponent. -/
theorem centeredExpMoment_neg_le_exp {s : ℝ} (hs : 0 ≤ s) :
    centeredExpMoment (-s) ≤ Real.exp (s ^ 2) := by
  have hdom : -s < Real.log 2 := by linarith [GeometricLog.log_two_pos]
  exact (Real.log_le_iff_le_exp (centeredExpMoment_pos hdom)).mp (log_centeredExpMoment_neg_le hs)

/-- The actual ENNReal expectation agrees with the summable real moment. -/
theorem centeredExpMoment_ennreal {s : ℝ} (hs : s < Real.log 2) :
    (∑' a : ℕ+, geometricLetter a * ENNReal.ofReal (Real.exp (s * ((a : ℕ) - (2 : ℝ))))) =
      ENNReal.ofReal (centeredExpMoment s) := by
  unfold centeredExpMoment
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun a => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le) (summable_centeredExpMoment hs)]
  apply tsum_congr
  intro a
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)]

end Reference
end WordCertDensity
