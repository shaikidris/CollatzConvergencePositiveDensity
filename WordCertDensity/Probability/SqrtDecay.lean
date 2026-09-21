/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Exact integral and sum of square-root exponential decay

The integral is evaluated through the Gamma formula at exponent one half.
Its positive value discharges integrability before the integral test is used.
The discrete estimates start at length one, with no zero-length contribution.
-/

@[expose] public section

namespace WordCertDensity
namespace SqrtDecay

open MeasureTheory Set

/-- The exact length factor in the short-interval failure bound. -/
noncomputable def weight (q L x : ℝ) : ℝ := Real.exp (-(q / 2) * Real.sqrt (x * L))

/-- The length factor is strictly positive. -/
theorem weight_pos (q L x : ℝ) : 0 < weight q L x := Real.exp_pos _

/-- At zero length there is a unit term, which is excluded from the failure sum. -/
@[simp] theorem weight_zero (q L : ℝ) : weight q L 0 = 1 := by simp [weight]

/-- Nonnegative parameters make the kernel antitone on the whole real line. -/
theorem weight_antitone {q L : ℝ} (hq : 0 ≤ q) (hL : 0 ≤ L) : Antitone (weight q L) := by
  intro x y hxy
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hxy hL)) (by linarith : -(q / 2) ≤ 0)

/-- The exact improper integral retains both the coefficient eight and the scale L. -/
theorem integral_weight {q L : ℝ} (hq : 0 < q) (hL : 0 < L) :
    (∫ x in Ioi (0 : ℝ), weight q L x) = 8 / (q ^ 2 * L) := by
  let b : ℝ := (q / 2) * Real.sqrt L
  have hb : 0 < b := mul_pos (by positivity) (Real.sqrt_pos.mpr hL)
  have hkernel (x : ℝ) : weight q L x = Real.exp (-b * x ^ (1 / (2 : ℝ))) := by
    unfold weight
    rw [mul_comm x L, Real.sqrt_mul hL.le, Real.sqrt_eq_rpow x]
    congr 1
    dsimp only [b]
    ring
  simp_rw [hkernel]
  rw [integral_exp_neg_mul_rpow (by norm_num : (0 : ℝ) < 1 / 2) hb]
  norm_num
  dsimp only [b]
  rw [mul_pow, div_pow, Real.sq_sqrt hL.le]
  field_simp
  norm_num

/-- The nonzero exact integral proves integrability, rather than assuming convergence. -/
theorem integrableOn_weight {q L : ℝ} (hq : 0 < q) (hL : 0 < L) :
    IntegrableOn (weight q L) (Ioi (0 : ℝ)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_weight hq hL]
  positivity

/-- The natural-index kernel is summable for positive parameters. -/
theorem summable_weight {q L : ℝ} (hq : 0 < q) (hL : 0 < L) :
    Summable (fun n : ℕ => weight q L n) :=
  ((weight_antitone hq.le hL.le).antitoneOn (Ici 0)).summable_of_integrableOn_Ioi_zero
    (integrableOn_weight hq hL) (fun x _ => (weight_pos q L x).le)

/-- Shifting to positive integer lengths preserves summability. -/
theorem summable_weight_add_one {q L : ℝ} (hq : 0 < q) (hL : 0 < L) :
    Summable (fun n : ℕ => weight q L (n + 1 : ℕ)) :=
  (summable_nat_add_iff 1).mpr (summable_weight hq hL)

/-- The positive-length sum has the exact manuscript upper bound. -/
theorem tsum_weight_add_one_le {q L : ℝ} (hq : 0 < q) (hL : 0 < L) :
    (∑' n : ℕ, weight q L (n + 1 : ℕ)) ≤ 8 / (q ^ 2 * L) := by
  have h := ((weight_antitone hq.le hL.le).antitoneOn (Ici 0)).tsum_add_one_le_integral
    (integrableOn_weight hq hL) (fun x _ => (weight_pos q L x).le)
  rw [integral_weight hq hL] at h
  exact h

/-- Every finite initial set of positive lengths satisfies the same bound. -/
theorem sum_weight_add_one_le {q L : ℝ} (hq : 0 < q) (hL : 0 < L) (N : ℕ) :
    (∑ n ∈ Finset.range N, weight q L (n + 1 : ℕ)) ≤ 8 / (q ^ 2 * L) := by
  have h := ((weight_antitone hq.le hL.le).antitoneOn (Icc 0 (N : ℝ))).sum_range_le_integral (N := N)
    (integrableOn_weight hq hL) (fun x _ => (weight_pos q L x).le)
  rw [integral_weight hq hL] at h
  exact h

end SqrtDecay
end WordCertDensity
