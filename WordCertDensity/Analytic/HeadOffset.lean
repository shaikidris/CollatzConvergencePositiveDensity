/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The finite geometric and Young-bound route is adapted from Lech Mazur,
Copyright 2026 Lech Mazur, under Apache License 2.0. The original LICENSE
and NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
This proof uses local word numerators and a coarser sufficient scalar margin.
-/
module

public import WordCertDensity.Analytic.HeadGate
public import WordCertDensity.Words.ClearedOffset
public import Mathlib.Algebra.Order.Ring.GeomSum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Small cleared offsets of actual typical heads

The full manuscript width range and common cutoff are retained. A sufficient
rational margin bounds the finite prefix sum directly; no numerical tables or
analytic decay hypothesis are used.
-/

@[expose] public section

namespace WordCertDensity
namespace Head

/-- The logarithmic decay is the difference between two binary logs and one ternary log. -/
theorem log_decay_identity : Real.log (4 / 3 : ℝ) = 2 * Real.log 2 - Real.log 3 := by
  rw [Real.log_div (by norm_num) (by norm_num)]
  have h := Real.log_pow (2 : ℝ) 2
  norm_num at h
  rw [h]

/-- A coarse negative coefficient suffices uniformly for every permitted head width. -/
theorem offset_coefficient_le {v : ℝ} (hv : 80 ≤ v) :
    (-Real.log 2 + (5 / 4 : ℝ) * (Real.log 2) ^ 2) * v ^ 2 +
      3 * Real.log 2 * v ≤ -v := by
  have hh0 : 0 ≤ Real.log 2 := by linarith [log_two_lower]
  have hh1 : Real.log 2 ≤ (7 / 10 : ℝ) := by linarith [log_two_upper]
  have hsq : (Real.log 2) ^ 2 ≤ (7 / 10 : ℝ) ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self hh0 hh1
  have hcoeff : -Real.log 2 + (5 / 4 : ℝ) * (Real.log 2) ^ 2 ≤ -(1 / 20 : ℝ) := by
    linarith [log_two_lower]
  have hm := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg v)
  have hl := mul_le_mul_of_nonneg_right hh1 (by linarith : 0 ≤ 3 * v)
  have hvv : 62 * v ≤ v ^ 2 := by nlinarith
  nlinarith

/-- Completing a square with a fixed fifth of the prefix length leaves geometric decay. -/
theorem offset_young {v L s : ℝ} (hL : 0 < L) (hs : 0 ≤ s) :
    Real.log 2 * v * Real.sqrt (s * L) ≤ s / 5 +
      (5 / 4 : ℝ) * (Real.log 2) ^ 2 * v ^ 2 * L := by
  have h := young_sqrt (a := Real.log 2 * v) (b := 1 / (5 * L)) (x := s * L)
    (by positivity) (mul_nonneg hs hL.le)
  calc
    _ ≤ (1 / (5 * L)) * (s * L) +
        (Real.log 2 * v) ^ 2 / (4 * (1 / (5 * L))) := by linarith
    _ = _ := by field_simp [hL.ne']

/-- The remaining finite geometric sum has a universal bound of sixteen. -/
theorem offset_geometric_sum_le (d : ℕ) :
    (∑ j ∈ Finset.range d, Real.exp (-(1 / 14 : ℝ)) ^ j) ≤ 16 := by
  have h := Real.add_one_le_exp (1 / 14 : ℝ)
  have hr : Real.exp (-(1 / 14 : ℝ)) ≤ (15 / 16 : ℝ) := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0 : ℝ) < 15 / 16)]
    norm_num
    linarith
  have hsum := geom_sum_mul_of_le_one (x := Real.exp (-(1 / 14 : ℝ)))
    (n := d) (by linarith : Real.exp (-(1 / 14 : ℝ)) ≤ 1)
  have hnonneg : 0 ≤ ∑ j ∈ Finset.range d, Real.exp (-(1 / 14 : ℝ)) ^ j := by positivity
  have hmul := mul_le_mul_of_nonneg_right hr hnonneg
  have hp : 0 ≤ Real.exp (-(1 / 14 : ℝ)) ^ d := by positivity
  nlinarith

/-- Each natural numerator summand is bounded by a common factor and geometric decay. -/
theorem Gate.cleared_summand_le {v : ℝ} {n k l j : ℕ} {w : ValuationWord}
    (hv : 80 ≤ v) (hL : 4 < Real.log (n : ℝ)) (hw : Gate v n k l w)
    (hj : j < w.length) :
    ((3 ^ j * 2 ^ (w.total - ValuationWord.total (w.take (j + 1))) : ℕ) : ℝ) ≤
      Real.exp ((n : ℝ) * Real.log 3 + 1 - v * Real.log (n : ℝ)) *
        Real.exp (-(1 / 14 : ℝ)) ^ j := by
  have hlog2 : 0 < Real.log 2 := by linarith [log_two_lower]
  have hprefix := hw.typical.prefix_lower (by omega : 0 < j + 1) (by omega : j + 1 ≤ w.length)
  have htotal := ValuationWord.total_take_le w (j + 1)
  have hupper := (hw.total_range (by linarith : 17 ≤ v) hL.le).2
  have hyoung := offset_young (v := v) (L := Real.log (n : ℝ))
    (s := (j : ℝ) + 1) (by linarith) (by positivity)
  have hp := mul_le_mul_of_nonneg_left hprefix hlog2.le
  have hu := mul_le_mul_of_nonneg_right hupper hlog2.le
  have hc := mul_le_mul_of_nonneg_right (offset_coefficient_le hv)
    (by linarith : 0 ≤ Real.log (n : ℝ))
  have hratio : logRatio * Real.log 2 = Real.log 3 := by
    unfold logRatio
    exact div_mul_cancel₀ _ hlog2.ne'
  have hgamma := mul_le_mul_of_nonneg_right log_four_thirds_lower.le
    (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  rw [log_decay_identity] at hgamma
  simp only [gateLevel, add_mul, sub_mul, mul_assoc] at hu
  rw [hratio] at hu
  norm_num only [Nat.cast_add, Nat.cast_one] at hp
  have hexponent : (j : ℝ) * Real.log 3 + ((l : ℝ) -
      (ValuationWord.total (w.take (j + 1)) : ℝ)) * Real.log 2 ≤
      (n : ℝ) * Real.log 3 + 1 - v * Real.log (n : ℝ) +
        (j : ℝ) * (-(1 / 14 : ℝ)) := by
    nlinarith only [hp, hu, hc, hyoung, hgamma, hlog2, (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hcast : (((w.total - ValuationWord.total (w.take (j + 1)) : ℕ)) : ℝ) =
      (l : ℝ) - (ValuationWord.total (w.take (j + 1)) : ℝ) := by
    rw [Nat.cast_sub htotal, hw.total_eq]
  have heq : ((3 ^ j * 2 ^ (w.total - ValuationWord.total (w.take (j + 1))) : ℕ) : ℝ) =
      Real.exp ((j : ℝ) * Real.log 3 + ((l : ℝ) -
        (ValuationWord.total (w.take (j + 1)) : ℝ)) * Real.log 2) := by
    rw [Real.exp_add, ← hcast, Real.exp_nat_mul, Real.exp_nat_mul]
    simp [Real.exp_log (by norm_num : (0 : ℝ) < 3), Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [heq, ← Real.exp_nat_mul, ← Real.exp_add]
  exact Real.exp_le_exp.mpr hexponent

/-- Every head at the common cutoff has its cleared offset strictly between zero and 3^n. -/
theorem Gate.clearedOffset_bounds {v : ℝ} {n k l : ℕ} {w : ValuationWord}
    (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) (hn : 2 ^ 80 ≤ n) (hw : Gate v n k l w) :
    0 < w.clearedOffset ∧ w.clearedOffset < 3 ^ n := by
  have hL := (common_margins hv hv' hn).1
  refine ⟨ValuationWord.clearedOffset_pos (by
    intro h
    have he := hw.length_eq
    rw [h] at he
    simp at he), ?_⟩
  have hsum : (w.clearedOffset : ℝ) ≤
      Real.exp ((n : ℝ) * Real.log 3 + 1 - v * Real.log (n : ℝ)) *
        ∑ j ∈ Finset.range w.length, Real.exp (-(1 / 14 : ℝ)) ^ j := by
    rw [ValuationWord.clearedOffset_eq_sum, Nat.cast_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    exact hw.cleared_summand_le hv hL (Finset.mem_range.mp hj)
  have hbound := mul_le_mul_of_nonneg_left (offset_geometric_sum_le w.length)
    (Real.exp_nonneg ((n : ℝ) * Real.log 3 + 1 - v * Real.log (n : ℝ)))
  have h16 : (16 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have hfinal : (w.clearedOffset : ℝ) < (3 : ℝ) ^ n := calc
    _ ≤ Real.exp ((n : ℝ) * Real.log 3 + 1 - v * Real.log (n : ℝ)) * 16 := hsum.trans hbound
    _ ≤ Real.exp ((n : ℝ) * Real.log 3 + 1 - v * Real.log (n : ℝ)) * Real.exp 16 :=
      mul_le_mul_of_nonneg_left h16 (Real.exp_nonneg _)
    _ = Real.exp ((n : ℝ) * Real.log 3 + 17 - v * Real.log (n : ℝ)) := by
      rw [← Real.exp_add]; congr 1; ring
    _ < Real.exp ((n : ℝ) * Real.log 3) := by
      apply Real.exp_lt_exp.mpr
      nlinarith
    _ = (3 : ℝ) ^ n := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  exact_mod_cast hfinal

/-- At fixed head index and total, the source residue identifies the whole head word. -/
theorem Gate.eq_of_residueOffset_eq {v : ℝ} {n k l : ℕ} {u w : ValuationWord}
    (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) (hn : 2 ^ 80 ≤ n)
    (hu : Gate v n k l u) (hw : Gate v n k l w)
    (heq : u.residueOffset n = w.residueOffset n) : u = w := by
  exact ValuationWord.eq_of_residueOffset_eq_of_lt
    (hu.length_eq.trans hw.length_eq.symm) (hu.total_eq.trans hw.total_eq.symm)
    (hu.clearedOffset_bounds hv hv' hn).2 (hw.clearedOffset_bounds hv hv' hn).2 heq

end Head
end WordCertDensity
