/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Analytic.FullMixing
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Generic limits from summable monotone increments

This module is deliberately independent of `Reference.Entropy`.  It packages
only the sequence argument needed after the entropy increment and error-tail
estimates have been established.
-/

namespace WordCertDensity.Reference

open Filter
open scoped Topology BigOperators

/-- The actual order-one entropy increment envelope. -/
noncomputable def entropyError (n : ℕ) : ℝ :=
  min (Real.log 3) (Analytic.mixingError n)

/-- Positive-index entropy errors are nonnegative. -/
theorem entropyError_nonneg {n : ℕ} (hn : 1 ≤ n) : 0 ≤ entropyError n := by
  unfold entropyError
  exact le_min (Real.log_nonneg (by norm_num)) (Analytic.mixingError_pos hn).le

/-- The positive-index entropy-error series is summable. -/
theorem entropyError_summable : Summable (fun j : ℕ => entropyError (j + 1)) := by
  have hpow : Summable (fun j : ℕ => (j : ℝ) ^ (-6 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have hshift : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ (-6 : ℝ)) := by
    simpa using (summable_nat_add_iff (f := fun j : ℕ => (j : ℝ) ^ (-6 : ℝ)) 1).mpr hpow
  refine (hshift.mul_left (Analytic.mixingCoefficient : ℝ)).of_nonneg_of_le ?_ ?_
  · intro j
    exact entropyError_nonneg (by omega)
  · intro j
    unfold entropyError
    exact (min_le_right _ _).trans (Analytic.mixingError_le_order6 (by omega))

/-- Each entropy-error tail retains the printed optimized mixing exponent. -/
theorem entropyError_tail_le_power (n : ℕ) (hn : 1 ≤ n) :
    ∑' j : ℕ, entropyError (n + j) ≤
      ∑' j : ℕ, min (Real.log 3)
        ((Analytic.mixingCoefficient : ℝ) * ((n + j : ℕ) : ℝ) ^ (-Analytic.mixingExponent)) := by
  have hleft : Summable (fun j : ℕ => entropyError (n + j)) := by
    have hshift := (summable_nat_add_iff (f := fun j : ℕ => entropyError (j + 1))
      (n - 1)).mpr entropyError_summable
    have hfun : (fun j : ℕ => entropyError (n + j)) =
        fun j => entropyError (j + (n - 1) + 1) := by
      funext j
      congr 1
      omega
    rw [hfun]
    exact hshift
  have hpow : Summable (fun j : ℕ => (j : ℝ) ^ (-Analytic.mixingExponent)) :=
    Real.summable_nat_rpow.mpr (by norm_num [Analytic.mixingExponent])
  have hshift : Summable (fun j : ℕ => ((n + j : ℕ) : ℝ) ^ (-Analytic.mixingExponent)) := by
    have hshift := (summable_nat_add_iff
      (f := fun j : ℕ => (j : ℝ) ^ (-Analytic.mixingExponent)) n).mpr hpow
    have hfun : (fun j : ℕ => ((n + j : ℕ) : ℝ) ^ (-Analytic.mixingExponent)) =
        fun j => ((j + n : ℕ) : ℝ) ^ (-Analytic.mixingExponent) := by
      funext j
      rw [Nat.add_comm]
    rw [hfun]
    exact hshift
  have hright : Summable (fun j : ℕ => min (Real.log 3)
      ((Analytic.mixingCoefficient : ℝ) * ((n + j : ℕ) : ℝ) ^ (-Analytic.mixingExponent))) :=
    (hshift.mul_left (Analytic.mixingCoefficient : ℝ)).of_nonneg_of_le
      (fun _ => le_min (Real.log_nonneg (by norm_num))
        (mul_nonneg Analytic.mixingCoefficient_pos.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)))
      (fun _ => min_le_right _ _)
  refine Summable.tsum_le_tsum ?_ hleft hright
  intro j
  unfold entropyError
  exact min_le_min_left _ (Analytic.mixingError_le_power (n + j))

private theorem le_base_add_increment_sum
    {D e : ℕ → ℝ} (hinc : ∀ n, 1 ≤ n → D (n + 1) - D n ≤ e n)
    {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    D (m + k) ≤ D m + ∑ i ∈ Finset.range k, e (m + i) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hstep := hinc (m + k) (by omega)
      rw [Finset.sum_range_succ]
      have hrewrite : m + (k + 1) = (m + k) + 1 := by omega
      rw [hrewrite]
      linarith

/-- A nonnegative monotone real sequence with summably bounded positive-index
increments has a finite limit, an initial-series bound, and every shifted tail
bound.  The index shift is explicit: the summability hypothesis concerns
`e (j + 1)`, while the tail at `n ≥ 1` is `e (n + j)`. -/
theorem bounded_increment_limit
    {D e : ℕ → ℝ} (hD0 : ∀ n, 0 ≤ D n) (hmono : Monotone D)
    (he0 : ∀ n, 1 ≤ n → 0 ≤ e n)
    (hinc : ∀ n, 1 ≤ n → D (n + 1) - D n ≤ e n)
    (hsum : Summable (fun j : ℕ => e (j + 1))) :
    ∃ z : ℝ, Tendsto D atTop (𝓝 z) ∧
      (∀ n, D n ≤ z) ∧
      z ≤ D 1 + ∑' j : ℕ, e (j + 1) ∧
      (∀ n, 1 ≤ n → 0 ≤ z - D n ∧ z - D n ≤ ∑' j : ℕ, e (n + j)) := by
  let g : ℕ → ℝ := fun j => e (j + 1)
  have hg0 (j : ℕ) : 0 ≤ g j := he0 (j + 1) (by omega)
  have hbase (n : ℕ) : D n ≤ D 1 + ∑' j : ℕ, g j := by
    rcases n with _ | n
    · exact (hmono (by omega : 0 ≤ 1)).trans
        (le_add_of_nonneg_right (tsum_nonneg hg0))
    · have hfinite := le_base_add_increment_sum hinc (by omega : 1 ≤ 1) n
      have hsumle : (∑ i ∈ Finset.range n, e (1 + i)) ≤ ∑' j : ℕ, g j := by
        simpa [g, Nat.add_comm] using hsum.sum_le_tsum (Finset.range n) (fun i _ => hg0 i)
      have hright : D 1 + ∑ i ∈ Finset.range n, e (1 + i) ≤ D 1 + ∑' j : ℕ, g j := by
        calc
          D 1 + ∑ i ∈ Finset.range n, e (1 + i) =
              (∑ i ∈ Finset.range n, e (1 + i)) + D 1 := add_comm _ _
          _ ≤ (∑' j : ℕ, g j) + D 1 := add_le_add_left hsumle _
          _ = D 1 + ∑' j : ℕ, g j := add_comm _ _
      simpa [Nat.add_comm] using hfinite.trans hright
  have hbdd : BddAbove (Set.range D) :=
    ⟨D 1 + ∑' j : ℕ, g j, fun _ hy => by rcases hy with ⟨n, rfl⟩; exact hbase n⟩
  have hz0 : 0 ≤ ⨆ n, D n :=
    (hD0 0).trans (le_ciSup hbdd 0)
  refine ⟨max 0 (⨆ n, D n), ?_, ?_, ?_, ?_⟩
  · simpa [max_eq_right hz0] using tendsto_atTop_ciSup hmono hbdd
  · intro n
    simpa [max_eq_right hz0] using le_ciSup hbdd n
  · simpa [max_eq_right hz0] using ciSup_le hbase
  · intro n hn
    have htail_sum : Summable (fun j : ℕ => e (n + j)) := by
      have hshift := (summable_nat_add_iff (f := g) (n - 1)).mpr hsum
      have hfun : (fun j : ℕ => e (n + j)) = fun j => e (1 + (j + (n - 1))) := by
        funext j
        congr 1
        omega
      rw [hfun]
      have hgshift : (fun j : ℕ => g (j + (n - 1))) =
          fun j => e (1 + (j + (n - 1))) := by
        funext j
        dsimp [g]
        congr 1
        omega
      rw [hgshift] at hshift
      exact hshift
    have htail0 (j : ℕ) : 0 ≤ e (n + j) := he0 (n + j) (by omega)
    have htail_bound (m : ℕ) : D m ≤ D n + ∑' j : ℕ, e (n + j) := by
      by_cases hmn : m ≤ n
      · exact (hmono hmn).trans (le_add_of_nonneg_right (tsum_nonneg htail0))
      · have hnm : n ≤ m := by omega
        have hfinite := le_base_add_increment_sum hinc hn (m - n)
        have hrewrite : n + (m - n) = m := Nat.add_sub_of_le hnm
        rw [hrewrite] at hfinite
        have hsumle : (∑ i ∈ Finset.range (m - n), e (n + i)) ≤ ∑' j : ℕ, e (n + j) :=
          htail_sum.sum_le_tsum (Finset.range (m - n)) (fun i _ => htail0 i)
        apply hfinite.trans
        calc
          D n + ∑ i ∈ Finset.range (m - n), e (n + i) =
              (∑ i ∈ Finset.range (m - n), e (n + i)) + D n := add_comm _ _
          _ ≤ (∑' j : ℕ, e (n + j)) + D n := add_le_add_left hsumle _
          _ = D n + ∑' j : ℕ, e (n + j) := add_comm _ _
    have hz : (⨆ m, D m) ≤ D n + ∑' j : ℕ, e (n + j) := ciSup_le htail_bound
    constructor
    · rw [max_eq_right hz0]
      exact sub_nonneg.mpr (le_ciSup hbdd n)
    · rw [max_eq_right hz0]
      linarith

/-- Bounded nonnegative sequences have zero growth after division by the index. -/
theorem bounded_nonneg_normalized_tendsto_zero {D : ℕ → ℝ} {C : ℝ}
    (hD : ∀ n, 0 ≤ D n) (hC : ∀ n, D n ≤ C) :
    Tendsto (fun n : ℕ => D n / n) atTop (𝓝 0) := by
  exact squeeze_zero (fun n => div_nonneg (hD n) (Nat.cast_nonneg n))
    (fun n => div_le_div_of_nonneg_right (hC n) (Nat.cast_nonneg n))
    (tendsto_const_div_atTop_nhds_zero_nat C)

/-- The normalized infimum uses strictly positive indices, not the totalized zero term. -/
theorem bounded_nonneg_normalized_iInf_zero {D : ℕ → ℝ} {C : ℝ}
    (hD : ∀ n, 0 ≤ D n) (hC : ∀ n, D n ≤ C) :
    (⨅ n : ℕ, D (n + 1) / (n + 1 : ℝ)) = 0 := by
  have hn (n : ℕ) : 0 ≤ D (n + 1) / (n + 1 : ℝ) :=
    div_nonneg (hD (n + 1)) (by positivity)
  have hb : BddBelow (Set.range (fun n : ℕ => D (n + 1) / (n + 1 : ℝ))) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact hn n⟩
  have ht : Tendsto (fun n : ℕ => D (n + 1) / (n + 1 : ℝ)) atTop (𝓝 0) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_add_atTop_iff_nat 1).2
        (bounded_nonneg_normalized_tendsto_zero hD hC)
  exact le_antisymm (ge_of_tendsto ht (Filter.Eventually.of_forall (ciInf_le hb)))
    (le_ciInf hn)

end WordCertDensity.Reference
