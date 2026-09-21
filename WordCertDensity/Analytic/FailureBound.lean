/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.IntervalCounting
public import WordCertDensity.Probability.SqrtDecay
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# The full length-sensitive typicality failure bound

Intervals are grouped by positive length. Each short-length cost is paid
at most n times; the long cost is paid by the exact triangular interval count.
Both estimates remain under the original iid word law.
-/

@[expose] public section

namespace WordCertDensity
namespace Head

/-- The three-term rejection envelope at width v and real ambient scale x. -/
noncomputable def failureEnvelope (v x : ℝ) : ℝ :=
  16 / ((v * Real.log 2) ^ 2 * Real.log x) * x ^ (1 - v * Real.log 2) +
    x ^ (-(v * Real.log 2)) + x ^ (-(v * Real.log 2) - 1)

end Head

namespace HeadSlice

private theorem weighted_start_sum_le (n : ℕ) (A B : ℝ) (f : ℕ → ℝ)
    (hA : 0 ≤ A) (hf : ∀ r ∈ Finset.range n, 0 ≤ f (r + 1)) :
    (∑ r ∈ Finset.range n, ((n - r : ℕ) : ℝ) * (A * f (r + 1) + B)) ≤
      (n : ℝ) * A * (∑ r ∈ Finset.range n, f (r + 1)) +
        ((n : ℝ) * ((n : ℝ) + 1) / 2) * B := by
  calc
    _ ≤ ∑ r ∈ Finset.range n,
        (((n : ℝ) * A) * f (r + 1) + ((n - r : ℕ) : ℝ) * B) := by
      apply Finset.sum_le_sum
      intro r hr
      have hnr : ((n - r : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n r
      have h := mul_le_mul_of_nonneg_right hnr (mul_nonneg hA (hf r hr))
      nlinarith only [h]
    _ = (n : ℝ) * A * (∑ r ∈ Finset.range n, f (r + 1)) +
        (∑ r ∈ Finset.range n, ((n - r : ℕ) : ℝ)) * B := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    _ = _ := by rw [Head.sum_interval_starts]

private theorem envelope_payment {x : ℝ} (hx : 0 < x) (q L : ℝ) :
    x * (2 * x ^ (-q)) * (8 / (q ^ 2 * L)) +
      (x * (x + 1) / 2) * (2 * x ^ (-q - 2)) =
        16 / (q ^ 2 * L) * x ^ (1 - q) + x ^ (-q) + x ^ (-q - 1) := by
  have hp (s : ℝ) : x * x ^ s = x ^ (s + 1) := by
    rw [Real.rpow_add hx, Real.rpow_one, mul_comm]
  have hfirst : x * x ^ (-q) = x ^ (1 - q) := by
    rw [hp]
    congr 1
    ring
  have htail : x * x ^ (-q - 2) = x ^ (-q - 1) := by
    rw [hp]
    congr 1
    ring
  have htail' : x * x ^ (-q - 1) = x ^ (-q) := by
    rw [hp]
    congr 1
    ring
  calc
    _ = 16 / (q ^ 2 * L) * (x * x ^ (-q)) +
        x * (x * x ^ (-q - 2)) + x * x ^ (-q - 2) := by ring
    _ = _ := by rw [hfirst, htail, htail']

/-- The actual global typicality failure satisfies all three manuscript terms. -/
theorem failureProbability_le {v : ℝ} {n : ℕ} (hv : 80 ≤ v) (hn : 1 < n) :
    failureProbability v n ≤ Head.failureEnvelope v n := by
  let q := v * Real.log 2
  let L := Real.log (n : ℝ)
  let A := 2 * (n : ℝ) ^ (-q)
  let B := 2 * (n : ℝ) ^ (-q - 2)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hL : 0 < L := Real.log_pos hn1
  have hq : 0 < q := mul_pos (by linarith) (Real.log_pos (by norm_num))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hinterval {i j : ℕ} (hij : i < j) (hjn : j ≤ n) :
      Gated.probability (Reference.wordPMF n) (Head.intervalFailure v n i j) ≤
        A * SqrtDecay.weight q L (j - i : ℕ) + B := by
    by_cases hr : ((j - i : ℕ) : ℝ) ≤ L
    · have h : Gated.probability (Reference.wordPMF n) (Head.intervalFailure v n i j) ≤
          A * SqrtDecay.weight q L (j - i : ℕ) := by
        simpa only [A, q, L, SqrtDecay.weight] using Head.intervalFailure_short hv hn hij hjn hr
      linarith only [h, hB]
    · have h : Gated.probability (Reference.wordPMF n) (Head.intervalFailure v n i j) ≤ B :=
        Head.intervalFailure_long hv hn hij hjn (le_of_lt (lt_of_not_ge hr))
      have hp := mul_nonneg hA (SqrtDecay.weight_pos q L (j - i : ℕ)).le
      linarith only [h, hp]
  have hsum : failureProbability v n ≤ ∑ r ∈ Finset.range n,
      ((n - r : ℕ) : ℝ) * (A * SqrtDecay.weight q L (r + 1 : ℕ) + B) := by
    apply (failureProbability_le_intervals v n).trans
    apply Finset.sum_le_sum
    intro r hr
    have hrn := Finset.mem_range.mp hr
    calc
      _ ≤ ∑ i ∈ Finset.range (n - r), (A * SqrtDecay.weight q L (r + 1 : ℕ) + B) := by
        apply Finset.sum_le_sum
        intro i hi
        have hin := Finset.mem_range.mp hi
        simpa only [Nat.add_sub_cancel_left] using
          hinterval (i := i) (j := i + (r + 1)) (by omega) (by omega)
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  calc
    _ ≤ ∑ r ∈ Finset.range n,
        ((n - r : ℕ) : ℝ) * (A * SqrtDecay.weight q L (r + 1 : ℕ) + B) := hsum
    _ ≤ (n : ℝ) * A * (∑ r ∈ Finset.range n, SqrtDecay.weight q L (r + 1 : ℕ)) +
        ((n : ℝ) * ((n : ℝ) + 1) / 2) * B :=
      weighted_start_sum_le n A B (fun r => SqrtDecay.weight q L r) hA
        (fun r _ => (SqrtDecay.weight_pos q L (r + 1 : ℕ)).le)
    _ ≤ (n : ℝ) * A * (8 / (q ^ 2 * L)) + ((n : ℝ) * ((n : ℝ) + 1) / 2) * B :=
      add_le_add (mul_le_mul_of_nonneg_left (SqrtDecay.sum_weight_add_one_le hq hL n)
        (mul_nonneg hn0.le hA)) le_rfl
    _ = Head.failureEnvelope v n := by
      simpa only [A, B, q, L, Head.failureEnvelope] using envelope_payment hn0 q L

/-- The original rejected residue mass inherits the same envelope at the manuscript's common cutoff. -/
theorem rejectedMass_sum_le_envelope {v : ℝ} {n : ℕ}
    (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) (hn : 2 ^ 80 ≤ n) :
    (∑ y, rejectedMass v n y) ≤ Head.failureEnvelope v n := by
  apply (rejectedMass_sum_le_failure hv hv' hn).trans
  apply failureProbability_le hv
  have hc : 1 < (2 : ℕ) ^ 80 := by norm_num
  omega

end HeadSlice
end WordCertDensity
