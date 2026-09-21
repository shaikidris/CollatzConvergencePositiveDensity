/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.SeedMajorant
import WordCertDensity.Construction.SeedCap
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Summability and the complete future tail of physical seed marks -/

namespace WordCertDensity.Construction

open Filter Topology

/-- The root-independent scalar series controlling every physical increment. -/
noncomputable def seedVariationTerm (n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ 3 * seedVariationRate ^ n

private theorem seedVariationTerm_nonneg (n : ℕ) : 0 ≤ seedVariationTerm n := by
  unfold seedVariationTerm
  exact mul_nonneg (pow_nonneg (by positivity) 3)
    (pow_nonneg seedVariationRate_contracts.1.le n)

private theorem seedVariationCoefficient_nonneg (b : ℕ) : 0 ≤ seedVariationCoefficient b := by
  unfold seedVariationCoefficient
  have hC : 0 ≤ Analytic.mixingCoefficient + 1 := by
    linarith [Analytic.mixingCoefficient_pos]
  exact mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) 467)
    (Nat.cast_nonneg b)) (pow_nonneg (by norm_num) b)) hC

/-- The full polynomially weighted variation series is summable. -/
theorem summable_seedVariationTerm : Summable seedVariationTerm := by
  have hr : ‖seedVariationRate‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos seedVariationRate_contracts.1]
    linarith [seedVariationRate_contracts.2]
  have hbase : Summable (fun n : ℕ => (n : ℝ) ^ 3 * seedVariationRate ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one 3 hr
  have hshift : Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) ^ 3 * seedVariationRate ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hbase
  have hscaled := hshift.mul_left seedVariationRate⁻¹
  apply hscaled.congr
  intro n
  unfold seedVariationTerm
  simp only [Nat.cast_add, Nat.cast_one]
  rw [pow_succ]
  field_simp [ne_of_gt seedVariationRate_contracts.1]
  ring_nf

/-- The manuscript's complete nonnegative majorant is summable for every startup depth. -/
theorem summable_seedVariationMajorant (b : ℕ) :
    Summable (fun n => seedVariationCoefficient b * seedVariationTerm n) :=
  summable_seedVariationTerm.mul_left _

private theorem physicalSeedMark_step_le {b root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) (n : ℕ) :
    dist (physicalSeedMark b n root) (physicalSeedMark b (n + 1) root) ≤
      seedVariationCoefficient b * seedVariationTerm n := by
  rw [Real.dist_eq, abs_sub_comm, seedVariationTerm]
  calc
    |physicalSeedMark b (n + 1) root - physicalSeedMark b n root| ≤
        seedVariationCoefficient b * ((n : ℝ) + 1) ^ 3 * seedVariationRate ^ n :=
      physicalSeedMark_variation (b := b) (root := root) hb hr n
    _ = seedVariationCoefficient b *
        (((n : ℝ) + 1) ^ 3 * seedVariationRate ^ n) := by ring

/-- The actual sequence of physical seed marks is Cauchy at every guarded root. -/
theorem physicalSeedMark_cauchy {b root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) : CauchySeq (fun n => physicalSeedMark b n root) := by
  apply cauchySeq_of_dist_le_of_summable
    (fun n => seedVariationCoefficient b * seedVariationTerm n)
  · exact physicalSeedMark_step_le hb hr
  · exact summable_seedVariationMajorant b

/-- The canonical limit of the physical seed marks. -/
noncomputable def physicalSeedLimit (b root : ℕ) : ℝ :=
  limUnder atTop (fun n => physicalSeedMark b n root)

/-- Every guarded physical seed sequence converges to its canonical limit. -/
theorem physicalSeedMark_tendsto {b root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) :
    Tendsto (fun n => physicalSeedMark b n root) atTop (𝓝 (physicalSeedLimit b root)) := by
  exact (physicalSeedMark_cauchy hb hr).tendsto_limUnder

/-- Finite physical marks differ by at most the entire future majorant tail. -/
theorem physicalSeedMark_finite_tail {b root N n : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) (hN : N ≤ n) :
    |physicalSeedMark b n root - physicalSeedMark b N root| ≤
      seedVariationCoefficient b * ∑' m, seedVariationTerm (N + m) := by
  have hs : Summable (fun m => seedVariationTerm (N + m)) :=
    summable_seedVariationTerm.comp_injective (fun _ _ h => Nat.add_left_cancel h)
  have hfinite :
      dist (physicalSeedMark b N root) (physicalSeedMark b n root) ≤
        ∑ j ∈ Finset.Ico N n, seedVariationCoefficient b * seedVariationTerm j := by
    apply dist_le_Ico_sum_of_dist_le hN
    intro j _ _
    exact physicalSeedMark_step_le hb hr j
  rw [abs_sub_comm]
  change dist (physicalSeedMark b N root) (physicalSeedMark b n root) ≤ _
  apply hfinite.trans
  calc
    (∑ j ∈ Finset.Ico N n, seedVariationCoefficient b * seedVariationTerm j) =
        ∑ j ∈ Finset.range (n - N),
          seedVariationCoefficient b * seedVariationTerm (N + j) := by
      rw [Finset.sum_Ico_eq_sum_range]
    _ ≤ ∑' j, seedVariationCoefficient b * seedVariationTerm (N + j) := by
      have hsum : Summable (fun j =>
          seedVariationCoefficient b * seedVariationTerm (N + j)) :=
        (summable_seedVariationMajorant b).comp_injective
          (fun _ _ h => Nat.add_left_cancel h)
      exact hsum.sum_le_tsum (Finset.range (n - N))
        (fun j _ => mul_nonneg (seedVariationCoefficient_nonneg b)
          (seedVariationTerm_nonneg (N + j)))
    _ = seedVariationCoefficient b * ∑' j, seedVariationTerm (N + j) :=
      hs.tsum_mul_left _

/-- The canonical limit satisfies the same complete future-tail estimate. -/
theorem physicalSeedMark_limit_tail {b root N : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) :
    |physicalSeedLimit b root - physicalSeedMark b N root| ≤
      seedVariationCoefficient b * ∑' m, seedVariationTerm (N + m) := by
  have hs : Summable (fun m => seedVariationTerm (N + m)) :=
    summable_seedVariationTerm.comp_injective (fun _ _ h => Nat.add_left_cancel h)
  have hdist := dist_le_tsum_of_dist_le_of_tendsto
    (fun n => seedVariationCoefficient b * seedVariationTerm n)
    (physicalSeedMark_step_le hb hr)
    (summable_seedVariationMajorant b) (physicalSeedMark_tendsto hb hr) N
  rw [hs.tsum_mul_left] at hdist
  simpa only [Real.dist_eq, abs_sub_comm] using hdist

/-- Odd guarded roots have a nonnegative limiting physical seed mark. -/
theorem physicalSeedLimit_nonneg {b root : ℕ} (hb : 32 ^ 5 ≤ b)
    (hr : 16 ^ b ≤ root) (hodd : Odd root) : 0 ≤ physicalSeedLimit b root := by
  exact ge_of_tendsto (physicalSeedMark_tendsto hb hr)
    (Filter.Eventually.of_forall fun n => (physicalSeedMark_cap hb hr hodd n).1)

end WordCertDensity.Construction
