/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.SeedMarks

/-! # Conductor growth guards for comparison of startup stages -/

namespace WordCertDensity.Construction

/-- The actual seed-size schedule is nondecreasing, even below its growth guard. -/
theorem seedSize_monotone (b : ℕ) : Monotone (seedSize b) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [seedSize]
  omega

/-- Retaining the initial depth in every block gives q(n)≥bn. -/
theorem seedConductor_ge_mul (b n : ℕ) : b * n ≤ seedConductor b n := by
  have hsum : b * n ≤ seedDepth b 0 n := by
    have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.range n) => seedSize_ge b (0 + j))
    simpa only [seedDepth, Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id,
      Nat.mul_comm] using h
  exact hsum.trans (Nat.le_add_right _ _)

/-- The fixed initial root index H=2b+1 is bounded by the terminal quarter. -/
theorem seedConductor_start_guard (b n : ℕ) : 2 * b + 1 ≤ 8 * seedConductor b n + 7 := by
  have h := seedSize_ge b n
  unfold seedConductor seedTailDepth
  omega

/-- Adding a positive block strictly increases the conductor, retaining its terminal tail. -/
theorem seedConductor_succ {b : ℕ} (hb : 1 ≤ b) (n : ℕ) :
    seedConductor b n + 1 ≤ seedConductor b (n + 1) := by
  have hdepth : seedDepth b 0 (n + 1) = seedDepth b 0 n + seedSize b n := by
    simp [seedDepth, Finset.sum_range_succ]
  have htail : seedTailDepth b n ≤ seedTailDepth b (n + 1) :=
    Nat.div_le_div_right (seedSize_monotone b (Nat.le_succ n))
  have hsize := hb.trans (seedSize_ge b n)
  unfold seedConductor
  rw [hdepth]
  omega

/-- Distinct later startup stages have strictly larger conductors. -/
theorem seedConductor_strictMono {b : ℕ} (hb : 1 ≤ b) : StrictMono (seedConductor b) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact Nat.lt_of_succ_le (seedConductor_succ hb n)

end WordCertDensity.Construction
