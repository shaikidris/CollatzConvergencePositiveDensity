/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Reference.Moments

/-! # Block propagation for all real-order reference moments -/

namespace WordCertDensity.Reference

/-- A certified block bounds every repetition, retaining the actual remainder moment. -/
theorem moment_block_ceiling (s : ℝ) (hs : 1 ≤ s) (b : ℕ) (B : ℝ)
    (hB : 0 ≤ B) (hb : moment s b ≤ B) (n : ℕ) :
    moment s n ≤ B ^ (n / b) * moment s (n % b) := by
  have blocks (q : ℕ) : moment s (b * q) ≤ B ^ q := by
    induction q with
    | zero => simp only [Nat.mul_zero, moment_zero, pow_zero, le_refl]
    | succ q ih =>
      rw [Nat.mul_succ, pow_succ]
      exact (moment_inheritance s hs (b * q) b).trans
        (mul_le_mul ih hb (moment_nonneg s b) (pow_nonneg hB q))
  calc
    moment s n = moment s (n % b + b * (n / b)) :=
      congrArg (moment s) (Nat.mod_add_div n b).symm
    _ ≤ moment s (n % b) * moment s (b * (n / b)) :=
      moment_inheritance s hs _ _
    _ ≤ moment s (n % b) * B ^ (n / b) :=
      mul_le_mul_of_nonneg_left (blocks _) (moment_nonneg s _)
    _ = B ^ (n / b) * moment s (n % b) := mul_comm _ _

/-- A one-step certificate controls all short remainders without further finite tables. -/
theorem moment_single_ceiling (s : ℝ) (hs : 1 ≤ s) (A : ℝ)
    (hA : 0 ≤ A) (h : moment s 1 ≤ A) (n : ℕ) : moment s n ≤ A ^ n := by
  simpa only [Nat.div_one, Nat.mod_one, moment_zero, mul_one] using
    moment_block_ceiling s hs 1 A hA h n

end WordCertDensity.Reference
