/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.VariationTail

/-! # Exact rational expression for the cubic geometric tail -/

namespace WordCertDensity.Construction

/-- The rational expression in R.exacttail. -/
noncomputable def cubicTailFormula (n : ℕ) (z : ℝ) : ℝ :=
  z ^ n * (((n : ℝ) + 1) ^ 3 / (1 - z) +
    3 * ((n : ℝ) + 1) ^ 2 * z / (1 - z) ^ 2 +
    3 * ((n : ℝ) + 1) * z * (1 + z) / (1 - z) ^ 3 +
    z * (1 + 4 * z + z ^ 2) / (1 - z) ^ 4)

/-- Successive rational tails differ by exactly the cubic geometric term. -/
theorem cubicTailFormula_step (n : ℕ) {z : ℝ} (hz : z ≠ 1) :
    cubicTailFormula n z - cubicTailFormula (n + 1) z =
      ((n : ℝ) + 1) ^ 3 * z ^ n := by
  have hd : 1 - z ≠ 0 := sub_ne_zero.mpr hz.symm
  unfold cubicTailFormula
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp
  ring

private theorem summable_shiftedPower {z : ℝ} (hz : 0 < z) (hz1 : z < 1) (k : ℕ) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ k * z ^ n) := by
  have hn : ‖z‖ < 1 := by simpa [Real.norm_eq_abs, abs_of_pos hz] using hz1
  have h := summable_pow_mul_geometric_of_norm_lt_one k hn
  have hs : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ k * z ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr h
  have hi := hs.mul_left z⁻¹
  apply hi.congr
  intro n
  simp only [Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

/-- The rational tail sequence itself is summable for every rate in (0,1). -/
theorem summable_cubicTailFormula {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    Summable (fun n => cubicTailFormula n z) := by
  have h3 := (summable_shiftedPower hz hz1 3).mul_right ((1 - z)⁻¹)
  have h2 := (summable_shiftedPower hz hz1 2).mul_right (3 * z / (1 - z) ^ 2)
  have h1 := (summable_shiftedPower hz hz1 1).mul_right
    (3 * z * (1 + z) / (1 - z) ^ 3)
  have h0 := (summable_shiftedPower hz hz1 0).mul_right
    (z * (1 + 4 * z + z ^ 2) / (1 - z) ^ 4)
  apply (((h3.add h2).add h1).add h0).congr
  intro n
  simp only [cubicTailFormula]
  ring

/-- Summing the telescoping differences gives the exact infinite tail. -/
theorem cubicTailFormula_eq_tsum (N : ℕ) {z : ℝ} (hz : 0 < z) (hz1 : z < 1) :
    cubicTailFormula N z = ∑' m : ℕ, ((N + m : ℕ) + 1 : ℝ) ^ 3 * z ^ (N + m) := by
  have hs : Summable (fun m => cubicTailFormula (N + m) z) :=
    (summable_cubicTailFormula hz hz1).comp_injective
      (fun _ _ h => Nat.add_left_cancel h)
  have ht : Summable (fun m => cubicTailFormula (N + (m + 1)) z) :=
    (summable_nat_add_iff 1).mpr hs
  have hfirst := hs.tsum_eq_zero_add
  have hdiff := hs.tsum_sub ht
  have heq : (fun m => cubicTailFormula (N + m) z -
      cubicTailFormula (N + (m + 1)) z) =
      (fun m => ((N + m : ℕ) + 1 : ℝ) ^ 3 * z ^ (N + m)) := by
    funext m
    simpa only [Nat.add_assoc] using cubicTailFormula_step (N + m) hz1.ne
  rw [heq] at hdiff
  simp only [Nat.add_zero] at hfirst
  linarith

/-- The actual variation tail equals the manuscript's rational expression. -/
theorem seedVariationTail_exact (N : ℕ) :
    seedVariationTail N = cubicTailFormula N seedVariationRate := by
  have hr := seedVariationRate_contracts
  have h := cubicTailFormula_eq_tsum N hr.1 (hr.2.trans (by norm_num))
  simpa only [seedVariationTail, seedVariationTerm, Nat.cast_add, Nat.cast_one] using h.symm

private theorem cubicTerm_step {n : ℕ} (hn : 16 ≤ n) {z : ℝ}
    (hz : 0 < z) (hzmax : z ≤ 41 / 100) :
    ((n + 1 : ℕ) + 1 : ℝ) ^ 3 * z ^ (n + 1) ≤
      (49 / 100 : ℝ) * (((n : ℝ) + 1) ^ 3 * z ^ n) := by
  have hnreal : (16 : ℝ) ≤ n := by exact_mod_cast hn
  have hlin : (n : ℝ) + 2 ≤ (18 / 17 : ℝ) * ((n : ℝ) + 1) := by linarith
  have hc := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (n : ℝ) + 2) hlin 3
  have hmul := mul_le_mul hc hzmax (le_of_lt hz) (by positivity)
  have hcoef : (18 / 17 : ℝ) ^ 3 * (41 / 100) ≤ 49 / 100 := by norm_num
  have hbound := mul_le_mul_of_nonneg_right hcoef
    (by positivity : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 3)
  have hstep : ((n : ℝ) + 2) ^ 3 * z ≤
      (49 / 100 : ℝ) * ((n : ℝ) + 1) ^ 3 := by nlinarith [hmul]
  have h := mul_le_mul_of_nonneg_right hstep (pow_nonneg hz.le n)
  calc
    _ = (((n : ℝ) + 2) ^ 3 * z) * z ^ n := by
      simp only [Nat.cast_add, Nat.cast_one, pow_succ]
      ring
    _ ≤ ((49 / 100 : ℝ) * ((n : ℝ) + 1) ^ 3) * z ^ n := h
    _ = _ := by ring

/-- After stage sixteen, the full cubic geometric tail is less than twice
its first term, as required by the bounded startup search (R.tailmajorant). -/
theorem cubicTailFormula_lt_twice {n : ℕ} (hn : 16 ≤ n) {z : ℝ}
    (hz : 0 < z) (hzmax : z ≤ 41 / 100) :
    cubicTailFormula n z < 2 * ((n : ℝ) + 1) ^ 3 * z ^ n := by
  let A : ℝ := ((n : ℝ) + 1) ^ 3 * z ^ n
  have hA : 0 < A := by dsimp [A]; positivity
  have hterm : ∀ k : ℕ, ((n + k : ℕ) + 1 : ℝ) ^ 3 * z ^ (n + k) ≤
      A * (49 / 100 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => simp [A]
    | succ k ih =>
      have hs := cubicTerm_step (n := n + k) (by omega) hz hzmax
      calc
        _ ≤ (49 / 100 : ℝ) * (((n + k : ℕ) + 1 : ℝ) ^ 3 * z ^ (n + k)) := by
          simpa only [Nat.add_assoc] using hs
        _ ≤ (49 / 100 : ℝ) * (A * (49 / 100 : ℝ) ^ k) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by rw [pow_succ]; ring
  have hs : Summable (fun k : ℕ => ((n + k : ℕ) + 1 : ℝ) ^ 3 * z ^ (n + k)) :=
    (summable_shiftedPower hz (by linarith) 3).comp_injective
      (fun _ _ h => Nat.add_left_cancel h)
  have hg := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 49 / 100)
    (by norm_num : (49 / 100 : ℝ) < 1)).mul_left A
  rw [cubicTailFormula_eq_tsum n hz (by linarith)]
  have hsum := hs.tsum_le_tsum hterm hg
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 49 / 100)
    (by norm_num : (49 / 100 : ℝ) < 1)] at hsum
  norm_num at hsum
  dsimp [A] at hsum hA
  simp only [Nat.cast_add]
  nlinarith

end WordCertDensity.Construction
