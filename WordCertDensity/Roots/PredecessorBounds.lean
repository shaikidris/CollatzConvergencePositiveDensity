/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Roots.PredecessorBlocks
public import Mathlib.Algebra.BigOperators.Field

/-!
# Common effective bounds for two predecessor blocks

An explicit start pays the seed height and incoming dyadic path guard.
The last root of the second block bounds both candidates. A rational score
uses this common denominator, independently of the nonrecurrent-block choice.
-/

@[expose] public section

namespace WordCertDensity.Roots

/-- A conservative computable start paying the height and dyadic-path guards. -/
def predecessorStart (b v : ℕ) : ℕ := 16 ^ b + v

/-- The final root of the second complete block bounds both candidates. -/
def predecessorMax (y q start : ℕ) : ℕ := inverseRoot y (start + 2 * 3 ^ q - 1)

/-- A rational lower score using the same denominator for either candidate block. -/
def predecessorScore (W K : ℚ) (y q start : ℕ) : ℚ :=
  min W (K / predecessorMax y q start)

/-- Every indexed predecessor of a unit target is strictly larger than its index. -/
theorem index_lt_inverseRoot {y : ℕ} (hy : ¬ 3 ∣ y) (t : ℕ) : t < inverseRoot y t := by
  induction t with
  | zero => exact inverseRoot_pos hy 0
  | succ t ih =>
    have h : inverseRoot y t < inverseRoot y (t + 1) :=
      inverseRoot_strictMono hy (Nat.lt_succ_self t)
    omega

/-- Every retained root is above the starting index. -/
theorem start_lt_unitPredecessorBlock {y q start x : ℕ} (hy : ¬ 3 ∣ y)
    (hx : x ∈ unitPredecessorBlock y q start) : start < x := by
  obtain ⟨_, i, rfl⟩ := mem_unitPredecessorBlock.mp hx
  exact lt_of_le_of_lt (Nat.le_add_right start i.val) (index_lt_inverseRoot hy _)

/-- Both blocks lie between the first root and the common final root. -/
theorem unitPredecessorBlock_bounds {y q start j x : ℕ} (hy : ¬ 3 ∣ y) (hj : j ≤ 1)
    (hx : x ∈ unitPredecessorBlock y q (start + j * 3 ^ q)) :
    inverseRoot y start ≤ x ∧ x ≤ predecessorMax y q start := by
  obtain ⟨_, i, rfl⟩ := mem_unitPredecessorBlock.mp hx
  have hjn : j * 3 ^ q ≤ 3 ^ q := by simpa using Nat.mul_le_mul_right (3 ^ q) hj
  have hn : 0 < 3 ^ q := pow_pos (by decide) _
  have hi := i.isLt
  constructor
  · exact (inverseRoot_strictMono hy).monotone (by omega)
  · exact (inverseRoot_strictMono hy).monotone (by omega)

/-- The common maximal root is positive. -/
theorem predecessorMax_pos {y : ℕ} (hy : ¬ 3 ∣ y) (q start : ℕ) :
    0 < predecessorMax y q start := inverseRoot_pos hy _

/-- The explicit start places every root of either candidate above the seed height. -/
theorem unitPredecessorBlock_height {y q b v j x : ℕ} (hy : ¬ 3 ∣ y)
    (hx : x ∈ unitPredecessorBlock y q (predecessorStart b v + j * 3 ^ q)) :
    16 ^ b ≤ x := by
  have h := start_lt_unitPredecessorBlock hy hx
  unfold predecessorStart at h
  omega

/-- A sufficiently large start gives the specified ordinary path to the dyadic target. -/
theorem unitPredecessorBlock_reaches {y q start v x : ℕ} (hy : ¬ 3 ∣ y)
    (hv : v ≤ start) (hx : x ∈ unitPredecessorBlock y q start) :
    ∃ t, start ≤ t ∧ t < start + 3 ^ q ∧
      ReachesIn x (2 ^ v * y) (1 + inverseExponent y t - v) := by
  obtain ⟨_, i, rfl⟩ := mem_unitPredecessorBlock.mp hx
  refine ⟨start + i.val, by omega, by have h := i.isLt; omega, ?_⟩
  apply inverseRoot_reaches_dyadic hy
  have he := inverseParity_bounds y
  unfold inverseExponent
  omega

/-- The common rational score is positive whenever its two scalar inputs are positive. -/
theorem predecessorScore_pos {W K : ℚ} (hW : 0 < W) (hK : 0 < K)
    {y : ℕ} (hy : ¬ 3 ∣ y) (q start : ℕ) : 0 < predecessorScore W K y q start := by
  apply lt_min hW
  exact div_pos hK (by exact_mod_cast predecessorMax_pos hy q start)

/-- The common rational score never exceeds the allowed score ceiling. -/
theorem predecessorScore_le (W K : ℚ) (y q start : ℕ) :
    predecessorScore W K y q start ≤ W := min_le_left _ _

/-- A lower bound for total residue weight gives the same score on either candidate block. -/
theorem predecessorScore_le_sum {y q start j : ℕ} (hy : ¬ 3 ∣ y) (hq : 0 < q)
    (hj : j ≤ 1) (W K : ℚ) (z : ℕ → ℝ)
    (hz : ∀ r ∈ unitResidues q, 0 ≤ z r) (hK : (K : ℝ) ≤ ∑ r ∈ unitResidues q, z r) :
    (predecessorScore W K y q start : ℝ) ≤
      ∑ x ∈ unitPredecessorBlock y q (start + j * 3 ^ q), z (x % 3 ^ q) / x := by
  have hmin : (predecessorScore W K y q start : ℝ) ≤
      (K : ℝ) / (predecessorMax y q start : ℝ) := by
    exact_mod_cast (min_le_right W (K / (predecessorMax y q start : ℚ)))
  apply hmin.trans
  calc
    (K : ℝ) / (predecessorMax y q start : ℝ) ≤
        (∑ r ∈ unitResidues q, z r) / (predecessorMax y q start : ℝ) :=
      div_le_div_of_nonneg_right hK (Nat.cast_nonneg _)
    _ = ∑ x ∈ unitPredecessorBlock y q (start + j * 3 ^ q),
        z (x % 3 ^ q) / (predecessorMax y q start : ℝ) := by
      rw [← sum_unitPredecessorBlock hy hq (start + j * 3 ^ q) z, Finset.sum_div]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro x hx
      exact div_le_div_of_nonneg_left (hz _ (unitPredecessorBlock_residue_mem hq hx))
        (by exact_mod_cast (unitPredecessorBlock_physical hy hx).1)
        (by exact_mod_cast (unitPredecessorBlock_bounds hy hj hx).2)

end WordCertDensity.Roots
