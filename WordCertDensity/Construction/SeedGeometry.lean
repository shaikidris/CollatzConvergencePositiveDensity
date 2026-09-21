/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.Seed
public import WordCertDensity.Construction.OffsetEnvelope
public import WordCertDensity.Transfer.Physical

/-!
# Local seed geometry and physical realization

The fixed-depth window pays both contraction and offset. At every sufficiently
large odd parent, affine compatibility is exactly physical realization, and
the endpoint clears the next seed height. No parent-convergence premise enters.
-/

@[expose] public section

namespace WordCertDensity.Construction

/-- Every seed offset is strictly below the elementary power-of-two envelope. -/
theorem seedWords_offset_lt {b : ℕ} {w : ValuationWord} (hw : w ∈ seedWords b) :
    w.offset < (2 : ℚ) ^ b := by
  have hlen := ((mem_seedWords w b).mp hw).1
  have hc := word_offset_le_depth w
  rw [hlen] at hc
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℚ) ≤ 3 / 2)
    (by norm_num : (3 / 2 : ℚ) ≤ 2) b
  linarith

/-- The exact binary displacement gives the strict exponential slope bound. -/
theorem seedWords_weight_lt {b : ℕ} (hb : 32 ^ 5 ≤ b) {w : ValuationWord}
    (hw : w ∈ seedWords b) : Transfer.weight w < (2 : ℝ) ^ (-(b : ℝ) / 3) := by
  apply (Real.log_lt_log_iff (Transfer.weight_pos w) (by positivity)).mp
  rw [log_weight_eq, Real.log_rpow (by norm_num)]
  have h := mul_lt_mul_of_pos_right (seedWords_displacement hb hw)
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
  nlinarith

/-- The displacement margin pays twice the next-height growth factor. -/
theorem seed_step_margin {b : ℕ} (hb : 32 ^ 5 ≤ b) :
    (1 : ℝ) + 4 * (b / 100 : ℕ) ≤ (b : ℝ) / 3 := by
  have hdiv : 100 * (b / 100) ≤ b := by omega
  have hdivR : (100 : ℝ) * (b / 100 : ℕ) ≤ b := by exact_mod_cast hdiv
  have hbase : (32 : ℝ) ^ 5 ≤ b := by exact_mod_cast hb
  nlinarith

/-- A rational slope bound retains the factor two that pays the local offset. -/
theorem seedWords_slope_half {b : ℕ} (hb : 32 ^ 5 ≤ b) {w : ValuationWord}
    (hw : w ∈ seedWords b) : w.slope < 1 / (2 * (16 : ℚ) ^ (b / 100)) := by
  have hlog16 : Real.log 16 = 4 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 4
    norm_num at h
    exact h
  have hlog : Real.log (1 / (2 * (16 : ℝ) ^ (b / 100))) =
      -((1 : ℝ) + 4 * (b / 100 : ℕ)) * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by positivity), Real.log_one,
      Real.log_mul (by norm_num) (by positivity), Real.log_pow, hlog16]
    ring
  have hlt : Real.log (Transfer.weight w) <
      Real.log (1 / (2 * (16 : ℝ) ^ (b / 100))) := by
    rw [log_weight_eq, hlog]
    have hm := (seed_step_margin hb).trans_lt (seedWords_displacement hb hw)
    have h := mul_lt_mul_of_pos_right hm (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    nlinarith
  have h := (Real.log_lt_log_iff (Transfer.weight_pos w) (by positivity)).mp hlt
  change (w.slope : ℝ) < _ at h
  have hc : (w.slope : ℝ) < ((1 / (2 * (16 : ℚ) ^ (b / 100)) : ℚ) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow] using h
  exact Rat.cast_lt.mp hc

/-- The manuscript's next-stage rational contraction follows from the paid bound. -/
theorem seedWords_slope_le {b : ℕ} (hb : 32 ^ 5 ≤ b) {w : ValuationWord}
    (hw : w ∈ seedWords b) : w.slope ≤ ((16 : ℚ) ^ (b / 100))⁻¹ := by
  apply (seedWords_slope_half hb hw).le.trans
  rw [inv_eq_one_div]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  have h : (0 : ℚ) ≤ 16 ^ (b / 100) := by positivity
  linarith

/-- At a large parent the offset occupies strictly less than half its value. -/
theorem seedWords_offset_half {b root : ℕ} (hb : 1 ≤ b) (hroot : 16 ^ b ≤ root)
    {w : ValuationWord} (hw : w ∈ seedWords b) : w.offset < (root : ℚ) / 2 := by
  have hp : (2 : ℚ) * 2 ^ b ≤ 16 ^ b := by
    calc
      _ = (2 : ℚ) ^ (b + 1) := by rw [pow_succ]; ring
      _ ≤ (2 : ℚ) ^ (4 * b) := pow_le_pow_right₀ (by norm_num) (by omega)
      _ = _ := by rw [pow_mul]; norm_num
  have hr : (16 : ℚ) ^ b ≤ root := by exact_mod_cast hroot
  have hc := seedWords_offset_lt hw
  linarith

/-- Every realized seed block pays the exact next-height factor. -/
theorem seedWords_source_growth {b root source : ℕ} (hb : 32 ^ 5 ≤ b)
    (hroot : 16 ^ b ≤ root) {w : ValuationWord} (hw : w ∈ seedWords b)
    (hphysical : PhysicalHistory w root source) : 16 ^ (b / 100) * root < source := by
  have hoff := seedWords_offset_half (by omega : 1 ≤ b) hroot hw
  have hs := (lt_div_iff₀ (by positivity : (0 : ℚ) < 2 * 16 ^ (b / 100))).mp
    (seedWords_slope_half hb hw)
  have hrootlt : (root : ℚ) < 2 * w.slope * source := by
    have heq := hphysical.affine_eq
    linarith
  have hx : (0 : ℚ) < source := by exact_mod_cast hphysical.source_pos
  have hg : (16 : ℚ) ^ (b / 100) * root < source := by
    calc
      _ < 16 ^ (b / 100) * (2 * w.slope * source) :=
        mul_lt_mul_of_pos_left hrootlt (by positivity)
      _ = (w.slope * (2 * 16 ^ (b / 100))) * source := by ring
      _ < source := by simpa using mul_lt_mul_of_pos_right hs hx
  exact_mod_cast hg

/-- The endpoint of every physical seed block satisfies the next stage's height guard. -/
theorem seedWords_source_height {b root source : ℕ} (hb : 32 ^ 5 ≤ b)
    (hroot : 16 ^ b ≤ root) {w : ValuationWord} (hw : w ∈ seedWords b)
    (hphysical : PhysicalHistory w root source) : 16 ^ (b + b / 100) ≤ source := by
  calc
    _ = 16 ^ (b / 100) * 16 ^ b := by rw [pow_add]; ring
    _ ≤ 16 ^ (b / 100) * root := Nat.mul_le_mul_left _ hroot
    _ ≤ source := (seedWords_source_growth hb hroot hw hphysical).le

/-- Every affine-compatible seed word is an actual positive odd inverse history. -/
theorem seedWords_compatible_iff {b root q : ℕ} (hb : 32 ^ 5 ≤ b)
    (hroot : 16 ^ b ≤ root) (hodd : Odd root) (hq : b ≤ q)
    {w : ValuationWord} (hw : w ∈ seedWords b) :
    (root : ZMod (3 ^ q)) ∈ Set.range (Transfer.wordMap w q) ↔
      ∃ source : ℕ, PhysicalHistory w root source := by
  have hlen := ((mem_seedWords w b).mp hw).1
  have hoff := seedWords_offset_half (by omega : 1 ≤ b) hroot hw
  have hr : (0 : ℚ) < root := by
    exact_mod_cast lt_of_lt_of_le (pow_pos (by decide : 0 < 16) b) hroot
  exact Transfer.mem_range_wordMap_iff_physical w (hlen ▸ hq) root hodd (by linarith)

/-- An affine-compatible seed has exactly one physical endpoint above the next height. -/
theorem seedWords_realizes {b root q : ℕ} (hb : 32 ^ 5 ≤ b)
    (hroot : 16 ^ b ≤ root) (hodd : Odd root) (hq : b ≤ q)
    {w : ValuationWord} (hw : w ∈ seedWords b)
    (hcompatible : (root : ZMod (3 ^ q)) ∈ Set.range (Transfer.wordMap w q)) :
    ∃! source : ℕ, PhysicalHistory w root source ∧ 16 ^ (b + b / 100) ≤ source := by
  obtain ⟨source, hp⟩ := (seedWords_compatible_iff hb hroot hodd hq hw).mp hcompatible
  exact ⟨source, ⟨hp, seedWords_source_height hb hroot hw hp⟩,
    fun _ h => h.1.source_unique hp⟩

end WordCertDensity.Construction
