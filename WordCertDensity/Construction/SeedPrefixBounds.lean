/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.SeedHistories

/-! # Deterministic seed-prefix valuation and clock bounds

The constants use the fixed splice, including the empty prefix. They do not
depend on the nonemptiness of any later physical subfamily.
-/

namespace WordCertDensity.Construction

/-- Largest permitted total valuation before the fixed splice. -/
noncomputable def seedPrefixValuationBound (b t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range t, (2 * seedSize b i + seedWidth (seedSize b i))

/-- Largest permitted ordinary clock before the fixed splice. -/
noncomputable def seedPrefixClockBound (b t : ℕ) : ℕ :=
  ∑ i ∈ Finset.range t, (3 * seedSize b i + seedWidth (seedSize b i))

theorem seedPrefixValuationBound_eq (b t : ℕ) :
    seedPrefixValuationBound b t = 2 * seedDepth b 0 t + seedRadius b 0 t := by
  simp [seedPrefixValuationBound, seedDepth, seedRadius, Finset.sum_add_distrib,
    Finset.mul_sum]

theorem seedPrefixClockBound_eq (b t : ℕ) :
    seedPrefixClockBound b t = 3 * seedDepth b 0 t + seedRadius b 0 t := by
  simp [seedPrefixClockBound, seedDepth, seedRadius, Finset.sum_add_distrib,
    Finset.mul_sum]

/-- Every retained prefix satisfies both deterministic integer bounds. -/
theorem seedBlocks_prefix_bounds {b : ℕ} {ws : List ValuationWord}
    (h : SeedBlocks b 0 ws) :
    (ValuationWord.total ws.flatten) ≤ seedPrefixValuationBound b ws.length ∧
      (ValuationWord.ordinaryCost ws.flatten) ≤ seedPrefixClockBound b ws.length := by
  have ht := (seedBlocks_total_bounds h).2
  have hd := seedBlocks_depth h
  rw [seedPrefixValuationBound_eq, seedPrefixClockBound_eq]
  constructor
  · exact ht
  · unfold ValuationWord.ordinaryCost
    omega

/-- The full incoming seed prefix never expands physical weight. -/
theorem seedBlocks_weight_le_one {b : ℕ} (hb : 32 ^ 5 ≤ b)
    {ws : List ValuationWord} (h : SeedBlocks b 0 ws) :
    Transfer.weight ws.flatten ≤ 1 := by
  have hs : (ValuationWord.slope ws.flatten) ≤ 1 := by
    apply (seedBlocks_slope_le hb h).trans
    apply (div_le_one (by positivity)).mpr
    simpa only [seedSize, Nat.zero_add] using
      pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 16) (seedSize_ge b ws.length)
  change ((ValuationWord.slope ws.flatten) : ℝ) ≤ 1
  exact_mod_cast hs

/-- Nonnegative seed displacement is bounded by the fixed valuation budget. -/
theorem seedBlocks_displacement_bounds {b : ℕ} (hb : 32 ^ 5 ≤ b)
    {ws : List ValuationWord} (h : SeedBlocks b 0 ws) :
    0 ≤ displacement ws.flatten ∧
      displacement ws.flatten ≤ seedPrefixValuationBound b ws.length := by
  have hl := Real.log_nonpos (Transfer.weight_pos ws.flatten).le
    (seedBlocks_weight_le_one hb h)
  rw [log_weight_eq] at hl
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : 0 ≤ Head.logRatio := by
    unfold Head.logRatio
    exact div_nonneg (Real.log_nonneg (by norm_num)) htwo.le
  have htotal : ((ValuationWord.total ws.flatten) : ℝ) ≤ seedPrefixValuationBound b ws.length := by
    exact_mod_cast (seedBlocks_prefix_bounds h).1
  constructor
  · nlinarith
  · unfold displacement
    have hn := mul_nonneg hratio (Nat.cast_nonneg ws.flatten.length : (0 : ℝ) ≤ _)
    linarith

end WordCertDensity.Construction
