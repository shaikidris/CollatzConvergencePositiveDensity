/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.WordMoment
public import WordCertDensity.Analytic.HeadScalars

/-! # Fixed-time centered geometric tails with the upper-tail correction -/

@[expose] public section

namespace WordCertDensity.Reference

/-- The conservative rational pole gives the fixed-time positive Chernoff exponent. -/
theorem word_upperTail_rational (n : ℕ) {s m : ℝ} (hs0 : 0 ≤ s) (hs : s < 2 / 3) :
    Gated.probability (wordPMF n) (fun w => m ≤ ValuationWord.centeredTotal w) ≤
      Real.exp (-s * m + (n : ℝ) * (s ^ 2 / (1 - (3 / 2 : ℝ) * s))) := by
  have hlog : s < Real.log 2 := by linarith [Head.log_two_lower]
  have hp : (Real.log 2)⁻¹ ≤ (3 / 2 : ℝ) := by
    apply (inv_le_iff_one_le_mul₀ GeometricLog.log_two_pos).mpr
    linarith [Head.log_two_lower]
  have hd : 0 < 1 - (3 / 2 : ℝ) * s := by linarith
  have hden : 1 - (3 / 2 : ℝ) * s ≤ 1 - (Real.log 2)⁻¹ * s := by
    nlinarith [mul_le_mul_of_nonneg_right hp hs0]
  have hdiv : s ^ 2 / (1 - (Real.log 2)⁻¹ * s) ≤ s ^ 2 / (1 - (3 / 2 : ℝ) * s) :=
    div_le_div_of_nonneg_left (sq_nonneg s) hd hden
  exact (word_upperTail_le n hs0 hlog).trans (Real.exp_le_exp.mpr
    (add_le_add (le_refl (-s * m)) (mul_le_mul_of_nonneg_left hdiv (Nat.cast_nonneg n))))

/-- The fixed-time positive tail pays the geometric denominator correction 3m. -/
theorem word_upperTail_fixedTime {n : ℕ} (hn : 0 < n) {m : ℝ} (hm : 0 ≤ m) :
    Gated.probability (wordPMF n) (fun w => m ≤ ValuationWord.centeredTotal w) ≤
      Real.exp (-(m ^ 2 / (4 * (n : ℝ) + 3 * m))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  let d : ℝ := 2 * n + (3 / 2 : ℝ) * m
  have hd : 0 < d := by dsimp [d]; positivity
  have ht0 : 0 ≤ m / d := div_nonneg hm hd.le
  have ht : m / d < (2 / 3 : ℝ) := by
    apply (div_lt_iff₀ hd).mpr
    dsimp [d]
    nlinarith
  have hslack : 1 - (3 / 2 : ℝ) * (m / d) = 2 * n / d := by
    dsimp [d]
    field_simp
    ring
  have he : -(m / d) * m + (n : ℝ) * ((m / d) ^ 2 / (1 - (3 / 2 : ℝ) * (m / d))) =
      -(m ^ 2 / (4 * (n : ℝ) + 3 * m)) := by
    rw [hslack]
    have hden : 4 * (n : ℝ) + 3 * m = 2 * d := by dsimp [d]; ring
    rw [hden]
    field_simp
    ring
  exact (word_upperTail_rational n ht0 ht).trans_eq (congrArg Real.exp he)

/-- The fixed-time negative tail has the smaller quadratic denominator 4B. -/
theorem word_lowerTail_fixedTime {n : ℕ} (hn : 0 < n) {m : ℝ} (hm : 0 ≤ m) :
    Gated.probability (wordPMF n) (fun w => ValuationWord.centeredTotal w ≤ -m) ≤
      Real.exp (-(m ^ 2 / (4 * (n : ℝ)))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : 0 ≤ m / (2 * (n : ℝ)) := by positivity
  have he : -(m / (2 * (n : ℝ))) * m + (n : ℝ) * (m / (2 * (n : ℝ))) ^ 2 =
      -(m ^ 2 / (4 * (n : ℝ))) := by
    field_simp
    ring
  exact (word_lowerTail_le n ht).trans_eq (congrArg Real.exp he)

/-- The original iid valuation window has the corrected two-sided fixed-time bound. -/
theorem word_absTail_fixedTime {n : ℕ} (hn : 0 < n) {m : ℝ} (hm : 0 ≤ m) :
    Gated.probability (wordPMF n) (fun w => m ≤ |ValuationWord.centeredTotal w|) ≤
      2 * Real.exp (-(m ^ 2 / (4 * (n : ℝ) + 3 * m))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h := Gated.probability_mono_on_support (wordPMF n)
    (fun w => m ≤ |ValuationWord.centeredTotal w|)
    (fun w => m ≤ ValuationWord.centeredTotal w ∨ ValuationWord.centeredTotal w ≤ -m)
    (fun w _ hw => by
      rcases le_or_gt 0 (ValuationWord.centeredTotal w) with hs | hs
      · exact Or.inl (by simpa only [abs_of_nonneg hs] using hw)
      · exact Or.inr (by rw [abs_of_neg hs] at hw; linarith))
  have hdiv : m ^ 2 / (4 * (n : ℝ) + 3 * m) ≤ m ^ 2 / (4 * (n : ℝ)) :=
    div_le_div_of_nonneg_left (sq_nonneg m) (by positivity) (by linarith)
  have hl := (word_lowerTail_fixedTime hn hm).trans (Real.exp_le_exp.mpr (neg_le_neg hdiv))
  have hu := Gated.probability_or_le (wordPMF n)
    (fun w => m ≤ ValuationWord.centeredTotal w) (fun w => ValuationWord.centeredTotal w ≤ -m)
  exact (h.trans hu).trans (by simpa only [two_mul] using add_le_add (word_upperTail_fixedTime hn hm) hl)

end WordCertDensity.Reference
