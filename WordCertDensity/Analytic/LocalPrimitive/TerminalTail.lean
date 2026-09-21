/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.FirstPassage
import WordCertDensity.Analytic.Typical
import Mathlib.Tactic

/-! # The original-law terminal first-passage tail -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

open scoped Classical

/-- The post-passage window ends beyond nine tenths of the remaining layer. -/
def terminalPassageEvent (s m P : ℕ) (w : ValuationWord) : Prop :=
  ∃ i : Fin (s / 2 + 1), horizonTailEvent s 0 i w ∧
    9 * m < 10 * ((i : ℕ) + 1 + P)

/-- A late passage forces the fixed prefix at floor(17m/20) to remain
below the crossed level. -/
theorem terminalPassageEvent_prefix_total_le (s m P : ℕ) (w : ValuationWord)
    (hP : 20 * P ≤ m) (he : terminalPassageEvent s m P w) :
    ValuationWord.total (w.take (2 * (17 * m / 20))) ≤ s := by
  obtain ⟨i, hi, hlate⟩ := he
  have hq : 17 * m / 20 ≤ (i : ℕ) := by omega
  exact (ValuationWord.total_take_mono w (Nat.mul_le_mul_left 2 hq)).trans hi.1

/-- The exact floor cutoff is far enough above the binomial midpoint. -/
theorem terminal_cutoff_deviation (s m : ℕ) (hm : 40 ≤ m) (hs : 5 * s ≤ 16 * m) :
    (m : ℝ) / 20 ≤ ((2 * (17 * m / 20) : ℕ) : ℝ) - (s : ℝ) / 2 := by
  have hfloor : 17 * m < 20 * (17 * m / 20) + 20 := by omega
  have hf : (17 : ℝ) * m < 20 * (17 * m / 20 : ℕ) + 20 := by exact_mod_cast hfloor
  have hs' : (5 : ℝ) * s ≤ 16 * m := by exact_mod_cast hs
  have hm' : (40 : ℝ) ≤ m := by exact_mod_cast hm
  push_cast
  linarith

/-- The fixed-cut binomial upper tail pays the manuscript's terminal exponent. -/
theorem terminal_binomial_tail_le (s m : ℕ) (hs : 0 < s)
    (hm : 40 ≤ m) (hsize : 5 * s ≤ 16 * m) :
    Gated.probability (Probability.fairBinomial s)
      (fun k => 2 * (17 * m / 20) ≤ k) ≤ Real.exp (-(m : ℝ) / 640) := by
  have hd := terminal_cutoff_deviation s m hm hsize
  have hpos : (0 : ℝ) < s := by exact_mod_cast hs
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hsize' : (5 : ℝ) * s ≤ 16 * m := by exact_mod_cast hsize
  apply (Probability.fairBinomial_upperTail_le s (2 * (17 * m / 20)) hs (by linarith)).trans
  apply Real.exp_le_exp.mpr
  apply (div_le_iff₀ hpos).mpr
  have hsq := sq_nonneg (((2 * (17 * m / 20) : ℕ) : ℝ) - (s : ℝ) / 2 - (m : ℝ) / 20)
  have hprod := mul_nonneg hm0 (show 0 ≤ ((2 * (17 * m / 20) : ℕ) : ℝ) -
    (s : ℝ) / 2 - (m : ℝ) / 20 by linarith)
  have hsizeprod := mul_le_mul_of_nonneg_left hsize' hm0
  nlinarith

/-- The original common-word terminal event has probability at most
exp(-m/640), with the actual passage event and fixed P-window. -/
theorem terminalPassage_probability_le (s m P L : ℕ) (hs : 0 < s)
    (hm : 40 ≤ m) (hsize : 5 * s ≤ 16 * m) (hP : 20 * P ≤ m)
    (hL : s / 2 + 1 ≤ L) :
    Gated.probability (Reference.wordPMF (2 * L)) (terminalPassageEvent s m P) ≤
      Real.exp (-(m : ℝ) / 640) := by
  by_cases hq : 17 * m / 20 ≤ L
  · have hmono := Gated.probability_mono_on_support (Reference.wordPMF (2 * L))
      (terminalPassageEvent s m P)
      (fun w => ValuationWord.total (w.take (2 * (17 * m / 20))) ≤ s)
      (fun w _ he => terminalPassageEvent_prefix_total_le s m P w hP he)
    have hmap := Gated.probability_map (Reference.wordPMF (2 * L))
      (fun w => w.take (2 * (17 * m / 20))) (fun w => ValuationWord.total w ≤ s)
    rw [Reference.wordPMF_map_take_of_le (Nat.mul_le_mul_left 2 hq)] at hmap
    rw [← hmap, Reference.word_total_le_binomial_probability] at hmono
    exact hmono.trans (terminal_binomial_tail_le s m hs hm hsize)
  · have hempty : ∀ w, ¬ terminalPassageEvent s m P w := by
      intro w he
      obtain ⟨i, _, hlate⟩ := he
      have hidx := i.isLt
      omega
    simp only [Gated.probability, hempty, if_false, tsum_zero, ENNReal.toReal_zero]
    exact (Real.exp_pos _).le

end WordCertDensity.LocalPrimitive
