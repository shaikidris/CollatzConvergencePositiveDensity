/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.StoppingTail
public import WordCertDensity.Reference.WaitingTime
public import WordCertDensity.Probability.FairBinomialTail
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The fixed-range precision timeout

The actual first-crossing deficit is bounded by two fair-binomial tails with
literal L-1 and E-1/N-1 endpoints. Integer cutoffs and the sharp centered tails
give epsilon(E) <= 2 exp(-E/75) <= 2^(-E/100) for E >= 256.
-/

@[expose] public section

namespace WordCertDensity.Construction

/-- The computational form of the manuscript's floor(2E/5). -/
def timeoutDepth (E : ℕ) : ℕ := 2 * E / 5

/-- The integer valuation cutoff at which depth N forces a crossing. -/
noncomputable def timeoutCutoff (E : ℕ) : ℕ :=
  ⌈Head.logRatio * timeoutDepth E + (3 : ℝ)⌉₊

/-- Both real rounding bounds, including zero precision. -/
theorem timeoutDepth_bounds (E : ℕ) :
    (timeoutDepth E : ℝ) ≤ 2 * E / 5 ∧
      2 * (E : ℝ) / 5 < timeoutDepth E + 1 := by
  have hu : 5 * timeoutDepth E ≤ 2 * E := by unfold timeoutDepth; omega
  have hl : 2 * E < 5 * (timeoutDepth E + 1) := by unfold timeoutDepth; omega
  constructor
  · have h : (5 : ℝ) * timeoutDepth E ≤ 2 * E := by exact_mod_cast hu
    linarith
  · have h : (2 : ℝ) * E < 5 * (timeoutDepth E + 1) := by exact_mod_cast hl
    linarith

/-- Natural division implements exactly the real floor in (S.binomial). -/
theorem timeoutDepth_eq_floor (E : ℕ) : timeoutDepth E = ⌊(2 : ℝ) * E / 5⌋₊ := by
  symm
  exact (Nat.floor_eq_iff (by positivity)).mpr (timeoutDepth_bounds E)

/-- The original deficit is controlled by the two exact waiting-time events. -/
theorem stoppedWords_deficit_binomial (E N L : ℕ) (hE : 0 < E) (hN : 0 < N)
    (hL : 0 < L) (hcross : Head.logRatio * N + 3 ≤ (L : ℝ)) :
    1 - Reference.stoppingMass (stoppedWords E) ≤
      Gated.probability (Probability.fairBinomial (L - 1)) (fun k => N ≤ k) +
      Gated.probability (Probability.fairBinomial (E - 1)) (fun k => k ≤ N - 1) := by
  have hno := Gated.probability_mono_on_support (Reference.wordPMF N) NoCrossing
    (fun w => w.total < L) (fun w hp hw => by
      have hn := (Reference.wordPMF_mem_support_iff N w).mp
        ((PMF.mem_support_iff _ _).mpr hp)
      have hd := noCrossing_displacement_lt hw
      simp only [displacement, hn] at hd
      have ht : (w.total : ℝ) < L := by linarith
      exact_mod_cast ht)
  change noCrossingProbability N ≤ _ at hno
  rw [Reference.word_total_lt_binomial_probability N L hL] at hno
  have hd := stoppedWords_deficit_le E N
  rw [Reference.word_total_ge_binomial_probability N E hN hE] at hd
  linarith

/-- Positive trial counts and both centered-distance guards in the fixed range. -/
theorem timeoutCutoff_guards (E : ℕ) (hE : 256 ≤ E) :
    0 < timeoutDepth E ∧ 0 < timeoutCutoff E - 1 ∧
      ((timeoutCutoff E - 1 : ℕ) : ℝ) ≤ 2 * E / 3 ∧
      (E : ℝ) / 15 ≤ timeoutDepth E - ((timeoutCutoff E - 1 : ℕ) : ℝ) / 2 ∧
      (E : ℝ) / 10 + 1 / 2 ≤
        ((E - 1 : ℕ) : ℝ) / 2 - ((timeoutDepth E - 1 : ℕ) : ℝ) := by
  have he : (256 : ℝ) ≤ E := by exact_mod_cast hE
  obtain ⟨hNu, hNl⟩ := timeoutDepth_bounds E
  have hN : 0 < timeoutDepth E := by unfold timeoutDepth; omega
  have hNp : (0 : ℝ) < timeoutDepth E := by exact_mod_cast hN
  have hlambda := Head.one_lt_logRatio
  have hceil := Nat.le_ceil (Head.logRatio * timeoutDepth E + (3 : ℝ))
  change Head.logRatio * timeoutDepth E + 3 ≤ (timeoutCutoff E : ℝ) at hceil
  have hL : 1 < timeoutCutoff E := by
    have hp : 1 < (timeoutCutoff E : ℝ) := by nlinarith
    exact_mod_cast hp
  have hprev := ((Nat.ceil_eq_iff (by omega : timeoutCutoff E ≠ 0)).mp
    (rfl : ⌈Head.logRatio * timeoutDepth E + (3 : ℝ)⌉₊ = timeoutCutoff E)).1
  have hupper : ((timeoutCutoff E - 1 : ℕ) : ℝ) <
      (8 / 5 : ℝ) * timeoutDepth E + 3 := by
    nlinarith [Head.logRatio_lt_eight_fifths]
  refine ⟨hN, by omega, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · rw [Nat.cast_sub (by omega : 1 ≤ E), Nat.cast_sub (by omega : 1 ≤ timeoutDepth E)]
    norm_num only [Nat.cast_one]
    linarith

/-- The displayed integer cutoffs specialize the exact two-binomial inclusion. -/
theorem stoppedWords_timeout_binomial (E : ℕ) (hE : 256 ≤ E) :
    1 - Reference.stoppingMass (stoppedWords E) ≤
      Gated.probability (Probability.fairBinomial (timeoutCutoff E - 1))
        (fun k => timeoutDepth E ≤ k) +
      Gated.probability (Probability.fairBinomial (E - 1))
        (fun k => k ≤ timeoutDepth E - 1) := by
  obtain ⟨hN, hL, _⟩ := timeoutCutoff_guards E hE
  exact stoppedWords_deficit_binomial E (timeoutDepth E) (timeoutCutoff E)
    (by omega) hN (by omega) (Nat.le_ceil _)

private theorem upper_timeout_tail (E : ℕ) (hE : 256 ≤ E) :
    Gated.probability (Probability.fairBinomial (timeoutCutoff E - 1))
      (fun k => timeoutDepth E ≤ k) ≤ Real.exp (-(E : ℝ) / 75) := by
  obtain ⟨_, hn, hnu, ha, _⟩ := timeoutCutoff_guards E hE
  have he : (0 : ℝ) ≤ E := Nat.cast_nonneg E
  have hnr : (0 : ℝ) < (timeoutCutoff E - 1 : ℕ) := by exact_mod_cast hn
  have hmid : ((timeoutCutoff E - 1 : ℕ) : ℝ) / 2 ≤ timeoutDepth E := by linarith
  refine (Probability.fairBinomial_upperTail_le _ _ hn hmid).trans ?_
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hnu (show 0 ≤ (E : ℝ) / 75 by positivity)
  have hs := mul_nonneg (show 0 ≤ (timeoutDepth E : ℝ) -
      ((timeoutCutoff E - 1 : ℕ) : ℝ) / 2 - (E : ℝ) / 15 by linarith)
    (show 0 ≤ (timeoutDepth E : ℝ) -
      ((timeoutCutoff E - 1 : ℕ) : ℝ) / 2 + (E : ℝ) / 15 by linarith)
  apply (div_le_iff₀ hnr).mpr
  nlinarith

private theorem lower_timeout_tail (E : ℕ) (hE : 256 ≤ E) :
    Gated.probability (Probability.fairBinomial (E - 1))
      (fun k => k ≤ timeoutDepth E - 1) ≤ Real.exp (-(E : ℝ) / 50) := by
  obtain ⟨_, _, _, _, ha⟩ := timeoutCutoff_guards E hE
  have he : (0 : ℝ) ≤ E := Nat.cast_nonneg E
  have hn : 0 < E - 1 := by omega
  have hnr : (0 : ℝ) < (E - 1 : ℕ) := by exact_mod_cast hn
  have hnu : ((E - 1 : ℕ) : ℝ) ≤ E := by exact_mod_cast Nat.sub_le E 1
  have hmid : ((timeoutDepth E - 1 : ℕ) : ℝ) ≤ ((E - 1 : ℕ) : ℝ) / 2 := by
    linarith
  refine (Probability.fairBinomial_lowerTail_le _ _ hn hmid).trans ?_
  apply Real.exp_le_exp.mpr
  have hm := mul_le_mul_of_nonneg_left hnu (show 0 ≤ (E : ℝ) / 50 by positivity)
  have hs := mul_nonneg (show 0 ≤ ((E - 1 : ℕ) : ℝ) / 2 -
      ((timeoutDepth E - 1 : ℕ) : ℝ) - (E : ℝ) / 10 by linarith)
    (show 0 ≤ ((E - 1 : ℕ) : ℝ) / 2 -
      ((timeoutDepth E - 1 : ℕ) : ℝ) + (E : ℝ) / 10 by linarith)
  apply (div_le_iff₀ hnr).mpr
  nlinarith

/-- The actual finite precision deficit satisfies the fixed exponential certificate. -/
theorem stoppedWords_timeout_exp (E : ℕ) (hE : 256 ≤ E) :
    1 - Reference.stoppingMass (stoppedWords E) ≤ 2 * Real.exp (-(E : ℝ) / 75) := by
  have hu := upper_timeout_tail E hE
  have hl := lower_timeout_tail E hE
  have hexp : Real.exp (-(E : ℝ) / 50) ≤ Real.exp (-(E : ℝ) / 75) := by
    apply Real.exp_le_exp.mpr
    have he : (0 : ℝ) ≤ E := Nat.cast_nonneg E
    linarith
  have hd := stoppedWords_timeout_binomial E hE
  linarith

/-- The scalar comparison to a real power holds from the literal cutoff 256. -/
theorem timeout_exp_le_rpow (E : ℕ) (hE : 256 ≤ E) :
    2 * Real.exp (-(E : ℝ) / 75) ≤ (2 : ℝ) ^ (-(E : ℝ) / 100) := by
  have he : (256 : ℝ) ≤ E := by exact_mod_cast hE
  have hlog : Real.log 2 < 7 / 10 := by linarith [Head.log_two_upper]
  have hgap := mul_nonneg (show 0 ≤ (E : ℝ) - 256 by linarith)
    (show 0 ≤ (1 / 75 : ℝ) - Real.log 2 / 100 by linarith)
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    2 * Real.exp (-(E : ℝ) / 75) = Real.exp (Real.log 2 - (E : ℝ) / 75) := by
      rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      congr 2
      ring
    _ ≤ Real.exp (Real.log 2 * (-(E : ℝ) / 100)) := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- Both bounds in (S.timeout), for the actual finite first-crossing family. -/
theorem stoppedWords_timeout (E : ℕ) (hE : 256 ≤ E) :
    1 - Reference.stoppingMass (stoppedWords E) ≤ 2 * Real.exp (-(E : ℝ) / 75) ∧
      2 * Real.exp (-(E : ℝ) / 75) ≤ (2 : ℝ) ^ (-(E : ℝ) / 100) :=
  ⟨stoppedWords_timeout_exp E hE, timeout_exp_le_rpow E hE⟩

end WordCertDensity.Construction
