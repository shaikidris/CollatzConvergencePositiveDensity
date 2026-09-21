/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The positive-letter map and atom proof are adapted from Lech Mazur,
Copyright 2026 Lech Mazur, under Apache License 2.0. The source LICENSE and
NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
This version proves normalization directly using the geometric series.
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Data.PNat.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Positive geometric letters

The auxiliary law has probability two to the negative letter at every
positive integer. It concerns independent reference words, not the valuations
of an arbitrary chosen collection of integer trajectories.
-/

@[expose] public section

namespace WordCertDensity

namespace Reference

/-- A geometric law on naturals, with mass one half to the successor power. -/
noncomputable def geometricNat : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1)), by
    have h : HasSum (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) 1 := by
      simpa [pow_succ] using hasSum_geometric_two.mul_right (1 / 2 : ℝ)
    exact ENNReal.hasSum_coe.mpr (by
      simpa using h.toNNReal (fun n => by positivity))⟩

/-- The reference valuation letter is the positive successor of a geometric natural. -/
noncomputable def geometricLetter : PMF ℕ+ :=
  geometricNat.map Nat.succPNat

/-- The natural geometric atom, viewed as a real number. -/
theorem geometricNat_toReal (n : ℕ) :
    (geometricNat n).toReal = (1 / 2 : ℝ) ^ (n + 1) := by
  change (ENNReal.ofReal ((1 / 2 : ℝ) ^ (n + 1))).toReal = _
  exact ENNReal.toReal_ofReal (by positivity)

/-- Mapping to positive letters preserves the unique predecessor atom. -/
theorem geometricLetter_apply (a : ℕ+) :
    geometricLetter a = geometricNat a.natPred := by
  rw [geometricLetter, PMF.map_apply, tsum_eq_single a.natPred]
  · simp
  · intro n hn
    have hne : a ≠ Nat.succPNat n := by
      intro h
      have heq := congrArg PNat.natPred h
      simp only [Nat.natPred_succPNat] at heq
      exact hn heq.symm
    simp [hne]

/-- The literal real-valued probability of a positive valuation letter. -/
theorem geometricLetter_toReal (a : ℕ+) :
    (geometricLetter a).toReal = (1 / 2 : ℝ) ^ (a : ℕ) := by
  rw [geometricLetter_apply, geometricNat_toReal]
  have heq : a.natPred + 1 = (a : ℕ) :=
    congrArg PNat.val (PNat.succPNat_natPred a)
  rw [heq]

/-- Every positive integer occurs with positive reference probability. -/
theorem geometricLetter_toReal_pos (a : ℕ+) : 0 < (geometricLetter a).toReal := by
  rw [geometricLetter_toReal]
  positivity

/-- The support is all positive letters. -/
theorem geometricLetter_mem_support (a : ℕ+) : a ∈ geometricLetter.support := by
  rw [PMF.mem_support_iff]
  intro hzero
  have hpos := geometricLetter_toReal_pos a
  simp [hzero] at hpos

end Reference

end WordCertDensity
