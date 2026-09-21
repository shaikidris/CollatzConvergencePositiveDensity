/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The dyadic-iteration proof is adapted from Lech Mazur, Copyright 2026 Lech Mazur,
under the Apache License, Version 2.0. Modifications use the local ordinaryStep
and reachability interfaces. The source LICENSE and NOTICE are retained at
research/sources/mazur_830b9d3f38f2/ in the repository root.
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Ordinary Collatz trajectories and finite clocks

Each odd step is one application of $3x+1$; halvings are counted separately.
A finite hitting witness expresses a budget without assigning a finite time
to a nonconvergent orbit. Zero is totalized by the map and excluded from good sets.
-/

@[expose] public section

namespace WordCertDensity

/-- The ordinary Collatz map on naturals, including its harmless value at zero. -/
def ordinaryStep (n : ℕ) : ℕ :=
  if Even n then n / 2 else 3 * n + 1

/-- Reaching a target in exactly the specified number of ordinary steps. -/
def ReachesIn (x target steps : ℕ) : Prop :=
  (ordinaryStep^[steps]) x = target

/-- Existence of a finite ordinary hitting time within a real budget. -/
def ReachesWithin (x target : ℕ) (budget : ℝ) : Prop :=
  ∃ steps : ℕ, ReachesIn x target steps ∧ (steps : ℝ) ≤ budget

/-- Positive sources reaching a target within the specified logarithmic clock. -/
def goodTarget (target : ℕ) (c : ℝ) : Set ℕ :=
  {x | 0 < x ∧ ReachesWithin x target (c * Real.log x)}

/-- The paper's set of positive integers reaching one within a fixed clock. -/
def good (c : ℝ) : Set ℕ := goodTarget 1 c

/-- Zero stays zero; it is not silently treated as a convergent positive source. -/
@[simp] theorem ordinaryStep_zero : ordinaryStep 0 = 0 := by
  simp [ordinaryStep]

/-- The ordinary map has the expected even branch. -/
theorem ordinaryStep_of_even {n : ℕ} (hn : Even n) : ordinaryStep n = n / 2 := by
  simp [ordinaryStep, hn]

/-- The ordinary map has the expected odd branch. -/
theorem ordinaryStep_of_odd {n : ℕ} (hn : Odd n) : ordinaryStep n = 3 * n + 1 := by
  simp [ordinaryStep, Nat.not_even_iff_odd.mpr hn]

/-- No positive source is zero, regardless of the budget or target. -/
@[simp] theorem zero_not_mem_goodTarget (target : ℕ) (c : ℝ) : 0 ∉ goodTarget target c := by
  simp [goodTarget]

/-- One reaches itself at time zero for every clock. -/
@[simp] theorem one_mem_good (c : ℝ) : 1 ∈ good c := by
  refine ⟨by decide, 0, ?_, ?_⟩
  · rfl
  · simp

/-- Enlarging a real budget preserves a finite hitting witness. -/
theorem ReachesWithin.mono {x target : ℕ} {a b : ℝ}
    (h : ReachesWithin x target a) (hab : a ≤ b) : ReachesWithin x target b := by
  obtain ⟨steps, hsteps, hbudget⟩ := h
  exact ⟨steps, hsteps, hbudget.trans hab⟩

/-- The logarithmic good sets increase with the clock on positive integers. -/
theorem goodTarget_mono (target : ℕ) {c d : ℝ} (hcd : c ≤ d) :
    goodTarget target c ⊆ goodTarget target d := by
  intro x hx
  refine ⟨hx.1, hx.2.mono ?_⟩
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hx.1
  exact mul_le_mul_of_nonneg_right hcd (Real.log_nonneg hxone)

/-- Consecutive trajectory pieces add their ordinary step counts. -/
theorem ReachesIn.trans {x y z a b : ℕ}
    (hxy : ReachesIn x y a) (hyz : ReachesIn y z b) : ReachesIn x z (a + b) := by
  dsimp [ReachesIn] at *
  rw [Nat.add_comm, Function.iterate_add_apply, hxy]
  exact hyz

/-- Exactly `a` halvings remove an initial factor of `2^a`. -/
theorem ordinaryStep_iterate_pow_two_mul (a x : ℕ) :
    (ordinaryStep^[a]) (2 ^ a * x) = x := by
  induction a with
  | zero => simp
  | succ a ih =>
      have heven : Even (2 ^ (a + 1) * x) := by
        refine ⟨2 ^ a * x, ?_⟩
        rw [pow_succ]
        ring
      rw [Function.iterate_succ_apply, ordinaryStep_of_even heven]
      have hdiv : 2 ^ (a + 1) * x / 2 = 2 ^ a * x := by
        rw [pow_succ]
        simpa [mul_assoc, mul_comm, mul_left_comm] using
          Nat.mul_div_left (2 ^ a * x) (by norm_num : 0 < (2 : ℕ))
      rw [hdiv]
      exact ih

/-- An initial segment of the halving orbit retains the remaining power of two. -/
theorem ordinaryStep_iterate_pow_two_prefix (a j : ℕ) (hj : j ≤ a) :
    (ordinaryStep^[j]) (2 ^ a) = 2 ^ (a - j) := by
  have hp : 2 ^ a = 2 ^ j * 2 ^ (a - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj]
  rw [hp]
  exact ordinaryStep_iterate_pow_two_mul j (2 ^ (a - j))

/-- A dyadic predecessor pays one ordinary step for each initial halving. -/
theorem ReachesIn.pow_two_mul {x target steps : ℕ}
    (h : ReachesIn x target steps) (a : ℕ) :
    ReachesIn (2 ^ a * x) target (a + steps) :=
  ReachesIn.trans (ordinaryStep_iterate_pow_two_mul a x) h

/-- A negative budget cannot contain a finite nonnegative step count. -/
theorem not_reachesWithin_of_neg {x target : ℕ} {budget : ℝ} (hbudget : budget < 0) :
    ¬ ReachesWithin x target budget := by
  rintro ⟨steps, _, hsteps⟩
  exact (not_le_of_gt hbudget) ((Nat.cast_nonneg steps).trans hsteps)

/-- A hits-within witness can always be chosen to be the first hit. -/
theorem reachesWithin_iff_firstHit (x target : ℕ) (budget : ℝ) :
    ReachesWithin x target budget ↔
      ∃ steps : ℕ, ReachesIn x target steps ∧
        (∀ j < steps, ¬ ReachesIn x target j) ∧ (steps : ℝ) ≤ budget := by
  classical
  constructor
  · rintro ⟨steps, hsteps, hbudget⟩
    have hex : ∃ j, ReachesIn x target j := ⟨steps, hsteps⟩
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_, ?_⟩
    · intro j hj
      exact Nat.find_min hex hj
    · exact (Nat.cast_le.mpr (Nat.find_min' hex hsteps)).trans hbudget
  · rintro ⟨steps, hsteps, _, hbudget⟩
    exact ⟨steps, hsteps, hbudget⟩

/-- Dyadic predecessors remain within a logarithmic clock that pays each halving. -/
theorem goodTarget_pow_two_mul {target x : ℕ} {c : ℝ}
    (hclock : 1 ≤ c * Real.log 2) (hx : x ∈ goodTarget target c) (a : ℕ) :
    2 ^ a * x ∈ goodTarget target c := by
  obtain ⟨hxpos, steps, hsteps, hbudget⟩ := hx
  refine ⟨Nat.mul_pos (by positivity) hxpos, a + steps, hsteps.pow_two_mul a, ?_⟩
  have hxreal : (0 : ℝ) < x := by exact_mod_cast hxpos
  have hlog : Real.log ((2 ^ a * x : ℕ) : ℝ) = (a : ℝ) * Real.log 2 + Real.log x := by
    push_cast
    rw [Real.log_mul (by positivity) (ne_of_gt hxreal), Real.log_pow]
  rw [hlog, Nat.cast_add]
  have hpay := mul_le_mul_of_nonneg_left hclock (Nat.cast_nonneg a)
  nlinarith

end WordCertDensity
