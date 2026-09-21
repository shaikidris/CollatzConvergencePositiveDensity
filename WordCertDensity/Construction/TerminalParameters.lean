/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.FirstCrossing
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Exact integer parameters for the terminal barrier

The ceiling-log is computed by Nat.clog, with a proved identification to the
real logarithmic formula. Integer subtraction in the radius is proved exact
on the manuscript domain in TerminalRadius.
-/

namespace WordCertDensity.Construction

/-- Exact computable ceiling of the binary logarithm of 3^v. -/
def terminalJ (v : ℕ) : ℕ := Nat.clog 2 (3 ^ v)

/-- The literal width floor. -/
def terminalWidth (b : ℕ) : ℕ := 3 * b / 5

/-- First depth at which a miss is required. -/
def terminalLow (b : ℕ) : ℕ := b - terminalWidth b

/-- Last eligible crossing depth. -/
def terminalHigh (b : ℕ) : ℕ := b + terminalWidth b

/-- The literal terminal precision floor. -/
def terminalPrecision (b : ℕ) : ℕ := b / 100

/-- The radius, with no subtraction truncation once b is at least 200. -/
def terminalRadius (b : ℕ) : ℕ :=
  2 * terminalWidth b - terminalJ (terminalWidth b) - 2 * terminalPrecision b

/-- The manuscript's integer barrier at each possible word depth. -/
def terminalBarrier (b u s : ℕ) : ℤ :=
  2 * (b : ℤ) + terminalJ (s - b) - terminalJ (b - s) + u - terminalRadius b

/-- Nat.clog is exactly the real ceiling in the manuscript, also at zero. -/
theorem terminalJ_eq (v : ℕ) : terminalJ v = ⌈Head.logRatio * v⌉₊ := by
  calc
    _ = ⌈Real.logb 2 ((3 ^ v : ℕ) : ℝ)⌉₊ := (Real.natCeil_logb_natCast 2 (3 ^ v)).symm
    _ = _ := by
      congr 1
      simp only [Nat.cast_pow, Nat.cast_ofNat, Real.logb, Real.log_pow]
      unfold Head.logRatio
      ring

@[simp] theorem terminalJ_zero : terminalJ 0 = 0 := by simp [terminalJ]

/-- The exact integer ceiling is nondecreasing in depth. -/
theorem terminalJ_mono : Monotone terminalJ := by
  intro a b hab
  rw [terminalJ_eq, terminalJ_eq]
  exact Nat.ceil_mono (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hab)
    (by linarith [Head.one_lt_logRatio]))

/-- Both real bounds on the ceiling retain their exact one-unit rounding loss. -/
theorem terminalJ_bounds (v : ℕ) :
    Head.logRatio * v ≤ terminalJ v ∧ (terminalJ v : ℝ) < Head.logRatio * v + 1 := by
  rw [terminalJ_eq]
  exact ⟨Nat.le_ceil _, Nat.ceil_lt_add_one
    (mul_nonneg (by linarith [Head.one_lt_logRatio]) (Nat.cast_nonneg _))⟩

/-- The width never exceeds the central depth. -/
theorem terminalWidth_le (b : ℕ) : terminalWidth b ≤ b := by
  unfold terminalWidth
  omega

/-- The width floor retains the two cleared-integer bounds. -/
theorem terminalWidth_bounds (b : ℕ) :
    5 * terminalWidth b ≤ 3 * b ∧ 3 * b ≤ 5 * terminalWidth b + 4 := by
  unfold terminalWidth
  omega

/-- The precision floor is bounded above without any domain restriction. -/
theorem terminalPrecision_upper (b : ℕ) : 100 * terminalPrecision b ≤ b := by
  unfold terminalPrecision
  omega

/-- On the terminal domain the precision retains at least b/200. -/
theorem terminalPrecision_lower {b : ℕ} (hb : 200 ≤ b) :
    (b : ℝ) / 200 ≤ terminalPrecision b := by
  have h : b ≤ 200 * terminalPrecision b := by unfold terminalPrecision; omega
  have hr : (b : ℝ) ≤ 200 * (terminalPrecision b : ℝ) := by exact_mod_cast h
  linarith

/-- The barrier is nondecreasing, including the change of formula at the center. -/
theorem terminalBarrier_mono (b u : ℕ) : Monotone (terminalBarrier b u) := by
  intro s t hst
  have hright := terminalJ_mono (show s - b ≤ t - b by omega)
  have hleft := terminalJ_mono (show b - t ≤ b - s by omega)
  have hr : (terminalJ (s - b) : ℤ) ≤ terminalJ (t - b) := by exact_mod_cast hright
  have hl : (terminalJ (b - t) : ℤ) ≤ terminalJ (b - s) := by exact_mod_cast hleft
  unfold terminalBarrier
  omega

end WordCertDensity.Construction
