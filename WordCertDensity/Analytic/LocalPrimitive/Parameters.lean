/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Tactic

/-! # Finite parameters for Appendix E's local primitive estimate

Appendix E fixes all quantities before selecting a conductor or frequency.
The paper writes dyadic quantities as rationals; these definitions clear their
denominators, so every member of the recipe is a natural number. This module
supplies no decay estimate: its all-level analytic consumer follows E-L5.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- The denominator of the paper's `δ = (16 · 10^B)⁻¹`. -/
def localPrimitiveDeltaDenom (B : ℕ) : ℕ := 16 * 10 ^ B

/-- The denominator of `d = 2⁻¹⁵⁷`, obtained from `ε = 2⁻⁷⁸`. -/
def localPrimitiveDDenom : ℕ := 2 ^ 157

/-- The denominator of `η = d / (32B)` for a positive requested order. -/
def localPrimitiveEtaDenom (B : ℕ) : ℕ := 32 * B * localPrimitiveDDenom

/-- Appendix E's `K = 16(B+1)/ε²`, after clearing the dyadic denominator. -/
def localPrimitiveK (B : ℕ) : ℕ := 16 * (B + 1) * 2 ^ 156

/-- Appendix E's finite recursion length. -/
def localPrimitiveR (B : ℕ) : ℕ := 4 * (localPrimitiveK B + 16 * (B + 1)) + 1

/-- Appendix E's horizontal scale `A = 64/δ`. -/
def localPrimitiveA (B : ℕ) : ℕ := 64 * localPrimitiveDeltaDenom B

/-- Appendix E's quartic-window coefficient `H = 2¹⁷ A²/δ`. -/
def localPrimitiveH (B : ℕ) : ℕ :=
  2 ^ 17 * localPrimitiveA B ^ 2 * localPrimitiveDeltaDenom B

/-- The recursively chosen vertical offsets from Appendix E. -/
def localPrimitiveV (B : ℕ) : ℕ → ℕ
  | 0 => localPrimitiveK B
  | i + 1 =>
      localPrimitiveV B i + localPrimitiveH B * (localPrimitiveV B i + 1) ^ 4 +
        localPrimitiveK B + 2

/-- The finite union depth `P = v_R + K + 2`. -/
def localPrimitiveP (B : ℕ) : ℕ :=
  localPrimitiveV B (localPrimitiveR B) + localPrimitiveK B + 2

/-- Appendix E's common square-root threshold `Z = 128 A(P+1)²/δ`. -/
def localPrimitiveZ (B : ℕ) : ℕ :=
  128 * localPrimitiveA B * (localPrimitiveP B + 1) ^ 2 * localPrimitiveDeltaDenom B

/-- The five integer lower bounds whose maximum defines Appendix E's `M`. -/
def localPrimitiveM (B : ℕ) : ℕ :=
  max (64 * B * localPrimitiveDDenom)
    (max (20 * (localPrimitiveP B + 1))
      (max ((2560 * (B + 1)) ^ 2)
        (max (localPrimitiveZ B ^ 2 * localPrimitiveEtaDenom B) 4096)))

/-- The local primitive coefficient `C_B^{loc} = (3M)^B`. -/
def localPrimitiveCoefficient (B : ℕ) : ℕ := (3 * localPrimitiveM B) ^ B

/-- The dyadic denominator used in `K` is positive. -/
theorem localPrimitiveDDenom_pos : 0 < localPrimitiveDDenom := by
  unfold localPrimitiveDDenom
  positivity

/-- Every delta denominator is positive. -/
theorem localPrimitiveDeltaDenom_pos (B : ℕ) : 0 < localPrimitiveDeltaDenom B := by
  unfold localPrimitiveDeltaDenom
  positivity

/-- At a positive requested order, the eta denominator is positive. -/
theorem localPrimitiveEtaDenom_pos {B : ℕ} (hB : 0 < B) :
    0 < localPrimitiveEtaDenom B := by
  unfold localPrimitiveEtaDenom
  exact Nat.mul_pos (Nat.mul_pos (by norm_num) hB) localPrimitiveDDenom_pos

/-- Every finite-recursion starting value is positive. -/
theorem localPrimitiveK_pos (B : ℕ) : 0 < localPrimitiveK B := by
  unfold localPrimitiveK
  positivity

/-- The finite recursion length is positive. -/
theorem localPrimitiveR_pos (B : ℕ) : 0 < localPrimitiveR B := by
  unfold localPrimitiveR
  omega

/-- Every recursively chosen vertical offset is positive. -/
theorem localPrimitiveV_pos (B i : ℕ) : 0 < localPrimitiveV B i := by
  induction i with
  | zero => exact localPrimitiveK_pos B
  | succ i ih =>
      rw [localPrimitiveV]
      omega

/-- The finite union depth is positive. -/
theorem localPrimitiveP_pos (B : ℕ) : 0 < localPrimitiveP B := by
  unfold localPrimitiveP
  omega

/-- The horizontal scale is positive. -/
theorem localPrimitiveA_pos (B : ℕ) : 0 < localPrimitiveA B := by
  unfold localPrimitiveA
  exact Nat.mul_pos (by norm_num) (localPrimitiveDeltaDenom_pos B)

/-- The quartic-window coefficient is positive. -/
theorem localPrimitiveH_pos (B : ℕ) : 0 < localPrimitiveH B := by
  unfold localPrimitiveH
  exact Nat.mul_pos
    (Nat.mul_pos (pow_pos (by norm_num) _) (pow_pos (localPrimitiveA_pos B) _))
    (localPrimitiveDeltaDenom_pos B)

/-- The common square-root threshold is positive. -/
theorem localPrimitiveZ_pos (B : ℕ) : 0 < localPrimitiveZ B := by
  unfold localPrimitiveZ
  exact Nat.mul_pos
    (Nat.mul_pos
      (Nat.mul_pos (by norm_num) (localPrimitiveA_pos B))
      (pow_pos (by omega) _))
    (localPrimitiveDeltaDenom_pos B)

/-- The recipe's maximum pays the first, entropy-loss lower bound. -/
theorem localPrimitiveM_ge_entropy (B : ℕ) :
    64 * B * localPrimitiveDDenom ≤ localPrimitiveM B := by
  unfold localPrimitiveM
  exact Nat.le_max_left _ _

/-- The recipe's maximum pays the finite-union horizon lower bound. -/
theorem localPrimitiveM_ge_horizon (B : ℕ) :
    20 * (localPrimitiveP B + 1) ≤ localPrimitiveM B := by
  unfold localPrimitiveM
  exact le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)

/-- The recipe's maximum pays the post-exit tail lower bound. -/
theorem localPrimitiveM_ge_tail (B : ℕ) :
    (2560 * (B + 1)) ^ 2 ≤ localPrimitiveM B := by
  unfold localPrimitiveM
  exact le_trans (Nat.le_max_left _ _) (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _))

/-- The recipe's maximum pays the terminal exceptional-event lower bound. -/
theorem localPrimitiveM_ge_terminal (B : ℕ) :
    localPrimitiveZ B ^ 2 * localPrimitiveEtaDenom B ≤ localPrimitiveM B := by
  unfold localPrimitiveM
  exact le_trans (Nat.le_max_left _ _)
    (le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))

/-- The fixed numerical floor is part of the coefficient recipe. -/
theorem localPrimitiveM_ge_floor (B : ℕ) : 4096 ≤ localPrimitiveM B := by
  unfold localPrimitiveM
  exact le_trans (Nat.le_max_right _ _)
    (le_trans (Nat.le_max_right _ _) (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)))

/-- The finite maximum is positive because its fixed floor is positive. -/
theorem localPrimitiveM_pos (B : ℕ) : 0 < localPrimitiveM B :=
  lt_of_lt_of_le (by norm_num) (localPrimitiveM_ge_floor B)

/-- The coefficient is at least one at every positive requested order. -/
theorem one_le_localPrimitiveCoefficient (B : ℕ) :
    1 ≤ localPrimitiveCoefficient B := by
  unfold localPrimitiveCoefficient
  apply Nat.one_le_pow
  have hM := localPrimitiveM_pos B
  omega

end WordCertDensity.LocalPrimitive
