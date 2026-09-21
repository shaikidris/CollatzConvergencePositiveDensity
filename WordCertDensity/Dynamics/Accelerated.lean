/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The positivity, oddness, factorization and ordinary-block proofs are adapted
from Lech Mazur, Copyright 2026 Lech Mazur, under the Apache License, Version 2.0.
Modifications use local dynamics interfaces and add the odd-quotient bridge.
The source LICENSE and NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
-/
module

public import WordCertDensity.Dynamics.Ordinary
public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum

/-!
# Actual accelerated Collatz blocks

The exponent is the exact exponent of two in `3 * x + 1`. On odd inputs,
one accelerated step consists of one ordinary odd step and that many halvings.
The map is totalized on naturals; physical histories require positive odd inputs.
-/

@[expose] public section

namespace WordCertDensity

/-- Exact two-adic valuation of the numerator in an accelerated step. -/
def acceleratedExponent (x : ℕ) : ℕ := (3 * x + 1).factorization 2

/-- Divide the odd-step numerator by its full power of two. -/
def acceleratedStep (x : ℕ) : ℕ := (3 * x + 1) / 2 ^ acceleratedExponent x

/-- The chronological valuations along a finite accelerated orbit. -/
def acceleratedValuations (x depth : ℕ) : List ℕ :=
  (List.range depth).map fun j => acceleratedExponent ((acceleratedStep^[j]) x)

/-- Extending a chronological orbit adds its next valuation at the end. -/
theorem acceleratedValuations_succ (x depth : ℕ) :
    acceleratedValuations x (depth + 1) = acceleratedValuations x depth ++
      [acceleratedExponent ((acceleratedStep^[depth]) x)] := by
  simp [acceleratedValuations, List.range_succ]

/-- Removing the first block leaves the chronological valuations of the remaining orbit. -/
theorem acceleratedValuations_cons (x depth : ℕ) :
    acceleratedValuations x (depth + 1) =
      acceleratedExponent x :: acceleratedValuations (acceleratedStep x) depth := by
  induction depth with
  | zero => rfl
  | succ depth ih =>
      rw [acceleratedValuations_succ, ih, acceleratedValuations_succ,
        Function.iterate_succ_apply]
      rfl

/-- Removing the full power of two leaves a positive integer. -/
theorem acceleratedStep_pos (x : ℕ) : 0 < acceleratedStep x := by
  exact Nat.ordCompl_pos 2 (by omega : 3 * x + 1 ≠ 0)

/-- Removing the full power of two leaves an odd integer. -/
theorem acceleratedStep_odd (x : ℕ) : Odd (acceleratedStep x) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  exact Nat.not_dvd_ordCompl Nat.prime_two (by omega : 3 * x + 1 ≠ 0)
    (even_iff_two_dvd.mp heven)

/-- The accelerated quotient reconstructs the exact integer numerator. -/
theorem pow_acceleratedExponent_mul (x : ℕ) :
    2 ^ acceleratedExponent x * acceleratedStep x = 3 * x + 1 := by
  exact Nat.ordProj_mul_ordCompl_eq_self (3 * x + 1) 2

/-- An odd input has at least one ordinary halving after its odd step. -/
theorem acceleratedExponent_pos_of_odd {x : ℕ} (hx : Odd x) :
    0 < acceleratedExponent x := by
  have hdiv : 2 ∣ 3 * x + 1 := by
    obtain ⟨a, ha⟩ := hx
    exact ⟨3 * a + 2, by omega⟩
  exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two (by omega) hdiv

/-- An odd quotient certifies that the recorded power of two is exact. -/
theorem acceleratedExponent_eq_of_odd_quotient {x root k : ℕ}
    (hroot : Odd root) (hidentity : 3 * x + 1 = 2 ^ k * root) :
    acceleratedExponent x = k := by
  have hrootne : root ≠ 0 := by
    intro hzero
    exact Nat.not_odd_zero (hzero ▸ hroot)
  unfold acceleratedExponent
  rw [hidentity, Nat.factorization_mul (by positivity) hrootne]
  simp [Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd hroot.not_two_dvd_nat]

/-- A certified odd quotient is the actual accelerated endpoint. -/
theorem acceleratedStep_eq_of_odd_quotient {x root k : ℕ}
    (hroot : Odd root) (hidentity : 3 * x + 1 = 2 ^ k * root) :
    acceleratedStep x = root := by
  unfold acceleratedStep
  rw [acceleratedExponent_eq_of_odd_quotient hroot hidentity, hidentity]
  exact Nat.mul_div_right root (by positivity : 0 < 2 ^ k)

/-- One accelerated block has exactly its valuation plus one ordinary steps. -/
theorem reachesIn_acceleratedStep_of_odd {x : ℕ} (hx : Odd x) :
    ReachesIn x (acceleratedStep x) (acceleratedExponent x + 1) := by
  unfold ReachesIn
  rw [Function.iterate_add_apply, Function.iterate_one, ordinaryStep_of_odd hx,
    ← pow_acceleratedExponent_mul x]
  exact ordinaryStep_iterate_pow_two_mul (acceleratedExponent x) (acceleratedStep x)

/-- The accelerated map fixes one, although the ordinary map does not. -/
@[simp] theorem acceleratedStep_one : acceleratedStep 1 = 1 :=
  acceleratedStep_eq_of_odd_quotient (k := 2) (by decide) (by decide)

end WordCertDensity
