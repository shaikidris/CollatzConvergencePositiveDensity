/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The root recurrence, numerator identity and positive-index oddness proofs are
adapted from Lech Mazur, Copyright 2026 Lech Mazur, under Apache License 2.0.
The source LICENSE and NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
Modifications use local root/dynamics interfaces and add first-hit minimality.
-/
module

public import WordCertDensity.Dynamics.Accelerated
import Mathlib.Tactic.NormNum

/-!
# The convergent root family

The recurrence includes `R₀ = 0` for algebraic convenience. Physical roots
have positive indices. The first root is one itself, whose first hit is zero;
all later roots have first ordinary hitting time `2 * s + 1`.
-/

@[expose] public section

namespace WordCertDensity

namespace Roots

/-- The roots `(4^s - 1) / 3`, encoded by their integer recurrence. -/
def value : ℕ → ℕ
  | 0 => 0
  | s + 1 => 4 * value s + 1

/-- The zero-index extension is not a physical positive root. -/
@[simp] theorem value_zero : value 0 = 0 := rfl

/-- Exact integral root recurrence. -/
@[simp] theorem value_succ (s : ℕ) : value (s + 1) = 4 * value s + 1 := rfl

/-- The first root is one itself. -/
theorem value_one : value 1 = 1 := rfl

/-- Each root's odd-step numerator is exactly a power of four. -/
theorem three_mul_value_add_one (s : ℕ) : 3 * value s + 1 = 4 ^ s := by
  induction s with
  | zero => norm_num [value]
  | succ s ih =>
      rw [value_succ, pow_succ]
      omega

/-- The recurrence agrees with the manuscript's displayed quotient. -/
theorem value_eq_quotient (s : ℕ) : value s = (4 ^ s - 1) / 3 := by
  rw [← three_mul_value_add_one]
  simp

/-- Roots at positive indices are odd. -/
theorem value_odd {s : ℕ} (hs : 0 < s) : Odd (value s) := by
  cases s with
  | zero => omega
  | succ s =>
      refine ⟨2 * value s, ?_⟩
      rw [value_succ]
      omega

/-- Roots at positive indices are positive. -/
theorem value_pos {s : ℕ} (hs : 0 < s) : 0 < value s := by
  cases s with
  | zero => omega
  | succ s => rw [value_succ]; omega

/-- Distinct indices give strictly ordered roots. -/
theorem value_strictMono : StrictMono value := by
  apply strictMono_nat_of_lt_succ
  intro s
  rw [value_succ]
  omega

/-- Root indices are uniquely determined by the root value. -/
theorem value_injective : Function.Injective value := value_strictMono.injective

/-- All roots after the first are strictly larger than one. -/
theorem one_lt_value {s : ℕ} (hs : 1 < s) : 1 < value s := by
  simpa using value_strictMono hs

/-- The root numerator has the exact binary exponent `2*s`. -/
theorem three_mul_value_add_one_eq_two_pow (s : ℕ) :
    3 * value s + 1 = 2 ^ (2 * s) := by
  rw [three_mul_value_add_one, show (4 : ℕ) = 2 ^ 2 by decide, pow_mul]

/-- Exact accelerated exponent, including the totalized zero-index identity. -/
theorem acceleratedExponent_value (s : ℕ) : acceleratedExponent (value s) = 2 * s :=
  acceleratedExponent_eq_of_odd_quotient (root := 1) (by decide)
    (by simpa using three_mul_value_add_one_eq_two_pow s)

/-- The totalized accelerated map sends each root value to one. -/
theorem acceleratedStep_value (s : ℕ) : acceleratedStep (value s) = 1 :=
  acceleratedStep_eq_of_odd_quotient (k := 2 * s) (by decide)
    (by simpa using three_mul_value_add_one_eq_two_pow s)

/-- After the odd step, every partial root orbit is an explicit power of two. -/
theorem ordinary_iterate_after_first {s : ℕ} (hs : 0 < s) (j : ℕ) (hj : j ≤ 2 * s) :
    (ordinaryStep^[j + 1]) (value s) = 2 ^ (2 * s - j) := by
  rw [Function.iterate_succ_apply, ordinaryStep_of_odd (value_odd hs),
    three_mul_value_add_one_eq_two_pow]
  exact ordinaryStep_iterate_pow_two_prefix (2 * s) j hj

/-- Every positive root arrives at one after the stated ordinary block. -/
theorem reachesIn_one {s : ℕ} (hs : 0 < s) : ReachesIn (value s) 1 (2 * s + 1) := by
  simpa [ReachesIn] using ordinary_iterate_after_first hs (2 * s) le_rfl

/-- For roots strictly after the first, the ordinary block is the first hit of one. -/
theorem first_hit_one {s : ℕ} (hs : 1 < s) :
    ReachesIn (value s) 1 (2 * s + 1) ∧
      ∀ j < 2 * s + 1, ¬ ReachesIn (value s) 1 j := by
  refine ⟨reachesIn_one (by omega), ?_⟩
  intro j hj hhit
  cases j with
  | zero =>
      have hlarge := one_lt_value hs
      change value s = 1 at hhit
      omega
  | succ j =>
      have hpartial := ordinary_iterate_after_first (by omega : 0 < s) j (by omega)
      have hpower : 1 < 2 ^ (2 * s - j) :=
        Nat.one_lt_pow (by omega : 2 * s - j ≠ 0) (by decide)
      unfold ReachesIn at hhit
      rw [hpartial] at hhit
      omega

/-- The first root has first hitting time zero, not the length of its return cycle. -/
theorem first_root_hit_zero :
    ReachesIn (value 1) 1 0 ∧ ∀ j < 0, ¬ ReachesIn (value 1) 1 j := by
  exact ⟨rfl, fun _ h => (Nat.not_lt_zero _ h).elim⟩

/-- The exact real-budget criterion for roots beyond the first. -/
theorem reachesWithin_one_iff {s : ℕ} (hs : 1 < s) (budget : ℝ) :
    ReachesWithin (value s) 1 budget ↔ ((2 * s + 1 : ℕ) : ℝ) ≤ budget := by
  obtain ⟨harrive, hminimal⟩ := first_hit_one hs
  constructor
  · rintro ⟨j, hj, hbudget⟩
    have hle : 2 * s + 1 ≤ j := by
      by_contra hlt
      exact hminimal j (Nat.lt_of_not_ge hlt) hj
    exact (Nat.cast_le.mpr hle).trans hbudget
  · intro hb
    exact ⟨2 * s + 1, harrive, hb⟩

end Roots

end WordCertDensity
