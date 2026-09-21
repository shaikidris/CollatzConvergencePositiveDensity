/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Roots.Basic
import Mathlib.Tactic.Linarith

/-!
# Complete odd predecessor fibers

The constructor is the manuscript's literal natural quotient. Odd unit targets
have positive odd predecessors indexed without repetition. Exact valuations
come from the existing odd-quotient bridge. Specified ordinary paths may be
returns, so their lengths are not claimed to be first hitting times.
-/

@[expose] public section

namespace WordCertDensity.Roots

/-- The required exponent parity for a target which is a unit modulo three. -/
def inverseParity (y : ℕ) : ℕ := if y % 3 = 1 then 2 else 1

/-- Positive exponents in the admissible parity class. -/
def inverseExponent (y t : ℕ) : ℕ := 2 * t + inverseParity y

/-- Literal one-step inverse constructor; physical claims require a unit target. -/
def inverseRoot (y t : ℕ) : ℕ := (2 ^ inverseExponent y t * y - 1) / 3

/-- The parity selector always gives one or two, including outside its unit domain. -/
theorem inverseParity_bounds (y : ℕ) : 1 ≤ inverseParity y ∧ inverseParity y ≤ 2 := by
  unfold inverseParity
  split_ifs <;> omega

/-- Every indexed exponent is positive. -/
theorem inverseExponent_pos (y t : ℕ) : 0 < inverseExponent y t := by
  have h := inverseParity_bounds y
  unfold inverseExponent
  omega

private theorem two_pow_mod_three (k : ℕ) :
    2 ^ k % 3 = if k % 2 = 0 then 1 else 2 := by
  have hfour (n : ℕ) : 4 ^ n % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have he : k = 2 * (k / 2) + k % 2 := by omega
  have hp : 2 ^ k % 3 = 2 ^ (k % 2) % 3 := by
    calc
      _ = (2 ^ (2 * (k / 2) + k % 2)) % 3 := by rw [← he]
      _ = (4 ^ (k / 2) * 2 ^ (k % 2)) % 3 := by rw [pow_add, pow_mul]; norm_num
      _ = _ := by rw [Nat.mul_mod, hfour]; simp
  rw [hp]
  have hr : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hr with hr | hr <;> simp [hr]

/-- Admissible exponents make the odd-step numerator congruent to one modulo three. -/
theorem inverseNumerator_mod_three {y : ℕ} (hy : ¬ 3 ∣ y) (t : ℕ) :
    (2 ^ inverseExponent y t * y) % 3 = 1 := by
  have hy0 : y % 3 ≠ 0 := fun h => hy (Nat.dvd_of_mod_eq_zero h)
  have hyr : y % 3 < 3 := Nat.mod_lt _ (by decide)
  rw [Nat.mul_mod, two_pow_mod_three]
  by_cases hy1 : y % 3 = 1
  · simp [inverseExponent, inverseParity, hy1]
  · have hy2 : y % 3 = 2 := by omega
    simp [inverseExponent, inverseParity, hy2, Nat.add_mod]

/-- The natural quotient reconstructs the exact numerator, with no truncation loss. -/
theorem inverseRoot_identity {y : ℕ} (hy : ¬ 3 ∣ y) (t : ℕ) :
    3 * inverseRoot y t + 1 = 2 ^ inverseExponent y t * y := by
  have h := inverseNumerator_mod_three hy t
  unfold inverseRoot
  omega

/-- Every constructed root of a unit target is odd. -/
theorem inverseRoot_odd {y : ℕ} (hy : ¬ 3 ∣ y) (t : ℕ) : Odd (inverseRoot y t) := by
  have he := inverseRoot_identity hy t
  have hk := inverseExponent_pos y t
  have hp : (2 ^ inverseExponent y t * y) % 2 = 0 := by
    obtain ⟨k, hk'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : inverseExponent y t ≠ 0)
    rw [hk', pow_succ]
    simp [Nat.mul_mod]
  apply Nat.odd_iff.mpr
  omega

/-- Odd natural constructed roots are positive, including index zero. -/
theorem inverseRoot_pos {y : ℕ} (hy : ¬ 3 ∣ y) (t : ℕ) : 0 < inverseRoot y t := by
  have h := Nat.odd_iff.mp (inverseRoot_odd hy t)
  omega

/-- The target's oddness certifies the exact valuation of each constructed root. -/
theorem inverseRoot_acceleratedExponent {y : ℕ} (hy : ¬ 3 ∣ y) (hodd : Odd y) (t : ℕ) :
    acceleratedExponent (inverseRoot y t) = inverseExponent y t :=
  acceleratedExponent_eq_of_odd_quotient hodd (inverseRoot_identity hy t)

/-- Every constructed root has the prescribed actual next odd value. -/
theorem inverseRoot_acceleratedStep {y : ℕ} (hy : ¬ 3 ∣ y) (hodd : Odd y) (t : ℕ) :
    acceleratedStep (inverseRoot y t) = y :=
  acceleratedStep_eq_of_odd_quotient hodd (inverseRoot_identity hy t)

/-- Consecutive indices obey the same exact affine recurrence for every unit target. -/
theorem inverseRoot_succ {y : ℕ} (hy : ¬ 3 ∣ y) (t : ℕ) :
    inverseRoot y (t + 1) = 4 * inverseRoot y t + 1 := by
  have h := inverseRoot_identity hy t
  have hn := inverseRoot_identity hy (t + 1)
  have hk : inverseExponent y (t + 1) = inverseExponent y t + 2 := by
    unfold inverseExponent
    omega
  rw [hk, pow_add] at hn
  norm_num at hn
  nlinarith

/-- The indexed constructor is strictly increasing, hence has no repetitions. -/
theorem inverseRoot_strictMono {y : ℕ} (hy : ¬ 3 ∣ y) : StrictMono (inverseRoot y) := by
  apply strictMono_nat_of_lt_succ
  intro t
  rw [inverseRoot_succ hy]
  omega

/-- Unit-target root indices are uniquely recoverable from their values. -/
theorem inverseRoot_injective {y : ℕ} (hy : ¬ 3 ∣ y) : Function.Injective (inverseRoot y) :=
  (inverseRoot_strictMono hy).injective

/-- Integrality determines exactly the indexed positive exponent class. -/
theorem inverseExponent_iff {y k : ℕ} (hy : ¬ 3 ∣ y) (hk : 0 < k) :
    (2 ^ k * y) % 3 = 1 ↔ ∃ t : ℕ, k = inverseExponent y t := by
  constructor
  · intro h
    have hy0 : y % 3 ≠ 0 := fun h => hy (Nat.dvd_of_mod_eq_zero h)
    have hyr : y % 3 < 3 := Nat.mod_lt _ (by decide)
    rw [Nat.mul_mod, two_pow_mod_three] at h
    by_cases hy1 : y % 3 = 1
    · have hp : k % 2 = 0 := by
        by_contra hn
        simp [hn, hy1] at h
      refine ⟨k / 2 - 1, ?_⟩
      simp only [inverseExponent, inverseParity, if_pos hy1]
      omega
    · have hy2 : y % 3 = 2 := by omega
      have hp : k % 2 = 1 := by
        by_cases hn : k % 2 = 0
        · simp [hn, hy2] at h
        · omega
      refine ⟨k / 2, ?_⟩
      simp only [inverseExponent, inverseParity, if_neg hy1]
      omega
  · rintro ⟨t, rfl⟩
    exact inverseNumerator_mod_three hy t

/-- An actual next odd value is never divisible by three, even for the totalized map. -/
theorem not_three_dvd_acceleratedStep (x : ℕ) : ¬ 3 ∣ acceleratedStep x := by
  intro h
  have hd := dvd_mul_of_dvd_right h (2 ^ acceleratedExponent x)
  rw [pow_acceleratedExponent_mul] at hd
  obtain ⟨a, ha⟩ := hd
  omega

/-- The constructor exhausts the actual positive odd predecessor fiber uniquely. -/
theorem inverseRoot_fiber_iff {y x : ℕ} (hy : ¬ 3 ∣ y) (hodd : Odd y) :
    (0 < x ∧ Odd x ∧ acceleratedStep x = y) ↔ ∃! t : ℕ, inverseRoot y t = x := by
  constructor
  · rintro ⟨_, hx, hxy⟩
    have hi := pow_acceleratedExponent_mul x
    rw [hxy] at hi
    have hm : (2 ^ acceleratedExponent x * y) % 3 = 1 := by rw [hi]; omega
    obtain ⟨t, ht⟩ := (inverseExponent_iff hy (acceleratedExponent_pos_of_odd hx)).mp hm
    have he : inverseRoot y t = x := by
      have hr := inverseRoot_identity hy t
      rw [ht] at hi
      omega
    refine ⟨t, he, ?_⟩
    intro s hs
    exact inverseRoot_injective hy (hs.trans he.symm)
  · rintro ⟨t, rfl, _⟩
    exact ⟨inverseRoot_pos hy t, inverseRoot_odd hy t, inverseRoot_acceleratedStep hy hodd t⟩

/-- A target divisible by three has no positive odd accelerated predecessors. -/
theorem no_odd_predecessor_of_three_dvd {y : ℕ} (hy : 3 ∣ y) :
    ¬ ∃ x : ℕ, 0 < x ∧ Odd x ∧ acceleratedStep x = y := by
  rintro ⟨x, _, _, hxy⟩
  exact not_three_dvd_acceleratedStep x (hxy.symm ▸ hy)

/-- The constructor is the literal affine image of the existing root recurrence R_t. -/
theorem inverseRoot_affine {y : ℕ} (hy : ¬ 3 ∣ y) (t : ℕ) :
    inverseRoot y t = 2 ^ inverseParity y * y * value t + inverseRoot y 0 := by
  induction t with
  | zero => simp [value_zero]
  | succ t ih =>
      rw [inverseRoot_succ hy, value_succ, ih]
      have h := inverseRoot_identity hy 0
      simp only [inverseExponent, Nat.mul_zero, Nat.zero_add] at h
      nlinarith

/-- The ordinary block has the exact specified length, which may be a return time. -/
theorem inverseRoot_reaches {y : ℕ} (hy : ¬ 3 ∣ y) (hodd : Odd y) (t : ℕ) :
    ReachesIn (inverseRoot y t) y (inverseExponent y t + 1) := by
  have h := reachesIn_acceleratedStep_of_odd (inverseRoot_odd hy t)
  rw [inverseRoot_acceleratedStep hy hodd, inverseRoot_acceleratedExponent hy hodd] at h
  exact h

/-- The prescribed incoming segment reaches a dyadic target with the stated halving guard. -/
theorem inverseRoot_reaches_dyadic {y : ℕ} (hy : ¬ 3 ∣ y) (t v : ℕ)
    (hv : v + 1 ≤ inverseExponent y t) :
    ReachesIn (inverseRoot y t) (2 ^ v * y) (1 + inverseExponent y t - v) := by
  have he : 1 + inverseExponent y t - v = (inverseExponent y t - v) + 1 := by omega
  have hp : 2 ^ inverseExponent y t * y =
      2 ^ (inverseExponent y t - v) * (2 ^ v * y) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega)]
  unfold ReachesIn
  rw [he, Function.iterate_succ_apply, ordinaryStep_of_odd (inverseRoot_odd hy t),
    inverseRoot_identity hy t, hp]
  exact ordinaryStep_iterate_pow_two_mul _ _

end WordCertDensity.Roots
