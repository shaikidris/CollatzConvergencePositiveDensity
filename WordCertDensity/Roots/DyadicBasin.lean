/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Dynamics.Ordinary

/-!
# Exact predecessor basin of a target divisible by three

Every step backwards from such a target is a doubling. This describes each
exact-time fiber and the entire positive finite-hitting basin. Counting and
density limits are subsequent consumers of this identity.
-/

@[expose] public section

namespace WordCertDensity

/-- Positive sources with a finite ordinary hitting witness to the target. -/
def ordinaryBasin (y : ℕ) : Set ℕ := {x | 0 < x ∧ ∃ n, ReachesIn x y n}

/-- A target divisible by three has exactly one ordinary predecessor: its double. -/
theorem ordinaryStep_eq_iff_of_three_dvd {x y : ℕ} (hy : 3 ∣ y) :
    ordinaryStep x = y ↔ x = 2 * y := by
  constructor
  · intro h
    by_cases heven : Even x
    · rw [ordinaryStep_of_even heven] at h
      obtain ⟨k, hk⟩ := heven
      omega
    · have hodd : 3 * x + 1 = y := by simpa [ordinaryStep, heven] using h
      obtain ⟨k, hk⟩ := hy
      omega
  · intro h
    rw [h, ordinaryStep_of_even (show Even (2 * y) from ⟨y, by omega⟩)]
    omega

/-- The exact n-step predecessor fiber of a multiple of three is a single dyadic predecessor. -/
theorem reachesIn_iff_of_three_dvd {y : ℕ} (hy : 3 ∣ y) (n x : ℕ) :
    ReachesIn x y n ↔ x = 2 ^ n * y := by
  induction n generalizing x with
  | zero => simp [ReachesIn]
  | succ n ih =>
    have hstep : ReachesIn x y (n + 1) ↔ ReachesIn (ordinaryStep x) y n := by
      simp [ReachesIn, Function.iterate_succ_apply]
    rw [hstep, ih, ordinaryStep_eq_iff_of_three_dvd (dvd_mul_of_dvd_right hy (2 ^ n))]
    simp [pow_succ, mul_comm, mul_left_comm]

/-- At a positive target divisible by three, the dyadic path is the first hit. -/
theorem first_hit_dyadic_of_three_dvd {y : ℕ} (hy : 3 ∣ y) (hpos : 0 < y) (n : ℕ) :
    ReachesIn (2 ^ n * y) y n ∧ ∀ j < n, ¬ ReachesIn (2 ^ n * y) y j := by
  refine ⟨ordinaryStep_iterate_pow_two_mul n y, ?_⟩
  intro j hj h
  have heq := (reachesIn_iff_of_three_dvd hy j _).mp h
  have hlt : 2 ^ j * y < 2 ^ n * y :=
    Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_right (by decide) hj) hpos
  exact (ne_of_lt hlt) heq.symm

/-- The full finite-hitting basin of a positive multiple of three consists exactly of its doublings. -/
theorem ordinaryBasin_eq_dyadic_range {y : ℕ} (hy : 3 ∣ y) (hpos : 0 < y) :
    ordinaryBasin y = Set.range (fun n : ℕ => 2 ^ n * y) := by
  ext x
  constructor
  · rintro ⟨_, n, hn⟩
    exact ⟨n, ((reachesIn_iff_of_three_dvd hy n x).mp hn).symm⟩
  · rintro ⟨n, rfl⟩
    exact ⟨Nat.mul_pos (pow_pos (by decide) n) hpos, n, ordinaryStep_iterate_pow_two_mul n y⟩

/-- A logarithmic-clock good set lies in the full finite-hitting basin. -/
theorem goodTarget_subset_ordinaryBasin (y : ℕ) (c : ℝ) : goodTarget y c ⊆ ordinaryBasin y := by
  rintro x ⟨hx, n, hn, _⟩
  exact ⟨hx, n, hn⟩

end WordCertDensity
