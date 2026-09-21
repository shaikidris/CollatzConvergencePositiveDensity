/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Roots.Periods
public import WordCertDensity.Reference.Residues
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Ring

/-! # Exact binary cycles on every positive ternary level -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- The exact return times of four come from the proved ternary valuation of roots. -/
theorem four_pow_eq_one_iff (q n : ℕ) :
    (4 : ZMod (3 ^ (q + 1))) ^ n = 1 ↔ 3 ^ q ∣ n := by
  have hc := congrArg (fun k : ℕ => (k : ZMod (3 ^ (q + 1))))
    (Roots.three_mul_value_add_one n)
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hc
  have he (a : ZMod (3 ^ (q + 1))) : a + 1 = 1 ↔ a = 0 := by
    constructor
    · intro h
      exact add_right_cancel (show a + 1 = 0 + 1 by simpa only [zero_add] using h)
    · rintro rfl
      simp
  rw [← hc, Nat.cast_add, Nat.cast_one, he, ZMod.natCast_eq_zero_iff, pow_succ, mul_comm (3 ^ q) 3,
    Nat.mul_dvd_mul_iff_left (by decide : 0 < 3), Roots.three_pow_dvd_value_iff]

/-- Four has exactly the full one-coset period. -/
theorem orderOf_four (q : ℕ) : orderOf (4 : ZMod (3 ^ (q + 1))) = 3 ^ q := by
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one]
    exact (four_pow_eq_one_iff q _).mpr dvd_rfl
  · exact (four_pow_eq_one_iff q _).mp (pow_orderOf_eq_one _)

/-- Binary parity is detected by the order-two unit modulo three. -/
theorem orderOf_two_mod_three : orderOf (2 : ZMod (3 ^ 1)) = 2 := by
  apply (orderOf_eq_iff (by decide : 0 < 2)).mpr
  constructor
  · decide
  · intro n hn hn0
    have he : n = 1 := by omega
    subst n
    decide

/-- The binary return times are exactly multiples of twice the ternary coset period. -/
theorem two_pow_eq_one_iff (q n : ℕ) :
    (2 : ZMod (3 ^ (q + 1))) ^ n = 1 ↔ 2 * 3 ^ q ∣ n := by
  constructor
  · intro h
    have hp := congrArg (Reference.project (show 1 ≤ q + 1 by omega)) h
    have h3 : (2 : ZMod (3 ^ 1)) ^ n = 1 := by
      simpa only [map_pow, map_ofNat, map_one] using hp
    have he : 2 ∣ n := by
      rw [← orderOf_two_mod_three]
      exact orderOf_dvd_iff_pow_eq_one.mpr h3
    obtain ⟨k, rfl⟩ := he
    rw [pow_mul, show (2 : ZMod (3 ^ (q + 1))) ^ 2 = 4 by ring] at h
    exact Nat.mul_dvd_mul_left 2 ((four_pow_eq_one_iff q k).mp h)
  · rintro ⟨k, rfl⟩
    rw [mul_assoc, pow_mul, show (2 : ZMod (3 ^ (q + 1))) ^ 2 = 4 by ring]
    exact (four_pow_eq_one_iff q _).mpr (dvd_mul_right _ _)

/-- The exact binary order equals the number of units at the positive ternary level. -/
theorem orderOf_two (q : ℕ) : orderOf (2 : ZMod (3 ^ (q + 1))) = 2 * 3 ^ q := by
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one]
    exact (two_pow_eq_one_iff q _).mpr dvd_rfl
  · exact (two_pow_eq_one_iff q _).mp (pow_orderOf_eq_one _)

/-- One complete binary period as actual ternary units. -/
noncomputable def unitCycle (q : ℕ) (i : Fin (2 * 3 ^ q)) : (ZMod (3 ^ (q + 1)))ˣ :=
  Reference.twoUnit (q + 1) ^ (i : ℕ)

/-- The entries are literally the residue powers used by the cyclic certificate algorithm. -/
theorem unitCycle_val (q : ℕ) (i : Fin (2 * 3 ^ q)) :
    (unitCycle q i : ZMod (3 ^ (q + 1))) = 2 ^ (i : ℕ) := by
  simp only [unitCycle, Units.val_pow_eq_pow_val, Reference.twoUnit_val]

/-- No two positions in the complete period give the same unit. -/
theorem unitCycle_injective (q : ℕ) : Function.Injective (unitCycle q) := by
  intro i j h
  have hv := congrArg (fun u : (ZMod (3 ^ (q + 1)))ˣ => (u : ZMod (3 ^ (q + 1)))) h
  simp only [unitCycle_val] at hv
  apply Fin.ext
  exact pow_injOn_Iio_orderOf
    (by simpa only [Set.mem_Iio, orderOf_two] using i.isLt)
    (by simpa only [Set.mem_Iio, orderOf_two] using j.isLt) hv

/-- Every unit occurs in the one complete period, with no numerical coverage assumption. -/
theorem unitCycle_bijective (q : ℕ) : Function.Bijective (unitCycle q) := by
  apply (Fintype.bijective_iff_injective_and_card (unitCycle q)).mpr
  refine ⟨unitCycle_injective q, ?_⟩
  rw [Fintype.card_fin, ZMod.card_units_eq_totient,
    Nat.totient_prime_pow_succ (by decide : Nat.Prime 3)]
  omega

end WordCertDensity.Certificates
