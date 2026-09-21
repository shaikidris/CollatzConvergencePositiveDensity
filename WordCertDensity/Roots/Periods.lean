/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Roots.Predecessors
public import Mathlib.NumberTheory.Multiplicity
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# Exact ternary periods of inverse roots

The canonical root sequence preserves ternary congruences in both directions.
An invertible affine change gives the same complete periods for every target
which is a unit modulo three. Index zero and the one-point modulus are retained.
-/

@[expose] public section

namespace WordCertDensity.Roots

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- Adding indices separates the initial root from a scaled continuation root. -/
theorem value_add (s t : ℕ) : value (s + t) = value s + 4 ^ s * value t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.add_succ, value_succ, ih, value_succ]
    have h := three_mul_value_add_one s
    nlinarith

/-- The root and its index have exactly the same ternary valuation, including zero. -/
theorem value_padicValNat (n : ℕ) : padicValNat 3 (value n) = padicValNat 3 n := by
  by_cases hn : n = 0
  · subst n
    rfl
  have hv : value n ≠ 0 := ne_of_gt (value_pos (Nat.pos_of_ne_zero hn))
  have h := padicValNat.pow_sub_pow (p := 3) (x := 4) (y := 1)
    (by decide) (by decide) (by decide) (by decide) hn
  have hid : 4 ^ n - 1 = 3 * value n := by
    have hi := three_mul_value_add_one n
    omega
  simp only [one_pow, hid] at h
  rw [padicValNat.mul (by decide) hv] at h
  norm_num at h
  omega

/-- A ternary prime power divides a canonical root exactly when it divides the index. -/
theorem three_pow_dvd_value_iff (q n : ℕ) : 3 ^ q ∣ value n ↔ 3 ^ q ∣ n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [padicValNat_dvd_iff_le (ne_of_gt (value_pos (Nat.pos_of_ne_zero hn))),
    value_padicValNat, padicValNat_dvd_iff_le hn]

/-- Canonical roots and indices have the same residue modulo three. -/
theorem value_mod_three (n : ℕ) : value n % 3 = n % 3 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [value_succ, Nat.add_mod, Nat.mul_mod, ih]

/-- Canonical roots preserve and reflect every ternary congruence. -/
theorem value_modEq_iff (q s t : ℕ) :
    Nat.ModEq (3 ^ q) (value s) (value t) ↔ Nat.ModEq (3 ^ q) s t := by
  have ordered (a b : ℕ) (hab : a ≤ b) :
      Nat.ModEq (3 ^ q) (value a) (value b) ↔ Nat.ModEq (3 ^ q) a b := by
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hab
    rw [value_add, Nat.left_modEq_add_iff, Nat.left_modEq_add_iff]
    have hc : Nat.Coprime (3 ^ q) (4 ^ a) := (show Nat.Coprime 3 4 by decide).pow _ _
    rw [hc.dvd_mul_left, three_pow_dvd_value_iff]
  rcases le_total s t with h | h
  · exact ordered s t h
  · exact ⟨fun hst => ((ordered t s h).mp hst.symm).symm,
      fun hst => ((ordered t s h).mpr hst.symm).symm⟩

/-- Every unit-target constructor preserves and reflects ternary index congruences. -/
theorem inverseRoot_modEq_iff {y : ℕ} (hy : ¬ 3 ∣ y) (q s t : ℕ) :
    Nat.ModEq (3 ^ q) (inverseRoot y s) (inverseRoot y t) ↔ Nat.ModEq (3 ^ q) s t := by
  rw [inverseRoot_affine hy s, inverseRoot_affine hy t,
    Nat.ModEq.add_iff_right (Nat.ModEq.refl (inverseRoot y 0))]
  have hc : Nat.Coprime (3 ^ q) (2 ^ inverseParity y * y) :=
    (((show Nat.Coprime 3 2 by decide).pow_right _).mul_right
      (Nat.prime_three.coprime_iff_not_dvd.mpr hy)).pow_left _
  constructor
  · intro h
    exact (value_modEq_iff q s t).mp (h.cancel_left_of_coprime hc)
  · intro h
    exact ((value_modEq_iff q s t).mpr h).mul_left _

/-- Residues of one complete consecutive canonical-root block. -/
def rootResidue (q start : ℕ) (i : Fin (3 ^ q)) : Fin (3 ^ q) :=
  ⟨value (start + i.val) % 3 ^ q, Nat.mod_lt _ (pow_pos (by decide) _)⟩

/-- No two indices in a complete canonical block share a residue. -/
theorem rootResidue_injective (q start : ℕ) : Function.Injective (rootResidue q start) := by
  intro i j h
  have hm : Nat.ModEq (3 ^ q) (value (start + i.val)) (value (start + j.val)) :=
    congrArg Fin.val h
  have hi := (value_modEq_iff q _ _).mp hm
  have hij := (Nat.ModEq.refl start).add_left_cancel hi
  exact Fin.ext (hij.eq_of_lt_of_lt i.isLt j.isLt)

/-- Every consecutive canonical-root block realizes each residue exactly once. -/
theorem rootResidue_bijective (q start : ℕ) : Function.Bijective (rootResidue q start) :=
  ⟨rootResidue_injective q start, Finite.surjective_of_injective (rootResidue_injective q start)⟩

/-- Residues of one complete consecutive block of the unit-target constructor. -/
def inverseResidue (y q start : ℕ) (i : Fin (3 ^ q)) : Fin (3 ^ q) :=
  ⟨inverseRoot y (start + i.val) % 3 ^ q, Nat.mod_lt _ (pow_pos (by decide) _)⟩

/-- No two constructor indices in one full block share a residue. -/
theorem inverseResidue_injective {y : ℕ} (hy : ¬ 3 ∣ y) (q start : ℕ) :
    Function.Injective (inverseResidue y q start) := by
  intro i j h
  have hm : Nat.ModEq (3 ^ q) (inverseRoot y (start + i.val))
      (inverseRoot y (start + j.val)) := congrArg Fin.val h
  have hi := (inverseRoot_modEq_iff hy q _ _).mp hm
  have hij := (Nat.ModEq.refl start).add_left_cancel hi
  exact Fin.ext (hij.eq_of_lt_of_lt i.isLt j.isLt)

/-- Every full block of a unit-target constructor realizes each residue exactly once. -/
theorem inverseResidue_bijective {y : ℕ} (hy : ¬ 3 ∣ y) (q start : ℕ) :
    Function.Bijective (inverseResidue y q start) :=
  ⟨inverseResidue_injective hy q start,
    Finite.surjective_of_injective (inverseResidue_injective hy q start)⟩

end WordCertDensity.Roots
