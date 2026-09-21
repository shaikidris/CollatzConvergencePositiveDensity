/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

Character conductor transport adapted from Lech Mazur, Copyright 2026 Lech Mazur,
under Apache License 2.0. The source LICENSE and NOTICE are retained at
research/sources/mazur_830b9d3f38f2/. Finite PMF sums and the positive Fourier
convention use the local reference law and pinned Mathlib APIs.
-/
module

public import WordCertDensity.Reference.Fourier
public import WordCertDensity.Reference.Projectivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-!
# Exact conductor transport of the reference Fourier sum

The finite PMF map identity keeps the original probability mass. Extracting
a ternary power from a frequency transports the standard positive character
to the lower group, and exact reference projectivity transports the Fourier sum.
-/

@[expose] public section

namespace WordCertDensity
namespace FiniteFourier

/-- A finite PMF pushforward preserves complex weighted sums exactly. -/
theorem sum_pmf_map_mul {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : α → β) (g : β → ℂ) :
    (∑ y, (((p.map f) y).toReal : ℂ) * g y) =
      ∑ x, ((p x).toReal : ℂ) * g (f x) := by
  classical
  have hmass (y : β) : ((p.map f) y).toReal =
      ∑ x, if y = f x then (p x).toReal else 0 := by
    rw [PMF.map_apply, tsum_fintype,
      ENNReal.toReal_sum (fun x _ => by split_ifs <;> simp [PMF.apply_ne_top])]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> simp
  simp only [hmass, Complex.ofReal_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp only [apply_ite Complex.ofReal, Complex.ofReal_zero, ite_mul, zero_mul]
  simp

private theorem character_three_pow_mul_natCast (r j x η : ℕ) :
    ZMod.stdAddChar ((x : ZMod (3 ^ (r + j))) *
        ((3 : ZMod (3 ^ (r + j))) ^ j * (η : ZMod (3 ^ (r + j))))) =
      ZMod.stdAddChar ((x : ZMod (3 ^ r)) * (η : ZMod (3 ^ r))) := by
  have hh : (x : ZMod (3 ^ (r + j))) * ((3 : ZMod (3 ^ (r + j))) ^ j * (η : ZMod (3 ^ (r + j)))) =
      ((x * (3 ^ j * η) : ℕ) : ZMod (3 ^ (r + j))) := by push_cast; rfl
  have hl : (x : ZMod (3 ^ r)) * (η : ZMod (3 ^ r)) =
      ((x * η : ℕ) : ZMod (3 ^ r)) := by push_cast; rfl
  rw [hh, hl]
  rw [show ((x * (3 ^ j * η) : ℕ) : ZMod (3 ^ (r + j))) =
    (((x * (3 ^ j * η) : ℕ) : ℤ) : ZMod (3 ^ (r + j))) by simp]
  rw [show ((x * η : ℕ) : ZMod (3 ^ r)) =
    (((x * η : ℕ) : ℤ) : ZMod (3 ^ r)) by simp]
  rw [ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  push_cast
  rw [pow_add]
  field_simp

/-- Extracting a ternary frequency power is exact positive-character projection. -/
theorem character_three_pow_mul (r j : ℕ) (x η : ZMod (3 ^ (r + j))) :
    ZMod.stdAddChar (x * ((3 : ZMod (3 ^ (r + j))) ^ j * η)) =
      ZMod.stdAddChar (Reference.project (Nat.le_add_right r j) x *
        Reference.project (Nat.le_add_right r j) η) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val η]
  conv_rhs => rw [← ZMod.natCast_zmod_val x, ← ZMod.natCast_zmod_val η]
  simp only [Reference.project_natCast]
  exact character_three_pow_mul_natCast r j x.val η.val

/-- The actual reference Fourier sum descends to the exact conductor level. -/
theorem fourierMass_three_pow_mul (r j : ℕ) (η : ZMod (3 ^ (r + j))) :
    Reference.fourierMass (r + j) ((3 : ZMod (3 ^ (r + j))) ^ j * η) =
      Reference.fourierMass r (Reference.project (Nat.le_add_right r j) η) := by
  rw [Reference.fourierMass]
  simp only [Reference.mass]
  simp_rw [mul_comm ((3 : ZMod (3 ^ (r + j))) ^ j * η), character_three_pow_mul]
  rw [← sum_pmf_map_mul (Reference.law (r + j))
    (Reference.project (Nat.le_add_right r j))
    (fun y => ZMod.stdAddChar (y * Reference.project (Nat.le_add_right r j) η))]
  rw [Reference.law_map_project]
  simp only [Reference.fourierMass, Reference.mass, mul_comm]

end FiniteFourier
end WordCertDensity
