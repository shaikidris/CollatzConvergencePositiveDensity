/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The binary-unit projection argument is adapted from Lech Mazur,
Copyright 2026 Lech Mazur, under Apache License 2.0. The source LICENSE and
NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
The recursive offsets use the local word algebra and reversed numerator.
-/
module

public import WordCertDensity.Words.Forward
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Dyadic offsets in ternary residue groups

Binary denominators are units modulo every power of three, including the
one-point group at level zero. A recursive residue offset is connected to the
rational inverse offset by their common integral numerator and binary denominator.
No generic rational cast into a ternary residue ring is used.
-/

@[expose] public section

namespace WordCertDensity

namespace Reference

/-- Two as an explicit unit modulo a power of three. -/
noncomputable def twoUnit (q : ℕ) : (ZMod (3 ^ q))ˣ :=
  ZMod.unitOfCoprime 2 ((show Nat.Coprime 2 3 by decide).pow_right q)

/-- The value of the binary unit is the residue two. -/
theorem twoUnit_val (q : ℕ) : (twoUnit q : ZMod (3 ^ q)) = 2 := by
  simp [twoUnit]

/-- The inverse of a binary power, evaluated by its unit. -/
noncomputable def inverseTwoPow (q k : ℕ) : ZMod (3 ^ q) :=
  ↑((twoUnit q)⁻¹ ^ k)

/-- A zero binary exponent evaluates to one. -/
@[simp] theorem inverseTwoPow_zero (q : ℕ) : inverseTwoPow q 0 = 1 := by
  simp [inverseTwoPow]

/-- Binary inverse powers multiply when exponents add. -/
theorem inverseTwoPow_add (q a b : ℕ) :
    inverseTwoPow q (a + b) = inverseTwoPow q a * inverseTwoPow q b := by
  simp [inverseTwoPow, pow_add]

/-- The unit representation agrees with the ring inverse notation. -/
theorem inverseTwoPow_eq_inv (q k : ℕ) :
    inverseTwoPow q k = ((2 : ZMod (3 ^ q)) ^ k)⁻¹ := by
  rw [← twoUnit_val q, ← Units.val_pow_eq_pow_val, ZMod.inv_coe_unit]
  simp [inverseTwoPow, inv_pow]

/-- A binary power cancels its explicitly represented inverse. -/
theorem two_pow_mul_inverseTwoPow (q k : ℕ) :
    (2 : ZMod (3 ^ q)) ^ k * inverseTwoPow q k = 1 := by
  rw [← twoUnit_val q]
  simp [inverseTwoPow, ← mul_pow]

/-- Reduction between ternary levels, including level zero. -/
noncomputable def project {m n : ℕ} (h : m ≤ n) :
    ZMod (3 ^ n) →+* ZMod (3 ^ m) :=
  ZMod.castHom (Nat.pow_dvd_pow 3 h) (ZMod (3 ^ m))

/-- Ternary reduction preserves integer representatives. -/
theorem project_natCast {m n : ℕ} (h : m ≤ n) (a : ℕ) :
    project h (a : ZMod (3 ^ n)) = (a : ZMod (3 ^ m)) := by
  rw [project, ZMod.castHom_apply]
  exact ZMod.cast_natCast (Nat.pow_dvd_pow 3 h) a

/-- Binary inverse units commute with reduction of the ternary modulus. -/
theorem project_inverseTwoPow {m n : ℕ} (h : m ≤ n) (k : ℕ) :
    project h (inverseTwoPow n k) = inverseTwoPow m k := by
  have hu : Units.map (project h) (twoUnit n) = twoUnit m := by
    apply Units.ext
    change project h (twoUnit n : ZMod (3 ^ n)) = (twoUnit m : ZMod (3 ^ m))
    rw [twoUnit_val, twoUnit_val]
    exact map_ofNat (project h) 2
  change ((Units.map (project h) ((twoUnit n)⁻¹ ^ k) : (ZMod (3 ^ m))ˣ) :
    ZMod (3 ^ m)) = ↑((twoUnit m)⁻¹ ^ k)
  rw [map_pow, map_inv, hu]

end Reference

namespace ValuationWord

/-- The inverse-prefix offset evaluated using binary inverse units. -/
noncomputable def residueOffset (q : ℕ) : ValuationWord → ZMod (3 ^ q)
  | [] => 0
  | k :: w => Reference.inverseTwoPow q k * (1 + 3 * residueOffset q w)

/-- An empty inverse word has zero residue offset. -/
@[simp] theorem residueOffset_nil (q : ℕ) : residueOffset q [] = 0 := rfl

/-- All offsets vanish in the one-point group. -/
theorem residueOffset_zero_level (w : ValuationWord) : residueOffset 0 w = 0 := by
  let : Subsingleton (ZMod (3 ^ 0)) := ZMod.subsingleton_iff.mpr (by decide)
  exact Subsingleton.elim _ _

/-- Ordered residue offsets satisfy the same affine composition as rational offsets. -/
theorem residueOffset_append (q : ℕ) (u v : ValuationWord) :
    residueOffset q (u ++ v) = residueOffset q u +
      (3 : ZMod (3 ^ q)) ^ u.length * Reference.inverseTwoPow q u.total *
        residueOffset q v := by
  induction u with
  | nil => simp [residueOffset, total]
  | cons k u ih =>
      simp only [List.cons_append, residueOffset, ih, List.length_cons]
      simp only [total, List.map_cons, List.sum_cons, Reference.inverseTwoPow_add, pow_succ]
      ring

/-- Reducing an inverse offset gives its value at the lower ternary level. -/
theorem project_residueOffset {m n : ℕ} (h : m ≤ n) (w : ValuationWord) :
    Reference.project h (residueOffset n w) = residueOffset m w := by
  induction w with
  | nil => simp [residueOffset]
  | cons k w ih =>
      simp only [residueOffset, map_mul, map_add, map_one,
        Reference.project_inverseTwoPow, ih]
      rw [show Reference.project h (3 : ZMod (3 ^ n)) = 3 from
        Reference.project_natCast h 3]

/-- The recursive offset is exactly the displayed inverse-prefix sum in the reference law. -/
theorem residueOffset_eq_prefix_sum (q : ℕ) (w : ValuationWord) :
    residueOffset q w = ∑ i ∈ Finset.range w.length,
      (3 : ZMod (3 ^ q)) ^ i * Reference.inverseTwoPow q (total (w.take (i + 1))) := by
  induction w with
  | nil => simp [residueOffset]
  | cons k w ih =>
      rw [residueOffset, List.length_cons, Finset.sum_range_succ']
      have hsum : (∑ i ∈ Finset.range w.length,
          (3 : ZMod (3 ^ q)) ^ (i + 1) *
            Reference.inverseTwoPow q (total ((k :: w).take (i + 1 + 1)))) =
          3 * Reference.inverseTwoPow q k * residueOffset q w := by
        rw [ih, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [List.take_succ_cons, total, List.map_cons, List.sum_cons,
          Reference.inverseTwoPow_add, pow_succ]
        ring
      rw [hsum]
      simp only [List.take_succ_cons, List.take_zero, total, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, add_zero, pow_zero, one_mul]
      ring

/-- Ternary offsets ignore every term after the modulus depth. -/
theorem residueOffset_append_of_level_le (q : ℕ) (u v : ValuationWord)
    (h : q ≤ u.length) : residueOffset q (u ++ v) = residueOffset q u := by
  rw [residueOffset_append]
  have hzero : (3 : ZMod (3 ^ q)) ^ q = 0 := by
    exact_mod_cast ZMod.natCast_self (3 ^ q)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  rw [hk, pow_add, hzero]
  simp

/-- Only the first q letters can affect the offset modulo three to the q. -/
theorem residueOffset_take (q : ℕ) (w : ValuationWord) :
    residueOffset q w = residueOffset q (w.take q) := by
  by_cases h : q ≤ w.length
  · calc
      residueOffset q w = residueOffset q (w.take q ++ w.drop q) := by
        rw [List.take_append_drop]
      _ = residueOffset q (w.take q) :=
        residueOffset_append_of_level_le q _ _ (by rw [List.length_take_of_le h])
  · rw [List.take_of_length_le (Nat.le_of_not_ge h)]

/-- Ternary reduction of a long offset is the lower-level prefix offset. -/
theorem project_residueOffset_take {m n : ℕ} (h : m ≤ n) (w : ValuationWord) :
    Reference.project h (residueOffset n w) = residueOffset m (w.take m) := by
  rw [project_residueOffset, residueOffset_take]

/-- The rational inverse offset uses the reversed chronological word numerator. -/
theorem offset_eq_reverseNumerator (w : ValuationWord) :
    w.offset = (forwardNumerator w.reverse : ℚ) / 2 ^ w.total := by
  induction w with
  | nil => simp [offset, forwardNumerator, total]
  | cons k w ih =>
      rw [offset, ih, List.reverse_cons, forwardNumerator_append_singleton, total_reverse]
      simp only [total, List.map_cons, List.sum_cons]
      push_cast
      rw [pow_add]
      field_simp
      ring

/-- The modular and rational inverse offsets have the same binary-scaled numerator. -/
theorem residueOffset_eq_reverseNumerator (q : ℕ) (w : ValuationWord) :
    residueOffset q w = Reference.inverseTwoPow q w.total *
      (forwardNumerator w.reverse : ZMod (3 ^ q)) := by
  induction w with
  | nil => simp [residueOffset, forwardNumerator]
  | cons k w ih =>
      rw [residueOffset, ih, List.reverse_cons, forwardNumerator_append_singleton, total_reverse]
      simp only [total, List.map_cons, List.sum_cons, Reference.inverseTwoPow_add]
      push_cast
      have hinv := Reference.two_pow_mul_inverseTwoPow q (total w)
      simp only [total] at hinv
      linear_combination -Reference.inverseTwoPow q k * hinv

end ValuationWord

end WordCertDensity
