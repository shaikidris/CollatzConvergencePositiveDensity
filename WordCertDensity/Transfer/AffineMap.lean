/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The modular cancellation argument is adapted from Lech Mazur,
Copyright 2026 Lech Mazur, under Apache License 2.0. The source LICENSE and
NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
This version uses the actual word length and the local inverse offset.
-/
module

public import WordCertDensity.Reference.Projectivity
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The affine map of one inverse word

At a level at least the word length, the affine map injects the remaining
ternary group onto exactly the offset fiber. Representatives are evaluated
using their natural values; the natural-cast lemma proves independence of
that choice after multiplication by the ternary word scale.
-/

@[expose] public section

namespace WordCertDensity

namespace Transfer

/-- The affine word map on the remaining ternary precision. -/
noncomputable def wordMap (w : ValuationWord) (q : ℕ)
    (z : ZMod (3 ^ (q - w.length))) : ZMod (3 ^ q) :=
  ValuationWord.residueOffset q w + (3 : ZMod (3 ^ q)) ^ w.length *
    Reference.inverseTwoPow q w.total * (z.val : ZMod (3 ^ q))

/-- The real transfer coefficient is the rational physical word slope. -/
noncomputable def weight (w : ValuationWord) : ℝ := (w.slope : ℝ)

/-- The transfer coefficient in literal powers of three and two. -/
theorem weight_eq (w : ValuationWord) : weight w = (3 : ℝ) ^ w.length / 2 ^ w.total := by
  simp [weight, ValuationWord.slope]

/-- Every affine word coefficient is positive. -/
theorem weight_pos (w : ValuationWord) : 0 < weight w := by
  rw [weight_eq]
  positivity

/-- Ternary multiplication makes the affine map independent of natural representatives. -/
theorem wordMap_natCast (w : ValuationWord) {q : ℕ} (hq : w.length ≤ q) (a : ℕ) :
    wordMap w q (a : ZMod (3 ^ (q - w.length))) =
      ValuationWord.residueOffset q w + (3 : ZMod (3 ^ q)) ^ w.length *
        Reference.inverseTwoPow q w.total * (a : ZMod (3 ^ q)) := by
  have hm := Nat.ModEq.mul_left' (3 ^ w.length) (Nat.mod_modEq a (3 ^ (q - w.length)))
  rw [← pow_add, Nat.add_sub_of_le hq] at hm
  have heq : (3 : ZMod (3 ^ q)) ^ w.length *
      ((a % 3 ^ (q - w.length) : ℕ) : ZMod (3 ^ q)) =
        (3 : ZMod (3 ^ q)) ^ w.length * (a : ZMod (3 ^ q)) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      (ZMod.natCast_eq_natCast_iff _ _ (3 ^ q)).mpr hm
  simp only [wordMap, ZMod.val_natCast]
  linear_combination Reference.inverseTwoPow q w.total * heq

/-- The affine word map is injective at every valid ambient level. -/
theorem wordMap_injective (w : ValuationWord) {q : ℕ} (hq : w.length ≤ q) :
    Function.Injective (wordMap w q) := by
  intro z v heq
  have hscaled : (3 : ZMod (3 ^ q)) ^ w.length * (z.val : ZMod (3 ^ q)) =
      (3 : ZMod (3 ^ q)) ^ w.length * (v.val : ZMod (3 ^ q)) := by
    have h := add_left_cancel heq
    have hc := Reference.two_pow_mul_inverseTwoPow q w.total
    change (3 : ZMod (3 ^ q)) ^ w.length * Reference.inverseTwoPow q w.total *
        (z.val : ZMod (3 ^ q)) =
      (3 : ZMod (3 ^ q)) ^ w.length * Reference.inverseTwoPow q w.total *
        (v.val : ZMod (3 ^ q)) at h
    linear_combination (2 : ZMod (3 ^ q)) ^ w.total * h -
      ((3 : ZMod (3 ^ q)) ^ w.length * ((z.val : ZMod (3 ^ q)) - v.val)) * hc
  have hm : 3 ^ w.length * z.val ≡ 3 ^ w.length * v.val [MOD 3 ^ q] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hscaled
  rw [show 3 ^ q = 3 ^ w.length * 3 ^ (q - w.length) by
    rw [← pow_add, Nat.add_sub_of_le hq]] at hm
  have hv := Nat.ModEq.mul_left_cancel' (pow_ne_zero w.length (by decide : 3 ≠ 0)) hm
  have hc := (ZMod.natCast_eq_natCast_iff _ _ (3 ^ (q - w.length))).mpr hv
  simpa only [ZMod.natCast_zmod_val] using hc

/-- The image lies in the fiber of the word's inverse offset. -/
theorem project_wordMap (w : ValuationWord) {q : ℕ} (hq : w.length ≤ q)
    (z : ZMod (3 ^ (q - w.length))) :
    Reference.project hq (wordMap w q z) = ValuationWord.residueOffset w.length w := by
  have hz : (3 : ZMod (3 ^ w.length)) ^ w.length = 0 := by
    exact_mod_cast ZMod.natCast_self (3 ^ w.length)
  simp only [wordMap, map_add, map_mul, map_pow, ValuationWord.project_residueOffset,
    map_ofNat, hz, zero_mul, add_zero]

/-- Injection and exact cardinality identify the complete affine image fiber. -/
theorem image_wordMap (w : ValuationWord) {q : ℕ} (hq : w.length ≤ q) :
    Finset.univ.image (wordMap w q) =
      Reference.fiber hq (ValuationWord.residueOffset w.length w) := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hy
    exact (Reference.mem_fiber _ _ _).mpr (project_wordMap w hq z)
  · rw [Finset.card_image_of_injective _ (wordMap_injective w hq),
      Finset.card_univ, ZMod.card, Reference.card_fiber]

/-- A residue belongs to the affine image exactly when its low offset agrees. -/
theorem mem_range_wordMap (w : ValuationWord) {q : ℕ} (hq : w.length ≤ q)
    (y : ZMod (3 ^ q)) :
    y ∈ Set.range (wordMap w q) ↔ Reference.project hq y =
      ValuationWord.residueOffset w.length w := by
  rw [← Reference.mem_fiber hq _ y, ← image_wordMap w hq]
  simp

/-- Applying the word map to a projected residue restores its scaled ambient value. -/
theorem wordMap_project (w : ValuationWord) {q : ℕ} (hq : w.length ≤ q)
    (z : ZMod (3 ^ q)) :
    wordMap w q (Reference.project (Nat.sub_le q w.length) z) =
      ValuationWord.residueOffset q w + (3 : ZMod (3 ^ q)) ^ w.length *
        Reference.inverseTwoPow q w.total * z := by
  have hp : Reference.project (Nat.sub_le q w.length) z =
      (z.val : ZMod (3 ^ (q - w.length))) := by
    simpa only [ZMod.natCast_zmod_val] using
      Reference.project_natCast (Nat.sub_le q w.length) z.val
  rw [hp, wordMap_natCast w hq, ZMod.natCast_zmod_val]

/-- Appending a tail offset is the actual affine word map of that tail. -/
theorem wordMap_offset_append (w v : ValuationWord) {q : ℕ} (hq : w.length ≤ q) :
    ValuationWord.residueOffset q (w ++ v) =
      wordMap w q (ValuationWord.residueOffset (q - w.length) v) := by
  rw [← ValuationWord.project_residueOffset (Nat.sub_le q w.length) v,
    wordMap_project w hq, ValuationWord.residueOffset_append]

/-- The empty word is the identity map at every level, including zero. -/
theorem wordMap_nil (q : ℕ) (z : ZMod (3 ^ q)) : wordMap [] q z = z := by
  simp [wordMap, ValuationWord.total]

/-- The empty word has coefficient one. -/
theorem weight_nil : weight [] = 1 := by
  simp [weight_eq, ValuationWord.total]

end Transfer

end WordCertDensity
