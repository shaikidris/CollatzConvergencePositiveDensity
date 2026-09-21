/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The representative and modular cancellation proofs specialize the local
Transfer.AffineMap arguments, adapted from Lech Mazur, Copyright 2026
Lech Mazur, under Apache License 2.0. LICENSE and NOTICE are retained at
research/sources/mazur_830b9d3f38f2/.
-/
module

public import WordCertDensity.Reference.AffineBlocks

/-! # Affine permutations of the exact ternary block fibers -/

@[expose] public section

namespace WordCertDensity.Reference

open scoped Classical

/-- The canonical coordinates of a complete ternary projection fiber. -/
def fiberLift (u v : ℕ) (y : ZMod (3 ^ v)) (z : ZMod (3 ^ u)) : ZMod (3 ^ (u + v)) :=
  (y.val : ZMod (3 ^ (u + v))) + (3 : ZMod (3 ^ (u + v))) ^ v * z.val

/-- The fixed ternary scale removes dependence on the representative of the upper coordinate. -/
theorem blockMap_natCast (u v : ℕ) (w : ValuationWord) (a : ℕ) :
    blockMap u v w (a : ZMod (3 ^ u)) =
      ValuationWord.residueOffset (u + v) w.reverse +
        (3 : ZMod (3 ^ (u + v))) ^ v * inverseTwoPow (u + v) w.total * a := by
  have hm := Nat.ModEq.mul_left' (3 ^ v) (Nat.mod_modEq a (3 ^ u))
  rw [← pow_add, Nat.add_comm v u] at hm
  have heq : (3 : ZMod (3 ^ (u + v))) ^ v *
      ((a % 3 ^ u : ℕ) : ZMod (3 ^ (u + v))) =
        (3 : ZMod (3 ^ (u + v))) ^ v * a := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      (ZMod.natCast_eq_natCast_iff _ _ (3 ^ (u + v))).mpr hm
  simp only [blockMap, ZMod.val_natCast]
  linear_combination inverseTwoPow (u + v) w.total * heq

/-- Projecting an ambient residue restores its scaled value in the block map. -/
theorem blockMap_project (u v : ℕ) (w : ValuationWord) (z : ZMod (3 ^ (u + v))) :
    blockMap u v w (project (Nat.le_add_right u v) z) =
      ValuationWord.residueOffset (u + v) w.reverse +
        (3 : ZMod (3 ^ (u + v))) ^ v * inverseTwoPow (u + v) w.total * z := by
  have hp : project (Nat.le_add_right u v) z = (z.val : ZMod (3 ^ u)) := by
    simpa only [ZMod.natCast_zmod_val] using project_natCast (Nat.le_add_right u v) z.val
  rw [hp, blockMap_natCast, ZMod.natCast_zmod_val]

/-- Every block map injects the entire shorter ternary group, including at depth zero. -/
theorem blockMap_injective (u v : ℕ) (w : ValuationWord) :
    Function.Injective (blockMap u v w) := by
  intro z t heq
  have h := add_left_cancel heq
  change (3 : ZMod (3 ^ (u + v))) ^ v * inverseTwoPow (u + v) w.total * z.val =
    (3 : ZMod (3 ^ (u + v))) ^ v * inverseTwoPow (u + v) w.total * t.val at h
  have hc := two_pow_mul_inverseTwoPow (u + v) w.total
  have hs : (3 : ZMod (3 ^ (u + v))) ^ v * z.val =
      (3 : ZMod (3 ^ (u + v))) ^ v * t.val := by
    linear_combination (2 : ZMod (3 ^ (u + v))) ^ w.total * h -
      ((3 : ZMod (3 ^ (u + v))) ^ v * ((z.val : ZMod (3 ^ (u + v))) - t.val)) * hc
  have hm : 3 ^ v * z.val ≡ 3 ^ v * t.val [MOD 3 ^ (u + v)] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hs
  rw [show 3 ^ (u + v) = 3 ^ v * 3 ^ u by rw [← pow_add, Nat.add_comm]] at hm
  have ht := Nat.ModEq.mul_left_cancel' (pow_ne_zero v (by decide : (3 : ℕ) ≠ 0)) hm
  have hh := (ZMod.natCast_eq_natCast_iff _ _ (3 ^ u)).mpr ht
  simpa only [ZMod.natCast_zmod_val] using hh

/-- The low coordinate of a block map is exactly its reversed-word offset. -/
theorem project_blockMap (u v : ℕ) (w : ValuationWord) (z : ZMod (3 ^ u)) :
    project (Nat.le_add_left v u) (blockMap u v w z) =
      ValuationWord.residueOffset v w.reverse := by
  have hz : (3 : ZMod (3 ^ v)) ^ v = 0 := by
    exact_mod_cast ZMod.natCast_self (3 ^ v)
  simp only [blockMap, map_add, map_mul, map_pow, ValuationWord.project_residueOffset,
    map_ofNat, hz, zero_mul, add_zero]

/-- Canonical fiber coordinates reduce to their literal lower residue. -/
theorem project_fiberLift (u v : ℕ) (y : ZMod (3 ^ v)) (z : ZMod (3 ^ u)) :
    project (Nat.le_add_left v u) (fiberLift u v y z) = y := by
  have hz : (3 : ZMod (3 ^ v)) ^ v = 0 := by
    exact_mod_cast ZMod.natCast_self (3 ^ v)
  simp only [fiberLift, map_add, map_mul, map_pow, project_natCast, map_ofNat,
    hz, zero_mul, add_zero, ZMod.natCast_zmod_val]

/-- Exact cardinalities identify the whole image of the block injection. -/
theorem image_blockMap (u v : ℕ) (w : ValuationWord) :
    Finset.univ.image (blockMap u v w) =
      fiber (Nat.le_add_left v u) (ValuationWord.residueOffset v w.reverse) := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hy
    exact (mem_fiber _ _ _).mpr (project_blockMap u v w z)
  · rw [Finset.card_image_of_injective _ (blockMap_injective u v w),
      Finset.card_univ, ZMod.card, card_fiber]
    simp

/-- The reversed-word low offset is the exact block compatibility condition. -/
theorem mem_range_blockMap (u v : ℕ) (w : ValuationWord) (x : ZMod (3 ^ (u + v))) :
    x ∈ Set.range (blockMap u v w) ↔
      project (Nat.le_add_left v u) x = ValuationWord.residueOffset v w.reverse := by
  rw [← mem_fiber, ← image_blockMap]
  simp

/-- Translation by the inverse multiplier realizes the canonical coordinate on a fiber. -/
theorem blockMap_translate (u v : ℕ) (w : ValuationWord) (r z : ZMod (3 ^ u)) :
    blockMap u v w (r + (2 : ZMod (3 ^ u)) ^ w.total * z) =
      blockMap u v w r + (3 : ZMod (3 ^ (u + v))) ^ v * z.val := by
  have h := blockMap_natCast u v w (r.val + 2 ^ w.total * z.val)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    ZMod.natCast_zmod_val] at h
  rw [h, blockMap]
  have hc := two_pow_mul_inverseTwoPow (u + v) w.total
  linear_combination (3 : ZMod (3 ^ (u + v))) ^ v *
    (z.val : ZMod (3 ^ (u + v))) * hc

/-- A compatible word has a unique origin over the canonical lift of the low residue. -/
theorem exists_blockOrigin (u v : ℕ) (y : ZMod (3 ^ v)) (w : ValuationWord)
    (hw : ValuationWord.residueOffset v w.reverse = y) :
    ∃ r : ZMod (3 ^ u), blockMap u v w r = (y.val : ZMod (3 ^ (u + v))) := by
  apply (mem_range_blockMap u v w _).mpr
  rw [project_natCast, ZMod.natCast_zmod_val, hw]

end WordCertDensity.Reference
