/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Reference.Law

/-! # The literal affine fan permutations

The offset is a natural integer quotient before passage to residues. The
binary unit proves permutation at every level, including the one-point group.
-/

namespace WordCertDensity.Reference

/-- The affine compression fan on the complete ternary residue group. -/
def fanMap (m j : ℕ) (x : ZMod (3^m)) : ZMod (3^m) :=
  4^j*x+((4^j-1)/3 : ℕ)

/-- The initial fan map is the identity. -/
@[simp] theorem fanMap_zero (m : ℕ) (x : ZMod (3^m)) : fanMap m 0 x = x := by
  simp [fanMap]

/-- Reduction of the actual integer fan source is exactly this residue map. -/
theorem fanMap_natCast (m j x : ℕ) :
    fanMap m j (x : ZMod (3^m)) = ((4^j*x+(4^j-1)/3 : ℕ) : ZMod (3^m)) := by
  simp [fanMap]

/-- A power of four has the existing inverse binary-power multiplier. -/
theorem fanMap_multiplier_inverse (m j : ℕ) :
    inverseTwoPow m (2*j)*(4 : ZMod (3^m))^j = 1 := by
  have he : (2 : ZMod (3^m))^(2*j) = (4 : ZMod (3^m))^j := by
    rw [pow_mul]
    norm_num
  rw [← he, mul_comm, two_pow_mul_inverseTwoPow]

/-- The whole-group affine map is injective, without a positive-level restriction. -/
theorem fanMap_injective (m j : ℕ) : Function.Injective (fanMap m j) := by
  intro x y he
  have h : (4 : ZMod (3^m))^j*x = (4 : ZMod (3^m))^j*y := add_right_cancel he
  have hh := congrArg (fun z => inverseTwoPow m (2*j)*z) h
  simpa only [← mul_assoc, fanMap_multiplier_inverse, one_mul] using hh

/-- Every fan map permutes the entire finite group. -/
theorem fanMap_bijective (m j : ℕ) : Function.Bijective (fanMap m j) :=
  ⟨fanMap_injective m j, Finite.surjective_of_injective (fanMap_injective m j)⟩

/-- Pullback by a fan permutation preserves the full-group mean. -/
theorem mean_fanMap (m j : ℕ) (f : ZMod (3^m) → ℝ) :
    mean m (fun x => f (fanMap m j x)) = mean m f := by
  rw [mean, (fanMap_bijective m j).sum_comp f]
  rfl

end WordCertDensity.Reference
