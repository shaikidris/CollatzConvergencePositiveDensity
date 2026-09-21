/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.Recursion
public import WordCertDensity.Roots.Predecessors

/-!
# Compatible one-letter classes

The low ternary affine-image condition is exactly the positive exponent
class already used by the integer predecessor constructor.
-/

@[expose] public section

namespace WordCertDensity.Transfer

/-- A one-letter affine image is precisely the numerator congruence modulo three. -/
theorem mem_range_singleton_nat (a : ℕ+) (n r : ℕ) :
    (r : ZMod (3 ^ (n + 1))) ∈ Set.range (wordMap [a] (n + 1)) ↔
      (2 ^ (a : ℕ) * r) % 3 = 1 := by
  rw [mem_range_wordMap [a] (show [a].length ≤ n + 1 by simp), Reference.project_natCast]
  change (r : ZMod 3) = Reference.inverseTwoPow 1 a * (1 + 3 * 0) ↔ _
  rw [mul_zero, add_zero, mul_one]
  have hinv := Reference.two_pow_mul_inverseTwoPow 1 a
  have he : ((2 ^ (a : ℕ) * r : ℕ) : ZMod 3) = 1 ↔
      (2 ^ (a : ℕ) * r) % 3 = 1 := by
    exact ZMod.natCast_eq_natCast_iff (2 ^ (a : ℕ) * r) 1 3
  rw [← he]
  push_cast
  constructor
  · intro hr
    rw [hr]
    exact hinv
  · intro hr
    have h := congrArg (fun z : ZMod 3 => Reference.inverseTwoPow 1 a * z) hr
    calc
      (r : ZMod 3) = Reference.inverseTwoPow 1 a * ((2 : ZMod 3) ^ (a : ℕ) * r) := by
        linear_combination -r * hinv
      _ = Reference.inverseTwoPow 1 a := by simpa using h

/-- A unit root admits exactly its indexed parity class, at every positive conductor. -/
theorem mem_range_singleton_iff_index {r : ℕ} (hr : ¬ 3 ∣ r) (a : ℕ+) (n : ℕ) :
    (r : ZMod (3 ^ (n + 1))) ∈ Set.range (wordMap [a] (n + 1)) ↔
      ∃ t : ℕ, (a : ℕ) = Roots.inverseExponent r t := by
  rw [mem_range_singleton_nat]
  exact Roots.inverseExponent_iff hr a.property

/-- A root divisible by three has no compatible positive letter. -/
theorem singleton_off_image_of_three_dvd {r : ℕ} (hr : 3 ∣ r) (a : ℕ+) (n : ℕ) :
    (r : ZMod (3 ^ (n + 1))) ∉ Set.range (wordMap [a] (n + 1)) := by
  rw [mem_range_singleton_nat, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hr]
  norm_num

/-- The indexed compatible coefficient sum is one on residue one and two on residue two. -/
theorem indexedLetterCoefficient_hasSum (r : ℕ) :
    HasSum (fun t : ℕ => 3 / (2 : ℝ) ^ Roots.inverseExponent r t)
      (if r % 3 = 1 then 1 else 2) := by
  by_cases hr : r % 3 = 1
  · simpa only [Roots.inverseExponent, Roots.inverseParity, if_pos hr] using
      Reference.evenLetterCoefficient_hasSum
  · simpa only [Roots.inverseExponent, Roots.inverseParity, if_neg hr] using
      Reference.oddLetterCoefficient_hasSum

/-- Every finite selection of compatible indexed letters has coefficient at most two. -/
theorem indexedLetterCoefficient_sum_le (r : ℕ) (A : Finset ℕ) :
    (∑ t ∈ A, 3 / (2 : ℝ) ^ Roots.inverseExponent r t) ≤ 2 := by
  have h := indexedLetterCoefficient_hasSum r
  calc
    _ ≤ ∑' t : ℕ, 3 / (2 : ℝ) ^ Roots.inverseExponent r t :=
      h.summable.sum_le_tsum A (fun _ _ => by positivity)
    _ = _ := h.tsum_eq
    _ ≤ 2 := by split_ifs <;> norm_num

/-- Any finite compatible letter family inherits the factor-two coefficient bound. -/
theorem compatibleLetter_sum_le {r n : ℕ} (hr : ¬ 3 ∣ r) (A : Finset ℕ+)
    (hA : ∀ a ∈ A, (r : ZMod (3 ^ (n + 1))) ∈ Set.range (wordMap [a] (n + 1))) :
    (∑ a ∈ A, 3 / (2 : ℝ) ^ (a : ℕ)) ≤ 2 := by
  classical
  have hex (a : A) : ∃ t : ℕ, (a.val : ℕ) = Roots.inverseExponent r t :=
    (mem_range_singleton_iff_index hr a.val n).mp (hA a.val a.property)
  let idx (a : A) : ℕ := Classical.choose (hex a)
  have he (a : A) : (a.val : ℕ) = Roots.inverseExponent r (idx a) :=
    Classical.choose_spec (hex a)
  have hi : Function.Injective idx := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact (he a).trans ((congrArg (Roots.inverseExponent r) hab).trans (he b).symm)
  have h := indexedLetterCoefficient_sum_le r (Finset.univ.image idx)
  rw [Finset.sum_image (fun a _ b _ hab => hi hab)] at h
  simp_rw [← he] at h
  exact (Finset.sum_attach A (fun a => 3 / (2 : ℝ) ^ (a : ℕ))).symm ▸ h

end WordCertDensity.Transfer
