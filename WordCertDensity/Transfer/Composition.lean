/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Transfer.Affine

/-! # Word transfer composition and finite payload algebra -/

@[expose] public section

namespace WordCertDensity.Transfer

/-- Concatenation multiplies the original physical transfer coefficients. -/
theorem weight_append (u v : ValuationWord) : weight (u ++ v) = weight u * weight v := by
  simp only [weight, ValuationWord.slope_append, Rat.cast_mul]

/-- Word transfer preserves pointwise order of its payload. -/
theorem wordOperator_mono (w : ValuationWord) (q : ℕ)
    (f g : ZMod (3 ^ (q - w.length)) → ℝ) (h : ∀ z, f z ≤ g z)
    (y : ZMod (3 ^ q)) : wordOperator w q f y ≤ wordOperator w q g y := by
  unfold wordOperator
  apply mul_le_mul_of_nonneg_left _ (weight_pos w).le
  apply Finset.sum_le_sum
  intro z _
  split_ifs
  · exact h z
  · exact le_refl 0

/-- A finite sum of payloads can be transferred before or after summation. -/
theorem wordOperator_finset_sum {α : Type*} (A : Finset α) (w : ValuationWord) (q : ℕ)
    (f : α → ZMod (3 ^ (q - w.length)) → ℝ) (y : ZMod (3 ^ q)) :
    wordOperator w q (fun z => ∑ a ∈ A, f a z) y =
      ∑ a ∈ A, wordOperator w q (f a) y := by
  classical
  unfold wordOperator
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> simp

/-- Composition holds at the actual residual levels, using projections from one ambient group. -/
theorem wordMap_append_project (u v : ValuationWord) {q : ℕ}
    (h : (u ++ v).length ≤ q) (x : ZMod (3 ^ q)) :
    wordMap (u ++ v) q (Reference.project (Nat.sub_le q (u ++ v).length) x) =
      wordMap u q (wordMap v (q - u.length)
        (Reference.project (Nat.sub_le (q - u.length) v.length)
          (Reference.project (Nat.sub_le q u.length) x))) := by
  have hu : u.length ≤ q := by simp only [List.length_append] at h; omega
  have hv : v.length ≤ q - u.length := by simp only [List.length_append] at h; omega
  let z : ZMod (3 ^ q) := ValuationWord.residueOffset q v +
    (3 : ZMod (3 ^ q)) ^ v.length * Reference.inverseTwoPow q v.total * x
  have hz : wordMap v (q - u.length)
      (Reference.project (Nat.sub_le (q - u.length) v.length)
        (Reference.project (Nat.sub_le q u.length) x)) =
      Reference.project (Nat.sub_le q u.length) z := by
    rw [wordMap_project v hv]
    simp only [z, map_add, map_mul, map_pow, map_ofNat,
      ValuationWord.project_residueOffset, Reference.project_inverseTwoPow]
  rw [hz, wordMap_project u hu, wordMap_project (u ++ v) h,
    ValuationWord.residueOffset_append, List.length_append,
    ValuationWord.total_append, Reference.inverseTwoPow_add, pow_add]
  dsimp only [z]
  ring

end WordCertDensity.Transfer
