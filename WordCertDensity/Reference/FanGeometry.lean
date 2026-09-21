/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Reference.Fan
import WordCertDensity.Reference.TransferRecurrence

/-! # The exact ternary coset embedding and compatible fan predecessors -/

namespace WordCertDensity.Reference

open scoped Classical

/-- The positive odd letters, indexed without a zero valuation. -/
def oddLetter (j : ℕ) : ℕ+ := ⟨2 * j + 1, by omega⟩

/-- The positive even letters. -/
def evenLetter (j : ℕ) : ℕ+ := ⟨2 * j + 2, by omega⟩

/-- Odd letters have unique natural indices. -/
theorem oddLetter_injective : Function.Injective oddLetter := by
  intro j k h
  have h := congrArg PNat.val h
  dsimp [oddLetter] at h
  omega

/-- Even letters have unique natural indices. -/
theorem evenLetter_injective : Function.Injective evenLetter := by
  intro j k h
  have h := congrArg PNat.val h
  dsimp [evenLetter] at h
  omega

/-- Multiplication by the binary power gives the exact singleton affine numerator. -/
theorem singletonMap_numerator (m : ℕ) (a : ℕ+) (x : ZMod (3 ^ m)) :
    (2 : ZMod (3 ^ (m + 1))) ^ (a : ℕ) * Transfer.wordMap [a] (m + 1) x =
      1 + 3 * (x.val : ZMod (3 ^ (m + 1))) := by
  simp only [Transfer.wordMap, ValuationWord.residueOffset, ValuationWord.total,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    mul_zero, mul_one, List.length_singleton, pow_one]
  have h := two_pow_mul_inverseTwoPow (m + 1) a
  linear_combination (1 + 3 * (x.val : ZMod (3 ^ (m + 1)))) * h

/-- The manuscript's map phi is exactly the one-letter inverse map with valuation one. -/
noncomputable def fanEmbedding (m : ℕ) (x : ZMod (3 ^ m)) : ZMod (3 ^ (m + 1)) :=
  Transfer.wordMap [1] (m + 1) x

/-- The literal numerator equation characterizes the fan embedding. -/
theorem two_mul_fanEmbedding (m : ℕ) (x : ZMod (3 ^ m)) :
    2 * fanEmbedding m x = 1 + 3 * (x.val : ZMod (3 ^ (m + 1))) := by
  simpa only [fanEmbedding, PNat.val_ofNat, pow_one] using singletonMap_numerator m 1 x

/-- The embedding is injective at every level, including level zero. -/
theorem fanEmbedding_injective (m : ℕ) : Function.Injective (fanEmbedding m) :=
  Transfer.wordMap_injective [1] (q := m + 1) (by simp)

/-- The image lies in the ternary residue-two coset. -/
theorem project_fanEmbedding (m : ℕ) (x : ZMod (3 ^ m)) :
    project (show 1 ≤ m + 1 by omega) (fanEmbedding m x) = 2 := by
  rw [fanEmbedding, Transfer.project_wordMap [1] (by simp)]
  norm_num [ValuationWord.residueOffset, inverseTwoPow_eq_inv]
  change (2 : ZMod 3)⁻¹ = 2
  have h := two_pow_mul_inverseTwoPow 1 1
  norm_num only [pow_one, inverseTwoPow_eq_inv] at h
  calc
    (2 : ZMod 3)⁻¹ = 2 * (2 * (2 : ZMod 3)⁻¹) := by
      rw [← mul_assoc, show (2 : ZMod 3) * 2 = 1 by decide, one_mul]
    _ = 2 := by rw [h]; norm_num

/-- The fan embedding enumerates the entire residue-two coset once. -/
theorem image_fanEmbedding (m : ℕ) :
    Finset.univ.image (fanEmbedding m) = fiber (show 1 ≤ m + 1 by omega) 2 := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    exact (mem_fiber _ _ _).mpr (project_fanEmbedding m x)
  · rw [Finset.card_image_of_injective _ (fanEmbedding_injective m),
      Finset.card_univ, ZMod.card, card_fiber]
    simp

/-- The natural representative of the embedding retains residue two modulo three. -/
theorem fanEmbedding_val_mod (m : ℕ) (x : ZMod (3 ^ m)) :
    (fanEmbedding m x).val % 3 = 2 := by
  have h := project_fanEmbedding m x
  rw [← ZMod.natCast_zmod_val (fanEmbedding m x), project_natCast] at h
  exact (ZMod.natCast_eq_natCast_iff _ 2 3).mp h

/-- Compatibility at the embedded point selects exactly the odd letters. -/
theorem compatible_fanEmbedding_iff (m : ℕ) (x : ZMod (3 ^ m)) (a : ℕ+) :
    (2 ^ (a : ℕ) * (fanEmbedding m x).val) % 3 = 1 ↔ ∃ j, a = oddLetter j := by
  have hv := fanEmbedding_val_mod m x
  have hn : ¬ 3 ∣ (fanEmbedding m x).val := by
    intro h
    have := Nat.mod_eq_zero_of_dvd h
    omega
  have he := Roots.inverseExponent_iff hn a.property
  simp only [Roots.inverseExponent, Roots.inverseParity, hv, show ¬ (2 : ℕ) = 1 by decide,
    if_false] at he
  constructor
  · intro h
    obtain ⟨j, hj⟩ := he.mp h
    exact ⟨j, Subtype.ext hj⟩
  · rintro ⟨j, rfl⟩
    exact he.mpr ⟨j, rfl⟩

/-- Adding an even number of valuations gives the literal affine fan predecessor. -/
theorem letter_fanMap (m j : ℕ) (a b : ℕ+) (hab : (a : ℕ) = 2 * j + (b : ℕ))
    (x : ZMod (3 ^ m)) :
    Transfer.wordMap [a] (m + 1) (fanMap m j x) = Transfer.wordMap [b] (m + 1) x := by
  have hx : x = (x.val : ZMod (3 ^ m)) := (ZMod.natCast_zmod_val x).symm
  rw [hx, fanMap_natCast, Transfer.wordMap_natCast _ (by simp)]
  simp only [ValuationWord.residueOffset, ValuationWord.total, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, add_zero, mul_zero, mul_one,
    List.length_singleton, pow_one, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [← Roots.value_eq_quotient]
  have hv : (3 : ZMod (3 ^ (m + 1))) * (Roots.value j : ZMod (3 ^ (m + 1))) + 1 = 4 ^ j := by
    have h := congrArg (fun n : ℕ => (n : ZMod (3 ^ (m + 1))))
      (Roots.three_mul_value_add_one j)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using h
  have he : (2 : ZMod (3 ^ (m + 1))) ^ (a : ℕ) = 4 ^ j * 2 ^ (b : ℕ) := by
    norm_num [hab, pow_add, pow_mul]
  have hc := two_pow_mul_inverseTwoPow (m + 1) a
  rw [he] at hc
  have hp := singletonMap_numerator m b x
  simp only [ZMod.natCast_zmod_val] at *
  linear_combination -inverseTwoPow (m + 1) a * (4 ^ j * hp - hv) +
    Transfer.wordMap [b] (m + 1) x * hc

/-- The odd-letter inverse input is the literal affine fan map. -/
theorem oddLetter_fanMap (m j : ℕ) (x : ZMod (3 ^ m)) :
    Transfer.wordMap [oddLetter j] (m + 1) (fanMap m j x) = fanEmbedding m x :=
  letter_fanMap m j (oddLetter j) 1 rfl x

end WordCertDensity.Reference
