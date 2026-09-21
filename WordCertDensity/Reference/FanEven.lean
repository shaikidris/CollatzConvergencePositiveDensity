/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Reference.FanIdentity

/-! # The other unit coset carries exactly half the embedded fan density -/

namespace WordCertDensity.Reference

open scoped Classical

/-- Valuation two parametrizes the residue-one coset. -/
noncomputable def evenEmbedding (m : ℕ) (x : ZMod (3 ^ m)) : ZMod (3 ^ (m + 1)) :=
  Transfer.wordMap [2] (m + 1) x

/-- The even embedding is injective at every level. -/
theorem evenEmbedding_injective (m : ℕ) : Function.Injective (evenEmbedding m) :=
  Transfer.wordMap_injective [2] (q := m + 1) (by simp)

/-- Its image lies in the residue-one coset. -/
theorem project_evenEmbedding (m : ℕ) (x : ZMod (3 ^ m)) :
    project (show 1 ≤ m + 1 by omega) (evenEmbedding m x) = 1 := by
  rw [evenEmbedding, Transfer.project_wordMap [2] (by simp)]
  norm_num [ValuationWord.residueOffset, inverseTwoPow_eq_inv]
  change (1 : ZMod 3)⁻¹ = 1
  exact ZMod.inv_one 3

/-- The even embedding enumerates the complete residue-one coset once. -/
theorem image_evenEmbedding (m : ℕ) :
    Finset.univ.image (evenEmbedding m) = fiber (show 1 ≤ m + 1 by omega) 1 := by
  apply Finset.eq_of_subset_of_card_le
  · intro y hy
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy
    exact (mem_fiber _ _ _).mpr (project_evenEmbedding m x)
  · rw [Finset.card_image_of_injective _ (evenEmbedding_injective m),
      Finset.card_univ, ZMod.card, card_fiber]
    simp

/-- Natural representatives of the even embedding retain residue one. -/
theorem evenEmbedding_val_mod (m : ℕ) (x : ZMod (3 ^ m)) :
    (evenEmbedding m x).val % 3 = 1 := by
  have h := project_evenEmbedding m x
  rw [← ZMod.natCast_zmod_val (evenEmbedding m x), project_natCast] at h
  exact (ZMod.natCast_eq_natCast_iff _ 1 3).mp h

/-- Compatibility at this coset selects exactly positive even letters. -/
theorem compatible_evenEmbedding_iff (m : ℕ) (x : ZMod (3 ^ m)) (a : ℕ+) :
    (2 ^ (a : ℕ) * (evenEmbedding m x).val) % 3 = 1 ↔ ∃ j, a = evenLetter j := by
  have hv := evenEmbedding_val_mod m x
  have hn : ¬ 3 ∣ (evenEmbedding m x).val := by
    intro h
    have := Nat.mod_eq_zero_of_dvd h
    omega
  have he := Roots.inverseExponent_iff hn a.property
  simp only [Roots.inverseExponent, Roots.inverseParity, hv, if_true] at he
  constructor
  · intro h
    obtain ⟨j, hj⟩ := he.mp h
    exact ⟨j, Subtype.ext hj⟩
  · rintro ⟨j, rfl⟩
    exact he.mpr ⟨j, rfl⟩

/-- Even letters have the same fan predecessors with the valuation-two embedding. -/
theorem evenLetter_fanMap (m j : ℕ) (x : ZMod (3 ^ m)) :
    Transfer.wordMap [evenLetter j] (m + 1) (fanMap m j x) = evenEmbedding m x :=
  letter_fanMap m j (evenLetter j) 2 rfl x

/-- The literal natural transfer quotient is again the same fan map. -/
theorem transferInput_evenEmbedding (m j : ℕ) (x : ZMod (3 ^ m)) :
    transferInput m (evenEmbedding m x) (evenLetter j) = fanMap m j x := by
  apply Transfer.wordMap_injective [evenLetter j] (q := m + 1) (by simp)
  rw [wordMap_transferInput m _ _ ((compatible_evenEmbedding_iff m x _).mpr ⟨j, rfl⟩),
    evenLetter_fanMap]

/-- Even geometric coefficients are one quarter of the fan coefficients. -/
theorem evenLetter_coefficient (j : ℕ) :
    (2 : ℝ) ^ (-((evenLetter j : ℕ) : ℤ)) = (1 / 4 : ℝ) * 4 ^ (-(j : ℤ)) := by
  simp only [zpow_neg, zpow_natCast]
  change ((2 : ℝ) ^ (2 * j + 2))⁻¹ = (1 / 4) * ((4 : ℝ) ^ j)⁻¹
  rw [pow_add, pow_mul]
  norm_num

/-- The residue-one density is nine eighths of the original marker fan. -/
theorem density_evenEmbedding (m : ℕ) (x : ZMod (3 ^ m)) :
    density (m + 1) (evenEmbedding m x) = (9 / 8 : ℝ) * fan m x := by
  let f : ℕ+ → ℝ := fun a => if (2 ^ (a : ℕ) * (evenEmbedding m x).val) % 3 = 1 then
    (2 : ℝ) ^ (-((a : ℕ) : ℤ)) * density m (transferInput m (evenEmbedding m x) a) else 0
  have hs : Function.support f ⊆ Set.range evenLetter := by
    intro a ha
    have hc : (2 ^ (a : ℕ) * (evenEmbedding m x).val) % 3 = 1 := by
      by_contra hn
      exact ha (by simp [f, hn])
    obtain ⟨j, hj⟩ := (compatible_evenEmbedding_iff m x a).mp hc
    exact ⟨j, hj.symm⟩
  have hf : ∑' a, f a = ∑' j, f (evenLetter j) := (evenLetter_injective.tsum_eq hs).symm
  rw [referenceTransfer]
  change 3 * (∑' a, f a) = _
  rw [hf]
  have hj (j : ℕ) : f (evenLetter j) =
      (1 / 4 : ℝ) * 4 ^ (-(j : ℤ)) * density m (fanMap m j x) := by
    simp only [f, if_pos ((compatible_evenEmbedding_iff m x _).mpr ⟨j, rfl⟩),
      transferInput_evenEmbedding, evenLetter_coefficient]
  simp_rw [hj]
  rw [fan, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro j
  unfold marker
  ring

/-- Matched points in the two unit cosets have exact density ratio two. -/
theorem density_coset_ratio (m : ℕ) (x : ZMod (3 ^ m)) :
    density (m + 1) (fanEmbedding m x) = 2 * density (m + 1) (evenEmbedding m x) := by
  rw [density_fanEmbedding, density_evenEmbedding]
  ring

/-- Multiplication by two matches the two explicit unit-coset parametrizations. -/
theorem two_mul_evenEmbedding (m : ℕ) (x : ZMod (3 ^ m)) :
    2 * evenEmbedding m x = fanEmbedding m x := by
  have he := singletonMap_numerator m 2 x
  have ho := two_mul_fanEmbedding m x
  change (2 : ZMod (3 ^ (m + 1))) ^ 2 * evenEmbedding m x = _ at he
  norm_num only [show (2 : ZMod (3 ^ (m + 1))) ^ 2 = 4 by ring] at he
  have hc := two_pow_mul_inverseTwoPow (m + 1) 1
  norm_num only [pow_one] at hc
  linear_combination inverseTwoPow (m + 1) 1 * (he - ho) -
    (2 * evenEmbedding m x - fanEmbedding m x) * hc

/-- On every residue-one point, binary multiplication doubles the actual density. -/
theorem density_two_mul_of_coset_one (m : ℕ) (y : ZMod (3 ^ (m + 1)))
    (hy : project (show 1 ≤ m + 1 by omega) y = 1) :
    density (m + 1) (2 * y) = 2 * density (m + 1) y := by
  have hmem : y ∈ Finset.univ.image (evenEmbedding m) := by
    rw [image_evenEmbedding]
    exact (mem_fiber _ _ _).mpr hy
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hmem
  rw [two_mul_evenEmbedding, density_coset_ratio]

end WordCertDensity.Reference
