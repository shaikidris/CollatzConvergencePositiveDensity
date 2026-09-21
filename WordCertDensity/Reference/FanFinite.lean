/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Reference.Fan

/-! # Enlarging finite indexed images to the full nonnegative fan -/

namespace WordCertDensity.Reference

open scoped Classical

/-- A finite image retains its index until the nonnegative fan enlargement. -/
theorem finiteFanImage_le {ι : Type*} (R : Finset ι) (k : ℕ)
    (src : ι → ℕ) (weight : ι → ℝ) (image : Finset (ι × ℕ))
    (hweight : ∀ i ∈ R, 0 ≤ weight i) (himage : ∀ p ∈ image, p.1 ∈ R) :
    (∑ p ∈ image, weight p.1*(4 : ℝ)^(-(p.2 : ℤ))*
      marker k (fanMap k p.2 (src p.1 : ZMod (3^k)))) ≤
        ∑ i ∈ R, weight i*fan k (src i : ZMod (3^k)) := by
  let J := image.image Prod.snd
  have hsub : image ⊆ R.product J := by
    intro p hp
    exact Finset.mem_product.mpr ⟨himage p hp, Finset.mem_image_of_mem Prod.snd hp⟩
  calc
    _ ≤ ∑ p ∈ R.product J, weight p.1*(4 : ℝ)^(-(p.2 : ℤ))*
        marker k (fanMap k p.2 (src p.1 : ZMod (3^k))) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p hp _
      exact mul_nonneg (mul_nonneg (hweight p.1 (Finset.mem_product.mp hp).1)
        (by positivity)) (marker_nonneg k _)
    _ = ∑ i ∈ R, weight i*(∑ j ∈ J, (4 : ℝ)^(-(j : ℤ))*
        marker k (fanMap k j (src i : ZMod (3^k)))) := by
      rw [Finset.product_eq_sprod, Finset.sum_product R J]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact mul_assoc _ _ _
    _ ≤ _ := Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (fan_finite_le k _ J) (hweight i hi)

/-- The finite-index form of the prepared compression-image handoff. -/
theorem finiteCompressionFan (n k : ℕ) (src : Fin n → ℕ) (weight : Fin n → ℝ)
    (image : Finset (Fin n × ℕ)) (hweight : ∀ i, 0 ≤ weight i) :
    (∑ p ∈ image, weight p.1*(4 : ℝ)^(-(p.2 : ℤ))*
      marker k (fanMap k p.2 (src p.1 : ZMod (3^k)))) ≤
        ∑ i, weight i*fan k (src i : ZMod (3^k)) :=
  finiteFanImage_le Finset.univ k src weight image (fun i _ => hweight i)
    (fun p _ => Finset.mem_univ p.1)

end WordCertDensity.Reference
