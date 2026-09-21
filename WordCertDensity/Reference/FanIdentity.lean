/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Reference.FanGeometry

/-! # The exact density identity of the whole affine fan -/

namespace WordCertDensity.Reference

open scoped Classical

/-- The literal transfer quotient at an odd compatible letter is the fan predecessor. -/
theorem transferInput_fanEmbedding (m j : ℕ) (x : ZMod (3 ^ m)) :
    transferInput m (fanEmbedding m x) (oddLetter j) = fanMap m j x := by
  apply Transfer.wordMap_injective [oddLetter j] (q := m + 1) (by simp)
  rw [wordMap_transferInput m _ _ ((compatible_fanEmbedding_iff m x _).mpr ⟨j, rfl⟩),
    oddLetter_fanMap]

/-- Odd geometric coefficients are one half times the original quarter-power fan weights. -/
theorem oddLetter_coefficient (j : ℕ) :
    (2 : ℝ) ^ (-((oddLetter j : ℕ) : ℤ)) = (1 / 2 : ℝ) * 4 ^ (-(j : ℤ)) := by
  simp only [zpow_neg, zpow_natCast]
  change ((2 : ℝ) ^ (2 * j + 1))⁻¹ = (1 / 2) * ((4 : ℝ) ^ j)⁻¹
  rw [pow_add, pow_mul]
  norm_num

/-- The conditional density at the embedded coset is nine fourths of the whole marker fan. -/
theorem density_fanEmbedding (m : ℕ) (x : ZMod (3 ^ m)) :
    density (m + 1) (fanEmbedding m x) = (9 / 4 : ℝ) * fan m x := by
  let f : ℕ+ → ℝ := fun a => if (2 ^ (a : ℕ) * (fanEmbedding m x).val) % 3 = 1 then
    (2 : ℝ) ^ (-((a : ℕ) : ℤ)) * density m (transferInput m (fanEmbedding m x) a) else 0
  have hs : Function.support f ⊆ Set.range oddLetter := by
    intro a ha
    have hc : (2 ^ (a : ℕ) * (fanEmbedding m x).val) % 3 = 1 := by
      by_contra hn
      exact ha (by simp [f, hn])
    obtain ⟨j, hj⟩ := (compatible_fanEmbedding_iff m x a).mp hc
    exact ⟨j, hj.symm⟩
  have hf : ∑' a, f a = ∑' j, f (oddLetter j) := (oddLetter_injective.tsum_eq hs).symm
  change density (m + 1) (fanEmbedding m x) = _
  rw [referenceTransfer]
  change 3 * (∑' a, f a) = _
  rw [hf]
  have hj (j : ℕ) : f (oddLetter j) =
      (1 / 2 : ℝ) * 4 ^ (-(j : ℤ)) * density m (fanMap m j x) := by
    simp only [f, if_pos ((compatible_fanEmbedding_iff m x _).mpr ⟨j, rfl⟩),
      transferInput_fanEmbedding, oddLetter_coefficient]
  simp_rw [hj]
  rw [fan, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro j
  unfold marker
  ring

/-- The exact factor four ninths uses full density, without unit renormalization. -/
theorem fan_density_identity (m : ℕ) (x : ZMod (3 ^ m)) :
    fan m x = (4 / 9 : ℝ) * density (m + 1) (fanEmbedding m x) := by
  rw [density_fanEmbedding]
  ring

end WordCertDensity.Reference
