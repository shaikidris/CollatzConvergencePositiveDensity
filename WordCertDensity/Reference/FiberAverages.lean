/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.AffineMixture

/-! # Exact full-group averaging in canonical ternary fiber coordinates -/

@[expose] public section

namespace WordCertDensity.Reference

open scoped Classical

/-- Canonical coordinates are injective within each projection fiber. -/
theorem fiberLift_injective (u v : ℕ) (y : ZMod (3 ^ v)) :
    Function.Injective (fiberLift u v y) := by
  intro z t h
  dsimp [fiberLift] at h
  apply blockMap_injective u v []
  simpa [blockMap, ValuationWord.total] using add_left_cancel h

/-- Canonical coordinates enumerate every point of the complete fiber once. -/
theorem image_fiberLift (u v : ℕ) (y : ZMod (3 ^ v)) :
    Finset.univ.image (fiberLift u v y) = fiber (Nat.le_add_left v u) y := by
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_fiber _ _ _).mpr (project_fiberLift u v y z)
  · rw [Finset.card_image_of_injective _ (fiberLift_injective u v y),
      Finset.card_univ, ZMod.card, card_fiber]
    simp

/-- Summing a fiber in coordinates is exactly its original finite residue sum. -/
theorem sum_fiberLift (u v : ℕ) (y : ZMod (3 ^ v)) (f : ZMod (3 ^ (u + v)) → ℝ) :
    (∑ z, f (fiberLift u v y z)) = ∑ x ∈ fiber (Nat.le_add_left v u) y, f x := by
  rw [← image_fiberLift, Finset.sum_image (fun a _ b _ h => fiberLift_injective u v y h)]

/-- Full-group averaging decomposes into the two normalized fiber averages. -/
theorem mean_fibers (u v : ℕ) (f : ZMod (3 ^ (u + v)) → ℝ) :
    mean (u + v) f = mean v (fun y => mean u (fun z => f (fiberLift u v y z))) := by
  have hs := Finset.sum_fiberwise (Finset.univ : Finset (ZMod (3 ^ (u + v))))
    (project (Nat.le_add_left v u)) f
  change (∑ y, ∑ x ∈ fiber (Nat.le_add_left v u) y, f x) = ∑ x, f x at hs
  simp only [mean, sum_fiberLift, ← Finset.sum_div, hs, div_div, pow_add]

/-- The two finite full-group averages commute. -/
theorem mean_comm (u v : ℕ) (f : ZMod (3 ^ u) → ZMod (3 ^ v) → ℝ) :
    mean u (fun x => mean v (f x)) = mean v (fun y => mean u (fun x => f x y)) := by
  simp only [mean, ← Finset.sum_div, div_div]
  rw [Finset.sum_comm]
  ring

/-- Any summable index family may be interchanged with the finite full-group average. -/
theorem mean_tsum_index {ι : Type*} (n : ℕ) (f : ι → ZMod (3 ^ n) → ℝ)
    (hf : ∀ x, Summable (fun i => f i x)) :
    mean n (fun x => ∑' i, f i x) = ∑' i, mean n (f i) := by
  have hs := Summable.tsum_finsetSum (s := Finset.univ) (fun x _ => hf x)
  simp only [mean, ← hs, tsum_div_const]

end WordCertDensity.Reference
