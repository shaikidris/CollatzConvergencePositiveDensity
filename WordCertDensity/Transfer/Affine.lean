/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik

The short finite-pushforward proofs are adapted from Lech Mazur,
Copyright 2026 Lech Mazur, under Apache License 2.0. The source LICENSE and
NOTICE are retained at research/sources/mazur_830b9d3f38f2/.
The operator uses the local word map and full-group normalization.
-/
module

public import WordCertDensity.Transfer.AffineMap
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact affine word transfer

The operator is defined by a finite pushforward, with one fixed classical
indicator convention. Injection gives its value on the image and its exact
absolute-value identity. Full-group normalization pays the geometric word
probability, not the ternary fiber size.
-/

@[expose] public section

namespace WordCertDensity

namespace Transfer

private noncomputable def finitePush {α β : Type*} [Fintype α]
    (f : α → β) (g : α → ℝ) (y : β) : ℝ :=
  ∑ z, @ite ℝ (f z = y) (Classical.propDecidable _) (g z) 0

private theorem finitePush_image {α β : Type*} [Fintype α]
    (f : α → β) (hf : Function.Injective f) (g : α → ℝ) (z : α) :
    finitePush f g (f z) = g z := by
  classical
  simp [finitePush, hf.eq_iff]

private theorem finitePush_off_image {α β : Type*} [Fintype α]
    (f : α → β) (g : α → ℝ) (y : β) (hy : y ∉ Set.range f) :
    finitePush f g y = 0 := by
  have hn (z : α) : f z ≠ y := fun h => hy ⟨z, h⟩
  simp [finitePush, hn]

private theorem finitePush_abs {α β : Type*} [Fintype α]
    (f : α → β) (hf : Function.Injective f) (g : α → ℝ) (y : β) :
    |finitePush f g y| = finitePush f (fun z => |g z|) y := by
  by_cases hy : y ∈ Set.range f
  · obtain ⟨z, rfl⟩ := hy
    rw [finitePush_image f hf, finitePush_image f hf]
  · rw [finitePush_off_image f g y hy, finitePush_off_image f _ y hy, abs_zero]

private theorem finitePush_sum {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β) (g : α → ℝ) : (∑ y, finitePush f g y) = ∑ z, g z := by
  classical
  simp only [finitePush]
  rw [Finset.sum_comm]
  simp

private theorem finitePush_add {α β : Type*} [Fintype α]
    (f : α → β) (g h : α → ℝ) (y : β) :
    finitePush f (fun z => g z + h z) y = finitePush f g y + finitePush f h y := by
  simp only [finitePush, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> simp

private theorem finitePush_sub {α β : Type*} [Fintype α]
    (f : α → β) (g h : α → ℝ) (y : β) :
    finitePush f (fun z => g z - h z) y = finitePush f g y - finitePush f h y := by
  simp only [finitePush, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> simp

private theorem finitePush_mul {α β : Type*} [Fintype α]
    (f : α → β) (c : ℝ) (g : α → ℝ) (y : β) :
    finitePush f (fun z => c * g z) y = c * finitePush f g y := by
  simp only [finitePush, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> simp

private theorem finitePush_nonneg {α β : Type*} [Fintype α]
    (f : α → β) (g : α → ℝ) (hg : ∀ z, 0 ≤ g z) (y : β) :
    0 ≤ finitePush f g y := by
  apply Finset.sum_nonneg
  intro z _
  split_ifs
  · exact hg z
  · exact le_refl 0

/-- The word coefficient times the finite affine pushforward. -/
noncomputable def wordOperator (w : ValuationWord) (q : ℕ)
    (g : ZMod (3 ^ (q - w.length)) → ℝ) (y : ZMod (3 ^ q)) : ℝ :=
  weight w * ∑ z, @ite ℝ (wordMap w q z = y) (Classical.propDecidable _) (g z) 0

private theorem wordOperator_eq_finitePush (w : ValuationWord) (q : ℕ)
    (g : ZMod (3 ^ (q - w.length)) → ℝ) (y : ZMod (3 ^ q)) :
    wordOperator w q g y = weight w * finitePush (wordMap w q) g y := rfl

/-- The operator has the stated coefficient and the unique value on its image. -/
theorem wordOperator_image (w : ValuationWord) {q : ℕ} (hq : w.length ≤ q)
    (g : ZMod (3 ^ (q - w.length)) → ℝ) (z : ZMod (3 ^ (q - w.length))) :
    wordOperator w q g (wordMap w q z) = weight w * g z := by
  rw [wordOperator_eq_finitePush, finitePush_image _ (wordMap_injective w hq)]

/-- A residue outside the affine image receives zero transferred value. -/
theorem wordOperator_off_image (w : ValuationWord) (q : ℕ)
    (g : ZMod (3 ^ (q - w.length)) → ℝ) (y : ZMod (3 ^ q))
    (hy : y ∉ Set.range (wordMap w q)) : wordOperator w q g y = 0 := by
  rw [wordOperator_eq_finitePush, finitePush_off_image _ _ _ hy, mul_zero]

/-- Affine transfer preserves addition of functions. -/
theorem wordOperator_add (w : ValuationWord) (q : ℕ)
    (g h : ZMod (3 ^ (q - w.length)) → ℝ) (y : ZMod (3 ^ q)) :
    wordOperator w q (fun z => g z + h z) y =
      wordOperator w q g y + wordOperator w q h y := by
  simp only [wordOperator_eq_finitePush, finitePush_add, mul_add]

/-- Affine transfer preserves subtraction of functions. -/
theorem wordOperator_sub (w : ValuationWord) (q : ℕ)
    (g h : ZMod (3 ^ (q - w.length)) → ℝ) (y : ZMod (3 ^ q)) :
    wordOperator w q (fun z => g z - h z) y =
      wordOperator w q g y - wordOperator w q h y := by
  simp only [wordOperator_eq_finitePush, finitePush_sub, mul_sub]

/-- Every real scalar commutes with affine transfer. -/
theorem wordOperator_mul (w : ValuationWord) (q : ℕ) (c : ℝ)
    (g : ZMod (3 ^ (q - w.length)) → ℝ) (y : ZMod (3 ^ q)) :
    wordOperator w q (fun z => c * g z) y = c * wordOperator w q g y := by
  simp only [wordOperator_eq_finitePush, finitePush_mul]
  ring

/-- Nonnegative functions remain nonnegative under affine transfer. -/
theorem wordOperator_nonneg (w : ValuationWord) (q : ℕ)
    (g : ZMod (3 ^ (q - w.length)) → ℝ) (hg : ∀ z, 0 ≤ g z) (y : ZMod (3 ^ q)) :
    0 ≤ wordOperator w q g y :=
  mul_nonneg (weight_pos w).le (finitePush_nonneg _ g hg y)

/-- Injection makes absolute values commute with the positive word transfer. -/
theorem wordOperator_abs (w : ValuationWord) {q : ℕ} (hq : w.length ≤ q)
    (g : ZMod (3 ^ (q - w.length)) → ℝ) (y : ZMod (3 ^ q)) :
    |wordOperator w q g y| = wordOperator w q (fun z => |g z|) y := by
  simp only [wordOperator_eq_finitePush, abs_mul, abs_of_pos (weight_pos w),
    finitePush_abs _ (wordMap_injective w hq)]

/-- The unnormalized transfer sum pays exactly the word coefficient. -/
theorem wordOperator_sum (w : ValuationWord) (q : ℕ)
    (g : ZMod (3 ^ (q - w.length)) → ℝ) :
    (∑ y, wordOperator w q g y) = weight w * ∑ z, g z := by
  simp only [wordOperator_eq_finitePush, ← Finset.mul_sum, finitePush_sum]

/-- The full-group mean pays the exact geometric word probability. -/
theorem mean_wordOperator (w : ValuationWord) {q : ℕ} (hq : w.length ≤ q)
    (g : ZMod (3 ^ (q - w.length)) → ℝ) :
    Reference.mean q (wordOperator w q g) =
      (1 / (2 : ℝ) ^ w.total) * Reference.mean (q - w.length) g := by
  simp only [Reference.mean, wordOperator_sum, weight_eq]
  rw [Reference.scale_eq hq]
  field_simp

/-- The exact unhalved full-group L1 norm pays the same geometric word probability. -/
theorem mean_abs_wordOperator (w : ValuationWord) {q : ℕ} (hq : w.length ≤ q)
    (g : ZMod (3 ^ (q - w.length)) → ℝ) :
    Reference.mean q (fun y => |wordOperator w q g y|) =
      (1 / (2 : ℝ) ^ w.total) * Reference.mean (q - w.length) (fun z => |g z|) := by
  simp_rw [wordOperator_abs w hq]
  exact mean_wordOperator w hq _

/-- The empty word acts identically, including on the one-point group. -/
theorem wordOperator_nil (q : ℕ) (g : ZMod (3 ^ q) → ℝ) (y : ZMod (3 ^ q)) :
    wordOperator [] q g y = g y := by
  have h := wordOperator_image [] (show 0 ≤ q by omega) g y
  simpa only [wordMap_nil, weight_nil, one_mul] using h

end Transfer

end WordCertDensity
