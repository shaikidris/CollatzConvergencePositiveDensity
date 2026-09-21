/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.BlockFibers
public import WordCertDensity.Reference.TransferRecurrence

/-! # The exact conditional affine mixture for moment inheritance -/

@[expose] public section

namespace WordCertDensity.Reference

open scoped Classical

/-- On its actual length support the block map is exactly inverse-offset concatenation. -/
theorem blockMap_offset (u v : ℕ) (w t : ValuationWord) (hw : w.length = v) :
    ValuationWord.residueOffset (u + v) (w.reverse ++ t) =
      blockMap u v w (ValuationWord.residueOffset u t) := by
  rw [← ValuationWord.project_residueOffset (Nat.le_add_right u v) t, blockMap_project]
  simp only [ValuationWord.residueOffset_append, List.length_reverse, hw,
    ValuationWord.total_reverse]

/-- The actual longer reference law is the original countable mixture of affine shorter laws. -/
theorem law_blocks (u v : ℕ) :
    law (u + v) = (wordPMF v).bind (fun w => (law u).map (blockMap u v w)) := by
  rw [law, wordPMF_reverse_prefix, PMF.map_bind]
  apply PMF.ext
  intro y
  rw [PMF.bind_apply, PMF.bind_apply]
  apply tsum_congr
  intro w
  by_cases hw : w.length = v
  · have hm : ((wordPMF u).map (fun t => w.reverse ++ t)).map
        (ValuationWord.residueOffset (u + v)) = (law u).map (blockMap u v w) := by
      rw [law, PMF.map_comp, PMF.map_comp]
      congr 1
      funext t
      exact blockMap_offset u v w t hw
    rw [hm]
  · simp [wordPMF_eq_zero_of_length_ne v w hw]

/-- Every real atom retains the original unnormalized independent block probabilities. -/
theorem mass_blocks (u v : ℕ) (y : ZMod (3 ^ (u + v))) :
    mass (u + v) y = ∑' w : ValuationWord, (wordPMF v w).toReal *
      (((law u).map (blockMap u v w)) y).toReal := by
  rw [mass, law_blocks, PMF.bind_apply, ENNReal.tsum_toReal_eq]
  · simp only [ENNReal.toReal_mul]
  · intro w
    exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)


/-- A chosen fiber origin, with a harmless zero default on incompatible words. -/
noncomputable def mixtureShift (u v : ℕ) (y : ZMod (3 ^ v)) (w : ValuationWord) :
    ZMod (3 ^ u) :=
  if h : ∃ r : ZMod (3 ^ u), blockMap u v w r = (y.val : ZMod (3 ^ (u + v))) then
    Classical.choose h else 0

/-- The inverse affine multiplier is the original binary word power. -/
def mixtureMultiplier (u : ℕ) (w : ValuationWord) : ZMod (3 ^ u) := 2 ^ w.total

/-- Every inverse multiplier is a ternary unit, even at level zero. -/
theorem mixtureMultiplier_isUnit (u : ℕ) (w : ValuationWord) :
    IsUnit (mixtureMultiplier u w) := by
  dsimp [mixtureMultiplier]
  rw [← twoUnit_val u]
  exact (twoUnit u).isUnit.pow _

/-- Compatibility guarantees that the selected origin maps to the canonical low lift. -/
theorem blockMap_mixtureShift (u v : ℕ) (y : ZMod (3 ^ v)) (w : ValuationWord)
    (hw : ValuationWord.residueOffset v w.reverse = y) :
    blockMap u v w (mixtureShift u v y w) = (y.val : ZMod (3 ^ (u + v))) := by
  have he := exists_blockOrigin u v y w hw
  rw [mixtureShift, dif_pos he]
  exact Classical.choose_spec he

/-- The selected shift and unit multiplier invert the block on every point of its fiber. -/
theorem blockMap_mixtureAffine (u v : ℕ) (y : ZMod (3 ^ v)) (w : ValuationWord)
    (hw : ValuationWord.residueOffset v w.reverse = y) (z : ZMod (3 ^ u)) :
    blockMap u v w (mixtureShift u v y w + mixtureMultiplier u w * z) =
      fiberLift u v y z := by
  rw [mixtureMultiplier, blockMap_translate, blockMap_mixtureShift u v y w hw]
  rfl

/-- Each conditional affine map permutes the full shorter ternary group. -/
theorem mixtureAffine_bijective (u v : ℕ) (y : ZMod (3 ^ v)) (w : ValuationWord) :
    Function.Bijective (fun z : ZMod (3 ^ u) =>
      mixtureShift u v y w + mixtureMultiplier u w * z) := by
  have hc : inverseTwoPow u w.total * mixtureMultiplier u w = 1 := by
    rw [mixtureMultiplier, mul_comm, two_pow_mul_inverseTwoPow]
  have hi : Function.Injective (fun z : ZMod (3 ^ u) =>
      mixtureShift u v y w + mixtureMultiplier u w * z) := by
    intro x z he
    have h := congrArg (fun t => inverseTwoPow u w.total * t) (add_left_cancel he)
    simpa only [← mul_assoc, hc, one_mul] using h
  exact ⟨hi, Finite.surjective_of_injective hi⟩

/-- Conditional affine pullback preserves full-group averages. -/
theorem mean_mixtureAffine (u v : ℕ) (y : ZMod (3 ^ v)) (w : ValuationWord)
    (f : ZMod (3 ^ u) → ℝ) :
    mean u (fun z => f (mixtureShift u v y w + mixtureMultiplier u w * z)) = mean u f := by
  rw [mean, (mixtureAffine_bijective u v y w).sum_comp f]
  rfl

/-- The actual mapped atom is its unique compatible input atom, and vanishes off that fiber. -/
theorem block_map_mass (u v : ℕ) (y : ZMod (3 ^ v)) (w : ValuationWord)
    (z : ZMod (3 ^ u)) :
    (((law u).map (blockMap u v w)) (fiberLift u v y z)).toReal =
      if ValuationWord.residueOffset v w.reverse = y then
        mass u (mixtureShift u v y w + mixtureMultiplier u w * z) else 0 := by
  by_cases hw : ValuationWord.residueOffset v w.reverse = y
  · rw [if_pos hw]
    conv_lhs => rw [← blockMap_mixtureAffine u v y w hw z]
    simp only [PMF.map_apply, (blockMap_injective u v w).eq_iff, mass]
    rw [tsum_eq_single (mixtureShift u v y w + mixtureMultiplier u w * z)]
    · simp
    · intro x hx
      simp [Ne.symm hx]
  · rw [if_neg hw]
    have hne (x : ZMod (3 ^ u)) : fiberLift u v y z ≠ blockMap u v w x := by
      intro h
      have hp := congrArg (project (Nat.le_add_left v u)) h
      rw [project_fiberLift, project_blockMap] at hp
      exact hw hp.symm
    simp [PMF.map_apply, hne]

/-- Exact reference density on a fiber is the original countable affine mixture. -/
theorem affine_mixture (u v : ℕ) (y : ZMod (3 ^ v)) (z : ZMod (3 ^ u)) :
    density (u + v) (fiberLift u v y z) = ∑' w : ValuationWord,
      mixtureCoefficient v y w * density u (mixtureShift u v y w + mixtureMultiplier u w * z) := by
  rw [density, mass_blocks, ← tsum_mul_left]
  apply tsum_congr
  intro w
  rw [block_map_mass]
  by_cases hw : ValuationWord.residueOffset v w.reverse = y
  · simp only [mixtureCoefficient, if_pos hw, density, pow_add]
    ring
  · simp [mixtureCoefficient, hw]

/-- The complete conditional-mixture contract retains original coefficients and unit permutations. -/
theorem conditionalAffineMixture (u v : ℕ) (y : ZMod (3 ^ v)) :
    (∑' w : ValuationWord, mixtureCoefficient v y w) = density v y ∧
    ∃ shift multiplier : ValuationWord → ZMod (3 ^ u),
      (∀ w, IsUnit (multiplier w)) ∧
      ∀ z : ZMod (3 ^ u), density (u + v)
          ((y.val : ZMod (3 ^ (u + v))) + 3 ^ v * z.val) =
        ∑' w : ValuationWord, mixtureCoefficient v y w * density u (shift w + multiplier w * z) :=
  ⟨mixtureCoefficient_sum v y, mixtureShift u v y, mixtureMultiplier u,
    mixtureMultiplier_isUnit u, affine_mixture u v y⟩

/-- A vanishing lower density makes the entire actual upper fiber vanish. -/
theorem affine_mixture_zero_fiber (u v : ℕ) (y : ZMod (3 ^ v))
    (hy : density v y = 0) (z : ZMod (3 ^ u)) : density (u + v) (fiberLift u v y z) = 0 := by
  rw [affine_mixture]
  simp only [mixtureCoefficient_eq_zero hy, zero_mul, tsum_zero]

end WordCertDensity.Reference
