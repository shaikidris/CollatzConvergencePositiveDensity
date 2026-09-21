/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.Projectivity

/-! # Original iid coefficients of the conditional affine mixture -/

@[expose] public section

namespace WordCertDensity.Reference

open scoped Classical

/-- Reversal is performed only in the iid law; the inverse-prefix reference law is unchanged. -/
theorem law_reverse (n : ℕ) :
    (wordPMF n).map (fun w => ValuationWord.residueOffset n w.reverse) = law n := by
  change (wordPMF n).map (ValuationWord.residueOffset n ∘ List.reverse) = _
  rw [← PMF.map_comp, wordPMF_map_reverse]
  rfl

/-- Each reference atom is the exact sum over its reversed-word fiber. -/
theorem law_reverse_atom (v : ℕ) (y : ZMod (3 ^ v)) :
    law v y = ∑' w : ValuationWord,
      if ValuationWord.residueOffset v w.reverse = y then wordPMF v w else 0 := by
  rw [← law_reverse, PMF.map_apply]
  apply tsum_congr
  intro w
  by_cases h : ValuationWord.residueOffset v w.reverse = y
  · simp [h]
  · simp [h, Ne.symm h]

/-- The original geometric word probability, multiplied by the ternary fiber scale. -/
noncomputable def mixtureCoefficient (v : ℕ) (y : ZMod (3 ^ v)) (w : ValuationWord) : ℝ :=
  if ValuationWord.residueOffset v w.reverse = y then
    (3 : ℝ) ^ v * (wordPMF v w).toReal else 0

/-- Every coefficient of the countable affine mixture is nonnegative. -/
theorem mixtureCoefficient_nonneg (v : ℕ) (y : ZMod (3 ^ v)) (w : ValuationWord) :
    0 ≤ mixtureCoefficient v y w := by
  unfold mixtureCoefficient
  split_ifs <;> positivity

/-- The full coefficient series has sum equal to the actual coarse reference density. -/
theorem mixtureCoefficient_hasSum (v : ℕ) (y : ZMod (3 ^ v)) :
    HasSum (mixtureCoefficient v y) (density v y) := by
  have hfinite : (∑' w : ValuationWord,
      if ValuationWord.residueOffset v w.reverse = y then wordPMF v w else 0) ≠ ⊤ := by
    rw [← law_reverse_atom]
    exact PMF.apply_ne_top _ _
  have h := (ENNReal.hasSum_toReal hfinite).mul_left ((3 : ℝ) ^ v)
  have hterm (w : ValuationWord) :
      (if ValuationWord.residueOffset v w.reverse = y then wordPMF v w else 0) ≠ ⊤ := by
    split_ifs <;> simp [PMF.apply_ne_top]
  rw [← ENNReal.tsum_toReal_eq hterm, ← law_reverse_atom] at h
  apply h.congr_fun
  intro w
  simp only [mixtureCoefficient]
  split_ifs <;> simp

/-- The coefficients are summable, including zero-density fibers and level zero. -/
theorem mixtureCoefficient_summable (v : ℕ) (y : ZMod (3 ^ v)) :
    Summable (mixtureCoefficient v y) := (mixtureCoefficient_hasSum v y).summable

/-- The exact coefficient normalization used before countable Jensen. -/
theorem mixtureCoefficient_sum (v : ℕ) (y : ZMod (3 ^ v)) :
    (∑' w, mixtureCoefficient v y w) = density v y :=
  (mixtureCoefficient_hasSum v y).tsum_eq

/-- A zero-density coarse fiber has no positive mixture coefficient. -/
theorem mixtureCoefficient_eq_zero {v : ℕ} {y : ZMod (3 ^ v)}
    (hy : density v y = 0) (w : ValuationWord) : mixtureCoefficient v y w = 0 := by
  apply le_antisymm ?_ (mixtureCoefficient_nonneg v y w)
  have h := (mixtureCoefficient_summable v y).le_tsum w
    (fun z _ => mixtureCoefficient_nonneg v y z)
  simpa only [mixtureCoefficient_sum, hy] using h

/-- At the empty block the only coefficient is the empty word's unit mass. -/
theorem mixtureCoefficient_zero (y : ZMod (3 ^ 0)) (w : ValuationWord) :
    mixtureCoefficient 0 y w = if w = [] then 1 else 0 := by
  let : Subsingleton (ZMod (3 ^ 0)) := ZMod.subsingleton_iff.mpr (by decide)
  have hy : y = 0 := Subsingleton.elim _ _
  subst y
  by_cases hw : w = [] <;>
    simp [mixtureCoefficient, ValuationWord.residueOffset_zero_level, wordPMF_zero,
      PMF.pure_apply, hw]

end WordCertDensity.Reference
