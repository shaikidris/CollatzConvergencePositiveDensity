/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Reference.Law
public import Mathlib.Analysis.Fourier.ZMod

/-!
# The reference probability-mass Fourier transform

The positive-character sum has no uniform-group normalization factor.
Mathlib's negative-character DFT gives the same sum at the opposite frequency.
-/

@[expose] public section

namespace WordCertDensity

namespace Reference

/-- The unnormalized positive-character Fourier transform of reference probability mass. -/
noncomputable def fourierMass (n : ℕ) (ξ : ZMod (3 ^ n)) : ℂ :=
  ∑ x, (mass n x : ℂ) * ZMod.stdAddChar (ξ * x)

/-- Negating the DFT frequency gives exactly the manuscript's positive Fourier sign. -/
theorem fourierMass_eq_dft_neg (n : ℕ) (ξ : ZMod (3 ^ n)) :
    fourierMass n ξ = ZMod.dft (fun x => (mass n x : ℂ)) (-ξ) := by
  rw [fourierMass, ZMod.dft_apply]
  simp only [mul_neg, neg_neg, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_comm ξ x, mul_comm]

/-- The zero frequency has value one, calibrating probability-mass normalization. -/
theorem fourierMass_zero (n : ℕ) : fourierMass n 0 = 1 := by
  simpa [fourierMass] using congrArg (fun x : ℝ => (x : ℂ)) (mass_sum n)

/-- The one-point reference group has Fourier mass one at its only frequency. -/
theorem fourierMass_zero_level (ξ : ZMod (3 ^ 0)) : fourierMass 0 ξ = 1 := by
  let : Subsingleton (ZMod (3 ^ 0)) := ZMod.subsingleton_iff.mpr (by decide)
  have hξ : ξ = 0 := Subsingleton.elim _ _
  rw [hξ, fourierMass_zero]

end Reference

end WordCertDensity
