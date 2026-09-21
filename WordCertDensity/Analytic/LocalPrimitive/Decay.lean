/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.ForwardExpectation
public import WordCertDensity.Analytic.LocalPrimitive.LayerData

/-! # Self-contained local primitive Fourier decay

This module composes the original-law Fourier-to-phase bridge with the finite
layer estimate and the explicit Appendix-E parameter recipe.
-/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- The local coefficient has the real form used by the decay estimate. -/
theorem localPrimitiveCoefficient_cast (B : ℕ) :
    (localPrimitiveCoefficient B : ℝ) =
      (3 * (localPrimitiveM B : ℝ)) ^ B := by
  simp [localPrimitiveCoefficient]

/-- Every positive order has an explicit local primitive Fourier-decay bound. -/
theorem localPrimitiveDecay (B n : ℕ) (hB : 0 < B) (hn : 1 ≤ n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) :
    ‖Reference.fourierMass n ξ‖ ≤
      (localPrimitiveCoefficient B : ℝ) / (n : ℝ) ^ B := by
  by_cases hn1 : n = 1
  · subst n
    have hnorm := norm_fourierMass_le_one 1 ξ
    have hcoeff : (1 : ℝ) ≤ localPrimitiveCoefficient B := by
      exact_mod_cast one_le_localPrimitiveCoefficient B
    simpa using hnorm.trans hcoeff
  · have hn2 : 2 ≤ n := by omega
    have hmpos : 0 < n / 2 := by omega
    have hmone : (1 : ℝ) ≤ (n / 2 : ℕ) := by exact_mod_cast hmpos
    have hbridge : ‖Reference.fourierMass n ξ‖ ≤
        phaseRemainingPotential n ξ (n / 2) (n / 2) 0 := by
      simpa [phaseRemainingPotential] using norm_fourierMass_le_phasePairPotential n ξ
    have hlayer := phaseRemainingPotential_layer_le_phasePeriod
      (B := B) (M := localPrimitiveM B) ξ (by omega) hξ hB le_rfl 0
    have hraw : ‖Reference.fourierMass n ξ‖ ≤
        (localPrimitiveM B : ℝ) ^ B / (n / 2 : ℕ) ^ B := by
      refine hbridge.trans ?_
      simpa [layerWeight, max_eq_left hmone] using hlayer
    refine hraw.trans ?_
    rw [localPrimitiveCoefficient_cast]
    have hnle : (n : ℝ) ≤ 3 * (n / 2 : ℕ) := by exact_mod_cast (show n ≤ 3 * (n / 2) by omega)
    have hpow : (n : ℝ) ^ B ≤ (3 * (n / 2 : ℕ) : ℝ) ^ B := by
      exact (pow_le_pow_left₀ (by positivity) hnle) B
    apply (div_le_div_iff₀ (by positivity : 0 < ((n / 2 : ℕ) : ℝ) ^ B)
      (by positivity : 0 < (n : ℝ) ^ B)).mpr
    calc
      (localPrimitiveM B : ℝ) ^ B * (n : ℝ) ^ B ≤
          (localPrimitiveM B : ℝ) ^ B * (3 * (n / 2 : ℕ) : ℝ) ^ B := by
            exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (3 * (localPrimitiveM B : ℝ)) ^ B * (n / 2 : ℕ) ^ B := by ring

/-- The manuscript's required order is supplied by the local coefficient. -/
theorem localPrimitiveDecay_order6409 (n : ℕ) (hn : 1 ≤ n)
    (ξ : ZMod (3 ^ n)) (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) :
    ‖Reference.fourierMass n ξ‖ ≤
      (localPrimitiveCoefficient 6409 : ℝ) / (n : ℝ) ^ 6409 :=
  localPrimitiveDecay 6409 n (by norm_num) hn ξ hξ

/-- The specialized coefficient is positive for downstream mixing bounds. -/
theorem one_le_localPrimitiveCoefficient_order6409 :
    1 ≤ localPrimitiveCoefficient 6409 :=
  one_le_localPrimitiveCoefficient 6409

end WordCertDensity.LocalPrimitive
