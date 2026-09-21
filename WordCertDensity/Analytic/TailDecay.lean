/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Analytic.TailConductor
import WordCertDensity.Analytic.Primitive

/-!
# Canonical decay for the actual unrestricted affine tail

The audited numerical primitive proof discharges the only analytic premise
of the intrinsic conductor theorem. Its coefficient is multiplied by exactly
20^6409, as in the manuscript; no mixing or density conclusion is assumed.
-/

namespace WordCertDensity
namespace Analytic

/-- The manuscript's tail coefficient D, with the primitive coefficient unchanged. -/
noncomputable def tailCoefficient : ℝ := (primitiveCoefficient : ℝ) * (20 : ℝ) ^ 6409

/-- The tail coefficient is positive. -/
theorem tailCoefficient_pos : 0 < tailCoefficient := by
  have h : (0 : ℝ) < (primitiveCoefficient : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one one_le_primitiveCoefficient)
  exact mul_pos h (pow_pos (by norm_num) _)

/-- The actual tail has order-6409 decay at every discarded frequency under the head guards. -/
theorem affineTailDecay {m k T l : ℕ} (hhead : k + 1 ≤ m)
    (hm : 9 * (T + (k + 1)) ≤ 10 * m) (hk : 20 * k ≤ 17 * (T + (k + 1)))
    {ξ : ZMod (3 ^ (T + (k + 1)))}
    (hξ : ¬ (3 : ZMod (3 ^ (T + (k + 1)))) ^ (T + (k + 1) - m) ∣ ξ) :
    ‖∑ x, (AffineTail.mass (k + 1) T l x : ℂ) * ZMod.stdAddChar (ξ * x)‖ ≤
      tailCoefficient / ((T + (k + 1) : ℕ) : ℝ) ^ 6409 := by
  exact AffineTail.fourier_mass_le (Nat.cast_nonneg primitiveCoefficient)
    primitiveDecay hhead hm hk hξ

end Analytic
end WordCertDensity
