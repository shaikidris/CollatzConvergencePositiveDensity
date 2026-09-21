/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Analytic.LocalPrimitive.Decay

/-!
# Canonical primitive decay for the actual reference law

This adapter exposes the locally proved primitive-decay theorem through the
stable names consumed by the mixing and construction modules.
-/

namespace WordCertDensity

namespace Analytic

/-- The canonical natural primitive coefficient at the required order. -/
noncomputable def primitiveCoefficient : ℕ :=
  LocalPrimitive.localPrimitiveCoefficient 6409

/-- The adapter uses exactly the locally proved coefficient, without enlargement. -/
theorem primitiveCoefficient_eq :
    primitiveCoefficient = LocalPrimitive.localPrimitiveCoefficient 6409 := rfl

/-- The canonical coefficient is at least one, as required by the mixing conversion. -/
theorem one_le_primitiveCoefficient : 1 ≤ primitiveCoefficient :=
  LocalPrimitive.one_le_localPrimitiveCoefficient_order6409

/-- Primitive reference Fourier decay with the literal canonical coefficient and order 6409. -/
theorem primitiveDecay (n : ℕ) (hn : 1 ≤ n) (ξ : ZMod (3 ^ n))
    (hξ : ¬ (3 : ZMod (3 ^ n)) ∣ ξ) :
    ‖Reference.fourierMass n ξ‖ ≤ (primitiveCoefficient : ℝ) / (n : ℝ) ^ 6409 :=
  LocalPrimitive.localPrimitiveDecay_order6409 n hn ξ hξ

end Analytic

end WordCertDensity
