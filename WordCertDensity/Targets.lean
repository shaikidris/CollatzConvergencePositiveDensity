/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Density.Basic
public import WordCertDensity.Dynamics.Ordinary

/-!
# Literal headline propositions

These definitions freeze targets. No term proving either target is supplied
by this module. Quantitative recipe definitions will be introduced with their
implementations, not replaced by an unspecified existential constant.
-/

@[expose] public section

namespace WordCertDensity

/-- The reference-model threshold in the ordinary-step convention. -/
noncomputable def criticalClock : ℝ := 3 / Real.log (4 / 3)

/-- One lower-density constant chosen before every strictly larger clock. -/
def CommonClockDensity : Prop :=
  ∃ d : ℝ, 0 < d ∧ ∀ c : ℝ, criticalClock < c → d ≤ lowerNaturalDensity (good c)

/-- The universal clock statement for a specified density constant. -/
def EveryClockDensityBound (d : ℝ) : Prop :=
  0 < d ∧ ∀ c : ℝ, criticalClock < c → d ≤ lowerNaturalDensity (good c)

/-- A specified common bound implies the corresponding existence proposition. -/
theorem EveryClockDensityBound.common {d : ℝ} (h : EveryClockDensityBound d) :
    CommonClockDensity := ⟨d, h⟩

end WordCertDensity
