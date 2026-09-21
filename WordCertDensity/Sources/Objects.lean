/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Targets
import WordCertDensity.Reference.Fan

/-! # Literal finite and all-scale physical source contracts -/

namespace WordCertDensity.Sources
open Filter
open scoped Topology

/-- A finite actual weighted odd source family at a real cutoff. -/
def SourceAt (target : ℕ) (c X R : ℝ) (S : Finset ℕ) (a : ℕ → ℝ) : Prop :=
  ∀ x ∈ S, Odd x ∧ x ∈ goodTarget target c ∧ X ≤ (x : ℝ) ∧
    (x : ℝ)<R*X ∧ 0 ≤ a x ∧ a x ≤ (x : ℝ)⁻¹

/-- One score precedes every fixed larger clock and every requested tolerance. -/
def AllScaleSources (target : ℕ) (W : ℝ) : Prop :=
  ∀ c : ℝ, criticalClock < c → ∀ ε : ℝ, 0 < ε → ∀ Λ : ℝ, 16 < Λ →
    ∃ (S : ℝ → Finset ℕ) (a : ℝ → ℕ → ℝ) (k : ℝ → ℕ) (R : ℝ → ℝ),
      Tendsto R atTop (𝓝 16) ∧ Tendsto k atTop atTop ∧
      Tendsto (fun X => (3 : ℝ)^k X/X) atTop (𝓝 0) ∧
      ∀ᶠ X in atTop, SourceAt target c X (R X) (S X) (a X) ∧ R X < Λ ∧
        W-ε ≤ ∑ x ∈ S X, a X x*Reference.fan (k X) (x : ZMod (3^k X))

end WordCertDensity.Sources
