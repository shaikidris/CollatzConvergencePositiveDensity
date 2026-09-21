/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalCrossing

/-! # Terminal deficit with its exact remaining overshoot event

The two endpoint failures are already bounded. The only remaining loss is
the original probability of a genuine eligible crossing exceeding the cap.
-/

namespace WordCertDensity.Construction

/-- A crossing exists, but its first eligible word exceeds the specified cap. -/
def TerminalOvershoot (b u K : ℕ) (w : ValuationWord) : Prop :=
  TerminalCrossing b u w ∧ ¬ Reference.prefixFamilyEvent (terminalWords b u K) w

/-- The literal finite-family deficit is bounded by the paid endpoints and actual cap loss. -/
theorem terminalMass_deficit_le_overshoot {b u K n : ℕ} (hb : 200 ≤ b)
    (hu : u ≤ 2 * terminalRadius b) (hn : terminalHigh b ≤ n) :
    1 - terminalMass b u K ≤ 2 * Real.exp (-(b : ℝ) / 64000) +
      Gated.probability (Reference.wordPMF n) (TerminalOvershoot b u K) := by
  have hm := Gated.probability_mono_on_support (Reference.wordPMF n)
    (fun w => ¬ Reference.prefixFamilyEvent (terminalWords b u K) w)
    (fun w => ¬ TerminalCrossing b u w ∨ TerminalOvershoot b u K w)
    (fun w _ hw => by
      by_cases hc : TerminalCrossing b u w
      · exact Or.inr ⟨hc, hw⟩
      · exact Or.inl hc)
  rw [Reference.prefixFamily_compl_probability _
    (fun w hw => (terminalWords_depth hw).trans hn) (terminalWords_prefixFree b u K)] at hm
  have hs := Gated.probability_or_le (Reference.wordPMF n)
    (fun w => ¬ TerminalCrossing b u w) (TerminalOvershoot b u K)
  have ht := terminalCrossing_failure_probability hb hu hn
  change 1 - terminalMass b u K ≤ _ at hm
  linarith

end WordCertDensity.Construction
