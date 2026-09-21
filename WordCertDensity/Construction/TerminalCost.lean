/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalBarrier
import WordCertDensity.Construction.TerminalRadius

/-! # Ordinary cost of the actual terminal words -/

namespace WordCertDensity.Construction

/-- The exact radius cancels the ceiling contribution in the terminal cost. -/
theorem terminalWord_cost {b u : ℕ} {w : ValuationWord}
    (hb : 200 ≤ b) (hu : u ≤ 2*terminalRadius b)
    (hw : TerminalWord b u (terminalPrecision b) w) :
    (w.ordinaryCost : ℝ) ≤ (24/5 : ℝ)*b := by
  have hbar := terminalBarrier_mono b u hw.2.1
  have he := (terminalBarrier_endpoints hb u).2
  have hov := hw.2.2.2.2
  have hr := terminalRadius_balance hb
  have hd := hw.2.1
  have hwid := (terminalWidth_bounds b).1
  have hc : 5*w.ordinaryCost ≤ 24*b := by
    unfold ValuationWord.ordinaryCost terminalHigh at *
    omega
  have hcR : (5 : ℝ)*w.ordinaryCost ≤ 24*(b : ℝ) := by exact_mod_cast hc
  linarith

/-- Overshoot at most one lies within the original precision cap. -/
theorem terminalWord_reduced_cost {b u : ℕ} {w : ValuationWord}
    (hb : 200 ≤ b) (hu : u ≤ 2*terminalRadius b) (hw : TerminalWord b u 1 w) :
    (w.ordinaryCost : ℝ) ≤ (24/5 : ℝ)*b := by
  have he : 1 ≤ terminalPrecision b := by unfold terminalPrecision; omega
  have hm := terminalWords_mono_cap b u he ((mem_terminalWords b u 1 w).mpr hw)
  exact terminalWord_cost hb hu ((mem_terminalWords b u (terminalPrecision b) w).mp hm)

/-- The retained coefficient pays the reduced word at the actual floored size. -/
theorem terminalWord_parametric_cost {θ : ℝ} (hθ : 0 ≤ θ) {B u : ℕ} {w : ValuationWord}
    (hb : 200 ≤ ⌊θ*B⌋₊) (hu : u ≤ 2*terminalRadius ⌊θ*B⌋₊)
    (hw : TerminalWord ⌊θ*B⌋₊ u 1 w) :
    (w.ordinaryCost : ℝ) ≤ (481/100 : ℝ)*θ*B := by
  have hc := terminalWord_reduced_cost hb hu hw
  have hf : (⌊θ*B⌋₊ : ℝ) ≤ θ*B := Nat.floor_le (by positivity)
  have hn : 0 ≤ θ*(B : ℝ) := mul_nonneg hθ (Nat.cast_nonneg _)
  nlinarith

end WordCertDensity.Construction
