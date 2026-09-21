/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalCost
import WordCertDensity.Construction.ClockMargin
import WordCertDensity.Construction.TerminalPrecisionLimit

/-! # Uniform reduced-source clocks with fixed target overhead

The parent is the actual physical terminal parent. Its specified target path
and the fixed prefix overhead are included in T, before the stage grows.
-/

namespace WordCertDensity.Construction
open Filter
open scoped Topology

/-- A strict rate margin absorbs both fixed height and fixed clock overheads. -/
theorem terminalClock_budget_eventually {Y R θ c : ℝ} (hY : 3 ≤ Y)
    (hcap : θ ≤ 1/1000)
    (hc : terminalClockRate Y R θ < c) (C T : ℝ) :
    ∀ᶠ B : ℕ in atTop,
      (R+θ/20+(481/100)*θ)*B+T ≤ c*(Real.log 2*((Y-θ/20)*B+C)) := by
  have hd := terminalClock_denominator_pos hY hcap
  have hg : 0 < c*(Real.log 2*(Y-θ/20))-(R+θ/20+(481/100)*θ) := by
    have h := (div_lt_iff₀ hd).mp hc
    linarith
  have ht : Tendsto (fun B : ℕ =>
      (c*(Real.log 2*(Y-θ/20))-(R+θ/20+(481/100)*θ))*(B : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hg
  filter_upwards [ht.eventually (eventually_ge_atTop (T-c*Real.log 2*C))] with B hB
  nlinarith

/-- Every later reduced physical source obeys the chosen ordinary target clock. -/
theorem terminalPhysical_clock_eventually {Y R θ c : ℝ} (hY : 3 ≤ Y)
    (hR : R=criticalClock*Real.log 2*Y) (hθ : 0 < θ) (hcap : θ ≤ 1/1000)
    (hc : terminalClockRate Y R θ < c) (C T : ℝ) (target : ℕ) :
    ∀ᶠ B : ℕ in atTop, ∀ u y x : ℕ, ∀ w : ValuationWord,
      u ≤ 2*terminalRadius ⌊θ*B⌋₊ → TerminalWord ⌊θ*B⌋₊ u 1 w →
      16^⌊θ*B⌋₊ ≤ y → PhysicalHistory w y x →
      (Y-θ/20)*B+C ≤ binaryLog y →
      ReachesWithin y target ((R+θ/20)*B+T) →
      ReachesWithin x target (c*Real.log x) := by
  have hc0 : 0 < c := by
    have hm := (terminalClock_margin hY hR hθ hcap).1
    linarith [criticalClock_bounds.1]
  filter_upwards [(terminalDepth_tendsto hθ).eventually (eventually_ge_atTop 200),
    terminalClock_budget_eventually hY hcap hc C T] with B hb hbudget
  intro u y x w hu hw hy hp hheight hpath
  have hcost := terminalWord_parametric_cost hθ.le hb hu hw
  have hparent := terminalPhysical_parent_le hb hw hy hp
  have hlog := hheight.trans (binaryLog_mono (x := (y : ℝ)) (y := (x : ℝ))
    (by exact_mod_cast hp.root_pos)
    (by exact_mod_cast hparent))
  have hln : Real.log 2*((Y-θ/20)*B+C) ≤ Real.log x := by
    have h := (le_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ)<2))).mp hlog
    nlinarith
  obtain ⟨steps,hsteps,hstepsCost⟩ := hpath
  refine ⟨w.ordinaryCost+steps, hp.reachesIn.trans hsteps, ?_⟩
  have hfinal := mul_le_mul_of_nonneg_left hln hc0.le
  push_cast
  nlinarith

/-- The complete fixed-overhead clock estimate with the actual stopped means. -/
theorem stoppedMean_terminalPhysical_clock {θ c : ℝ} (hθ : 0 < θ) (hcap : θ ≤ 1/1000)
    (hc : criticalClock+3*θ ≤ c) (C T : ℝ) (target : ℕ) :
    ∀ᶠ B : ℕ in atTop, ∀ u y x : ℕ, ∀ w : ValuationWord,
      u ≤ 2*terminalRadius ⌊θ*B⌋₊ → TerminalWord ⌊θ*B⌋₊ u 1 w →
      16^⌊θ*B⌋₊ ≤ y → PhysicalHistory w y x →
      (stoppedExpectation displacement-θ/20)*B+C ≤ binaryLog y →
      ReachesWithin y target
        ((stoppedExpectation (fun w => w.ordinaryCost)+θ/20)*B+T) →
      ReachesWithin x target (c*Real.log x) := by
  apply terminalPhysical_clock_eventually stoppedExpectation_displacement_lower
    stoppedMean_clock_identity hθ hcap _ C T target
  linarith [(stoppedMean_terminalClock_margin hθ hcap).2]

/-- The selected stage retains the actual radius and diverging marker precision. -/
theorem terminalSelected_scales {α : Type*} {l : Filter α} {B : α → ℕ}
    (hB : Tendsto B l atTop) {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (fun a => terminalShellRadius ⌊θ*B a⌋₊) l (𝓝 16) ∧
      Tendsto (fun a => parametricLevel θ (B a)) l atTop :=
  ⟨terminalShellRadius_tendsto.comp ((terminalDepth_tendsto hθ).comp hB),
    (parametricLevel_tendsto hθ).comp hB⟩

end WordCertDensity.Construction
