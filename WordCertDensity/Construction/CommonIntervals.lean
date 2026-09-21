/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.CommonGeometry
import WordCertDensity.Construction.MacroIntervalBounds
import WordCertDensity.Construction.IntervalCoverage

/-! # Every sufficiently large cutoff belongs to a common source interval

Literal shell endpoints have bounded linear errors and logarithmic changes
at successive macro counts. Positive theta leaves linear overlap room. The
first suitable upper endpoint then supplies a stage tending to infinity.
-/

namespace WordCertDensity.Construction

open Filter Asymptotics
open scoped Topology

/-- Both exact common endpoints eventually satisfy fixed linear error bounds. -/
theorem commonLinear_eventually {θ : ℝ} (hθ : 0 < θ) (Y minus plus : ℝ) :
    ∀ᶠ B : ℕ in atTop, 200 ≤ ⌊θ*B⌋₊ ∧
      |commonLowExponent θ Y plus B-(commonLowRate θ Y*B+plus)| ≤ 6 ∧
      |commonHighExponent θ Y minus B-(commonHighRate θ Y*B+minus)| ≤ 7 := by
  filter_upwards [eventually_ge_atTop ⌈(200 : ℝ)/θ⌉₊] with B hcut
  have hd : (200 : ℝ)/θ ≤ B := (Nat.le_ceil _).trans (Nat.cast_le.mpr hcut)
  have hb : 200 ≤ ⌊θ*B⌋₊ := by
    apply (Nat.le_floor_iff (by positivity)).mpr
    norm_num only [Nat.cast_ofNat]
    have h := (div_le_iff₀ hθ).mp hd
    nlinarith
  exact ⟨hb, commonLow_linear hθ.le hb, commonHigh_linear hθ.le hb⟩

/-- Both deterministic logarithmic endpoints diverge along the count. -/
theorem commonEndpoints_tendsto {θ Y : ℝ} (hθ : 0 < θ) (hY : 3 ≤ Y) (minus plus : ℝ) :
    Tendsto (commonLowExponent θ Y plus) atTop atTop ∧
      Tendsto (commonHighExponent θ Y minus) atTop atTop := by
  obtain ⟨ha,hgap⟩ := commonRates_gap hθ hY
  have hd : 0 < commonHighRate θ Y := by nlinarith
  have h := commonLinear_eventually hθ Y minus plus
  exact ⟨linearEndpoint_tendsto ha (h.mono fun B hB => hB.2.1),
    linearEndpoint_tendsto hd (h.mono fun B hB => hB.2.2)⟩

/-- Both exact endpoint changes have the required logarithmic macro-step size. -/
theorem commonEndpoint_changes {θ L : ℝ} (hθ : 0 < θ) (hL : 0 ≤ L) (Y minus plus : ℝ) :
    ((fun B : ℕ => commonLowExponent θ Y plus (B+macroLength L B)-commonLowExponent θ Y plus B)
      =O[atTop] (fun B : ℕ => Real.log ((B : ℝ)+2))) ∧
    ((fun B : ℕ => commonHighExponent θ Y minus (B+macroLength L B)-commonHighExponent θ Y minus B)
      =O[atTop] (fun B : ℕ => Real.log ((B : ℝ)+2))) := by
  have h := commonLinear_eventually hθ Y minus plus
  exact ⟨linearEndpoint_macro_isBigO hL (by norm_num) (h.mono fun B hB => hB.2.1),
    linearEndpoint_macro_isBigO hL (by norm_num) (h.mono fun B hB => hB.2.2)⟩

/-- Consecutive actual macro intervals eventually overlap. -/
theorem commonEndpoints_overlap {θ L Y : ℝ} (hθ : 0 < θ) (hL : 0 ≤ L) (hY : 3 ≤ Y)
    (minus plus : ℝ) : ∀ᶠ B : ℕ in atTop,
      commonLowExponent θ Y plus (B+macroLength L B) ≤ commonHighExponent θ Y minus B := by
  have hg := (commonRates_gap hθ hY).2
  have hgap : commonLowRate θ Y < commonHighRate θ Y := by nlinarith
  have h := commonLinear_eventually hθ Y minus plus
  exact linearEndpoints_macro_overlap hL hgap
    (h.mono fun B hB => hB.2.1) (h.mono fun B hB => hB.2.2)

/-- The literal common intervals cover a half-line with a diverging selected stage. -/
theorem commonIntervalCoverage (θ L Y minus plus : ℝ) (B₀ : ℕ)
    (hθ : 0 < θ) (_hcap : θ ≤ 1/1000) (hL : 0 < L) (hY : 3 ≤ Y) :
    ∃ stage : ℝ → ℕ, Tendsto stage atTop atTop ∧
      ∀ᶠ X : ℝ in atTop,
        let B := macroCount L B₀ (stage X)
        (2 : ℝ)^(commonLowExponent θ Y plus B) < X ∧
          X ≤ (2 : ℝ)^(commonHighExponent θ Y minus B) := by
  let A := fun j => (2 : ℝ)^(commonLowExponent θ Y plus (macroCount L B₀ j))
  let D := fun j => (2 : ℝ)^(commonHighExponent θ Y minus (macroCount L B₀ j))
  have hD : Tendsto D atTop atTop :=
    ((tendsto_rpow_atTop_of_base_gt_one 2 (by norm_num)).comp
      (commonEndpoints_tendsto hθ hY minus plus).2).comp (macroCount_tendsto hL B₀)
  have hov : ∀ᶠ j : ℕ in atTop, A (j+1) ≤ D j := by
    filter_upwards [(macroCount_tendsto hL B₀).eventually
      (commonEndpoints_overlap hθ hL.le hY minus plus)] with j hj
    have hp := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hj
    simpa only [A, D, macroCount] using hp
  exact interval_eventual_coverage A D hD hov

end WordCertDensity.Construction
