/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.CommonShell
import WordCertDensity.Construction.TerminalPrecisionLimit

/-! # Fine-precision limit from deterministic common cutoffs

A deterministic upper height supplies the precision comparison. No actual
retained parent must be chosen from a possibly empty physical family.
-/

namespace WordCertDensity.Construction
open Filter
open scoped Topology

/-- The binary height of a real binary exponential is exact. -/
theorem binaryLog_two_rpow (a : ℝ) : binaryLog ((2 : ℝ)^a) = a := by
  rw [binaryLog, Real.log_rpow (by norm_num : (0 : ℝ)<2)]
  exact mul_div_cancel_right₀ a (Real.log_pos (by norm_num : (1 : ℝ)<2)).ne'

/-- The deterministic upper parent height eventually satisfies the terminal height premise. -/
theorem commonUpper_height_eventually {θ Y : ℝ} (hθ : 0 ≤ θ) (hcap : θ ≤ 1/1000)
    (hY : 3 ≤ Y) (plus : ℝ) :
    ∀ᶠ B : ℕ in atTop,
      (16 : ℝ)^⌊θ*B⌋₊ ≤ (2 : ℝ)^((Y+θ/20)*B+plus) := by
  filter_upwards [commonParent_height_eventually hθ hcap hY plus] with B hB
  apply hB _ (by positivity)
  rw [binaryLog_two_rpow]
  nlinarith [mul_nonneg hθ (Nat.cast_nonneg B : (0 : ℝ)≤B)]

/-- The full ceiling-sensitive precision estimate holds along any selected common cutoffs. -/
theorem commonCutoff_precision {α : Type*} {l : Filter α} {B : α → ℕ}
    (hB : Tendsto B l atTop) {θ Y plus : ℝ}
    (hθ : 0 < θ) (hcap : θ ≤ 1/1000) (hY : 3 ≤ Y) {X : α → ℝ}
    (hX : ∀ᶠ a in l, (2 : ℝ)^commonLowExponent θ Y plus (B a) < X a) :
    Tendsto (fun a => (3 : ℝ)^parametricLevel θ (B a)/X a) l (𝓝 0) := by
  apply terminalSelected_precision hB hθ
    (hB.eventually (commonUpper_height_eventually hθ.le hcap hY plus))
  filter_upwards [((terminalDepth_tendsto hθ).comp hB).eventually (eventually_ge_atTop 1),hX]
    with a hd ha
  change 1 ≤ ⌊θ*B a⌋₊ at hd
  have hp : 0 < ⌊θ*B a⌋₊ := by omega
  rw [terminalShellLow_mul]
  simpa only [commonLow_power hp] using ha

end WordCertDensity.Construction
