/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.CommonIntervals

/-! # Common cutoffs satisfy every actual parent's shell conditions -/

namespace WordCertDensity.Construction
open Filter
open scoped Topology

/-- Exponentiating the physical binary height recovers its positive argument. -/
theorem two_rpow_binaryLog {y : ℝ} (hy : 0 < y) : (2 : ℝ)^binaryLog y = y := by
  exact Real.rpow_logb (by norm_num) (by norm_num) hy

/-- The lower shell depends linearly on its actual parent. -/
theorem terminalShellLow_mul (b : ℕ) (y : ℝ) :
    terminalShellLow b y = y*terminalShellLow b 1 := by
  unfold terminalShellLow
  ring

/-- Literal factorization of the common lower endpoint. -/
theorem commonLow_power {θ Y plus : ℝ} {B : ℕ} (hb : 0 < ⌊θ*B⌋₊) :
    (2 : ℝ)^commonLowExponent θ Y plus B =
      (2 : ℝ)^((Y+θ/20)*B+plus)*terminalShellLow ⌊θ*B⌋₊ 1 := by
  rw [commonLowExponent, Real.rpow_add (by norm_num),
    two_rpow_binaryLog (terminalShellLow_pos hb (by norm_num))]

/-- Literal factorization of the common upper endpoint, with its full shift radius. -/
theorem commonHigh_power {θ Y minus : ℝ} {B : ℕ} (hb : 0 < ⌊θ*B⌋₊) :
    (2 : ℝ)^commonHighExponent θ Y minus B =
      (2 : ℝ)^(2*terminalRadius ⌊θ*B⌋₊)*
        ((2 : ℝ)^((Y-θ/20)*B+minus)*terminalShellLow ⌊θ*B⌋₊ 1) := by
  rw [commonHighExponent, Real.rpow_add (by norm_num), Real.rpow_add (by norm_num),
    two_rpow_binaryLog (terminalShellLow_pos hb (by norm_num))]
  have hc : (2 : ℝ)^(2*(terminalRadius ⌊θ*B⌋₊ : ℝ)) = (2 : ℝ)^(2*terminalRadius ⌊θ*B⌋₊) := by
    rw [show (2 : ℝ)*(terminalRadius ⌊θ*B⌋₊ : ℝ) = ((2*terminalRadius ⌊θ*B⌋₊ : ℕ) : ℝ) by push_cast; rfl,
      Real.rpow_natCast]
  rw [hc]
  ring

/-- The deterministic common interval works simultaneously for every parent in its height band. -/
theorem commonParent_shell {θ Y minus plus y X : ℝ} {B : ℕ}
    (hb : 0 < ⌊θ*B⌋₊) (hy : 0 < y)
    (hlo : (Y-θ/20)*B+minus ≤ binaryLog y)
    (hhi : binaryLog y ≤ (Y+θ/20)*B+plus)
    (hXlo : (2 : ℝ)^commonLowExponent θ Y plus B < X)
    (hXhi : X ≤ (2 : ℝ)^commonHighExponent θ Y minus B) :
    terminalShellLow ⌊θ*B⌋₊ y < X ∧
      X ≤ (2 : ℝ)^(2*terminalRadius ⌊θ*B⌋₊)*terminalShellLow ⌊θ*B⌋₊ y := by
  have hsmall := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) hlo
  have hlarge := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) hhi
  rw [two_rpow_binaryLog hy] at hsmall hlarge
  have hunit := (terminalShellLow_pos hb (by norm_num : (0 : ℝ)<1)).le
  rw [commonLow_power hb] at hXlo
  rw [commonHigh_power hb] at hXhi
  rw [terminalShellLow_mul]
  exact ⟨(mul_le_mul_of_nonneg_right hlarge hunit).trans_lt hXlo,
    hXhi.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsmall hunit) (by positivity))⟩

/-- A binary exponent four times a natural depth is the exact parent-height power. -/
theorem two_rpow_four_nat (d : ℕ) : (2 : ℝ)^((4 : ℝ)*d) = (16 : ℝ)^d := by
  rw [show (4 : ℝ)*d = ((4*d : ℕ) : ℝ) by push_cast; rfl, Real.rpow_natCast, pow_mul]
  norm_num

/-- Every parent in the deterministic lower band eventually meets the terminal height guard. -/
theorem commonParent_height_eventually {θ Y : ℝ} (hθ : 0 ≤ θ) (hcap : θ ≤ 1/1000)
    (hY : 3 ≤ Y) (C : ℝ) :
    ∀ᶠ B : ℕ in atTop, ∀ y : ℝ, 0 < y →
      (Y-θ/20)*B+C ≤ binaryLog y → (16 : ℝ)^⌊θ*B⌋₊ ≤ y := by
  have hg : 0 < Y-θ/20-4*θ := by linarith
  have ht : Tendsto (fun B : ℕ => (Y-θ/20-4*θ)*(B : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hg
  filter_upwards [ht.eventually (eventually_ge_atTop (-C))] with B hB
  intro y hy hh
  have hf : (⌊θ*B⌋₊ : ℝ) ≤ θ*B := Nat.floor_le (by positivity)
  have hlog : (4 : ℝ)*⌊θ*B⌋₊ ≤ binaryLog y := by nlinarith
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2) hlog
  simpa only [two_rpow_four_nat, two_rpow_binaryLog hy] using h

end WordCertDensity.Construction
