/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalScale

/-! # Sharp shells for actual terminal sources

The offset correction retains the parent height. These bounds apply to
physical histories with overshoot zero or one, before selecting a common cutoff.
-/

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- Lower shell scale with the actual relative offset correction. -/
noncomputable def terminalShellLow (b : ℕ) (y : ℝ) : ℝ :=
  (1 - terminalEta b) * y * terminalScale b 0 / 2

/-- Containing radius after the least binary shift. -/
noncomputable def terminalShellRadius (b : ℕ) : ℝ := 16 / (1 - terminalEta b)

/-- The lower shell scale equals the manuscript's literal rational-power recipe. -/
theorem terminalShellLow_recipe (b : ℕ) (y : ℝ) :
    terminalShellLow b y =
      2 * (1 - terminalEta b) * (4 : ℝ) ^ b * y /
        (4 * 2 ^ terminalRadius b * 3 ^ b) := by
  simp only [terminalShellLow, terminalScale, pow_zero, mul_one]
  ring

/-- The lower shell scale is positive at every permitted positive parent and size. -/
theorem terminalShellLow_pos {b : ℕ} (hb : 0 < b) {y : ℝ} (hy : 0 < y) :
    0 < terminalShellLow b y := by
  unfold terminalShellLow
  exact div_pos (mul_pos (mul_pos (sub_pos.mpr (terminalEta_bounds hb).2) hy)
    (terminalScale_pos b 0)) (by norm_num)

/-- Shifting the shell preserves the exact physical scale. -/
theorem terminalShellLow_shift (b u : ℕ) (y : ℝ) :
    2 ^ u * terminalShellLow b y = (1 - terminalEta b) * y * terminalScale b u / 2 := by
  rw [terminalShellLow, terminalScale_shift b u]
  ring

/-- The upper shell endpoint simplifies without losing the offset correction in its radius. -/
theorem terminalShell_upper_eq {b : ℕ} (hb : 0 < b) (u : ℕ) (y : ℝ) :
    8 / (1 - terminalEta b) * (2 ^ u * terminalShellLow b y) =
      y * (4 * terminalScale b u) := by
  have he : 1 - terminalEta b ≠ 0 := ne_of_gt (sub_pos.mpr (terminalEta_bounds hb).2)
  rw [terminalShellLow_shift]
  field_simp
  ring

/-- Every reduced compatible physical source lies in its stated sharp shell. -/
theorem terminalPhysical_shell {b u y x : ℕ} (hb : 0 < b) {w : ValuationWord}
    (hw : TerminalWord b u 1 w) (hy : 16 ^ b ≤ y) (hp : PhysicalHistory w y x) :
    2 ^ u * terminalShellLow b y ≤ (x : ℝ) ∧
      (x : ℝ) ≤ 8 / (1 - terminalEta b) * (2 ^ u * terminalShellLow b y) := by
  have hyR : (16 : ℝ) ^ b ≤ (y : ℝ) := by exact_mod_cast hy
  have hyp : (0 : ℝ) < y := (by positivity : (0 : ℝ) < 16 ^ b).trans_le hyR
  have hoff := terminalWord_relative_offset hb hw hyR
  have hgap : (1 - terminalEta b) * y ≤ (y : ℝ) - (w.offset : ℝ) := by
    have h := (div_lt_iff₀ hyp).mp hoff
    nlinarith
  have hgap0 : 0 ≤ (1 - terminalEta b) * y :=
    mul_nonneg (sub_nonneg.mpr (terminalEta_bounds hb).2.le) hyp.le
  have hupp : (y : ℝ) - (w.offset : ℝ) ≤ y := by
    have h := (terminalWord_offset hb hw).1
    linarith
  have ha := terminalWord_inverseSlope hw
  have hap := (one_div_pos.mpr (Transfer.weight_pos w)).le
  have hx : (x : ℝ) = ((y : ℝ) - (w.offset : ℝ)) * (1 / Transfer.weight w) := by
    rw [terminalPhysical_source_eq hp, div_eq_mul_one_div]
  constructor
  · rw [terminalShellLow_shift, hx]
    calc
      _ = ((1 - terminalEta b) * y) * (terminalScale b u / 2) := by ring
      _ ≤ ((1 - terminalEta b) * y) * (1 / Transfer.weight w) :=
        mul_le_mul_of_nonneg_left ha.1 hgap0
      _ ≤ _ := mul_le_mul_of_nonneg_right hgap hap
  · rw [terminalShell_upper_eq hb, hx]
    exact (mul_le_mul_of_nonneg_right hupp hap).trans
      (mul_le_mul_of_nonneg_left ha.2 hyp.le)

/-- The offset correction tends to zero along the terminal sizes. -/
theorem terminalEta_tendsto : Tendsto terminalEta atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- The finite containing radii tend to sixteen. -/
theorem terminalShellRadius_tendsto : Tendsto terminalShellRadius atTop (𝓝 16) := by
  have h : Tendsto (fun b => (16 : ℝ) / (1 - terminalEta b)) atTop (𝓝 (16 / (1 - 0))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.sub terminalEta_tendsto)
      (by norm_num : (1 : ℝ) - 0 ≠ 0)
  change Tendsto (fun b : ℕ => (16 : ℝ) / (1 - terminalEta b)) atTop (𝓝 16)
  simpa only [sub_zero, div_one] using h

end WordCertDensity.Construction
