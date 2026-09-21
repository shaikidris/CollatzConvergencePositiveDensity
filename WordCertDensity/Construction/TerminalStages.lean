/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalBudget

/-! # Eventual guards for the parameterized terminal stage

The positive parameter is fixed before the original-block count increases.
The terminal conductor retains its finite point term until its explicit
comparison with that count pays the boundary.
-/

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- Once theta B reaches two, the depth floor keeps at least half of it. -/
theorem terminalStage_half {θ : ℝ} {B : ℕ} (hlarge : 2 ≤ θ*B) :
    θ*(B : ℝ)/2 ≤ (⌊θ*B⌋₊ : ℝ) := by
  have h := Nat.lt_floor_add_one (θ*(B : ℝ))
  linarith

/-- The terminal conductor is at most the original-block count on a uniform finite domain. -/
theorem terminalConductor_stage_le {θ : ℝ} (hθ : 0 ≤ θ) (hcap : θ ≤ 1/1000)
    {B : ℕ} (hB : 2 ≤ B) :
    terminalConductor ⌊θ*B⌋₊ (parametricLevel θ B) ≤ B := by
  have hd : (⌊θ*B⌋₊ : ℝ) ≤ θ*B := Nat.floor_le (by positivity)
  have hhi : terminalHigh ⌊θ*B⌋₊ ≤ 2*⌊θ*B⌋₊ := by
    have := terminalWidth_le ⌊θ*B⌋₊
    unfold terminalHigh
    omega
  have hhiR : (terminalHigh ⌊θ*B⌋₊ : ℝ) ≤ 2*(⌊θ*B⌋₊ : ℝ) := by exact_mod_cast hhi
  have hk := (parametricLevel_bounds hθ B).2
  have hcapB := mul_le_mul_of_nonneg_right hcap (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
  have hBR : (2 : ℝ) ≤ B := by exact_mod_cast hB
  apply Nat.cast_le.mp (show (terminalConductor ⌊θ*B⌋₊ (parametricLevel θ B) : ℝ) ≤ B from ?_)
  simp only [terminalConductor, Nat.cast_add]
  linarith

/-- The actual finite-modulus boundary is paid without dropping it from the capacity theorem. -/
theorem terminalBoundary_stage_le_one {θ : ℝ} (hθ : 0 ≤ θ) (hcap : θ ≤ 1/1000)
    {B : ℕ} (hB : 2 ≤ B) :
    terminalBoundary ⌊θ*B⌋₊ (parametricLevel θ B) B ≤ 1 := by
  unfold terminalBoundary
  calc
    _ ≤ (3 : ℝ)^B * (1/8 : ℝ)^B :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num)
        (terminalConductor_stage_le hθ hcap hB)) (by positivity)
    _ = ((3 : ℝ)*(1/8))^B := (mul_pow _ _ _).symm
    _ ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)

/-- Every fixed positive theta eventually meets all finite-stage payment guards. -/
theorem eventually_terminalStage_guards {θ : ℝ} (hθ : 0 < θ) (hcap : θ ≤ 1/1000) :
    ∀ᶠ B : ℕ in atTop, 200 ≤ ⌊θ*B⌋₊ ∧ 1 ≤ parametricLevel θ B ∧
      terminalBoundary ⌊θ*B⌋₊ (parametricLevel θ B) B ≤ 1 := by
  filter_upwards [eventually_ge_atTop 2, eventually_ge_atTop ⌈(200 : ℝ)/θ⌉₊] with B hB hcut
  have hdiv : (200 : ℝ)/θ ≤ B := (Nat.le_ceil _).trans (Nat.cast_le.mpr hcut)
  have hlarge : (200 : ℝ) ≤ θ*B := by
    simpa only [mul_comm] using (div_le_iff₀ hθ).mp hdiv
  refine ⟨(Nat.le_floor_iff (by positivity)).mpr hlarge,
    parametricLevel_pos hθ (by omega), terminalBoundary_stage_le_one hθ.le hcap hB⟩

/-- A linear count bound pays every permitted selected shift, including the zero label. -/
theorem terminalStage_shift_count {θ : ℝ} (hθ : 0 ≤ θ) (hcap : θ ≤ 1)
    {B : ℕ} (hB : 1 ≤ B) : 2*terminalRadius ⌊θ*B⌋₊+1 ≤ 5*B := by
  have hd : ⌊θ*B⌋₊ ≤ B := by
    apply Nat.cast_le.mp (show (⌊θ*B⌋₊ : ℝ) ≤ (B : ℝ) from ?_)
    exact (Nat.floor_le (by positivity : 0 ≤ θ*(B : ℝ))).trans
      (by nlinarith [mul_le_mul_of_nonneg_right hcap (Nat.cast_nonneg B : (0 : ℝ) ≤ B)])
  have hw := terminalWidth_le ⌊θ*B⌋₊
  unfold terminalRadius
  omega

end WordCertDensity.Construction
