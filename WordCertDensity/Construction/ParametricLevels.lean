/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.MacroLevels

/-! # Positive-parameter marker levels on the unchanged macro schedule

Only the appended marker level changes. The actual retained macroblocks,
their maximal depth and the original-block count keep their existing meaning.
-/

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- Appended marker level for the fixed positive parameter. -/
noncomputable def parametricLevel (θ : ℝ) (B : ℕ) : ℕ := ⌈θ * B⌉₊

/-- Next marker level plus the actual finite-family maximum depth. -/
noncomputable def parametricConductor (θ L δ : ℝ) (B : ℕ) : ℕ :=
  parametricLevel θ (B + macroLength L B) + macroblockDepth L δ B

@[simp] theorem parametricLevel_zero (θ : ℝ) : parametricLevel θ 0 = 0 := by
  simp [parametricLevel]

/-- Exact specialization preserves the fixed-scale definition. -/
theorem parametricLevel_fixed (B : ℕ) : parametricLevel (1 / 1000) B = macroLevel B := by
  unfold parametricLevel macroLevel
  congr 1
  ring

/-- The full conductor also specializes literally. -/
theorem parametricConductor_fixed (L δ : ℝ) (B : ℕ) :
    parametricConductor (1 / 1000) L δ B = macroConductor L δ B := by
  simp only [parametricConductor, macroConductor, parametricLevel_fixed]

/-- The ceiling costs less than one at every count. -/
theorem parametricLevel_bounds {θ : ℝ} (hθ : 0 ≤ θ) (B : ℕ) :
    θ * B ≤ parametricLevel θ B ∧ (parametricLevel θ B : ℝ) < θ * B + 1 :=
  ⟨Nat.le_ceil _, Nat.ceil_lt_add_one (mul_nonneg hθ (Nat.cast_nonneg _))⟩

/-- Appended levels are monotone in the actual original count. -/
theorem parametricLevel_mono {θ : ℝ} (hθ : 0 ≤ θ) : Monotone (parametricLevel θ) := by
  intro B C hBC
  exact Nat.ceil_mono (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hBC) hθ)

/-- A positive parameter and positive count give a usable positive mixing level. -/
theorem parametricLevel_pos {θ : ℝ} (hθ : 0 < θ) {B : ℕ} (hB : 1 ≤ B) :
    1 ≤ parametricLevel θ B := by
  apply Nat.one_le_ceil_iff.mpr
  exact mul_pos hθ (Nat.cast_pos.mpr (by omega))

/-- The positive parameter remains fixed while the marker level diverges. -/
theorem parametricLevel_tendsto {θ : ℝ} (hθ : 0 < θ) :
    Tendsto (parametricLevel θ) atTop atTop := by
  apply tendsto_atTop.mpr
  intro k
  filter_upwards [eventually_ge_atTop ⌈(k : ℝ) / θ⌉₊] with B hB
  have hdiv : (k : ℝ) / θ ≤ B := (Nat.le_ceil _).trans (Nat.cast_le.mpr hB)
  have hk : (k : ℝ) ≤ θ * B := by
    simpa only [mul_comm] using (div_le_iff₀ hθ).mp hdiv
  exact Nat.cast_le.mp (hk.trans (parametricLevel_bounds hθ.le B).1)

/-- All old/new/conductor order guards retain the positive parameter. -/
theorem parametricConductor_guards {θ : ℝ} (hθ : 0 < θ) (L δ : ℝ)
    {B : ℕ} (hB : 1 ≤ B) :
    1 ≤ parametricLevel θ B ∧
      parametricLevel θ B ≤ parametricLevel θ (B + macroLength L B) ∧
      parametricLevel θ (B + macroLength L B) ≤ parametricConductor θ L δ B ∧
      parametricLevel θ B ≤ parametricConductor θ L δ B := by
  have hm := parametricLevel_mono hθ.le (Nat.le_add_right B (macroLength L B))
  have hq : parametricLevel θ (B + macroLength L B) ≤ parametricConductor θ L δ B :=
    Nat.le_add_right _ _
  exact ⟨parametricLevel_pos hθ hB, hm, hq, hm.trans hq⟩

/-- The actual maximal word depth pays every subtraction in stopped transfer. -/
theorem parametricConductor_word_guards (θ : ℝ) {L δ : ℝ} {B : ℕ} {w : ValuationWord}
    (hw : w ∈ macroblocks L δ B) :
    w.length ≤ parametricConductor θ L δ B ∧
      parametricLevel θ (B + macroLength L B) ≤ parametricConductor θ L δ B - w.length := by
  have hd : w.length ≤ macroblockDepth L δ B := Finset.le_sup hw
  unfold parametricConductor
  omega

/-- Decreasing the marker parameter cannot enlarge the previous literal level. -/
theorem parametricLevel_le_fixed {θ : ℝ} (hθ : θ ≤ 1 / 1000) (B : ℕ) :
    parametricLevel θ B ≤ macroLevel B := by
  rw [← parametricLevel_fixed]
  exact Nat.ceil_mono (mul_le_mul_of_nonneg_right hθ (Nat.cast_nonneg _))

/-- The same conductor cutoff is valid throughout the permitted parameter range. -/
theorem parametricConductor_le_fixed {θ : ℝ} (hθ : θ ≤ 1 / 1000) (L δ : ℝ) (B : ℕ) :
    parametricConductor θ L δ B ≤ macroConductor L δ B :=
  Nat.add_le_add_right (parametricLevel_le_fixed hθ _) _

end WordCertDensity.Construction
