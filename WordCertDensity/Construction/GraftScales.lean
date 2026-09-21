/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.SeedConductor
import WordCertDensity.Construction.MacroLevels
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Nat.Sqrt

/-! # The literal rounded transition scales

Natural square root and division realize E=floor(sqrt(b_t)) and B_0=floor(E/4).
The bounds below retain these rounded quantities in the later graft error.
-/

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- The common finite precision used only for the transition. -/
def graftPrecision (b t : ℕ) : ℕ := Nat.sqrt (seedSize b t)

/-- The transition's actual number of appended stopped blocks. -/
def graftInitialCount (b t : ℕ) : ℕ := graftPrecision b t / 4

/-- Natural square root agrees with the manuscript's real-floor formula. -/
theorem graftPrecision_eq_floor (b t : ℕ) :
    graftPrecision b t = ⌊Real.sqrt (seedSize b t : ℝ)⌋₊ :=
  Real.nat_floor_real_sqrt_eq_nat_sqrt.symm

/-- The transition precision is between half the square root and the square root. -/
theorem graftPrecision_bounds {b t : ℕ} (hb : 1 ≤ b) :
    Real.sqrt (seedSize b t : ℝ) / 2 ≤ graftPrecision b t ∧
      (graftPrecision b t : ℝ) ≤ Real.sqrt (seedSize b t : ℝ) := by
  have hn : 0 < seedSize b t := by have := seedSize_ge b t; omega
  have hE : 1 ≤ graftPrecision b t := Nat.sqrt_pos.mpr hn
  have hEr : (1 : ℝ) ≤ graftPrecision b t := by exact_mod_cast hE
  have hupper := Real.real_sqrt_lt_nat_sqrt_succ (a := seedSize b t)
  change Real.sqrt (seedSize b t : ℝ) < (graftPrecision b t : ℝ) + 1 at hupper
  exact ⟨by linarith, Real.nat_sqrt_le_real_sqrt⟩

/-- Every depth at least 256 squared already meets the transition precision guard. -/
theorem graftPrecision_ge_256 {b : ℕ} (hb : 256 ^ 2 ≤ b) (t : ℕ) :
    256 ≤ graftPrecision b t :=
  Nat.le_sqrt'.mpr (hb.trans (seedSize_ge b t))

/-- Exact quarter rounding retains both square-root count bounds. -/
theorem graftInitialCount_bounds {b t : ℕ} (hb : 256 ^ 2 ≤ b) :
    Real.sqrt (seedSize b t : ℝ) / 16 ≤ graftInitialCount b t ∧
      (graftInitialCount b t : ℝ) ≤ Real.sqrt (seedSize b t : ℝ) / 4 := by
  have hE := graftPrecision_ge_256 hb t
  have hnat : graftPrecision b t ≤ 8 * graftInitialCount b t ∧
      4 * graftInitialCount b t ≤ graftPrecision b t := by
    unfold graftInitialCount
    omega
  have hr : (graftPrecision b t : ℝ) ≤ 8 * (graftInitialCount b t : ℝ) ∧
      4 * (graftInitialCount b t : ℝ) ≤ graftPrecision b t := by exact_mod_cast hnat
  have hs := graftPrecision_bounds (b := b) (t := t) (by omega)
  constructor <;> linarith [hs.1, hs.2, hr.1, hr.2]

/-- The original transition depth fits inside one quarter of the current seed depth. -/
theorem graftTransition_depth (b t : ℕ) :
    graftInitialCount b t * (graftPrecision b t - 1) ≤ seedSize b t / 4 := by
  have hE : graftPrecision b t * graftPrecision b t ≤ seedSize b t := Nat.sqrt_le _
  have hquarter : 4 * graftInitialCount b t ≤ graftPrecision b t := by
    unfold graftInitialCount
    omega
  have hprod := Nat.mul_le_mul hquarter (Nat.sub_le (graftPrecision b t) 1)
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 4)).mpr
  calc
    _ = (4 * graftInitialCount b t) * (graftPrecision b t - 1) := by ac_rfl
    _ ≤ graftPrecision b t * graftPrecision b t := hprod
    _ ≤ _ := hE

/-- The new marker level retains the quantitative square-root lower bound. -/
theorem graftInitialLevel_lower {b t : ℕ} (hb : 256 ^ 2 ≤ b) :
    Real.sqrt (seedSize b t : ℝ) / 16000 ≤ macroLevel (graftInitialCount b t) := by
  have hc := (graftInitialCount_bounds (t := t) hb).1
  have hl := (macroLevel_bounds (graftInitialCount b t)).1
  linarith

/-- Both positive marker levels and the enlarged conductor Q=2b_t are valid. -/
theorem graftTransition_level_guards {b : ℕ} (hb : 256 ^ 2 ≤ b) (t : ℕ) :
    1 ≤ macroLevel (graftInitialCount b t) ∧
      seedTailDepth b t ≤ 2 * seedSize b t ∧
      graftInitialCount b t * (graftPrecision b t - 1) +
        macroLevel (graftInitialCount b t) ≤ 2 * seedSize b t := by
  have hE := graftPrecision_ge_256 hb t
  have hcount : 1 ≤ graftInitialCount b t := by unfold graftInitialCount; omega
  have hn : 2 ≤ seedSize b t := by have := seedSize_ge b t; omega
  have hEn : graftPrecision b t ≤ seedSize b t := Nat.sqrt_le_self _
  have hCE : graftInitialCount b t ≤ graftPrecision b t := Nat.div_le_self _ _
  have hlevel : macroLevel (graftInitialCount b t) ≤ graftInitialCount b t := by
    apply Nat.ceil_le.mpr
    have hnonneg : (0 : ℝ) ≤ graftInitialCount b t := Nat.cast_nonneg _
    change (graftInitialCount b t : ℝ) / 1000 ≤ graftInitialCount b t
    linarith
  have hdepth := graftTransition_depth b t
  refine ⟨macroLevel_pos hcount, ?_, ?_⟩
  · unfold seedTailDepth
    omega
  · omega

/-- The incoming marker keeps the quantitative lower bound for its mixing error. -/
theorem graftOldLevel_lower {b : ℕ} (hb : 256 ^ 2 ≤ b) (t : ℕ) :
    (seedSize b t : ℝ) / 8 ≤ seedTailDepth b t := by
  have hn : 4 ≤ seedSize b t := by have := seedSize_ge b t; omega
  have hnat : seedSize b t ≤ 8 * seedTailDepth b t := by unfold seedTailDepth; omega
  have hr : (seedSize b t : ℝ) ≤ 8 * (seedTailDepth b t : ℝ) := by exact_mod_cast hnat
  linarith

/-- The literal transition count eventually exceeds every fixed threshold. -/
theorem graftInitialCount_tendsto {b : ℕ} (hb : 100 ≤ b) :
    Tendsto (graftInitialCount b) atTop atTop := by
  apply tendsto_atTop.2
  intro K
  filter_upwards [eventually_ge_atTop ((4 * K) ^ 2)] with t ht
  have hsize := seedSize_ge_add hb t
  have hsqrt : 4 * K ≤ graftPrecision b t := Nat.le_sqrt'.mpr (by omega)
  exact (Nat.le_div_iff_mul_le (by decide : 0 < 4)).mpr (by omega)

end WordCertDensity.Construction
