/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftScales
import WordCertDensity.Construction.SeedCapacity
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Graft error decay with the growing incoming family retained

The literal P_t B_0^(-3) factor is bounded using the rounded transition
count and the original geometric seed growth. It is summable and tends to
zero as the splice moves, before any root pool or physical cutoff is chosen.
-/

namespace WordCertDensity.Construction

open Filter
open scoped Topology

/-- The retained geometric rate of the complete continuation error. -/
noncomputable def graftDecayRate : ℝ :=
  seedTagGrowth / (201 / 200 : ℝ) ^ (3 / 2 : ℝ)

/-- The incoming-family factor in the complete graft tail. -/
noncomputable def graftTailWeight (b t : ℕ) : ℝ :=
  seedCapacity b t * ((graftInitialCount b t : ℝ) ^ 3)⁻¹

/-- The manuscript's exact strict margin pays for incoming tag growth. -/
theorem graft_growth_gap :
    (201 / 200 : ℝ) ^ 3 - seedTagGrowth ^ 2 = 16263 / 8000000 := by
  norm_num [seedTagGrowth]

/-- The retained incoming-weighted geometric rate is strictly between zero and one. -/
theorem graftDecayRate_bounds : 0 < graftDecayRate ∧ graftDecayRate < 1 := by
  have hg : 0 < seedTagGrowth := by norm_num [seedTagGrowth]
  have hgamma : 0 < (201 / 200 : ℝ) ^ (3 / 2 : ℝ) := by positivity
  have hlt : seedTagGrowth < (201 / 200 : ℝ) ^ (3 / 2 : ℝ) := by
    apply (Real.rpow_lt_rpow_iff hg.le hgamma.le (by norm_num : (0 : ℝ) < 2)).mp
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 201 / 200)]
    norm_num [seedTagGrowth]
  exact ⟨div_pos hg hgamma, (div_lt_one hgamma).mpr hlt⟩

/-- Raising the original geometric lower bound retains the initial seed depth. -/
theorem seedSize_three_halves_lower {b : ℕ} (hb : 200 ≤ b) (t : ℕ) :
    (b : ℝ) ^ (3 / 2 : ℝ) * ((201 / 200 : ℝ) ^ (3 / 2 : ℝ)) ^ t ≤
      (seedSize b t : ℝ) ^ (3 / 2 : ℝ) := by
  have hQ := (seedSize_geometric hb t).1
  have hr : (b : ℝ) * (201 / 200 : ℝ) ^ t ≤ seedSize b t := by
    have h := Rat.cast_le (K := ℝ) |>.mpr hQ
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat] using h
  have h := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ b * (201 / 200 : ℝ) ^ t)
    hr (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [Real.mul_rpow (Nat.cast_nonneg b) (by positivity),
    ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 201 / 200),
    mul_comm (t : ℝ) (3 / 2 : ℝ), Real.rpow_mul_natCast (by norm_num)] at h
  exact h

/-- Cubing the literal count bound gives the exact factor 4096 in the graft tail. -/
theorem graftInitialCount_cube_lower {b : ℕ} (hb : 256 ^ 2 ≤ b) (t : ℕ) :
    (b : ℝ) ^ (3 / 2 : ℝ) * ((201 / 200 : ℝ) ^ (3 / 2 : ℝ)) ^ t ≤
      4096 * (graftInitialCount b t : ℝ) ^ 3 := by
  have hc := (graftInitialCount_bounds (t := t) hb).1
  have hpow := pow_le_pow_left₀ (Real.sqrt_nonneg (seedSize b t : ℝ))
    (show Real.sqrt (seedSize b t : ℝ) ≤ 16 * (graftInitialCount b t : ℝ) by linarith) 3
  have hsqrt : Real.sqrt (seedSize b t : ℝ) ^ 3 =
      (seedSize b t : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (Nat.cast_nonneg _)]
    norm_num
  rw [hsqrt, mul_pow] at hpow
  norm_num only [show (16 : ℝ) ^ 3 = 4096 by norm_num] at hpow
  exact (seedSize_three_halves_lower (by omega) t).trans hpow

/-- The complete incoming tail factor is nonnegative, including zero-count boundaries. -/
theorem graftTailWeight_nonneg (b t : ℕ) : 0 ≤ graftTailWeight b t :=
  mul_nonneg ((seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t))
    (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _))

/-- Literal incoming-weighted bound in the proof of G.graft. -/
theorem graftTailWeight_bound {b : ℕ} (hb : 256 ^ 2 ≤ b) (t : ℕ) :
    graftTailWeight b t ≤
      4096 * seedCapacityConstant b * ((b : ℝ) ^ (3 / 2 : ℝ))⁻¹ *
        ((t : ℝ) + 1) ^ 3 * graftDecayRate ^ t := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hE := graftPrecision_ge_256 hb t
  have hcount : 0 < graftInitialCount b t := by unfold graftInitialCount; omega
  have hcountR : (0 : ℝ) < graftInitialCount b t := by exact_mod_cast hcount
  have hcube := graftInitialCount_cube_lower hb t
  have hrec : ((graftInitialCount b t : ℝ) ^ 3)⁻¹ ≤
      4096 * ((b : ℝ) ^ (3 / 2 : ℝ) * ((201 / 200 : ℝ) ^ (3 / 2 : ℝ)) ^ t)⁻¹ := by
    have hdiv : 1 / (graftInitialCount b t : ℝ) ^ 3 ≤
        4096 / ((b : ℝ) ^ (3 / 2 : ℝ) * ((201 / 200 : ℝ) ^ (3 / 2 : ℝ)) ^ t) := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      simpa only [one_mul] using hcube
    simpa only [div_eq_mul_inv, one_mul] using hdiv
  have hP : 0 ≤ seedCapacity b t :=
    (seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t)
  calc
    _ ≤ seedCapacity b t *
        (4096 * ((b : ℝ) ^ (3 / 2 : ℝ) * ((201 / 200 : ℝ) ^ (3 / 2 : ℝ)) ^ t)⁻¹) :=
      mul_le_mul_of_nonneg_left hrec hP
    _ = _ := by
      unfold seedCapacity graftDecayRate
      rw [div_pow]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

private theorem summable_graft_polynomial :
    Summable (fun t : ℕ => ((t : ℝ) + 1) ^ 3 * graftDecayRate ^ t) := by
  have hr : ‖graftDecayRate‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos graftDecayRate_bounds.1]
    exact graftDecayRate_bounds.2
  have hbase : Summable (fun t : ℕ => (t : ℝ) ^ 3 * graftDecayRate ^ t) :=
    summable_pow_mul_geometric_of_norm_lt_one 3 hr
  have hshift : Summable (fun t : ℕ =>
      ((t + 1 : ℕ) : ℝ) ^ 3 * graftDecayRate ^ (t + 1)) :=
    (summable_nat_add_iff 1).mpr hbase
  have hscaled := hshift.mul_left graftDecayRate⁻¹
  apply hscaled.congr
  intro t
  simp only [Nat.cast_add, Nat.cast_one]
  rw [pow_succ graftDecayRate t]
  calc
    _ = (((t : ℝ) + 1) ^ 3 * graftDecayRate ^ t) * (graftDecayRate⁻¹ * graftDecayRate) := by ac_rfl
    _ = _ := by rw [inv_mul_cancel₀ graftDecayRate_bounds.1.ne', mul_one]

/-- The actual growing incoming family still gives a summable sequence of graft tail factors. -/
theorem summable_graftTailWeight {b : ℕ} (hb : 256 ^ 2 ≤ b) :
    Summable (graftTailWeight b) := by
  have hs := summable_graft_polynomial.mul_left
    (4096 * seedCapacityConstant b * ((b : ℝ) ^ (3 / 2 : ℝ))⁻¹)
  apply Summable.of_nonneg_of_le (graftTailWeight_nonneg b)
    (fun t => graftTailWeight_bound hb t)
  simpa only [mul_assoc] using hs

/-- The full P_t B_0^(-3) factor tends to zero as the splice moves later. -/
theorem graftTailWeight_tendsto {b : ℕ} (hb : 256 ^ 2 ≤ b) :
    Tendsto (graftTailWeight b) atTop (𝓝 0) :=
  (summable_graftTailWeight hb).tendsto_atTop_zero

/-- The transition's P_t b_t^(-3) factor is bounded by the same complete-tail factor. -/
theorem graftTransitionWeight_le {b : ℕ} (hb : 256 ^ 2 ≤ b) (t : ℕ) :
    seedCapacity b t * ((seedSize b t : ℝ) ^ 3)⁻¹ ≤ graftTailWeight b t := by
  have hE := graftPrecision_ge_256 hb t
  have hcount : 0 < graftInitialCount b t := by unfold graftInitialCount; omega
  have hcountR : (0 : ℝ) < graftInitialCount b t := by exact_mod_cast hcount
  have hsize : graftInitialCount b t ≤ seedSize b t :=
    (Nat.div_le_self _ _).trans (Nat.sqrt_le_self _)
  have hcube : (graftInitialCount b t : ℝ) ^ 3 ≤ (seedSize b t : ℝ) ^ 3 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hsize) 3
  have hrec := one_div_le_one_div_of_le (by positivity) hcube
  have hP : 0 ≤ seedCapacity b t :=
    (seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t)
  simpa only [one_div, graftTailWeight] using mul_le_mul_of_nonneg_left hrec hP

/-- The transition error factor also tends to zero with the actual incoming family. -/
theorem graftTransitionWeight_tendsto {b : ℕ} (hb : 256 ^ 2 ≤ b) :
    Tendsto (fun t => seedCapacity b t * ((seedSize b t : ℝ) ^ 3)⁻¹) atTop (𝓝 0) := by
  apply squeeze_zero (fun t => ?_) (graftTransitionWeight_le hb) (graftTailWeight_tendsto hb)
  exact mul_nonneg ((seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t))
    (inv_nonneg.mpr (pow_nonneg (Nat.cast_nonneg _) _))

end WordCertDensity.Construction
