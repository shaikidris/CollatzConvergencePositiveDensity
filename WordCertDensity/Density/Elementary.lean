/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Counting.CoarseSources
import WordCertDensity.Counting.Radial
import WordCertDensity.Reference.FanElementary
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Table-free density from one fixed persistent score -/

namespace WordCertDensity.Density

open Filter
open scoped BigOperators Topology

/-- The small-score domain of the manuscript's counting conversion. -/
def SmallScore (W : ℝ) : Prop := 0 < W ∧ W ≤ 27 / (2 : ℝ) ^ 27

/-- The exact limiting harmonic capacity times the fan mean. -/
noncomputable def kappa : ℝ := (8 / 9) * (2 * Real.log 2)

/-- A positive bound fixed before every permitted clock for the specified target. -/
def TargetBound (target : ℕ) (d : ℝ) : Prop :=
  0 < d ∧ ∀ c : ℝ, criticalClock < c → d ≤ lowerNaturalDensity (goodTarget target c)

/-- The harmonic mass extracted with the elementary fan maximum. -/
noncomputable def elementaryMass (W : ℝ) (m : ℕ) : ℝ := 9 * W / (16 * (2 : ℝ) ^ m)

/-- A positive persistent score yields positive elementary harmonic mass. -/
theorem elementaryMass_pos {W : ℝ} (hW : 0 < W) (m : ℕ) : 0 < elementaryMass W m := by
  dsimp [elementaryMass]
  positivity

/-- The elementary fan cap charges exactly half the original score. -/
theorem elementaryMass_cap (W : ℝ) (m : ℕ) :
    ((8 / 9 : ℝ) * 2 ^ m) * elementaryMass W m = W / 2 := by
  dsimp [elementaryMass]
  field_simp
  ring

/-- The extracted harmonic mass stays below the nonnegative input score. -/
theorem elementaryMass_le_score {W : ℝ} (hW : 0 ≤ W) (m : ℕ) : elementaryMass W m ≤ W := by
  have hp : (1 : ℝ) ≤ 2 ^ m := by
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.zero_le m)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * 2 ^ m)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hp hW]

/-- The full allowed score range lies inside the radial theorem's mass domain. -/
theorem elementaryMass_domain {W : ℝ} (hW : SmallScore W) (m : ℕ) :
    0 ≤ elementaryMass W m ∧ elementaryMass W m ≤ Real.log (3 / 2) / 2 := by
  have hlog := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  norm_num at hlog
  have hsmall : W ≤ 1 / 8 := hW.2.trans (by norm_num)
  exact ⟨(elementaryMass_pos hW.1 m).le, by linarith [elementaryMass_le_score hW.1.le m]⟩

/-- Every clock above the reference ratio pays for each added halving. -/
theorem clock_pays_doubling {c : ℝ} (hc : criticalClock < c) : 1 ≤ c * Real.log 2 := by
  have hl : 0 < Real.log (4 / 3 : ℝ) := Real.log_pos (by norm_num)
  have h2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log (4 / 3 : ℝ) ≤ Real.log 2 :=
    Real.log_le_log (by norm_num) (by norm_num)
  have hbase : 1 ≤ criticalClock * Real.log 2 := by
    dsimp [criticalClock]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hl).mpr
    nlinarith
  exact hbase.trans (mul_le_mul_of_nonneg_right hc.le h2.le)

/-- Actual good-target sets are dyadically closed at every admitted ordinary clock. -/
theorem goodTarget_dyadicallyClosed {target : ℕ} {c : ℝ} (hc : criticalClock < c) :
    Counting.DyadicallyClosed (goodTarget target c) :=
  fun _ hx n => goodTarget_pow_two_mul (clock_pays_doubling hc) hx n

/-- Coarse marked mass becomes actual unmarked shell mass without a finite moment table. -/
theorem elementary_shellMass (target : ℕ) (W : ℝ) (hsrc : Sources.AllScaleSources target W)
    (c : ℝ) (hc : criticalClock < c) (m : ℕ) (hm : 2 ≤ m)
    (hpaid : kappa * Analytic.mixingError m < W / 2) :
    Counting.ShellMass (goodTarget target c) (elementaryMass W m) := by
  intro Λ hΛ
  let η := (W / 2 - kappa * Analytic.mixingError m) / 2
  have hη : 0 < η := by dsimp [η]; linarith
  obtain ⟨S, a, R, _, hfin⟩ := Counting.exists_coarse_sources target W hsrc c hc m hm η hη Λ hΛ
  have hk : 16 * Real.log 2 / 9 = kappa := by dsimp [kappa]; ring
  filter_upwards [hfin, eventually_gt_atTop (0 : ℝ)] with X hX hpos
  refine ⟨S X, a X, ?_, ?_⟩
  · intro x hx
    obtain ⟨ho, hG, hl, hu, ha, hau⟩ := hX.1 x hx
    exact ⟨ho, hG, hl, hu.trans (mul_lt_mul_of_pos_right hX.2.1 hpos), ha, hau⟩
  · have hupper : (∑ x ∈ S X, a X x * Reference.fan m (x : ZMod (3 ^ m))) ≤
        ((8 / 9 : ℝ) * 2 ^ m) * ∑ x ∈ S X, a X x := by
      calc
        _ ≤ ∑ x ∈ S X, a X x * ((8 / 9 : ℝ) * 2 ^ m) :=
          Finset.sum_le_sum (fun x hx => mul_le_mul_of_nonneg_left
            (Reference.fan_le_two_pow m _) (hX.1 x hx).2.2.2.2.1)
        _ = _ := by rw [← Finset.sum_mul]; ring
    have hmark := hX.2.2
    rw [hk] at hmark
    have hhalf : W / 2 ≤ ((8 / 9 : ℝ) * 2 ^ m) * ∑ x ∈ S X, a X x := by
      dsimp [η] at hmark
      linarith
    rw [← elementaryMass_cap W m] at hhalf
    exact le_of_mul_le_mul_left hhalf (by positivity)

/-- One fixed score and coarse level give the printed table-free constant for every clock. -/
theorem elementaryDensity (target : ℕ) (W : ℝ) (hW : SmallScore W)
    (hsrc : Sources.AllScaleSources target W) (m : ℕ) (hm : 2 ≤ m)
    (hpaid : kappa * Analytic.mixingError m < W / 2) :
    TargetBound target (4 * W / (25 * (2 : ℝ) ^ m)) := by
  have hWpos := hW.1
  refine ⟨by positivity, ?_⟩
  intro c hc
  have hd := Counting.radialConversion (goodTarget target c) (elementaryMass W m)
    (goodTarget_dyadicallyClosed hc) (elementaryMass_domain hW m).1
    (elementaryMass_domain hW m).2 (elementary_shellMass target W hsrc c hc m hm hpaid)
  have hlinear := (Counting.radial_ge_linear (elementaryMass W m)).trans hd
  have he : 64 * elementaryMass W m / 225 = 4 * W / (25 * (2 : ℝ) ^ m) := by
    dsimp [elementaryMass]
    ring
  rwa [he] at hlinear

end WordCertDensity.Density
