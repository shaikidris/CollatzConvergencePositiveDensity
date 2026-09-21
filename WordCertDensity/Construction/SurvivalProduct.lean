/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.SurvivalGuards
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Summable survival loss and the finite/infinite product certificate -/

@[expose] public section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace WordCertDensity.Construction

private theorem integral_Ioi_add_right (f : ℝ → ℝ) (a : ℝ) :
    (∫ x in Set.Ioi a, f x) = ∫ t in Set.Ioi 0, f (t + a) := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  rw [← MeasureTheory.integral_add_right_eq_self ((Set.Ioi a).indicator f) a]
  apply integral_congr_ae
  filter_upwards [] with x
  have hmem : x + a ∈ Set.Ioi a ↔ x ∈ Set.Ioi 0 := by
    simp only [Set.mem_Ioi]
    constructor <;> intro h <;> linarith
  simp only [Set.indicator_apply, hmem]

private theorem exp_moment_integrable_zero :
    IntegrableOn (fun t : ℝ => Real.exp (-t)) (Set.Ioi 0) := by
  simpa using (Real.GammaIntegral_convergent (s := (1 : ℝ)) (by norm_num))

private theorem exp_moment_integrable_one :
    IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Set.Ioi 0) := by
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, mul_comm] using
    (Real.GammaIntegral_convergent (s := (2 : ℝ)) (by norm_num))

private theorem exp_moment_integrable_two :
    IntegrableOn (fun t : ℝ => t ^ 2 * Real.exp (-t)) (Set.Ioi 0) := by
  simpa only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two, mul_comm] using
    (Real.GammaIntegral_convergent (s := (3 : ℝ)) (by norm_num))

private theorem integral_exp_moment_zero :
    (∫ t : ℝ in Set.Ioi 0, Real.exp (-t)) = 1 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (1 : ℝ)) (r := (1 : ℝ)) (by norm_num) (by norm_num)
  simpa [Real.Gamma_one] using h

private theorem integral_exp_moment_one :
    (∫ t : ℝ in Set.Ioi 0, t * Real.exp (-t)) = 1 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2 : ℝ)) (r := (1 : ℝ)) (by norm_num) (by norm_num)
  have hg : Real.Gamma 2 = 1 := by
    convert Real.Gamma_nat_eq_factorial 1 <;> norm_num
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, one_div, inv_one, Real.one_rpow, one_mul, mul_one, neg_one_mul, mul_comm, hg] using h

private theorem integral_exp_moment_two :
    (∫ t : ℝ in Set.Ioi 0, t ^ 2 * Real.exp (-t)) = 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (3 : ℝ)) (r := (1 : ℝ)) (by norm_num) (by norm_num)
  have hg : Real.Gamma 3 = 2 := by
    convert Real.Gamma_nat_eq_factorial 2 <;> norm_num
  simpa only [show (3 : ℝ) - 1 = 2 by norm_num, Real.rpow_two, one_div, inv_one, Real.one_rpow, one_mul, mul_one, neg_one_mul, mul_comm, hg] using h

private theorem reciprocal_quadratic_bound {u t : ℝ} (hu : 0 < u) (ht : 0 ≤ t) :
    1 / (u + t) ≤ 1 / u - t / u ^ 2 + t ^ 2 / u ^ 3 := by
  apply (div_le_iff₀ (add_pos_of_pos_of_nonneg hu ht)).2
  have hu0 : u ≠ 0 := hu.ne'
  field_simp [hu0]
  nlinarith [sq_nonneg t]



/-- Continuous kernel behind the discrete survival deficit. -/
noncomputable def survivalKernel (t : ℝ) : ℝ :=
  Real.exp (-survivalDeficitExponent * survivalDeficitRate ^ t)

private theorem survivalDeficitExponent_pos : 0 < survivalDeficitExponent := by
  norm_num [survivalDeficitExponent]

private theorem survivalKernel_pos (t : ℝ) : 0 < survivalKernel t :=
  Real.exp_pos _

private theorem survivalKernel_antitone : Antitone survivalKernel := by
  intro x y hxy
  unfold survivalKernel
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left
    ((Real.strictMono_rpow_of_base_gt_one one_lt_survivalDeficitRate).monotone hxy)
    (neg_nonpos.mpr survivalDeficitExponent_pos.le)

private theorem survivalKernel_integrableOn :
    IntegrableOn survivalKernel (Set.Ioi 0) := by
  let a : ℝ := survivalDeficitExponent / 504
  have ha : 0 < a := div_pos survivalDeficitExponent_pos (by norm_num)
  have hmajor := exp_neg_integrableOn_Ioi (0 : ℝ) ha
  apply hmajor.mono'
  · apply Continuous.aestronglyMeasurable
    unfold survivalKernel
    exact Real.continuous_exp.comp
      (continuous_const.mul (Real.continuous_const_rpow survivalDeficitRate_pos.ne'))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := ht.le
    have hlogmul : t / 504 ≤ Real.log survivalDeficitRate * t := by
      simpa [div_eq_mul_inv, mul_comm] using
        mul_le_mul_of_nonneg_right survival_log_rate_lower.le ht0
    have hexp : Real.log survivalDeficitRate * t ≤
        Real.exp (Real.log survivalDeficitRate * t) := by
      linarith [Real.add_one_le_exp (Real.log survivalDeficitRate * t)]
    have hrpow : t / 504 ≤ survivalDeficitRate ^ t := by
      rw [Real.rpow_def_of_pos survivalDeficitRate_pos]
      exact hlogmul.trans hexp
    have hscaled : a * t ≤ survivalDeficitExponent * survivalDeficitRate ^ t := by
      calc
        survivalDeficitExponent / 504 * t =
            survivalDeficitExponent * (t / 504) := by ring
        _ ≤ survivalDeficitExponent * survivalDeficitRate ^ t :=
          mul_le_mul_of_nonneg_left hrpow survivalDeficitExponent_pos.le
    rw [Real.norm_eq_abs, abs_of_pos (survivalKernel_pos t)]
    unfold survivalKernel
    exact Real.exp_le_exp.mpr (by simpa only [neg_mul] using neg_le_neg hscaled)



private theorem integral_survivalKernel_eq :
    (∫ t in Set.Ioi 0, survivalKernel t) =
      (Real.log survivalDeficitRate)⁻¹ *
        ∫ x in Set.Ioi survivalDeficitExponent, x⁻¹ * Real.exp (-x) := by
  have hlog : 0 < Real.log survivalDeficitRate :=
    Real.log_pos one_lt_survivalDeficitRate
  have hlinear := MeasureTheory.integral_comp_mul_left_Ioi
    (fun y : ℝ => Real.exp
      (-survivalDeficitExponent * Real.exp y)) 0 hlog
  have hlinear' :
      (∫ t in Set.Ioi 0, survivalKernel t) =
        (Real.log survivalDeficitRate)⁻¹ *
          ∫ y in Set.Ioi 0,
            Real.exp (-survivalDeficitExponent * Real.exp y) := by
    simpa [survivalKernel, Real.rpow_def_of_pos survivalDeficitRate_pos] using hlinear
  have hexp := MeasureTheory.integral_comp_exp_Ioi
    (fun x : ℝ => x⁻¹ * Real.exp (-survivalDeficitExponent * x)) 0
  have hexp' :
      (∫ y in Set.Ioi 0,
          Real.exp (-survivalDeficitExponent * Real.exp y)) =
        ∫ x in Set.Ioi 1,
          x⁻¹ * Real.exp (-survivalDeficitExponent * x) := by
    calc
      (∫ y in Set.Ioi 0,
          Real.exp (-survivalDeficitExponent * Real.exp y)) =
          ∫ y in Set.Ioi 0,
            Real.exp y * ((Real.exp y)⁻¹ *
              Real.exp (-survivalDeficitExponent * Real.exp y)) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro y _
            field_simp [Real.exp_ne_zero]
      _ = ∫ x in Set.Ioi (Real.exp 0),
          x⁻¹ * Real.exp (-survivalDeficitExponent * x) := by
            simpa only [smul_eq_mul] using hexp
      _ = ∫ x in Set.Ioi 1,
          x⁻¹ * Real.exp (-survivalDeficitExponent * x) := by
            rw [Real.exp_zero]
  have hscale := MeasureTheory.integral_comp_mul_left_Ioi'
    (fun z : ℝ => z⁻¹ * Real.exp (-z)) 1 survivalDeficitExponent_pos
  have hscale' :
      (∫ x in Set.Ioi 1,
          x⁻¹ * Real.exp (-survivalDeficitExponent * x)) =
        ∫ z in Set.Ioi survivalDeficitExponent, z⁻¹ * Real.exp (-z) := by
    calc
      (∫ x in Set.Ioi 1,
          x⁻¹ * Real.exp (-survivalDeficitExponent * x)) =
          ∫ x in Set.Ioi 1,
            survivalDeficitExponent *
              ((survivalDeficitExponent * x)⁻¹ *
                Real.exp (-(survivalDeficitExponent * x))) := by
            apply setIntegral_congr_fun measurableSet_Ioi
            intro x hx
            have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
            field_simp [survivalDeficitExponent_pos.ne', hx0]
      _ = survivalDeficitExponent *
          ∫ x in Set.Ioi 1,
            (survivalDeficitExponent * x)⁻¹ *
              Real.exp (-(survivalDeficitExponent * x)) := by
            rw [MeasureTheory.integral_const_mul]
      _ = ∫ z in Set.Ioi survivalDeficitExponent,
          z⁻¹ * Real.exp (-z) := by
            simpa only [smul_eq_mul, mul_one] using hscale
  rw [hlinear', hexp', hscale']



private noncomputable def survivalIntegralMajorant (u t : ℝ) : ℝ :=
  Real.exp (-u) *
    ((1 / u) * Real.exp (-t) -
      (1 / u ^ 2) * (t * Real.exp (-t)) +
      (1 / u ^ 3) * (t ^ 2 * Real.exp (-t)))

private theorem survivalIntegralMajorant_integrableOn {u : ℝ} :
    IntegrableOn (survivalIntegralMajorant u) (Set.Ioi 0) := by
  have h0 := exp_moment_integrable_zero.const_mul (1 / u)
  have h1 := exp_moment_integrable_one.const_mul (1 / u ^ 2)
  have h2 := exp_moment_integrable_two.const_mul (1 / u ^ 3)
  exact ((h0.sub h1).add h2).const_mul (Real.exp (-u))

private theorem integral_survivalIntegralMajorant {u : ℝ} :
    (∫ t in Set.Ioi 0, survivalIntegralMajorant u t) =
      Real.exp (-u) * (1 / u - 1 / u ^ 2 + 2 / u ^ 3) := by
  have h0 := exp_moment_integrable_zero.const_mul (1 / u)
  have h1 := exp_moment_integrable_one.const_mul (1 / u ^ 2)
  have h2 := exp_moment_integrable_two.const_mul (1 / u ^ 3)
  unfold survivalIntegralMajorant
  rw [MeasureTheory.integral_const_mul]
  congr 1
  calc
    (∫ t in Set.Ioi 0,
        (1 / u) * Real.exp (-t) -
          (1 / u ^ 2) * (t * Real.exp (-t)) +
          (1 / u ^ 3) * (t ^ 2 * Real.exp (-t))) =
        (∫ t in Set.Ioi 0,
          (1 / u) * Real.exp (-t) -
            (1 / u ^ 2) * (t * Real.exp (-t))) +
        ∫ t in Set.Ioi 0,
          (1 / u ^ 3) * (t ^ 2 * Real.exp (-t)) :=
      MeasureTheory.integral_add (h0.sub h1) h2
    _ = ((∫ t in Set.Ioi 0, (1 / u) * Real.exp (-t)) -
          ∫ t in Set.Ioi 0, (1 / u ^ 2) * (t * Real.exp (-t))) +
        ∫ t in Set.Ioi 0, (1 / u ^ 3) * (t ^ 2 * Real.exp (-t)) := by
      rw [MeasureTheory.integral_sub h0 h1]
    _ = (1 / u) * (∫ t in Set.Ioi 0, Real.exp (-t)) -
          (1 / u ^ 2) * (∫ t in Set.Ioi 0, t * Real.exp (-t)) +
          (1 / u ^ 3) * (∫ t in Set.Ioi 0, t ^ 2 * Real.exp (-t)) := by
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
        MeasureTheory.integral_const_mul]
    _ = 1 / u - 1 / u ^ 2 + 2 / u ^ 3 := by
      rw [integral_exp_moment_zero, integral_exp_moment_one,
        integral_exp_moment_two]
      ring

private theorem shifted_reciprocal_integrableOn {u : ℝ} (hu : 0 < u) :
    IntegrableOn (fun t : ℝ => (t + u)⁻¹ * Real.exp (-(t + u))) (Set.Ioi 0) := by
  have hmajor := exp_moment_integrable_zero.const_mul (Real.exp (-u) / u)
  apply hmajor.mono'
  · exact (by fun_prop : Measurable fun t : ℝ =>
      (t + u)⁻¹ * Real.exp (-(t + u))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := ht.le
    have htu : 0 < t + u := add_pos_of_nonneg_of_pos ht0 hu
    have hrec : (t + u)⁻¹ ≤ u⁻¹ := inv_anti₀ hu (by linarith)
    have hexp : Real.exp (-(t + u)) = Real.exp (-u) * Real.exp (-t) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [Real.norm_eq_abs, abs_of_pos (mul_pos (inv_pos.mpr htu) (Real.exp_pos _)),
      hexp]
    calc
      (t + u)⁻¹ * (Real.exp (-u) * Real.exp (-t)) ≤
          u⁻¹ * (Real.exp (-u) * Real.exp (-t)) :=
        mul_le_mul_of_nonneg_right hrec (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
      _ = Real.exp (-u) / u * Real.exp (-t) := by ring

private theorem shifted_reciprocal_le_majorant {u t : ℝ} (hu : 0 < u) (ht : 0 ≤ t) :
    (t + u)⁻¹ * Real.exp (-(t + u)) ≤ survivalIntegralMajorant u t := by
  have hrec := reciprocal_quadratic_bound hu ht
  have hfac : 0 ≤ Real.exp (-u) * Real.exp (-t) :=
    mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  have hmul := mul_le_mul_of_nonneg_left hrec hfac
  have hexp : Real.exp (-(t + u)) = Real.exp (-u) * Real.exp (-t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  unfold survivalIntegralMajorant
  calc
    (t + u)⁻¹ * (Real.exp (-u) * Real.exp (-t)) =
        (Real.exp (-u) * Real.exp (-t)) * (1 / (u + t)) := by
      rw [one_div, add_comm]
      ring
    _ ≤ (Real.exp (-u) * Real.exp (-t)) *
        (1 / u - t / u ^ 2 + t ^ 2 / u ^ 3) := hmul
    _ = Real.exp (-u) *
        ((1 / u) * Real.exp (-t) -
          (1 / u ^ 2) * (t * Real.exp (-t)) +
          (1 / u ^ 3) * (t ^ 2 * Real.exp (-t))) := by ring

private theorem reciprocal_exp_integral_le {u : ℝ} (hu : 0 < u) :
    (∫ x in Set.Ioi u, x⁻¹ * Real.exp (-x)) ≤
      Real.exp (-u) * (1 / u - 1 / u ^ 2 + 2 / u ^ 3) := by
  rw [integral_Ioi_add_right (fun x : ℝ => x⁻¹ * Real.exp (-x)) u]
  have hleft := shifted_reciprocal_integrableOn hu
  have hright := survivalIntegralMajorant_integrableOn (u := u)
  calc
    (∫ t in Set.Ioi 0, (t + u)⁻¹ * Real.exp (-(t + u))) ≤
        ∫ t in Set.Ioi 0, survivalIntegralMajorant u t := by
      apply MeasureTheory.integral_mono_ae hleft hright
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact shifted_reciprocal_le_majorant hu ht.le
    _ = Real.exp (-u) * (1 / u - 1 / u ^ 2 + 2 / u ^ 3) :=
      integral_survivalIntegralMajorant (u := u)



/-- The continuous kernel has the strict integral bound used by the survival budget. -/
theorem integral_survivalKernel_lt :
    (∫ t in Set.Ioi 0, survivalKernel t) <
      504 * Real.exp (-survivalDeficitExponent) *
        (1 / survivalDeficitExponent - 1 / survivalDeficitExponent ^ 2 +
          2 / survivalDeficitExponent ^ 3) := by
  have hlog : 0 < Real.log survivalDeficitRate :=
    Real.log_pos one_lt_survivalDeficitRate
  have hinv : (Real.log survivalDeficitRate)⁻¹ < 504 := by
    have h := (inv_lt_inv₀ hlog (by norm_num : (0 : ℝ) < 1 / 504)).2
      survival_log_rate_lower
    norm_num at h ⊢
    exact h
  have hrec := reciprocal_exp_integral_le survivalDeficitExponent_pos
  have hpoly : 0 <
      1 / survivalDeficitExponent - 1 / survivalDeficitExponent ^ 2 +
        2 / survivalDeficitExponent ^ 3 := by
    norm_num [survivalDeficitExponent]
  have hbound : 0 < Real.exp (-survivalDeficitExponent) *
      (1 / survivalDeficitExponent - 1 / survivalDeficitExponent ^ 2 +
        2 / survivalDeficitExponent ^ 3) := mul_pos (Real.exp_pos _) hpoly
  rw [integral_survivalKernel_eq]
  calc
    (Real.log survivalDeficitRate)⁻¹ *
        (∫ x in Set.Ioi survivalDeficitExponent, x⁻¹ * Real.exp (-x)) ≤
      (Real.log survivalDeficitRate)⁻¹ *
        (Real.exp (-survivalDeficitExponent) *
          (1 / survivalDeficitExponent - 1 / survivalDeficitExponent ^ 2 +
            2 / survivalDeficitExponent ^ 3)) :=
      mul_le_mul_of_nonneg_left hrec (inv_nonneg.mpr hlog.le)
    _ < 504 *
        (Real.exp (-survivalDeficitExponent) *
          (1 / survivalDeficitExponent - 1 / survivalDeficitExponent ^ 2 +
            2 / survivalDeficitExponent ^ 3)) :=
      mul_lt_mul_of_pos_right hinv hbound
    _ = 504 * Real.exp (-survivalDeficitExponent) *
        (1 / survivalDeficitExponent - 1 / survivalDeficitExponent ^ 2 +
          2 / survivalDeficitExponent ^ 3) := by ring

/-- The discrete survival deficits form a summable nonnegative sequence. -/
theorem summable_survivalDeficit : Summable survivalDeficit := by
  have hk : Summable (fun n : ℕ => survivalKernel n) :=
    (survivalKernel_antitone.antitoneOn (Set.Ici 0)).summable_of_integrableOn_Ioi_zero
      survivalKernel_integrableOn (fun x _ => (survivalKernel_pos x).le)
  have htwo := hk.mul_left (2 : ℝ)
  change Summable (fun j : ℕ =>
    2 * Real.exp (-survivalDeficitExponent * survivalDeficitRate ^ j))
  simpa [survivalKernel, Real.rpow_natCast, neg_mul] using htwo

/-- The entire rejected reference mass fits strictly inside one twenty-fifth. -/
theorem tsum_survivalDeficit_lt : (∑' j : ℕ, survivalDeficit j) < 1 / 25 := by
  have htest :=
    (survivalKernel_antitone.antitoneOn (Set.Ici 0)).tsum_le_integral
      survivalKernel_integrableOn (fun x _ => (survivalKernel_pos x).le)
  have hint := integral_survivalKernel_lt
  have hkernel0 : survivalKernel 0 = Real.exp (-survivalDeficitExponent) := by
    simp [survivalKernel]
  have hdefeq : (∑' j : ℕ, survivalDeficit j) =
      2 * ∑' j : ℕ, survivalKernel j := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro j
    simp [survivalDeficit, survivalKernel, Real.rpow_natCast]
  have hanalytic : (∑' j : ℕ, survivalDeficit j) <
      2 * Real.exp (-survivalDeficitExponent) *
        (1 + 504 *
          (1 / survivalDeficitExponent - 1 / survivalDeficitExponent ^ 2 +
            2 / survivalDeficitExponent ^ 3)) := by
    rw [hdefeq]
    have hklt : (∑' j : ℕ, survivalKernel j) <
        Real.exp (-survivalDeficitExponent) +
          504 * Real.exp (-survivalDeficitExponent) *
            (1 / survivalDeficitExponent - 1 / survivalDeficitExponent ^ 2 +
              2 / survivalDeficitExponent ^ 3) := by
      rw [hkernel0] at htest
      nlinarith
    nlinarith
  have hexpneg : Real.exp (-survivalDeficitExponent) < 1 / 2920 := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2920) survival_exp_guard
  have hfactor : 0 < 1 + 504 *
      (1 / survivalDeficitExponent - 1 / survivalDeficitExponent ^ 2 +
        2 / survivalDeficitExponent ^ 3) := by
    norm_num [survivalDeficitExponent]
  have hpoly := survival_integral_factor_lt
  have hbudget := survival_rational_budget
  calc
    (∑' j : ℕ, survivalDeficit j) <
        2 * Real.exp (-survivalDeficitExponent) *
          (1 + 504 *
            (1 / survivalDeficitExponent - 1 / survivalDeficitExponent ^ 2 +
              2 / survivalDeficitExponent ^ 3)) := hanalytic
    _ < 2 * (1 / 2920) *
          (1 + 504 *
            (1 / survivalDeficitExponent - 1 / survivalDeficitExponent ^ 2 +
              2 / survivalDeficitExponent ^ 3)) := by
      exact mul_lt_mul_of_pos_right
        (mul_lt_mul_of_pos_left hexpneg (by norm_num)) hfactor
    _ < (2 / 2920) * (1 + 504 * (227 / 2000)) := by
      have : 1 + 504 *
          (1 / survivalDeficitExponent - 1 / survivalDeficitExponent ^ 2 +
            2 / survivalDeficitExponent ^ 3) < 1 + 504 * (227 / 2000) := by
        nlinarith
      have hmul := mul_lt_mul_of_pos_left this (by norm_num : (0 : ℝ) < 2 / 2920)
      simpa only [div_eq_mul_inv, one_mul, mul_assoc] using hmul
    _ = 14551 / 365000 := hbudget.1
    _ < 1 / 25 := hbudget.2



/-- The actual unconditioned reference success probability at stage `j`. -/
noncomputable def survivalSuccess (j : ℕ) : ℝ :=
  Reference.stoppingMass (seedWords (seedSize survivalSeedSize j))

/-- The finite survival product through the first `N` seed stages. -/
noncomputable def survivalPartialProduct (N : ℕ) : ℝ :=
  ∏ j ∈ Finset.range N, survivalSuccess j

/-- The decreasing-limit interpretation of the infinite survival product. -/
noncomputable def survivalProduct : ℝ :=
  ⨅ N : ℕ, survivalPartialProduct N

/-- Every stage success is a genuine number in the unit interval. -/
theorem survivalSuccess_bounds (j : ℕ) :
    0 ≤ survivalSuccess j ∧ survivalSuccess j ≤ 1 := by
  simpa [survivalSuccess] using seedWords_mass_bounds (seedSize survivalSeedSize j)

/-- Every stage deficit is nonnegative. -/
theorem survivalDeficit_nonneg (j : ℕ) : 0 ≤ survivalDeficit j := by
  exact mul_nonneg (by norm_num) (Real.exp_pos _).le

/-- The actual stage failure is trapped between zero and its summable majorant. -/
theorem survivalSuccess_failure_bounds (j : ℕ) :
    0 ≤ 1 - survivalSuccess j ∧ 1 - survivalSuccess j ≤ survivalDeficit j := by
  constructor
  · exact sub_nonneg.mpr (survivalSuccess_bounds j).2
  · simpa [survivalSuccess] using seedWords_failure_le_survivalDeficit j

/-- Every finite actual failure sum already fits the strict rational budget. -/
theorem survivalSuccess_failure_sum_lt (N : ℕ) :
    (∑ j ∈ Finset.range N, (1 - survivalSuccess j)) < 1 / 25 := by
  calc
    (∑ j ∈ Finset.range N, (1 - survivalSuccess j)) ≤
        ∑ j ∈ Finset.range N, survivalDeficit j := by
      exact Finset.sum_le_sum fun j _ => (survivalSuccess_failure_bounds j).2
    _ ≤ ∑' j : ℕ, survivalDeficit j :=
      summable_survivalDeficit.sum_le_tsum (Finset.range N)
        (fun j _ => survivalDeficit_nonneg j)
    _ < 1 / 25 := tsum_survivalDeficit_lt

private theorem one_sub_sum_one_sub_le_prod
    (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j ∧ p j ≤ 1) (N : ℕ) :
    1 - (∑ j ∈ Finset.range N, (1 - p j)) ≤
      ∏ j ∈ Finset.range N, p j := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.prod_range_succ]
      have hpN := hp N
      have hsum : 0 ≤ ∑ j ∈ Finset.range N, (1 - p j) :=
        Finset.sum_nonneg fun j _ => sub_nonneg.mpr (hp j).2
      have hscaled := mul_le_mul_of_nonneg_right ih hpN.1
      have hcorrection := mul_nonneg hsum (sub_nonneg.mpr hpN.2)
      nlinarith

/-- Every finite survival product is strictly larger than `24/25`. -/
theorem survivalFraction_lt_partialProduct (N : ℕ) :
    survivalFraction < survivalPartialProduct N := by
  have hprod := one_sub_sum_one_sub_le_prod survivalSuccess survivalSuccess_bounds N
  have hsum := survivalSuccess_failure_sum_lt N
  unfold survivalFraction survivalPartialProduct
  nlinarith

/-- Finite survival products are nonnegative. -/
theorem survivalPartialProduct_nonneg (N : ℕ) : 0 ≤ survivalPartialProduct N := by
  unfold survivalPartialProduct
  exact Finset.prod_nonneg fun j _ => (survivalSuccess_bounds j).1

/-- Adding one more stage can only decrease the finite survival product. -/
theorem survivalPartialProduct_succ_le (N : ℕ) :
    survivalPartialProduct (N + 1) ≤ survivalPartialProduct N := by
  rw [survivalPartialProduct, Finset.prod_range_succ]
  exact mul_le_of_le_one_right (survivalPartialProduct_nonneg N)
    (survivalSuccess_bounds N).2

/-- The finite survival products form a decreasing sequence. -/
theorem survivalPartialProduct_antitone : Antitone survivalPartialProduct :=
  antitone_nat_of_succ_le survivalPartialProduct_succ_le

/-- The finite survival products converge to their infimum. -/
theorem survivalPartialProduct_tendsto :
    Tendsto survivalPartialProduct atTop (nhds survivalProduct) := by
  unfold survivalProduct
  apply tendsto_atTop_ciInf survivalPartialProduct_antitone
  refine ⟨0, ?_⟩
  rintro x ⟨N, rfl⟩
  exact survivalPartialProduct_nonneg N

/-- The infinite survival product retains at least `24/25` of the reference mass. -/
theorem survivalFraction_le_product : survivalFraction ≤ survivalProduct := by
  unfold survivalProduct
  exact le_ciInf fun N => (survivalFraction_lt_partialProduct N).le

/-- The complete finite/infinite survival certificate. -/
theorem survival_certificate :
    (∀ N : ℕ, survivalFraction < survivalPartialProduct N) ∧
      Tendsto survivalPartialProduct atTop (nhds survivalProduct) ∧
      survivalFraction ≤ survivalProduct :=
  ⟨survivalFraction_lt_partialProduct, survivalPartialProduct_tendsto,
    survivalFraction_le_product⟩

end WordCertDensity.Construction
