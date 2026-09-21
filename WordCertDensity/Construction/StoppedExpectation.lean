/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.StoppedMoment
public import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Actual stopped expectations and finite-precision error bounds

Expectations retain the original normalized stopped weights. Exponential
comparison proves absolute summability before any use of linearity. Finite
precision means total valuation strictly below the cutoff, without rescaling.
The exact predictable-increment identity is a separate obligation.
-/

@[expose] public section

namespace WordCertDensity.Construction

open scoped Classical ENNReal

/-- Real weighted sum under the original stopped law; linearity requires summability. -/
noncomputable def stoppedExpectation (F : ValuationWord → ℝ) : ℝ :=
  ∑' w, (stoppedPMF w).toReal * F w

/-- Original finite subexpectation at strict total-valuation precision. -/
noncomputable def stoppedPrecisionExpectation (E : ℕ) (F : ValuationWord → ℝ) : ℝ :=
  ∑ w ∈ stoppedWords E, (1 / (2 : ℝ) ^ w.total) * F w

private theorem summable_real_weights : Summable (fun w => (stoppedPMF w).toReal) :=
  ENNReal.summable_toReal (by rw [stoppedPMF.tsum_coe]; exact ENNReal.one_ne_top)

private theorem real_weights_sum : (∑' w, (stoppedPMF w).toReal) = 1 := by
  rw [← ENNReal.tsum_toReal_eq (f := stoppedPMF) (fun _ => PMF.apply_ne_top _ _),
    stoppedPMF.tsum_coe]
  rfl

/-- The full stopped exponential moment is summable as a real weighted series. -/
theorem summable_stopped_expMoment :
    Summable (fun w => (stoppedPMF w).toReal *
      Real.exp ((1 / 1000 : ℝ) * w.ordinaryCost)) := by
  have h := ENNReal.summable_toReal stopped_ordinaryExpMoment_lt_top.ne
  apply h.congr
  intro w
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- The real exponential moment has the same explicit geometric upper bound. -/
theorem stopped_expMoment_le :
    stoppedExpectation (fun w => Real.exp ((1 / 1000 : ℝ) * w.ordinaryCost)) ≤
      stoppedMomentBound := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top stopped_ordinaryExpMoment_le
  rw [ENNReal.toReal_ofReal stoppedMomentBound_pos.le] at h
  refine le_trans (le_of_eq ?_) h
  unfold stoppedExpectation
  rw [ENNReal.tsum_toReal_eq (fun w => ENNReal.mul_ne_top (PMF.apply_ne_top _ _)
    ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro w
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le]

/-- Exponential domination supplies absolute summability under the stopped law. -/
theorem summable_stopped_of_abs_le_exp {F : ValuationWord → ℝ} {C : ℝ}
    (hF : ∀ w, |F w| ≤ C * Real.exp ((1 / 1000 : ℝ) * w.ordinaryCost)) :
    Summable (fun w => (stoppedPMF w).toReal * F w) := by
  refine (summable_stopped_expMoment.mul_left C).of_norm_bounded (fun w => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  have h := mul_le_mul_of_nonneg_left (hF w) (ENNReal.toReal_nonneg :
    0 ≤ (stoppedPMF w).toReal)
  nlinarith

private theorem cost_le_exp (w : ValuationWord) :
    (w.ordinaryCost : ℝ) ≤ 2000 * Real.exp ((1 / 2000 : ℝ) * w.ordinaryCost) := by
  have h := Real.add_one_le_exp ((1 / 2000 : ℝ) * w.ordinaryCost)
  linarith

/-- Every cost-dominated observable is absolutely integrable under the stopped law. -/
theorem summable_stopped_of_abs_le_cost {F : ValuationWord → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hF : ∀ w, |F w| ≤ C * w.ordinaryCost) :
    Summable (fun w => (stoppedPMF w).toReal * F w) := by
  apply summable_stopped_of_abs_le_exp (C := 2000 * C)
  intro w
  have he : Real.exp ((1 / 2000 : ℝ) * w.ordinaryCost) ≤
      Real.exp ((1 / 1000 : ℝ) * w.ordinaryCost) := by
    apply Real.exp_le_exp.mpr
    have hR : (0 : ℝ) ≤ w.ordinaryCost := Nat.cast_nonneg _
    linarith
  have h := mul_le_mul_of_nonneg_left (cost_le_exp w) hC
  have h' := mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 2000 * C)
  nlinarith [hF w]

/-- Constant observables have their stated expectation without conditioning. -/
theorem stoppedExpectation_const (c : ℝ) : stoppedExpectation (fun _ => c) = c := by
  rw [stoppedExpectation, tsum_mul_right, real_weights_sum, one_mul]

/-- The stopped ordinary cost is integrable. -/
theorem summable_stopped_cost :
    Summable (fun w => (stoppedPMF w).toReal * (w.ordinaryCost : ℝ)) := by
  apply summable_stopped_of_abs_le_cost (C := 1) (by norm_num)
  intro w
  simp [abs_of_nonneg ((Nat.cast_nonneg w.ordinaryCost : (0 : ℝ) ≤ w.ordinaryCost))]

/-- The stopped total valuation is integrable. -/
theorem summable_stopped_total :
    Summable (fun w => (stoppedPMF w).toReal * (w.total : ℝ)) := by
  apply summable_stopped_of_abs_le_cost (C := 1) (by norm_num)
  intro w
  simp only [abs_of_nonneg ((Nat.cast_nonneg w.total : (0 : ℝ) ≤ w.total)), one_mul,
    ValuationWord.ordinaryCost, Nat.cast_add]
  exact le_add_of_nonneg_right (Nat.cast_nonneg w.length : (0 : ℝ) ≤ w.length)

/-- The stopped depth is integrable. -/
theorem summable_stopped_depth :
    Summable (fun w => (stoppedPMF w).toReal * (w.length : ℝ)) := by
  apply summable_stopped_of_abs_le_cost (C := 1) (by norm_num)
  intro w
  simp only [abs_of_nonneg ((Nat.cast_nonneg w.length : (0 : ℝ) ≤ w.length)), one_mul,
    ValuationWord.ordinaryCost, Nat.cast_add]
  exact le_add_of_nonneg_left (Nat.cast_nonneg w.total : (0 : ℝ) ≤ w.total)

/-- The stopped displacement is absolutely integrable, including its signed formula. -/
theorem summable_stopped_displacement :
    Summable (fun w => (stoppedPMF w).toReal * displacement w) :=
  summable_stopped_of_abs_le_cost (by norm_num : (0 : ℝ) ≤ 2) abs_displacement_le_cost

/-- Ordinary cost is valuation plus depth also at the level of actual expectations. -/
theorem stoppedExpectation_cost :
    stoppedExpectation (fun w => w.ordinaryCost) =
      stoppedExpectation (fun w => w.total) + stoppedExpectation (fun w => w.length) := by
  simp only [stoppedExpectation, ValuationWord.ordinaryCost, Nat.cast_add, mul_add]
  exact summable_stopped_total.tsum_add summable_stopped_depth

/-- Displacement has its exact linear expectation before using the Wald identity. -/
theorem stoppedExpectation_displacement :
    stoppedExpectation displacement = stoppedExpectation (fun w => w.total) -
      Head.logRatio * stoppedExpectation (fun w => w.length) := by
  have h := summable_stopped_depth.mul_left Head.logRatio
  calc
    stoppedExpectation displacement = ∑' w,
        ((stoppedPMF w).toReal * (w.total : ℝ) -
          Head.logRatio * ((stoppedPMF w).toReal * (w.length : ℝ))) := by
      apply tsum_congr
      intro w
      simp only [displacement]
      ring
    _ = _ := by rw [summable_stopped_total.tsum_sub h, tsum_mul_left]; rfl

/-- Every admitted stopped word has displacement at least three, hence so does its mean. -/
theorem stoppedExpectation_displacement_lower : 3 ≤ stoppedExpectation displacement := by
  rw [← stoppedExpectation_const 3]
  apply Summable.tsum_le_tsum _ (summable_real_weights.mul_right 3)
    summable_stopped_displacement
  intro w
  by_cases hw : FirstCrossing w
  · exact mul_le_mul_of_nonneg_left ((firstCrossing_iff w).mp hw).1
      ENNReal.toReal_nonneg
  · rw [stoppedPMF_apply_of_not_firstCrossing hw]
    simp

private theorem precision_eq_weighted (E : ℕ) (F : ValuationWord → ℝ) :
    stoppedPrecisionExpectation E F =
      ∑ w ∈ stoppedWords E, (stoppedPMF w).toReal * F w := by
  apply Finset.sum_congr rfl
  intro w hw
  rw [stoppedPMF_toReal ((mem_stoppedWords w E).mp hw).1]

/-- Half-parameter exponential domination gives an explicit precision-truncation error. -/
theorem stoppedExpectation_precision_error_exp {F : ValuationWord → ℝ} {C : ℝ}
    (hC : 0 ≤ C)
    (hF : ∀ w, |F w| ≤ C * Real.exp ((1 / 2000 : ℝ) * w.ordinaryCost)) (E : ℕ) :
    |stoppedExpectation F - stoppedPrecisionExpectation E F| ≤
      C * Real.exp (-(E : ℝ) / 2000) * stoppedMomentBound := by
  have hsum : Summable (fun w => (stoppedPMF w).toReal * F w) := by
    apply summable_stopped_of_abs_le_exp
    intro w
    refine (hF w).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC)
    have hR : (0 : ℝ) ≤ w.ordinaryCost := Nat.cast_nonneg _
    linarith
  let V := stoppedWords E
  let B := C * Real.exp (-(E : ℝ) / 2000)
  let g := fun w => (stoppedPMF w).toReal *
    Real.exp ((1 / 1000 : ℝ) * w.ordinaryCost)
  have hg : Summable g := summable_stopped_expMoment
  have hB : 0 ≤ B := mul_nonneg hC (Real.exp_pos _).le
  have herr : stoppedExpectation F - stoppedPrecisionExpectation E F =
      ∑' w : {w // w ∉ V}, (stoppedPMF w).toReal * F w := by
    have h := hsum.sum_add_tsum_subtype_compl V
    rw [precision_eq_weighted]
    dsimp [stoppedExpectation]
    linarith
  rw [herr]
  have hbound : ∀ w : {w // w ∉ V},
      ‖(stoppedPMF w).toReal * F w‖ ≤ B * g w := by
    intro w
    by_cases hw : FirstCrossing w.val
    · have hE : E ≤ w.val.total := by
        by_contra h
        exact w.property ((mem_stoppedWords w.val E).mpr ⟨hw, by omega⟩)
      have hER : (E : ℝ) ≤ w.val.ordinaryCost := by
        have ht : w.val.total ≤ w.val.ordinaryCost := by
          simp [ValuationWord.ordinaryCost]
        exact_mod_cast hE.trans ht
      have he : Real.exp ((1 / 2000 : ℝ) * w.val.ordinaryCost) ≤
          Real.exp (-(E : ℝ) / 2000) *
            Real.exp ((1 / 1000 : ℝ) * w.val.ordinaryCost) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      have h1 := mul_le_mul_of_nonneg_left (hF w.val)
        (ENNReal.toReal_nonneg : 0 ≤ (stoppedPMF w.val).toReal)
      have h2 := mul_le_mul_of_nonneg_left he
        (mul_nonneg (ENNReal.toReal_nonneg : 0 ≤ (stoppedPMF w.val).toReal) hC)
      dsimp [B, g]
      nlinarith
    · simp [stoppedPMF_apply_of_not_firstCrossing hw, g]
  have hn := tsum_of_norm_bounded ((hg.subtype (fun w => w ∉ V)).mul_left B).hasSum hbound
  have hsub : (∑' w : {w // w ∉ V}, g w) ≤ ∑' w, g w :=
    Summable.tsum_le_tsum_of_inj Subtype.val Subtype.val_injective
      (fun _ _ => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
      (fun _ => le_rfl) (hg.subtype _) hg
  rw [tsum_mul_left] at hn
  change |∑' w : {w // w ∉ V}, (stoppedPMF w).toReal * F w| ≤ B * stoppedMomentBound
  rw [Real.norm_eq_abs] at hn
  exact hn.trans ((mul_le_mul_of_nonneg_left hsub hB).trans
    (mul_le_mul_of_nonneg_left stopped_expMoment_le hB))

/-- Cost-dominated observables have an effective original-weight finite-precision error. -/
theorem stoppedExpectation_precision_error_cost {F : ValuationWord → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hF : ∀ w, |F w| ≤ C * w.ordinaryCost) (E : ℕ) :
    |stoppedExpectation F - stoppedPrecisionExpectation E F| ≤
      2000 * C * Real.exp (-(E : ℝ) / 2000) * stoppedMomentBound := by
  apply stoppedExpectation_precision_error_exp (by positivity : 0 ≤ 2000 * C) _ E
  intro w
  have h := mul_le_mul_of_nonneg_left (cost_le_exp w) hC
  nlinarith [hF w]

end WordCertDensity.Construction
