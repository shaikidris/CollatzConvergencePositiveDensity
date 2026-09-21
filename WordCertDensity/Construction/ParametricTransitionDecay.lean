/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.ParametricTransition
import WordCertDensity.Construction.GraftTransitionPolynomial

/-! # Decay of the full parameterized physical transition debit

The rounded initial count supplies the theta-dependent marker coefficient.
The other marker and both rejection terms retain their original bounds.
The full incoming capacity stays in the inverse-cube majorant as the splice moves.
-/

namespace WordCertDensity.Construction

open Filter
open scoped Topology

private theorem sqrt_six {x : ℝ} (hx : 0 ≤ x) : Real.sqrt x ^ 6 = x ^ 3 := by
  rw [show (6 : ℕ) = 2 * 3 by decide, pow_mul, Real.sq_sqrt hx]

private theorem inverse_six_sqrt {x y A : ℝ} (hx : 0 < x) (hA : 0 < A)
    (hy : Real.sqrt x / A ≤ y) : y ^ (-6 : ℝ) ≤ A ^ 6 / x ^ 3 := by
  have hs : 0 < Real.sqrt x / A := div_pos (Real.sqrt_pos.mpr hx) hA
  have hp := Real.rpow_le_rpow_of_nonpos hs hy (by norm_num : (-6 : ℝ) ≤ 0)
  apply hp.trans_eq
  rw [Real.rpow_neg hs.le, show (6 : ℝ) = (6 : ℕ) by norm_num,
    Real.rpow_natCast, div_pow, sqrt_six hx.le]
  field_simp

/-- Both actual marker levels retain the inverse-cube scale at fixed positive theta. -/
theorem parametricTransition_marker_polynomial {θ : ℝ} (hθ : 0 < θ) {b : ℕ}
    (hb : 256 ^ 2 ≤ b) (t : ℕ) :
    (parametricLevel θ (graftInitialCount b t) : ℝ) ^ (-6 : ℝ) ≤
        (16 / θ) ^ 6 / (seedSize b t : ℝ) ^ 3 ∧
      (seedTailDepth b t : ℝ) ^ (-6 : ℝ) ≤
        (8 : ℝ) ^ 6 / (seedSize b t : ℝ) ^ 3 := by
  have hx : (0 : ℝ) < seedSize b t := by
    have hs := seedSize_ge b t
    exact_mod_cast (show 0 < seedSize b t by omega)
  have hlo := (mul_le_mul_of_nonneg_left (graftInitialCount_bounds (t := t) hb).1 hθ.le).trans
    (parametricLevel_bounds hθ.le (graftInitialCount b t)).1
  have he : Real.sqrt (seedSize b t : ℝ) / (16 / θ) =
      θ * (Real.sqrt (seedSize b t : ℝ) / 16) := by field_simp
  refine ⟨inverse_six_sqrt hx (by positivity) ?_, (graftTransition_marker_polynomial hb t).2⟩
  rw [he]
  exact hlo

/-- The fixed effective coefficient for the complete transition debit. -/
noncomputable def parametricTransitionConstant (θ δ : ℝ) : ℝ :=
  (2 / 3 : ℝ) * ((Analytic.mixingCoefficient : ℝ) * (16 / θ) ^ 6 +
    (Analytic.mixingCoefficient : ℝ) * 8 ^ 6 +
      graftPrecisionFailureConstant + graftCorridorFailureConstant δ)

/-- The full debit has the manuscript's P_t b_t^-3 majorant, with all four costs retained. -/
theorem parametricTransitionDebit_polynomial {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) {b : ℕ}
    (hb : 256 ^ 2 ≤ b) (t : ℕ) :
    parametricTransitionDebit θ δ b t ≤
      parametricTransitionConstant θ δ * seedCapacity b t / (seedSize b t : ℝ) ^ 3 := by
  have hm := parametricTransition_marker_polynomial hθ hb t
  have hk := mul_le_mul_of_nonneg_left hm.1 Analytic.mixingCoefficient_pos.le
  have ha := mul_le_mul_of_nonneg_left hm.2 Analytic.mixingCoefficient_pos.le
  have hp := graftPrecisionFailure_polynomial hb t
  have hc := graftCorridorFailure_polynomial hδ hb t
  have hP := (seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t)
  unfold parametricTransitionDebit graftTransitionFailure
  calc
    _ ≤ (2 / 3 : ℝ) * seedCapacity b t *
        ((Analytic.mixingCoefficient : ℝ) * ((16 / θ) ^ 6 / (seedSize b t : ℝ) ^ 3) +
          (Analytic.mixingCoefficient : ℝ) * ((8 : ℝ) ^ 6 / (seedSize b t : ℝ) ^ 3) +
          (graftPrecisionFailureConstant / (seedSize b t : ℝ) ^ 3 +
            graftCorridorFailureConstant δ / (seedSize b t : ℝ) ^ 3)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hk ha) (add_le_add hp hc)) (by positivity)
    _ = _ := by unfold parametricTransitionConstant; ring

/-- The transition coefficient exactly recovers the original fixed marker scale. -/
theorem parametricTransitionConstant_fixed (δ : ℝ) :
    parametricTransitionConstant (1 / 1000) δ = graftTransitionConstant δ := by
  norm_num [parametricTransitionConstant, graftTransitionConstant]

/-- The original transition budget is the exact fixed-parameter specialization. -/
theorem parametricTransitionDebit_fixed (δ : ℝ) (b t : ℕ) :
    parametricTransitionDebit (1 / 1000) δ b t = graftTransitionDebit δ b t := by
  simp only [parametricTransitionDebit, graftTransitionDebit, parametricLevel_fixed]

/-- The actual full transition debit is nonnegative. -/
theorem parametricTransitionDebit_nonneg (θ δ : ℝ)
    (b t : ℕ) : 0 ≤ parametricTransitionDebit θ δ b t := by
  have hP := (seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t)
  have hC := Analytic.mixingCoefficient_pos.le
  unfold parametricTransitionDebit graftTransitionFailure
  positivity

/-- The transition debit tends to zero with the growing incoming family, uniformly in the root. -/
theorem parametricTransitionDebit_tendsto {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) {b : ℕ}
    (hb : 256 ^ 2 ≤ b) :
    Tendsto (parametricTransitionDebit θ δ b) atTop (𝓝 0) := by
  have ht := (graftTransitionWeight_tendsto hb).const_mul (parametricTransitionConstant θ δ)
  have hmajor : Tendsto (fun t => parametricTransitionConstant θ δ * seedCapacity b t /
      (seedSize b t : ℝ) ^ 3) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, mul_assoc] using ht
  change Tendsto (fun t => parametricTransitionDebit θ δ b t) atTop (𝓝 0)
  exact squeeze_zero (parametricTransitionDebit_nonneg θ δ b)
    (parametricTransitionDebit_polynomial hθ hδ hb) hmajor

end WordCertDensity.Construction
