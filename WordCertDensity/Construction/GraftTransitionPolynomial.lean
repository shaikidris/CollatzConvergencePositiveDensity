/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftDebit
import WordCertDensity.Construction.GraftDecay
import WordCertDensity.Construction.SeedPolynomial

/-! # Polynomial decay of the full incoming-weighted transition debit

The precision failure keeps its B_0 prefactor and uses the seventh
exponential-series term. The corridor failure uses the sixth term.
Both marker levels keep their own coefficients. All constants are fixed
before the splice, and the actual incoming growth P_t remains in the bound.
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

private theorem weighted_exp_seven {u c : ℝ} (hu : 0 < u) (hc : 0 < c) :
    u * Real.exp (-c * u) ≤ (Nat.factorial 7 : ℝ) / c ^ 7 / u ^ 6 := by
  have h := exp_neg_le_factorial_div (mul_pos hc hu) 7
  have he : -c * u = -(c * u) := by ring
  rw [he]
  calc
    _ ≤ u * ((Nat.factorial 7 : ℝ) / (c * u) ^ 7) := mul_le_mul_of_nonneg_left h hu.le
    _ = _ := by field_simp

private theorem exp_sqrt_six {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    Real.exp (-c * Real.sqrt x) ≤ (Nat.factorial 6 : ℝ) / c ^ 6 / x ^ 3 := by
  have h := exp_neg_le_factorial_div (mul_pos hc (Real.sqrt_pos.mpr hx)) 6
  have he : -c * Real.sqrt x = -(c * Real.sqrt x) := by ring
  rw [he]
  calc
    _ ≤ (Nat.factorial 6 : ℝ) / (c * Real.sqrt x) ^ 6 := h
    _ = _ := by rw [mul_pow, sqrt_six hx.le]; ring

/-- Fixed coefficient for the precision failure, including its linear B_0 prefactor. -/
noncomputable def graftPrecisionFailureConstant : ℝ :=
  (Nat.factorial 7 : ℝ) / (Real.log 2 / 200) ^ 7 / 4

/-- Fixed coefficient for the corridor rejection at the chosen positive tolerance. -/
noncomputable def graftCorridorFailureConstant (δ : ℝ) : ℝ :=
  4 * ((Nat.factorial 6 : ℝ) / (stoppedCorridorRate δ / 16) ^ 6)

/-- Both literal marker levels satisfy the retained inverse-cube scale bound. -/
theorem graftTransition_marker_polynomial {b : ℕ} (hb : 256 ^ 2 ≤ b) (t : ℕ) :
    (macroLevel (graftInitialCount b t) : ℝ) ^ (-6 : ℝ) ≤
        (16000 : ℝ) ^ 6 / (seedSize b t : ℝ) ^ 3 ∧
      (seedTailDepth b t : ℝ) ^ (-6 : ℝ) ≤
        (8 : ℝ) ^ 6 / (seedSize b t : ℝ) ^ 3 := by
  have hn : 1 ≤ seedSize b t := by have := seedSize_ge b t; omega
  have hx : (0 : ℝ) < seedSize b t := Nat.cast_pos.mpr (by omega)
  have hs : Real.sqrt (seedSize b t : ℝ) ≤ (seedSize b t : ℝ) :=
    Real.sqrt_le_self_iff.mpr (Or.inr (Nat.one_le_cast.mpr hn))
  exact ⟨inverse_six_sqrt hx (by norm_num) (graftInitialLevel_lower hb),
    inverse_six_sqrt hx (by norm_num)
      ((div_le_div_of_nonneg_right hs (by norm_num)).trans (graftOldLevel_lower hb t))⟩

/-- The seventh exponential-series term pays the full precision rejection mass. -/
theorem graftPrecisionFailure_polynomial {b : ℕ} (hb : 256 ^ 2 ≤ b) (t : ℕ) :
    (graftInitialCount b t : ℝ) * (2 : ℝ) ^ (-(graftPrecision b t : ℝ) / 100) ≤
      graftPrecisionFailureConstant / (seedSize b t : ℝ) ^ 3 := by
  have hx : (0 : ℝ) < seedSize b t := by
    have hn := seedSize_ge b t
    exact_mod_cast (show 0 < seedSize b t by omega)
  have hu := Real.sqrt_pos.mpr hx
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hE := (graftPrecision_bounds (t := t) (by omega : 1 ≤ b)).1
  have hB := (graftInitialCount_bounds (t := t) hb).2
  have hexp : (2 : ℝ) ^ (-(graftPrecision b t : ℝ) / 100) ≤
      Real.exp (-(Real.log 2 / 200) * Real.sqrt (seedSize b t : ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hE hlog.le
    nlinarith
  calc
    _ ≤ (Real.sqrt (seedSize b t : ℝ) / 4) *
        Real.exp (-(Real.log 2 / 200) * Real.sqrt (seedSize b t : ℝ)) :=
      mul_le_mul hB hexp (by positivity) (by positivity)
    _ = (1 / 4 : ℝ) * (Real.sqrt (seedSize b t : ℝ) *
        Real.exp (-(Real.log 2 / 200) * Real.sqrt (seedSize b t : ℝ))) := by ring
    _ ≤ (1 / 4 : ℝ) * ((Nat.factorial 7 : ℝ) / (Real.log 2 / 200) ^ 7 /
        Real.sqrt (seedSize b t : ℝ) ^ 6) :=
      mul_le_mul_of_nonneg_left (weighted_exp_seven hu (by positivity)) (by norm_num)
    _ = _ := by rw [sqrt_six hx.le]; unfold graftPrecisionFailureConstant; ring

/-- The sixth exponential-series term pays the full corridor rejection mass. -/
theorem graftCorridorFailure_polynomial {δ : ℝ} (hδ : 0 < δ) {b : ℕ}
    (hb : 256 ^ 2 ≤ b) (t : ℕ) :
    4 * Real.exp (-stoppedCorridorRate δ * graftInitialCount b t) ≤
      graftCorridorFailureConstant δ / (seedSize b t : ℝ) ^ 3 := by
  have hx : (0 : ℝ) < seedSize b t := by
    have hn := seedSize_ge b t
    exact_mod_cast (show 0 < seedSize b t by omega)
  have hc := stoppedCorridorRate_pos hδ
  have hB := (graftInitialCount_bounds (t := t) hb).1
  have hexp : Real.exp (-stoppedCorridorRate δ * graftInitialCount b t) ≤
      Real.exp (-(stoppedCorridorRate δ / 16) * Real.sqrt (seedSize b t : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hB hc.le
    nlinarith
  calc
    _ ≤ 4 * Real.exp (-(stoppedCorridorRate δ / 16) * Real.sqrt (seedSize b t : ℝ)) :=
      mul_le_mul_of_nonneg_left hexp (by norm_num)
    _ ≤ 4 * ((Nat.factorial 6 : ℝ) / (stoppedCorridorRate δ / 16) ^ 6 /
        (seedSize b t : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left (exp_sqrt_six hx (by positivity)) (by norm_num)
    _ = _ := by unfold graftCorridorFailureConstant; ring

/-- The fixed effective coefficient for the complete transition debit. -/
noncomputable def graftTransitionConstant (δ : ℝ) : ℝ :=
  (2 / 3 : ℝ) * ((Analytic.mixingCoefficient : ℝ) * 16000 ^ 6 +
    (Analytic.mixingCoefficient : ℝ) * 8 ^ 6 +
      graftPrecisionFailureConstant + graftCorridorFailureConstant δ)

/-- The full debit has the manuscript's P_t b_t^-3 majorant, with all four costs retained. -/
theorem graftTransitionDebit_polynomial {δ : ℝ} (hδ : 0 < δ) {b : ℕ}
    (hb : 256 ^ 2 ≤ b) (t : ℕ) :
    graftTransitionDebit δ b t ≤
      graftTransitionConstant δ * seedCapacity b t / (seedSize b t : ℝ) ^ 3 := by
  have hm := graftTransition_marker_polynomial hb t
  have hk := mul_le_mul_of_nonneg_left hm.1 Analytic.mixingCoefficient_pos.le
  have ha := mul_le_mul_of_nonneg_left hm.2 Analytic.mixingCoefficient_pos.le
  have hp := graftPrecisionFailure_polynomial hb t
  have hc := graftCorridorFailure_polynomial hδ hb t
  have hP := (seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t)
  unfold graftTransitionDebit graftTransitionFailure
  calc
    _ ≤ (2 / 3 : ℝ) * seedCapacity b t *
        ((Analytic.mixingCoefficient : ℝ) * ((16000 : ℝ) ^ 6 / (seedSize b t : ℝ) ^ 3) +
          (Analytic.mixingCoefficient : ℝ) * ((8 : ℝ) ^ 6 / (seedSize b t : ℝ) ^ 3) +
          (graftPrecisionFailureConstant / (seedSize b t : ℝ) ^ 3 +
            graftCorridorFailureConstant δ / (seedSize b t : ℝ) ^ 3)) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hk ha) (add_le_add hp hc)) (by positivity)
    _ = _ := by unfold graftTransitionConstant; ring

/-- The actual full transition debit is nonnegative. -/
theorem graftTransitionDebit_nonneg (δ : ℝ) (b t : ℕ) : 0 ≤ graftTransitionDebit δ b t := by
  have hP := (seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t)
  have hC := Analytic.mixingCoefficient_pos.le
  unfold graftTransitionDebit graftTransitionFailure
  positivity

/-- The transition debit tends to zero with the growing incoming family, uniformly in the root. -/
theorem graftTransitionDebit_tendsto {δ : ℝ} (hδ : 0 < δ) {b : ℕ} (hb : 256 ^ 2 ≤ b) :
    Tendsto (graftTransitionDebit δ b) atTop (𝓝 0) := by
  have ht := (graftTransitionWeight_tendsto hb).const_mul (graftTransitionConstant δ)
  have hmajor : Tendsto (fun t => graftTransitionConstant δ * seedCapacity b t /
      (seedSize b t : ℝ) ^ 3) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, mul_assoc] using ht
  change Tendsto (fun t => graftTransitionDebit δ b t) atTop (𝓝 0)
  exact squeeze_zero (graftTransitionDebit_nonneg δ b) (graftTransitionDebit_polynomial hδ hb) hmajor

end WordCertDensity.Construction
