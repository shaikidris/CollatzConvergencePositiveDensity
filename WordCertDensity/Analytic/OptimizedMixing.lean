/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Analytic.AllHighMixing
import Mathlib.Tactic.GCongr

/-!
# The optimized power with one canonical coefficient

The width 6749/50 pays exponent 2314/25. The very same coefficient covers
small conductors by the universal probability-mass bound two.
-/

namespace WordCertDensity.Analytic

/-- The fixed rational width used for the optimized power. -/
noncomputable def optimizedWidth : ℝ := 6749 / 50

/-- The retained optimized mixing exponent. -/
noncomputable def mixingExponent : ℝ := 2314 / 25

/-- The canonical scalar C6=2D+2; its exact natural recipe is proved below. -/
noncomputable def mixingCoefficient : ℝ := 2 * tailCoefficient + 2

/-- Exact agreement of the coefficient with 2D+2. -/
theorem mixingCoefficient_eq : mixingCoefficient = 2 * tailCoefficient + 2 := rfl

/-- The scalar coefficient is exactly the manuscript's natural arithmetic recipe. -/
theorem mixingCoefficient_eq_natCast :
    mixingCoefficient = ((2 * primitiveCoefficient * 20 ^ 6409 + 2 : ℕ) : ℝ) := by
  have h (C a k : ℕ) : 2 * ((C : ℝ) * (a : ℝ) ^ k) + 2 =
      ((2 * C * a ^ k + 2 : ℕ) : ℝ) := by
    push_cast
    ring
  exact h primitiveCoefficient 20 6409

/-- The canonical coefficient is positive. -/
theorem mixingCoefficient_pos : (0 : ℝ) < mixingCoefficient := by
  rw [mixingCoefficient_eq]
  linarith [tailCoefficient_pos]

/-- The fixed optimized width lies in the original permitted interval. -/
theorem optimizedWidth_mem : optimizedWidth ∈ Set.Icc (80 : ℝ) (679 / 5) := by
  norm_num [optimizedWidth]

/-- Both competing exponents strictly exceed the retained optimized rate. -/
theorem optimized_exponent_guards :
    -6407 + Real.log 2 * optimizedWidth ^ 2 / 2 < -mixingExponent ∧
      1 - optimizedWidth * Real.log 2 < -mixingExponent := by
  have hl := Real.log_two_gt_d9
  have hu := Real.log_two_lt_d9
  norm_num only [optimizedWidth, mixingExponent]
  constructor <;> nlinarith only [hl, hu]

/-- At the fixed width the three rejection terms together cost less than one power unit. -/
theorem optimized_failure_lt {x : ℝ} (hx : 4 ≤ x) (hlog : 4 < Real.log x) :
    Head.failureEnvelope optimizedWidth x < x ^ (-mixingExponent) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hq : 55 < optimizedWidth * Real.log 2 := by
    have h := Head.log_two_lower
    norm_num only [optimizedWidth]
    nlinarith only [h]
  have hden : 64 ≤ (optimizedWidth * Real.log 2) ^ 2 * Real.log x := by
    have hsq : (3025 : ℝ) ≤ (optimizedWidth * Real.log 2) ^ 2 := by nlinarith
    have hprod := mul_le_mul hsq hlog.le (by norm_num : (0 : ℝ) ≤ 4)
      (sq_nonneg (optimizedWidth * Real.log 2))
    nlinarith only [hprod]
  have hcoeff : 16 / ((optimizedWidth * Real.log 2) ^ 2 * Real.log x) ≤ (1 / 4 : ℝ) := by
    apply (div_le_iff₀ (by linarith)).mpr
    linarith
  have hB := optimized_exponent_guards.2.le
  have hshort := mul_le_mul hcoeff
    (Real.rpow_le_rpow_of_exponent_le hx1 hB)
    (Real.rpow_nonneg hx0.le _) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hC : -(optimizedWidth * Real.log 2) ≤ -mixingExponent - 1 := by linarith
  have hsecond : x ^ (-(optimizedWidth * Real.log 2)) ≤ (1 / 4 : ℝ) * x ^ (-mixingExponent) := by
    calc
      _ ≤ x ^ (-mixingExponent - 1) := Real.rpow_le_rpow_of_exponent_le hx1 hC
      _ = x ^ (-mixingExponent) / x := by rw [Real.rpow_sub hx0, Real.rpow_one]
      _ ≤ (1 / 4 : ℝ) * x ^ (-mixingExponent) := by
        apply (div_le_iff₀ hx0).mpr
        nlinarith [mul_le_mul_of_nonneg_left hx (Real.rpow_nonneg hx0.le (-mixingExponent))]
  have hthird : x ^ (-(optimizedWidth * Real.log 2) - 1) ≤
      (1 / 4 : ℝ) * x ^ (-mixingExponent) :=
    (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)).trans hsecond
  have hpos := Real.rpow_pos_of_pos hx0 (-mixingExponent)
  unfold Head.failureEnvelope
  linarith only [hshort, hsecond, hthird, hpos]

/-- The optimized real-scale envelope fits the exact canonical coefficient. -/
theorem optimizedEnvelope_lt {x : ℝ} (hx : 4 ≤ x) (hlog : 4 < Real.log x) :
    mixingEnvelope optimizedWidth x < (mixingCoefficient : ℝ) * x ^ (-mixingExponent) := by
  have hmain := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ x) optimized_exponent_guards.1.le)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) tailCoefficient_pos.le)
  have hfail := optimized_failure_lt hx hlog
  rw [mixingCoefficient_eq]
  unfold mixingEnvelope
  linarith

/-- Small levels are paid by the original coefficient, not by an enlarged replacement. -/
theorem two_lt_mixing_power {m : ℕ} (hm : 1 ≤ m) (hm' : m < 2 ^ 80) :
    2 < (mixingCoefficient : ℝ) * (m : ℝ) ^ (-mixingExponent) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hb : (m : ℝ) ≤ (2 : ℝ) ^ 80 := by exact_mod_cast hm'.le
  have hpow : (m : ℝ) ^ mixingExponent ≤ (2 : ℝ) ^ 8000 := by
    calc
      _ ≤ (m : ℝ) ^ (100 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm1 (by norm_num [mixingExponent])
      _ = (m : ℝ) ^ (100 : ℕ) := Real.rpow_natCast _ _
      _ ≤ ((2 : ℝ) ^ 80) ^ 100 := by gcongr
      _ = _ := by rw [← pow_mul]
  have h20 : (2 : ℝ) ^ 8000 ≤ (20 : ℝ) ^ 6409 := by
    calc
      _ ≤ (2 : ℝ) ^ (4 * 6409) := by gcongr <;> norm_num
      _ = ((2 : ℝ) ^ 4) ^ 6409 := pow_mul _ _ _
      _ ≤ _ := by gcongr; norm_num
  have hC : (1 : ℝ) ≤ primitiveCoefficient := by exact_mod_cast one_le_primitiveCoefficient
  have hD : (20 : ℝ) ^ 6409 ≤ tailCoefficient := by
    simpa only [tailCoefficient, one_mul] using
      mul_le_mul_of_nonneg_right hC (pow_nonneg (by norm_num : (0 : ℝ) ≤ 20) 6409)
  have hbound : 2 * (m : ℝ) ^ mixingExponent < (mixingCoefficient : ℝ) := by
    rw [mixingCoefficient_eq]
    calc
      _ ≤ 2 * tailCoefficient := mul_le_mul_of_nonneg_left
        (hpow.trans (h20.trans hD)) (by norm_num)
      _ < _ := lt_add_of_pos_right _ (by norm_num : (0 : ℝ) < 2)
  rw [Real.rpow_neg hm0.le, ← div_eq_mul_inv]
  exact (lt_div_iff₀ (Real.rpow_pos_of_pos hm0 mixingExponent)).mpr hbound

/-- The same coefficient gives the optimized power bound at every positive coarse level. -/
theorem oscillation_le_mixing_power {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    FiniteFourier.oscillation hmn (Reference.mass n) ≤
      (mixingCoefficient : ℝ) * (m : ℝ) ^ (-mixingExponent) := by
  by_cases hhigh : 2 ^ 80 ≤ m
  · have hlog := (Head.common_margins optimizedWidth_mem.1 optimizedWidth_mem.2 hhigh).1
    exact (all_high_oscillation_le optimizedWidth_mem.1 optimizedWidth_mem.2 hhigh hmn).trans
      (optimizedEnvelope_lt (by exact_mod_cast (by omega : 4 ≤ m)) hlog).le
  · rw [FiniteFourier.oscillation_mass]
    exact (Reference.fullL1_le_two hmn).trans (two_lt_mixing_power hm (by omega)).le

/-- Every weaker power uses the identical canonical coefficient. -/
theorem mixing_power_le {m : ℕ} (hm : 1 ≤ m) {p : ℝ} (hp : p ≤ mixingExponent) :
    (mixingCoefficient : ℝ) * (m : ℝ) ^ (-mixingExponent) ≤
      (mixingCoefficient : ℝ) * (m : ℝ) ^ (-p) := by
  apply mul_le_mul_of_nonneg_left _ mixingCoefficient_pos.le
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (neg_le_neg hp)

end WordCertDensity.Analytic
