/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.GraftPairing

/-! # The inverse-fourth-power continuation debit

The exact positive count gives the factor 1000 in both marker errors.
After paying the boundary by one, the quadratic total tag count leaves
an inverse fourth power with a coefficient independent of the splice.
-/

namespace WordCertDensity.Construction

/-- The unshifted positive count retains the manuscript's exact marker coefficient. -/
theorem graft_macroLevel_mixing_le {B k : ℕ} (hB : 1 ≤ B) (hk : macroLevel B ≤ k) :
    Analytic.mixingError k ≤
      (Analytic.mixingCoefficient : ℝ) * 1000 ^ 6 / (B : ℝ) ^ 6 := by
  have hb : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have he : (B : ℝ) / 1000 ≤ k := (macroLevel_bounds B).1.trans (Nat.cast_le.mpr hk)
  have hm := Analytic.mixingError_le_order6 ((macroLevel_pos hB).trans hk)
  have hp := Real.rpow_le_rpow_of_nonpos (by positivity : (0 : ℝ) < (B : ℝ) / 1000)
    he (by norm_num : (-6 : ℝ) ≤ 0)
  apply hm.trans
  have hmul := mul_le_mul_of_nonneg_left hp Analytic.mixingCoefficient_pos.le
  convert hmul using 1
  rw [Real.div_rpow hb.le (by norm_num)]
  norm_num [Real.rpow_neg, Real.rpow_natCast, div_eq_mul_inv]
  ring

/-- Both marker costs and the full macro rejection fit the literal order-six coefficient. -/
theorem graft_macroError_le {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) {B : ℕ} (hB : 1 ≤ B) :
    macroError L δ B ≤
      (2 * (Analytic.mixingCoefficient : ℝ) * 1000 ^ 6 + L + 5) / (B : ℝ) ^ 6 := by
  have hb : (1 : ℝ) ≤ B := Nat.one_le_cast.mpr hB
  have hold := graft_macroLevel_mixing_le hB (le_refl (macroLevel B))
  have hnew := graft_macroLevel_mixing_le hB
    (macroLevel_mono (Nat.le_add_right B (macroLength L B)))
  have hdef := (macroblockMass_deficit_bounds hL hδ hpay B).2
  have hpow : ((B : ℝ) + 2) ^ (-9 : ℝ) ≤ (B : ℝ) ^ (-6 : ℝ) := by
    apply (Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ (B : ℝ) + 2)
      (by norm_num : (-9 : ℝ) ≤ -6)).trans
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
  have hdef' := hdef.trans (mul_le_mul_of_nonneg_left hpow (by linarith : 0 ≤ L + 5))
  have hdef'' : 1 - macroblockMass L δ B ≤ (L + 5) / (B : ℝ) ^ 6 := by
    simpa only [Real.rpow_neg (by linarith : (0 : ℝ) ≤ B),
      show (6 : ℝ) = (6 : ℕ) by norm_num, Real.rpow_natCast, div_eq_mul_inv] using hdef'
  unfold macroError
  calc
    _ ≤ (Analytic.mixingCoefficient : ℝ) * 1000 ^ 6 / (B : ℝ) ^ 6 +
        (Analytic.mixingCoefficient : ℝ) * 1000 ^ 6 / (B : ℝ) ^ 6 +
        (L + 5) / (B : ℝ) ^ 6 := by linarith
    _ = _ := by ring

/-- Fixed coefficient of the hybrid continuation's inverse-fourth-power bound. -/
noncomputable def graftVariationConstant (L : ℝ) (b : ℕ) : ℝ :=
  (8 / 3 : ℝ) * ((2 : ℝ) ^ (b + 1) + 2) *
    (2 * (Analytic.mixingCoefficient : ℝ) * 1000 ^ 6 + L + 5)

/-- Once the actual conductor boundary is paid, the complete debit is at most K P_t B^-4. -/
theorem graftMacroDebit_polynomial {L δ : ℝ} (hL : 0 ≤ L) (hδ : 0 < δ)
    (hpay : 10 ≤ stoppedCorridorRate δ * L) (b t : ℕ) {B : ℕ} (hB : 1 ≤ B)
    (hboundary : macroBoundary L δ B ≤ 1) :
    graftMacroDebit L δ b t B ≤
      graftVariationConstant L b * seedCapacity b t / (B : ℝ) ^ 4 := by
  have hb : (1 : ℝ) ≤ B := Nat.one_le_cast.mpr hB
  have hbpos : (0 : ℝ) < B := by linarith
  have hP := (seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t)
  have htags : ((B : ℝ) + 1) ^ 2 ≤ 4 * (B : ℝ) ^ 2 := by nlinarith
  have hC : (0 : ℝ) ≤ (2 : ℝ) ^ (b + 1) + 1 + macroBoundary L δ B := by
    have := (macroBoundary_pos L δ B).le
    positivity
  have hbound : (2 : ℝ) ^ (b + 1) + 1 + macroBoundary L δ B ≤
      (2 : ℝ) ^ (b + 1) + 2 := by linarith
  have he := graft_macroError_le hL hδ hpay hB
  have hcoef : 0 ≤ 2 * (Analytic.mixingCoefficient : ℝ) * 1000 ^ 6 + L + 5 := by
    have := Analytic.mixingCoefficient_pos.le
    positivity
  unfold graftMacroDebit
  calc
    _ ≤ (2 / 3 : ℝ) * (seedCapacity b t * (4 * (B : ℝ) ^ 2)) *
        ((2 : ℝ) ^ (b + 1) + 2) *
        ((2 * (Analytic.mixingCoefficient : ℝ) * 1000 ^ 6 + L + 5) / (B : ℝ) ^ 6) := by
      apply mul_le_mul _ he (macroError_nonneg L δ hB) (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htags hP) (by norm_num)) hbound hC (by positivity)
    _ = _ := by
      unfold graftVariationConstant
      field_simp
      ring

end WordCertDensity.Construction
