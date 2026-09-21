/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Construction.TerminalStages
import WordCertDensity.Construction.SeedPolynomial

/-! # Polynomial domination of the literal terminal payment

A single sixth exponential-series term pays both original failure tails.
The unchanged incoming coefficient, quadratic capacity and linear shift count
then give inverse-cubic decay at every sufficiently large original-block count.
-/

namespace WordCertDensity.Construction

/-- A fixed positive parameter bounds a linear exponential by an inverse sixth power. -/
theorem terminal_exp_order6 {θ x : ℝ} (hθ : 0 < θ) (hx : 0 < x) :
    Real.exp (-(θ*x)/128000) ≤
      (Nat.factorial 6 : ℝ)*(128000/θ)^6/x^6 := by
  calc
    _ = Real.exp (-(θ*x/128000)) := by congr 1; ring
    _ ≤ (Nat.factorial 6 : ℝ)/(θ*x/128000)^6 :=
      exp_neg_le_factorial_div (by positivity) 6
    _ = _ := by field_simp [ne_of_gt hθ, ne_of_gt hx]

/-- The exact geometric precision loss is smaller than the retained endpoint exponential. -/
theorem terminalPrecision_tail_exp {d : ℕ} (hd : 200 ≤ d) :
    (2 : ℝ)^(-((terminalPrecision d : ℤ)+1)) ≤ Real.exp (-(d : ℝ)/64000) := by
  rw [← Real.rpow_intCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply Real.exp_le_exp.mpr
  push_cast
  have hlog : (1/2 : ℝ) ≤ Real.log 2 := by linarith [Head.log_two_lower]
  have hm := mul_le_mul_of_nonneg_right hlog
    (Nat.cast_nonneg (terminalPrecision d) : (0 : ℝ) ≤ terminalPrecision d)
  have hp := terminalPrecision_lower hd
  have hn : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  nlinarith

/-- The same explicit primitive coefficient pays the two terminal marker terms. -/
theorem terminalLevel_order6 {θ : ℝ} (hθ : 0 < θ) {B : ℕ} (hB : 1 ≤ B) :
    2*(Analytic.mixingCoefficient : ℝ)/(parametricLevel θ B : ℝ)^6 ≤
      2*(Analytic.mixingCoefficient : ℝ)*(θ⁻¹)^6/(B : ℝ)^6 := by
  have hBR : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hC := Analytic.mixingCoefficient_pos.le
  calc
    _ ≤ 2*(Analytic.mixingCoefficient : ℝ)/(θ*(B : ℝ))^6 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) (parametricLevel_bounds hθ.le B).1 6)
    _ = _ := by field_simp [ne_of_gt hθ, ne_of_gt hBR]

/-- The scalar coefficient is fixed before the original-block count or cutoff. -/
noncomputable def terminalScalarCoefficient (θ : ℝ) : ℝ :=
  2*(Analytic.mixingCoefficient : ℝ)*(θ⁻¹)^6 +
    3*(Nat.factorial 6 : ℝ)*(128000/θ)^6

/-- Both mixing costs and both original tails have one inverse-sixth-power majorant. -/
theorem terminalScalarError_le {θ : ℝ} (hθ : 0 < θ) {B : ℕ} (hB : 1 ≤ B)
    (hd : 200 ≤ ⌊θ*B⌋₊) :
    2*(Analytic.mixingCoefficient : ℝ)/(parametricLevel θ B : ℝ)^6 +
      2*Real.exp (-(⌊θ*B⌋₊ : ℝ)/64000) +
      (2 : ℝ)^(-((terminalPrecision ⌊θ*B⌋₊ : ℤ)+1)) ≤
        terminalScalarCoefficient θ/(B : ℝ)^6 := by
  have hBR : (0 : ℝ) < B := Nat.cast_pos.mpr (by omega)
  have hfloor : (⌊θ*B⌋₊ : ℝ) ≤ θ*B := Nat.floor_le (by positivity)
  have hdR : (200 : ℝ) ≤ (⌊θ*B⌋₊ : ℝ) := by exact_mod_cast hd
  have hhalf := terminalStage_half (show 2 ≤ θ*(B : ℝ) by linarith)
  have hexp : Real.exp (-(⌊θ*B⌋₊ : ℝ)/64000) ≤ Real.exp (-(θ*(B : ℝ))/128000) :=
    Real.exp_le_exp.mpr (by linarith)
  have he := hexp.trans (terminal_exp_order6 hθ hBR)
  have hg := (terminalPrecision_tail_exp hd).trans he
  have hm := terminalLevel_order6 hθ hB
  calc
    _ ≤ 2*(Analytic.mixingCoefficient : ℝ)*(θ⁻¹)^6/(B : ℝ)^6 +
        3*((Nat.factorial 6 : ℝ)*(128000/θ)^6/(B : ℝ)^6) := by linarith
    _ = _ := by unfold terminalScalarCoefficient; ring

/-- Complete fixed coefficient after paying incoming capacity and the selected-shift count. -/
noncomputable def terminalPaymentCoefficient (b t : ℕ) (θ : ℝ) : ℝ :=
  (40/3 : ℝ)*seedCapacity b t*((2 : ℝ)^(b+1)+2)*terminalScalarCoefficient θ

/-- The actual terminal error has inverse-cubic decay with every original prefactor retained. -/
theorem terminalPaymentError_polynomial (b t : ℕ) {θ : ℝ}
    (hθ : 0 < θ) (hcap : θ ≤ 1/1000) {B : ℕ} (hB : 1 ≤ B)
    (hd : 200 ≤ ⌊θ*B⌋₊) :
    terminalPaymentError b t θ B ≤ terminalPaymentCoefficient b t θ/(B : ℝ)^3 := by
  have hP := (seedTagBudget_nonneg b t).trans (seedTagBudget_le_capacity b t)
  have hC := Analytic.mixingCoefficient_pos.le
  have hBR : (1 : ℝ) ≤ B := Nat.one_le_cast.mpr hB
  have hpos : (0 : ℝ) < B := by linarith
  have hsquare : ((B : ℝ)+1)^2 ≤ 4*(B : ℝ)^2 := by nlinarith
  have hcount : 2*(terminalRadius ⌊θ*B⌋₊ : ℝ)+1 ≤ 5*(B : ℝ) := by
    exact_mod_cast terminalStage_shift_count hθ.le (by linarith : θ ≤ 1) hB
  have herr := terminalScalarError_le hθ hB hd
  unfold terminalPaymentError
  dsimp only
  calc
    _ ≤ (2/3 : ℝ)*seedCapacity b t*(4*(B : ℝ)^2)*((2 : ℝ)^(b+1)+2)*
        (5*(B : ℝ))*(terminalScalarCoefficient θ/(B : ℝ)^6) := by
      apply mul_le_mul _ herr (by positivity) (by positivity)
      apply mul_le_mul _ hcount (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsquare (by positivity)) (by positivity)
    _ = _ := by
      unfold terminalPaymentCoefficient
      field_simp [ne_of_gt hpos]
      ring

end WordCertDensity.Construction
