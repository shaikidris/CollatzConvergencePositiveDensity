/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.LocalPrimitive.LongCrossingLaw

/-! # Finite numerical budgets for the long-crossing union -/

@[expose] public section

namespace WordCertDensity.LocalPrimitive

/-- An elementary finite inverse-square estimate; no infinite series is needed. -/
theorem longCrossing_inverseSquare_sum_le (P : ℕ) :
    (∑ p ∈ Finset.range P, 1 / ((p : ℝ) + 1) ^ 2) ≤ 2 := by
  have hbound : ∀ P : ℕ,
      (∑ p ∈ Finset.range P, 1 / ((p : ℝ) + 1) ^ 2) ≤ 2 - 2 / ((P : ℝ) + 1) := by
    intro P
    induction P with
    | zero => norm_num
    | succ P ih =>
      rw [Finset.sum_range_succ]
      have hp : (0 : ℝ) < P + 1 := by positivity
      have hp' : (0 : ℝ) < P + 2 := by positivity
      have hstep : 1 / ((P : ℝ) + 1) ^ 2 ≤
          2 / ((P : ℝ) + 1) - 2 / ((P : ℝ) + 2) := by
        field_simp
        nlinarith [Nat.cast_nonneg (α := ℝ) P]
      push_cast
      rw [show (P : ℝ) + 1 + 1 = P + 2 by ring]
      linarith
  exact (hbound P).trans (sub_le_self _ (by positivity))

/-- The finite linear sum with the manuscript's convenient square upper bound. -/
theorem longCrossing_linear_sum_le (P : ℕ) :
    (∑ p ∈ Finset.range P, ((p : ℝ) + 1)) ≤ ((P : ℝ) + 1) ^ 2 / 2 := by
  have heq : ∀ P : ℕ, (∑ p ∈ Finset.range P, ((p : ℝ) + 1)) =
      (P : ℝ) * ((P : ℝ) + 1) / 2 := by
    intro P
    induction P with
    | zero => norm_num
    | succ P ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  rw [heq]
  nlinarith [Nat.cast_nonneg (α := ℝ) P]

private theorem recipe_coefficient_le (d : ℝ) (hd : 1 ≤ d) :
    4 / (64 * d) + 1 / (16 * (64 * d) ^ 2) +
        2560 * (64 * d) ^ 2 / (2 ^ 17 * (64 * d) ^ 2 * d) ≤ 1 / (8 * d) := by
  have hd0 : 0 < d := by linarith
  have ht : 2560 * (64 * d) ^ 2 / (2 ^ 17 * (64 * d) ^ 2 * d) = 5 / (256 * d) := by
    field_simp
    ring
  rw [ht]
  field_simp
  nlinarith

/-- The full finite scalar premise of the final union contract follows from
the recipe. No probability or geometric conclusion is assumed here. -/
theorem longCrossing_recipe_sum_lt (s B A H P Z : ℕ)
    (_hB : 0 < B) (_hP : 0 < P)
    (hA : A = 64 * (16 * 10 ^ B))
    (hH : H = 2 ^ 17 * A ^ 2 * (16 * 10 ^ B))
    (hZ : Z = 128 * A * (P + 1) ^ 2 * (16 * 10 ^ B))
    (hlevel : (Z : ℝ) ≤ Real.sqrt s) :
    (∑ p ∈ Finset.range P, longCrossingProbabilityBound A H s p) <
      1 / (16 * (10 : ℝ) ^ B) := by
  let d : ℝ := 16 * (10 : ℝ) ^ B
  have hd : 1 ≤ d := by
    have hpow : (1 : ℝ) ≤ 10 ^ B := one_le_pow₀ (by norm_num)
    dsimp [d]
    linarith
  have hd0 : 0 < d := by linarith
  have hAr : (A : ℝ) = 64 * d := by dsimp [d]; exact_mod_cast hA
  have hHr : (H : ℝ) = 2 ^ 17 * (A : ℝ) ^ 2 * d := by dsimp [d]; exact_mod_cast hH
  have hZr : (Z : ℝ) = 128 * (A : ℝ) * ((P : ℝ) + 1) ^ 2 * d := by
    dsimp [d]
    exact_mod_cast hZ
  have hAp : (0 : ℝ) < A := by rw [hAr]; positivity
  have hHp : (0 : ℝ) < H := by rw [hHr]; positivity
  have hZp : (0 : ℝ) < Z := by rw [hZr]; positivity
  have hsqrt : 0 < Real.sqrt (s : ℝ) := lt_of_lt_of_le hZp hlevel
  let C : ℝ := 4 / A + 1 / (16 * (A : ℝ) ^ 2) + 2560 * (A : ℝ) ^ 2 / H
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  have hC : C ≤ 1 / (8 * d) := by
    dsimp [C]
    rw [hHr, hAr]
    exact recipe_coefficient_le d hd
  have hsum : (∑ p ∈ Finset.range P, longCrossingProbabilityBound A H s p) =
      C * (∑ p ∈ Finset.range P, 1 / ((p : ℝ) + 1) ^ 2) +
        (8 * A / Real.sqrt s) * (∑ p ∈ Finset.range P, ((p : ℝ) + 1)) := by
    simp only [longCrossingProbabilityBound, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _
    dsimp [C]
    ring
  have hlin : (8 * A / Real.sqrt s) * ((P : ℝ) + 1) ^ 2 / 2 ≤ 1 / (32 * d) := by
    have hlev := hlevel
    rw [hZr] at hlev
    rw [show (8 * (A : ℝ) / Real.sqrt s) * ((P : ℝ) + 1) ^ 2 / 2 =
      (4 * A * ((P : ℝ) + 1) ^ 2) / Real.sqrt s by ring]
    apply (div_le_div_iff₀ hsqrt (by positivity : (0 : ℝ) < 32 * d)).mpr
    nlinarith
  rw [hsum]
  have h₁ := mul_le_mul_of_nonneg_left (longCrossing_inverseSquare_sum_le P) hC0
  have h₂ := mul_le_mul_of_nonneg_left (longCrossing_linear_sum_le P)
    (show 0 ≤ 8 * (A : ℝ) / Real.sqrt s by positivity)
  have hsmall : 2 * (1 / (8 * d)) + 1 / (32 * d) < 1 / d := by
    field_simp
    linarith
  change _ < 1 / d
  nlinarith

/-- The recipe discharges the numerical premise of the final union assembly.
Only the substantive fixed-offset probability theorem remains an input. -/
theorem longCrossingUnionTarget_of_fixed (hfixed : LongCrossingFixedTarget) :
    LongCrossingUnionTarget :=
  longCrossingUnionTarget_of_fixedTarget hfixed longCrossing_recipe_sum_lt

/-- The level recipe supplies the square-root margin needed by every offset. -/
theorem longCrossing_recipe_sqrt_margin (s B A P Z p : ℕ)
    (hA : A = 64 * (16 * 10 ^ B))
    (hZ : Z = 128 * A * (P + 1) ^ 2 * (16 * 10 ^ B))
    (hlevel : (Z : ℝ) ≤ Real.sqrt s) (hp : p < P) :
    32 ≤ A ∧ 128 * (A : ℝ) * ((p : ℝ) + 1) ≤ Real.sqrt s := by
  have hd : 1 ≤ 16 * 10 ^ B := by
    have : 0 < 16 * 10 ^ B := by positivity
    omega
  have hAr : 32 ≤ A := by rw [hA]; omega
  refine ⟨hAr, ?_⟩
  have hidx : p + 1 ≤ (P + 1) ^ 2 := by nlinarith
  have hnat : 128 * A * (p + 1) ≤ Z := by
    rw [hZ]
    calc
      _ ≤ 128 * A * (P + 1) ^ 2 := Nat.mul_le_mul_left _ hidx
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  exact (show (128 : ℝ) * A * ((p : ℝ) + 1) ≤ Z by exact_mod_cast hnat).trans hlevel

/-- All basic width budgets follow from the square-root margin, before
rounding the rectangle endpoints. -/
theorem longCrossing_rectangle_width_budgets (s A p : ℕ) (hA : 32 ≤ A)
    (hmargin : 128 * (A : ℝ) * ((p : ℝ) + 1) ≤ Real.sqrt s) :
    0 < s ∧ 1 ≤ A * (p + 1) ∧
    (A : ℝ) * ((p : ℝ) + 1) * Real.sqrt s + 1 ≤ (s : ℝ) / 64 ∧
    (A : ℝ) * ((p : ℝ) + 1) ≤ (s : ℝ) / 64 ∧
    (p : ℝ) ≤ (s : ℝ) / 64 ∧
    (A : ℝ) * ((p : ℝ) + 1) ≤ (A : ℝ) * ((p : ℝ) + 1) * Real.sqrt s + 1 ∧
    (A : ℝ) * ((p : ℝ) + 1) * Real.sqrt s + 1 ≤
      2 * A * ((p : ℝ) + 1) * Real.sqrt s := by
  let Y : ℝ := A * ((p : ℝ) + 1)
  have hAr : (32 : ℝ) ≤ A := by exact_mod_cast hA
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hY : 1 ≤ Y := by dsimp [Y]; nlinarith
  have hq : 128 ≤ Real.sqrt (s : ℝ) := by dsimp [Y] at hY; nlinarith
  have hq0 := Real.sqrt_nonneg (s : ℝ)
  have hsquare := Real.sq_sqrt (Nat.cast_nonneg s)
  have hprod : 0 ≤ (Real.sqrt (s : ℝ) - 128 * Y) * Real.sqrt s := by
    apply mul_nonneg _ hq0
    dsimp [Y]
    linarith
  have hYq : Y ≤ Y * Real.sqrt s := le_mul_of_one_le_right (by linarith) (by linarith)
  have hW : Y * Real.sqrt s + 1 ≤ (s : ℝ) / 64 := by nlinarith
  have hpY : (p : ℝ) ≤ Y := by dsimp [Y]; nlinarith
  refine ⟨?_, ?_, hW, ?_, ?_, ?_, ?_⟩
  · have : (0 : ℝ) < s := by nlinarith
    exact_mod_cast this
  · dsimp [Y] at hY
    exact_mod_cast hY
  · dsimp [Y] at hYq hW
    linarith
  · linarith
  · exact hYq.trans (le_add_of_nonneg_right (by norm_num))
  · change Y * Real.sqrt s + 1 ≤ 2 * A * ((p : ℝ) + 1) * Real.sqrt s
    have heq : 2 * (A : ℝ) * ((p : ℝ) + 1) = 2 * Y := by dsimp [Y]; ring
    rw [heq]
    nlinarith

/-- The degree-four threshold satisfies the common-height packing budget. -/
theorem longCrossing_recipe_threshold_budget (B A H p : ℕ) (hA : 32 ≤ A)
    (hH : H = 2 ^ 17 * A ^ 2 * (16 * 10 ^ B)) :
    0 < longCrossingThreshold H p ∧
    4 * ((A * (p + 1) : ℕ) : ℝ) * Real.log 2 ≤ longCrossingThreshold H p := by
  have hd : 0 < 16 * 10 ^ B := by positivity
  have hbase : 4 * A ≤ H := by
    rw [hH]
    calc
      _ ≤ 2 ^ 17 * A ^ 2 := by nlinarith
      _ ≤ _ := Nat.le_mul_of_pos_right _ hd
  have hr : p + 1 ≤ (p + 1) ^ 4 := by
    have hh := pow_le_pow_right₀ (show 1 ≤ p + 1 by omega) (show 1 ≤ 4 by omega)
    simpa using hh
  have hnat : 4 * (A * (p + 1)) ≤ longCrossingThreshold H p := by
    unfold longCrossingThreshold
    calc
      _ = (4 * A) * (p + 1) := by ring
      _ ≤ H * (p + 1) ^ 4 := Nat.mul_le_mul hbase hr
  have hpos : 0 < A * (p + 1) := by
    have : 0 < A := by omega
    positivity
  refine ⟨by omega, ?_⟩
  have hlog : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hreal : (4 : ℝ) * (A * (p + 1) : ℕ) ≤ longCrossingThreshold H p := by
    exact_mod_cast hnat
  have hm := mul_le_mul_of_nonneg_left hlog
    (show (0 : ℝ) ≤ 4 * (A * (p + 1) : ℕ) by positivity)
  linarith

end WordCertDensity.LocalPrimitive
