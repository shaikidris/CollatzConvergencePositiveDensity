/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.StoppedCopies
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Effective concentration of independent stopped blocks

One explicit parameter and rate control both signs of both coordinates.
The events use the actual sum minus the prescribed number of full-law means.
The support theorem justifies that count, including the empty list at zero.
-/

@[expose] public section

namespace WordCertDensity.Construction

open scoped ENNReal

/-- An explicit positive Chernoff parameter at every positive corridor width. -/
noncomputable def stoppedCorridorParameter (δ : ℝ) : ℝ :=
  min (1 / 8000) (δ / (2 * stoppedQuadraticBound))

/-- The common exponential decay rate for the four stopped-coordinate tails. -/
noncomputable def stoppedCorridorRate (δ : ℝ) : ℝ := stoppedCorridorParameter δ * δ / 2

/-- Every strictly positive corridor width gives a strictly positive parameter. -/
theorem stoppedCorridorParameter_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < stoppedCorridorParameter δ := by
  exact lt_min (by norm_num) (div_pos hδ (mul_pos (by norm_num) stoppedQuadraticBound_pos))

/-- The selected parameter is within the fixed centered-MGF domain. -/
theorem stoppedCorridorParameter_le (δ : ℝ) : stoppedCorridorParameter δ ≤ 1 / 8000 :=
  min_le_left _ _

/-- The quadratic moment cost uses at most half the linear tail exponent. -/
theorem stoppedCorridorParameter_budget (δ : ℝ) :
    stoppedQuadraticBound * stoppedCorridorParameter δ ≤ δ / 2 := by
  have h := (le_div_iff₀ (mul_pos (by norm_num) stoppedQuadraticBound_pos)).mp
    (min_le_right (1 / 8000 : ℝ) (δ / (2 * stoppedQuadraticBound)))
  change stoppedCorridorParameter δ * (2 * stoppedQuadraticBound) ≤ δ at h
  nlinarith

/-- Every strictly positive width gives a strictly positive decay rate. -/
theorem stoppedCorridorRate_pos {δ : ℝ} (hδ : 0 < δ) : 0 < stoppedCorridorRate δ :=
  div_pos (mul_pos (stoppedCorridorParameter_pos hδ) hδ) (by norm_num)

private theorem corridor_abs_parameter {δ : ℝ} (hδ : 0 < δ) :
    |stoppedCorridorParameter δ| ≤ 1 / 8000 := by
  rw [abs_of_pos (stoppedCorridorParameter_pos hδ)]
  exact stoppedCorridorParameter_le δ

private theorem corridor_exponent_le (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    -stoppedCorridorParameter δ * (δ * n) +
        (n : ℝ) * (stoppedQuadraticBound * stoppedCorridorParameter δ ^ 2) ≤
      -stoppedCorridorRate δ * n := by
  have h := mul_le_mul_of_nonneg_right (stoppedCorridorParameter_budget δ)
    (mul_nonneg (stoppedCorridorParameter_pos hδ).le (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  unfold stoppedCorridorRate
  nlinarith

/-- The non-strict upper centered tail has the explicit common decay rate. -/
theorem stoppedCopies_upperTail_le (n : ℕ) {F : ValuationWord → ℝ}
    (hF : ∀ w, |F w| ≤ 2 * w.ordinaryCost) {δ : ℝ} (hδ : 0 < δ) :
    Gated.probability (stoppedCopiesPMF n)
      (fun ws => δ * n ≤ blockSum (stoppedCentered F) ws) ≤
      Real.exp (-stoppedCorridorRate δ * n) := by
  have h := Gated.probability_le_exp (stoppedCopiesPMF n) (blockSum (stoppedCentered F))
    (cutoff := δ * n) (stoppedCorridorParameter_pos hδ).le
    (stoppedCopies_centered_expMoment_le n hF (corridor_abs_parameter hδ))
  exact h.trans (Real.exp_le_exp.mpr (corridor_exponent_le n hδ))

/-- The non-strict lower centered tail uses the same parameter and decay rate. -/
theorem stoppedCopies_lowerTail_le (n : ℕ) {F : ValuationWord → ℝ}
    (hF : ∀ w, |F w| ≤ 2 * w.ordinaryCost) {δ : ℝ} (hδ : 0 < δ) :
    Gated.probability (stoppedCopiesPMF n)
      (fun ws => blockSum (stoppedCentered F) ws ≤ -(δ * n)) ≤
      Real.exp (-stoppedCorridorRate δ * n) := by
  have hneg : |-stoppedCorridorParameter δ| ≤ 1 / 8000 := by
    simpa only [abs_neg] using corridor_abs_parameter hδ
  have hm : (∑' ws, stoppedCopiesPMF n ws * ENNReal.ofReal
        (Real.exp (stoppedCorridorParameter δ * (-blockSum (stoppedCentered F) ws)))) ≤
      ENNReal.ofReal (Real.exp
        ((n : ℝ) * (stoppedQuadraticBound * stoppedCorridorParameter δ ^ 2))) := by
    simpa only [mul_neg, neg_mul, neg_sq] using stoppedCopies_centered_expMoment_le n hF hneg
  have h := Gated.probability_le_exp (stoppedCopiesPMF n)
    (fun ws => -blockSum (stoppedCentered F) ws) (cutoff := δ * n)
    (stoppedCorridorParameter_pos hδ).le hm
  have h' := h.trans (Real.exp_le_exp.mpr (corridor_exponent_le n hδ))
  simpa only [le_neg] using h'

/-- A strict deviation of the actual sum from n full-law means has the two-tail bound. -/
theorem stoppedCopies_deviation_le (n : ℕ) {F : ValuationWord → ℝ}
    (hF : ∀ w, |F w| ≤ 2 * w.ordinaryCost) {δ : ℝ} (hδ : 0 < δ) :
    Gated.probability (stoppedCopiesPMF n)
      (fun ws => δ * n < |blockSum F ws - (n : ℝ) * stoppedExpectation F|) ≤
      2 * Real.exp (-stoppedCorridorRate δ * n) := by
  have hmono := Gated.probability_mono_on_support (stoppedCopiesPMF n)
    (fun ws => δ * n < |blockSum F ws - (n : ℝ) * stoppedExpectation F|)
    (fun ws => δ * n ≤ blockSum (stoppedCentered F) ws ∨
      blockSum (stoppedCentered F) ws ≤ -(δ * n)) (fun ws hws he => by
        have hlen := ((stoppedCopiesPMF_mem_support_iff n ws).mp
          ((PMF.mem_support_iff (stoppedCopiesPMF n) ws).mpr hws)).1
        have hc : blockSum (stoppedCentered F) ws =
            blockSum F ws - (n : ℝ) * stoppedExpectation F := by
          rw [blockSum_centered, hlen]
        rw [← hc] at he
        by_cases hp : δ * n ≤ blockSum (stoppedCentered F) ws
        · exact Or.inl hp
        · apply Or.inr
          by_contra hn
          have ha : |blockSum (stoppedCentered F) ws| ≤ δ * n :=
            abs_le.mpr ⟨by linarith, by linarith⟩
          linarith)
  calc
    _ ≤ Gated.probability (stoppedCopiesPMF n)
        (fun ws => δ * n ≤ blockSum (stoppedCentered F) ws ∨
          blockSum (stoppedCentered F) ws ≤ -(δ * n)) := hmono
    _ ≤ Gated.probability (stoppedCopiesPMF n)
          (fun ws => δ * n ≤ blockSum (stoppedCentered F) ws) +
        Gated.probability (stoppedCopiesPMF n)
          (fun ws => blockSum (stoppedCentered F) ws ≤ -(δ * n)) :=
      Gated.probability_or_le _ _ _
    _ ≤ Real.exp (-stoppedCorridorRate δ * n) + Real.exp (-stoppedCorridorRate δ * n) :=
      add_le_add (stoppedCopies_upperTail_le n hF hδ) (stoppedCopies_lowerTail_le n hF hδ)
    _ = _ := by ring

/-- The literal displacement-or-cost corridor failure has an explicit four-tail bound. -/
theorem stoppedCopies_corridor_le (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Gated.probability (stoppedCopiesPMF n) (fun ws =>
      δ * n < |blockSum displacement ws - (n : ℝ) * stoppedExpectation displacement| ∨
      δ * n < |blockSum (fun w => w.ordinaryCost) ws -
        (n : ℝ) * stoppedExpectation (fun w => w.ordinaryCost)|) ≤
      4 * Real.exp (-stoppedCorridorRate δ * n) := by
  have hR : ∀ w : ValuationWord, |(w.ordinaryCost : ℝ)| ≤ 2 * w.ordinaryCost := by
    intro w
    rw [abs_of_nonneg (Nat.cast_nonneg w.ordinaryCost : (0 : ℝ) ≤ w.ordinaryCost)]
    have h : (0 : ℝ) ≤ w.ordinaryCost := Nat.cast_nonneg _
    linarith
  calc
    _ ≤ Gated.probability (stoppedCopiesPMF n)
          (fun ws => δ * n < |blockSum displacement ws -
            (n : ℝ) * stoppedExpectation displacement|) +
        Gated.probability (stoppedCopiesPMF n)
          (fun ws => δ * n < |blockSum (fun w => w.ordinaryCost) ws -
            (n : ℝ) * stoppedExpectation (fun w => w.ordinaryCost)|) :=
      Gated.probability_or_le _ _ _
    _ ≤ 2 * Real.exp (-stoppedCorridorRate δ * n) +
        2 * Real.exp (-stoppedCorridorRate δ * n) :=
      add_le_add (stoppedCopies_deviation_le n abs_displacement_le_cost hδ)
        (stoppedCopies_deviation_le n hR hδ)
    _ = _ := by ring

/-- Every positive width has fixed positive concentration constants for all copy counts. -/
theorem stoppedCopies_corridor_constants {δ : ℝ} (hδ : 0 < δ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ,
      Gated.probability (stoppedCopiesPMF n) (fun ws =>
        δ * n < |blockSum displacement ws - (n : ℝ) * stoppedExpectation displacement| ∨
        δ * n < |blockSum (fun w => w.ordinaryCost) ws -
          (n : ℝ) * stoppedExpectation (fun w => w.ordinaryCost)|) ≤
        C * Real.exp (-c * n) :=
  ⟨4, stoppedCorridorRate δ, by norm_num, stoppedCorridorRate_pos hδ,
    fun n => stoppedCopies_corridor_le n hδ⟩

end WordCertDensity.Construction
