/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Construction.StoppedLaw
public import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Joint exponential moments of the actual stopped law

Weighted Holder at exponent two bounds each stopping-depth contribution.
The original iid moment and preceding-depth stopping tail give a summable
explicit majorant. All expectations use the normalized original stopped law.
-/

@[expose] public section

namespace WordCertDensity.Construction

open scoped Classical ENNReal

private theorem exp_rpow_half (x : ℝ) :
    ENNReal.ofReal (Real.exp x) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.exp (x / 2)) := by
  rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul]
  congr 2
  ring

private theorem gated_exp_le {α : Type*} (p : PMF α) (G : α → Prop) (X : α → ℝ)
    (s B C : ℝ)
    (hp : Gated.probability p G ≤ Real.exp C)
    (hm : (∑' a, p a * ENNReal.ofReal (Real.exp ((2 * s) * X a))) ≤
      ENNReal.ofReal (Real.exp B)) :
    (∑' a, if G a then p a * ENNReal.ofReal (Real.exp (s * X a)) else 0) ≤
      ENNReal.ofReal (Real.exp ((B + C) / 2)) := by
  have hp' : (∑' a, if G a then p a else 0) ≤ ENNReal.ofReal (Real.exp C) := by
    have h := ENNReal.ofReal_le_ofReal hp
    simpa only [Gated.probability, ENNReal.ofReal_toReal (Gated.event_ne_top p G)] using h
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro V
  let F (a : α) := ENNReal.ofReal (Real.exp (s * X a))
  let W (a : α) := if G a then p a else 0
  have h := ENNReal.inner_le_weight_mul_Lp_of_nonneg V (p := 2) (by norm_num) W F
  have hW : ∑ a ∈ V, W a ≤ ENNReal.ofReal (Real.exp C) :=
    (ENNReal.sum_le_tsum V).trans hp'
  have hF : ∑ a ∈ V, W a * F a ^ (2 : ℝ) ≤ ENNReal.ofReal (Real.exp B) := by
    refine (Finset.sum_le_sum (fun a _ => ?_)).trans ((ENNReal.sum_le_tsum V).trans hm)
    dsimp [W, F]
    rw [ENNReal.rpow_two, ← ENNReal.ofReal_pow (Real.exp_pos _).le,
      ← Real.exp_nat_mul]
    have he : (2 : ℝ) * (s * X a) = (2 * s) * X a := by ring
    simp only [Nat.cast_ofNat]
    rw [he]
    by_cases ha : G a <;> simp [ha]
  have hh := mul_le_mul' (ENNReal.rpow_le_rpow hW (by norm_num : (0 : ℝ) ≤ 1 / 2))
    (ENNReal.rpow_le_rpow hF (by norm_num : (0 : ℝ) ≤ 1 / 2))
  have hnorm : (∑ a ∈ V, W a * F a) ≤
      ENNReal.ofReal (Real.exp C) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (Real.exp B) ^ (1 / 2 : ℝ) := by
    refine le_trans ?_ hh
    rw [show (1 - (2 : ℝ)⁻¹) = 1 / 2 by norm_num,
      show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at h
    exact h
  have heq : ENNReal.ofReal (Real.exp C) ^ (1 / 2 : ℝ) *
      ENNReal.ofReal (Real.exp B) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (Real.exp ((B + C) / 2)) := by
    rw [exp_rpow_half, exp_rpow_half, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add]
    congr 2
    ring
  rw [heq] at hnorm
  simpa only [W, F, ite_mul, zero_mul] using hnorm

/-- The iid ordinary-cost moment follows from the actual centered valuation moment. -/
theorem word_ordinaryExpMoment_le (n : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht : t < Real.log 2) :
    (∑' w, Reference.wordPMF n w * ENNReal.ofReal (Real.exp (t * w.ordinaryCost))) ≤
      ENNReal.ofReal (Real.exp ((n : ℝ) *
        (3 * t + t ^ 2 / (1 - (Real.log 2)⁻¹ * t)))) := by
  have he : (∑' w, Reference.wordPMF n w *
      ENNReal.ofReal (Real.exp (t * w.ordinaryCost))) =
      ENNReal.ofReal (Real.exp (3 * t * n)) *
        ∑' w, Reference.wordPMF n w *
          ENNReal.ofReal (Real.exp (t * ValuationWord.centeredTotal w)) := by
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro w
    by_cases hp : Reference.wordPMF n w = 0
    · simp [hp]
    have hn := (Reference.wordPMF_mem_support_iff n w).mp ((PMF.mem_support_iff _ _).mpr hp)
    have hc : (w.ordinaryCost : ℝ) = ValuationWord.centeredTotal w + 3 * n := by
      simp only [ValuationWord.ordinaryCost, Nat.cast_add, ValuationWord.centeredTotal, hn]
      ring
    rw [hc, mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
    have hx : t * (3 * (n : ℝ)) = 3 * t * n := by ring
    rw [hx]
    ac_rfl
  rw [he]
  refine (mul_le_mul' le_rfl (Reference.word_centeredExpMoment_le n ht0 ht)).trans_eq ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2
  ring

/-- One explicit doubled parameter has iid cost-moment growth at most exp(n/100). -/
theorem word_ordinaryExpMoment_small (n : ℕ) :
    (∑' w, Reference.wordPMF n w * ENNReal.ofReal (Real.exp ((1 / 500 : ℝ) *
      w.ordinaryCost))) ≤ ENNReal.ofReal (Real.exp ((n : ℝ) / 100)) := by
  have hl : (1 / 500 : ℝ) < Real.log 2 := by linarith [Head.log_two_lower]
  refine (word_ordinaryExpMoment_le n (t := 1 / 500) (by norm_num) hl).trans ?_
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hi : (Real.log 2)⁻¹ ≤ 2 := by
    apply (inv_le_iff_one_le_mul₀ (by linarith [Head.log_two_lower])).mpr
    linarith [Head.log_two_lower]
  have hd : 0 < 1 - (Real.log 2)⁻¹ * (1 / 500) := by linarith
  have hq : (1 / 500 : ℝ) ^ 2 / (1 - (Real.log 2)⁻¹ * (1 / 500)) ≤ 1 / 250 := by
    apply (div_le_iff₀ hd).mpr
    linarith
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- The full ordinary-cost exponential contribution from each positive stopping depth. -/
theorem stopped_ordinaryExpMoment_depth (n : ℕ) :
    (∑' w, if w.length = n + 1 then stoppedPMF w *
      ENNReal.ofReal (Real.exp ((1 / 1000 : ℝ) * w.ordinaryCost)) else 0) ≤
      ENNReal.ofReal (Real.exp (61 / 200 - 3 * (n : ℝ) / 200)) := by
  rw [stoppedPMF_length_moment]
  have hp : Gated.probability (Reference.wordPMF (n + 1)) FirstCrossing ≤
      Real.exp (3 / 5 - (n : ℝ) / 25) := by
    rw [← stoppedPMF_length_probability]
    exact stoppedPMF_succ_length_exp_bound n
  have hm := word_ordinaryExpMoment_small (n + 1)
  have h := gated_exp_le (Reference.wordPMF (n + 1)) FirstCrossing
    (fun w => w.ordinaryCost) (1 / 1000) ((n + 1 : ℕ) / 100)
    (3 / 5 - (n : ℝ) / 25) hp (by norm_num only [mul_div, one_mul] at *; exact hm)
  refine le_trans ?_ (h.trans_eq ?_)
  · apply le_of_eq
    apply tsum_congr
    intro w
    by_cases hw : FirstCrossing w <;> simp only [hw, if_true, if_false]
  · congr 2
    push_cast
    ring

private theorem moment_depth_sum (F : ValuationWord → ℝ≥0∞) :
    (∑' w, stoppedPMF w * F w) =
      ∑' n : ℕ, ∑' w, if w.length = n then stoppedPMF w * F w else 0 := by
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro w
  rw [tsum_eq_single w.length]
  · simp
  · intro n hn
    simp [hn.symm]

private theorem moment_depth_zero (F : ValuationWord → ℝ≥0∞) :
    (∑' w, if w.length = 0 then stoppedPMF w * F w else 0) = 0 := by
  apply ENNReal.tsum_eq_zero.mpr
  intro w
  by_cases hw : w.length = 0
  · have he : w = [] := List.length_eq_zero_iff.mp hw
    subst w
    have hz : stoppedPMF [] = 0 := stoppedPMF_apply_of_not_firstCrossing
      (fun h => firstCrossing_nonempty h rfl)
    simp [hz]
  · simp [hw]

private theorem summable_depth_majorant :
    Summable (fun n : ℕ => Real.exp (61 / 200 - 3 * (n : ℝ) / 200)) := by
  have h := Real.summable_exp_nat_mul_iff.mpr (by norm_num : (-3 / 200 : ℝ) < 0)
  have hm := h.mul_left (Real.exp (61 / 200))
  apply hm.congr
  intro n
  rw [← Real.exp_add]
  congr 1
  ring

/-- The complete stopped ordinary-cost moment is finite at a fixed positive parameter. -/
theorem stopped_ordinaryExpMoment_lt_top :
    (∑' w, stoppedPMF w * ENNReal.ofReal
      (Real.exp ((1 / 1000 : ℝ) * w.ordinaryCost))) < ⊤ := by
  rw [moment_depth_sum, tsum_eq_zero_add' ENNReal.summable, moment_depth_zero, zero_add]
  exact lt_of_le_of_lt (ENNReal.tsum_le_tsum stopped_ordinaryExpMoment_depth)
    summable_depth_majorant.tsum_ofReal_lt_top

/-- Closed geometric upper bound for the stopped ordinary-cost exponential moment. -/
noncomputable def stoppedMomentBound : ℝ :=
  Real.exp (61 / 200) / (1 - Real.exp (-3 / 200))

/-- The explicit moment bound has a positive denominator and is positive. -/
theorem stoppedMomentBound_pos : 0 < stoppedMomentBound := by
  apply div_pos (Real.exp_pos _)
  have h : Real.exp (-3 / 200 : ℝ) < 1 := Real.exp_lt_one_iff.mpr (by norm_num)
  linarith

/-- The complete moment is bounded by its explicit depth-geometric sum. -/
theorem stopped_ordinaryExpMoment_le :
    (∑' w, stoppedPMF w * ENNReal.ofReal
      (Real.exp ((1 / 1000 : ℝ) * w.ordinaryCost))) ≤
      ENNReal.ofReal stoppedMomentBound := by
  rw [moment_depth_sum, tsum_eq_zero_add' ENNReal.summable, moment_depth_zero, zero_add]
  refine (ENNReal.tsum_le_tsum stopped_ordinaryExpMoment_depth).trans_eq ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le)
    summable_depth_majorant]
  congr 1
  calc
    (∑' n : ℕ, Real.exp (61 / 200 - 3 * (n : ℝ) / 200)) =
        ∑' n : ℕ, Real.exp (61 / 200) * Real.exp (-3 / 200) ^ n := by
      apply tsum_congr
      intro n
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      ring
    _ = stoppedMomentBound := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le
        (Real.exp_lt_one_iff.mpr (by norm_num : (-3 / 200 : ℝ) < 0))]
      rfl

/-- Absolute displacement is controlled by twice the actual ordinary step cost. -/
theorem abs_displacement_le_cost (w : ValuationWord) :
    |displacement w| ≤ 2 * (w.ordinaryCost : ℝ) := by
  have hl0 : 0 ≤ Head.logRatio := by linarith [Head.one_lt_logRatio]
  have hl2 : Head.logRatio ≤ 2 := by linarith [Head.logRatio_lt_eight_fifths]
  have hd : (0 : ℝ) ≤ w.length := Nat.cast_nonneg _
  have hA : (0 : ℝ) ≤ w.total := Nat.cast_nonneg _
  rw [displacement]
  refine (abs_sub _ _).trans ?_
  rw [abs_of_nonneg hA, abs_of_nonneg (mul_nonneg hl0 hd)]
  simp only [ValuationWord.ordinaryCost, Nat.cast_add]
  nlinarith

/-- A fixed neighborhood of zero has a finite actual joint displacement/cost moment. -/
theorem stopped_jointExpMoment_lt_top {u v : ℝ}
    (hu : |u| ≤ 1 / 4000) (hv : |v| ≤ 1 / 4000) :
    (∑' w, stoppedPMF w * ENNReal.ofReal
      (Real.exp (u * displacement w + v * w.ordinaryCost))) < ⊤ := by
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum (fun w => ?_)) stopped_ordinaryExpMoment_lt_top
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  have hR : (0 : ℝ) ≤ w.ordinaryCost := Nat.cast_nonneg _
  have hY := abs_displacement_le_cost w
  have h1 : u * displacement w ≤ |u| * |displacement w| := by
    simpa only [abs_mul] using le_abs_self (u * displacement w)
  have h2 : v * (w.ordinaryCost : ℝ) ≤ |v| * w.ordinaryCost :=
    mul_le_mul_of_nonneg_right (le_abs_self v) hR
  have h3 := mul_le_mul_of_nonneg_left hY (abs_nonneg u)
  have h4 := mul_le_mul_of_nonneg_right hu hR
  have h5 := mul_le_mul_of_nonneg_right hv hR
  nlinarith

end WordCertDensity.Construction
