/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The centered geometric log moment up to its exact pole

The upper bound uses the chord of the exponential between zero and log 2.
Comparing second derivatives and the two zero initial values proves the
positive pole bound and the negative-parameter quadratic bound.
-/

@[expose] public section

namespace WordCertDensity
namespace GeometricLog

/-- The exact reciprocal location of the geometric MGF pole. -/
noncomputable def poleCoefficient : ℝ := (Real.log 2)⁻¹

/-- The centered geometric log-moment formula on s<log 2. -/
noncomputable def value (s : ℝ) : ℝ := -s - Real.log (2 - Real.exp s)

/-- Distance to the pole in the denominator of the upper bound. -/
noncomputable def slack (s : ℝ) : ℝ := 1 - poleCoefficient * s

/-- The manuscript's positive-parameter log-MGF majorant. -/
noncomputable def upper (s : ℝ) : ℝ := s ^ 2 / slack s

private noncomputable def first (s : ℝ) : ℝ := -1 + Real.exp s / (2 - Real.exp s)
private noncomputable def second (s : ℝ) : ℝ := 2 * Real.exp s / (2 - Real.exp s) ^ 2
private noncomputable def upperFirst (s : ℝ) : ℝ :=
  (2 * s - poleCoefficient * s ^ 2) / slack s ^ 2

/-- The logarithmic pole location is positive. -/
theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- The reciprocal pole coefficient is positive. -/
theorem poleCoefficient_pos : 0 < poleCoefficient := inv_pos.mpr log_two_pos

/-- The reciprocal pole coefficient cancels the logarithmic pole location. -/
theorem poleCoefficient_mul_log : poleCoefficient * Real.log 2 = 1 := by
  exact inv_mul_cancel₀ log_two_pos.ne'

/-- The pole coefficient is at least one, as required for the exponential comparison. -/
theorem one_le_poleCoefficient : 1 ≤ poleCoefficient := by
  have hl := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hm := mul_le_mul_of_nonneg_left hl poleCoefficient_pos.le
  rw [poleCoefficient_mul_log] at hm
  norm_num at hm
  exact hm

/-- The upper-bound denominator is positive strictly before the pole. -/
theorem slack_pos {s : ℝ} (hs : s < Real.log 2) : 0 < slack s := by
  have h := mul_lt_mul_of_pos_left hs poleCoefficient_pos
  rw [poleCoefficient_mul_log] at h
  exact sub_pos.mpr h

/-- The exact MGF denominator is positive strictly before the pole. -/
theorem denominator_pos {s : ℝ} (hs : s < Real.log 2) : 0 < 2 - Real.exp s := by
  have h := Real.exp_lt_exp.mpr hs
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h
  linarith

private theorem value_hasDeriv {s : ℝ} (hs : s < Real.log 2) :
    HasDerivAt value (first s) s := by
  have h := (hasDerivAt_id s).neg.sub
    (((Real.hasDerivAt_exp s).const_sub 2).log (denominator_pos hs).ne')
  convert! h using 1
  simp only [first]
  ring

private theorem first_hasDeriv {s : ℝ} (hs : s < Real.log 2) :
    HasDerivAt first (second s) s := by
  have h := ((Real.hasDerivAt_exp s).div ((Real.hasDerivAt_exp s).const_sub 2)
    (denominator_pos hs).ne').const_add (-1)
  convert! h using 1
  simp only [second]
  field_simp
  ring

private theorem upper_hasDeriv {s : ℝ} (hs : s < Real.log 2) :
    HasDerivAt upper (upperFirst s) s := by
  have h := ((hasDerivAt_id s).pow 2).div
    (((hasDerivAt_id s).const_mul poleCoefficient).const_sub 1) (slack_pos hs).ne'
  convert! h using 1
  simp [upperFirst, slack]
  field_simp
  ring

private theorem upperFirst_hasDeriv {s : ℝ} (hs : s < Real.log 2) :
    HasDerivAt upperFirst (2 / slack s ^ 3) s := by
  have hn := ((hasDerivAt_id s).const_mul 2).sub
    (((hasDerivAt_id s).pow 2).const_mul poleCoefficient)
  have hd := (((hasDerivAt_id s).const_mul poleCoefficient).const_sub 1).pow 2
  have h := hn.div hd (pow_ne_zero 2 (slack_pos hs).ne')
  convert! h using 1
  simp [slack]
  field_simp [show 1 - poleCoefficient * s ≠ 0 from (slack_pos hs).ne']
  ring

private theorem compare_from_zero {f g df dg : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hf : ∀ x ∈ Set.Icc 0 t, HasDerivAt f (df x) x)
    (hg : ∀ x ∈ Set.Icc 0 t, HasDerivAt g (dg x) x)
    (hd : ∀ x ∈ Set.Icc 0 t, df x ≤ dg x) (hzero : f 0 ≤ g 0) : f t ≤ g t := by
  have hm : MonotoneOn (fun x => g x - f x) (Set.Icc 0 t) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t)
      (fun x hx => ((hg x hx).sub (hf x hx)).continuousAt.continuousWithinAt)
      (fun x hx => ((hg x (interior_subset hx)).sub (hf x (interior_subset hx))).hasDerivWithinAt)
      (fun x hx => sub_nonneg.mpr (hd x (interior_subset hx)))
  have h := hm ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  linarith

private theorem compare_twice {f g df dg ddf ddg : ℝ → ℝ} {t : ℝ} (ht : 0 ≤ t)
    (hf : ∀ x ∈ Set.Icc 0 t, HasDerivAt f (df x) x)
    (hg : ∀ x ∈ Set.Icc 0 t, HasDerivAt g (dg x) x)
    (hdf : ∀ x ∈ Set.Icc 0 t, HasDerivAt df (ddf x) x)
    (hdg : ∀ x ∈ Set.Icc 0 t, HasDerivAt dg (ddg x) x)
    (hdd : ∀ x ∈ Set.Icc 0 t, ddf x ≤ ddg x)
    (hfirst : df 0 ≤ dg 0) (hzero : f 0 ≤ g 0) : f t ≤ g t := by
  apply compare_from_zero ht hf hg _ hzero
  intro x hx
  exact compare_from_zero hx.1
    (fun y hy => hdf y ⟨hy.1, hy.2.trans hx.2⟩)
    (fun y hy => hdg y ⟨hy.1, hy.2.trans hx.2⟩)
    (fun y hy => hdd y ⟨hy.1, hy.2.trans hx.2⟩) hfirst

/-- The exponential chord bounds the true MGF denominator from below. -/
theorem slack_le_denominator {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ Real.log 2) :
    slack s ≤ 2 - Real.exp s := by
  have hw0 : 0 ≤ s / Real.log 2 := div_nonneg hs0 log_two_pos.le
  have hw1 : s / Real.log 2 ≤ 1 := (div_le_one log_two_pos).mpr hs
  have h := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (Real.log 2))
    (sub_nonneg.mpr hw1) hw0 (by ring : 1 - s / Real.log 2 + s / Real.log 2 = 1)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one,
    Real.exp_log (by norm_num : (0 : ℝ) < 2), div_mul_cancel₀ _ log_two_pos.ne'] at h
  rw [div_eq_mul_inv] at h
  dsimp [slack, poleCoefficient]
  nlinarith only [h]

/-- Multiplying the slack by the exponential costs at most one on the positive half-line. -/
theorem exp_mul_slack_le_one {s : ℝ} (hs : 0 ≤ s) : Real.exp s * slack s ≤ 1 := by
  have hm := mul_le_mul_of_nonneg_right one_le_poleCoefficient hs
  have he := Real.add_one_le_exp (-s)
  have hsl : slack s ≤ Real.exp (-s) := by dsimp [slack]; linarith
  have h := mul_le_mul_of_nonneg_left hsl (Real.exp_pos s).le
  simpa only [← Real.exp_add, add_neg_cancel, Real.exp_zero] using h

private theorem second_le_upper {s : ℝ} (hs0 : 0 ≤ s) (hs : s < Real.log 2) :
    second s ≤ 2 / slack s ^ 3 := by
  have ha := slack_pos hs
  have hd := denominator_pos hs
  have had := slack_le_denominator hs0 hs.le
  have he := mul_le_mul_of_nonneg_right (exp_mul_slack_le_one hs0) (sq_nonneg (slack s))
  have hsq := (sq_le_sq₀ ha.le hd.le).mpr had
  rw [second, div_le_div_iff₀ (pow_pos hd 2) (pow_pos ha 3)]
  nlinarith only [he, hsq]

private theorem second_neg_le_two {s : ℝ} (hs : 0 ≤ s) : second (-s) ≤ 2 := by
  have he : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hd : 0 < 2 - Real.exp (-s) := by linarith
  rw [second, div_le_iff₀ (pow_pos hd 2)]
  nlinarith [Real.exp_pos (-s)]

/-- The positive log-MGF is dominated up to the exact logarithmic pole. -/
theorem value_le_upper {s : ℝ} (hs0 : 0 ≤ s) (hs : s < Real.log 2) : value s ≤ upper s := by
  apply compare_twice hs0
    (fun x hx => value_hasDeriv (hx.2.trans_lt hs))
    (fun x hx => upper_hasDeriv (hx.2.trans_lt hs))
    (fun x hx => first_hasDeriv (hx.2.trans_lt hs))
    (fun x hx => upperFirst_hasDeriv (hx.2.trans_lt hs))
    (fun x hx => second_le_upper hx.1 (hx.2.trans_lt hs))
  · norm_num [first, upperFirst, slack]
  · norm_num [value, upper, slack]

/-- At every negative parameter the centered log-MGF has a quadratic bound. -/
theorem value_neg_le_sq {s : ℝ} (hs : 0 ≤ s) : value (-s) ≤ s ^ 2 := by
  have hdom (x : ℝ) (hx : 0 ≤ x) : -x < Real.log 2 := by linarith [log_two_pos]
  apply compare_twice (f := fun x => value (-x)) (g := fun x => x ^ 2)
    (df := fun x => -first (-x)) (dg := fun x => 2 * x)
    (ddf := fun x => second (-x)) (ddg := fun _ => 2) hs
  · intro x hx
    convert! (value_hasDeriv (hdom x hx.1)).comp x (hasDerivAt_id x).neg using 1
    simp
  · intro x _
    convert! (hasDerivAt_id x).pow 2 using 1
    simp
  · intro x hx
    convert! ((first_hasDeriv (hdom x hx.1)).comp x (hasDerivAt_id x).neg).neg using 1
    simp
  · intro x _
    convert! (hasDerivAt_id x).const_mul 2 using 1
    simp
  · intro x hx
    exact second_neg_le_two hx.1
  · norm_num [first]
  · norm_num [value]

end GeometricLog
end WordCertDensity
