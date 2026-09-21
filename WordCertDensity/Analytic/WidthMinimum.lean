/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Analytic.MixingEnvelope
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.FunProp

/-!
# The attained compact width minimum

At any scale above one, the envelope is continuous in the permitted width.
The infimum is attained inside that fixed interval and remains positive.
-/

namespace WordCertDensity.Analytic

/-- The infimum of the existing width family over the original compact interval. -/
noncomputable def widthMinimum (x : ℝ) : ℝ :=
  sInf ((fun v => mixingEnvelope v x) '' Set.Icc (80 : ℝ) (679 / 5))

/-- The width dependence is continuous on the whole permitted interval. -/
theorem mixingEnvelope_continuousOn {x : ℝ} (hx : 1 < x) :
    ContinuousOn (fun v => mixingEnvelope v x) (Set.Icc (80 : ℝ) (679 / 5)) := by
  intro v hv
  have hv0 : 0 < v := by linarith [hv.1]
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold mixingEnvelope Head.failureEnvelope
  fun_prop (disch := positivity)

/-- A permitted width realizes the infimum and is no worse than any other permitted width. -/
theorem exists_minimizing_width {x : ℝ} (hx : 1 < x) :
    ∃ v ∈ Set.Icc (80 : ℝ) (679 / 5), mixingEnvelope v x = widthMinimum x ∧
      ∀ w ∈ Set.Icc (80 : ℝ) (679 / 5), mixingEnvelope v x ≤ mixingEnvelope w x := by
  obtain ⟨v, hv, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Set.Icc (80 : ℝ) (679 / 5)).Nonempty from ⟨80, by norm_num⟩)
    (mixingEnvelope_continuousOn hx)
  have hleast : IsLeast ((fun w => mixingEnvelope w x) '' Set.Icc (80 : ℝ) (679 / 5))
      (mixingEnvelope v x) := by
    refine ⟨⟨v, hv, rfl⟩, ?_⟩
    rintro y ⟨w, hw, rfl⟩
    exact hmin hw
  exact ⟨v, hv, hleast.csInf_eq.symm, fun _ hw => hmin hw⟩

/-- The compact minimum is strictly positive at every scale in its natural domain. -/
theorem widthMinimum_pos {x : ℝ} (hx : 1 < x) : 0 < widthMinimum x := by
  obtain ⟨v, hv, heq, _⟩ := exists_minimizing_width hx
  rw [← heq]
  exact mixingEnvelope_pos hv.1 hx

/-- Each permitted width gives an upper bound on the attained minimum. -/
theorem widthMinimum_le {x v : ℝ} (hx : 1 < x) (hv : v ∈ Set.Icc (80 : ℝ) (679 / 5)) :
    widthMinimum x ≤ mixingEnvelope v x := by
  obtain ⟨w, hw, heq, hmin⟩ := exists_minimizing_width hx
  rw [← heq]
  exact hmin v hv

end WordCertDensity.Analytic
