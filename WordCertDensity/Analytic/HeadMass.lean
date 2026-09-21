/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Analytic.HeadOffset
public import WordCertDensity.Reference.Words
public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Original-weight head submass and its second moment

The iid word law is mapped to a residue on acceptance and to `none` on
rejection. Thus accepted mass is never divided by a success probability.
Small-offset injection makes each occupied atom equal to its original weight.
-/

@[expose] public section

namespace WordCertDensity
namespace Head

open scoped Classical

/-- The original iid head law, with rejected words retained as a separate outcome. -/
noncomputable def law (v : ℝ) (n k l : ℕ) : PMF (Option (ZMod (3 ^ n))) := by
  classical
  exact (Reference.wordPMF (k + 1)).map
    (fun w => if Gate v n k l w then some (w.residueOffset n) else none)

/-- Accepted head mass at one residue, with its original iid probability. -/
noncomputable def mass (v : ℝ) (n k l : ℕ) (y : ZMod (3 ^ n)) : ℝ :=
  (law v n k l (some y)).toReal

/-- The accepted law is exactly the original word sum on the stated gate and residue. -/
theorem law_some_apply (v : ℝ) (n k l : ℕ) (y : ZMod (3 ^ n)) :
    law v n k l (some y) = ∑' w : ValuationWord,
      if Gate v n k l w ∧ w.residueOffset n = y then Reference.wordPMF (k + 1) w else 0 := by
  classical
  rw [law, PMF.map_apply]
  apply tsum_congr
  intro w
  by_cases h : Gate v n k l w <;> simp [h, eq_comm]

/-- Accepted masses are nonnegative. -/
theorem mass_nonneg (v : ℝ) (n k l : ℕ) (y : ZMod (3 ^ n)) :
    0 ≤ mass v n k l y := ENNReal.toReal_nonneg

/-- Accepted mass plus the unchanged rejection probability is exactly one. -/
theorem mass_sum_add_rejected (v : ℝ) (n k l : ℕ) :
    (∑ y, mass v n k l y) + (law v n k l none).toReal = 1 := by
  have h := congrArg ENNReal.toReal (PMF.tsum_coe (law v n k l))
  rw [tsum_fintype, ENNReal.toReal_sum (fun y _ => PMF.apply_ne_top _ y),
    ENNReal.toReal_one, Fintype.sum_option] at h
  simpa only [mass, add_comm] using h

/-- Each fixed head family has total mass at most one, including empty families. -/
theorem mass_sum_le_one (v : ℝ) (n k l : ℕ) : ∑ y, mass v n k l y ≤ 1 := by
  have h := mass_sum_add_rejected v n k l
  have hnone : 0 ≤ (law v n k l none).toReal := ENNReal.toReal_nonneg
  linarith

/-- A residue with no accepted head has zero mass. -/
theorem mass_eq_zero_of_no_head {v : ℝ} {n k l : ℕ} {y : ZMod (3 ^ n)}
    (h : ¬ ∃ w : ValuationWord, Gate v n k l w ∧ w.residueOffset n = y) :
    mass v n k l y = 0 := by
  classical
  unfold mass
  rw [law_some_apply]
  have hn (w : ValuationWord) : ¬ (Gate v n k l w ∧ w.residueOffset n = y) :=
    fun hw => h ⟨w, hw⟩
  simp [hn]

/-- A uniquely occupied residue has exactly the original word weight, without normalization. -/
theorem mass_eq_weight_of_unique_head {v : ℝ} {n k l : ℕ} {w : ValuationWord}
    (hw : Gate v n k l w)
    (hunique : ∀ u : ValuationWord, Gate v n k l u →
      u.residueOffset n = w.residueOffset n → u = w) :
    mass v n k l (w.residueOffset n) = 1 / (2 : ℝ) ^ l := by
  classical
  unfold mass
  rw [law_some_apply, tsum_eq_single w]
  · rw [if_pos ⟨hw, rfl⟩, ← hw.length_eq,
      Reference.wordPMF_toReal_length_eq_inv_pow, hw.total_eq]
  · intro u hu
    exact if_neg (fun h => hu (hunique u h.1 h.2))

/-- At the common cutoff every occupied residue has precisely its head's iid weight. -/
theorem mass_eq_weight_of_gate {v : ℝ} {n k l : ℕ} {w : ValuationWord}
    (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) (hn : 2 ^ 80 ≤ n) (hw : Gate v n k l w) :
    mass v n k l (w.residueOffset n) = 1 / (2 : ℝ) ^ l := by
  exact mass_eq_weight_of_unique_head hw
    (fun _ hu heq => hu.eq_of_residueOffset_eq hv hv' hn hw heq)

/-- Every atom is either unoccupied or has the original fixed-total weight. -/
theorem mass_eq_zero_or_weight {v : ℝ} {n k l : ℕ}
    (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) (hn : 2 ^ 80 ≤ n) (y : ZMod (3 ^ n)) :
    mass v n k l y = 0 ∨ mass v n k l y = 1 / (2 : ℝ) ^ l := by
  by_cases h : ∃ w : ValuationWord, Gate v n k l w ∧ w.residueOffset n = y
  · obtain ⟨w, hw, rfl⟩ := h
    exact Or.inr (mass_eq_weight_of_gate hv hv' hn hw)
  · exact Or.inl (mass_eq_zero_of_no_head h)

/-- The head second moment is exactly the original weight times the accepted mass. -/
theorem mass_second_moment_eq {v : ℝ} {n k l : ℕ}
    (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) (hn : 2 ^ 80 ≤ n) :
    (∑ y, mass v n k l y ^ 2) = (1 / (2 : ℝ) ^ l) * ∑ y, mass v n k l y := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rcases mass_eq_zero_or_weight hv hv' hn y with h | h <;> rw [h] <;> simp [pow_two]

/-- The manuscript's original-weight head second-moment bound holds at the common cutoff. -/
theorem mass_second_moment_le {v : ℝ} {n k l : ℕ}
    (hv : 80 ≤ v) (hv' : v ≤ 679 / 5) (hn : 2 ^ 80 ≤ n) :
    (∑ y, mass v n k l y ^ 2) ≤ 1 / (2 : ℝ) ^ l := by
  rw [mass_second_moment_eq hv hv' hn]
  simpa using mul_le_mul_of_nonneg_left (mass_sum_le_one v n k l)
    (by positivity : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ l)

end Head
end WordCertDensity
