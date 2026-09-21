/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Counting.RadialSources
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Cutoff, containing-radius and packing-depth limits for radial counting -/

@[expose] public section

namespace WordCertDensity.Counting

open Filter
open scoped BigOperators Topology

/-- A fixed finite counting error vanishes at the real-cutoff lower-density interface. -/
theorem lower_density_of_eventual_linear_count (G : Set ℕ) (A B : ℝ)
    (h : ∀ᶠ Y : ℝ in atTop, A * Y - B ≤ (prefixCount G ⌊Y⌋₊ : ℝ)) :
    A ≤ lowerNaturalDensity G := by
  apply (le_lowerNaturalDensity_iff_real G A).mpr
  intro e he
  filter_upwards [h, eventually_ge_atTop (B / (A - e)),
    eventually_gt_atTop (0 : ℝ)] with Y hc hlarge hY
  have hB := (div_le_iff₀ (sub_pos.mpr he)).mp hlarge
  apply (le_div_iff₀ hY).mpr
  nlinarith

/-- First take the cutoff limit with both packing depth and containing radius fixed. -/
theorem finite_radial_density {G : Set ℕ} {u R s : ℝ} (h : ShellMass G u)
    (hclosed : DyadicallyClosed G) (hR : 16 < R) (I : Finset ℕ)
    (hI : ∀ j ∈ I, 1 ≤ j) (hs : 1 < s) (hsu : s ≤ 3 / 2)
    (hmargin : ∀ j ∈ I, Real.log s / 2 < u - j / 2 * Real.log (R / 16)) :
    (s - 1) * (∑ j ∈ I, 2 * (j : ℝ) / (16 : ℝ) ^ j) ≤ lowerNaturalDensity G := by
  apply lower_density_of_eventual_linear_count G _ (∑ j ∈ I, 4 * (j : ℝ) * (s + 1))
  filter_upwards [eventually_packed_source_count h hclosed hR I hI hs hsu hmargin] with Y hY
  have he : (∑ j ∈ I, (2 * (j : ℝ) * (s - 1) * (Y / (16 : ℝ) ^ j) - 4 * j * (s + 1))) =
      ((s - 1) * ∑ j ∈ I, 2 * (j : ℝ) / (16 : ℝ) ^ j) * Y -
        ∑ j ∈ I, 4 * (j : ℝ) * (s + 1) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    calc
      _ = ∑ j ∈ I, (2 * (j : ℝ) / (16 : ℝ) ^ j) * ((s - 1) * Y) :=
        Finset.sum_congr rfl (fun _ _ => by ring)
      _ = _ := by rw [← Finset.sum_mul]; ring
  rwa [he] at hY

/-- Any fixed finite depth admits a radius strictly above sixteen with arbitrarily small debit. -/
theorem exists_radius_for_depth (J : ℕ) {u s : ℝ} (hgap : Real.log s / 2 < u) :
    ∃ R : ℝ, 16 < R ∧ ∀ j ∈ Finset.Ico 1 J,
      Real.log s / 2 < u - j / 2 * Real.log (R / 16) := by
  let δ := (u - Real.log s / 2) / ((J : ℝ) + 1)
  have hd : 0 < δ := div_pos (by linarith) (by positivity)
  refine ⟨16 * Real.exp δ, ?_, ?_⟩
  · have h := Real.exp_lt_exp.mpr hd
    rw [Real.exp_zero] at h
    linarith
  · intro j hj
    have hjr : (j : ℝ) ≤ J := by exact_mod_cast (Finset.mem_Ico.mp hj).2.le
    have he : Real.log (16 * Real.exp δ / 16) = δ := by
      rw [mul_div_cancel_left₀ _ (by norm_num : (16 : ℝ) ≠ 0), Real.log_exp]
    rw [he]
    have hmul : δ * ((J : ℝ) + 1) = u - Real.log s / 2 :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_right hjr hd.le]

/-- Removing the containing-radius loss is justified at each fixed finite depth. -/
theorem finite_depth_radial_density {G : Set ℕ} {u s : ℝ} (h : ShellMass G u)
    (hclosed : DyadicallyClosed G) (J : ℕ) (hs : 1 < s) (hsu : s ≤ 3 / 2)
    (hgap : Real.log s / 2 < u) :
    (s - 1) * (∑ j ∈ Finset.Ico 1 J, 2 * (j : ℝ) / (16 : ℝ) ^ j) ≤ lowerNaturalDensity G := by
  obtain ⟨R, hR, hm⟩ := exists_radius_for_depth J hgap
  exact finite_radial_density h hclosed hR (Finset.Ico 1 J)
    (fun _ hj => (Finset.mem_Ico.mp hj).1) hs hsu hm

/-- The exact weighted geometric series supplies the radial coefficient. -/
theorem hasSum_radial_weights :
    HasSum (fun j : ℕ => 2 * (j : ℝ) / (16 : ℝ) ^ j) (32 / 225 : ℝ) := by
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one
    (by norm_num : ‖(1 / 16 : ℝ)‖ < 1)).mul_left 2
  have hf : (fun j : ℕ => 2 * (j : ℝ) / (16 : ℝ) ^ j) =
      (fun j : ℕ => (2 : ℝ) * (j * (1 / 16 : ℝ) ^ j)) := by
    funext j
    simp only [div_eq_mul_inv, inv_pow, one_mul]
    ring
  rw [hf]
  norm_num at h
  exact h

/-- Starting at index one only removes a zero summand, including at zero packing depth. -/
theorem sum_radial_weights_Ico (J : ℕ) :
    (∑ j ∈ Finset.Ico 1 J, 2 * (j : ℝ) / (16 : ℝ) ^ j) =
      ∑ j ∈ Finset.range J, 2 * (j : ℝ) / (16 : ℝ) ^ j := by
  by_cases hJ : J = 0
  · simp [hJ]
  · rw [Finset.sum_range_eq_add_Ico _ (Nat.pos_of_ne_zero hJ)]
    simp

/-- The increasing packing-depth limit retains the same set and lower natural density. -/
theorem inner_radial_density {G : Set ℕ} {u s : ℝ} (h : ShellMass G u)
    (hclosed : DyadicallyClosed G) (hs : 1 < s) (hsu : s ≤ 3 / 2)
    (hgap : Real.log s / 2 < u) :
    (s - 1) * (32 / 225 : ℝ) ≤ lowerNaturalDensity G := by
  have ht := hasSum_radial_weights.tendsto_sum_nat.const_mul (s - 1)
  apply le_of_tendsto' ht
  intro J
  rw [← sum_radial_weights_Ico J]
  exact finite_depth_radial_density h hclosed J hs hsu hgap

end WordCertDensity.Counting
