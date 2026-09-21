/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.ExactLowLevels
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic.FinCases

/-!
# Order-one entropy of the reference law

This module starts the restricted entropy extension with the actual normalized
reference density. The finite-fiber increment identity and its mixing bound
belong to the subsequent tasks in this same module.
-/

namespace WordCertDensity.Reference

/-- The full-group order-one entropy of the actual normalized reference law. -/
noncomputable def entropy (n : ℕ) : ℝ :=
  mean n (fun x => density n x * Real.log (density n x))

/-- The scalar relative-entropy defect, with the zero convention inherited from `Real.log`. -/
noncomputable def entropyDefect (u : ℝ) : ℝ := u * Real.log u - u + 1

/-- The level-zero reference law has zero order-one entropy. -/
theorem entropy_zero : entropy 0 = 0 := by
  unfold entropy
  have h (x : ZMod (3 ^ 0)) : density 0 x * Real.log (density 0 x) = 0 := by
    rw [density_zero]
    norm_num
  simp_rw [h]
  exact mean_const 0 0

/-- The first nontrivial reference law has the exact order-one entropy. -/
theorem entropy_one : entropy 1 = (2 / 3 : ℝ) * Real.log 2 := by
  obtain ⟨h0, h1, h2⟩ := density_one_values
  unfold entropy mean
  simp only [pow_one]
  change (∑ x : Fin 3, density 1 x * Real.log (density 1 x)) / 3 = _
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  change (density 1 0 * Real.log (density 1 0) +
    (density 1 1 * Real.log (density 1 1) +
      (density 1 2 * Real.log (density 1 2) + 0))) / 3 = _
  rw [h0, h1, h2]
  simp only [Real.log_one, mul_zero, zero_mul, zero_add]
  ring

/-- The scalar defect is nonnegative on the nonnegative half-line. -/
theorem entropyDefect_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ entropyDefect u := by
  unfold entropyDefect
  linarith [Real.self_sub_one_le_mul_log hu]

/-- A rational logarithmic bound sufficient for the upper scalar defect estimate. -/
private theorem log_three_le_four_thirds : Real.log 3 ≤ (4 / 3 : ℝ) := by
  apply (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3)).mpr
  have h := Real.sum_le_exp_of_nonneg (x := (4 / 3 : ℝ)) (by norm_num) 4
  norm_num [Finset.sum_range_succ] at h ⊢
  linarith

/-- On the range needed by a three-point fiber, the scalar defect is L1-controlled. -/
theorem entropyDefect_le_abs_sub_one {u : ℝ} (hu0 : 0 ≤ u) (hu3 : u ≤ 3) :
    entropyDefect u ≤ |u - 1| := by
  unfold entropyDefect
  by_cases hu1 : u ≤ 1
  · rw [abs_of_nonpos (by linarith)]
    have hlog : u * Real.log u ≤ 0 := Real.mul_log_nonpos hu0 hu1
    linarith
  · have h1 : 1 ≤ u := le_of_not_ge hu1
    rw [abs_of_nonneg (by linarith)]
    by_cases hu2 : u ≤ 2
    · have hlog : Real.log u ≤ u - 1 := by
        exact Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one h1)
      have hmul : u * Real.log u ≤ u * (u - 1) :=
        mul_le_mul_of_nonneg_left hlog hu0
      nlinarith [mul_nonneg (by linarith : 0 ≤ u - 1) (by linarith : 0 ≤ 2 - u)]
    · have h2 : 2 ≤ u := le_of_not_ge hu2
      have hlog_div : Real.log (u / 3) ≤ u / 3 - 1 := by
        exact Real.log_le_sub_one_of_pos (div_pos (lt_of_lt_of_le zero_lt_one h1)
          (by norm_num))
      have hlog : Real.log u ≤ Real.log 3 + (u - 3) / 3 := by
        rw [Real.log_div (lt_of_lt_of_le zero_lt_one h1).ne' (by norm_num : (3 : ℝ) ≠ 0)] at hlog_div
        linarith
      have hlog' : Real.log u ≤ u / 3 + 1 / 3 := by
        linarith [log_three_le_four_thirds]
      have hmul : u * Real.log u ≤ u * (u / 3 + 1 / 3) :=
        mul_le_mul_of_nonneg_left hlog' hu0
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (by linarith : 0 ≤ u - 2)
        (by linarith : u - 3 ≤ 0)]

/-- The scalar defect has the exact bounds required for the three-point fiber argument. -/
theorem entropyDefect_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu3 : u ≤ 3) :
    0 ≤ entropyDefect u ∧ entropyDefect u ≤ |u - 1| :=
  ⟨entropyDefect_nonneg hu0, entropyDefect_le_abs_sub_one hu0 hu3⟩

/-- On a one-step fiber with positive base density, the density ratio lies in `[0,3]`. -/
theorem density_ratio_bounds (n : ℕ) (x : ZMod (3 ^ (n + 1)))
    (hbase : 0 < density n (project (Nat.le_succ n) x)) :
    0 ≤ density (n + 1) x / density n (project (Nat.le_succ n) x) ∧
      density (n + 1) x / density n (project (Nat.le_succ n) x) ≤ 3 := by
  have hnonneg : 0 ≤ density (n + 1) x := density_nonneg _ _
  have hupper := density_le_fiber (Nat.le_succ n) x
  have hupper' : density (n + 1) x ≤ 3 * density n (project (Nat.le_succ n) x) := by
    simpa [Nat.succ_eq_add_one] using hupper
  constructor
  · exact div_nonneg hnonneg hbase.le
  · exact (div_le_iff₀ hbase).2 (by simpa [mul_comm] using hupper')

/-- Lower-level entropy is exactly the upper-level mean of its pullback. -/
theorem entropy_pullback (n : ℕ) :
    entropy n = mean (n + 1) (fun x =>
      density n (project (Nat.le_succ n) x) *
        Real.log (density n (project (Nat.le_succ n) x))) := by
  unfold entropy
  exact (mean_project (Nat.le_succ n) _).symm

/-- The zero-base branch of a one-step fiber contributes zero entropy upstairs. -/
theorem entropy_fiber_zero (n : ℕ) (x : ZMod (3 ^ (n + 1)))
    (hbase : density n (project (Nat.le_succ n) x) = 0) :
    density (n + 1) x * Real.log (density (n + 1) x) = 0 := by
  have hzero := density_eq_zero_of_project_eq_zero (Nat.le_succ n) x hbase
  rw [hzero]
  simp

/-- The positive-fiber logarithmic decomposition behind entropy cancellation. -/
theorem entropy_defect_decomposition {f g : ℝ} (hf : 0 < f) (hg : 0 < g) :
    f * Real.log f - g * Real.log g =
      g * entropyDefect (f / g) + (f - g) * (Real.log g + 1) := by
  unfold entropyDefect
  rw [Real.log_div hf.ne' hg.ne']
  field_simp
  ring

/-- One-step projectivity cancels the linear residual in the entropy decomposition. -/
theorem density_increment_mean_zero (n : ℕ) :
    mean (n + 1) (fun x => density (n + 1) x -
      density n (project (Nat.le_succ n) x)) = 0 := by
  rw [mean_sub, mean_density, mean_project (Nat.le_succ n), mean_density]
  ring

private theorem weighted_project {m n : ℕ} (h : m ≤ n) (a : ZMod (3^m) → ℝ) :
    mean n (fun x => density n x * a (project h x)) =
      mean m (fun y => density m y * a y) := by
  classical
  have hs := Finset.sum_fiberwise Finset.univ (project h)
    (fun x => density n x * a (project h x))
  have hf (y : ZMod (3^m)) :
      (∑ x ∈ fiber h y, density n x * a (project h x)) =
        (3 : ℝ)^(n-m) * (density m y * a y) := by
    calc
      _ = ∑ x ∈ fiber h y, density n x * a y := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [(mem_fiber h y x).mp hx]
      _ = _ := by rw [← Finset.sum_mul, density_fiber]; ring
  change (∑ y, ∑ x ∈ fiber h y, density n x * a (project h x)) = _ at hs
  simp_rw [hf] at hs
  rw [← Finset.mul_sum] at hs
  unfold mean
  rw [← hs, scale_eq h]
  field_simp

private theorem residual_cancel (n : ℕ) (a : ZMod (3^n) → ℝ) :
    mean (n+1) (fun x => (density (n+1) x - density n (project (Nat.le_succ n) x)) *
      a (project (Nat.le_succ n) x)) = 0 := by
  simp_rw [sub_mul]
  rw [mean_sub, weighted_project,
    mean_project (Nat.le_succ n) (fun y => density n y * a y)]
  exact sub_self _

/-- Exact one-step entropy increment, with zero fibers included. -/
theorem entropy_increment_defect (n : ℕ) :
    entropy (n+1) - entropy n = mean (n+1) (fun x =>
      density n (project (Nat.le_succ n) x) * entropyDefect
        (density (n+1) x / density n (project (Nat.le_succ n) x))) := by
  have he (x : ZMod (3^(n+1))) :
      density (n+1) x * Real.log (density (n+1) x) -
        density n (project (Nat.le_succ n) x) * Real.log (density n (project (Nat.le_succ n) x)) =
      density n (project (Nat.le_succ n) x) * entropyDefect
        (density (n+1) x / density n (project (Nat.le_succ n) x)) +
      (density (n+1) x-density n (project (Nat.le_succ n) x)) *
        (Real.log (density n (project (Nat.le_succ n) x))+1) := by
    by_cases hg : density n (project (Nat.le_succ n) x) = 0
    · have hz := density_eq_zero_of_project_eq_zero (Nat.le_succ n) x hg
      simp [hg, hz]
    · by_cases hf : density (n+1) x = 0
      · simp [hf, entropyDefect]; ring
      · exact entropy_defect_decomposition
          (lt_of_le_of_ne (density_nonneg _ _) (Ne.symm hf))
          (lt_of_le_of_ne (density_nonneg _ _) (Ne.symm hg))
  rw [entropy_pullback n]
  change mean (n+1) _ - mean (n+1) _ = _
  rw [← mean_sub]
  simp_rw [he]
  rw [mean_add, residual_cancel n (fun y => Real.log (density n y)+1), add_zero]

private theorem weighted_defect_bounds {f g : ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hcap : f ≤ 3*g) :
    0 ≤ g*entropyDefect (f/g) ∧ g*entropyDefect (f/g) ≤ |f-g| := by
  by_cases hz : g = 0
  · have hfz : f = 0 := by subst g; linarith
    simp [hz, hfz]
  · have hgp : 0 < g := lt_of_le_of_ne hg (Ne.symm hz)
    have hb := entropyDefect_bounds (div_nonneg hf hg) ((div_le_iff₀ hgp).2 hcap)
    refine ⟨mul_nonneg hg hb.1, (mul_le_mul_of_nonneg_left hb.2 hg).trans_eq ?_⟩
    rw [show g * |f/g-1| = |g*(f/g-1)| by rw [abs_mul, abs_of_nonneg hg]]
    congr 1
    field_simp

/-- Entropy increases by at most the full, unhalved density L1 oscillation. -/
theorem entropy_increment_l1 (n : ℕ) :
    0 ≤ entropy (n+1)-entropy n ∧
    entropy (n+1)-entropy n ≤ mean (n+1) (fun x =>
      |density (n+1) x-density n (project (Nat.le_succ n) x)|) := by
  rw [entropy_increment_defect]
  have hb (x : ZMod (3^(n+1))) := weighted_defect_bounds
    (density_nonneg (n+1) x) (density_nonneg n (project (Nat.le_succ n) x))
    (show density (n+1) x ≤ 3*density n (project (Nat.le_succ n) x) by
      simpa [Nat.succ_eq_add_one] using density_le_fiber (Nat.le_succ n) x)
  exact ⟨mean_nonneg _ _ (fun x => (hb x).1), mean_mono _ _ _ (fun x => (hb x).2)⟩

private theorem weighted_defect_log_three {f g : ℝ} (hf : 0 ≤ f) (hg : 0 ≤ g)
    (hcap : f ≤ 3*g) : g*entropyDefect (f/g) ≤ f*Real.log 3-f+g := by
  by_cases hz : g = 0
  · have hfz : f = 0 := by subst g; linarith
    simp [hz, hfz]
  · have hgp : 0 < g := lt_of_le_of_ne hg (Ne.symm hz)
    by_cases hfz : f = 0
    · simp [hfz, entropyDefect]
    · have hfp : 0 < f := lt_of_le_of_ne hf (Ne.symm hfz)
      have hl := Real.log_le_log (div_pos hfp hgp) ((div_le_iff₀ hgp).2 hcap)
      have he : g*entropyDefect (f/g) = f*Real.log (f/g)-f+g := by
        unfold entropyDefect
        field_simp
      rw [he]
      nlinarith [mul_le_mul_of_nonneg_left hl hf]

/-- A ternary refinement increases entropy by at most log three. -/
theorem entropy_increment_log_three (n : ℕ) :
    entropy (n+1)-entropy n ≤ Real.log 3 := by
  rw [entropy_increment_defect]
  have hb := mean_mono (n+1) _ _ (fun x => weighted_defect_log_three
    (density_nonneg (n+1) x) (density_nonneg n (project (Nat.le_succ n) x))
    (show density (n+1) x ≤ 3*density n (project (Nat.le_succ n) x) by
      simpa [Nat.succ_eq_add_one] using density_le_fiber (Nat.le_succ n) x))
  refine hb.trans_eq ?_
  rw [mean_add, mean_sub, mean_project (Nat.le_succ n) (density n), mean_density]
  simp_rw [mul_comm (density (n+1) _) (Real.log 3)]
  rw [mean_mul, mean_density, mean_density]
  ring

/-- Order-one entropy increases along the actual projective reference law. -/
theorem entropy_monotone : Monotone entropy := by
  apply monotone_nat_of_le_succ
  intro n
  exact sub_nonneg.mp (entropy_increment_l1 n).1

/-- The normalized reference law has nonnegative order-one entropy at every level. -/
theorem entropy_nonneg (n : ℕ) : 0 ≤ entropy n := by
  simpa only [entropy_zero] using entropy_monotone (Nat.zero_le n)

end WordCertDensity.Reference
