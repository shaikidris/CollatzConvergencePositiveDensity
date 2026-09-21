/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Analytic.OptimizedMixing
import WordCertDensity.Analytic.WidthMinimum

/-!
# Full quantitative reference mixing

The single error envelope retains the universal bound, the optimized power,
and the attained minimum over permitted widths at high levels. The same
canonical coefficient supplies all downstream weaker powers and markers.
-/

namespace WordCertDensity.Analytic

/-- The manuscript's piecewise compact mixing envelope epsilon_m. -/
noncomputable def mixingError (m : ℕ) : ℝ :=
  if m < 2 ^ 80 then min 2 ((mixingCoefficient : ℝ) * (m : ℝ) ^ (-mixingExponent))
  else min (min 2 ((mixingCoefficient : ℝ) * (m : ℝ) ^ (-mixingExponent)))
    (widthMinimum m)

/-- Every positive coarse level has a positive error envelope. -/
theorem mixingError_pos {m : ℕ} (hm : 1 ≤ m) : 0 < mixingError m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hp := mul_pos mixingCoefficient_pos (Real.rpow_pos_of_pos hm0 (-mixingExponent))
  unfold mixingError
  split_ifs with h
  · exact lt_min (by norm_num) hp
  · exact lt_min (lt_min (by norm_num) hp)
      (widthMinimum_pos (by exact_mod_cast (by omega : 1 < m)))

/-- The compact envelope never exceeds the universal probability-mass bound. -/
theorem mixingError_le_two (m : ℕ) : mixingError m ≤ 2 := by
  unfold mixingError
  split_ifs
  · exact min_le_left _ _
  · exact (min_le_left _ _).trans (min_le_left _ _)

/-- The compact envelope retains the optimized power with the canonical coefficient. -/
theorem mixingError_le_power (m : ℕ) : mixingError m ≤
    (mixingCoefficient : ℝ) * (m : ℝ) ^ (-mixingExponent) := by
  unfold mixingError
  split_ifs
  · exact min_le_right _ _
  · exact (min_le_left _ _).trans (min_le_right _ _)

/-- Every permitted high-level width remains a bound on the compact envelope. -/
theorem mixingError_le_width {m : ℕ} (hm : 2 ^ 80 ≤ m) {v : ℝ}
    (hv : v ∈ Set.Icc (80 : ℝ) (679 / 5)) : mixingError m ≤ mixingEnvelope v m := by
  rw [mixingError, if_neg (by omega)]
  exact (min_le_right _ _).trans (widthMinimum_le
    (by exact_mod_cast (by omega : 1 < m)) hv)

/-- The actual reference law satisfies the complete retained envelope (M.target). -/
theorem oscillation_le_mixingError {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    FiniteFourier.oscillation hmn (Reference.mass n) ≤ mixingError m := by
  have htwo : FiniteFourier.oscillation hmn (Reference.mass n) ≤ 2 := by
    rw [FiniteFourier.oscillation_mass]
    exact Reference.fullL1_le_two hmn
  have hpower := oscillation_le_mixing_power hm hmn
  unfold mixingError
  split_ifs with h
  · exact le_min htwo hpower
  · obtain ⟨v, hv, heq, _⟩ := exists_minimizing_width
      (x := (m : ℝ)) (by exact_mod_cast (by omega : 1 < m))
    apply le_min (le_min htwo hpower)
    rw [← heq]
    exact all_high_oscillation_le hv.1 hv.2 (by omega) hmn

/-- Full-group density mixing uses the same compact error envelope. -/
theorem mean_le_mixingError {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    Reference.mean n (fun x =>
      |Reference.density n x - Reference.density m (Reference.project hmn x)|) ≤ mixingError m := by
  rw [← FiniteFourier.oscillation_mass hmn]
  exact oscillation_le_mixingError hm hmn

/-- The envelope has order 92 with the same coefficient. -/
theorem mixingError_le_order92 {m : ℕ} (hm : 1 ≤ m) :
    mixingError m ≤ (mixingCoefficient : ℝ) * (m : ℝ) ^ (-92 : ℝ) :=
  (mixingError_le_power m).trans (mixing_power_le hm (by norm_num [mixingExponent]))

/-- The envelope has order six with the same coefficient. -/
theorem mixingError_le_order6 {m : ℕ} (hm : 1 ≤ m) :
    mixingError m ≤ (mixingCoefficient : ℝ) * (m : ℝ) ^ (-6 : ℝ) :=
  (mixingError_le_power m).trans (mixing_power_le hm (by norm_num [mixingExponent]))

/-- The marker pays exactly two thirds of the full-group density error (M.marker). -/
theorem marker_mean_le_mixingError {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    Reference.mean n (fun x =>
      |Reference.marker n x - Reference.marker m (Reference.project hmn x)|) ≤
        (2 / 3 : ℝ) * mixingError m := by
  rw [Reference.marker_fullL1]
  exact mul_le_mul_of_nonneg_left (mean_le_mixingError hm hmn) (by norm_num)

/-- The sixth-order marker estimate used by the finite graft and terminal constructions. -/
theorem marker_mean_le_order6 {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    Reference.mean n (fun x =>
      |Reference.marker n x - Reference.marker m (Reference.project hmn x)|) ≤
        (2 / 3 : ℝ) * (mixingCoefficient : ℝ) / (m : ℝ) ^ 6 := by
  have h := (marker_mean_le_mixingError hm hmn).trans
    (mul_le_mul_of_nonneg_left (mixingError_le_order6 hm) (by norm_num : (0 : ℝ) ≤ 2 / 3))
  simpa only [Real.rpow_neg (Nat.cast_nonneg m), Real.rpow_natCast, Real.rpow_ofNat,
    div_eq_mul_inv, mul_assoc] using h

end WordCertDensity.Analytic
