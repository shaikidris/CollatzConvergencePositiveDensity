/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.PositiveGroupSummary
import WordCertDensity.Certificates.Data.LevelFive
import WordCertDensity.Certificates.LevelFourBounds

/-! # The complete depth-five bounds for the actual reference law -/

namespace WordCertDensity.Certificates

/-- The complete stored tree bounds the actual depth-five reference density. -/
theorem levelFive_upper (x : ZMod (3 ^ 5)) :
    (2 : ℝ) ^ 48 * Reference.density 5 x ≤ levelFive.lookup x.val := by
  exact checked_direct_upper levelFour levelFive 4 2045911758830089 16 (by decide)
    ((2 : ℝ) ^ 48) (by positivity) levelFour_cap levelFour_upper levelFive_transfer x

/-- The retained depth-five maximum inequality concerns the actual law. -/
theorem maximum_five : Reference.maximum 5 ≤ 11 := by
  refine le_trans (integer_maximum_certificate 5 (2 ^ 48) 11 1 (by positivity) (by decide)
    (fun x => levelFive.lookup x.val) ?_ ?_) ?_
  · intro x
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using levelFive_upper x
  · intro x
    exact (Nat.mul_le_mul_left 1 (levelFive.lookup_le _ levelFive_cap x.val)).trans
      levelFive_max_comparison
  · norm_num

/-- The retained depth-five second moment includes all residues. -/
theorem energy_five : Reference.moment 2 5 ≤ 707 / 200 := by
  apply integer_energy_certificate 5 (2 ^ 48) 707 200 (by positivity) (by decide)
    (fun x => levelFive.lookup x.val)
  · intro x
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using levelFive_upper x
  · rw [sum_zmod_positive_list (3 ^ 5) (fun i => levelFive.lookup i ^ 2)]
    simp only [show 3 ^ 5 = 243 from rfl]
    rw [← energySum_eq]
    exact levelFive_energy_comparison

/-- Integer square enclosures prove the retained depth-five fractional row. -/
theorem fractional_five : Reference.moment (3 / 2) 5 ≤ 862279 / 500000 := by
  apply integer_fractional_even_certificate 5 24 862279 500000 (by decide)
    (fun x => levelFive.lookup x.val) (fun x => levelFiveRoots.lookup x.val)
  · exact levelFive_upper
  · exact levelFive_square_enclosures
  · rw [sum_zmod_positive_list (3 ^ 5) (fun i => levelFive.lookup i * levelFiveRoots.lookup i)]
    simp only [show 3 ^ 5 = 243 from rfl, show 3 * 24 = 72 from rfl]
    rw [← fractionalSum_eq]
    exact levelFive_fractional_comparison

end WordCertDensity.Certificates
