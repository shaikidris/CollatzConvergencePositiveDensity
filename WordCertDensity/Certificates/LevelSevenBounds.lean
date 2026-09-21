/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.PositiveGroupSummary
import WordCertDensity.Certificates.Data.LevelSeven
import WordCertDensity.Certificates.LevelSixBounds

/-! # The complete depth-seven bounds for the actual reference law -/

namespace WordCertDensity.Certificates

/-- The complete stored tree bounds the actual depth-seven reference density. -/
theorem levelSeven_upper (x : ZMod (3 ^ 7)) :
    (2 : ℝ) ^ 48 * Reference.density 7 x ≤ levelSeven.lookup x.val := by
  exact checked_direct_upper levelSix levelSeven 6 4651932141793643 16 (by decide)
    ((2 : ℝ) ^ 48) (by positivity) levelSix_cap levelSix_upper levelSeven_transfer x

/-- The retained depth-seven maximum inequality concerns the actual law. -/
theorem maximum_seven : Reference.maximum 7 ≤ 25 := by
  refine le_trans (integer_maximum_certificate 7 (2 ^ 48) 25 1 (by positivity) (by decide)
    (fun x => levelSeven.lookup x.val) ?_ ?_) ?_
  · intro x
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using levelSeven_upper x
  · intro x
    exact (Nat.mul_le_mul_left 1 (levelSeven.lookup_le _ levelSeven_cap x.val)).trans
      levelSeven_max_comparison
  · norm_num

/-- The retained depth-seven second moment includes all residues. -/
theorem energy_seven : Reference.moment 2 7 ≤ 2233 / 500 := by
  apply integer_energy_certificate 7 (2 ^ 48) 2233 500 (by positivity) (by decide)
    (fun x => levelSeven.lookup x.val)
  · intro x
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using levelSeven_upper x
  · rw [sum_zmod_positive_list (3 ^ 7) (fun i => levelSeven.lookup i ^ 2)]
    simp only [show 3 ^ 7 = 2187 from rfl]
    rw [← energySum_eq]
    exact levelSeven_energy_comparison

/-- Integer square enclosures prove the retained depth-seven fractional row. -/
theorem fractional_seven : Reference.moment (3 / 2) 7 ≤ 116627 / 62500 := by
  apply integer_fractional_even_certificate 7 24 116627 62500 (by decide)
    (fun x => levelSeven.lookup x.val) (fun x => levelSevenRoots.lookup x.val)
  · exact levelSeven_upper
  · exact levelSeven_square_enclosures
  · rw [sum_zmod_positive_list (3 ^ 7) (fun i => levelSeven.lookup i * levelSevenRoots.lookup i)]
    simp only [show 3 ^ 7 = 2187 from rfl, show 3 * 24 = 72 from rfl]
    rw [← fractionalSum_eq]
    exact levelSeven_fractional_comparison

end WordCertDensity.Certificates
