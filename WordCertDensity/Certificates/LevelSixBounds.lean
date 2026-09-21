/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.PositiveGroupSummary
import WordCertDensity.Certificates.Data.LevelSix
import WordCertDensity.Certificates.LevelFiveBounds

/-! # The complete depth-six bounds for the actual reference law -/

namespace WordCertDensity.Certificates

/-- The complete stored tree bounds the actual depth-six reference density. -/
theorem levelSix_upper (x : ZMod (3 ^ 6)) :
    (2 : ℝ) ^ 48 * Reference.density 6 x ≤ levelSix.lookup x.val := by
  exact checked_direct_upper levelFive levelSix 5 3089969650018044 16 (by decide)
    ((2 : ℝ) ^ 48) (by positivity) levelFive_cap levelFive_upper levelSix_transfer x

/-- The retained depth-six maximum inequality concerns the actual law. -/
theorem maximum_six : Reference.maximum 6 ≤ 17 := by
  refine le_trans (integer_maximum_certificate 6 (2 ^ 48) 17 1 (by positivity) (by decide)
    (fun x => levelSix.lookup x.val) ?_ ?_) ?_
  · intro x
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using levelSix_upper x
  · intro x
    exact (Nat.mul_le_mul_left 1 (levelSix.lookup_le _ levelSix_cap x.val)).trans
      levelSix_max_comparison
  · norm_num

/-- The retained depth-six second moment includes all residues. -/
theorem energy_six : Reference.moment 2 6 ≤ 4001 / 1000 := by
  apply integer_energy_certificate 6 (2 ^ 48) 4001 1000 (by positivity) (by decide)
    (fun x => levelSix.lookup x.val)
  · intro x
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using levelSix_upper x
  · rw [sum_zmod_positive_list (3 ^ 6) (fun i => levelSix.lookup i ^ 2)]
    simp only [show 3 ^ 6 = 729 from rfl]
    rw [← energySum_eq]
    exact levelSix_energy_comparison

/-- Integer square enclosures prove the retained depth-six fractional row. -/
theorem fractional_six : Reference.moment (3 / 2) 6 ≤ 449901 / 250000 := by
  apply integer_fractional_even_certificate 6 24 449901 250000 (by decide)
    (fun x => levelSix.lookup x.val) (fun x => levelSixRoots.lookup x.val)
  · exact levelSix_upper
  · exact levelSix_square_enclosures
  · rw [sum_zmod_positive_list (3 ^ 6) (fun i => levelSix.lookup i * levelSixRoots.lookup i)]
    simp only [show 3 ^ 6 = 729 from rfl, show 3 * 24 = 72 from rfl]
    rw [← fractionalSum_eq]
    exact levelSix_fractional_comparison

end WordCertDensity.Certificates
