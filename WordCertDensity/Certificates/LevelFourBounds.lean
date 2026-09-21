/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.Data.LevelFour
import WordCertDensity.Certificates.LevelThreeBounds

/-! # The complete depth-four bounds for the actual reference law -/

namespace WordCertDensity.Certificates

/-- The complete stored tree bounds the actual depth-four reference density. -/
theorem levelFour_upper (x : ZMod (3 ^ 4)) :
    (2 : ℝ) ^ 48 * Reference.density 4 x ≤ levelFour.lookup x.val := by
  exact checked_direct_upper levelThree levelFour 3 1350117382722123 16 (by decide)
    ((2 : ℝ) ^ 48) (by positivity) levelThree_cap levelThree_upper levelFour_transfer x

/-- The retained depth-four maximum inequality concerns the actual law. -/
theorem maximum_four : Reference.maximum 4 ≤ 73 / 10 := by
  apply integer_maximum_certificate 4 (2 ^ 48) 73 10 (by positivity) (by decide)
    (fun x => levelFour.lookup x.val)
  · intro x
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using levelFour_upper x
  · intro x
    exact (Nat.mul_le_mul_left 10 (levelFour.lookup_le _ levelFour_cap x.val)).trans
      levelFour_max_comparison

/-- The retained depth-four second moment includes all residues. -/
theorem energy_four : Reference.moment 2 4 ≤ 3069 / 1000 := by
  apply integer_energy_certificate 4 (2 ^ 48) 3069 1000 (by positivity) (by decide)
    (fun x => levelFour.lookup x.val)
  · intro x
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using levelFour_upper x
  · change 1000 * (∑ x : ZMod (80 + 1), levelFour.lookup x.val ^ 2) ≤ _
    rw [sum_zmod_succ_list 80 (fun i => levelFour.lookup i ^ 2)]
    exact levelFour_energy_comparison

/-- Integer square enclosures prove the retained depth-four fractional row. -/
theorem fractional_four : Reference.moment (3 / 2) 4 ≤ 32779 / 20000 := by
  apply integer_fractional_even_certificate 4 24 32779 20000 (by decide)
    (fun x => levelFour.lookup x.val) (fun x => levelFourRoots.lookup x.val)
  · exact levelFour_upper
  · exact levelFour_square_enclosures
  · change 20000 * (∑ x : ZMod (80 + 1),
      levelFour.lookup x.val * levelFourRoots.lookup x.val) ≤ _
    rw [sum_zmod_succ_list 80 (fun i => levelFour.lookup i * levelFourRoots.lookup i)]
    exact levelFour_fractional_comparison

end WordCertDensity.Certificates
