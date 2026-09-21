/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.PositiveGroupSummary
import WordCertDensity.Certificates.DepthEight.Summary
import WordCertDensity.Certificates.LevelSevenBounds

/-! # The complete depth-eight bounds for the actual reference law -/

namespace WordCertDensity.Certificates

/-- The complete stored tree bounds the actual depth-eight reference density. -/
theorem levelEight_upper (x : ZMod (3 ^ 8)) :
    (2 : ℝ) ^ 48 * Reference.density 8 x ≤ levelEight.lookup x.val := by
  exact checked_direct_upper levelSeven levelEight 7 6994258928192191 16 (by decide)
    ((2 : ℝ) ^ 48) (by positivity) levelSeven_cap levelSeven_upper levelEight_transfer x

/-- The retained depth-eight maximum inequality concerns the actual law. -/
theorem maximum_eight : Reference.maximum 8 ≤ 38 := by
  refine le_trans (integer_maximum_certificate 8 (2 ^ 48) 38 1 (by positivity) (by decide)
    (fun x => levelEight.lookup x.val) ?_ ?_) ?_
  · intro x
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using levelEight_upper x
  · intro x
    exact (Nat.mul_le_mul_left 1 (levelEight.lookup_le _ levelEight_cap x.val)).trans
      levelEight_max_comparison
  · norm_num

end WordCertDensity.Certificates
