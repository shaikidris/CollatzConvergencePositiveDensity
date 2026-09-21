/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.PositiveGroupSummary
import WordCertDensity.Certificates.DepthNine.Summary
import WordCertDensity.Certificates.DepthNine.Cap
import WordCertDensity.Certificates.LevelEightBounds

/-! # The complete depth-nine bounds for the actual reference law -/

namespace WordCertDensity.Certificates

/-- The complete stored tree bounds the actual depth-nine reference density. -/
theorem levelNine_upper (x : ZMod (3 ^ 9)) :
    (2 : ℝ) ^ 48 * Reference.density 9 x ≤ levelNine.lookup x.val := by
  exact checked_direct_upper levelEight levelNine 8 10508811906322856 16 (by decide)
    ((2 : ℝ) ^ 48) (by positivity) levelEight_cap levelEight_upper levelNine_transfer x

/-- The retained depth-nine maximum inequality concerns the actual law. -/
theorem maximum_nine : Reference.maximum 9 ≤ 57 := by
  refine le_trans (integer_maximum_certificate 9 (2 ^ 48) 57 1 (by positivity) (by decide)
    (fun x => levelNine.lookup x.val) ?_ ?_) ?_
  · intro x
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact levelNine_upper x
  · intro x
    exact (Nat.mul_le_mul_left 1 (levelNine.lookup_le _ levelNine_cap x.val)).trans
      levelNine_max_comparison
  · norm_num

end WordCertDensity.Certificates
