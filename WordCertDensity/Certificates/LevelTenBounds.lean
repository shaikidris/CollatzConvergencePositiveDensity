/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.CyclicCheckerSoundness
import WordCertDensity.Certificates.LevelNineBounds
import WordCertDensity.Certificates.DepthTen.Summary

/-! # Actual depth-ten maximum from a cyclic supersolution -/

namespace WordCertDensity.Certificates

/-- The complete local certificate bounds the actual depth-ten reference density. -/
theorem levelTen_upper (x : ZMod (3 ^ 10)) :
    (2 : ℝ) ^ 48 * Reference.density 10 x ≤ levelTen.lookup x.val := by
  exact checked_cyclic_upper levelNine levelTen 9 ((2 : ℝ) ^ 48)
    levelNine_upper levelTen_cyclic x

/-- The retained depth-ten maximum follows from the actual upper array. -/
theorem maximum_ten : Reference.maximum 10 ≤ 85 := by
  refine le_trans (integer_maximum_certificate 10 (2 ^ 48) 85 1 (by positivity) (by decide)
    (fun x => levelTen.lookup x.val) ?_ ?_) ?_
  · intro x
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact levelTen_upper x
  · intro x
    exact (Nat.mul_le_mul_left 1 (levelTen_range_cap x)).trans levelTen_max_comparison
  · norm_num

end WordCertDensity.Certificates
