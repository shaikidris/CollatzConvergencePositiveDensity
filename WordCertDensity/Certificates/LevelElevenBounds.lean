/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.CyclicCheckerSoundness
import WordCertDensity.Certificates.LevelTenBounds
import WordCertDensity.Certificates.DepthEleven.Summary

/-! # Actual depth-eleven maximum from a cyclic supersolution -/

namespace WordCertDensity.Certificates

/-- The complete local certificate bounds the actual depth-eleven reference density. -/
theorem levelEleven_upper (x : ZMod (3 ^ 11)) :
    (2 : ℝ) ^ 48 * Reference.density 11 x ≤ levelEleven.lookup x.val := by
  exact checked_cyclic_upper levelTen levelEleven 10 ((2 : ℝ) ^ 48)
    levelTen_upper levelEleven_cyclic x

/-- The retained depth-eleven maximum follows from the actual upper array. -/
theorem maximum_eleven : Reference.maximum 11 ≤ 127 := by
  refine le_trans (integer_maximum_certificate 11 (2 ^ 48) 127 1 (by positivity) (by decide)
    (fun x => levelEleven.lookup x.val) ?_ ?_) ?_
  · intro x
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact levelEleven_upper x
  · intro x
    exact (Nat.mul_le_mul_left 1 (levelEleven_range_cap x)).trans levelEleven_max_comparison
  · norm_num

end WordCertDensity.Certificates
