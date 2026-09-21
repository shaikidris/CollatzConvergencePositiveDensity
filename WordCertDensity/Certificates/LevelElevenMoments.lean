/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.LevelElevenEnergy
import WordCertDensity.Certificates.DepthEleven.Moments

/-! # Actual depth-eleven energy and fractional bounds -/

namespace WordCertDensity.Certificates

/-- Integer square enclosures prove the retained depth-eleven fractional row. -/
theorem fractional_eleven : Reference.moment (3 / 2) 11 ≤ 259093 / 125000 := by
  apply integer_fractional_tree_certificate 11 177147 24 259093 125000
    (by decide) (by decide) levelEleven levelElevenRoots
  · exact levelEleven_upper
  · intro x
    exact levelEleven_square_enclosures x
  · exact levelEleven_fractional_comparison

end WordCertDensity.Certificates
