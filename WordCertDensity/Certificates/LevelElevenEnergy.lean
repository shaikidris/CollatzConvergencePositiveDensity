/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
import WordCertDensity.Certificates.LevelElevenBounds
import WordCertDensity.Certificates.TreeMomentCertificates
import WordCertDensity.Certificates.DepthEleven.Moments

/-! # Actual depth-eleven energy and fractional bounds -/

namespace WordCertDensity.Certificates

/-- The retained depth-eleven second moment includes all residues. -/
theorem energy_eleven : Reference.moment 2 11 ≤ 3167 / 500 := by
  apply integer_energy_tree_certificate 11 177147 (2 ^ 48) 3167 500
    (by decide) (by positivity) (by decide) levelEleven
  · intro x
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact levelEleven_upper x
  · exact levelEleven_energy_comparison

end WordCertDensity.Certificates
