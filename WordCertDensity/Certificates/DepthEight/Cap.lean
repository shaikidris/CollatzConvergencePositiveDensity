/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.Data.LevelEight

/-! # Complete depth-eight numerical summary -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- The cap bounds every stored entry. -/
theorem levelEight_cap : levelEight.allLE 10508811906322856 = true := by decide +kernel

/-- Scaled maximum comparison. -/
theorem levelEight_max_comparison : 1 * 10508811906322856 ≤ 38 * 2 ^ 48 := by decide +kernel


end WordCertDensity.Certificates
