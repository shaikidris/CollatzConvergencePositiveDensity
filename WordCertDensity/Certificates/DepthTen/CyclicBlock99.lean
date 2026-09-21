/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.Data.LevelTen

/-! # Depth-ten cyclic supersolution certificates -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Complete local inequalities for this block. -/
theorem levelTen_cyclic_block_99 :
    levelNine.cyclicCheck levelTen 10 50688 512 = true := by decide +kernel

/-- Complete cap inequalities for this block. -/
theorem levelTen_cap_block_99 :
    levelTen.capCheck 23693701508080468 50688 512 = true := by decide +kernel

end WordCertDensity.Certificates
