/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.Data.LevelElevenFast

/-! # Depth-eleven cyclic supersolution certificates -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Complete local inequalities for this block. -/
theorem levelEleven_cyclic_block_62 :
    levelTen.cyclicCheck levelEleven 11 31744 512 = true := by
  rw [← FastPacked.fastCheck_eq]
  decide +kernel

/-- Complete cap inequalities for this block. -/
theorem levelEleven_cap_block_62 :
    levelEleven.capCheck 35561393379481422 31744 512 = true := by decide +kernel

end WordCertDensity.Certificates
