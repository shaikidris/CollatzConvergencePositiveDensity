/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.Data.LevelEleven

/-! # Depth-eleven cyclic supersolution certificates -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Complete local inequalities for this block. -/
theorem levelEleven_cyclic_block_184 :
    levelTen.cyclicCheck levelEleven 11 94208 512 = true := by decide +kernel

/-- Complete cap inequalities for this block. -/
theorem levelEleven_cap_block_184 :
    levelEleven.capCheck 35561393379481422 94208 512 = true := by decide +kernel

end WordCertDensity.Certificates
