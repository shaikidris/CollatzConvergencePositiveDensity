/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module
public import WordCertDensity.Certificates.DepthNine.Join0
public import WordCertDensity.Certificates.DepthNine.Join1
public import WordCertDensity.Certificates.DepthNine.Join2
public import WordCertDensity.Certificates.DepthNine.Join3
public import WordCertDensity.Certificates.DepthNine.Join4
public import WordCertDensity.Certificates.DepthNine.Join5
public import WordCertDensity.Certificates.DepthNine.Join6
public import WordCertDensity.Certificates.DepthNine.Join7
public import WordCertDensity.Certificates.DepthNine.Join8
public import WordCertDensity.Certificates.DepthNine.Join9
/-! # Depth-nine integer certificate component -/

@[expose] public section
namespace WordCertDensity.Certificates
/-- Exact finite certificate for the stated depth-nine range or bound. -/
theorem levelNine_transfer : levelNine.checkRange (levelEight.directEntry 10508811906322856 9 16) 0 19683 = true := by
  have h0 := levelNine_group_0
  have h1 := Entries.checkRange_append levelNine _ 0 2048 2048 h0 levelNine_group_1
  have h2 := Entries.checkRange_append levelNine _ 0 4096 2048 h1 levelNine_group_2
  have h3 := Entries.checkRange_append levelNine _ 0 6144 2048 h2 levelNine_group_3
  have h4 := Entries.checkRange_append levelNine _ 0 8192 2048 h3 levelNine_group_4
  have h5 := Entries.checkRange_append levelNine _ 0 10240 2048 h4 levelNine_group_5
  have h6 := Entries.checkRange_append levelNine _ 0 12288 2048 h5 levelNine_group_6
  have h7 := Entries.checkRange_append levelNine _ 0 14336 2048 h6 levelNine_group_7
  have h8 := Entries.checkRange_append levelNine _ 0 16384 2048 h7 levelNine_group_8
  have h9 := Entries.checkRange_append levelNine _ 0 18432 1251 h8 levelNine_group_9
  exact h9
end WordCertDensity.Certificates
