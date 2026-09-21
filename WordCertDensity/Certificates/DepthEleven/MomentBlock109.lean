/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Authors: Idris Ali Shaik
-/
module

public import WordCertDensity.Certificates.Data.LevelElevenRoots

/-! # Bounded depth-eleven moment certificates -/

@[expose] public section

namespace WordCertDensity.Certificates

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_55808 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 55808 128 =
      28091136070984057232137189102300 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_55808 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55808 128 =
      917885225398785213700419 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_55808 : ∀ i : Fin 128,
    levelEleven.lookup (55808 + i.val) ≤ levelElevenRoots.lookup (55808 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_55936 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 55936 128 =
      47669691850988968964170315561441 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_55936 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55936 128 =
      1162767909529870833087269 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_55936 : ∀ i : Fin 128,
    levelEleven.lookup (55936 + i.val) ≤ levelElevenRoots.lookup (55936 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_56064 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 56064 128 =
      71976161729444479821506809435607 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_56064 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56064 128 =
      1403131056704837533523338 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_56064 : ∀ i : Fin 128,
    levelEleven.lookup (56064 + i.val) ≤ levelElevenRoots.lookup (56064 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_56192 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 56192 128 =
      73229716794862571556655874210171 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_56192 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 56192 128 =
      1522679378793527124990031 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_56192 : ∀ i : Fin 128,
    levelEleven.lookup (56192 + i.val) ≤ levelElevenRoots.lookup (56192 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_109 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 55808 512 =
      220966706446280077574470188309519 := by
  have h0 := levelEleven_energy_55808
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 55808 256 =
      75760827921973026196307504663741 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 55808 128 128
      28091136070984057232137189102300 47669691850988968964170315561441 h0 levelEleven_energy_55936
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 55808 384 =
      147736989651417506017814314099348 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 55808 256 128
      75760827921973026196307504663741 71976161729444479821506809435607 h1 levelEleven_energy_56064
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 55808 512 =
      220966706446280077574470188309519 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 55808 384 128
      147736989651417506017814314099348 73229716794862571556655874210171 h2 levelEleven_energy_56192
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_109 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55808 512 =
      5006463570427020705301057 := by
  have h0 := levelEleven_fractional_55808
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55808 256 =
      2080653134928656046787688 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55808 128 128
      917885225398785213700419 1162767909529870833087269 h0 levelEleven_fractional_55936
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55808 384 =
      3483784191633493580311026 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55808 256 128
      2080653134928656046787688 1403131056704837533523338 h1 levelEleven_fractional_56064
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55808 512 =
      5006463570427020705301057 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55808 384 128
      3483784191633493580311026 1522679378793527124990031 h2 levelEleven_fractional_56192
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_109 : ∀ i : Fin 512,
    levelEleven.lookup (55808 + i.val) ≤ levelElevenRoots.lookup (55808 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_55808
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 55808 128 128
    h0 levelEleven_squares_55936
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 55808 256 128
    h1 levelEleven_squares_56064
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 55808 384 128
    h2 levelEleven_squares_56192
  exact h3

end WordCertDensity.Certificates
