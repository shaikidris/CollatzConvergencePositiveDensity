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
theorem levelEleven_energy_151040 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 151040 128 =
      89153386252383734491792016863948 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_151040 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151040 128 =
      1781319459348228375100063 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_151040 : ∀ i : Fin 128,
    levelEleven.lookup (151040 + i.val) ≤ levelElevenRoots.lookup (151040 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_151168 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 151168 128 =
      22291078130872152374142888330775 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_151168 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151168 128 =
      763518929447911203837119 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_151168 : ∀ i : Fin 128,
    levelEleven.lookup (151168 + i.val) ≤ levelElevenRoots.lookup (151168 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_151296 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 151296 128 =
      38116316497292693489892902713075 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_151296 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151296 128 =
      1073076020796134644253506 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_151296 : ∀ i : Fin 128,
    levelEleven.lookup (151296 + i.val) ≤ levelElevenRoots.lookup (151296 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_151424 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 151424 128 =
      46573954223394698749661632311001 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_151424 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151424 128 =
      1164579825105549422287733 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_151424 : ∀ i : Fin 128,
    levelEleven.lookup (151424 + i.val) ≤ levelElevenRoots.lookup (151424 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_295 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 151040 512 =
      196134735103943279105489440218799 := by
  have h0 := levelEleven_energy_151040
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 151040 256 =
      111444464383255886865934905194723 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 151040 128 128
      89153386252383734491792016863948 22291078130872152374142888330775 h0 levelEleven_energy_151168
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 151040 384 =
      149560780880548580355827807907798 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 151040 256 128
      111444464383255886865934905194723 38116316497292693489892902713075 h1 levelEleven_energy_151296
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 151040 512 =
      196134735103943279105489440218799 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 151040 384 128
      149560780880548580355827807907798 46573954223394698749661632311001 h2 levelEleven_energy_151424
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_295 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151040 512 =
      4782494234697823645478421 := by
  have h0 := levelEleven_fractional_151040
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151040 256 =
      2544838388796139578937182 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151040 128 128
      1781319459348228375100063 763518929447911203837119 h0 levelEleven_fractional_151168
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151040 384 =
      3617914409592274223190688 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151040 256 128
      2544838388796139578937182 1073076020796134644253506 h1 levelEleven_fractional_151296
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151040 512 =
      4782494234697823645478421 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 151040 384 128
      3617914409592274223190688 1164579825105549422287733 h2 levelEleven_fractional_151424
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_295 : ∀ i : Fin 512,
    levelEleven.lookup (151040 + i.val) ≤ levelElevenRoots.lookup (151040 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_151040
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 151040 128 128
    h0 levelEleven_squares_151168
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 151040 256 128
    h1 levelEleven_squares_151296
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 151040 384 128
    h2 levelEleven_squares_151424
  exact h3

end WordCertDensity.Certificates
