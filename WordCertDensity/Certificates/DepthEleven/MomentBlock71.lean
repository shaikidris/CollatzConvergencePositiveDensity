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
theorem levelEleven_energy_36352 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 36352 128 =
      175500369915823159864367684131920 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_36352 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36352 128 =
      2425120197116840030506135 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_36352 : ∀ i : Fin 128,
    levelEleven.lookup (36352 + i.val) ≤ levelElevenRoots.lookup (36352 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_36480 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 36480 128 =
      17889614098592710156878315096950 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_36480 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36480 128 =
      638704498700343390627497 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_36480 : ∀ i : Fin 128,
    levelEleven.lookup (36480 + i.val) ≤ levelElevenRoots.lookup (36480 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_36608 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 36608 128 =
      34392780392183032140116467586258 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_36608 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36608 128 =
      978813150714333414515057 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_36608 : ∀ i : Fin 128,
    levelEleven.lookup (36608 + i.val) ≤ levelElevenRoots.lookup (36608 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_36736 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 36736 128 =
      42190382127205988660790833457472 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_36736 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36736 128 =
      1080840285902224770802724 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_36736 : ∀ i : Fin 128,
    levelEleven.lookup (36736 + i.val) ≤ levelElevenRoots.lookup (36736 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_71 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 36352 512 =
      269973146533804890822153300272600 := by
  have h0 := levelEleven_energy_36352
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 36352 256 =
      193389984014415870021245999228870 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 36352 128 128
      175500369915823159864367684131920 17889614098592710156878315096950 h0 levelEleven_energy_36480
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 36352 384 =
      227782764406598902161362466815128 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 36352 256 128
      193389984014415870021245999228870 34392780392183032140116467586258 h1 levelEleven_energy_36608
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 36352 512 =
      269973146533804890822153300272600 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 36352 384 128
      227782764406598902161362466815128 42190382127205988660790833457472 h2 levelEleven_energy_36736
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_71 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36352 512 =
      5123478132433741606451413 := by
  have h0 := levelEleven_fractional_36352
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36352 256 =
      3063824695817183421133632 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36352 128 128
      2425120197116840030506135 638704498700343390627497 h0 levelEleven_fractional_36480
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36352 384 =
      4042637846531516835648689 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36352 256 128
      3063824695817183421133632 978813150714333414515057 h1 levelEleven_fractional_36608
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36352 512 =
      5123478132433741606451413 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 36352 384 128
      4042637846531516835648689 1080840285902224770802724 h2 levelEleven_fractional_36736
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_71 : ∀ i : Fin 512,
    levelEleven.lookup (36352 + i.val) ≤ levelElevenRoots.lookup (36352 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_36352
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 36352 128 128
    h0 levelEleven_squares_36480
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 36352 256 128
    h1 levelEleven_squares_36608
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 36352 384 128
    h2 levelEleven_squares_36736
  exact h3

end WordCertDensity.Certificates
