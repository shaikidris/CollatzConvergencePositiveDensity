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
theorem levelEleven_energy_50176 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 50176 128 =
      71695508526852188212365877704685 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_50176 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50176 128 =
      1596179096248772842353109 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_50176 : ∀ i : Fin 128,
    levelEleven.lookup (50176 + i.val) ≤ levelElevenRoots.lookup (50176 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_50304 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 50304 128 =
      21924585454516414068993243194681 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_50304 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50304 128 =
      711855659241016016462185 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_50304 : ∀ i : Fin 128,
    levelEleven.lookup (50304 + i.val) ≤ levelElevenRoots.lookup (50304 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_50432 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 50432 128 =
      103879749700131169671995211059628 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_50432 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50432 128 =
      1904951477773126181494531 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_50432 : ∀ i : Fin 128,
    levelEleven.lookup (50432 + i.val) ≤ levelElevenRoots.lookup (50432 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_50560 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 50560 128 =
      19425860004744041869897758523226 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_50560 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50560 128 =
      725338550945217545489844 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_50560 : ∀ i : Fin 128,
    levelEleven.lookup (50560 + i.val) ≤ levelElevenRoots.lookup (50560 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_98 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 50176 512 =
      216925703686243813823252090482220 := by
  have h0 := levelEleven_energy_50176
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 50176 256 =
      93620093981368602281359120899366 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 50176 128 128
      71695508526852188212365877704685 21924585454516414068993243194681 h0 levelEleven_energy_50304
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 50176 384 =
      197499843681499771953354331958994 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 50176 256 128
      93620093981368602281359120899366 103879749700131169671995211059628 h1 levelEleven_energy_50432
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 50176 512 =
      216925703686243813823252090482220 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 50176 384 128
      197499843681499771953354331958994 19425860004744041869897758523226 h2 levelEleven_energy_50560
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_98 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50176 512 =
      4938324784208132585799669 := by
  have h0 := levelEleven_fractional_50176
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50176 256 =
      2308034755489788858815294 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50176 128 128
      1596179096248772842353109 711855659241016016462185 h0 levelEleven_fractional_50304
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50176 384 =
      4212986233262915040309825 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50176 256 128
      2308034755489788858815294 1904951477773126181494531 h1 levelEleven_fractional_50432
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50176 512 =
      4938324784208132585799669 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 50176 384 128
      4212986233262915040309825 725338550945217545489844 h2 levelEleven_fractional_50560
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_98 : ∀ i : Fin 512,
    levelEleven.lookup (50176 + i.val) ≤ levelElevenRoots.lookup (50176 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_50176
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 50176 128 128
    h0 levelEleven_squares_50304
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 50176 256 128
    h1 levelEleven_squares_50432
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 50176 384 128
    h2 levelEleven_squares_50560
  exact h3

end WordCertDensity.Certificates
