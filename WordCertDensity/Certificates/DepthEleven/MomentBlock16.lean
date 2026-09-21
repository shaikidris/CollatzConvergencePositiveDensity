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
theorem levelEleven_energy_8192 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 8192 128 =
      54371529386659798270118335065313 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_8192 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8192 128 =
      1205701468977081931684521 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_8192 : ∀ i : Fin 128,
    levelEleven.lookup (8192 + i.val) ≤ levelElevenRoots.lookup (8192 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_8320 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 8320 128 =
      38041901810548076564340423010817 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_8320 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8320 128 =
      1057832796418363125528894 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_8320 : ∀ i : Fin 128,
    levelEleven.lookup (8320 + i.val) ≤ levelElevenRoots.lookup (8320 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_8448 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 8448 128 =
      25374945347317778095455813123979 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_8448 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8448 128 =
      823113060314293332299407 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_8448 : ∀ i : Fin 128,
    levelEleven.lookup (8448 + i.val) ≤ levelElevenRoots.lookup (8448 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_8576 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 8576 128 =
      121280608585818758882714941632702 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_8576 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8576 128 =
      1973490946964313347145304 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_8576 : ∀ i : Fin 128,
    levelEleven.lookup (8576 + i.val) ≤ levelElevenRoots.lookup (8576 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_16 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 8192 512 =
      239068985130344411812629512832811 := by
  have h0 := levelEleven_energy_8192
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 8192 256 =
      92413431197207874834458758076130 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 8192 128 128
      54371529386659798270118335065313 38041901810548076564340423010817 h0 levelEleven_energy_8320
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 8192 384 =
      117788376544525652929914571200109 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 8192 256 128
      92413431197207874834458758076130 25374945347317778095455813123979 h1 levelEleven_energy_8448
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 8192 512 =
      239068985130344411812629512832811 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 8192 384 128
      117788376544525652929914571200109 121280608585818758882714941632702 h2 levelEleven_energy_8576
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_16 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8192 512 =
      5060138272674051736658126 := by
  have h0 := levelEleven_fractional_8192
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8192 256 =
      2263534265395445057213415 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8192 128 128
      1205701468977081931684521 1057832796418363125528894 h0 levelEleven_fractional_8320
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8192 384 =
      3086647325709738389512822 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8192 256 128
      2263534265395445057213415 823113060314293332299407 h1 levelEleven_fractional_8448
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8192 512 =
      5060138272674051736658126 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 8192 384 128
      3086647325709738389512822 1973490946964313347145304 h2 levelEleven_fractional_8576
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_16 : ∀ i : Fin 512,
    levelEleven.lookup (8192 + i.val) ≤ levelElevenRoots.lookup (8192 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_8192
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 8192 128 128
    h0 levelEleven_squares_8320
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 8192 256 128
    h1 levelEleven_squares_8448
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 8192 384 128
    h2 levelEleven_squares_8576
  exact h3

end WordCertDensity.Certificates
