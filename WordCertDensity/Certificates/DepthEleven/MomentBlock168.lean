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
theorem levelEleven_energy_86016 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 86016 128 =
      70047223984472954906233755134795 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_86016 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86016 128 =
      1210205710083205011869266 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_86016 : ∀ i : Fin 128,
    levelEleven.lookup (86016 + i.val) ≤ levelElevenRoots.lookup (86016 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_86144 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 86144 128 =
      34313168610861873689025189534194 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_86144 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86144 128 =
      986360105871811910773554 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_86144 : ∀ i : Fin 128,
    levelEleven.lookup (86144 + i.val) ≤ levelElevenRoots.lookup (86144 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_86272 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 86272 128 =
      73745546420541848859417742162498 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_86272 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86272 128 =
      1475905898099975692059867 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_86272 : ∀ i : Fin 128,
    levelEleven.lookup (86272 + i.val) ≤ levelElevenRoots.lookup (86272 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_86400 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 86400 128 =
      29404463822246532046374138834562 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_86400 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86400 128 =
      894964684980271759009527 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_86400 : ∀ i : Fin 128,
    levelEleven.lookup (86400 + i.val) ≤ levelElevenRoots.lookup (86400 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_168 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 86016 512 =
      207510402838123209501050825666049 := by
  have h0 := levelEleven_energy_86016
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 86016 256 =
      104360392595334828595258944668989 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 86016 128 128
      70047223984472954906233755134795 34313168610861873689025189534194 h0 levelEleven_energy_86144
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 86016 384 =
      178105939015876677454676686831487 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 86016 256 128
      104360392595334828595258944668989 73745546420541848859417742162498 h1 levelEleven_energy_86272
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 86016 512 =
      207510402838123209501050825666049 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 86016 384 128
      178105939015876677454676686831487 29404463822246532046374138834562 h2 levelEleven_energy_86400
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_168 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86016 512 =
      4567436399035264373712214 := by
  have h0 := levelEleven_fractional_86016
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86016 256 =
      2196565815955016922642820 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86016 128 128
      1210205710083205011869266 986360105871811910773554 h0 levelEleven_fractional_86144
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86016 384 =
      3672471714054992614702687 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86016 256 128
      2196565815955016922642820 1475905898099975692059867 h1 levelEleven_fractional_86272
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86016 512 =
      4567436399035264373712214 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 86016 384 128
      3672471714054992614702687 894964684980271759009527 h2 levelEleven_fractional_86400
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_168 : ∀ i : Fin 512,
    levelEleven.lookup (86016 + i.val) ≤ levelElevenRoots.lookup (86016 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_86016
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 86016 128 128
    h0 levelEleven_squares_86144
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 86016 256 128
    h1 levelEleven_squares_86272
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 86016 384 128
    h2 levelEleven_squares_86400
  exact h3

end WordCertDensity.Certificates
