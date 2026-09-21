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
theorem levelEleven_energy_55296 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 55296 128 =
      48806123762868619382820514064591 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_55296 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55296 128 =
      1225398132373263097907300 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_55296 : ∀ i : Fin 128,
    levelEleven.lookup (55296 + i.val) ≤ levelElevenRoots.lookup (55296 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_55424 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 55424 128 =
      26863567203097191680076890091834 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_55424 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55424 128 =
      816889357847442437984728 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_55424 : ∀ i : Fin 128,
    levelEleven.lookup (55424 + i.val) ≤ levelElevenRoots.lookup (55424 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_55552 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 55552 128 =
      125091058262158870612688212035720 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_55552 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55552 128 =
      2127626811371679689234939 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_55552 : ∀ i : Fin 128,
    levelEleven.lookup (55552 + i.val) ≤ levelElevenRoots.lookup (55552 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_55680 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 55680 128 =
      62053018507984663146007817464863 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_55680 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55680 128 =
      1204736203813801025006750 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_55680 : ∀ i : Fin 128,
    levelEleven.lookup (55680 + i.val) ≤ levelElevenRoots.lookup (55680 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_108 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 55296 512 =
      262813767736109344821593433657008 := by
  have h0 := levelEleven_energy_55296
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 55296 256 =
      75669690965965811062897404156425 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 55296 128 128
      48806123762868619382820514064591 26863567203097191680076890091834 h0 levelEleven_energy_55424
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 55296 384 =
      200760749228124681675585616192145 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 55296 256 128
      75669690965965811062897404156425 125091058262158870612688212035720 h1 levelEleven_energy_55552
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 55296 512 =
      262813767736109344821593433657008 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 55296 384 128
      200760749228124681675585616192145 62053018507984663146007817464863 h2 levelEleven_energy_55680
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_108 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55296 512 =
      5374650505406186250133717 := by
  have h0 := levelEleven_fractional_55296
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55296 256 =
      2042287490220705535892028 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55296 128 128
      1225398132373263097907300 816889357847442437984728 h0 levelEleven_fractional_55424
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55296 384 =
      4169914301592385225126967 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55296 256 128
      2042287490220705535892028 2127626811371679689234939 h1 levelEleven_fractional_55552
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55296 512 =
      5374650505406186250133717 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 55296 384 128
      4169914301592385225126967 1204736203813801025006750 h2 levelEleven_fractional_55680
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_108 : ∀ i : Fin 512,
    levelEleven.lookup (55296 + i.val) ≤ levelElevenRoots.lookup (55296 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_55296
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 55296 128 128
    h0 levelEleven_squares_55424
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 55296 256 128
    h1 levelEleven_squares_55552
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 55296 384 128
    h2 levelEleven_squares_55680
  exact h3

end WordCertDensity.Certificates
