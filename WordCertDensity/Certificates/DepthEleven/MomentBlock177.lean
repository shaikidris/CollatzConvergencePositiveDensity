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
theorem levelEleven_energy_90624 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 90624 128 =
      48535440459496763169164327192449 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_90624 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90624 128 =
      1151837156331361624286688 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_90624 : ∀ i : Fin 128,
    levelEleven.lookup (90624 + i.val) ≤ levelElevenRoots.lookup (90624 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_90752 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 90752 128 =
      23046282525842076657675266396001 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_90752 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90752 128 =
      791471922457761365853748 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_90752 : ∀ i : Fin 128,
    levelEleven.lookup (90752 + i.val) ≤ levelElevenRoots.lookup (90752 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_90880 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 90880 128 =
      34815080218129005014794930366714 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_90880 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90880 128 =
      981570112886532287413264 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_90880 : ∀ i : Fin 128,
    levelEleven.lookup (90880 + i.val) ≤ levelElevenRoots.lookup (90880 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_91008 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 91008 128 =
      128367605651338689361620147883049 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_91008 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 91008 128 =
      1883536852550669861554298 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_91008 : ∀ i : Fin 128,
    levelEleven.lookup (91008 + i.val) ≤ levelElevenRoots.lookup (91008 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_177 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 90624 512 =
      234764408854806534203254671838213 := by
  have h0 := levelEleven_energy_90624
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 90624 256 =
      71581722985338839826839593588450 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 90624 128 128
      48535440459496763169164327192449 23046282525842076657675266396001 h0 levelEleven_energy_90752
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 90624 384 =
      106396803203467844841634523955164 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 90624 256 128
      71581722985338839826839593588450 34815080218129005014794930366714 h1 levelEleven_energy_90880
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 90624 512 =
      234764408854806534203254671838213 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 90624 384 128
      106396803203467844841634523955164 128367605651338689361620147883049 h2 levelEleven_energy_91008
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_177 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90624 512 =
      4808416044226325139107998 := by
  have h0 := levelEleven_fractional_90624
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90624 256 =
      1943309078789122990140436 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90624 128 128
      1151837156331361624286688 791471922457761365853748 h0 levelEleven_fractional_90752
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90624 384 =
      2924879191675655277553700 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90624 256 128
      1943309078789122990140436 981570112886532287413264 h1 levelEleven_fractional_90880
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90624 512 =
      4808416044226325139107998 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 90624 384 128
      2924879191675655277553700 1883536852550669861554298 h2 levelEleven_fractional_91008
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_177 : ∀ i : Fin 512,
    levelEleven.lookup (90624 + i.val) ≤ levelElevenRoots.lookup (90624 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_90624
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 90624 128 128
    h0 levelEleven_squares_90752
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 90624 256 128
    h1 levelEleven_squares_90880
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 90624 384 128
    h2 levelEleven_squares_91008
  exact h3

end WordCertDensity.Certificates
