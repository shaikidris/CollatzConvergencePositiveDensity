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
theorem levelEleven_energy_70656 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 70656 128 =
      15574560504122774017029246073575 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_70656 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70656 128 =
      586294383622552458474567 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_70656 : ∀ i : Fin 128,
    levelEleven.lookup (70656 + i.val) ≤ levelElevenRoots.lookup (70656 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_70784 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 70784 128 =
      51286890479275391897940153572595 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_70784 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70784 128 =
      1267667861374386445034282 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_70784 : ∀ i : Fin 128,
    levelEleven.lookup (70784 + i.val) ≤ levelElevenRoots.lookup (70784 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_70912 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 70912 128 =
      47354975948650431929712912834734 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_70912 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70912 128 =
      1198990131223981495791052 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_70912 : ∀ i : Fin 128,
    levelEleven.lookup (70912 + i.val) ≤ levelElevenRoots.lookup (70912 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_71040 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 71040 128 =
      39545973478256525987694751302745 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_71040 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 71040 128 =
      1071274494498647595403765 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_71040 : ∀ i : Fin 128,
    levelEleven.lookup (71040 + i.val) ≤ levelElevenRoots.lookup (71040 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_138 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 70656 512 =
      153762400410305123832377063783649 := by
  have h0 := levelEleven_energy_70656
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 70656 256 =
      66861450983398165914969399646170 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 70656 128 128
      15574560504122774017029246073575 51286890479275391897940153572595 h0 levelEleven_energy_70784
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 70656 384 =
      114216426932048597844682312480904 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 70656 256 128
      66861450983398165914969399646170 47354975948650431929712912834734 h1 levelEleven_energy_70912
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 70656 512 =
      153762400410305123832377063783649 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 70656 384 128
      114216426932048597844682312480904 39545973478256525987694751302745 h2 levelEleven_energy_71040
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_138 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70656 512 =
      4124226870719567994703666 := by
  have h0 := levelEleven_fractional_70656
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70656 256 =
      1853962244996938903508849 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70656 128 128
      586294383622552458474567 1267667861374386445034282 h0 levelEleven_fractional_70784
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70656 384 =
      3052952376220920399299901 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70656 256 128
      1853962244996938903508849 1198990131223981495791052 h1 levelEleven_fractional_70912
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70656 512 =
      4124226870719567994703666 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 70656 384 128
      3052952376220920399299901 1071274494498647595403765 h2 levelEleven_fractional_71040
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_138 : ∀ i : Fin 512,
    levelEleven.lookup (70656 + i.val) ≤ levelElevenRoots.lookup (70656 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_70656
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 70656 128 128
    h0 levelEleven_squares_70784
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 70656 256 128
    h1 levelEleven_squares_70912
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 70656 384 128
    h2 levelEleven_squares_71040
  exact h3

end WordCertDensity.Certificates
