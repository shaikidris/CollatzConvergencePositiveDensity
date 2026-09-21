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
theorem levelEleven_energy_6144 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 6144 128 =
      32933547603318358952304633065834 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_6144 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6144 128 =
      936359367597842169566376 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_6144 : ∀ i : Fin 128,
    levelEleven.lookup (6144 + i.val) ≤ levelElevenRoots.lookup (6144 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_6272 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 6272 128 =
      20454149559546715414120884868154 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_6272 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6272 128 =
      727314600326396967969409 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_6272 : ∀ i : Fin 128,
    levelEleven.lookup (6272 + i.val) ≤ levelElevenRoots.lookup (6272 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_6400 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 6400 128 =
      69344392422367924533367515533265 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_6400 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6400 128 =
      1480174819108990767428581 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_6400 : ∀ i : Fin 128,
    levelEleven.lookup (6400 + i.val) ≤ levelElevenRoots.lookup (6400 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_6528 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 6528 128 =
      40650544643840135029313652026847 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_6528 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6528 128 =
      943149003527803503983100 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_6528 : ∀ i : Fin 128,
    levelEleven.lookup (6528 + i.val) ≤ levelElevenRoots.lookup (6528 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_12 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 6144 512 =
      163382634229073133929106685494100 := by
  have h0 := levelEleven_energy_6144
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 6144 256 =
      53387697162865074366425517933988 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 6144 128 128
      32933547603318358952304633065834 20454149559546715414120884868154 h0 levelEleven_energy_6272
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 6144 384 =
      122732089585232998899793033467253 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 6144 256 128
      53387697162865074366425517933988 69344392422367924533367515533265 h1 levelEleven_energy_6400
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 6144 512 =
      163382634229073133929106685494100 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 6144 384 128
      122732089585232998899793033467253 40650544643840135029313652026847 h2 levelEleven_energy_6528
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_12 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6144 512 =
      4086997790561033408947466 := by
  have h0 := levelEleven_fractional_6144
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6144 256 =
      1663673967924239137535785 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6144 128 128
      936359367597842169566376 727314600326396967969409 h0 levelEleven_fractional_6272
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6144 384 =
      3143848787033229904964366 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6144 256 128
      1663673967924239137535785 1480174819108990767428581 h1 levelEleven_fractional_6400
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6144 512 =
      4086997790561033408947466 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 6144 384 128
      3143848787033229904964366 943149003527803503983100 h2 levelEleven_fractional_6528
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_12 : ∀ i : Fin 512,
    levelEleven.lookup (6144 + i.val) ≤ levelElevenRoots.lookup (6144 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_6144
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 6144 128 128
    h0 levelEleven_squares_6272
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 6144 256 128
    h1 levelEleven_squares_6400
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 6144 384 128
    h2 levelEleven_squares_6528
  exact h3

end WordCertDensity.Certificates
