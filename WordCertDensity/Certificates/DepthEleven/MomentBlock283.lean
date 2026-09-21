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
theorem levelEleven_energy_144896 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 144896 128 =
      102148297128698509579897428530743 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_144896 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144896 128 =
      1706785526086220187545430 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_144896 : ∀ i : Fin 128,
    levelEleven.lookup (144896 + i.val) ≤ levelElevenRoots.lookup (144896 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_145024 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 145024 128 =
      69517301482886784341505073328721 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_145024 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145024 128 =
      1211290066269611315446606 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_145024 : ∀ i : Fin 128,
    levelEleven.lookup (145024 + i.val) ≤ levelElevenRoots.lookup (145024 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_145152 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 145152 128 =
      52213201841997190260729279059607 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_145152 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145152 128 =
      1193037145543067765475070 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_145152 : ∀ i : Fin 128,
    levelEleven.lookup (145152 + i.val) ≤ levelElevenRoots.lookup (145152 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_145280 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 145280 128 =
      28373667240463752434611161535650 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_145280 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 145280 128 =
      869243663702421073345037 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_145280 : ∀ i : Fin 128,
    levelEleven.lookup (145280 + i.val) ≤ levelElevenRoots.lookup (145280 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_283 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 144896 512 =
      252252467694046236616742942454721 := by
  have h0 := levelEleven_energy_144896
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 144896 256 =
      171665598611585293921402501859464 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 144896 128 128
      102148297128698509579897428530743 69517301482886784341505073328721 h0 levelEleven_energy_145024
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 144896 384 =
      223878800453582484182131780919071 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 144896 256 128
      171665598611585293921402501859464 52213201841997190260729279059607 h1 levelEleven_energy_145152
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 144896 512 =
      252252467694046236616742942454721 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 144896 384 128
      223878800453582484182131780919071 28373667240463752434611161535650 h2 levelEleven_energy_145280
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_283 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144896 512 =
      4980356401601320341812143 := by
  have h0 := levelEleven_fractional_144896
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144896 256 =
      2918075592355831502992036 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144896 128 128
      1706785526086220187545430 1211290066269611315446606 h0 levelEleven_fractional_145024
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144896 384 =
      4111112737898899268467106 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144896 256 128
      2918075592355831502992036 1193037145543067765475070 h1 levelEleven_fractional_145152
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144896 512 =
      4980356401601320341812143 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 144896 384 128
      4111112737898899268467106 869243663702421073345037 h2 levelEleven_fractional_145280
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_283 : ∀ i : Fin 512,
    levelEleven.lookup (144896 + i.val) ≤ levelElevenRoots.lookup (144896 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_144896
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 144896 128 128
    h0 levelEleven_squares_145024
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 144896 256 128
    h1 levelEleven_squares_145152
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 144896 384 128
    h2 levelEleven_squares_145280
  exact h3

end WordCertDensity.Certificates
