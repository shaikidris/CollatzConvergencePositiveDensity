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
theorem levelEleven_energy_87040 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 87040 128 =
      34450105446826792406367224024119 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_87040 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87040 128 =
      962220124785679378613030 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_87040 : ∀ i : Fin 128,
    levelEleven.lookup (87040 + i.val) ≤ levelElevenRoots.lookup (87040 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_87168 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 87168 128 =
      26826621061029498540731653714488 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_87168 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87168 128 =
      878315560517103567072883 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_87168 : ∀ i : Fin 128,
    levelEleven.lookup (87168 + i.val) ≤ levelElevenRoots.lookup (87168 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_87296 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 87296 128 =
      82545270275464295504548815821321 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_87296 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87296 128 =
      1609869437225162983358222 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_87296 : ∀ i : Fin 128,
    levelEleven.lookup (87296 + i.val) ≤ levelElevenRoots.lookup (87296 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_87424 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 87424 128 =
      29705252893746145025296323201420 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_87424 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87424 128 =
      852426924126388290941719 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_87424 : ∀ i : Fin 128,
    levelEleven.lookup (87424 + i.val) ≤ levelElevenRoots.lookup (87424 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_170 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 87040 512 =
      173527249677066731476944016761348 := by
  have h0 := levelEleven_energy_87040
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 87040 256 =
      61276726507856290947098877738607 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 87040 128 128
      34450105446826792406367224024119 26826621061029498540731653714488 h0 levelEleven_energy_87168
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 87040 384 =
      143821996783320586451647693559928 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 87040 256 128
      61276726507856290947098877738607 82545270275464295504548815821321 h1 levelEleven_energy_87296
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 87040 512 =
      173527249677066731476944016761348 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 87040 384 128
      143821996783320586451647693559928 29705252893746145025296323201420 h2 levelEleven_energy_87424
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_170 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87040 512 =
      4302832046654334219985854 := by
  have h0 := levelEleven_fractional_87040
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87040 256 =
      1840535685302782945685913 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87040 128 128
      962220124785679378613030 878315560517103567072883 h0 levelEleven_fractional_87168
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87040 384 =
      3450405122527945929044135 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87040 256 128
      1840535685302782945685913 1609869437225162983358222 h1 levelEleven_fractional_87296
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87040 512 =
      4302832046654334219985854 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 87040 384 128
      3450405122527945929044135 852426924126388290941719 h2 levelEleven_fractional_87424
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_170 : ∀ i : Fin 512,
    levelEleven.lookup (87040 + i.val) ≤ levelElevenRoots.lookup (87040 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_87040
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 87040 128 128
    h0 levelEleven_squares_87168
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 87040 256 128
    h1 levelEleven_squares_87296
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 87040 384 128
    h2 levelEleven_squares_87424
  exact h3

end WordCertDensity.Certificates
