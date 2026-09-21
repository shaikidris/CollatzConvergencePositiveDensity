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
theorem levelEleven_energy_51200 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 51200 128 =
      42296380943813077325913327019209 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_51200 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51200 128 =
      1051721005203432631255249 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_51200 : ∀ i : Fin 128,
    levelEleven.lookup (51200 + i.val) ≤ levelElevenRoots.lookup (51200 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_51328 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 51328 128 =
      25874544139245583438618818984113 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_51328 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51328 128 =
      852459832440099954758599 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_51328 : ∀ i : Fin 128,
    levelEleven.lookup (51328 + i.val) ≤ levelElevenRoots.lookup (51328 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_51456 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 51456 128 =
      19881820971157664353671748591730 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_51456 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51456 128 =
      690615104926072342989365 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_51456 : ∀ i : Fin 128,
    levelEleven.lookup (51456 + i.val) ≤ levelElevenRoots.lookup (51456 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_51584 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 51584 128 =
      152719428148858582462662362927461 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_51584 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51584 128 =
      2080429427940727903302264 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_51584 : ∀ i : Fin 128,
    levelEleven.lookup (51584 + i.val) ≤ levelElevenRoots.lookup (51584 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_100 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 51200 512 =
      240772174203074907580866257522513 := by
  have h0 := levelEleven_energy_51200
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 51200 256 =
      68170925083058660764532146003322 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 51200 128 128
      42296380943813077325913327019209 25874544139245583438618818984113 h0 levelEleven_energy_51328
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 51200 384 =
      88052746054216325118203894595052 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 51200 256 128
      68170925083058660764532146003322 19881820971157664353671748591730 h1 levelEleven_energy_51456
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 51200 512 =
      240772174203074907580866257522513 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 51200 384 128
      88052746054216325118203894595052 152719428148858582462662362927461 h2 levelEleven_energy_51584
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_100 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51200 512 =
      4675225370510332832305477 := by
  have h0 := levelEleven_fractional_51200
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51200 256 =
      1904180837643532586013848 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51200 128 128
      1051721005203432631255249 852459832440099954758599 h0 levelEleven_fractional_51328
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51200 384 =
      2594795942569604929003213 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51200 256 128
      1904180837643532586013848 690615104926072342989365 h1 levelEleven_fractional_51456
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51200 512 =
      4675225370510332832305477 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 51200 384 128
      2594795942569604929003213 2080429427940727903302264 h2 levelEleven_fractional_51584
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_100 : ∀ i : Fin 512,
    levelEleven.lookup (51200 + i.val) ≤ levelElevenRoots.lookup (51200 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_51200
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 51200 128 128
    h0 levelEleven_squares_51328
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 51200 256 128
    h1 levelEleven_squares_51456
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 51200 384 128
    h2 levelEleven_squares_51584
  exact h3

end WordCertDensity.Certificates
