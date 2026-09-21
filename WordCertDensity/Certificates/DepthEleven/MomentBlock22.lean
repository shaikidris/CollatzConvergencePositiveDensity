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
theorem levelEleven_energy_11264 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 11264 128 =
      88627667581096239546697784739183 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_11264 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11264 128 =
      1638660647094790679808120 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_11264 : ∀ i : Fin 128,
    levelEleven.lookup (11264 + i.val) ≤ levelElevenRoots.lookup (11264 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_11392 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 11392 128 =
      25893596208960773343994619528305 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_11392 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11392 128 =
      822350827971708028149332 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_11392 : ∀ i : Fin 128,
    levelEleven.lookup (11392 + i.val) ≤ levelElevenRoots.lookup (11392 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_11520 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 11520 128 =
      42919362101420198413318128805093 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_11520 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11520 128 =
      1023738905233624710222767 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_11520 : ∀ i : Fin 128,
    levelEleven.lookup (11520 + i.val) ≤ levelElevenRoots.lookup (11520 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_11648 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 11648 128 =
      33674452533988014636704889245726 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_11648 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11648 128 =
      902819937799723962145808 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_11648 : ∀ i : Fin 128,
    levelEleven.lookup (11648 + i.val) ≤ levelElevenRoots.lookup (11648 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_22 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 11264 512 =
      191115078425465225940715422318307 := by
  have h0 := levelEleven_energy_11264
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 11264 256 =
      114521263790057012890692404267488 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 11264 128 128
      88627667581096239546697784739183 25893596208960773343994619528305 h0 levelEleven_energy_11392
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 11264 384 =
      157440625891477211304010533072581 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 11264 256 128
      114521263790057012890692404267488 42919362101420198413318128805093 h1 levelEleven_energy_11520
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 11264 512 =
      191115078425465225940715422318307 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 11264 384 128
      157440625891477211304010533072581 33674452533988014636704889245726 h2 levelEleven_energy_11648
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_22 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11264 512 =
      4387570318099847380326027 := by
  have h0 := levelEleven_fractional_11264
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11264 256 =
      2461011475066498707957452 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11264 128 128
      1638660647094790679808120 822350827971708028149332 h0 levelEleven_fractional_11392
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11264 384 =
      3484750380300123418180219 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11264 256 128
      2461011475066498707957452 1023738905233624710222767 h1 levelEleven_fractional_11520
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11264 512 =
      4387570318099847380326027 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 11264 384 128
      3484750380300123418180219 902819937799723962145808 h2 levelEleven_fractional_11648
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_22 : ∀ i : Fin 512,
    levelEleven.lookup (11264 + i.val) ≤ levelElevenRoots.lookup (11264 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_11264
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 11264 128 128
    h0 levelEleven_squares_11392
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 11264 256 128
    h1 levelEleven_squares_11520
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 11264 384 128
    h2 levelEleven_squares_11648
  exact h3

end WordCertDensity.Certificates
