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
theorem levelEleven_energy_9728 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 9728 128 =
      57460651268081608980743595073849 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_9728 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9728 128 =
      1273341470145104963361078 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_9728 : ∀ i : Fin 128,
    levelEleven.lookup (9728 + i.val) ≤ levelElevenRoots.lookup (9728 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_9856 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 9856 128 =
      21156080873560645136926002239940 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_9856 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9856 128 =
      771765815543425680842460 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_9856 : ∀ i : Fin 128,
    levelEleven.lookup (9856 + i.val) ≤ levelElevenRoots.lookup (9856 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_9984 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 9984 128 =
      23875014418471085676916912590671 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_9984 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9984 128 =
      773053940318712710838955 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_9984 : ∀ i : Fin 128,
    levelEleven.lookup (9984 + i.val) ≤ levelElevenRoots.lookup (9984 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_10112 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 10112 128 =
      120643277998592913111031081237159 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_10112 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 10112 128 =
      2015034180395980044781358 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_10112 : ∀ i : Fin 128,
    levelEleven.lookup (10112 + i.val) ≤ levelElevenRoots.lookup (10112 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_19 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 9728 512 =
      223135024558706252905617591141619 := by
  have h0 := levelEleven_energy_9728
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 9728 256 =
      78616732141642254117669597313789 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 9728 128 128
      57460651268081608980743595073849 21156080873560645136926002239940 h0 levelEleven_energy_9856
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 9728 384 =
      102491746560113339794586509904460 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 9728 256 128
      78616732141642254117669597313789 23875014418471085676916912590671 h1 levelEleven_energy_9984
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 9728 512 =
      223135024558706252905617591141619 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 9728 384 128
      102491746560113339794586509904460 120643277998592913111031081237159 h2 levelEleven_energy_10112
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_19 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9728 512 =
      4833195406403223399823851 := by
  have h0 := levelEleven_fractional_9728
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9728 256 =
      2045107285688530644203538 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9728 128 128
      1273341470145104963361078 771765815543425680842460 h0 levelEleven_fractional_9856
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9728 384 =
      2818161226007243355042493 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9728 256 128
      2045107285688530644203538 773053940318712710838955 h1 levelEleven_fractional_9984
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9728 512 =
      4833195406403223399823851 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 9728 384 128
      2818161226007243355042493 2015034180395980044781358 h2 levelEleven_fractional_10112
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_19 : ∀ i : Fin 512,
    levelEleven.lookup (9728 + i.val) ≤ levelElevenRoots.lookup (9728 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_9728
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 9728 128 128
    h0 levelEleven_squares_9856
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 9728 256 128
    h1 levelEleven_squares_9984
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 9728 384 128
    h2 levelEleven_squares_10112
  exact h3

end WordCertDensity.Certificates
