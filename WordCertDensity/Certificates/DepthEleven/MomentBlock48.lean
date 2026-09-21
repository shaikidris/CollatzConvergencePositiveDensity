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
theorem levelEleven_energy_24576 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 24576 128 =
      16599780922332520465537643533895 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_24576 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24576 128 =
      604209537103542593795644 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_24576 : ∀ i : Fin 128,
    levelEleven.lookup (24576 + i.val) ≤ levelElevenRoots.lookup (24576 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_24704 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 24704 128 =
      23974602544067900136630083372335 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_24704 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24704 128 =
      809711668548334970433266 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_24704 : ∀ i : Fin 128,
    levelEleven.lookup (24704 + i.val) ≤ levelElevenRoots.lookup (24704 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_24832 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 24832 128 =
      31056140620241704162799220525130 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_24832 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24832 128 =
      926732179726446257206401 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_24832 : ∀ i : Fin 128,
    levelEleven.lookup (24832 + i.val) ≤ levelElevenRoots.lookup (24832 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_24960 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 24960 128 =
      33833429420306874307347476156677 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_24960 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24960 128 =
      986517539940761179403202 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_24960 : ∀ i : Fin 128,
    levelEleven.lookup (24960 + i.val) ≤ levelElevenRoots.lookup (24960 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_48 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 24576 512 =
      105463953506948999072314423588037 := by
  have h0 := levelEleven_energy_24576
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 24576 256 =
      40574383466400420602167726906230 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 24576 128 128
      16599780922332520465537643533895 23974602544067900136630083372335 h0 levelEleven_energy_24704
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 24576 384 =
      71630524086642124764966947431360 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 24576 256 128
      40574383466400420602167726906230 31056140620241704162799220525130 h1 levelEleven_energy_24832
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 24576 512 =
      105463953506948999072314423588037 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 24576 384 128
      71630524086642124764966947431360 33833429420306874307347476156677 h2 levelEleven_energy_24960
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_48 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24576 512 =
      3327170925319085000838513 := by
  have h0 := levelEleven_fractional_24576
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24576 256 =
      1413921205651877564228910 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24576 128 128
      604209537103542593795644 809711668548334970433266 h0 levelEleven_fractional_24704
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24576 384 =
      2340653385378323821435311 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24576 256 128
      1413921205651877564228910 926732179726446257206401 h1 levelEleven_fractional_24832
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24576 512 =
      3327170925319085000838513 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 24576 384 128
      2340653385378323821435311 986517539940761179403202 h2 levelEleven_fractional_24960
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_48 : ∀ i : Fin 512,
    levelEleven.lookup (24576 + i.val) ≤ levelElevenRoots.lookup (24576 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_24576
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 24576 128 128
    h0 levelEleven_squares_24704
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 24576 256 128
    h1 levelEleven_squares_24832
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 24576 384 128
    h2 levelEleven_squares_24960
  exact h3

end WordCertDensity.Certificates
