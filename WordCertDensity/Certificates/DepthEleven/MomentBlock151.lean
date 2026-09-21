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
theorem levelEleven_energy_77312 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 77312 128 =
      32866282102459833187118909902050 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_77312 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77312 128 =
      927121962301802977138255 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_77312 : ∀ i : Fin 128,
    levelEleven.lookup (77312 + i.val) ≤ levelElevenRoots.lookup (77312 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_77440 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 77440 128 =
      33536450301166007208734344451229 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_77440 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77440 128 =
      990403842475154788897695 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_77440 : ∀ i : Fin 128,
    levelEleven.lookup (77440 + i.val) ≤ levelElevenRoots.lookup (77440 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_77568 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 77568 128 =
      40520145423256121898938193445564 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_77568 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77568 128 =
      1045582075073978052245956 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_77568 : ∀ i : Fin 128,
    levelEleven.lookup (77568 + i.val) ≤ levelElevenRoots.lookup (77568 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_77696 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 77696 128 =
      29423873614018601779515218644534 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_77696 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77696 128 =
      878073531286233160563825 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_77696 : ∀ i : Fin 128,
    levelEleven.lookup (77696 + i.val) ≤ levelElevenRoots.lookup (77696 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_151 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 77312 512 =
      136346751440900564074306666443377 := by
  have h0 := levelEleven_energy_77312
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 77312 256 =
      66402732403625840395853254353279 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 77312 128 128
      32866282102459833187118909902050 33536450301166007208734344451229 h0 levelEleven_energy_77440
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 77312 384 =
      106922877826881962294791447798843 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 77312 256 128
      66402732403625840395853254353279 40520145423256121898938193445564 h1 levelEleven_energy_77568
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 77312 512 =
      136346751440900564074306666443377 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 77312 384 128
      106922877826881962294791447798843 29423873614018601779515218644534 h2 levelEleven_energy_77696
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_151 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77312 512 =
      3841181411137168978845731 := by
  have h0 := levelEleven_fractional_77312
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77312 256 =
      1917525804776957766035950 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77312 128 128
      927121962301802977138255 990403842475154788897695 h0 levelEleven_fractional_77440
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77312 384 =
      2963107879850935818281906 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77312 256 128
      1917525804776957766035950 1045582075073978052245956 h1 levelEleven_fractional_77568
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77312 512 =
      3841181411137168978845731 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 77312 384 128
      2963107879850935818281906 878073531286233160563825 h2 levelEleven_fractional_77696
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_151 : ∀ i : Fin 512,
    levelEleven.lookup (77312 + i.val) ≤ levelElevenRoots.lookup (77312 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_77312
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 77312 128 128
    h0 levelEleven_squares_77440
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 77312 256 128
    h1 levelEleven_squares_77568
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 77312 384 128
    h2 levelEleven_squares_77696
  exact h3

end WordCertDensity.Certificates
