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
theorem levelEleven_energy_150016 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 150016 128 =
      258524361739736819738155493480434 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_150016 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150016 128 =
      2797234751623792797014904 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_150016 : ∀ i : Fin 128,
    levelEleven.lookup (150016 + i.val) ≤ levelElevenRoots.lookup (150016 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_150144 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 150144 128 =
      22918579823735206533740831581477 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_150144 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150144 128 =
      747733348249943900189124 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_150144 : ∀ i : Fin 128,
    levelEleven.lookup (150144 + i.val) ≤ levelElevenRoots.lookup (150144 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_150272 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 150272 128 =
      67355514818044660729867133742175 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_150272 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150272 128 =
      1376539075112355687783363 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_150272 : ∀ i : Fin 128,
    levelEleven.lookup (150272 + i.val) ≤ levelElevenRoots.lookup (150272 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_150400 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 150400 128 =
      32011057341682053650078744643242 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_150400 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150400 128 =
      910970697350985172299949 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_150400 : ∀ i : Fin 128,
    levelEleven.lookup (150400 + i.val) ≤ levelElevenRoots.lookup (150400 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_293 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 150016 512 =
      380809513723198740651842203447328 := by
  have h0 := levelEleven_energy_150016
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 150016 256 =
      281442941563472026271896325061911 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 150016 128 128
      258524361739736819738155493480434 22918579823735206533740831581477 h0 levelEleven_energy_150144
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 150016 384 =
      348798456381516687001763458804086 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 150016 256 128
      281442941563472026271896325061911 67355514818044660729867133742175 h1 levelEleven_energy_150272
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 150016 512 =
      380809513723198740651842203447328 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 150016 384 128
      348798456381516687001763458804086 32011057341682053650078744643242 h2 levelEleven_energy_150400
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_293 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150016 512 =
      5832477872337077557287340 := by
  have h0 := levelEleven_fractional_150016
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150016 256 =
      3544968099873736697204028 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150016 128 128
      2797234751623792797014904 747733348249943900189124 h0 levelEleven_fractional_150144
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150016 384 =
      4921507174986092384987391 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150016 256 128
      3544968099873736697204028 1376539075112355687783363 h1 levelEleven_fractional_150272
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150016 512 =
      5832477872337077557287340 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 150016 384 128
      4921507174986092384987391 910970697350985172299949 h2 levelEleven_fractional_150400
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_293 : ∀ i : Fin 512,
    levelEleven.lookup (150016 + i.val) ≤ levelElevenRoots.lookup (150016 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_150016
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 150016 128 128
    h0 levelEleven_squares_150144
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 150016 256 128
    h1 levelEleven_squares_150272
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 150016 384 128
    h2 levelEleven_squares_150400
  exact h3

end WordCertDensity.Certificates
