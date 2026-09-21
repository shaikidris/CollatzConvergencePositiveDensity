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
theorem levelEleven_energy_117248 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 117248 128 =
      58331735063096348971163158829413 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_117248 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117248 128 =
      1316985628372788421479009 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_117248 : ∀ i : Fin 128,
    levelEleven.lookup (117248 + i.val) ≤ levelElevenRoots.lookup (117248 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_117376 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 117376 128 =
      23104575525452107646727118293865 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_117376 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117376 128 =
      773150184037066466405337 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_117376 : ∀ i : Fin 128,
    levelEleven.lookup (117376 + i.val) ≤ levelElevenRoots.lookup (117376 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_117504 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 117504 128 =
      33720179063423983549165551850151 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_117504 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117504 128 =
      983458301167651750547191 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_117504 : ∀ i : Fin 128,
    levelEleven.lookup (117504 + i.val) ≤ levelElevenRoots.lookup (117504 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_117632 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 117632 128 =
      70011020917384290904887255602852 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_117632 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117632 128 =
      1319466859887246144309770 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_117632 : ∀ i : Fin 128,
    levelEleven.lookup (117632 + i.val) ≤ levelElevenRoots.lookup (117632 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_229 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 117248 512 =
      185167510569356731071943084576281 := by
  have h0 := levelEleven_energy_117248
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 117248 256 =
      81436310588548456617890277123278 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 117248 128 128
      58331735063096348971163158829413 23104575525452107646727118293865 h0 levelEleven_energy_117376
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 117248 384 =
      115156489651972440167055828973429 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 117248 256 128
      81436310588548456617890277123278 33720179063423983549165551850151 h1 levelEleven_energy_117504
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 117248 512 =
      185167510569356731071943084576281 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 117248 384 128
      115156489651972440167055828973429 70011020917384290904887255602852 h2 levelEleven_energy_117632
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_229 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117248 512 =
      4393060973464752782741307 := by
  have h0 := levelEleven_fractional_117248
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117248 256 =
      2090135812409854887884346 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117248 128 128
      1316985628372788421479009 773150184037066466405337 h0 levelEleven_fractional_117376
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117248 384 =
      3073594113577506638431537 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117248 256 128
      2090135812409854887884346 983458301167651750547191 h1 levelEleven_fractional_117504
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117248 512 =
      4393060973464752782741307 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 117248 384 128
      3073594113577506638431537 1319466859887246144309770 h2 levelEleven_fractional_117632
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_229 : ∀ i : Fin 512,
    levelEleven.lookup (117248 + i.val) ≤ levelElevenRoots.lookup (117248 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_117248
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 117248 128 128
    h0 levelEleven_squares_117376
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 117248 256 128
    h1 levelEleven_squares_117504
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 117248 384 128
    h2 levelEleven_squares_117632
  exact h3

end WordCertDensity.Certificates
