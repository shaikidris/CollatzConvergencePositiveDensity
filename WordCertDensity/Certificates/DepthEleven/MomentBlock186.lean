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
theorem levelEleven_energy_95232 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 95232 128 =
      16974572159131093692006339699470 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_95232 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95232 128 =
      661695756735249228571470 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_95232 : ∀ i : Fin 128,
    levelEleven.lookup (95232 + i.val) ≤ levelElevenRoots.lookup (95232 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_95360 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 95360 128 =
      45468192881745693578848476793894 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_95360 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95360 128 =
      1176778811606903441625521 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_95360 : ∀ i : Fin 128,
    levelEleven.lookup (95360 + i.val) ≤ levelElevenRoots.lookup (95360 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_95488 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 95488 128 =
      775944158144782630222227689683602 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_95488 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95488 128 =
      5580787718008153499152910 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_95488 : ∀ i : Fin 128,
    levelEleven.lookup (95488 + i.val) ≤ levelElevenRoots.lookup (95488 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_95616 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 95616 128 =
      34169776289896465450469375179598 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_95616 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95616 128 =
      975547273189760736588377 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_95616 : ∀ i : Fin 128,
    levelEleven.lookup (95616 + i.val) ≤ levelElevenRoots.lookup (95616 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_186 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 95232 512 =
      872556699475555882943551881356564 := by
  have h0 := levelEleven_energy_95232
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 95232 256 =
      62442765040876787270854816493364 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 95232 128 128
      16974572159131093692006339699470 45468192881745693578848476793894 h0 levelEleven_energy_95360
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 95232 384 =
      838386923185659417493082506176966 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 95232 256 128
      62442765040876787270854816493364 775944158144782630222227689683602 h1 levelEleven_energy_95488
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 95232 512 =
      872556699475555882943551881356564 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 95232 384 128
      838386923185659417493082506176966 34169776289896465450469375179598 h2 levelEleven_energy_95616
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_186 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95232 512 =
      8394809559540066905938278 := by
  have h0 := levelEleven_fractional_95232
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95232 256 =
      1838474568342152670196991 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95232 128 128
      661695756735249228571470 1176778811606903441625521 h0 levelEleven_fractional_95360
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95232 384 =
      7419262286350306169349901 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95232 256 128
      1838474568342152670196991 5580787718008153499152910 h1 levelEleven_fractional_95488
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95232 512 =
      8394809559540066905938278 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 95232 384 128
      7419262286350306169349901 975547273189760736588377 h2 levelEleven_fractional_95616
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_186 : ∀ i : Fin 512,
    levelEleven.lookup (95232 + i.val) ≤ levelElevenRoots.lookup (95232 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_95232
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 95232 128 128
    h0 levelEleven_squares_95360
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 95232 256 128
    h1 levelEleven_squares_95488
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 95232 384 128
    h2 levelEleven_squares_95616
  exact h3

end WordCertDensity.Certificates
