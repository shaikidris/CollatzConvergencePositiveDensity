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
theorem levelEleven_energy_123904 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 123904 128 =
      41807188253752198121588818307843 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_123904 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123904 128 =
      1001052988170716688290814 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_123904 : ∀ i : Fin 128,
    levelEleven.lookup (123904 + i.val) ≤ levelElevenRoots.lookup (123904 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_124032 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 124032 128 =
      56428228207154315837731371573642 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_124032 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124032 128 =
      1270380435273206993018798 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_124032 : ∀ i : Fin 128,
    levelEleven.lookup (124032 + i.val) ≤ levelElevenRoots.lookup (124032 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_124160 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 124160 128 =
      56760377720918474447700168629534 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_124160 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124160 128 =
      1308960976119094774834322 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_124160 : ∀ i : Fin 128,
    levelEleven.lookup (124160 + i.val) ≤ levelElevenRoots.lookup (124160 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_124288 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 124288 128 =
      31240918641774365080229174973478 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_124288 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 124288 128 =
      972867777400586431817430 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_124288 : ∀ i : Fin 128,
    levelEleven.lookup (124288 + i.val) ≤ levelElevenRoots.lookup (124288 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_242 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 123904 512 =
      186236712823599353487249533484497 := by
  have h0 := levelEleven_energy_123904
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 123904 256 =
      98235416460906513959320189881485 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 123904 128 128
      41807188253752198121588818307843 56428228207154315837731371573642 h0 levelEleven_energy_124032
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 123904 384 =
      154995794181824988407020358511019 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 123904 256 128
      98235416460906513959320189881485 56760377720918474447700168629534 h1 levelEleven_energy_124160
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 123904 512 =
      186236712823599353487249533484497 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 123904 384 128
      154995794181824988407020358511019 31240918641774365080229174973478 h2 levelEleven_energy_124288
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_242 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123904 512 =
      4553262176963604887961364 := by
  have h0 := levelEleven_fractional_123904
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123904 256 =
      2271433423443923681309612 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123904 128 128
      1001052988170716688290814 1270380435273206993018798 h0 levelEleven_fractional_124032
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123904 384 =
      3580394399563018456143934 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123904 256 128
      2271433423443923681309612 1308960976119094774834322 h1 levelEleven_fractional_124160
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123904 512 =
      4553262176963604887961364 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 123904 384 128
      3580394399563018456143934 972867777400586431817430 h2 levelEleven_fractional_124288
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_242 : ∀ i : Fin 512,
    levelEleven.lookup (123904 + i.val) ≤ levelElevenRoots.lookup (123904 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_123904
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 123904 128 128
    h0 levelEleven_squares_124032
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 123904 256 128
    h1 levelEleven_squares_124160
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 123904 384 128
    h2 levelEleven_squares_124288
  exact h3

end WordCertDensity.Certificates
