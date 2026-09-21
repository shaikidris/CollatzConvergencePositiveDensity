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
theorem levelEleven_energy_173568 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 173568 128 =
      110166440702791035685825573778930 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_173568 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173568 128 =
      1968462590363800751878482 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_173568 : ∀ i : Fin 128,
    levelEleven.lookup (173568 + i.val) ≤ levelElevenRoots.lookup (173568 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_173696 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 173696 128 =
      33796153803524035012886652512185 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_173696 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173696 128 =
      926793369074742384339916 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_173696 : ∀ i : Fin 128,
    levelEleven.lookup (173696 + i.val) ≤ levelElevenRoots.lookup (173696 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_173824 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 173824 128 =
      206979862080960401403280358970075 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_173824 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173824 128 =
      2430616357584882109244520 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_173824 : ∀ i : Fin 128,
    levelEleven.lookup (173824 + i.val) ≤ levelElevenRoots.lookup (173824 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_173952 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 173952 128 =
      20058617061328197815038512736797 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_173952 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173952 128 =
      712087052762445011277423 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_173952 : ∀ i : Fin 128,
    levelEleven.lookup (173952 + i.val) ≤ levelElevenRoots.lookup (173952 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_339 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 173568 512 =
      371001073648603669917031097997987 := by
  have h0 := levelEleven_energy_173568
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 173568 256 =
      143962594506315070698712226291115 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 173568 128 128
      110166440702791035685825573778930 33796153803524035012886652512185 h0 levelEleven_energy_173696
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 173568 384 =
      350942456587275472101992585261190 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 173568 256 128
      143962594506315070698712226291115 206979862080960401403280358970075 h1 levelEleven_energy_173824
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 173568 512 =
      371001073648603669917031097997987 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 173568 384 128
      350942456587275472101992585261190 20058617061328197815038512736797 h2 levelEleven_energy_173952
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_339 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173568 512 =
      6037959369785870256740341 := by
  have h0 := levelEleven_fractional_173568
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173568 256 =
      2895255959438543136218398 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173568 128 128
      1968462590363800751878482 926793369074742384339916 h0 levelEleven_fractional_173696
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173568 384 =
      5325872317023425245462918 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173568 256 128
      2895255959438543136218398 2430616357584882109244520 h1 levelEleven_fractional_173824
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173568 512 =
      6037959369785870256740341 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 173568 384 128
      5325872317023425245462918 712087052762445011277423 h2 levelEleven_fractional_173952
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_339 : ∀ i : Fin 512,
    levelEleven.lookup (173568 + i.val) ≤ levelElevenRoots.lookup (173568 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_173568
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 173568 128 128
    h0 levelEleven_squares_173696
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 173568 256 128
    h1 levelEleven_squares_173824
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 173568 384 128
    h2 levelEleven_squares_173952
  exact h3

end WordCertDensity.Certificates
