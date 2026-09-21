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
theorem levelEleven_energy_4608 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 4608 128 =
      141650246791579526309541293963920 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_4608 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4608 128 =
      1836081298703338873698843 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_4608 : ∀ i : Fin 128,
    levelEleven.lookup (4608 + i.val) ≤ levelElevenRoots.lookup (4608 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_4736 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 4736 128 =
      59867816927964597167604030540459 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_4736 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4736 128 =
      1365014154795477904770025 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_4736 : ∀ i : Fin 128,
    levelEleven.lookup (4736 + i.val) ≤ levelElevenRoots.lookup (4736 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_4864 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 4864 128 =
      14137791747464145280047649164909 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_4864 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4864 128 =
      570790922880774410791627 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_4864 : ∀ i : Fin 128,
    levelEleven.lookup (4864 + i.val) ≤ levelElevenRoots.lookup (4864 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_4992 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 4992 128 =
      50755125498331762968946986518634 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_4992 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4992 128 =
      1249689909047846168305016 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_4992 : ∀ i : Fin 128,
    levelEleven.lookup (4992 + i.val) ≤ levelElevenRoots.lookup (4992 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_9 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 4608 512 =
      266410980965340031726139960187922 := by
  have h0 := levelEleven_energy_4608
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 4608 256 =
      201518063719544123477145324504379 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 4608 128 128
      141650246791579526309541293963920 59867816927964597167604030540459 h0 levelEleven_energy_4736
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 4608 384 =
      215655855467008268757192973669288 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 4608 256 128
      201518063719544123477145324504379 14137791747464145280047649164909 h1 levelEleven_energy_4864
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 4608 512 =
      266410980965340031726139960187922 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 4608 384 128
      215655855467008268757192973669288 50755125498331762968946986518634 h2 levelEleven_energy_4992
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_9 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4608 512 =
      5021576285427437357565511 := by
  have h0 := levelEleven_fractional_4608
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4608 256 =
      3201095453498816778468868 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4608 128 128
      1836081298703338873698843 1365014154795477904770025 h0 levelEleven_fractional_4736
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4608 384 =
      3771886376379591189260495 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4608 256 128
      3201095453498816778468868 570790922880774410791627 h1 levelEleven_fractional_4864
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4608 512 =
      5021576285427437357565511 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 4608 384 128
      3771886376379591189260495 1249689909047846168305016 h2 levelEleven_fractional_4992
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_9 : ∀ i : Fin 512,
    levelEleven.lookup (4608 + i.val) ≤ levelElevenRoots.lookup (4608 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_4608
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 4608 128 128
    h0 levelEleven_squares_4736
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 4608 256 128
    h1 levelEleven_squares_4864
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 4608 384 128
    h2 levelEleven_squares_4992
  exact h3

end WordCertDensity.Certificates
