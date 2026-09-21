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
theorem levelEleven_energy_101376 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 101376 128 =
      157717651695416375745638374922936 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_101376 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101376 128 =
      2059969740433461316576651 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_101376 : ∀ i : Fin 128,
    levelEleven.lookup (101376 + i.val) ≤ levelElevenRoots.lookup (101376 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_101504 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 101504 128 =
      71056733458142570636734234762885 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_101504 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101504 128 =
      1404225671244064746459133 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_101504 : ∀ i : Fin 128,
    levelEleven.lookup (101504 + i.val) ≤ levelElevenRoots.lookup (101504 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_101632 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 101632 128 =
      30068384698897671224257881007558 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_101632 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101632 128 =
      909485041910541596984680 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_101632 : ∀ i : Fin 128,
    levelEleven.lookup (101632 + i.val) ≤ levelElevenRoots.lookup (101632 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_101760 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 101760 128 =
      21740154771810848652915935850996 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_101760 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101760 128 =
      753285635679754076413680 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_101760 : ∀ i : Fin 128,
    levelEleven.lookup (101760 + i.val) ≤ levelElevenRoots.lookup (101760 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_198 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 101376 512 =
      280582924624267466259546426544375 := by
  have h0 := levelEleven_energy_101376
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 101376 256 =
      228774385153558946382372609685821 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 101376 128 128
      157717651695416375745638374922936 71056733458142570636734234762885 h0 levelEleven_energy_101504
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 101376 384 =
      258842769852456617606630490693379 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 101376 256 128
      228774385153558946382372609685821 30068384698897671224257881007558 h1 levelEleven_energy_101632
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 101376 512 =
      280582924624267466259546426544375 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 101376 384 128
      258842769852456617606630490693379 21740154771810848652915935850996 h2 levelEleven_energy_101760
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_198 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101376 512 =
      5126966089267821736434144 := by
  have h0 := levelEleven_fractional_101376
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101376 256 =
      3464195411677526063035784 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101376 128 128
      2059969740433461316576651 1404225671244064746459133 h0 levelEleven_fractional_101504
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101376 384 =
      4373680453588067660020464 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101376 256 128
      3464195411677526063035784 909485041910541596984680 h1 levelEleven_fractional_101632
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101376 512 =
      5126966089267821736434144 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 101376 384 128
      4373680453588067660020464 753285635679754076413680 h2 levelEleven_fractional_101760
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_198 : ∀ i : Fin 512,
    levelEleven.lookup (101376 + i.val) ≤ levelElevenRoots.lookup (101376 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_101376
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 101376 128 128
    h0 levelEleven_squares_101504
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 101376 256 128
    h1 levelEleven_squares_101632
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 101376 384 128
    h2 levelEleven_squares_101760
  exact h3

end WordCertDensity.Certificates
