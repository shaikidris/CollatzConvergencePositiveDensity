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
theorem levelEleven_energy_92160 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 92160 128 =
      59111157393491645900284112705350 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_92160 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92160 128 =
      1402370278906886796954692 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_92160 : ∀ i : Fin 128,
    levelEleven.lookup (92160 + i.val) ≤ levelElevenRoots.lookup (92160 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_92288 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 92288 128 =
      21051495793508791261995289979111 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_92288 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92288 128 =
      744591168513661062791548 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_92288 : ∀ i : Fin 128,
    levelEleven.lookup (92288 + i.val) ≤ levelElevenRoots.lookup (92288 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_92416 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 92416 128 =
      43826126046451283449648597013869 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_92416 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92416 128 =
      1155968149823730311092122 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_92416 : ∀ i : Fin 128,
    levelEleven.lookup (92416 + i.val) ≤ levelElevenRoots.lookup (92416 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_92544 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 92544 128 =
      46167252692699011451205230197302 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_92544 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92544 128 =
      1031720963889945074725999 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_92544 : ∀ i : Fin 128,
    levelEleven.lookup (92544 + i.val) ≤ levelElevenRoots.lookup (92544 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_180 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 92160 512 =
      170156031926150732063133229895632 := by
  have h0 := levelEleven_energy_92160
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 92160 256 =
      80162653187000437162279402684461 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 92160 128 128
      59111157393491645900284112705350 21051495793508791261995289979111 h0 levelEleven_energy_92288
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 92160 384 =
      123988779233451720611927999698330 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 92160 256 128
      80162653187000437162279402684461 43826126046451283449648597013869 h1 levelEleven_energy_92416
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 92160 512 =
      170156031926150732063133229895632 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 92160 384 128
      123988779233451720611927999698330 46167252692699011451205230197302 h2 levelEleven_energy_92544
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_180 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92160 512 =
      4334650561134223245564361 := by
  have h0 := levelEleven_fractional_92160
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92160 256 =
      2146961447420547859746240 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92160 128 128
      1402370278906886796954692 744591168513661062791548 h0 levelEleven_fractional_92288
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92160 384 =
      3302929597244278170838362 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92160 256 128
      2146961447420547859746240 1155968149823730311092122 h1 levelEleven_fractional_92416
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92160 512 =
      4334650561134223245564361 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 92160 384 128
      3302929597244278170838362 1031720963889945074725999 h2 levelEleven_fractional_92544
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_180 : ∀ i : Fin 512,
    levelEleven.lookup (92160 + i.val) ≤ levelElevenRoots.lookup (92160 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_92160
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 92160 128 128
    h0 levelEleven_squares_92288
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 92160 256 128
    h1 levelEleven_squares_92416
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 92160 384 128
    h2 levelEleven_squares_92544
  exact h3

end WordCertDensity.Certificates
