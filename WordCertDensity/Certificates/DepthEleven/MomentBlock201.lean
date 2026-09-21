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
theorem levelEleven_energy_102912 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 102912 128 =
      266290709113738971125489399177523 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_102912 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102912 128 =
      2933807512376035288195549 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_102912 : ∀ i : Fin 128,
    levelEleven.lookup (102912 + i.val) ≤ levelElevenRoots.lookup (102912 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_103040 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 103040 128 =
      36293944013268804833536995155434 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_103040 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103040 128 =
      977061619774505105968422 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_103040 : ∀ i : Fin 128,
    levelEleven.lookup (103040 + i.val) ≤ levelElevenRoots.lookup (103040 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_103168 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 103168 128 =
      47926506065778949524997724253815 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_103168 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103168 128 =
      1250747232123287841513422 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_103168 : ∀ i : Fin 128,
    levelEleven.lookup (103168 + i.val) ≤ levelElevenRoots.lookup (103168 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_103296 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 103296 128 =
      13951499156353886222682882885689 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_103296 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 103296 128 =
      546103420201034503399737 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_103296 : ∀ i : Fin 128,
    levelEleven.lookup (103296 + i.val) ≤ levelElevenRoots.lookup (103296 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_201 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 102912 512 =
      364462658349140611706707001472461 := by
  have h0 := levelEleven_energy_102912
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 102912 256 =
      302584653127007775959026394332957 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 102912 128 128
      266290709113738971125489399177523 36293944013268804833536995155434 h0 levelEleven_energy_103040
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 102912 384 =
      350511159192786725484024118586772 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 102912 256 128
      302584653127007775959026394332957 47926506065778949524997724253815 h1 levelEleven_energy_103168
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 102912 512 =
      364462658349140611706707001472461 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 102912 384 128
      350511159192786725484024118586772 13951499156353886222682882885689 h2 levelEleven_energy_103296
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_201 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102912 512 =
      5707719784474862739077130 := by
  have h0 := levelEleven_fractional_102912
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102912 256 =
      3910869132150540394163971 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102912 128 128
      2933807512376035288195549 977061619774505105968422 h0 levelEleven_fractional_103040
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102912 384 =
      5161616364273828235677393 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102912 256 128
      3910869132150540394163971 1250747232123287841513422 h1 levelEleven_fractional_103168
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102912 512 =
      5707719784474862739077130 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 102912 384 128
      5161616364273828235677393 546103420201034503399737 h2 levelEleven_fractional_103296
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_201 : ∀ i : Fin 512,
    levelEleven.lookup (102912 + i.val) ≤ levelElevenRoots.lookup (102912 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_102912
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 102912 128 128
    h0 levelEleven_squares_103040
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 102912 256 128
    h1 levelEleven_squares_103168
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 102912 384 128
    h2 levelEleven_squares_103296
  exact h3

end WordCertDensity.Certificates
