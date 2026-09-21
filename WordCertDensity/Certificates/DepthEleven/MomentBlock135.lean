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
theorem levelEleven_energy_69120 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 69120 128 =
      264264540454024763079788250590828 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_69120 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69120 128 =
      2947671257010728700964817 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_69120 : ∀ i : Fin 128,
    levelEleven.lookup (69120 + i.val) ≤ levelElevenRoots.lookup (69120 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_69248 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 69248 128 =
      43873095634165955174363693977753 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_69248 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69248 128 =
      1005231506309409774821540 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_69248 : ∀ i : Fin 128,
    levelEleven.lookup (69248 + i.val) ≤ levelElevenRoots.lookup (69248 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_69376 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 69376 128 =
      65716614103833755695742905567772 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_69376 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69376 128 =
      1447787329652034775181383 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_69376 : ∀ i : Fin 128,
    levelEleven.lookup (69376 + i.val) ≤ levelElevenRoots.lookup (69376 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_69504 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 69504 128 =
      34420096467713209707126794460532 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_69504 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69504 128 =
      985449304872835734895104 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_69504 : ∀ i : Fin 128,
    levelEleven.lookup (69504 + i.val) ≤ levelElevenRoots.lookup (69504 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_135 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 69120 512 =
      408274346659737683657021644596885 := by
  have h0 := levelEleven_energy_69120
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 69120 256 =
      308137636088190718254151944568581 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 69120 128 128
      264264540454024763079788250590828 43873095634165955174363693977753 h0 levelEleven_energy_69248
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 69120 384 =
      373854250192024473949894850136353 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 69120 256 128
      308137636088190718254151944568581 65716614103833755695742905567772 h1 levelEleven_energy_69376
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 69120 512 =
      408274346659737683657021644596885 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 69120 384 128
      373854250192024473949894850136353 34420096467713209707126794460532 h2 levelEleven_energy_69504
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_135 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69120 512 =
      6386139397845008985862844 := by
  have h0 := levelEleven_fractional_69120
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69120 256 =
      3952902763320138475786357 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69120 128 128
      2947671257010728700964817 1005231506309409774821540 h0 levelEleven_fractional_69248
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69120 384 =
      5400690092972173250967740 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69120 256 128
      3952902763320138475786357 1447787329652034775181383 h1 levelEleven_fractional_69376
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69120 512 =
      6386139397845008985862844 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 69120 384 128
      5400690092972173250967740 985449304872835734895104 h2 levelEleven_fractional_69504
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_135 : ∀ i : Fin 512,
    levelEleven.lookup (69120 + i.val) ≤ levelElevenRoots.lookup (69120 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_69120
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 69120 128 128
    h0 levelEleven_squares_69248
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 69120 256 128
    h1 levelEleven_squares_69376
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 69120 384 128
    h2 levelEleven_squares_69504
  exact h3

end WordCertDensity.Certificates
