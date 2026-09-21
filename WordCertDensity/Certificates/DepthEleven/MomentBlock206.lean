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
theorem levelEleven_energy_105472 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 105472 128 =
      29989532937894970435422432907411 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_105472 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105472 128 =
      850002408491528059412749 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_105472 : ∀ i : Fin 128,
    levelEleven.lookup (105472 + i.val) ≤ levelElevenRoots.lookup (105472 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_105600 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 105600 128 =
      100390892905389442865323216176173 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_105600 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105600 128 =
      1709940520881024833345736 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_105600 : ∀ i : Fin 128,
    levelEleven.lookup (105600 + i.val) ≤ levelElevenRoots.lookup (105600 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_105728 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 105728 128 =
      28929317582443095761657328447970 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_105728 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105728 128 =
      797472977185324899916540 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_105728 : ∀ i : Fin 128,
    levelEleven.lookup (105728 + i.val) ≤ levelElevenRoots.lookup (105728 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_105856 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 105856 128 =
      29779252809612859779466611087027 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_105856 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105856 128 =
      916956184846146377965198 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_105856 : ∀ i : Fin 128,
    levelEleven.lookup (105856 + i.val) ≤ levelElevenRoots.lookup (105856 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_206 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 105472 512 =
      189088996235340368841869588618581 := by
  have h0 := levelEleven_energy_105472
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 105472 256 =
      130380425843284413300745649083584 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 105472 128 128
      29989532937894970435422432907411 100390892905389442865323216176173 h0 levelEleven_energy_105600
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 105472 384 =
      159309743425727509062402977531554 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 105472 256 128
      130380425843284413300745649083584 28929317582443095761657328447970 h1 levelEleven_energy_105728
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 105472 512 =
      189088996235340368841869588618581 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 105472 384 128
      159309743425727509062402977531554 29779252809612859779466611087027 h2 levelEleven_energy_105856
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_206 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105472 512 =
      4274372091404024170640223 := by
  have h0 := levelEleven_fractional_105472
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105472 256 =
      2559942929372552892758485 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105472 128 128
      850002408491528059412749 1709940520881024833345736 h0 levelEleven_fractional_105600
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105472 384 =
      3357415906557877792675025 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105472 256 128
      2559942929372552892758485 797472977185324899916540 h1 levelEleven_fractional_105728
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105472 512 =
      4274372091404024170640223 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 105472 384 128
      3357415906557877792675025 916956184846146377965198 h2 levelEleven_fractional_105856
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_206 : ∀ i : Fin 512,
    levelEleven.lookup (105472 + i.val) ≤ levelElevenRoots.lookup (105472 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_105472
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 105472 128 128
    h0 levelEleven_squares_105600
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 105472 256 128
    h1 levelEleven_squares_105728
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 105472 384 128
    h2 levelEleven_squares_105856
  exact h3

end WordCertDensity.Certificates
