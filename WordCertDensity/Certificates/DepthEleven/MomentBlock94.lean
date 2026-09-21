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
theorem levelEleven_energy_48128 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 48128 128 =
      17768347000872797344565090699831 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_48128 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48128 128 =
      662376207385965207846279 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_48128 : ∀ i : Fin 128,
    levelEleven.lookup (48128 + i.val) ≤ levelElevenRoots.lookup (48128 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_48256 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 48256 128 =
      43460690685110907395894622264182 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_48256 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48256 128 =
      1197098651975060940505570 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_48256 : ∀ i : Fin 128,
    levelEleven.lookup (48256 + i.val) ≤ levelElevenRoots.lookup (48256 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_48384 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 48384 128 =
      29768111197836749287353393138669 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_48384 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48384 128 =
      840360072611402153612485 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_48384 : ∀ i : Fin 128,
    levelEleven.lookup (48384 + i.val) ≤ levelElevenRoots.lookup (48384 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_48512 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 48512 128 =
      45214927566961112886287704681044 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_48512 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48512 128 =
      1116998847639208739511665 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_48512 : ∀ i : Fin 128,
    levelEleven.lookup (48512 + i.val) ≤ levelElevenRoots.lookup (48512 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_94 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 48128 512 =
      136212076450781566914100810783726 := by
  have h0 := levelEleven_energy_48128
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 48128 256 =
      61229037685983704740459712964013 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 48128 128 128
      17768347000872797344565090699831 43460690685110907395894622264182 h0 levelEleven_energy_48256
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 48128 384 =
      90997148883820454027813106102682 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 48128 256 128
      61229037685983704740459712964013 29768111197836749287353393138669 h1 levelEleven_energy_48384
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 48128 512 =
      136212076450781566914100810783726 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 48128 384 128
      90997148883820454027813106102682 45214927566961112886287704681044 h2 levelEleven_energy_48512
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_94 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48128 512 =
      3816833779611637041475999 := by
  have h0 := levelEleven_fractional_48128
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48128 256 =
      1859474859361026148351849 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48128 128 128
      662376207385965207846279 1197098651975060940505570 h0 levelEleven_fractional_48256
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48128 384 =
      2699834931972428301964334 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48128 256 128
      1859474859361026148351849 840360072611402153612485 h1 levelEleven_fractional_48384
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48128 512 =
      3816833779611637041475999 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 48128 384 128
      2699834931972428301964334 1116998847639208739511665 h2 levelEleven_fractional_48512
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_94 : ∀ i : Fin 512,
    levelEleven.lookup (48128 + i.val) ≤ levelElevenRoots.lookup (48128 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_48128
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 48128 128 128
    h0 levelEleven_squares_48256
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 48128 256 128
    h1 levelEleven_squares_48384
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 48128 384 128
    h2 levelEleven_squares_48512
  exact h3

end WordCertDensity.Certificates
