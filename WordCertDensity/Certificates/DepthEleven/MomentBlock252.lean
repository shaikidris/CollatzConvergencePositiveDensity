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
theorem levelEleven_energy_129024 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 129024 128 =
      22308812297512056062106841476687 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_129024 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129024 128 =
      745433558457255778866285 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_129024 : ∀ i : Fin 128,
    levelEleven.lookup (129024 + i.val) ≤ levelElevenRoots.lookup (129024 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_129152 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 129152 128 =
      106256788718405384537739354655950 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_129152 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129152 128 =
      1830072601440890030268400 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_129152 : ∀ i : Fin 128,
    levelEleven.lookup (129152 + i.val) ≤ levelElevenRoots.lookup (129152 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_129280 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 129280 128 =
      29669599926596717188173713250675 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_129280 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129280 128 =
      927683729458397016763593 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_129280 : ∀ i : Fin 128,
    levelEleven.lookup (129280 + i.val) ≤ levelElevenRoots.lookup (129280 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_129408 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 129408 128 =
      40836895648147183350427033349444 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_129408 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129408 128 =
      1092365439107705058358625 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_129408 : ∀ i : Fin 128,
    levelEleven.lookup (129408 + i.val) ≤ levelElevenRoots.lookup (129408 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_252 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 129024 512 =
      199072096590661341138446942732756 := by
  have h0 := levelEleven_energy_129024
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 129024 256 =
      128565601015917440599846196132637 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 129024 128 128
      22308812297512056062106841476687 106256788718405384537739354655950 h0 levelEleven_energy_129152
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 129024 384 =
      158235200942514157788019909383312 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 129024 256 128
      128565601015917440599846196132637 29669599926596717188173713250675 h1 levelEleven_energy_129280
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 129024 512 =
      199072096590661341138446942732756 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 129024 384 128
      158235200942514157788019909383312 40836895648147183350427033349444 h2 levelEleven_energy_129408
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_252 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129024 512 =
      4595555328464247884256903 := by
  have h0 := levelEleven_fractional_129024
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129024 256 =
      2575506159898145809134685 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129024 128 128
      745433558457255778866285 1830072601440890030268400 h0 levelEleven_fractional_129152
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129024 384 =
      3503189889356542825898278 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129024 256 128
      2575506159898145809134685 927683729458397016763593 h1 levelEleven_fractional_129280
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129024 512 =
      4595555328464247884256903 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 129024 384 128
      3503189889356542825898278 1092365439107705058358625 h2 levelEleven_fractional_129408
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_252 : ∀ i : Fin 512,
    levelEleven.lookup (129024 + i.val) ≤ levelElevenRoots.lookup (129024 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_129024
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 129024 128 128
    h0 levelEleven_squares_129152
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 129024 256 128
    h1 levelEleven_squares_129280
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 129024 384 128
    h2 levelEleven_squares_129408
  exact h3

end WordCertDensity.Certificates
