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
theorem levelEleven_energy_14848 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 14848 128 =
      39965850545066590894633750027515 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_14848 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14848 128 =
      1071565421454923496114468 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_14848 : ∀ i : Fin 128,
    levelEleven.lookup (14848 + i.val) ≤ levelElevenRoots.lookup (14848 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_14976 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 14976 128 =
      25108430015516533330834513206232 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_14976 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14976 128 =
      828258560553052400078633 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_14976 : ∀ i : Fin 128,
    levelEleven.lookup (14976 + i.val) ≤ levelElevenRoots.lookup (14976 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_15104 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 15104 128 =
      287704049010699980122425952551899 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_15104 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15104 128 =
      3261694977309887733089205 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_15104 : ∀ i : Fin 128,
    levelEleven.lookup (15104 + i.val) ≤ levelElevenRoots.lookup (15104 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_15232 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 15232 128 =
      66230838739605370529537623175892 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_15232 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 15232 128 =
      1295579345298599060989948 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_15232 : ∀ i : Fin 128,
    levelEleven.lookup (15232 + i.val) ≤ levelElevenRoots.lookup (15232 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_29 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 14848 512 =
      419009168310888474877431838961538 := by
  have h0 := levelEleven_energy_14848
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 14848 256 =
      65074280560583124225468263233747 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 14848 128 128
      39965850545066590894633750027515 25108430015516533330834513206232 h0 levelEleven_energy_14976
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 14848 384 =
      352778329571283104347894215785646 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 14848 256 128
      65074280560583124225468263233747 287704049010699980122425952551899 h1 levelEleven_energy_15104
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 14848 512 =
      419009168310888474877431838961538 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 14848 384 128
      352778329571283104347894215785646 66230838739605370529537623175892 h2 levelEleven_energy_15232
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_29 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14848 512 =
      6457098304616462690272254 := by
  have h0 := levelEleven_fractional_14848
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14848 256 =
      1899823982007975896193101 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14848 128 128
      1071565421454923496114468 828258560553052400078633 h0 levelEleven_fractional_14976
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14848 384 =
      5161518959317863629282306 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14848 256 128
      1899823982007975896193101 3261694977309887733089205 h1 levelEleven_fractional_15104
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14848 512 =
      6457098304616462690272254 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 14848 384 128
      5161518959317863629282306 1295579345298599060989948 h2 levelEleven_fractional_15232
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_29 : ∀ i : Fin 512,
    levelEleven.lookup (14848 + i.val) ≤ levelElevenRoots.lookup (14848 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_14848
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 14848 128 128
    h0 levelEleven_squares_14976
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 14848 256 128
    h1 levelEleven_squares_15104
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 14848 384 128
    h2 levelEleven_squares_15232
  exact h3

end WordCertDensity.Certificates
