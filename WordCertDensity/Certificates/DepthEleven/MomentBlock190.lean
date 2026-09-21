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
theorem levelEleven_energy_97280 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 97280 128 =
      31910084805471306192506936949260 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_97280 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97280 128 =
      956872482892266090585052 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_97280 : ∀ i : Fin 128,
    levelEleven.lookup (97280 + i.val) ≤ levelElevenRoots.lookup (97280 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_97408 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 97408 128 =
      19970740098628871694057857694427 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_97408 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97408 128 =
      690862948480208638394178 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_97408 : ∀ i : Fin 128,
    levelEleven.lookup (97408 + i.val) ≤ levelElevenRoots.lookup (97408 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_97536 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 97536 128 =
      91973267887013011973302338769649 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_97536 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97536 128 =
      1633485631483820811321175 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_97536 : ∀ i : Fin 128,
    levelEleven.lookup (97536 + i.val) ≤ levelElevenRoots.lookup (97536 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_97664 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 97664 128 =
      24709191293477437347723019433190 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_97664 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97664 128 =
      783439304760348639963854 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_97664 : ∀ i : Fin 128,
    levelEleven.lookup (97664 + i.val) ≤ levelElevenRoots.lookup (97664 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_190 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 97280 512 =
      168563284084590627207590152846526 := by
  have h0 := levelEleven_energy_97280
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 97280 256 =
      51880824904100177886564794643687 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 97280 128 128
      31910084805471306192506936949260 19970740098628871694057857694427 h0 levelEleven_energy_97408
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 97280 384 =
      143854092791113189859867133413336 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 97280 256 128
      51880824904100177886564794643687 91973267887013011973302338769649 h1 levelEleven_energy_97536
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 97280 512 =
      168563284084590627207590152846526 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 97280 384 128
      143854092791113189859867133413336 24709191293477437347723019433190 h2 levelEleven_energy_97664
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_190 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97280 512 =
      4064660367616644180264259 := by
  have h0 := levelEleven_fractional_97280
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97280 256 =
      1647735431372474728979230 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97280 128 128
      956872482892266090585052 690862948480208638394178 h0 levelEleven_fractional_97408
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97280 384 =
      3281221062856295540300405 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97280 256 128
      1647735431372474728979230 1633485631483820811321175 h1 levelEleven_fractional_97536
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97280 512 =
      4064660367616644180264259 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97280 384 128
      3281221062856295540300405 783439304760348639963854 h2 levelEleven_fractional_97664
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_190 : ∀ i : Fin 512,
    levelEleven.lookup (97280 + i.val) ≤ levelElevenRoots.lookup (97280 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_97280
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 97280 128 128
    h0 levelEleven_squares_97408
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 97280 256 128
    h1 levelEleven_squares_97536
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 97280 384 128
    h2 levelEleven_squares_97664
  exact h3

end WordCertDensity.Certificates
