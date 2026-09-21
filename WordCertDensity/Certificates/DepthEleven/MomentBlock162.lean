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
theorem levelEleven_energy_82944 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 82944 128 =
      252349266420074434328089396940930 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_82944 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82944 128 =
      3114842234450187532065474 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_82944 : ∀ i : Fin 128,
    levelEleven.lookup (82944 + i.val) ≤ levelElevenRoots.lookup (82944 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_83072 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 83072 128 =
      37904912200782430585608886413588 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_83072 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83072 128 =
      931541468981230623777380 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_83072 : ∀ i : Fin 128,
    levelEleven.lookup (83072 + i.val) ≤ levelElevenRoots.lookup (83072 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_83200 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 83200 128 =
      60162602273297879199972729547773 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_83200 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83200 128 =
      1360484229483365640567750 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_83200 : ∀ i : Fin 128,
    levelEleven.lookup (83200 + i.val) ≤ levelElevenRoots.lookup (83200 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_83328 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 83328 128 =
      100765847184854669374803694862358 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_83328 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 83328 128 =
      1612692730557992435812005 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_83328 : ∀ i : Fin 128,
    levelEleven.lookup (83328 + i.val) ≤ levelElevenRoots.lookup (83328 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_162 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 82944 512 =
      451182628079009413488474707764649 := by
  have h0 := levelEleven_energy_82944
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 82944 256 =
      290254178620856864913698283354518 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 82944 128 128
      252349266420074434328089396940930 37904912200782430585608886413588 h0 levelEleven_energy_83072
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 82944 384 =
      350416780894154744113671012902291 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 82944 256 128
      290254178620856864913698283354518 60162602273297879199972729547773 h1 levelEleven_energy_83200
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 82944 512 =
      451182628079009413488474707764649 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 82944 384 128
      350416780894154744113671012902291 100765847184854669374803694862358 h2 levelEleven_energy_83328
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_162 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82944 512 =
      7019560663472776232222609 := by
  have h0 := levelEleven_fractional_82944
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82944 256 =
      4046383703431418155842854 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82944 128 128
      3114842234450187532065474 931541468981230623777380 h0 levelEleven_fractional_83072
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82944 384 =
      5406867932914783796410604 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82944 256 128
      4046383703431418155842854 1360484229483365640567750 h1 levelEleven_fractional_83200
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82944 512 =
      7019560663472776232222609 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 82944 384 128
      5406867932914783796410604 1612692730557992435812005 h2 levelEleven_fractional_83328
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_162 : ∀ i : Fin 512,
    levelEleven.lookup (82944 + i.val) ≤ levelElevenRoots.lookup (82944 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_82944
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 82944 128 128
    h0 levelEleven_squares_83072
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 82944 256 128
    h1 levelEleven_squares_83200
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 82944 384 128
    h2 levelEleven_squares_83328
  exact h3

end WordCertDensity.Certificates
