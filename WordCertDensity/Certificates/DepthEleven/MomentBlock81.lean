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
theorem levelEleven_energy_41472 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 41472 128 =
      119622960932262853191748172336584 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_41472 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41472 128 =
      1999083695188853598890584 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_41472 : ∀ i : Fin 128,
    levelEleven.lookup (41472 + i.val) ≤ levelElevenRoots.lookup (41472 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_41600 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 41600 128 =
      42670070883170557086535969283560 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_41600 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41600 128 =
      1049071840952032858251175 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_41600 : ∀ i : Fin 128,
    levelEleven.lookup (41600 + i.val) ≤ levelElevenRoots.lookup (41600 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_41728 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 41728 128 =
      50768148574772645070377530072095 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_41728 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41728 128 =
      1195481044404646900481901 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_41728 : ∀ i : Fin 128,
    levelEleven.lookup (41728 + i.val) ≤ levelElevenRoots.lookup (41728 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_41856 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 41856 128 =
      28040870391507260224185110842109 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_41856 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41856 128 =
      902571754936763855778897 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_41856 : ∀ i : Fin 128,
    levelEleven.lookup (41856 + i.val) ≤ levelElevenRoots.lookup (41856 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_81 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 41472 512 =
      241102050781713315572846782534348 := by
  have h0 := levelEleven_energy_41472
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 41472 256 =
      162293031815433410278284141620144 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 41472 128 128
      119622960932262853191748172336584 42670070883170557086535969283560 h0 levelEleven_energy_41600
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 41472 384 =
      213061180390206055348661671692239 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 41472 256 128
      162293031815433410278284141620144 50768148574772645070377530072095 h1 levelEleven_energy_41728
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 41472 512 =
      241102050781713315572846782534348 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 41472 384 128
      213061180390206055348661671692239 28040870391507260224185110842109 h2 levelEleven_energy_41856
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_81 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41472 512 =
      5146208335482297213402557 := by
  have h0 := levelEleven_fractional_41472
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41472 256 =
      3048155536140886457141759 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41472 128 128
      1999083695188853598890584 1049071840952032858251175 h0 levelEleven_fractional_41600
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41472 384 =
      4243636580545533357623660 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41472 256 128
      3048155536140886457141759 1195481044404646900481901 h1 levelEleven_fractional_41728
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41472 512 =
      5146208335482297213402557 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 41472 384 128
      4243636580545533357623660 902571754936763855778897 h2 levelEleven_fractional_41856
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_81 : ∀ i : Fin 512,
    levelEleven.lookup (41472 + i.val) ≤ levelElevenRoots.lookup (41472 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_41472
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 41472 128 128
    h0 levelEleven_squares_41600
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 41472 256 128
    h1 levelEleven_squares_41728
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 41472 384 128
    h2 levelEleven_squares_41856
  exact h3

end WordCertDensity.Certificates
