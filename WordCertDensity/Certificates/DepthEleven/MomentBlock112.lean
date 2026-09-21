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
theorem levelEleven_energy_57344 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 57344 128 =
      25329862015812097956545719805655 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_57344 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57344 128 =
      777766836365871441524036 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_57344 : ∀ i : Fin 128,
    levelEleven.lookup (57344 + i.val) ≤ levelElevenRoots.lookup (57344 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_57472 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 57472 128 =
      33997690582526240806629789964411 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_57472 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57472 128 =
      996644115182934146521751 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_57472 : ∀ i : Fin 128,
    levelEleven.lookup (57472 + i.val) ≤ levelElevenRoots.lookup (57472 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_57600 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 57600 128 =
      14615534979707641489710982135649 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_57600 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57600 128 =
      584738441089710645985471 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_57600 : ∀ i : Fin 128,
    levelEleven.lookup (57600 + i.val) ≤ levelElevenRoots.lookup (57600 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_57728 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 57728 128 =
      65246837688141896131588745015971 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_57728 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57728 128 =
      1465098241912810039060545 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_57728 : ∀ i : Fin 128,
    levelEleven.lookup (57728 + i.val) ≤ levelElevenRoots.lookup (57728 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_112 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 57344 512 =
      139189925266187876384475236921686 := by
  have h0 := levelEleven_energy_57344
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 57344 256 =
      59327552598338338763175509770066 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 57344 128 128
      25329862015812097956545719805655 33997690582526240806629789964411 h0 levelEleven_energy_57472
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 57344 384 =
      73943087578045980252886491905715 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 57344 256 128
      59327552598338338763175509770066 14615534979707641489710982135649 h1 levelEleven_energy_57600
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 57344 512 =
      139189925266187876384475236921686 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 57344 384 128
      73943087578045980252886491905715 65246837688141896131588745015971 h2 levelEleven_energy_57728
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_112 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57344 512 =
      3824247634551326273091803 := by
  have h0 := levelEleven_fractional_57344
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57344 256 =
      1774410951548805588045787 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57344 128 128
      777766836365871441524036 996644115182934146521751 h0 levelEleven_fractional_57472
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57344 384 =
      2359149392638516234031258 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57344 256 128
      1774410951548805588045787 584738441089710645985471 h1 levelEleven_fractional_57600
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57344 512 =
      3824247634551326273091803 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 57344 384 128
      2359149392638516234031258 1465098241912810039060545 h2 levelEleven_fractional_57728
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_112 : ∀ i : Fin 512,
    levelEleven.lookup (57344 + i.val) ≤ levelElevenRoots.lookup (57344 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_57344
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 57344 128 128
    h0 levelEleven_squares_57472
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 57344 256 128
    h1 levelEleven_squares_57600
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 57344 384 128
    h2 levelEleven_squares_57728
  exact h3

end WordCertDensity.Certificates
