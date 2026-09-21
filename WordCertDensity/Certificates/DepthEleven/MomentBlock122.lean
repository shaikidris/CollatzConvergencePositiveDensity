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
theorem levelEleven_energy_62464 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 62464 128 =
      19835615267792997657197274770592 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_62464 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62464 128 =
      690299650825607122325162 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_62464 : ∀ i : Fin 128,
    levelEleven.lookup (62464 + i.val) ≤ levelElevenRoots.lookup (62464 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_62592 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 62592 128 =
      149900963251085301915682440454446 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_62592 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62592 128 =
      2323764550383604084177132 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_62592 : ∀ i : Fin 128,
    levelEleven.lookup (62592 + i.val) ≤ levelElevenRoots.lookup (62592 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_62720 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 62720 128 =
      16753704247601159398464736625884 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_62720 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62720 128 =
      616071453479916236807320 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_62720 : ∀ i : Fin 128,
    levelEleven.lookup (62720 + i.val) ≤ levelElevenRoots.lookup (62720 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_62848 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 62848 128 =
      40737940575130003897496182255138 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_62848 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62848 128 =
      1116597777904423587917136 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_62848 : ∀ i : Fin 128,
    levelEleven.lookup (62848 + i.val) ≤ levelElevenRoots.lookup (62848 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_122 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 62464 512 =
      227228223341609462868840634106060 := by
  have h0 := levelEleven_energy_62464
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 62464 256 =
      169736578518878299572879715225038 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 62464 128 128
      19835615267792997657197274770592 149900963251085301915682440454446 h0 levelEleven_energy_62592
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 62464 384 =
      186490282766479458971344451850922 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 62464 256 128
      169736578518878299572879715225038 16753704247601159398464736625884 h1 levelEleven_energy_62720
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 62464 512 =
      227228223341609462868840634106060 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 62464 384 128
      186490282766479458971344451850922 40737940575130003897496182255138 h2 levelEleven_energy_62848
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_122 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62464 512 =
      4746733432593551031226750 := by
  have h0 := levelEleven_fractional_62464
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62464 256 =
      3014064201209211206502294 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62464 128 128
      690299650825607122325162 2323764550383604084177132 h0 levelEleven_fractional_62592
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62464 384 =
      3630135654689127443309614 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62464 256 128
      3014064201209211206502294 616071453479916236807320 h1 levelEleven_fractional_62720
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62464 512 =
      4746733432593551031226750 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 62464 384 128
      3630135654689127443309614 1116597777904423587917136 h2 levelEleven_fractional_62848
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_122 : ∀ i : Fin 512,
    levelEleven.lookup (62464 + i.val) ≤ levelElevenRoots.lookup (62464 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_62464
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 62464 128 128
    h0 levelEleven_squares_62592
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 62464 256 128
    h1 levelEleven_squares_62720
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 62464 384 128
    h2 levelEleven_squares_62848
  exact h3

end WordCertDensity.Certificates
