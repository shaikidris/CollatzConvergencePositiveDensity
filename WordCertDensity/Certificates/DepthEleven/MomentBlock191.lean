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
theorem levelEleven_energy_97792 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 97792 128 =
      33182206748747854500306348524786 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_97792 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97792 128 =
      981600801314314186232355 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_97792 : ∀ i : Fin 128,
    levelEleven.lookup (97792 + i.val) ≤ levelElevenRoots.lookup (97792 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_97920 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 97920 128 =
      73423106959336137079991041844483 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_97920 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97920 128 =
      1367244489442204918412924 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_97920 : ∀ i : Fin 128,
    levelEleven.lookup (97920 + i.val) ≤ levelElevenRoots.lookup (97920 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_98048 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 98048 128 =
      41994536321506498006562339150134 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_98048 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98048 128 =
      1102618603355255036784892 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_98048 : ∀ i : Fin 128,
    levelEleven.lookup (98048 + i.val) ≤ levelElevenRoots.lookup (98048 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_98176 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 98176 128 =
      43169676961452725445869125594980 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_98176 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 98176 128 =
      1060762237604921617268027 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_98176 : ∀ i : Fin 128,
    levelEleven.lookup (98176 + i.val) ≤ levelElevenRoots.lookup (98176 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_191 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 97792 512 =
      191769526991043215032728855114383 := by
  have h0 := levelEleven_energy_97792
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 97792 256 =
      106605313708083991580297390369269 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 97792 128 128
      33182206748747854500306348524786 73423106959336137079991041844483 h0 levelEleven_energy_97920
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 97792 384 =
      148599850029590489586859729519403 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 97792 256 128
      106605313708083991580297390369269 41994536321506498006562339150134 h1 levelEleven_energy_98048
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 97792 512 =
      191769526991043215032728855114383 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 97792 384 128
      148599850029590489586859729519403 43169676961452725445869125594980 h2 levelEleven_energy_98176
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_191 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97792 512 =
      4512226131716695758698198 := by
  have h0 := levelEleven_fractional_97792
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97792 256 =
      2348845290756519104645279 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97792 128 128
      981600801314314186232355 1367244489442204918412924 h0 levelEleven_fractional_97920
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97792 384 =
      3451463894111774141430171 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97792 256 128
      2348845290756519104645279 1102618603355255036784892 h1 levelEleven_fractional_98048
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97792 512 =
      4512226131716695758698198 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 97792 384 128
      3451463894111774141430171 1060762237604921617268027 h2 levelEleven_fractional_98176
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_191 : ∀ i : Fin 512,
    levelEleven.lookup (97792 + i.val) ≤ levelElevenRoots.lookup (97792 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_97792
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 97792 128 128
    h0 levelEleven_squares_97920
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 97792 256 128
    h1 levelEleven_squares_98048
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 97792 384 128
    h2 levelEleven_squares_98176
  exact h3

end WordCertDensity.Certificates
