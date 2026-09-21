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
theorem levelEleven_energy_23040 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 23040 128 =
      19017230140542580317769310341139 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_23040 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23040 128 =
      717243342603332023233806 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_23040 : ∀ i : Fin 128,
    levelEleven.lookup (23040 + i.val) ≤ levelElevenRoots.lookup (23040 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_23168 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 23168 128 =
      83350719721410676316851950899848 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_23168 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23168 128 =
      1515059222112405562235926 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_23168 : ∀ i : Fin 128,
    levelEleven.lookup (23168 + i.val) ≤ levelElevenRoots.lookup (23168 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_23296 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 23296 128 =
      87582023425170105269769507624941 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_23296 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23296 128 =
      1352508488051462123835028 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_23296 : ∀ i : Fin 128,
    levelEleven.lookup (23296 + i.val) ≤ levelElevenRoots.lookup (23296 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_23424 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 23424 128 =
      50811790902314570761154742635195 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_23424 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23424 128 =
      1202187451608002273232682 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_23424 : ∀ i : Fin 128,
    levelEleven.lookup (23424 + i.val) ≤ levelElevenRoots.lookup (23424 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_45 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 23040 512 =
      240761764189437932665545511501123 := by
  have h0 := levelEleven_energy_23040
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 23040 256 =
      102367949861953256634621261240987 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 23040 128 128
      19017230140542580317769310341139 83350719721410676316851950899848 h0 levelEleven_energy_23168
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 23040 384 =
      189949973287123361904390768865928 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 23040 256 128
      102367949861953256634621261240987 87582023425170105269769507624941 h1 levelEleven_energy_23296
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 23040 512 =
      240761764189437932665545511501123 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 23040 384 128
      189949973287123361904390768865928 50811790902314570761154742635195 h2 levelEleven_energy_23424
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_45 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23040 512 =
      4786998504375201982537442 := by
  have h0 := levelEleven_fractional_23040
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23040 256 =
      2232302564715737585469732 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23040 128 128
      717243342603332023233806 1515059222112405562235926 h0 levelEleven_fractional_23168
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23040 384 =
      3584811052767199709304760 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23040 256 128
      2232302564715737585469732 1352508488051462123835028 h1 levelEleven_fractional_23296
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23040 512 =
      4786998504375201982537442 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 23040 384 128
      3584811052767199709304760 1202187451608002273232682 h2 levelEleven_fractional_23424
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_45 : ∀ i : Fin 512,
    levelEleven.lookup (23040 + i.val) ≤ levelElevenRoots.lookup (23040 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_23040
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 23040 128 128
    h0 levelEleven_squares_23168
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 23040 256 128
    h1 levelEleven_squares_23296
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 23040 384 128
    h2 levelEleven_squares_23424
  exact h3

end WordCertDensity.Certificates
