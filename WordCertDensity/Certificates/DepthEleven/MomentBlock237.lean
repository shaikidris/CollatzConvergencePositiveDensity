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
theorem levelEleven_energy_121344 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 121344 128 =
      43554568040914217756517458999499 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_121344 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121344 128 =
      1171455703026865284021758 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_121344 : ∀ i : Fin 128,
    levelEleven.lookup (121344 + i.val) ≤ levelElevenRoots.lookup (121344 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_121472 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 121472 128 =
      15880155941445692881038682566475 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_121472 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121472 128 =
      614211423985100929338989 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_121472 : ∀ i : Fin 128,
    levelEleven.lookup (121472 + i.val) ≤ levelElevenRoots.lookup (121472 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_121600 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 121600 128 =
      68998511572012461476990445356962 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_121600 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121600 128 =
      1414927826440736224168968 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_121600 : ∀ i : Fin 128,
    levelEleven.lookup (121600 + i.val) ≤ levelElevenRoots.lookup (121600 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_121728 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 121728 128 =
      98430853454397208660425235168799 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_121728 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121728 128 =
      1546148816368016430231591 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_121728 : ∀ i : Fin 128,
    levelEleven.lookup (121728 + i.val) ≤ levelElevenRoots.lookup (121728 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_237 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 121344 512 =
      226864089008769580774971822091735 := by
  have h0 := levelEleven_energy_121344
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 121344 256 =
      59434723982359910637556141565974 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 121344 128 128
      43554568040914217756517458999499 15880155941445692881038682566475 h0 levelEleven_energy_121472
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 121344 384 =
      128433235554372372114546586922936 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 121344 256 128
      59434723982359910637556141565974 68998511572012461476990445356962 h1 levelEleven_energy_121600
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 121344 512 =
      226864089008769580774971822091735 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 121344 384 128
      128433235554372372114546586922936 98430853454397208660425235168799 h2 levelEleven_energy_121728
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_237 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121344 512 =
      4746743769820718867761306 := by
  have h0 := levelEleven_fractional_121344
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121344 256 =
      1785667127011966213360747 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121344 128 128
      1171455703026865284021758 614211423985100929338989 h0 levelEleven_fractional_121472
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121344 384 =
      3200594953452702437529715 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121344 256 128
      1785667127011966213360747 1414927826440736224168968 h1 levelEleven_fractional_121600
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121344 512 =
      4746743769820718867761306 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 121344 384 128
      3200594953452702437529715 1546148816368016430231591 h2 levelEleven_fractional_121728
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_237 : ∀ i : Fin 512,
    levelEleven.lookup (121344 + i.val) ≤ levelElevenRoots.lookup (121344 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_121344
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 121344 128 128
    h0 levelEleven_squares_121472
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 121344 256 128
    h1 levelEleven_squares_121600
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 121344 384 128
    h2 levelEleven_squares_121728
  exact h3

end WordCertDensity.Certificates
