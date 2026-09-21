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
theorem levelEleven_energy_176640 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 176640 128 =
      37584842242029349277207280582572 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_176640 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176640 128 =
      987182291717325995484105 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_176640 : ∀ i : Fin 128,
    levelEleven.lookup (176640 + i.val) ≤ levelElevenRoots.lookup (176640 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_176768 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 176768 128 =
      24026932488801455855930915486168 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_176768 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176768 128 =
      837396808594283206287049 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_176768 : ∀ i : Fin 128,
    levelEleven.lookup (176768 + i.val) ≤ levelElevenRoots.lookup (176768 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_176896 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 176896 128 =
      40395612669586601008833619484281 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_176896 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176896 128 =
      1029428967733554730250153 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_176896 : ∀ i : Fin 128,
    levelEleven.lookup (176896 + i.val) ≤ levelElevenRoots.lookup (176896 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_177024 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 177024 123 =
      1339472770705254799381467167639560 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_177024 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 177024 123 =
      8389013574980118080368563 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_177024 : ∀ i : Fin 123,
    levelEleven.lookup (177024 + i.val) ≤ levelElevenRoots.lookup (177024 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_345 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 176640 507 =
      1441480158105672205523438983192581 := by
  have h0 := levelEleven_energy_176640
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 176640 256 =
      61611774730830805133138196068740 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 176640 128 128
      37584842242029349277207280582572 24026932488801455855930915486168 h0 levelEleven_energy_176768
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 176640 384 =
      102007387400417406141971815553021 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 176640 256 128
      61611774730830805133138196068740 40395612669586601008833619484281 h1 levelEleven_energy_176896
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 176640 507 =
      1441480158105672205523438983192581 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 176640 384 123
      102007387400417406141971815553021 1339472770705254799381467167639560 h2 levelEleven_energy_177024
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_345 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176640 507 =
      11243021643025282012389870 := by
  have h0 := levelEleven_fractional_176640
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176640 256 =
      1824579100311609201771154 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176640 128 128
      987182291717325995484105 837396808594283206287049 h0 levelEleven_fractional_176768
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176640 384 =
      2854008068045163932021307 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176640 256 128
      1824579100311609201771154 1029428967733554730250153 h1 levelEleven_fractional_176896
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176640 507 =
      11243021643025282012389870 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 176640 384 123
      2854008068045163932021307 8389013574980118080368563 h2 levelEleven_fractional_177024
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_345 : ∀ i : Fin 507,
    levelEleven.lookup (176640 + i.val) ≤ levelElevenRoots.lookup (176640 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_176640
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 176640 128 128
    h0 levelEleven_squares_176768
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 176640 256 128
    h1 levelEleven_squares_176896
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 176640 384 123
    h2 levelEleven_squares_177024
  exact h3

end WordCertDensity.Certificates
