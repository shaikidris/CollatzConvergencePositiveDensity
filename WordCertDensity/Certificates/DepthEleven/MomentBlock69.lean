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
theorem levelEleven_energy_35328 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 35328 128 =
      31819548723449020570255032166972 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_35328 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35328 128 =
      944785368962526665406942 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_35328 : ∀ i : Fin 128,
    levelEleven.lookup (35328 + i.val) ≤ levelElevenRoots.lookup (35328 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_35456 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 35456 128 =
      28113432005652561988119243296816 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_35456 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35456 128 =
      885049436280221068290044 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_35456 : ∀ i : Fin 128,
    levelEleven.lookup (35456 + i.val) ≤ levelElevenRoots.lookup (35456 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_35584 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 35584 128 =
      44519570224280781876140044543177 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_35584 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35584 128 =
      1152704934216344741700966 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_35584 : ∀ i : Fin 128,
    levelEleven.lookup (35584 + i.val) ≤ levelElevenRoots.lookup (35584 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_35712 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 35712 128 =
      68927021289811276517967245025730 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_35712 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35712 128 =
      1270419124453070417115195 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_35712 : ∀ i : Fin 128,
    levelEleven.lookup (35712 + i.val) ≤ levelElevenRoots.lookup (35712 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_69 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 35328 512 =
      173379572243193640952481565032695 := by
  have h0 := levelEleven_energy_35328
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 35328 256 =
      59932980729101582558374275463788 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 35328 128 128
      31819548723449020570255032166972 28113432005652561988119243296816 h0 levelEleven_energy_35456
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 35328 384 =
      104452550953382364434514320006965 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 35328 256 128
      59932980729101582558374275463788 44519570224280781876140044543177 h1 levelEleven_energy_35584
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 35328 512 =
      173379572243193640952481565032695 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 35328 384 128
      104452550953382364434514320006965 68927021289811276517967245025730 h2 levelEleven_energy_35712
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_69 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35328 512 =
      4252958863912162892513147 := by
  have h0 := levelEleven_fractional_35328
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35328 256 =
      1829834805242747733696986 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35328 128 128
      944785368962526665406942 885049436280221068290044 h0 levelEleven_fractional_35456
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35328 384 =
      2982539739459092475397952 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35328 256 128
      1829834805242747733696986 1152704934216344741700966 h1 levelEleven_fractional_35584
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35328 512 =
      4252958863912162892513147 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 35328 384 128
      2982539739459092475397952 1270419124453070417115195 h2 levelEleven_fractional_35712
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_69 : ∀ i : Fin 512,
    levelEleven.lookup (35328 + i.val) ≤ levelElevenRoots.lookup (35328 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_35328
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 35328 128 128
    h0 levelEleven_squares_35456
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 35328 256 128
    h1 levelEleven_squares_35584
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 35328 384 128
    h2 levelEleven_squares_35712
  exact h3

end WordCertDensity.Certificates
