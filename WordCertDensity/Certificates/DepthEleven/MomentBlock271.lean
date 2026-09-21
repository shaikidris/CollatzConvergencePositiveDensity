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
theorem levelEleven_energy_138752 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 138752 128 =
      95905785048157686850360762230540 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_138752 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138752 128 =
      1647641022811469300583310 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_138752 : ∀ i : Fin 128,
    levelEleven.lookup (138752 + i.val) ≤ levelElevenRoots.lookup (138752 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_138880 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 138880 128 =
      21194217126682698014388774007743 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_138880 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138880 128 =
      732522294189012697333236 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_138880 : ∀ i : Fin 128,
    levelEleven.lookup (138880 + i.val) ≤ levelElevenRoots.lookup (138880 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_139008 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 139008 128 =
      19294600877325781921346973909228 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_139008 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139008 128 =
      693164548948425887110027 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_139008 : ∀ i : Fin 128,
    levelEleven.lookup (139008 + i.val) ≤ levelElevenRoots.lookup (139008 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_139136 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 139136 128 =
      57228802479136752774937038730442 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_139136 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 139136 128 =
      1283714711708472068844213 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_139136 : ∀ i : Fin 128,
    levelEleven.lookup (139136 + i.val) ≤ levelElevenRoots.lookup (139136 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_271 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 138752 512 =
      193623405531302919561033548877953 := by
  have h0 := levelEleven_energy_138752
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 138752 256 =
      117100002174840384864749536238283 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 138752 128 128
      95905785048157686850360762230540 21194217126682698014388774007743 h0 levelEleven_energy_138880
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 138752 384 =
      136394603052166166786096510147511 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 138752 256 128
      117100002174840384864749536238283 19294600877325781921346973909228 h1 levelEleven_energy_139008
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 138752 512 =
      193623405531302919561033548877953 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 138752 384 128
      136394603052166166786096510147511 57228802479136752774937038730442 h2 levelEleven_energy_139136
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_271 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138752 512 =
      4357042577657379953870786 := by
  have h0 := levelEleven_fractional_138752
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138752 256 =
      2380163317000481997916546 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138752 128 128
      1647641022811469300583310 732522294189012697333236 h0 levelEleven_fractional_138880
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138752 384 =
      3073327865948907885026573 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138752 256 128
      2380163317000481997916546 693164548948425887110027 h1 levelEleven_fractional_139008
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138752 512 =
      4357042577657379953870786 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 138752 384 128
      3073327865948907885026573 1283714711708472068844213 h2 levelEleven_fractional_139136
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_271 : ∀ i : Fin 512,
    levelEleven.lookup (138752 + i.val) ≤ levelElevenRoots.lookup (138752 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_138752
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 138752 128 128
    h0 levelEleven_squares_138880
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 138752 256 128
    h1 levelEleven_squares_139008
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 138752 384 128
    h2 levelEleven_squares_139136
  exact h3

end WordCertDensity.Certificates
