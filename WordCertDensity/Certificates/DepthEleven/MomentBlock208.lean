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
theorem levelEleven_energy_106496 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 106496 128 =
      71420951985216255153252323948908 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_106496 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 106496 128 =
      1576982700596610963077142 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_106496 : ∀ i : Fin 128,
    levelEleven.lookup (106496 + i.val) ≤ levelElevenRoots.lookup (106496 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_106624 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 106624 128 =
      22271443463225291897973811129202 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_106624 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 106624 128 =
      744515859609555680977449 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_106624 : ∀ i : Fin 128,
    levelEleven.lookup (106624 + i.val) ≤ levelElevenRoots.lookup (106624 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_106752 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 106752 128 =
      69292335436849881871839559546709 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_106752 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 106752 128 =
      1419011955769458347898792 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_106752 : ∀ i : Fin 128,
    levelEleven.lookup (106752 + i.val) ≤ levelElevenRoots.lookup (106752 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_106880 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 106880 128 =
      67336109562253261312981725778640 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_106880 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 106880 128 =
      1256453149220032969889661 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_106880 : ∀ i : Fin 128,
    levelEleven.lookup (106880 + i.val) ≤ levelElevenRoots.lookup (106880 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_208 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 106496 512 =
      230320840447544690236047420403459 := by
  have h0 := levelEleven_energy_106496
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 106496 256 =
      93692395448441547051226135078110 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 106496 128 128
      71420951985216255153252323948908 22271443463225291897973811129202 h0 levelEleven_energy_106624
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 106496 384 =
      162984730885291428923065694624819 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 106496 256 128
      93692395448441547051226135078110 69292335436849881871839559546709 h1 levelEleven_energy_106752
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 106496 512 =
      230320840447544690236047420403459 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 106496 384 128
      162984730885291428923065694624819 67336109562253261312981725778640 h2 levelEleven_energy_106880
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_208 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 106496 512 =
      4996963665195657961843044 := by
  have h0 := levelEleven_fractional_106496
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 106496 256 =
      2321498560206166644054591 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 106496 128 128
      1576982700596610963077142 744515859609555680977449 h0 levelEleven_fractional_106624
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 106496 384 =
      3740510515975624991953383 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 106496 256 128
      2321498560206166644054591 1419011955769458347898792 h1 levelEleven_fractional_106752
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 106496 512 =
      4996963665195657961843044 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 106496 384 128
      3740510515975624991953383 1256453149220032969889661 h2 levelEleven_fractional_106880
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_208 : ∀ i : Fin 512,
    levelEleven.lookup (106496 + i.val) ≤ levelElevenRoots.lookup (106496 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_106496
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 106496 128 128
    h0 levelEleven_squares_106624
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 106496 256 128
    h1 levelEleven_squares_106752
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 106496 384 128
    h2 levelEleven_squares_106880
  exact h3

end WordCertDensity.Certificates
