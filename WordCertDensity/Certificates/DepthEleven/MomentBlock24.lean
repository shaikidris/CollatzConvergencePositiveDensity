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
theorem levelEleven_energy_12288 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 12288 128 =
      78925573237807310556977098121097 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_12288 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12288 128 =
      1479629054697875954503060 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_12288 : ∀ i : Fin 128,
    levelEleven.lookup (12288 + i.val) ≤ levelElevenRoots.lookup (12288 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_12416 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 12416 128 =
      14666582180270414538108022717699 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_12416 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12416 128 =
      567349400015639419313536 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_12416 : ∀ i : Fin 128,
    levelEleven.lookup (12416 + i.val) ≤ levelElevenRoots.lookup (12416 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_12544 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 12544 128 =
      119345912628212894865421108936154 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_12544 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12544 128 =
      1958145627155882642370460 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_12544 : ∀ i : Fin 128,
    levelEleven.lookup (12544 + i.val) ≤ levelElevenRoots.lookup (12544 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_12672 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 12672 128 =
      29521536750235692804542719587473 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_12672 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12672 128 =
      880181765567402837013666 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_12672 : ∀ i : Fin 128,
    levelEleven.lookup (12672 + i.val) ≤ levelElevenRoots.lookup (12672 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_24 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 12288 512 =
      242459604796526312765048949362423 := by
  have h0 := levelEleven_energy_12288
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 12288 256 =
      93592155418077725095085120838796 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 12288 128 128
      78925573237807310556977098121097 14666582180270414538108022717699 h0 levelEleven_energy_12416
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 12288 384 =
      212938068046290619960506229774950 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 12288 256 128
      93592155418077725095085120838796 119345912628212894865421108936154 h1 levelEleven_energy_12544
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 12288 512 =
      242459604796526312765048949362423 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 12288 384 128
      212938068046290619960506229774950 29521536750235692804542719587473 h2 levelEleven_energy_12672
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_24 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12288 512 =
      4885305847436800853200722 := by
  have h0 := levelEleven_fractional_12288
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12288 256 =
      2046978454713515373816596 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12288 128 128
      1479629054697875954503060 567349400015639419313536 h0 levelEleven_fractional_12416
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12288 384 =
      4005124081869398016187056 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12288 256 128
      2046978454713515373816596 1958145627155882642370460 h1 levelEleven_fractional_12544
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12288 512 =
      4885305847436800853200722 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 12288 384 128
      4005124081869398016187056 880181765567402837013666 h2 levelEleven_fractional_12672
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_24 : ∀ i : Fin 512,
    levelEleven.lookup (12288 + i.val) ≤ levelElevenRoots.lookup (12288 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_12288
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 12288 128 128
    h0 levelEleven_squares_12416
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 12288 256 128
    h1 levelEleven_squares_12544
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 12288 384 128
    h2 levelEleven_squares_12672
  exact h3

end WordCertDensity.Certificates
