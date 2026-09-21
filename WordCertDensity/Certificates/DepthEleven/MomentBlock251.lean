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
theorem levelEleven_energy_128512 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 128512 128 =
      35057527609559378858271516578975 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_128512 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128512 128 =
      934092315256458338811170 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_128512 : ∀ i : Fin 128,
    levelEleven.lookup (128512 + i.val) ≤ levelElevenRoots.lookup (128512 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_128640 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 128640 128 =
      47338023752613934554243827633976 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_128640 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128640 128 =
      1297867620814376956169460 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_128640 : ∀ i : Fin 128,
    levelEleven.lookup (128640 + i.val) ≤ levelElevenRoots.lookup (128640 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_128768 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 128768 128 =
      23724015521033599506826612164433 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_128768 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128768 128 =
      800938110990114827740727 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_128768 : ∀ i : Fin 128,
    levelEleven.lookup (128768 + i.val) ≤ levelElevenRoots.lookup (128768 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_128896 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 128896 128 =
      90048590807634259645172654524902 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_128896 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128896 128 =
      1752043260004673055455459 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_128896 : ∀ i : Fin 128,
    levelEleven.lookup (128896 + i.val) ≤ levelElevenRoots.lookup (128896 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_251 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 128512 512 =
      196168157690841172564514610902286 := by
  have h0 := levelEleven_energy_128512
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 128512 256 =
      82395551362173313412515344212951 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 128512 128 128
      35057527609559378858271516578975 47338023752613934554243827633976 h0 levelEleven_energy_128640
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 128512 384 =
      106119566883206912919341956377384 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 128512 256 128
      82395551362173313412515344212951 23724015521033599506826612164433 h1 levelEleven_energy_128768
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 128512 512 =
      196168157690841172564514610902286 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 128512 384 128
      106119566883206912919341956377384 90048590807634259645172654524902 h2 levelEleven_energy_128896
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_251 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128512 512 =
      4784941307065623178176816 := by
  have h0 := levelEleven_fractional_128512
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128512 256 =
      2231959936070835294980630 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128512 128 128
      934092315256458338811170 1297867620814376956169460 h0 levelEleven_fractional_128640
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128512 384 =
      3032898047060950122721357 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128512 256 128
      2231959936070835294980630 800938110990114827740727 h1 levelEleven_fractional_128768
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128512 512 =
      4784941307065623178176816 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 128512 384 128
      3032898047060950122721357 1752043260004673055455459 h2 levelEleven_fractional_128896
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_251 : ∀ i : Fin 512,
    levelEleven.lookup (128512 + i.val) ≤ levelElevenRoots.lookup (128512 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_128512
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 128512 128 128
    h0 levelEleven_squares_128640
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 128512 256 128
    h1 levelEleven_squares_128768
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 128512 384 128
    h2 levelEleven_squares_128896
  exact h3

end WordCertDensity.Certificates
