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
theorem levelEleven_energy_38912 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 38912 128 =
      29894563635568847256961415561875 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_38912 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38912 128 =
      852629279914801039421731 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_38912 : ∀ i : Fin 128,
    levelEleven.lookup (38912 + i.val) ≤ levelElevenRoots.lookup (38912 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_39040 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 39040 128 =
      32671987302472729010456457266965 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_39040 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39040 128 =
      976861388759881525964564 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_39040 : ∀ i : Fin 128,
    levelEleven.lookup (39040 + i.val) ≤ levelElevenRoots.lookup (39040 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_39168 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 39168 128 =
      87199664350668720843679930738268 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_39168 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39168 128 =
      1506388534092297060975118 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_39168 : ∀ i : Fin 128,
    levelEleven.lookup (39168 + i.val) ≤ levelElevenRoots.lookup (39168 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_39296 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 39296 128 =
      53076444976185629713680724921114 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_39296 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 39296 128 =
      1244693978920120560662051 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_39296 : ∀ i : Fin 128,
    levelEleven.lookup (39296 + i.val) ≤ levelElevenRoots.lookup (39296 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_76 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 38912 512 =
      202842660264895926824778528488222 := by
  have h0 := levelEleven_energy_38912
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 38912 256 =
      62566550938041576267417872828840 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 38912 128 128
      29894563635568847256961415561875 32671987302472729010456457266965 h0 levelEleven_energy_39040
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 38912 384 =
      149766215288710297111097803567108 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 38912 256 128
      62566550938041576267417872828840 87199664350668720843679930738268 h1 levelEleven_energy_39168
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 38912 512 =
      202842660264895926824778528488222 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 38912 384 128
      149766215288710297111097803567108 53076444976185629713680724921114 h2 levelEleven_energy_39296
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_76 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38912 512 =
      4580573181687100187023464 := by
  have h0 := levelEleven_fractional_38912
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38912 256 =
      1829490668674682565386295 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38912 128 128
      852629279914801039421731 976861388759881525964564 h0 levelEleven_fractional_39040
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38912 384 =
      3335879202766979626361413 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38912 256 128
      1829490668674682565386295 1506388534092297060975118 h1 levelEleven_fractional_39168
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38912 512 =
      4580573181687100187023464 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 38912 384 128
      3335879202766979626361413 1244693978920120560662051 h2 levelEleven_fractional_39296
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_76 : ∀ i : Fin 512,
    levelEleven.lookup (38912 + i.val) ≤ levelElevenRoots.lookup (38912 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_38912
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 38912 128 128
    h0 levelEleven_squares_39040
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 38912 256 128
    h1 levelEleven_squares_39168
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 38912 384 128
    h2 levelEleven_squares_39296
  exact h3

end WordCertDensity.Certificates
