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
theorem levelEleven_energy_134656 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 134656 128 =
      33784804284789883157818972362404 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_134656 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134656 128 =
      988355307565271315724688 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_134656 : ∀ i : Fin 128,
    levelEleven.lookup (134656 + i.val) ≤ levelElevenRoots.lookup (134656 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_134784 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 134784 128 =
      274127056673240158809236978323581 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_134784 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134784 128 =
      3053445940740773664377361 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_134784 : ∀ i : Fin 128,
    levelEleven.lookup (134784 + i.val) ≤ levelElevenRoots.lookup (134784 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_134912 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 134912 128 =
      26970109443378501047036108751407 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_134912 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134912 128 =
      771266126141547257432380 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_134912 : ∀ i : Fin 128,
    levelEleven.lookup (134912 + i.val) ≤ levelElevenRoots.lookup (134912 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_135040 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 135040 128 =
      39878258255313348476634866148166 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_135040 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 135040 128 =
      1110824486295101872836842 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_135040 : ∀ i : Fin 128,
    levelEleven.lookup (135040 + i.val) ≤ levelElevenRoots.lookup (135040 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_263 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 134656 512 =
      374760228656721891490726925585558 := by
  have h0 := levelEleven_energy_134656
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 134656 256 =
      307911860958030041967055950685985 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 134656 128 128
      33784804284789883157818972362404 274127056673240158809236978323581 h0 levelEleven_energy_134784
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 134656 384 =
      334881970401408543014092059437392 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 134656 256 128
      307911860958030041967055950685985 26970109443378501047036108751407 h1 levelEleven_energy_134912
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 134656 512 =
      374760228656721891490726925585558 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 134656 384 128
      334881970401408543014092059437392 39878258255313348476634866148166 h2 levelEleven_energy_135040
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_263 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134656 512 =
      5923891860742694110371271 := by
  have h0 := levelEleven_fractional_134656
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134656 256 =
      4041801248306044980102049 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134656 128 128
      988355307565271315724688 3053445940740773664377361 h0 levelEleven_fractional_134784
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134656 384 =
      4813067374447592237534429 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134656 256 128
      4041801248306044980102049 771266126141547257432380 h1 levelEleven_fractional_134912
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134656 512 =
      5923891860742694110371271 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 134656 384 128
      4813067374447592237534429 1110824486295101872836842 h2 levelEleven_fractional_135040
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_263 : ∀ i : Fin 512,
    levelEleven.lookup (134656 + i.val) ≤ levelElevenRoots.lookup (134656 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_134656
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 134656 128 128
    h0 levelEleven_squares_134784
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 134656 256 128
    h1 levelEleven_squares_134912
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 134656 384 128
    h2 levelEleven_squares_135040
  exact h3

end WordCertDensity.Certificates
