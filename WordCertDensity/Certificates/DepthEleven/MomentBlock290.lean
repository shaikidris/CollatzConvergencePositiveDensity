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
theorem levelEleven_energy_148480 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 148480 128 =
      26623224045534899427843550998673 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_148480 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148480 128 =
      831670766408082789182662 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_148480 : ∀ i : Fin 128,
    levelEleven.lookup (148480 + i.val) ≤ levelElevenRoots.lookup (148480 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_148608 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 148608 128 =
      74617073317044652473299799753885 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_148608 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148608 128 =
      1497466983144458421248359 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_148608 : ∀ i : Fin 128,
    levelEleven.lookup (148608 + i.val) ≤ levelElevenRoots.lookup (148608 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_148736 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 148736 128 =
      45566737222018537110188557710661 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_148736 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148736 128 =
      1059524423704313875376433 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_148736 : ∀ i : Fin 128,
    levelEleven.lookup (148736 + i.val) ≤ levelElevenRoots.lookup (148736 + i.val) ^ 2 := by
  decide +kernel

/-- Exact energy numerator on this interval. -/
theorem levelEleven_energy_148864 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 148864 128 =
      235551650297825769320113954802724 := by decide +kernel

/-- Exact fractional numerator on this interval. -/
theorem levelEleven_fractional_148864 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148864 128 =
      2694412538622417549970566 := by decide +kernel

/-- Every square enclosure on this interval. -/
theorem levelEleven_squares_148864 : ∀ i : Fin 128,
    levelEleven.lookup (148864 + i.val) ≤ levelElevenRoots.lookup (148864 + i.val) ^ 2 := by
  decide +kernel

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_energy_block_290 :
    rangeSum (fun i => levelEleven.lookup i ^ 2) 148480 512 =
      382358684882423858331445863265943 := by
  have h0 := levelEleven_energy_148480
  have h1 : rangeSum (fun i => levelEleven.lookup i ^ 2) 148480 256 =
      101240297362579551901143350752558 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 148480 128 128
      26623224045534899427843550998673 74617073317044652473299799753885 h0 levelEleven_energy_148608
  have h2 : rangeSum (fun i => levelEleven.lookup i ^ 2) 148480 384 =
      146807034584598089011331908463219 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 148480 256 128
      101240297362579551901143350752558 45566737222018537110188557710661 h1 levelEleven_energy_148736
  have h3 : rangeSum (fun i => levelEleven.lookup i ^ 2) 148480 512 =
      382358684882423858331445863265943 :=
    rangeSum_join (fun i => levelEleven.lookup i ^ 2) 148480 384 128
      146807034584598089011331908463219 235551650297825769320113954802724 h2 levelEleven_energy_148864
  exact h3

/-- The four consecutive intervals give the block numerator. -/
theorem levelEleven_fractional_block_290 :
    rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148480 512 =
      6083074711879272635778020 := by
  have h0 := levelEleven_fractional_148480
  have h1 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148480 256 =
      2329137749552541210431021 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148480 128 128
      831670766408082789182662 1497466983144458421248359 h0 levelEleven_fractional_148608
  have h2 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148480 384 =
      3388662173256855085807454 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148480 256 128
      2329137749552541210431021 1059524423704313875376433 h1 levelEleven_fractional_148736
  have h3 : rangeSum (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148480 512 =
      6083074711879272635778020 :=
    rangeSum_join (fun i => levelEleven.lookup i * levelElevenRoots.lookup i) 148480 384 128
      3388662173256855085807454 2694412538622417549970566 h2 levelEleven_fractional_148864
  exact h3

/-- The block contains every indicated square enclosure. -/
theorem levelEleven_squares_block_290 : ∀ i : Fin 512,
    levelEleven.lookup (148480 + i.val) ≤ levelElevenRoots.lookup (148480 + i.val) ^ 2 := by
  have h0 := levelEleven_squares_148480
  have h1 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 148480 128 128
    h0 levelEleven_squares_148608
  have h2 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 148480 256 128
    h1 levelEleven_squares_148736
  have h3 := forallInterval_join
    (fun i => levelEleven.lookup i ≤ levelElevenRoots.lookup i ^ 2) 148480 384 128
    h2 levelEleven_squares_148864
  exact h3

end WordCertDensity.Certificates
